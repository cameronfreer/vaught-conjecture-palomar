/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReductReferenceContext
public import VaughtConjecture.Knight.ContextSourceRow
public import VaughtConjecture.Knight.OffsetGuard
public import VaughtConjecture.Knight.FiniteCutoffBound
public import VaughtConjecture.Knight.RestrictedComposition
public import VaughtConjecture.Knight.CountedEncoding

/-! # Guard activation from the actual reference context (strict-lower-stage calibration)

The reviewer's assignment (2026-09-18, item 2): for a limit stage `β < α`, construct actual
references and a marker `β + j` inside the receiving model, choose the threshold after their
offsets are known, obtain the dominating cap, and show that **every** relevant actual coface
activates the capped-offset guard of `Knight/OffsetGuard.lean` — derived from the context, not
assumed at each step.

* The reference context of `Knight/ReferenceContext.lean` already does the construction
  (uniformity for the references and the block-`β` marker, threshold after the offsets,
  padding, high-grade dominance for the cap).  What it does not record is that the
  representatives' **grades** are below the threshold — needed for guard reflection.  That
  bound is true of the construction (the representatives are cells of a context of arity below
  `N`, transported along cofaces), so `exists_referenceContext_graded` reruns the assembly with
  the grade tracked, without changing the structure on `main`.
* `exists_controller`: in every coface `q` of the context (any extension domain), completeness
  supplies a full-scope cell of grade `N` and availability from the old cap a controller `Θ` at
  that index with `q cap ≤ q Θ`.
* `guard_active`: at such a `Θ`, the ordinary capped labelling `min (q ·) (q Θ)` satisfies
  `Guard j marker cap`, `j` the marker's offset: the old labels are literal in the coface, and
  `marker ≤ cap ≤ Θ` collapses the capped marker to `β + j`.  Here the stable labelling *is* the
  ordinary one: no stable value is needed in this regime.
* `guarded_correct_capped`: the two-labelling readback of `OffsetGuard` without the `⊤`
  hypothesis — for any transportable predicate `Φ`, safety of the controller's row plus the
  guard on the stable capped labelling gives `Φ` of the ordinary capped labelling.
* `read_proper_capped` / `read_top_capped`: from finite-value correctness resp. the cutoff
  lower bound of the capped labelling, a requested proper value strictly below the cap is read
  **exactly**, and a requested cell whose representative is the block-`β` marker reads at least
  `β`, i.e. `⊤` after reduction at `β` (the block-floor condition, never raw marker domination).

The safe rows themselves (a probe whose controller rows satisfy `Safe`) are supplied by the
separate probe-producing session; nothing here constructs them.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan Transform

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}

/-! ## The grade of the representatives is below the threshold -/

namespace Ctx

/-- Every cell of a context type has grade at most the context's arity. -/
theorem grade_le_arity (C : Ctx R t) (c : Cell C.p₀.scheme.scheme) :
    C.p₀.scheme.scheme.grade c ≤ C.m :=
  (C.p₀.scheme.scheme.grade_le_card_scope c).trans
    ((Finset.card_le_card (Finset.subset_univ _)).trans (Finset.card_fin _).le)

/-- The graded form of `HasCellsWith`: the representatives have grade at most `K`. -/
def HasCellsGraded (C : Ctx R t) (rs : List BlockRequest) (off : ∀ r, r ∈ rs → ℕ)
    (K : ℕ) : Prop :=
  ∀ r (hr : r ∈ rs), ∃ c : Cell C.p₀.scheme.scheme,
    C.p₀.label c = ofOrd (r.block + off r hr) ∧ C.p₀.scheme.scheme.grade c ≤ K

theorem HasCellsWith.graded {C : Ctx R t} {rs : List BlockRequest} {off : ∀ r, r ∈ rs → ℕ}
    (h : C.HasCellsWith rs off) : C.HasCellsGraded rs off C.m := by
  intro r hr
  obtain ⟨c, hc⟩ := h r hr
  exact ⟨c, hc, C.grade_le_arity c⟩

/-- Graded cells transport along a coface step (labels and grades of old cells are literal). -/
theorem HasCellsGraded.step {C : Ctx R t} {rs : List BlockRequest} {off : ∀ r, r ∈ rs → ℕ}
    {K : ℕ} (h : C.HasCellsGraded rs off K) {y : M} {hy : y ∉ Set.range C.ctx}
    {q : S α.1 (C.m + 1)} (hq : IsCoface C.p₀ q) (heval : R.eval (snoc C.ctx y hy) = some q) :
    (C.step y hy q heval).HasCellsGraded rs off K := by
  intro r hr
  obtain ⟨c, hc, hg⟩ := h r hr
  refine ⟨hq.extendsDomain.cellOf c, ?_, ?_⟩
  · exact (hq.label_cellOf c).trans hc
  · exact (hq.extendsDomain.grade_cellOf c).trans_le hg

/-- Padding with the grade bound kept. -/
theorem exists_pad_graded (hM : R.IsModel) (C : Ctx R t) (rs : List BlockRequest)
    (off : ∀ r, r ∈ rs → ℕ) {K : ℕ} (h : C.HasCellsGraded rs off K) (k : ℕ) :
    ∃ C' : Ctx R t, C'.m = C.m + k ∧ C'.HasCellsGraded rs off K := by
  induction k with
  | zero => exact ⟨C, rfl, h⟩
  | succ k ih =>
    obtain ⟨C₁, hm, h₁⟩ := ih
    obtain ⟨y, hy, q, -, hcof, heval⟩ :=
      hM.highGradeDominance C₁.ctx C₁.p₀ C₁.eval_ctx 0 stage_pos
    refine ⟨C₁.step y hy q heval, ?_, h₁.step hcof heval⟩
    change C₁.m + 1 = C.m + (k + 1)
    omega

end Ctx

/-- **The reference context with graded representatives**: the construction of
`exists_referenceContext`, rerun with the grade of every representative tracked; each
representative has grade at most the threshold. -/
theorem exists_referenceContext_graded (hM : R.IsModel) (p : S α.1 n) (hp : R.eval t = some p)
    (reqs : List BlockRequest)
    (hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1) :
    ∃ C : ReferenceContext R t reqs,
      ∀ r ∈ reqs, C.p₀.scheme.scheme.grade (C.repBase r.block) ≤ C.N := by
  classical
  obtain ⟨C₁, h₁⟩ := exists_ctx_hasCells hM (Ctx.root p hp) reqs hreqs
  choose cell₁ off hcell₁ using h₁
  have h₁' : C₁.HasCellsWith reqs off := fun r hr => ⟨cell₁ r hr, hcell₁ r hr⟩
  have h₁g : C₁.HasCellsGraded reqs off C₁.m := h₁'.graded
  let offs : List ℕ := reqs.attach.map fun x => off x.1 x.2
  let N : ℕ := C₁.m + 1 + natMax offs + natMax (reqs.map fun r => r.offset)
  have hN_off : ∀ r (hr : r ∈ reqs), off r hr < N := by
    intro r hr
    have : off r hr ≤ natMax offs :=
      le_natMax (List.mem_map.mpr ⟨⟨r, hr⟩, List.mem_attach _ _, rfl⟩)
    omega
  have hN_req : ∀ r ∈ reqs, r.offset < N := by
    intro r hr
    have : r.offset ≤ natMax (reqs.map fun r => r.offset) :=
      le_natMax (List.mem_map_of_mem hr)
    omega
  have hm₁N : C₁.m < N := by omega
  obtain ⟨C₂, hm₂, h₂⟩ := Ctx.exists_pad_graded hM C₁ reqs off h₁g (N - 1 - C₁.m)
  have hm₂' : C₂.m + 1 = N := by omega
  let vals : List Ordinal.{0} :=
    (reqs.map fun r => r.value) ++
      (reqs.attach.map fun x => x.1.block + ((off x.1 x.2 : ℕ) : Ordinal.{0}))
  have hvals : ∀ a ∈ vals, a < α.1 := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
      exact add_nat_lt_stage (hreqs r hr).2 r.offset
    · obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
      exact add_nat_lt_stage (hreqs x.1 x.2).2 _
  have hγ : listMax vals < α.1 := listMax_lt stage_pos hvals
  obtain ⟨y, hy, q, ⟨cap, hcapg, hcapl⟩, hcof, heval⟩ :=
    hM.highGradeDominance C₂.ctx C₂.p₀ C₂.eval_ctx (listMax vals) hγ
  let C₃ := C₂.step y hy q heval
  have h₃ : ∀ r (hr : r ∈ reqs), ∃ c : Cell q.scheme.scheme,
      q.label c = ofOrd (r.block + off r hr) ∧ q.scheme.scheme.grade c ≤ C₁.m :=
    h₂.step hcof heval
  choose cell₃ hcell₃ hgrade₃ using h₃
  let repBase : Ordinal.{0} → Cell q.scheme.scheme := totalize reqs cell₃ cap
  let repOff : Ordinal.{0} → ℕ := totalize reqs off 0
  have hrep_label : ∀ μ (h : ∃ r ∈ reqs, r.block = μ),
      q.label (repBase μ) = ofOrd (μ + repOff μ) := by
    intro μ h
    change q.label (totalize reqs cell₃ cap μ) =
      ofOrd (μ + ((totalize reqs off 0 μ : ℕ) : Ordinal.{0}))
    rw [totalize_of_ex reqs cell₃ cap h, totalize_of_ex reqs off 0 h]
    have e := hcell₃ (pick reqs μ h) (pick_mem reqs μ h)
    rw [pick_block reqs μ h] at e
    exact e
  have hrep_grade : ∀ μ (h : ∃ r ∈ reqs, r.block = μ),
      q.scheme.scheme.grade (repBase μ) ≤ N := by
    intro μ h
    change q.scheme.scheme.grade (totalize reqs cell₃ cap μ) ≤ N
    rw [totalize_of_ex reqs cell₃ cap h]
    exact (hgrade₃ _ _).trans hm₁N.le
  have hoff_lt : ∀ μ (h : ∃ r ∈ reqs, r.block = μ), repOff μ < N := by
    intro μ h
    change totalize reqs off 0 μ < N
    rw [totalize_of_ex reqs off 0 h]
    exact hN_off _ _
  have hrep_le : ∀ μ (h : ∃ r ∈ reqs, r.block = μ), q.label (repBase μ) ≤ q.label cap := by
    intro μ h
    rw [hrep_label μ h]
    have hmem : μ + ((repOff μ : ℕ) : Ordinal.{0}) ∈ vals := by
      refine List.mem_append_right _ (List.mem_map.mpr
        ⟨⟨pick reqs μ h, pick_mem reqs μ h⟩, List.mem_attach _ _, ?_⟩)
      change (pick reqs μ h).block + ((off (pick reqs μ h) (pick_mem reqs μ h) : ℕ) : Ordinal.{0})
        = μ + ((totalize reqs off 0 μ : ℕ) : Ordinal.{0})
      rw [totalize_of_ex reqs off 0 h, pick_block reqs μ h]
    exact le_of_lt (lt_of_le_of_lt (ofOrd_le_ofOrd.mpr (le_listMax (l := vals) hmem)) hcapl)
  refine ⟨⟨C₃.m, C₃.ctx, C₃.proj, C₃.proj_ctx, C₃.p₀, C₃.eval_ctx, N, cap, ?_, ?_,
    repBase, repOff, ?_, ?_, ?_, hN_req⟩, ?_⟩
  · change q.scheme.scheme.grade cap = N
    rw [hcapg]; exact hm₂'
  · intro r hr
    change ofOrd r.value < q.label cap
    exact lt_of_le_of_lt (ofOrd_le_ofOrd.mpr (le_listMax (l := vals)
      (List.mem_append_left _ (List.mem_map_of_mem hr)))) hcapl
  · intro r hr; exact hrep_label r.block ⟨r, hr, rfl⟩
  · intro r hr; exact hoff_lt r.block ⟨r, hr, rfl⟩
  · intro r hr; exact hrep_le r.block ⟨r, hr, rfl⟩
  · intro r hr; exact hrep_grade r.block ⟨r, hr, rfl⟩

/-! ## The controller and the guard in every coface of the context -/

namespace ReferenceContext

variable {reqs : List BlockRequest} (C : ReferenceContext R t reqs)

/-- The threshold is positive (it is the grade of the cap). -/
theorem N_pos : 0 < C.N := by
  have := C.p₀.scheme.scheme.grade_pos C.capBase
  rwa [C.cap_grade] at this

/-- The threshold is at most the context's arity (the cap is a cell of the context). -/
theorem N_le_m : C.N ≤ C.m := by
  have h := C.p₀.scheme.scheme.grade_le_card_scope C.capBase
  rw [C.cap_grade] at h
  exact h.trans ((Finset.card_le_card (Finset.subset_univ _)).trans (Finset.card_fin _).le)

/-- **The controller**: in every coface of the context, completeness supplies a full-scope cell
of grade `N`, and availability from the old cap supplies a controller at that index dominating
the cap. -/
theorem exists_controller (q : S α.1 (C.m + 1)) (hcof : IsCoface C.p₀ q) :
    ∃ Θ : Cell q.scheme.scheme, q.scheme.scheme.cell Θ = (Finset.univ, C.N) ∧
      q.label (hcof.extendsDomain.cellOf C.capBase) ≤ q.label Θ := by
  have hmem : ((Finset.univ : Finset (Fin (C.m + 1))), C.N) ∈
      Plan.gradedPlan q.scheme.scheme.plan := by
    refine Plan.mem_gradedPlan.mpr ⟨q.scheme.scheme.isPlan.domain_mem, C.N_pos, ?_⟩
    rw [Finset.card_fin]
    exact C.N_le_m.trans (Nat.le_succ _)
  obtain ⟨Xi₀, hXi₀⟩ := q.scheme.complete _ hmem
  have hg : q.scheme.scheme.grade (hcof.extendsDomain.cellOf C.capBase) =
      q.scheme.scheme.grade Xi₀ := by
    rw [hcof.extendsDomain.grade_cellOf, C.cap_grade]
    exact (congrArg Prod.snd hXi₀).symm
  have hs : q.scheme.scheme.scope (hcof.extendsDomain.cellOf C.capBase) ⊆
      q.scheme.scheme.scope Xi₀ := by
    rw [show q.scheme.scheme.scope Xi₀ = Finset.univ from congrArg Prod.fst hXi₀]
    exact Finset.subset_univ _
  obtain ⟨Θ, hΘ, hle⟩ := q.respects.availability _ Xi₀ hs hg
  exact ⟨Θ, hΘ.trans hXi₀, hle⟩

variable {β : LimitStage}

/-- The marker's label is `β + j`, `j = C.repOff β`. -/
theorem marker_label (hβ : blockRequest β ∈ reqs) :
    C.p₀.label (C.repBase β.1) = ofOrd (β.1 + C.repOff β.1) :=
  C.rep_label _ hβ

theorem marker_offset_lt (hβ : blockRequest β ∈ reqs) : C.repOff β.1 < C.N := C.rep_off_lt _ hβ

theorem marker_le_cap (hβ : blockRequest β ∈ reqs) :
    C.p₀.label (C.repBase β.1) ≤ C.p₀.label C.capBase := C.rep_le_cap _ hβ

theorem stage_lt_cap (hβ : blockRequest β ∈ reqs) : ofOrd β.1 < C.p₀.label C.capBase := by
  have := C.cap_dom _ hβ
  rwa [blockRequest_value] at this

/-- A cell of the coface of grade at most `N` lies below a controller at `(univ, N)`. -/
theorem below_controller {q : S α.1 (C.m + 1)} {Θ : Cell q.scheme.scheme}
    (hΘ : q.scheme.scheme.cell Θ = (Finset.univ, C.N)) {d : Cell q.scheme.scheme}
    (hd : q.scheme.scheme.grade d ≤ C.N) :
    GradedLe (q.scheme.scheme.cell d) (q.scheme.scheme.cell Θ) := by
  rw [hΘ]
  exact ⟨Finset.subset_univ _, hd⟩

/-- The old cap, below a controller at `(univ, N)`. -/
noncomputable def capBelow {q : S α.1 (C.m + 1)} (hcof : IsCoface C.p₀ q) {Θ : Cell q.scheme.scheme}
    (hΘ : q.scheme.scheme.cell Θ = (Finset.univ, C.N)) :
    q.scheme.scheme.below (q.scheme.scheme.cell Θ) :=
  ⟨hcof.extendsDomain.cellOf C.capBase, C.below_controller hΘ
    (by rw [hcof.extendsDomain.grade_cellOf, C.cap_grade])⟩

/-- The block-`β` marker, below a controller at `(univ, N)` (its grade is at most `N`). -/
noncomputable def markerBelow {q : S α.1 (C.m + 1)} (hcof : IsCoface C.p₀ q)
    {Θ : Cell q.scheme.scheme}
    (hΘ : q.scheme.scheme.cell Θ = (Finset.univ, C.N))
    (hgr : C.p₀.scheme.scheme.grade (C.repBase β.1) ≤ C.N) :
    q.scheme.scheme.below (q.scheme.scheme.cell Θ) :=
  ⟨hcof.extendsDomain.cellOf (C.repBase β.1), C.below_controller hΘ
    (by rw [hcof.extendsDomain.grade_cellOf]; exact hgr)⟩

theorem grade_capBelow {q : S α.1 (C.m + 1)} (hcof : IsCoface C.p₀ q)
    {Θ : Cell q.scheme.scheme} (hΘ : q.scheme.scheme.cell Θ = (Finset.univ, C.N)) :
    q.scheme.scheme.grade (C.capBelow hcof hΘ).1 = C.N := by
  change q.scheme.scheme.grade (hcof.extendsDomain.cellOf C.capBase) = C.N
  rw [hcof.extendsDomain.grade_cellOf, C.cap_grade]

theorem grade_markerBelow {q : S α.1 (C.m + 1)} (hcof : IsCoface C.p₀ q)
    {Θ : Cell q.scheme.scheme} (hΘ : q.scheme.scheme.cell Θ = (Finset.univ, C.N))
    (hgr : C.p₀.scheme.scheme.grade (C.repBase β.1) ≤ C.N) :
    q.scheme.scheme.grade (C.markerBelow hcof hΘ hgr).1 ≤ C.N := by
  change q.scheme.scheme.grade (hcof.extendsDomain.cellOf (C.repBase β.1)) ≤ C.N
  rw [hcof.extendsDomain.grade_cellOf]
  exact hgr

theorem label_capBelow {q : S α.1 (C.m + 1)} (hcof : IsCoface C.p₀ q)
    {Θ : Cell q.scheme.scheme} (hΘ : q.scheme.scheme.cell Θ = (Finset.univ, C.N)) :
    q.label (C.capBelow hcof hΘ).1 = C.p₀.label C.capBase :=
  hcof.label_cellOf _

theorem label_markerBelow (hβ : blockRequest β ∈ reqs) {q : S α.1 (C.m + 1)}
    (hcof : IsCoface C.p₀ q)
    {Θ : Cell q.scheme.scheme} (hΘ : q.scheme.scheme.cell Θ = (Finset.univ, C.N))
    (hgr : C.p₀.scheme.scheme.grade (C.repBase β.1) ≤ C.N) :
    q.label (C.markerBelow hcof hΘ hgr).1 = ofOrd (β.1 + C.repOff β.1) :=
  (hcof.label_cellOf _).trans (C.marker_label hβ)

/-- **Guard activation**: at a controller dominating the old cap, the ordinary capped labelling
of every coface of the context satisfies the guard with the marker's own offset. -/
theorem guard_active (hβ : blockRequest β ∈ reqs) {q : S α.1 (C.m + 1)}
    (hcof : IsCoface C.p₀ q) {Θ : Cell q.scheme.scheme}
    (hΘ : q.scheme.scheme.cell Θ = (Finset.univ, C.N))
    (hgr : C.p₀.scheme.scheme.grade (C.repBase β.1) ≤ C.N)
    (hcapΘ : q.label (hcof.extendsDomain.cellOf C.capBase) ≤ q.label Θ) :
    Guard (C.repOff β.1) (C.markerBelow hcof hΘ hgr) (C.capBelow hcof hΘ)
      (fun d => min (q.label d.1) (q.label Θ)) := by
  have hlim : limitPart β.1 = β.1 := limitPart_eq_self_of_isNonSuccessor (Or.inr β.2)
  have ha := C.label_markerBelow hβ hcof hΘ hgr
  have hC := C.label_capBelow hcof hΘ
  have haC : q.label (C.markerBelow hcof hΘ hgr).1 ≤ q.label (C.capBelow hcof hΘ).1 := by
    rw [ha, hC, ← C.marker_label hβ]
    exact C.marker_le_cap hβ
  have hCΘ : q.label (C.capBelow hcof hΘ).1 ≤ q.label Θ := hcapΘ
  refine ⟨β.1 + C.repOff β.1, ?_, finitePart_limitPart_add_nat' hlim _⟩
  change min (min (q.label (C.markerBelow hcof hΘ hgr).1) (q.label Θ))
    (min (q.label (C.capBelow hcof hΘ).1) (q.label Θ)) = _
  rw [min_eq_left (haC.trans hCΘ), min_eq_left hCΘ, min_eq_left haC, ha]

end ReferenceContext

/-! ## Two-labelling readback, capped at the controller -/

section Readback

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- **Two-labelling readback at a controller, capped**: for a predicate `Φ` preserved by
faithful transformation, a controller `Θ` whose row is safe, and the guard active on the stable
capped labelling at `Θ`, the ordinary capped labelling satisfies `Φ`.  (`guarded_readback_at`
is the case `q Θ = ⊤` for the two finite correctness predicates.) -/
theorem guarded_correct_capped {Θ : Cell D} {Φ : (D.below (D.cell Θ) → ExtOrd) → Prop}
    (hΦ : ∀ f f', TransformsTo (fun d : D.below (D.cell Θ) => D.grade d.1) f f' → Φ f → Φ f')
    {q s : Cell D → ExtOrd} (hq : RespectsSemantics sem q) (hs : RespectsSemantics sem s)
    {N j : ℕ} (hj : j < N) {a C : D.below (D.cell Θ)} (hC : D.grade C.1 = N)
    (ha : D.grade a.1 ≤ N) (hsafe : Safe Φ j a C (sem.E Θ))
    (hguard : Guard j a C (fun d => min (s d.1) (s Θ))) :
    Φ (fun d => min (q d.1) (q Θ)) :=
  hΦ _ _ (hq.locality Θ) (hsafe (hguard.reflect (hs.locality Θ) hC ha hj))

end Readback

/-! ## Reading the capped correctness predicates -/

/-- From `min x c = v` with `v < c`, `x = v`. -/
theorem eq_of_min_eq_of_lt {x c v : ExtOrd} (h : min x c = v) (hv : v < c) : x = v := by
  rcases le_total x c with hx | hx
  · rwa [min_eq_left hx] at h
  · rw [min_eq_right hx] at h
    rw [h] at hv
    exact absurd hv (lt_irrefl _)

variable {D' : Type*} {grade : D' → ℕ}

/-- **Exact proper readback under a cap**: from finite-value correctness of a labelling capped
at `c`, a request whose representative reads `μ + j'` (`j' < N`, `μ` a limit) and whose value
`μ + i` lies strictly below the cap, which is at most `c`, is read exactly. -/
theorem read_proper_capped {R : FiniteReferenceData D' grade} {f : D' → ExtOrd} {c : ExtOrd}
    (hc : R.Correct (fun d => min (f d) c)) (ht : f R.trigger ≠ ⊥) (hct : c ≠ ⊥)
    (hcap : f R.cap ≤ c) {r : FiniteRequest D'} (hr : r ∈ R.requests)
    (hlim : limitPart r.block = r.block) {j' : ℕ} (hj' : j' < R.N)
    (href : f (R.rep r.block) = ofOrd (r.block + j')) (hrep : f (R.rep r.block) ≤ f R.cap)
    (hlt : ofOrd (r.block + r.offset) < f R.cap) :
    f r.cell = ofOrd (r.block + r.offset) := by
  have h := hc (by
    intro h0
    change min (f R.trigger) c = ⊥ at h0
    rcases le_total (f R.trigger) c with h1 | h1
    · rw [min_eq_left h1] at h0; exact ht h0
    · rw [min_eq_right h1] at h0; exact hct h0) r hr
  change min (min (f r.cell) c) (min (f R.cap) c) =
    min (extVisibilityReplace (min (f (R.rep r.block)) c) R.N r.offset) (min (f R.cap) c) at h
  rw [min_eq_left hcap, min_eq_left (hrep.trans hcap), href,
    extVisibilityReplace_of_finitePart_lt (by rw [finitePart_limitPart_add_nat' hlim]; exact hj'),
    limitPart_add_nat_of_limitPart_eq hlim, min_eq_left hlt.le, min_assoc, min_eq_right hcap] at h
  exact eq_of_min_eq_of_lt h hlt

/-- **Threshold readback under a cap** (the block-floor condition): from the cutoff lower bound
of a labelling capped at `c`, a request with offset `0` whose representative reads `β + j`
(`j < N`, `β` a limit) below the cap, which is at most `c`, and with `β` below the cap, reads at
least `β`, i.e. `⊤` after reduction at `β`. -/
theorem read_top_capped {R : FiniteReferenceData D' grade} {f : D' → ExtOrd} {c : ExtOrd}
    (hc : R.CutoffBound (fun d => min (f d) c)) (ht : f R.trigger ≠ ⊥) (hct : c ≠ ⊥)
    (hcap : f R.cap ≤ c) {r : FiniteRequest D'} (hr : r ∈ R.requests) (h0 : r.offset = 0)
    (hlim : limitPart r.block = r.block) {j : ℕ} (hj : j < R.N)
    (href : f (R.rep r.block) = ofOrd (r.block + j)) (hrep : f (R.rep r.block) ≤ f R.cap)
    (hlt : ofOrd r.block < f R.cap) :
    ofOrd r.block ≤ f r.cell ∧ truncExt r.block (f r.cell) = ⊤ := by
  have h := hc (by
    intro h0
    change min (f R.trigger) c = ⊥ at h0
    rcases le_total (f R.trigger) c with h1 | h1
    · rw [min_eq_left h1] at h0; exact ht h0
    · rw [min_eq_right h1] at h0; exact hct h0) r hr
  change min (extVisibilityReplace (min (f (R.rep r.block)) c) R.N r.offset) (min (f R.cap) c) ≤
    min (min (f r.cell) c) (min (f R.cap) c) at h
  rw [min_eq_left hcap, min_eq_left (hrep.trans hcap), href, h0,
    extVisibilityReplace_of_finitePart_lt (by rw [finitePart_limitPart_add_nat' hlim]; exact hj),
    limitPart_add_nat_of_limitPart_eq hlim, Nat.cast_zero, add_zero, min_eq_left hlt.le, min_assoc,
    min_eq_right hcap] at h
  have hle : ofOrd r.block ≤ f r.cell := h.trans (min_le_left _ _)
  exact ⟨hle, truncExt_eq_top_of_ge hle⟩

end VaughtConjecture.Knight
