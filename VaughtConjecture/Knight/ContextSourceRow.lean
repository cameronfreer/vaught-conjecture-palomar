/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReferenceContext
public import VaughtConjecture.Knight.CountedRecoding

/-! # The smallest non-mute unary request: the controller row over the actual context, and
where the extension stops

The reviewer's bounded assignment (2026-09-14): attempt the smallest actually eligible non-mute
unary request with its requested value strictly below the cut, retaining its actual domain and
the receiver's actual reference context; construct the extension's rows and lawful triggering
labelling, then bountifulness and forced readback; assume nothing in a record; if the attempt
stops, isolate the first unsupported incidence or literal lifting obligation.

**The request.**  A one-point type with one cell of grade `1` labelled `γ = μ + i`, `μ` the
limit part, `i ≥ 1` the finite part (`grade_le_finitePart_of_label`: a grade-`1` cell cannot
carry a limit label), `γ < β`.  The single block request is `⟨μ, i⟩`, and the receiver's
reference context for it exists (`exists_referenceContext_single`): arity `m`, type `p₀`,
threshold `N > i`, a cap of grade `N` above `γ`, a representative of block `μ` labelled
`μ + j`, `j < N`.  **`N` is not `1` or `2`**: it is chosen after the representative offsets and
is bounded below by them and by the context arity; nothing here reduces the grade.

**Necessity, first** (`exists_controller_of_extendsDomain`).  In *any* domain `D` extending
`p₀` with *any* respecting labelling `q'` extending `p₀`'s labels — the certificate's fields, or
the labelling of any realized coface — availability from the cap produces a controller `Ξ` at
`(univ, N)` with `q' Ξ ≥ p₀(cap)`, and locality at `Ξ` transforms its row to `q' ∧ q' Ξ`.  So
the controller's own row must decode, through one Def. 2.3.9 shifter, to the context's actual
labels capped at `q' Ξ`; its diagonal is nonbottom whenever the cap is.  Rows are coded
(`ω·a + b`, `b ≤ N + 1`) while the context's labels are arbitrary below the stage, so the
shifter is a genuine block decoder.  This is what any construction owes, before any request.

**What is constructed** (`ContextSourceRow`).  Over the actual context — its cells of grade
`≤ N` with the request cell adjoined (`cellType`), carrying the actual labels and the requested
value (`actual`) — the **candidate controller row** `sourceRow` recodes every label at grade
`N` by the counted recoding of `Knight/CountedRecoding.lean` (`⊥ ↦ ⊥`, `⊤ ↦` the cap code,
`v ↦ code v`).  Proved, with nothing assumed:
* it is coded at `N` (`sourceRow_isCoded`) and orderly (`sourceRow_orderly`);
* it is **correct** for the reference data of the request (`sourceRow_correct`, Def. 8.3.1's
  finite clause): the request cell reads `code (μ + i)`, which is the visibility replacement at
  `N`, offset `i`, of the representative's `code (μ + j)` — same block, finite part replaced —
  under any cap, and without the trigger guard;
* it **decodes to the actual labels** capped at any `ρ` self-visible at `N`
  (`sourceRow_transformsTo`, from `transformsTo_of_shift` and exact decoding `shift_code`):
  exactly the locality the necessity theorem demands of the controller.

**Where it stops: the first unsupported obligation.**  Consistency (Def. 2.5.12) of the extended
domain asks that this row respect the restricted semantics of its own lower set — in particular
**locality at every inherited cell**: for each old `Sig` of grade `≤ N`,
`p₀.scheme.rows.E Sig ⇒ sourceRow ∧ sourceRow Sig`.  What is known is
`p₀.scheme.rows.E Sig ⇒ p₀.label ∧ p₀.label Sig` (`p₀.respects`), and `sourceRow` is the
recoding of `p₀.label`; the needed transformation is their composite, the transitivity of `⇒`
that the faithful calculus does not have (`Knight/Transform.lean`: the printed composite
witness is refuted).  This is a *literal lifting obligation on the inherited rows*: a coded
labelling of the old lower set that is at once the decoding source of the actual labels and a
transformation target of every inherited row — KVC's source-row contract.  Behind it stand the
rows of the remaining new cells (mixed scopes, the other full-scope grades) with availability
among them, and the bountifulness of the whole (the §9 thinning; the two-level tower candidate
is refuted, `SepThreeTower.tower_not_bountiful`).  Given the three, readback is
`ReadbackInputs.readback`.  No row of the extension beyond the candidate controller row is
constructed here, and no bountifulness is claimed.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open VaughtConjecture.AmalgamationPlan
open TypeTower StageType KnightRealization Transform Value ExtOrd
open CellScheme.restrictFace (toCell)

universe w

/-! ## Grades and finite parts -/

/-- **A cell's grade is at most the finite part of its proper label**: orderliness at the cell. -/
theorem grade_le_finitePart_of_label {α : Ordinal.{0}} {n : ℕ} (t : S α n)
    (d : Cell t.scheme.scheme) {v : Ordinal.{0}} (hv : t.label d = ofOrd v) :
    t.scheme.scheme.grade d ≤ finitePart v := by
  have h := t.respects.orderly d
  rw [hv] at h
  exact selfVis_ofOrd_iff.mp h.symm

/-! ## Necessity: every legal extension has a controller decoding above the cap -/

theorem SemScheme.grade_castCell {n : ℕ} {X Y : SemScheme n} (e : X = Y) (d : Cell X.scheme) :
    Y.scheme.grade (SemScheme.castCell e d) = X.scheme.grade d := by
  subst e
  rfl

/-- The cell map of a domain extension preserves grades. -/
theorem ExtendsDomain.grade_cellOf {α : Ordinal.{0}} {m : ℕ} {p : S α m} {D : SemScheme (m + 1)}
    (h : ExtendsDomain p D) (d : Cell p.scheme.scheme) :
    D.scheme.grade (h.cellOf d) = p.scheme.scheme.grade d := by
  change (D.restrictFace Fin.castSuccEmb h.visible).scheme.grade
    (SemScheme.castCell h.restrict.symm d) = _
  exact SemScheme.grade_castCell h.restrict.symm d

/-- **Every legal extension has a controller above the cap whose row decodes to the labels**:
for a domain `D` extending `p` and a respecting labelling `q'` extending `p`'s labels, there is
a cell `Ξ` at `(univ, grade cap)` with `q' Ξ ≥ p (cap)`, whose row transforms (Def. 2.3.9) to
`q' ∧ q' Ξ` on its lower set; its diagonal is `⊥` only if the cap's label is. -/
theorem exists_controller_of_extendsDomain {α : Ordinal.{0}} {m : ℕ} {p : S α m}
    {D : SemScheme (m + 1)} (h : ExtendsDomain p D) {q' : Cell D.scheme → ExtOrd}
    (hq : RespectsSemantics D.rows q') (hext : ∀ d, q' (h.cellOf d) = p.label d)
    (cap : Cell p.scheme.scheme) :
    ∃ Ξ : Cell D.scheme, D.scheme.cell Ξ = (Finset.univ, p.scheme.scheme.grade cap) ∧
      p.label cap ≤ q' Ξ ∧
      TransformsTo (fun d : D.scheme.below (D.scheme.cell Ξ) => D.scheme.grade d.1)
        (D.rows.E Ξ) (fun d => min (q' d.1) (q' Ξ)) ∧
      (D.rows.E Ξ ⟨Ξ, GradedLe.refl _⟩ = ⊥ → p.label cap = ⊥) := by
  have hmem : (Finset.univ, p.scheme.scheme.grade cap) ∈ Plan.gradedPlan D.scheme.plan := by
    refine Plan.mem_gradedPlan.mpr
      ⟨D.scheme.isPlan.domain_mem, p.scheme.scheme.grade_pos cap, ?_⟩
    change p.scheme.scheme.grade cap ≤ (Finset.univ : Finset (Fin (m + 1))).card
    calc p.scheme.scheme.grade cap ≤ (p.scheme.scheme.scope cap).card :=
          p.scheme.scheme.grade_le_card_scope cap
      _ ≤ Fintype.card (Fin m) := Finset.card_le_univ _
      _ ≤ (Finset.univ : Finset (Fin (m + 1))).card := by
          rw [Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
          exact Nat.le_succ m
  obtain ⟨Xi₀, hXi₀⟩ := D.complete _ hmem
  obtain ⟨Ξ, hΞ, hle⟩ := hq.availability (h.cellOf cap) Xi₀
    (by
      rw [show D.scheme.scope Xi₀ = Finset.univ from congrArg Prod.fst hXi₀]
      exact Finset.subset_univ _)
    (by
      rw [show D.scheme.grade Xi₀ = p.scheme.scheme.grade cap from congrArg Prod.snd hXi₀]
      exact h.grade_cellOf cap)
  rw [hXi₀] at hΞ
  rw [hext cap] at hle
  refine ⟨Ξ, hΞ, hle, hq.locality Ξ, fun hbot => ?_⟩
  obtain ⟨g, σ, -, -, hσbot, -, -, heq⟩ := hq.locality Ξ
  have key : q' Ξ = min (σ (D.rows.E Ξ ⟨Ξ, GradedLe.refl _⟩)) (g (D.scheme.grade Ξ)) := by
    have := heq ⟨Ξ, GradedLe.refl _⟩
    simpa only [min_self] using this
  have hΞbot : q' Ξ = ⊥ := by
    rw [key, hbot, hσbot]
    exact min_eq_left bot_le
  exact le_antisymm (hle.trans hΞbot.le) bot_le

/-! ## The reference context of a single request -/

/-- The single block request of a proper value: its limit and finite parts. -/
noncomputable def blockRequestOf (γ : Ordinal.{0}) : BlockRequest := ⟨limitPart γ, finitePart γ⟩

theorem blockRequestOf_value (γ : Ordinal.{0}) : (blockRequestOf γ).value = γ :=
  decomposition γ

theorem limitPart_blockRequestOf (γ : Ordinal.{0}) :
    limitPart (blockRequestOf γ).block = (blockRequestOf γ).block :=
  limitPart_idem γ

/-- **The receiver's reference context for one proper value below the stage** exists over every
realized root tuple. -/
theorem exists_referenceContext_single {α : LimitStage} {M : Type w}
    {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M} (hM : R.IsModel) (p : S α.1 n)
    (hp : R.eval t = some p) {γ : Ordinal.{0}} (hγ : γ < α.1) :
    Nonempty (ReferenceContext R t [blockRequestOf γ]) :=
  exists_referenceContext hM p hp _ fun r hr => by
    rw [List.mem_singleton] at hr
    subst hr
    exact ⟨isNonSuccessor_iff_isSuccPrelimit.mpr
      (Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr ⟨_, rfl⟩),
      lt_of_le_of_lt (limitPart_le γ) hγ⟩

/-! ## The candidate controller row over the actual context -/

namespace ContextSourceRow

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {r : BlockRequest} (C : ReferenceContext R t [r])

/-- The cells of the candidate controller row: the old cells of grade at most `N`, and the
request cell. -/
abbrev cellType : Type :=
  {d : Cell C.p₀.scheme.scheme // C.p₀.scheme.scheme.grade d ≤ C.N} ⊕ Unit

/-- The grades: the old grades, and `1` at the request cell. -/
def grade : cellType C → ℕ
  | Sum.inl d => C.p₀.scheme.scheme.grade d.1
  | Sum.inr _ => 1

/-- The actual labels: the context's labels, and the requested value at the request cell. -/
noncomputable def actual : cellType C → ExtOrd
  | Sum.inl d => C.p₀.label d.1
  | Sum.inr _ => ofOrd r.value

/-- The ordinal values of a label. -/
noncomputable def ordSet : ExtOrd → Finset Ordinal.{0}
  | some (some v) => {v}
  | _ => ∅

/-- The value set to be recoded: the requested value and every proper label of the context. -/
noncomputable def vals : Finset Ordinal.{0} :=
  insert r.value (Finset.univ.biUnion fun d : Cell C.p₀.scheme.scheme => ordSet (C.p₀.label d))

theorem value_mem_vals : r.value ∈ vals C := Finset.mem_insert_self _ _

theorem mem_vals_of_label {d : Cell C.p₀.scheme.scheme} {v : Ordinal.{0}}
    (hv : C.p₀.label d = ofOrd v) : v ∈ vals C := by
  unfold vals
  apply Finset.mem_insert_of_mem
  rw [Finset.mem_biUnion]
  refine ⟨d, Finset.mem_univ _, ?_⟩
  rw [hv]
  exact Finset.mem_singleton_self v

/-- Coding a label at grade `N` over the values: `⊥ ↦ ⊥`, `⊤ ↦` the cap code, `v ↦ code v`. -/
noncomputable def codeLabel : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ofOrd (capCode C.N (vals C))
  | some (some v) => ofOrd (code C.N (vals C) v)

/-- **The candidate controller row**: the actual labels, recoded at grade `N`. -/
noncomputable def sourceRow (c : cellType C) : ExtOrd := codeLabel C (actual C c)

theorem codeLabel_isCoded (x : ExtOrd) : IsCodedLabel C.N (codeLabel C x) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact Or.inl rfl
  · exact capCode_isCoded _ _
  · exact code_isCoded _ _ _

/-- The row is coded at grade `N`. -/
theorem sourceRow_isCoded (c : cellType C) : IsCodedLabel C.N (sourceRow C c) :=
  codeLabel_isCoded C _

/-- The row decodes to the actual label at every cell. -/
theorem shift_sourceRow (c : cellType C) : shift C.N (vals C) ⊤ (sourceRow C c) = actual C c := by
  rcases c with d | u
  · change shift C.N (vals C) ⊤ (codeLabel C (C.p₀.label d.1)) = C.p₀.label d.1
    rcases hl : C.p₀.label d.1 with _ | _ | v
    · rfl
    · exact shift_capCode _ _ _
    · exact shift_code _ _ _ (mem_vals_of_label C hl)
  · exact shift_code _ _ _ (value_mem_vals C)

section Single

variable (hμ : limitPart r.block = r.block)
include hμ

theorem finitePart_value : finitePart r.value = r.offset := by
  have := finitePart_limitPart_add_nat r.block r.offset
  rwa [hμ] at this

theorem limitPart_value : limitPart r.value = r.block := by
  have := limitPart_limitPart_add_nat r.block r.offset
  rwa [hμ] at this

theorem finitePart_rep : finitePart (r.block + C.repOff r.block) = C.repOff r.block := by
  have := finitePart_limitPart_add_nat r.block (C.repOff r.block)
  rwa [hμ] at this

theorem limitPart_rep : limitPart (r.block + C.repOff r.block) = r.block := by
  have := limitPart_limitPart_add_nat r.block (C.repOff r.block)
  rwa [hμ] at this

omit hμ in
theorem offset_lt : r.offset < C.N := C.offset_lt r (List.mem_singleton_self r)

omit hμ in
theorem repOff_lt : C.repOff r.block < C.N := C.rep_off_lt r (List.mem_singleton_self r)

omit hμ in
theorem one_le_N : 1 ≤ C.N := Nat.lt_of_le_of_lt (Nat.zero_le _) (offset_lt C)

/-- The representative has grade below the threshold: its label is `μ + j` with `j < N`. -/
theorem grade_repBase_le : C.p₀.scheme.scheme.grade (C.repBase r.block) ≤ C.N := by
  have h := grade_le_finitePart_of_label C.p₀ (C.repBase r.block)
    (C.rep_label r (List.mem_singleton_self r))
  rw [finitePart_rep C hμ] at h
  exact h.trans (repOff_lt C).le

/-- The row is orderly, provided the requested offset is positive (as the orderliness of the
request's own grade-`1` cell forces). -/
theorem sourceRow_orderly (h1 : 1 ≤ r.offset) : IsOrderly (grade C) (sourceRow C) := by
  intro c
  refine (?_ : SelfVis (grade C c) (sourceRow C c)).symm
  rcases c with d | u
  · change SelfVis (C.p₀.scheme.scheme.grade d.1) (codeLabel C (C.p₀.label d.1))
    rcases hl : C.p₀.label d.1 with _ | _ | v
    · exact selfVis_bot _
    · exact (capCode_selfVis _ _).mono d.2
    · exact code_selfVis _ _ (grade_le_finitePart_of_label C.p₀ d.1 hl) d.2
  · change SelfVis 1 (ofOrd (code C.N (vals C) r.value))
    refine code_selfVis _ _ ?_ (one_le_N C)
    rw [finitePart_value hμ]
    exact h1

/-- **The reference data of the request over the row's cells**: the context's cap,
representative (also the trigger, nonbottom), and the one request at the request cell. -/
noncomputable def refData : FiniteReferenceData (cellType C) (grade C) where
  N := C.N
  cap := Sum.inl ⟨C.capBase, C.cap_grade.le⟩
  cap_grade := C.cap_grade
  trigger := Sum.inl ⟨C.repBase r.block, grade_repBase_le C hμ⟩
  rep μ := if h : C.p₀.scheme.scheme.grade (C.repBase μ) ≤ C.N then Sum.inl ⟨C.repBase μ, h⟩
    else Sum.inl ⟨C.capBase, C.cap_grade.le⟩
  requests := [⟨Sum.inr (), r.block, r.offset⟩]
  req_grade_le q hq := by
    rw [List.mem_singleton] at hq
    subst hq
    exact one_le_N C
  rep_grade_le q hq := by
    rw [List.mem_singleton] at hq
    subst hq
    change grade C (if h : _ then _ else _) ≤ _
    rw [dite_eq_left (grade_repBase_le C hμ)]
    exact grade_repBase_le C hμ
  offset_lt q hq := by
    rw [List.mem_singleton] at hq
    subst hq
    exact offset_lt C

/-- **The candidate row is correct** (Def. 8.3.1, finite clause): the request cell reads the
visibility replacement at `N`, offset `i`, of the representative's code — same block, finite
part replaced — under any cap, without the trigger guard. -/
theorem sourceRow_correct : (refData C hμ).Correct (sourceRow C) := by
  intro _ q hq
  change q ∈ [⟨Sum.inr (), r.block, r.offset⟩] at hq
  rw [List.mem_singleton] at hq
  subst hq
  congr 1
  change ofOrd (code C.N (vals C) r.value) =
    extVisibilityReplace (sourceRow C (if h : _ then _ else _)) C.N r.offset
  rw [dite_eq_left (grade_repBase_le C hμ)]
  change ofOrd (code C.N (vals C) r.value) =
    extVisibilityReplace (codeLabel C (C.p₀.label (C.repBase r.block))) C.N r.offset
  rw [C.rep_label r (List.mem_singleton_self r)]
  change ofOrd (code C.N (vals C) r.value) =
    extVisibilityReplace (ofOrd (code C.N (vals C) (r.block + C.repOff r.block))) C.N r.offset
  rw [extVisibilityReplace_ofOrd, ofOrd_inj]
  have hi := offset_lt C
  have hj := repOff_lt C
  have hkey : blockOf C.N (vals C) r.value = blockOf C.N (vals C) (r.block + C.repOff r.block) := by
    unfold blockOf keyOrd
    rw [finitePart_value hμ, finitePart_rep C hμ, ite_eq_left hi.le, ite_eq_left hj.le,
      limitPart_value hμ, limitPart_rep C hμ]
  unfold code visibilityReplace
  rw [finitePart_value hμ, finitePart_rep C hμ, hkey, finitePart_mul_add, min_eq_left hi.le,
    min_eq_left hj.le, ite_eq_left hj]
  unfold ordinalReplace
  rw [limitPart_mul_add]

end Single

/-- **The row decodes to the actual labels capped at any `ρ` self-visible at `N`**: the locality
that the necessity theorem demands of a controller, with the counted decoder as shifter. -/
theorem sourceRow_transformsTo {ρ : ExtOrd} (hρ : SelfVis C.N ρ) :
    TransformsTo (grade C) (sourceRow C) (fun c => min (actual C c) ρ) := by
  have h := transformsTo_of_shift C.N (vals C) ⊤ (grade C) (extVisibilityReplace_top _ _)
    (fun _ _ => le_top) (sourceRow C) hρ
  convert h using 1
  funext c
  have hg : grade C c ≤ C.N := by
    rcases c with d | u
    · exact d.2
    · exact one_le_N C
  rw [ite_eq_left hg, shift_sourceRow]

end ContextSourceRow

end VaughtConjecture.Knight
