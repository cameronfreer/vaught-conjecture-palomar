/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RowReadback

/-! # The finite reference context (Lemma 8.1.1, finite labels) from `IsModel`

Lemma 8.1.1 enlarges the context of a request so that the readback of Lemma 10.1.1 has old
cells to refer to: a **cap** of full grade whose label dominates every requested finite value,
and one **block representative** per requested limit block, labelled in that block.  This module
produces exactly that finite reference geometry from the model clauses alone:

* `ReferenceContext R t reqs`: an enlarged realized context `ctx ⊇ t` with the projection back
  to the root, its realized type `p₀`, a threshold `N`, the cap `capBase` of grade `N`
  (`cap_grade`, `cap_dom`), and the representatives `repBase`/`repOff` with their labels
  `μ + j`, `j < N`, under the cap.  These are the "old cell" fields of `ReadbackInputs`
  (`capBase`, `cap_dom`, `repBase`, `repOff`, `rep_label`, `rep_off_lt`, `rep_le_cap`) and the
  context/projection fields of `CorrectCertificateData` (`m`, `ctx`, `p₀`, `eval_ctx`, `proj`,
  `proj_ctx`).
* `exists_referenceContext`: it exists in every model, over every realized root tuple, for every
  finite list of requests whose blocks are non-successors below the stage.

## The construction

Representatives first: one Uniformity step per request realizes a coface with a cell labelled in
`[μ, μ + ω)`, i.e. `μ + j` (`exists_nat_of_band`).  The offsets `j` are Skolemized only
afterwards, and the threshold `N` is then chosen above the context arity, every representative
offset and every requested offset — this quantifier order is what makes `rep_off_lt` and
`offset_lt` unconditional.  Padding steps (High-Grade Dominance at threshold `0`) enlarge the
context to arity `N - 1`, so that one final High-Grade Dominance step, at the maximum of all
requested values and representative labels (below the stage since the stage is a limit,
`add_nat_lt_stage`), yields a cell of grade exactly `N`: the cap.  Every old cell is transported
along each coface step with its label (`IsCoface.extendsDomain.cellOf`, `IsCoface.label_cellOf`),
and the projection is the composite of the initial-segment embeddings.

**"Old" is relative.**  The cap is newly created in the final context type `p₀`; it is *old*
relative to the later enlarged domain `D*` of Lemma 8.1.1, which extends `p₀` by one further
point and in which the cap and the representatives are the cells of the initial face.  Likewise
the representatives are old relative to `D*`, not to the root.

## Bridge to `ReadbackInputs.block_limit`

`limitPart_eq_self_of_isNonSuccessor`: a non-successor block satisfies `limitPart μ = μ`, which
is the `block_limit` field the readback needs for every requested block
(`ReferenceContext.block_limit`).

## What remains of the §§8–9 producer

This module discharges only the finite reference-context geometry.  The residual is: the
`FiniteReferenceData` cells *inside* `D*` (the extended domain over `p₀`) with the cap and
representatives read through the face map, the trigger `Σ♦`, the controllers at `(univ, N)` and
`(univ, K)`, the correctness of their rows (Def. 8.3.1/8.3.2), the thinning of `D*` with its
bountifulness (§9), and the `∞` branch (Lemma 8.1.1 clauses 1–2 and Def. 8.3.1 clauses 3–5).
Construction-private, not root-exported. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd Cardinal

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

/-! ## Requests and the produced context -/

/-- A finite request: a block (to be a non-successor below the stage) and an offset. -/
structure BlockRequest where
  /-- The requested limit block. -/
  block : Ordinal.{0}
  /-- The requested finite offset. -/
  offset : ℕ

/-- The requested value `μ + i`. -/
def BlockRequest.value (r : BlockRequest) : Ordinal.{0} := r.block + r.offset

/-- **The finite reference context** over a root tuple `t`, for the requests `reqs`. -/
structure ReferenceContext (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M)
    (reqs : List BlockRequest) : Type (max 1 w) where
  /-- Arity of the enlarged context. -/
  m : ℕ
  /-- The enlarged context tuple. -/
  ctx : Fin m ↪ M
  /-- The projection back to the root tuple. -/
  proj : Fin n ↪ Fin m
  /-- The root tuple is a face of the context. -/
  proj_ctx : proj.trans ctx = t
  /-- The realized type of the context. -/
  p₀ : S α.1 m
  /-- It is realized. -/
  eval_ctx : R.eval ctx = some p₀
  /-- The threshold. -/
  N : ℕ
  /-- The cap: an old full-grade cell. -/
  capBase : Cell p₀.scheme.scheme
  /-- The cap has grade `N`. -/
  cap_grade : p₀.scheme.scheme.grade capBase = N
  /-- The cap dominates every requested finite value. -/
  cap_dom : ∀ r ∈ reqs, ofOrd r.value < p₀.label capBase
  /-- The block representatives. -/
  repBase : Ordinal.{0} → Cell p₀.scheme.scheme
  /-- Their offsets. -/
  repOff : Ordinal.{0} → ℕ
  /-- Each representative carries its block plus a finite offset. -/
  rep_label : ∀ r ∈ reqs, p₀.label (repBase r.block) = ofOrd (r.block + repOff r.block)
  /-- The offsets are below the threshold. -/
  rep_off_lt : ∀ r ∈ reqs, repOff r.block < N
  /-- The representatives are under the cap. -/
  rep_le_cap : ∀ r ∈ reqs, p₀.label (repBase r.block) ≤ p₀.label capBase
  /-- The requested offsets are below the threshold. -/
  offset_lt : ∀ r ∈ reqs, r.offset < N

/-! ## The intermediate context state and one coface step -/

/-- An intermediate enlarged context: a realized tuple with the root as a face. -/
structure Ctx (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M) : Type (max 1 w) where
  m : ℕ
  ctx : Fin m ↪ M
  proj : Fin n ↪ Fin m
  proj_ctx : proj.trans ctx = t
  p₀ : S α.1 m
  eval_ctx : R.eval ctx = some p₀

namespace Ctx

variable {n : ℕ} {t : Fin n ↪ M}

/-- The root context. -/
def root (p : S α.1 n) (hp : R.eval t = some p) : Ctx R t :=
  ⟨n, t, Function.Embedding.refl _, by ext i; rfl, p, hp⟩

/-- One coface step: adjoin a fresh point realizing a coface `q` of the current type. -/
def step (C : Ctx R t) (y : M) (hy : y ∉ Set.range C.ctx) (q : S α.1 (C.m + 1))
    (heval : R.eval (snoc C.ctx y hy) = some q) : Ctx R t :=
  ⟨C.m + 1, snoc C.ctx y hy, C.proj.trans Fin.castSuccEmb, by
    rw [Function.Embedding.trans_assoc, castSuccEmb_trans_snoc, C.proj_ctx], q, heval⟩

/-- Old cells transport along a coface step, with their labels. -/
theorem exists_cell_step (C : Ctx R t) {y : M} {hy : y ∉ Set.range C.ctx} {q : S α.1 (C.m + 1)}
    (hq : IsCoface C.p₀ q) (heval : R.eval (snoc C.ctx y hy) = some q)
    (d : Cell C.p₀.scheme.scheme) :
    ∃ d' : Cell (C.step y hy q heval).p₀.scheme.scheme,
      (C.step y hy q heval).p₀.label d' = C.p₀.label d :=
  ⟨hq.extendsDomain.cellOf d, hq.label_cellOf d⟩

/-- Every request in `rs` has an old cell labelled in its block: `μ + j` for some finite `j`. -/
def HasCells (C : Ctx R t) (rs : List BlockRequest) : Prop :=
  ∀ r ∈ rs, ∃ (c : Cell C.p₀.scheme.scheme) (j : ℕ), C.p₀.label c = ofOrd (r.block + j)

theorem HasCells.step {C : Ctx R t} {rs : List BlockRequest}
    (h : C.HasCells rs) {y : M} {hy : y ∉ Set.range C.ctx} {q : S α.1 (C.m + 1)}
    (hq : IsCoface C.p₀ q) (heval : R.eval (snoc C.ctx y hy) = some q) :
    (C.step y hy q heval).HasCells rs := by
  intro r hr
  obtain ⟨c, j, hc⟩ := h r hr
  obtain ⟨c', hc'⟩ := C.exists_cell_step hq heval c
  exact ⟨c', j, hc'.trans hc⟩

/-- The same, with the offsets fixed in advance. -/
def HasCellsWith (C : Ctx R t) (rs : List BlockRequest) (off : ∀ r, r ∈ rs → ℕ) : Prop :=
  ∀ r (hr : r ∈ rs), ∃ c : Cell C.p₀.scheme.scheme, C.p₀.label c = ofOrd (r.block + off r hr)

theorem HasCellsWith.step {C : Ctx R t} {rs : List BlockRequest} {off : ∀ r, r ∈ rs → ℕ}
    (h : C.HasCellsWith rs off) {y : M} {hy : y ∉ Set.range C.ctx} {q : S α.1 (C.m + 1)}
    (hq : IsCoface C.p₀ q) (heval : R.eval (snoc C.ctx y hy) = some q) :
    (C.step y hy q heval).HasCellsWith rs off := by
  intro r hr
  obtain ⟨c, hc⟩ := h r hr
  obtain ⟨c', hc'⟩ := C.exists_cell_step hq heval c
  exact ⟨c', hc'.trans hc⟩

end Ctx

/-! ## Arithmetic helpers -/

/-- A label in the band `[μ, μ + ω)` is `μ + j` for a finite `j`. -/
theorem exists_nat_of_band {μ : Ordinal.{0}} {x : ExtOrd} (h1 : ofOrd μ ≤ x)
    (h2 : x < ofOrd (μ + Ordinal.omega0)) : ∃ j : ℕ, x = ofOrd (μ + j) := by
  obtain ⟨β, rfl⟩ : ∃ β : Ordinal.{0}, x = ofOrd β := by
    rcases x with _ | _ | β
    · exact absurd h1 (not_le.mpr (bot_lt_ofOrd μ))
    · exact absurd h2 (not_lt.mpr le_top)
    · exact ⟨β, rfl⟩
  rw [ofOrd_le_ofOrd] at h1
  rw [ofOrd_lt_ofOrd] at h2
  obtain ⟨j, hj⟩ := Ordinal.lt_omega0.mp (Ordinal.sub_lt_of_lt_add h2 Ordinal.omega0_pos)
  refine ⟨j, ?_⟩
  rw [← hj, Ordinal.add_sub_cancel_of_le h1]

/-- The finite maximum of a list of ordinals. -/
noncomputable def listMax (l : List Ordinal.{0}) : Ordinal.{0} := l.foldr max 0

theorem le_listMax {l : List Ordinal.{0}} {a : Ordinal.{0}} (h : a ∈ l) : a ≤ listMax l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem listMax_lt {l : List Ordinal.{0}} {γ : Ordinal.{0}} (h0 : 0 < γ)
    (h : ∀ a ∈ l, a < γ) : listMax l < γ := by
  induction l with
  | nil => exact h0
  | cons b l ih =>
    exact max_lt (h b (List.mem_cons_self)) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))

/-- Below a limit stage, a block plus a finite offset stays below the stage. -/
theorem add_nat_lt_stage {μ : Ordinal.{0}} (hμ : μ < α.1) (j : ℕ) : μ + j < α.1 :=
  lt_of_lt_of_le ((add_lt_add_iff_left μ).mpr (Ordinal.natCast_lt_omega0 j))
    (add_omega0_le_of_lt_isSuccLimit α.2 hμ)

theorem stage_pos : (0 : Ordinal.{0}) < α.1 := by
  have := α.2.bot_lt
  simpa using this

/-- **Bridge to `ReadbackInputs.block_limit`**: a non-successor block is its own limit part. -/
theorem limitPart_eq_self_of_isNonSuccessor {μ : Ordinal.{0}} (h : Value.IsNonSuccessor μ) :
    limitPart μ = μ := by
  rcases h with rfl | h
  · simp [limitPart]
  · exact le_antisymm (limitPart_le μ) (succLimit_le_limitPart h le_rfl)

/-- The finite maximum of a list of naturals. -/
def natMax (l : List ℕ) : ℕ := l.foldr max 0

theorem le_natMax {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ natMax l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-! ## The producer -/

variable {n : ℕ} {t : Fin n ↪ M}

/-- **Representatives**: one old cell labelled in the requested block, for every request, by
Uniformity, one coface step per request. -/
theorem exists_ctx_hasCells (hM : R.IsModel) (C : Ctx R t) (rs : List BlockRequest)
    (hrs : ∀ r ∈ rs, Value.IsNonSuccessor r.block ∧ r.block < α.1) :
    ∃ C' : Ctx R t, C'.HasCells rs := by
  induction rs generalizing C with
  | nil => exact ⟨C, fun r hr => by simp at hr⟩
  | cons r rs ih =>
    obtain ⟨C₁, h₁⟩ := ih C fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr')
    obtain ⟨hns, hlt⟩ := hrs r List.mem_cons_self
    obtain ⟨y, hy, q, ⟨Sig, hlo, hhi⟩, hcof, heval⟩ :=
      hM.uniformity C₁.ctx C₁.p₀ C₁.eval_ctx r.block hns hlt
    obtain ⟨j, hj⟩ := exists_nat_of_band hlo hhi
    refine ⟨C₁.step y hy q heval, fun r' hr' => ?_⟩
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact ⟨Sig, j, hj⟩
    · exact (h₁.step hcof heval) r' hr'

/-- **Padding**: enlarge the context by `k` fresh points, keeping the cells. -/
theorem exists_ctx_pad (hM : R.IsModel) (C : Ctx R t) (rs : List BlockRequest)
    (off : ∀ r, r ∈ rs → ℕ) (h : C.HasCellsWith rs off) (k : ℕ) :
    ∃ C' : Ctx R t, C'.m = C.m + k ∧ C'.HasCellsWith rs off := by
  induction k with
  | zero => exact ⟨C, rfl, h⟩
  | succ k ih =>
    obtain ⟨C₁, hm, h₁⟩ := ih
    obtain ⟨y, hy, q, -, hcof, heval⟩ :=
      hM.highGradeDominance C₁.ctx C₁.p₀ C₁.eval_ctx 0 stage_pos
    refine ⟨C₁.step y hy q heval, ?_, h₁.step hcof heval⟩
    show C₁.m + 1 = C.m + (k + 1)
    omega

/-- A request with a given block, when one exists. -/
noncomputable def pick (reqs : List BlockRequest) (μ : Ordinal.{0})
    (h : ∃ r ∈ reqs, r.block = μ) : BlockRequest := h.choose

theorem pick_mem (reqs : List BlockRequest) (μ : Ordinal.{0}) (h : ∃ r ∈ reqs, r.block = μ) :
    pick reqs μ h ∈ reqs := h.choose_spec.1

theorem pick_block (reqs : List BlockRequest) (μ : Ordinal.{0}) (h : ∃ r ∈ reqs, r.block = μ) :
    (pick reqs μ h).block = μ := h.choose_spec.2

open Classical in
/-- Totalize a request-indexed assignment over blocks, with a default off the requested blocks. -/
noncomputable def totalize {X : Type*} (reqs : List BlockRequest) (v : ∀ r, r ∈ reqs → X)
    (dflt : X) (μ : Ordinal.{0}) : X :=
  if h : ∃ r ∈ reqs, r.block = μ then v (pick reqs μ h) (pick_mem reqs μ h) else dflt

theorem totalize_of_ex {X : Type*} (reqs : List BlockRequest) (v : ∀ r, r ∈ reqs → X)
    (dflt : X) {μ : Ordinal.{0}} (h : ∃ r ∈ reqs, r.block = μ) :
    totalize reqs v dflt μ = v (pick reqs μ h) (pick_mem reqs μ h) := by
  unfold totalize
  rw [dite_eq_left h]

/-- **The finite reference context exists** in every model, over every realized root tuple, for
every finite list of non-successor blocks below the stage with arbitrary offsets. -/
theorem exists_referenceContext (hM : R.IsModel) (p : S α.1 n) (hp : R.eval t = some p)
    (reqs : List BlockRequest)
    (hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1) :
    Nonempty (ReferenceContext R t reqs) := by
  classical
  -- representatives, then Skolemize their offsets
  obtain ⟨C₁, h₁⟩ := exists_ctx_hasCells hM (Ctx.root p hp) reqs hreqs
  choose cell₁ off hcell₁ using h₁
  have h₁' : C₁.HasCellsWith reqs off := fun r hr => ⟨cell₁ r hr, hcell₁ r hr⟩
  -- the threshold: above the context arity, every representative offset, every request offset
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
  -- pad to arity `N - 1`
  obtain ⟨C₂, hm₂, h₂⟩ := exists_ctx_pad hM C₁ reqs off h₁' (N - 1 - C₁.m)
  have hm₂' : C₂.m + 1 = N := by omega
  -- the cap: high-grade dominance above every requested value and every representative label
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
      q.label c = ofOrd (r.block + off r hr) := h₂.step hcof heval
  choose cell₃ hcell₃ using h₃
  -- totalize over blocks
  let repBase : Ordinal.{0} → Cell q.scheme.scheme := totalize reqs cell₃ cap
  let repOff : Ordinal.{0} → ℕ := totalize reqs off 0
  have hrep_label : ∀ μ (h : ∃ r ∈ reqs, r.block = μ),
      q.label (repBase μ) = ofOrd (μ + repOff μ) := by
    intro μ h
    show q.label (totalize reqs cell₃ cap μ) =
      ofOrd (μ + ((totalize reqs off 0 μ : ℕ) : Ordinal.{0}))
    rw [totalize_of_ex reqs cell₃ cap h, totalize_of_ex reqs off 0 h]
    have e := hcell₃ (pick reqs μ h) (pick_mem reqs μ h)
    rw [pick_block reqs μ h] at e
    exact e
  have hoff_lt : ∀ μ (h : ∃ r ∈ reqs, r.block = μ), repOff μ < N := by
    intro μ h
    show totalize reqs off 0 μ < N
    rw [totalize_of_ex reqs off 0 h]
    exact hN_off _ _
  have hrep_le : ∀ μ (h : ∃ r ∈ reqs, r.block = μ), q.label (repBase μ) ≤ q.label cap := by
    intro μ h
    rw [hrep_label μ h]
    have hmem : μ + ((repOff μ : ℕ) : Ordinal.{0}) ∈ vals := by
      refine List.mem_append_right _ (List.mem_map.mpr
        ⟨⟨pick reqs μ h, pick_mem reqs μ h⟩, List.mem_attach _ _, ?_⟩)
      show (pick reqs μ h).block + ((off (pick reqs μ h) (pick_mem reqs μ h) : ℕ) : Ordinal.{0})
        = μ + ((totalize reqs off 0 μ : ℕ) : Ordinal.{0})
      rw [totalize_of_ex reqs off 0 h, pick_block reqs μ h]
    exact le_of_lt (lt_of_le_of_lt (ofOrd_le_ofOrd.mpr (le_listMax (l := vals) hmem)) hcapl)
  refine ⟨⟨C₃.m, C₃.ctx, C₃.proj, C₃.proj_ctx, C₃.p₀, C₃.eval_ctx, N, cap, ?_, ?_,
    repBase, repOff, ?_, ?_, ?_, hN_req⟩⟩
  · show q.scheme.scheme.grade cap = N
    rw [hcapg]; exact hm₂'
  · intro r hr
    show ofOrd r.value < q.label cap
    exact lt_of_le_of_lt (ofOrd_le_ofOrd.mpr (le_listMax (l := vals)
      (List.mem_append_left _ (List.mem_map_of_mem hr)))) hcapl
  · intro r hr; exact hrep_label r.block ⟨r, hr, rfl⟩
  · intro r hr; exact hoff_lt r.block ⟨r, hr, rfl⟩
  · intro r hr; exact hrep_le r.block ⟨r, hr, rfl⟩

/-- The `block_limit` field of `ReadbackInputs`, for the requests of a reference context whose
blocks are non-successors. -/
theorem ReferenceContext.block_limit {reqs : List BlockRequest}
    (hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1)
    (_C : ReferenceContext R t reqs) : ∀ r ∈ reqs, limitPart r.block = r.block :=
  fun r hr => limitPart_eq_self_of_isNonSuccessor (hreqs r hr).1

end VaughtConjecture.Knight
