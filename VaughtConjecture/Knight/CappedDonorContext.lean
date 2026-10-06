/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorReceiving
public import VaughtConjecture.Knight.CappedDonorFace
public import VaughtConjecture.Knight.ReferenceContextMargin
public import VaughtConjecture.Knight.ReferenceOrbitRow

/-! # The receiving input from an actual model (notes32 §1, the adapter)

The capped-donor reference data `CappedDonor.Ref` — hence the receiving-input family and both
fibres of `Knight/CappedDonorReceiving.lean` — **obtained from an actual model**: a model `R`,
a realized root tuple `t` of type `p`, and a lawful stage-`α` donor `q`, a coface of `p` (the
request scheme on `A + x` with the actual tuple's type on `A`).

* The **requests** are the block and offset of every proper donor label (`donorRequests`,
  `mem_donorRequests`); their blocks are non-successors below the stage (`donorRequests_ok`).
  The block list `blocks q` may be empty: no representative is then required.
* The **private context** is the reference context with the endpoint margin
  (`exists_referenceContext_margin`, floor `n + 1`), of arity `J = C.m ≥ N`; its cap is the
  full-scope grade-`N` controller `FullController` dominating the reference cap, so the
  acquisition face is the whole context here (`C₀ = univ`).
* The **common face** is literal: the root type is the restriction of the context along the
  projection (the model's consistency clause) and of the donor along the initial segment (the
  coface condition), so `commonFace` / `commonFace_respects` supply the identification and its
  lawfulness transport **at every grade** (`commonFace_grade`, `commonFace_val_congr`), and the
  labels agree on the face (`face_actual`) by `StageType.label_castCell`.  The root arity is
  arbitrary: `KA = n`, with `n = 0` the empty root (the empty face is visible).

`exists_ref` packages all of this: the reference data exists with the donor as `p`, the actual
context labelling as `vact` and the controller as `cap`.  The only model clauses used are those
of the existing reference-context construction (Uniformity, High-Grade Dominance) and
consistency; the margin is supplied by the same High-Grade Dominance step with a larger finite
bound, so no branch is left unsupplied. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CellScheme.restrictFace

namespace CappedDonor

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}

/-! ## The requests of a donor -/

/-- The block request of a proper label: its block and offset. -/
noncomputable def properRequest : ExtOrd → Option BlockRequest
  | some (some β) => some ⟨limitPart β, finitePart β⟩
  | _ => none

theorem properRequest_ofOrd (β : Ordinal.{0}) :
    properRequest (ofOrd β) = some ⟨limitPart β, finitePart β⟩ := rfl

theorem properRequest_eq_some {x : ExtOrd} {r : BlockRequest} (h : properRequest x = some r) :
    ∃ β : Ordinal.{0}, x = ofOrd β ∧ r = ⟨limitPart β, finitePart β⟩ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact nomatch h
  · exact nomatch h
  · rw [properRequest_ofOrd] at h
    exact ⟨β, rfl, (Option.some.inj h).symm⟩

/-- The requests of a donor: the block and offset of each proper label. -/
noncomputable def donorRequests (q : S α.1 (n + 1)) : List BlockRequest :=
  (List.finRange q.scheme.scheme.card).filterMap fun d => properRequest (q.label d)

theorem mem_donorRequests {q : S α.1 (n + 1)} {r : BlockRequest} :
    r ∈ donorRequests q ↔ ∃ (d : Cell q.scheme.scheme) (β : Ordinal.{0}),
      q.label d = ofOrd β ∧ r = ⟨limitPart β, finitePart β⟩ := by
  unfold donorRequests
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨d, -, hd⟩
    obtain ⟨β, hβ, hr⟩ := properRequest_eq_some hd
    exact ⟨d, β, hβ, hr⟩
  · rintro ⟨d, β, hβ, rfl⟩
    exact ⟨d, List.mem_finRange d, by rw [hβ, properRequest_ofOrd]⟩

/-- The limit part of an ordinal is a non-successor (ported from the reviewer's private lemma in
`FiniteBlockBridge`, with attribution). -/
theorem isNonSuccessor_limitPart (δ : Ordinal.{0}) : IsNonSuccessor (limitPart δ) := by
  by_cases h0 : limitPart δ = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    rw [Order.isSuccLimit_iff]
    refine ⟨by simpa using h0, (Ordinal.isSuccPrelimit_iff_omega0_dvd).2 ?_⟩
    exact ⟨δ / Ordinal.omega0, rfl⟩

/-- The requested blocks are non-successors below the stage. -/
theorem donorRequests_ok (q : S α.1 (n + 1)) :
    ∀ r ∈ donorRequests q, IsNonSuccessor r.block ∧ r.block < α.1 := by
  intro r hr
  obtain ⟨d, β, hβ, rfl⟩ := mem_donorRequests.mp hr
  refine ⟨isNonSuccessor_limitPart β, ?_⟩
  rcases q.label_bound d with h | h
  · rw [hβ, ofOrd_lt_ofOrd] at h
    exact (limitPart_le β).trans_lt h
  · rw [hβ] at h
    exact absurd h (ofOrd_ne_top β)

open Classical in
/-- The blocks of a request list. -/
noncomputable def blocksOf (reqs : List BlockRequest) : Finset Ordinal.{0} :=
  reqs.toFinset.image BlockRequest.block

open Classical in
theorem mem_blocksOf {reqs : List BlockRequest} {μ : Ordinal.{0}} :
    μ ∈ blocksOf reqs ↔ ∃ r ∈ reqs, r.block = μ := by
  unfold blocksOf
  simp only [Finset.mem_image, List.mem_toFinset]

/-- The requested blocks of a donor. -/
noncomputable def blocks (q : S α.1 (n + 1)) : Finset Ordinal.{0} := blocksOf (donorRequests q)

theorem mem_blocks {q : S α.1 (n + 1)} {μ : Ordinal.{0}} :
    μ ∈ blocks q ↔ ∃ r ∈ donorRequests q, r.block = μ := mem_blocksOf

/-- The comparison-only block-zero request (audit18 §5): block `0`, requested offset `0`; the
actual offset of its representative is observed by the context construction. -/
def zeroRequest : BlockRequest := ⟨0, 0⟩

/-- Block zero is a non-successor below every limit stage. -/
theorem zeroRequest_ok : Value.IsNonSuccessor zeroRequest.block ∧ zeroRequest.block < α.1 :=
  ⟨Or.inl rfl, by
    rcases eq_or_ne α.1 0 with h | h
    · exact absurd (by rw [h, ← Ordinal.bot_eq_zero]; exact isMin_bot) α.2.not_isMin
    · exact pos_iff_ne_zero.mpr h⟩

/-! ## The reference data from the model -/

/-- **The receiving input from a reference context**: over a realized root tuple `t` of type `p`
(any arity, the empty root included), a lawful donor `q`, a coface of `p`, and a reference
context with the endpoint margin for a request list containing the donor's requests, there are a
full-scope grade-`N` controller and capped-donor reference data over the blocks of the list whose
donor is `q`, whose actual private labelling is the context's, and whose cap is the controller.
Extra requests are
**comparison-only references**: representatives acquired and their offsets observed before the
threshold is chosen.  This form exports the geometric receipts of the construction: the block map
is the block itself (`μ = Subtype.val`), the faces, representatives and offsets are the context's,
and the face identification is the literal common face `commonFace`. -/
theorem ref_of_referenceContext' (hM : R.IsModel) (p : S α.1 n)
    (hp : R.eval t = some p) (q : S α.1 (n + 1)) (hq : IsCoface p q) {reqs : List BlockRequest}
    (hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1)
    (hsub : ∀ r ∈ donorRequests q, r ∈ reqs) (C : ReferenceContext R t reqs)
    (hNmin : n + 1 < C.N) (hcap_pos : ⊥ < C.p₀.label C.capBase)
    (hmargin : ∀ r ∈ reqs, ofOrd (r.block + C.N) < C.p₀.label C.capBase) :
    ∃ (F : C.FullController) (Rf : Ref ↥(blocksOf reqs) n C.N C.m q.scheme C.p₀.scheme),
      Rf.p = q.label ∧ Rf.vact = C.p₀.label ∧ Rf.cap = F.cell ∧ Rf.KA = n ∧
      Rf.A' = Finset.univ.image C.proj ∧ Rf.A = Finset.univ.image Fin.castSuccEmb ∧
      Rf.μ = Subtype.val ∧ Rf.C₀ = Finset.univ ∧ Rf.ref = (fun i => C.repBase i.1) ∧
      Rf.off = (fun i => C.repOff i.1) ∧
      ∃ (hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan)
        (hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme)
        (hvC : Finset.univ.image C.proj ∈ C.p₀.scheme.scheme.plan)
        (hC : C.p₀.scheme.restrictFace C.proj hvC = p.scheme),
        HEq Rf.face (commonFace Fin.castSuccEmb hvP hP C.proj hvC hC n) := by
  classical
  obtain ⟨F⟩ := C.exists_fullController
  -- the consistency clause: the root type is the restriction of the context along the projection
  have hcons : typeMap C.proj C.p₀ = some p := by
    have h := hM.consistent C.ctx C.p₀ C.proj C.eval_ctx
    rw [C.proj_ctx, hp, knightTower_pull] at h
    exact h.symm
  have hvC : Finset.univ.image C.proj ∈ C.p₀.scheme.scheme.plan :=
    (typeMap_isSome_iff _ _).mp (by rw [hcons]; rfl)
  have hC' : C.p₀.restrictFace C.proj hvC = p := by
    have h := hcons
    rw [typeMap_eq_some _ _ hvC, Option.some.injEq] at h
    exact h
  -- the coface condition: the root type is the restriction of the donor along the initial face
  have hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan := hq.extendsDomain.visible
  have hP' : q.restrictFace Fin.castSuccEmb hvP = p := by
    have h : typeMap Fin.castSuccEmb q = some p := hq
    rw [typeMap_eq_some _ _ hvP, Option.some.injEq] at h
    exact h
  have hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme := congrArg StageType.scheme hP'
  have hC : C.p₀.scheme.restrictFace C.proj hvC = p.scheme := congrArg StageType.scheme hC'
  -- the controller's grade is at most the context arity
  have hNm : C.N ≤ C.m := by
    have h := C.p₀.scheme.scheme.grade_le_card_scope F.cell
    rw [show C.p₀.scheme.scheme.grade F.cell = C.N from congrArg Prod.snd F.index,
      show C.p₀.scheme.scheme.scope F.cell = Finset.univ from congrArg Prod.fst F.index,
      Finset.card_univ, Fintype.card_fin] at h
    exact h
  -- each block is the block of a request
  have hblk : ∀ i : ↥(blocksOf reqs), ∃ r ∈ reqs, r.block = i.1 := fun i =>
    mem_blocksOf.mp i.2
  refine ⟨F, {
    arity_lt := hNmin
    N_le := hNm
    μ := Subtype.val
    μ_limit := fun i => by
      obtain ⟨r, hr, hrb⟩ := hblk i
      rw [← hrb]
      exact limitPart_eq_self_of_isNonSuccessor (hreqs r hr).1
    μ_inj := Subtype.val_injective
    ref := fun i => C.repBase i.1
    off := fun i => C.repOff i.1
    off_lt := fun i => by
      obtain ⟨r, hr, hrb⟩ := hblk i
      have h := C.rep_off_lt r hr
      rwa [hrb] at h
    C₀ := Finset.univ
    cap := F.cell
    cap_cell := F.index
    ref_scope := fun _ => Finset.subset_univ _
    vact := C.p₀.label
    vact_respects := C.p₀.respects
    vact_ref := fun i => by
      obtain ⟨r, hr, hrb⟩ := hblk i
      have h := C.rep_label r hr
      rwa [hrb] at h
    cap_pos := hcap_pos.trans_le F.dominates
    margin := fun i => by
      obtain ⟨r, hr, hrb⟩ := hblk i
      have h := hmargin r hr
      rw [hrb] at h
      exact h.trans_le F.dominates
    p := q.label
    p_respects := q.respects
    p_code := fun d hb ht => by
      rcases ExtOrd.cases (q.label d) with h | h | ⟨β, hβ⟩
      · exact absurd h hb
      · exact absurd h ht
      have hr : (⟨limitPart β, finitePart β⟩ : BlockRequest) ∈ reqs :=
        hsub _ (mem_donorRequests.mpr ⟨d, β, hβ, rfl⟩)
      refine ⟨⟨limitPart β, mem_blocksOf.mpr ⟨_, hr, rfl⟩⟩, finitePart β, C.offset_lt _ hr, ?_⟩
      rw [hβ]
      exact congrArg ofOrd (decomposition β).symm
    A := Finset.univ.image Fin.castSuccEmb
    A' := Finset.univ.image C.proj
    KA := n
    A_mem := hvP
    A'_mem := hvC
    KA_le_card := by
      rw [Finset.card_image_of_injective _ Fin.castSuccEmb.injective, Finset.card_univ,
        Fintype.card_fin]
    KA_le_card' := by
      rw [Finset.card_image_of_injective _ C.proj.injective, Finset.card_univ, Fintype.card_fin]
    A'_sub := Finset.subset_univ _
    face := commonFace Fin.castSuccEmb hvP hP C.proj hvC hC n
    face_grade := commonFace_grade Fin.castSuccEmb hvP hP C.proj hvC hC n
    face_actual := fun a => by
      rw [commonFace_val]
      exact (StageType.label_castCell hC'.symm _).trans ((StageType.label_castCell hP' _).trans
        (congrArg q.label (toCell_belowEquiv_symm_val _ _ _ _ a)))
    face_respects := fun k hk r => by
      refine (commonFace_respects Fin.castSuccEmb hvP hP C.proj hvC hC k r).trans ?_
      refine Iff.of_eq (congrArg (RespectsSemanticsBelow q.scheme.rows _) (funext fun a => ?_))
      congr 1
      apply Subtype.ext
      exact commonFace_val_congr Fin.castSuccEmb hvP hP C.proj hvC hC k a _ rfl }, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvP, hP, hvC, hC, HEq.rfl⟩

/-- **The receiving input from a reference context** (the geometric receipts of
`ref_of_referenceContext'` dropped). -/
theorem ref_of_referenceContext (hM : R.IsModel) (p : S α.1 n)
    (hp : R.eval t = some p) (q : S α.1 (n + 1)) (hq : IsCoface p q) {reqs : List BlockRequest}
    (hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1)
    (hsub : ∀ r ∈ donorRequests q, r ∈ reqs) (C : ReferenceContext R t reqs)
    (hNmin : n + 1 < C.N) (hcap_pos : ⊥ < C.p₀.label C.capBase)
    (hmargin : ∀ r ∈ reqs, ofOrd (r.block + C.N) < C.p₀.label C.capBase) :
    ∃ (F : C.FullController) (Rf : Ref ↥(blocksOf reqs) n C.N C.m q.scheme C.p₀.scheme),
      Rf.p = q.label ∧ Rf.vact = C.p₀.label ∧ Rf.cap = F.cell ∧ Rf.KA = n ∧
      Rf.A' = Finset.univ.image C.proj := by
  obtain ⟨F, Rf, h1, h2, h3, h4, h5, -⟩ :=
    ref_of_referenceContext' hM p hp q hq hreqs hsub C hNmin hcap_pos hmargin
  exact ⟨F, Rf, h1, h2, h3, h4, h5⟩

/-- **The receiving input exists in every model, for any request list containing the donor's
requests** (the reference context with the margin, then `ref_of_referenceContext`). -/
theorem exists_ref_of_reqs (hM : R.IsModel) (p : S α.1 n) (hp : R.eval t = some p)
    (q : S α.1 (n + 1)) (hq : IsCoface p q) (reqs : List BlockRequest)
    (hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1)
    (hsub : ∀ r ∈ donorRequests q, r ∈ reqs) :
    ∃ (C : ReferenceContext R t reqs) (F : C.FullController)
      (Rf : Ref ↥(blocksOf reqs) n C.N C.m q.scheme C.p₀.scheme),
      Rf.p = q.label ∧ Rf.vact = C.p₀.label ∧ Rf.cap = F.cell ∧ Rf.KA = n := by
  obtain ⟨C, hNmin, hcap_pos, hmargin⟩ :=
    exists_referenceContext_margin hM p hp reqs hreqs (n + 1)
  obtain ⟨F, Rf, h1, h2, h3, h4, -⟩ :=
    ref_of_referenceContext hM p hp q hq hreqs hsub C hNmin hcap_pos hmargin
  exact ⟨C, F, Rf, h1, h2, h3, h4⟩

/-- **The receiving input exists in every model** (the donor's own requests). -/
theorem exists_ref (hM : R.IsModel) (p : S α.1 n) (hp : R.eval t = some p)
    (q : S α.1 (n + 1)) (hq : IsCoface p q) :
    ∃ (C : ReferenceContext R t (donorRequests q)) (F : C.FullController)
      (Rf : Ref ↥(blocks q) n C.N C.m q.scheme C.p₀.scheme),
      Rf.p = q.label ∧ Rf.vact = C.p₀.label ∧ Rf.cap = F.cell ∧ Rf.KA = n :=
  exists_ref_of_reqs hM p hp q hq (donorRequests q) (donorRequests_ok q) fun _ h => h

/-- **The comparison-only reference** (audit18 §5): with the block-zero request added, the
reference data always has a block (`0`), so the actual cut is positive — with no proper donor
block, `cut vact = N` instead of bottom.  The order of choices is the context construction's:
acquire the representative, observe its offset, choose the threshold above it, request the
controller.  This changes the chosen reference data; it does not make the empty maximum
positive. -/
theorem exists_ref_zero (hM : R.IsModel) (p : S α.1 n) (hp : R.eval t = some p)
    (q : S α.1 (n + 1)) (hq : IsCoface p q) :
    ∃ (C : ReferenceContext R t (zeroRequest :: donorRequests q)) (F : C.FullController)
      (Rf : Ref ↥(blocksOf (zeroRequest :: donorRequests q)) n C.N C.m q.scheme C.p₀.scheme),
      Rf.p = q.label ∧ Rf.vact = C.p₀.label ∧ Rf.cap = F.cell ∧ Rf.KA = n ∧
      (0 : Ordinal.{0}) ∈ blocksOf (zeroRequest :: donorRequests q) ∧ ⊥ < Rf.cut Rf.vactL := by
  obtain ⟨C, F, Rf, hp', hv, hc, hKA⟩ := exists_ref_of_reqs hM p hp q hq
    (zeroRequest :: donorRequests q) (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact zeroRequest_ok
      · exact donorRequests_ok q r hr)
    (fun r hr => List.mem_cons_of_mem _ hr)
  have h0 : (0 : Ordinal.{0}) ∈ blocksOf (zeroRequest :: donorRequests q) :=
    mem_blocksOf.mpr ⟨zeroRequest, List.mem_cons_self, rfl⟩
  refine ⟨C, F, Rf, hp', hv, hc, hKA, h0, ?_⟩
  rw [Rf.cut_actual]
  exact (bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)).trans_le
    (Finset.le_sup (f := fun i : ↥(blocksOf (zeroRequest :: donorRequests q)) =>
      ofOrd (Rf.μ i + C.N)) (Finset.mem_univ ⟨0, h0⟩))

end CappedDonor

end VaughtConjecture.Knight
