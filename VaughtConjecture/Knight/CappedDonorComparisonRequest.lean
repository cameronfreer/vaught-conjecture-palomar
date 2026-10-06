/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorContext
public import VaughtConjecture.Knight.CappedDonorReadback

/-! # Reference acquisition above a requested cutoff

The ordinary `Ref` side of the upper-only receiver (newapproach16 new29 §4): reference data
acquired in the model with the actual cut above a requested comparison cutoff `δ = ofOrd ν`, and
with the geometric receipts of the construction exported.  No characteristic-arity, anchor,
flexibility, low-reference or LOW hypothesis is used.

`exists_ref_above_cut_min`: add the comparison-only request `(limitPart ν, finitePart ν)` to the
donor's requests.  The reference context is acquired with the threshold above the observed and
requested offsets (`exists_referenceContext_margin'`), so `finitePart ν < N` and the comparison
block's endpoint `limitPart ν + N` exceeds `ν`; the actual cut is the maximum of the endpoints
(`cut_actual`) with the block map the block itself (`μ = Subtype.val`, retained by
`ref_of_referenceContext'`), hence `δ < β`; the endpoint margin gives `β < H`
(`cut_actual_lt_cap`).  The context arity equals the threshold (`J = N`: the construction pads
to arity `N - 1` and takes one coface step carrying the cap), and the literal root/face
identifications are exported (`A`, `A'`, `KA = n`, the common face).  The threshold is acquired
above a requested floor `Nmin` as well as above the donor arity (`exists_referenceContext_margin'`
at `max (n + 1) Nmin`), so a small-cutoff restriction of a consumer never limits receiving;
`exists_ref_above_cut'` and `exists_ref_above_cut` are the corollaries without the floor. -/

@[expose] public section

universe w

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan

namespace CappedDonor

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}

/-- **Reference acquisition above a requested cutoff and a requested threshold floor**: the
threshold exceeds both `Nmin` and the donor arity, with `J = N`, the block map, the faces, the
representatives and offsets, the **literal common-face identification** (`HEq Rf.face
(commonFace …)`), and `δ < β < H`. -/
theorem exists_ref_above_cut_min (hM : R.IsModel) (p : S α.1 n) (hp : R.eval t = some p)
    (q : S α.1 (n + 1)) (hq : IsCoface p q) (ν : Ordinal.{0}) (hν : ν < α.1) (Nmin : ℕ) :
    ∃ (C : ReferenceContext R t (⟨limitPart ν, finitePart ν⟩ :: donorRequests q))
      (F : C.FullController)
      (Rf : Ref ↥(blocksOf (⟨limitPart ν, finitePart ν⟩ :: donorRequests q)) n C.N C.m
        q.scheme C.p₀.scheme),
      Rf.p = q.label ∧ Rf.vact = C.p₀.label ∧ Rf.cap = F.cell ∧ Rf.KA = n ∧
      Rf.A' = Finset.univ.image C.proj ∧ Rf.A = Finset.univ.image Fin.castSuccEmb ∧
      Rf.μ = Subtype.val ∧ Rf.C₀ = Finset.univ ∧ Rf.ref = (fun i => C.repBase i.1) ∧
      Rf.off = (fun i => C.repOff i.1) ∧
      (∃ (hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan)
        (hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme)
        (hvC : Finset.univ.image C.proj ∈ C.p₀.scheme.scheme.plan)
        (hC : C.p₀.scheme.restrictFace C.proj hvC = p.scheme),
        HEq Rf.face (commonFace Fin.castSuccEmb hvP hP C.proj hvC hC n)) ∧
      C.m = C.N ∧ Nmin < C.N ∧ n + 1 < C.N ∧
      ofOrd ν < Rf.cut Rf.vactL ∧ Rf.cut Rf.vactL < Rf.vact Rf.cap := by
  set reqs : List BlockRequest := ⟨limitPart ν, finitePart ν⟩ :: donorRequests q with hreqs_def
  have hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1 := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨isNonSuccessor_limitPart ν, (limitPart_le ν).trans_lt hν⟩
    · exact donorRequests_ok q r hr
  obtain ⟨C, hmax, hcap_pos, hmargin, hm⟩ :=
    exists_referenceContext_margin' hM p hp reqs hreqs (max (n + 1) Nmin)
  have hNmin : n + 1 < C.N := (le_max_left _ _).trans_lt hmax
  obtain ⟨F, Rf, h1, h2, h3, h4, h5, h6, hμ, h7, h8, h9, hface⟩ :=
    ref_of_referenceContext' hM p hp q hq hreqs (fun r hr => List.mem_cons_of_mem _ hr) C hNmin
      hcap_pos hmargin
  refine ⟨C, F, Rf, h1, h2, h3, h4, h5, h6, hμ, h7, h8, h9, hface, hm,
    (le_max_right _ _).trans_lt hmax, hNmin, ?_, Ref.cut_actual_lt_cap (R := Rf)⟩
  have hmem : limitPart ν ∈ blocksOf reqs := mem_blocksOf.mpr ⟨_, List.mem_cons_self, rfl⟩
  have hoff : finitePart ν < C.N := C.offset_lt _ List.mem_cons_self
  rw [Rf.cut_actual]
  refine lt_of_lt_of_le ?_ (Finset.le_sup (f := fun i : ↥(blocksOf reqs) =>
    ofOrd (Rf.μ i + C.N)) (Finset.mem_univ ⟨limitPart ν, hmem⟩))
  rw [hμ]
  change ofOrd ν < ofOrd (limitPart ν + C.N)
  rw [ofOrd_lt_ofOrd]
  calc ν = limitPart ν + finitePart ν := (decomposition ν).symm
    _ < limitPart ν + C.N := (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hoff)

/-- **Reference acquisition above a requested cutoff**, with `J = N`, the block map, the faces,
the representatives and offsets, the **literal common-face identification** (`HEq Rf.face
(commonFace …)`), and `δ < β < H` (the threshold floor of `exists_ref_above_cut_min` dropped). -/
theorem exists_ref_above_cut' (hM : R.IsModel) (p : S α.1 n) (hp : R.eval t = some p)
    (q : S α.1 (n + 1)) (hq : IsCoface p q) (ν : Ordinal.{0}) (hν : ν < α.1) :
    ∃ (C : ReferenceContext R t (⟨limitPart ν, finitePart ν⟩ :: donorRequests q))
      (F : C.FullController)
      (Rf : Ref ↥(blocksOf (⟨limitPart ν, finitePart ν⟩ :: donorRequests q)) n C.N C.m
        q.scheme C.p₀.scheme),
      Rf.p = q.label ∧ Rf.vact = C.p₀.label ∧ Rf.cap = F.cell ∧ Rf.KA = n ∧
      Rf.A' = Finset.univ.image C.proj ∧ Rf.A = Finset.univ.image Fin.castSuccEmb ∧
      Rf.μ = Subtype.val ∧ Rf.C₀ = Finset.univ ∧ Rf.ref = (fun i => C.repBase i.1) ∧
      Rf.off = (fun i => C.repOff i.1) ∧
      (∃ (hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan)
        (hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme)
        (hvC : Finset.univ.image C.proj ∈ C.p₀.scheme.scheme.plan)
        (hC : C.p₀.scheme.restrictFace C.proj hvC = p.scheme),
        HEq Rf.face (commonFace Fin.castSuccEmb hvP hP C.proj hvC hC n)) ∧
      C.m = C.N ∧ n + 1 < C.N ∧
      ofOrd ν < Rf.cut Rf.vactL ∧ Rf.cut Rf.vactL < Rf.vact Rf.cap := by
  obtain ⟨C, F, Rf, h1, h2, h3, h4, h5, h6, hμ, h7, h8, h9, hface, hm, -, hNmin, hlt, hH⟩ :=
    exists_ref_above_cut_min hM p hp q hq ν hν 0
  exact ⟨C, F, Rf, h1, h2, h3, h4, h5, h6, hμ, h7, h8, h9, hface, hm, hNmin, hlt, hH⟩

/-- **Reference acquisition above a requested cutoff** (the face receipts of
`exists_ref_above_cut'` dropped). -/
theorem exists_ref_above_cut (hM : R.IsModel) (p : S α.1 n) (hp : R.eval t = some p)
    (q : S α.1 (n + 1)) (hq : IsCoface p q) (ν : Ordinal.{0}) (hν : ν < α.1) :
    ∃ (C : ReferenceContext R t (⟨limitPart ν, finitePart ν⟩ :: donorRequests q))
      (F : C.FullController)
      (Rf : Ref ↥(blocksOf (⟨limitPart ν, finitePart ν⟩ :: donorRequests q)) n C.N C.m
        q.scheme C.p₀.scheme),
      Rf.p = q.label ∧ Rf.vact = C.p₀.label ∧ Rf.cap = F.cell ∧ Rf.KA = n ∧
      Rf.A' = Finset.univ.image C.proj ∧ Rf.A = Finset.univ.image Fin.castSuccEmb ∧
      Rf.μ = Subtype.val ∧ C.m = C.N ∧ n + 1 < C.N ∧
      ofOrd ν < Rf.cut Rf.vactL ∧ Rf.cut Rf.vactL < Rf.vact Rf.cap := by
  obtain ⟨C, F, Rf, h1, h2, h3, h4, h5, h6, hμ, -, -, -, -, hm, hNmin, hlt, hH⟩ :=
    exists_ref_above_cut' hM p hp q hq ν hν
  exact ⟨C, F, Rf, h1, h2, h3, h4, h5, h6, hμ, hm, hNmin, hlt, hH⟩

end CappedDonor

end VaughtConjecture.Knight
