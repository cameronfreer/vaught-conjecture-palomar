/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HollowGrowthAdmission
public import VaughtConjecture.Knight.CanonicalCoatomFiniteSupply
public import VaughtConjecture.Knight.CoatomFaceLift

/-! # Positive-root calibration over arbitrary public roots

Pad the realized root by one actual point and enlarge the legal donor with
the constructed ordinary coatom supplier. The scalar receiving template
then has a positive graded root, while the original donor stays a literal
face. No growth physical receiver or stable occurrence is asserted.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.HollowGrowthTemplate
open TypeTower StageType KnightRealization Value ExtOrd CappedDonor
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}

/-- Arbitrary-root acquisition, including the empty root. The padded donor
is legal and restricts literally to the original donor at `extendFace`.
The extra root point is actual, but the padded donor is not claimed realized. -/
theorem acquire_padded (hM : W.IsModel) (hg : W.HasTopGradeGrowth) (hh : W.IsHollow)
    {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (hp : W.eval t = some p)
    (q : S α.1 (n + 1)) (hq : IsCoface p q) (floor : ℕ) :
    ∃ (z : M) (hz : z ∉ Set.range t) (pR : S α.1 (n + 1)),
      W.eval (snoc t z hz) = some pR ∧ IsCoface p pR ∧
      ∃ Q : S α.1 (n + 1 + 1), IsCoface pR Q ∧
        typeMap (FixedHeight.extendFace Fin.castSuccEmb) Q = some q ∧
        ∃ D : HollowGrowthReference.Data (W := W) (snoc t z hz) pR (donorRequests Q)
          (n + 1 + 1) floor, Nonempty (Input Q D) := by
  obtain ⟨z, hz, pR, _, hco, heval⟩ := hM.highGradeDominance t p hp 0 stage_pos
  obtain ⟨Q, hQ, hkeep⟩ := FixedHeight.pinnedCofaceLift (CanonicalCoatomSupply.supply α.2)
    1 (by omega) pR Fin.castSuccEmb p hco q hq
  obtain ⟨D, hD⟩ := acquire Q hM hg hh (Nat.succ_pos n) heval hQ floor
  exact ⟨z, hz, pR, heval, hco, Q, hQ, hkeep, D, hD⟩

/-- The donor restriction after padding still has the original public root
and the same new donor point. This is the tuple equation a later model
application will need; padding has not changed the requested one-point support. -/
theorem donor_tuple {n : ℕ} (t : Fin n ↪ M) (z : M) (hz : z ∉ Set.range t)
    (y : M) (hy : y ∉ Set.range (snoc t z hz)) :
    (FixedHeight.extendFace Fin.castSuccEmb).trans (snoc (snoc t z hz) y hy) =
      snoc t y (fun h => hy (by
        obtain ⟨i, hi⟩ := h
        exact ⟨Fin.castSucc i, (snoc_apply_castSucc t z hz i).trans hi⟩)) := by
  apply Function.Embedding.ext
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [Function.Embedding.trans_apply, FixedHeight.extendFace_last, snoc_apply_last]
  · simp only [Function.Embedding.trans_apply, FixedHeight.extendFace_castSucc,
      Fin.castSuccEmb_apply, snoc_apply_castSucc]

end VaughtConjecture.Knight.HollowGrowthTemplate
