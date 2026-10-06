/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedPrivateLift
public import VaughtConjecture.Knight.GrowthPaddedDonorLift
public import VaughtConjecture.Knight.GrowthPaddedSupply

/-! # Both all-cap original-face grade-two lifts on unchanged growth rows

Bottom supply is independent. Inactive prescriptions use the capped ambient
and the checked lower lift; active ones use their own asymmetric scalar fibre.
No pair ledger or higher successor is constructed here. The proof structure
follows LowOnlyPaddedOriginalLifts, consuming growth repairs on growth rows.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedOriginalLifts
open Transform Value ExtOrd CappedDonor Growth
open GrowthPaddedSuccessor GrowthPaddedDecode
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem private_inactive
    {p : I.right.scheme.below (Finset.univ, 2) → ExtOrd}
    {q : (carrier I X T hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 2) p)
    (hq : RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ)
    (hinactive : ∀ d, I.right.scheme.grade d.1 = 2 → p d ≤ γ)
    (hag : ∀ d, min (q (privateAt I X T hA hB hC d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) r ∧
      (∀ d, r (privateAt I X T hA hB hC d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨r, hr, hread, hcap⟩ := GrowthPaddedPrivateLift.restore I X T hA hB hC hp
    (hq.cap hγ) hγ hag (fun _ => min_le_right _ _) hinactive
  exact ⟨r, hr, hread, fun d => (hcap d).trans (by rw [min_assoc, min_self])⟩

/-- All permitted original caps, including bottom and top. The prescription
and ambient are arbitrary lawful inputs; every physical cap is retained. -/
theorem private_lift
    {p : I.right.scheme.below (Finset.univ, 2) → ExtOrd}
    {q : (carrier I X T hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 2) p)
    (hq : RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ)
    (hag : ∀ d, min (q (privateAt I X T hA hB hC d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) r ∧
      (∀ d, r (privateAt I X T hA hB hC d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := GrowthPaddedSupply.private_bottom_supply I X T hA hB hC hp
    exact ⟨r, hr, hread, fun _ => by simp only [hz, min_bot_right]⟩
  by_cases ha : ∃ d, I.right.scheme.grade d.1 = 2 ∧ γ < p d
  · exact GrowthPaddedPrivateLift.active_private_lift I X T hA hB hC hp hq hγ
      (bot_lt_iff_ne_bot.mpr hz) ha hag
  · exact private_inactive I X T hA hB hC hp hq hγ
      (fun d hd => le_of_not_gt (fun h => ha ⟨d, hd, h⟩)) hag

theorem donor_inactive (hN : 1 < X.req.N)
    {p : I.left.scheme.below (Finset.univ, 2) → ExtOrd}
    {q : (carrier I X T hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) p)
    (hq : RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ)
    (hinactive : ∀ d, I.left.scheme.grade d.1 = 2 → p d ≤ γ)
    (hag : ∀ d, min (q (donorAt I X T hA hB hC d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) r ∧
      (∀ d, r (donorAt I X T hA hB hC d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨r, hr, hread, hcap⟩ := GrowthPaddedDonorLift.restore I X T hA hB hC hN hp
    (hq.cap hγ) hγ hag (fun _ => min_le_right _ _) hinactive
  exact ⟨r, hr, hread, fun d => (hcap d).trans (by rw [min_assoc, min_self])⟩

/-- All permitted original caps, including bottom and top. The prescription
and ambient are arbitrary lawful inputs; every physical cap is retained. -/
theorem donor_lift (hN : 2 < X.req.N)
    {p : I.left.scheme.below (Finset.univ, 2) → ExtOrd}
    {q : (carrier I X T hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) p)
    (hq : RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ)
    (hag : ∀ d, min (q (donorAt I X T hA hB hC d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) r ∧
      (∀ d, r (donorAt I X T hA hB hC d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := GrowthPaddedSupply.donor_bottom_supply I X T hA hB hC hN hp
    exact ⟨r, hr, hread, fun _ => by simp only [hz, min_bot_right]⟩
  by_cases ha : ∃ d, I.left.scheme.grade d.1 = 2 ∧ γ < p d
  · exact GrowthPaddedDonorLift.active_donor_lift I X T hA hB hC hN hp hq hγ
      (bot_lt_iff_ne_bot.mpr hz) ha hag
  · exact donor_inactive I X T hA hB hC (by omega) hp hq hγ
      (fun d hd => le_of_not_gt (fun h => ha ⟨d, hd, h⟩)) hag

end
end VaughtConjecture.Knight.GrowthPaddedOriginalLifts
