/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedPrivateLift
public import VaughtConjecture.Knight.LowOnlyPaddedDonorLift
public import VaughtConjecture.Knight.LowOnlyPaddedSupply

/-! # Both all-cap original-face grade-two lifts on unchanged LOW rows

Bottom supply is independent. Inactive prescriptions use the capped ambient
and the checked lower lift; active ones use their own asymmetric scalar fibre.
No pair ledger or higher successor is constructed here.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedOriginalLifts
open Transform Value ExtOrd CappedDonor LowOnly
open LowOnlyPaddedSuccessor LowOnlyPaddedDecode
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem private_inactive
    {p : I.right.scheme.below (effC n 2) → ExtOrd}
    {q : (carrier I F hroot hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (effC n 2) p)
    (hq : RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ)
    (hinactive : ∀ d, I.right.scheme.grade d.1 = 2 → p d ≤ γ)
    (hag : ∀ d, min (q (privateAt I F hroot hA hB hC d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) r ∧
      (∀ d, r (privateAt I F hroot hA hB hC d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨r, hr, hread, hcap⟩ := LowOnlyPaddedPrivateLift.restore I F hroot hA hB hC hp
    (hq.cap hγ) hγ hag (fun _ => min_le_right _ _) hinactive
  exact ⟨r, hr, hread, fun d => (hcap d).trans (by rw [min_assoc, min_self])⟩

/-- All permitted original caps, including bottom and top. The prescription
and ambient are arbitrary lawful inputs; every physical cap is retained. -/
theorem private_lift
    {p : I.right.scheme.below (effC n 2) → ExtOrd}
    {q : (carrier I F hroot hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (effC n 2) p)
    (hq : RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ)
    (hag : ∀ d, min (q (privateAt I F hroot hA hB hC d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) r ∧
      (∀ d, r (privateAt I F hroot hA hB hC d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := LowOnlyPaddedSupply.private_bottom_supply I F hroot hA hB hC hp
    exact ⟨r, hr, hread, fun _ => by simp only [hz, min_bot_right]⟩
  by_cases ha : ∃ d, I.right.scheme.grade d.1 = 2 ∧ γ < p d
  · exact LowOnlyPaddedPrivateLift.active_private_lift I F hroot hA hB hC hp hq hγ
      (bot_lt_iff_ne_bot.mpr hz) ha hag
  · exact private_inactive I F hroot hA hB hC hp hq hγ
      (fun d hd => le_of_not_gt (fun h => ha ⟨d, hd, h⟩)) hag

theorem donor_inactive
    {p : I.left.scheme.below (effC n 2) → ExtOrd}
    {q : (carrier I F hroot hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n 2) p)
    (hq : RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ)
    (hinactive : ∀ d, I.left.scheme.grade d.1 = 2 → p d ≤ γ)
    (hag : ∀ d, min (q (donorAt I F hroot hA hB hC d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) r ∧
      (∀ d, r (donorAt I F hroot hA hB hC d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨r, hr, hread, hcap⟩ := LowOnlyPaddedDonorLift.restore I F hroot hA hB hC hp
    (hq.cap hγ) hγ hag (fun _ => min_le_right _ _) hinactive
  exact ⟨r, hr, hread, fun d => (hcap d).trans (by rw [min_assoc, min_self])⟩

/-- All permitted original caps, including bottom and top. The prescription
and ambient are arbitrary lawful inputs; every physical cap is retained. -/
theorem donor_lift
    {p : I.left.scheme.below (effC n 2) → ExtOrd}
    {q : (carrier I F hroot hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n 2) p)
    (hq : RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ)
    (hag : ∀ d, min (q (donorAt I F hroot hA hB hC d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) r ∧
      (∀ d, r (donorAt I F hroot hA hB hC d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := LowOnlyPaddedSupply.donor_bottom_supply I F hroot hA hB hC hp
    exact ⟨r, hr, hread, fun _ => by simp only [hz, min_bot_right]⟩
  by_cases ha : ∃ d, I.left.scheme.grade d.1 = 2 ∧ γ < p d
  · exact LowOnlyPaddedDonorLift.active_donor_lift I F hroot hA hB hC hp hq hγ
      (bot_lt_iff_ne_bot.mpr hz) ha hag
  · exact donor_inactive I F hroot hA hB hC hp hq hγ
      (fun d hd => le_of_not_gt (fun h => ha ⟨d, hd, h⟩)) hag

end
end VaughtConjecture.Knight.LowOnlyPaddedOriginalLifts
