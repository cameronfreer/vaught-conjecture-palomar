/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedStepPrivateLift
public import VaughtConjecture.Knight.GrowthPaddedStepDonorLift
public import VaughtConjecture.Knight.GrowthPaddedStepSupply

/-! # All-cap original-face successor lifting on unchanged growth rows

Bottom supply is independent. Inactive prescriptions use the capped ambient
and the predecessor's original-face lift; active ones use their own scalar fibre.
Donor inactivity is tested before bottom supply: strict arity makes the
activated branch inactive without any activated donor repair assumption.
No pair ledger or higher successor is constructed here. The proof structure
follows GrowthPaddedOriginalLifts, consuming the actual higher growth rows.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedStepOriginalLifts
open Transform Value ExtOrd CappedDonor Growth
open GrowthPaddedContract GrowthPaddedStepRows GrowthPaddedStepDecode
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

theorem private_inactive (hprev : GrowthPaddedStepPrivateLift.PrivateLowerLift P)
    {p : I.right.scheme.below (Finset.univ, k + 1) → ExtOrd}
    {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, k + 1) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ)
    (hinactive : ∀ d, I.right.scheme.grade d.1 = k + 1 → p d ≤ γ)
    (hag : ∀ d, min (q (privateAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
      (∀ d, r (privateAt P hnext d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨r, hr, hread, hcap⟩ := GrowthPaddedStepPrivateLift.restore P hk hnext hprev hp
    (hq.cap hγ) hγ hag (fun _ => min_le_right _ _) hinactive
  exact ⟨r, hr, hread, fun d => (hcap d).trans (by rw [min_assoc, min_self])⟩

/-- All permitted original caps, including bottom and top. The prescription
and ambient are arbitrary lawful inputs; every physical cap is retained. -/
theorem private_lift (hprev : GrowthPaddedStepPrivateLift.PrivateLowerLift P)
    {p : I.right.scheme.below (Finset.univ, k + 1) → ExtOrd}
    {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, k + 1) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ)
    (hag : ∀ d, min (q (privateAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
      (∀ d, r (privateAt P hnext d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := GrowthPaddedStepSupply.private_bottom_supply P hk hnext hp
    exact ⟨r, hr, hread, fun _ => by simp only [hz, min_bot_right]⟩
  by_cases ha : ∃ d, I.right.scheme.grade d.1 = k + 1 ∧ γ < p d
  · exact GrowthPaddedStepPrivateLift.active_private_lift P hk hnext hprev hp hq hγ
      (bot_lt_iff_ne_bot.mpr hz) ha hag
  · exact private_inactive P hk hnext hprev hp hq hγ
      (fun d hd => le_of_not_gt (fun h => ha ⟨d, hd, h⟩)) hag

theorem donor_inactive (hprev : GrowthPaddedStepDonorLift.DonorLowerLift P)
    {p : I.left.scheme.below (Finset.univ, k + 1) → ExtOrd}
    {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ)
    (hinactive : ∀ d, I.left.scheme.grade d.1 = k + 1 → p d ≤ γ)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨r, hr, hread, hcap⟩ := GrowthPaddedStepDonorLift.restore P hk hnext hprev hp
    (hq.cap hγ) hγ hag (fun _ => min_le_right _ _) hinactive
  exact ⟨r, hr, hread, fun d => (hcap d).trans (by rw [min_assoc, min_self])⟩

/-- All permitted original caps, including bottom and top. The prescription
and ambient are arbitrary lawful inputs; every physical cap is retained. -/
theorem donor_lift (hsmall : n + 1 < X.req.N)
    (hprev : GrowthPaddedStepDonorLift.DonorLowerLift P)
    {p : I.left.scheme.below (Finset.univ, k + 1) → ExtOrd}
    {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  by_cases hi : ∀ d, I.left.scheme.grade d.1 = k + 1 → p d ≤ γ
  · exact donor_inactive P hk hnext hprev hp hq hγ hi hag
  obtain ⟨d, hd⟩ := not_forall.mp hi
  obtain ⟨hg, hv⟩ := not_imp.mp hd
  have hN : k + 1 < X.req.N :=
    hg ▸ Growth.donor_grade_lt I.left hsmall d.1
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := GrowthPaddedStepSupply.donor_bottom_supply P hk hnext hN hp
    exact ⟨r, hr, hread, fun _ => by simp only [hz, min_bot_right]⟩
  exact GrowthPaddedStepDonorLift.active_donor_lift P hk hnext hN hprev hp hq hγ
    (bot_lt_iff_ne_bot.mpr hz) ⟨d, hg, not_le.mp hv⟩ hag

/-- At and above activation strict donor arity forces the inactive branch,
for every prescription and every cap. This includes bottom-cap supply. -/
theorem donor_after_activation (hsmall : n + 1 < X.req.N) (hN : X.req.N ≤ k + 1)
    (hprev : GrowthPaddedStepDonorLift.DonorLowerLift P)
    {p : I.left.scheme.below (Finset.univ, k + 1) → ExtOrd}
    {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ :=
  donor_inactive P hk hnext hprev hp hq hγ
    (fun d hd => False.elim ((Growth.donor_grade_lt I.left hsmall d.1).not_ge
      (by rwa [hd]))) hag

end
end VaughtConjecture.Knight.GrowthPaddedStepOriginalLifts
