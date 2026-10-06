/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepOriginalLifts

/-! # Exhaustive all-cap successor lifting ledger

The actual two-face scope cover reduces proper prescriptions through an
inherited original face. It is not a simultaneous two-history assertion or a
mixed-prescription lift on an arbitrary larger plan.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedStepLedger
open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse
open LowOnlyPaddedContract LowOnlyPaddedStepRows LowOnlyOrderedLadder
open LowOnlyPaddedStepDecode LowOnlyPaddedStepFaces
open LowOnlyPaddedFaces (fullEquiv full_respects_iff)
open AmalgamationPlan CoatomBoundaryExtension
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)


variable (hplan : P.carrier.plan = R) (hprev : TargetGradeLifting.Through P.rows k)
  (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)

theorem inherited_lift {U V : Finset ι × ℕ}
    (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V) (hv : V.1 ⊆ B ∨ V.1 ⊆ C) :
    CappedLift (rows P hk hnext) h := by
  by_cases he : U = V
  · subst V; exact lift_refl
  rcases hv with hb | hc
  · exact (donorFace P hk hnext).lift hb
      (I.left_mem hU (h.1.trans hb)) (I.left_mem hV hb) h he
      (PointImageSemantics.bountiful _ _ _ _ I.left.complete I.left.bountiful)
  · exact (privateFace P hk hnext).lift hc
      (I.right_mem hU (h.1.trans hc)) (I.right_mem hV hc) h he
      (PointImageSemantics.bountiful _ _ _ _ I.right.complete I.right.bountiful)

include hplan hprev in
theorem private_clause (hface : k ≤ n) : CappedLift (rows P hk hnext)
    (show GradedLe (C, k + 1) (A, k + 1) from ⟨hC.subset, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  let e := fullEquiv I.right I.placeRight I.imageRight (privateFace P hk hnext) (k + 1)
  have hid (d) : CellScheme.below.mono
      (show GradedLe (C, k + 1) (A, k + 1) from ⟨hC.subset, le_rfl⟩) (e d) =
      privateAt P hnext d := by apply Subtype.ext; rfl
  obtain ⟨r, hr, hread, hcap⟩ := LowOnlyPaddedStepOriginalLifts.private_lift
    P hk hnext hplan hprev hface
    ((full_respects_iff I.right I.placeRight I.imageRight
      (privateFace P hk hnext) (k + 1) p).mp hp) hq hγ
    (fun d => by
      change min (q (privateAt P hnext d)) γ = min (p (e d)) γ
      simpa only [hid] using hag (e d))
  refine ⟨r, hr, hcap, ?_⟩
  intro d
  obtain ⟨x, rfl⟩ := e.surjective d
  rw [hid]
  exact hread x

include hplan hprev in
theorem donor_clause (hface : k ≤ n) : CappedLift (rows P hk hnext)
    (show GradedLe (B, k + 1) (A, k + 1) from ⟨hB.subset, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  let e := fullEquiv I.left I.placeLeft I.imageLeft (donorFace P hk hnext) (k + 1)
  have hid (d) : CellScheme.below.mono
      (show GradedLe (B, k + 1) (A, k + 1) from ⟨hB.subset, le_rfl⟩) (e d) =
      donorAt P hnext d := by apply Subtype.ext; rfl
  obtain ⟨r, hr, hread, hcap⟩ := LowOnlyPaddedStepOriginalLifts.donor_lift
    P hk hnext hplan hprev hface
    ((full_respects_iff I.left I.placeLeft I.imageLeft
      (donorFace P hk hnext) (k + 1) p).mp hp) hq hγ
    (fun d => by
      change min (q (donorAt P hnext d)) γ = min (p (e d)) γ
      simpa only [hid] using hag (e d))
  refine ⟨r, hr, hcap, ?_⟩
  intro d
  obtain ⟨x, rfl⟩ := e.surjective d
  rw [hid]
  exact hread x

include hplan hprev hcover in
theorem same_grade {S T : Finset ι}
    (hS : (S, k + 1) ∈ Plan.gradedPlan R) (hT : (T, k + 1) ∈ Plan.gradedPlan R)
    (hST : S ⊆ T) :
    CappedLift (rows P hk hnext)
      (show GradedLe (S, k + 1) (T, k + 1) from ⟨hST, le_rfl⟩) := by
  by_cases ht : T = A
  · subst T
    by_cases hs : S = A
    · subst S; exact lift_refl
    have hjpos := (Plan.mem_gradedPlan.mp hS).2.1
    rcases hcover S (Plan.mem_gradedPlan.mp hS).1 hs with hb | hc
    · have hBj : (B, k + 1) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
        ⟨I.leftPlan_le I.leftScheme.isPlan.domain_mem, hjpos,
          (Plan.mem_gradedPlan.mp hS).2.2.trans (Finset.card_le_card hb)⟩
      have hcard : B.card = n := by
        rw [← I.imageLeft, Finset.card_image_of_injective _ I.placeLeft.injective]
        simp only [Finset.card_univ, Fintype.card_fin]
      have hface : k ≤ n := by
        have ht := (Plan.mem_gradedPlan.mp hBj).2.2
        change k + 1 ≤ B.card at ht
        omega
      exact (inherited_lift P hk hnext hS hBj
        (show GradedLe (S, k + 1) (B, k + 1) from ⟨hb, le_rfl⟩)
        (Or.inl (Finset.Subset.refl _))).comp (donor_clause P hk hnext hplan hprev hface)
    · have hCj : (C, k + 1) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
        ⟨I.rightPlan_le I.rightScheme.isPlan.domain_mem, hjpos,
          (Plan.mem_gradedPlan.mp hS).2.2.trans (Finset.card_le_card hc)⟩
      have hcard : C.card = n := by
        rw [← I.imageRight, Finset.card_image_of_injective _ I.placeRight.injective]
        simp only [Finset.card_univ, Fintype.card_fin]
      have hface : k ≤ n := by
        have ht := (Plan.mem_gradedPlan.mp hCj).2.2
        change k + 1 ≤ C.card at ht
        omega
      exact (inherited_lift P hk hnext hS hCj
        (show GradedLe (S, k + 1) (C, k + 1) from ⟨hc, le_rfl⟩)
        (Or.inr (Finset.Subset.refl _))).comp (private_clause P hk hnext hplan hprev hface)
  · exact inherited_lift P hk hnext hS hT ⟨hST, le_rfl⟩
      (hcover T (Plan.mem_gradedPlan.mp hT).1 ht)

include hplan hprev hcover in
/-- Unrestricted all-cap lifting through the next installed grade. -/
theorem through_successor : TargetGradeLifting.Through (rows P hk hnext) (k + 1) := by
  apply TargetGradeLifting.successor (rows P hk hnext) (lower_lifting P hk hnext hprev)
  intro S T hS hT hST
  apply same_grade P hk hnext hplan hprev hcover _ _ hST
  · change (S, k + 1) ∈ Plan.gradedPlan P.carrier.plan at hS
    rwa [hplan] at hS
  · change (T, k + 1) ∈ Plan.gradedPlan P.carrier.plan at hT
    rwa [hplan] at hT

end
end VaughtConjecture.Knight.LowOnlyPaddedStepLedger
