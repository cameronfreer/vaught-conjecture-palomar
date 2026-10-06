/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoatomBoundaryPresentation
public import VaughtConjecture.Knight.CanonicalRecursiveInitialized
public import VaughtConjecture.Knight.CanonicalRecursiveCoverage

/-! # Initialized grade recursion from actual legal coatom inputs

The input schemes supply every proper-boundary hypothesis. The output is
consistent and bountiful at all nominal grades, and complete through the
coatom height. The missing highest full index and ordered stage-labelled
installation are separate obligations.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CoatomRecursiveInput
open AmalgamationPlan AmalgamatedBoundaryPlan SemSchemeBoundaryInput
open Transform Value ExtOrd CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {s : Step A}

theorem oldLifts {m nL nR : ℕ} (I : Input s m nL nR) :
    CanonicalCoatomBountiful.OldLifts I.rows := by
  intro CI BJ hCI hBJ hB h
  by_cases he : CI = BJ
  · subst BJ
    exact lift_refl
  · exact I.proper_lift hCI hBJ h he hB

variable {m n : ℕ} (I : Input s m (n + 3) (n + 3))

include I in
theorem height_le : n + 3 ≤ A.card := by
  rw [← I.card_left]
  exact Finset.card_le_card (Finset.erase_subset _ _)

abbrev scheme := CanonicalRecursiveContract.carrier I.rows n (height_le I)
abbrev rows := CanonicalRecursiveSemantics.rows I.rows I.proper n (height_le I)

theorem ready : CanonicalRecursiveRecurrence.Ready I.rows I.proper n (height_le I) := by
  apply CanonicalRecursiveInitialized.ready I.rows I.proper I.consistent (oldLifts I)
    I.left_visible I.right_visible
    (fun h => Finset.notMem_erase s.a A (h.symm ▸ s.ha))
    (fun h => Finset.notMem_erase s.b A (h.symm ▸ s.hb))
    I.intersection_visible (fun _ hC hCA => I.proper_scope_cover hC hCA)
    n (height_le I) (by rw [I.card_left]) (by rw [I.card_right])
  intro C hC hCA j hj hjC _
  exact I.complete_proper (Plan.mem_gradedPlan.mpr ⟨hC, hj, hjC⟩) hCA

theorem consistent : (rows I).IsConsistent :=
  CanonicalRecursiveSemantics.consistent I.rows I.proper I.consistent n (height_le I)

theorem grade_bound (d : Cell (scheme I)) : (scheme I).grade d ≤ n + 3 :=
  CanonicalRecursiveCoverage.grade_bound I.rows (n + 3) (height_le I)
    (fun d => by simpa only [max_self] using I.grade_le d) d

/-- Effective nominal grades are included; no cap is raised. -/
theorem bountiful : (rows I).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade (grade_bound I) (by omega)
  intro C B j hC hB hj hCB
  apply (GradeCutLifting.lift_iff (rows I) (n + 3)
    (I := (C, j)) (J := (B, j)) ⟨hCB, le_rfl⟩ hj).mp
  exact lift_of_bountiful (ready I).2 hC hB ⟨hCB, le_rfl⟩

theorem complete_through (J : Finset ι × ℕ)
    (hJ : J ∈ Plan.gradedPlan (scheme I).plan) (hj : J.2 ≤ n + 3) :
    ∃ d, (scheme I).cell d = J :=
  CanonicalRecursiveCoverage.complete_through I.rows (n + 3) (height_le I)
    (fun _ h hA => I.complete_proper h hA) J hJ hj

/-- Arbitrary compatible legal coatom types initialize the entire recursion;
no overlap, old-lifting, completeness, or source-section premise is supplied. -/
theorem of_compatible {α : Ordinal.{0}} (C : CoatomPair (n + 2))
    {pa pb : S α (n + 3)} (h : C.Compatible pa pb) :
    let I := (CoatomBoundaryPresentation.of_compatible C h).input
    (rows I).IsConsistent ∧ (rows I).IsBountiful ∧
      ∀ J ∈ Plan.gradedPlan (scheme I).plan, J.2 ≤ n + 3 →
        ∃ d, (scheme I).cell d = J :=
  ⟨consistent _, bountiful _, complete_through _⟩

end
end VaughtConjecture.Knight.CoatomRecursiveInput
