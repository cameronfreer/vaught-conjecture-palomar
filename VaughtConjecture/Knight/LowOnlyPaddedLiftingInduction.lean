/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepLedger

/-! # Closed all-cap lifting induction on the installed padded tower

The actual grade-two base initializes the uniform successor ledger. Every
predecessor lifting input is discharged by induction on integration's unchanged
build. Completeness is restricted to installed heights; the ambient-height
output is bountiful and complete.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedLiftingInduction
open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse
open LowOnlyPaddedContract LowOnlyPaddedStepRows LowOnlyOrderedLadder
open LowOnlyPaddedDecode (grid_fixed_below)
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)

open LowOnlyPaddedIteration TargetGradeLifting AmalgamationPlan CoatomBoundaryExtension
include hcover

/-- Closed induction on integration's actual installed recursion. -/
theorem build_lifting (t : ℕ) (ht : t + 2 ≤ A.card) :
    Through (build I F hroot hA hB hC t ht).rows (t + 2) := by
  induction t with
  | zero => exact LowOnlyPaddedLiftingReady.through_two I F hroot hA hB hC hcover
  | succ t ih =>
    exact LowOnlyPaddedStepLedger.through_successor
      (build I F hroot hA hB hC t (by omega)) (by omega) (by omega)
      (build_plan I F hroot hA hB hC t (by omega)) (ih (by omega)) hcover

/-- All permitted original caps on all pairs whose targets are installed. -/
theorem lift (t : ℕ) (ht : t + 2 ≤ A.card) {U V : Finset ι × ℕ}
    (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V) (hv : V.2 ≤ t + 2) :
    CappedLift (build I F hroot hA hB hC t ht).rows h := by
  apply build_lifting I F hroot hA hB hC hcover t ht _ _ h hv
  · rwa [build_plan]
  · rwa [build_plan]

theorem gradeCut_bountiful (t : ℕ) (ht : t + 2 ≤ A.card) :
    (GradeCutBoundary.rows (build I F hroot hA hB hC t ht).carrier (t + 2)
      (build I F hroot hA hB hC t ht).rows).IsBountiful :=
  TargetGradeLifting.gradeCut_bountiful _ (by omega)
    (build_lifting I F hroot hA hB hC hcover t ht)

/-- Grade four is the same proved successor, not a separately designed test. -/
theorem grade_four (ht : 4 ≤ A.card) :
    Through (gradeFour I F hroot hA hB hC ht).rows 4 :=
  build_lifting I F hroot hA hB hC hcover 2 ht

theorem grade_three (ht : 3 ≤ A.card) :
    Through (gradeThree I F hroot hA hB hC ht).rows 3 :=
  build_lifting I F hroot hA hB hC hcover 1 ht

/-- Completeness is asserted only at filled grades. Proper original owners
above this height are retained but no missing full owners are postulated. -/
theorem complete_through (t : ℕ) (ht : t + 2 ≤ A.card) {J : Finset ι × ℕ}
    (hJ : J ∈ Plan.gradedPlan R) (hj : J.2 ≤ t + 2) :
    ∃ d, (build I F hroot hA hB hC t ht).carrier.cell d = J := by
  let L := build I F hroot hA hB hC t ht
  rcases J with ⟨T, j⟩
  by_cases he : T = A
  · subst T
    obtain ⟨a, _⟩ := F.exists_rank_anchor (by omega : 1 ≤ t + 2)
      (F.zero_admissible (t + 2))
    obtain ⟨c, hc, _⟩ := L.ceiling_at le_rfl (state F a)
      (state_admissible F a) (state_proper F a)
      (G := PairedSlotComparison.sourceGrid (t + 2) (Fintype.card (Field I.left I.right)))
      (H := CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right))
      (fun _ hz => PairedSlotComparison.sourceGrid_visible hz)
      (PairedSlotComparison.sourceGrid_visible
        (PairedSlotComparison.sourceGrid_endpoint le_rfl))
      (fun f => by rw [state_profile]; exact LowOnlyRecursiveCharts.anchor_bound F a f)
      j (Plan.mem_gradedPlan.mp hJ).2.1 hj
    exact ⟨c, hc⟩
  · obtain ⟨d, hd⟩ := (I.occupied_iff hJ).mpr (hcover T (Plan.mem_gradedPlan.mp hJ).1 he)
    refine ⟨L.baseMap (RelativeLadderLayer.old I.boundary (by omega) d), ?_⟩
    exact (L.base_index _).trans
      ((RelativeLadderLayer.old_index I.boundary (by omega) d).trans hd)

/-- At the ambient height every permitted graded pair is covered. -/
theorem full_bountiful :
    (build I F hroot hA hB hC (A.card - 2) (by omega)).rows.IsBountiful := by
  intro U V hU hV h _
  have hv : V.2 ≤ A.card - 2 + 2 := by
    have hV' := Plan.mem_gradedPlan.mp hV
    have hscope :=
      (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier.isPlan.subset_of_mem hV'.1
    have hb := hV'.2.2.trans (Finset.card_le_card hscope)
    omega
  exact build_lifting I F hroot hA hB hC hcover (A.card - 2) (by omega) hU hV h hv

theorem full_complete :
    (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier.IsComplete := by
  intro J hJ
  have hJ' := Plan.mem_gradedPlan.mp hJ
  have hscope :=
    (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier.isPlan.subset_of_mem hJ'.1
  have hb := hJ'.2.2.trans (Finset.card_le_card hscope)
  apply complete_through I F hroot hA hB hC hcover (A.card - 2) (by omega) _ (by omega)
  rwa [build_plan] at hJ

omit hcover in
/-- The intended two-coface plan discharges coverage, rather than assuming
that every proper mixed scope is an original face. -/
theorem build_lifting_two_cofaces (s : AmalgamatedBoundaryPlan.Step A)
    (hR : R = s.plan) (hleft : B = A.erase s.a) (hright : C = A.erase s.b)
    (t : ℕ) (ht : t + 2 ≤ A.card) :
    Through (build I F hroot hA hB hC t ht).rows (t + 2) :=
  build_lifting I F hroot hA hB hC
    (LowOnlyPaddedPairLift.cover_two_cofaces s hR hleft hright) t ht

end
end VaughtConjecture.Knight.LowOnlyPaddedLiftingInduction
