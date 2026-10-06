/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedInstallation
public import VaughtConjecture.Knight.LowOnlyPaddedStepSupply
public import VaughtConjecture.Knight.LowOnlyPaddedLiftingReady

/-! # Closed recursive LOW installation endpoints

The actual recursive outputs preserve KVC's checked grade-two lifting ledger.
They also admit native sections, including literal top, at every constructed
height. At full height this supplies a lawful whole display on the coded,
consistent, complete carrier, with both original faces literal. Higher lifting
and the separator readback remain separate; no legal probe is packaged here.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedEndpoints
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedInstallation
open AmalgamationPlan
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

section Step
variable {I F hroot hA hB hC} {k r : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

/-- The actual row identities discharge all generic transport premises. -/
theorem successor_through (hr : r ≤ k) (hl : TargetGradeLifting.Through P.rows r) :
    TargetGradeLifting.Through (successor P hk hnext).rows r :=
  TargetGradeLifting.through_separated P.rows (F.Anchor (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated I F hroot hA hB hC (by omega))
    (LowOnlyPaddedStepRows.rows P hk hnext)
    (LowOnlyPaddedStepRows.inherited_row P hk hnext) (by omega) hl
end Step

theorem through_two (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)
    (t : ℕ) (ht : t + 2 ≤ A.card) :
    TargetGradeLifting.Through (build I F hroot hA hB hC t ht).rows 2 := by
  induction t with
  | zero => exact LowOnlyPaddedLiftingReady.through_two I F hroot hA hB hC hcover
  | succ t ih =>
    exact successor_through (build I F hroot hA hB hC t (by omega))
      (by omega) ht (by omega) (ih (by omega))

theorem grade_two_bountiful (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)
    (t : ℕ) (ht : t + 2 ≤ A.card) :
    (GradeCutBoundary.rows (build I F hroot hA hB hC t ht).carrier 2
      (build I F hroot hA hB hC t ht).rows).IsBountiful :=
  TargetGradeLifting.gradeCut_bountiful (build I F hroot hA hB hC t ht).rows (r := 2) (by decide)
    (through_two I F hroot hA hB hC hcover t ht)

def original (t : ℕ) (ht : t + 2 ≤ A.card) (d : Cell I.boundary) :
    Cell (build I F hroot hA hB hC t ht).carrier :=
  (build I F hroot hA hB hC t ht).baseMap
    (RelativeLadderLayer.old I.boundary (by omega) d)

theorem original_index (t : ℕ) (ht : t + 2 ≤ A.card) (d : Cell I.boundary) :
    (build I F hroot hA hB hC t ht).carrier.cell (original I F hroot hA hB hC t ht d) =
      I.boundary.cell d :=
  ((build I F hroot hA hB hC t ht).base_index _).trans
    (RelativeLadderLayer.old_index I.boundary (by omega) d)

theorem exists_native_section (t : ℕ) (ht : t + 2 ≤ A.card)
    {S : State I.left I.right} (hS : F.Admissible (t + 2) S) :
    ∃ w, RespectsSemanticsBelow (build I F hroot hA hB hC t ht).rows (A, t + 2) w ∧
      ∀ d : I.boundary.below (A, t + 2),
        w ⟨original I F hroot hA hB hC t ht d.1, by rw [original_index]; exact d.2⟩ =
          S.profile (field I d.1) := by
  cases t with
  | zero => exact LowOnlyPaddedSupply.exists_section I F hroot hA hB hC hS
  | succ t =>
    exact LowOnlyPaddedStepSupply.exists_section
      (build I F hroot hA hB hC t (by omega)) (by omega) ht hS

/-- Literal whole displays on the full-height output. This is an existence
theorem for sections, not arbitrary-ambient cap lifting or a stage-bound claim. -/
theorem exists_whole_section {S : State I.left I.right} (hS : F.Admissible A.card S) :
    ∃ w : Cell (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier → ExtOrd,
      RespectsSemantics (build I F hroot hA hB hC (A.card - 2) (by omega)).rows w ∧
      ∀ d : Cell I.boundary,
        w (original I F hroot hA hB hC (A.card - 2) (by omega) d) = S.profile (field I d) := by
  have hn : A.card - 2 + 2 = A.card := by omega
  obtain ⟨w, hw, hread⟩ := exists_native_section I F hroot hA hB hC
    (A.card - 2) (by omega) (hn.symm ▸ hS)
  let D := (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier
  have hall (d : Cell D) : GradedLe (D.cell d) (A, A.card - 2 + 2) := by
    have hs := D.isPlan.subset_of_mem (D.scope_mem_plan d)
    exact ⟨hs, ((D.grade_le_card_scope d).trans (Finset.card_le_card hs)).trans_eq hn.symm⟩
  refine ⟨fun d => w ⟨d, hall d⟩, hw.toRespects hall, ?_⟩
  intro d
  have hd : GradedLe (I.boundary.cell d) (A, A.card - 2 + 2) := by
    have hs := I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan d)
    exact ⟨hs, ((I.boundary.grade_le_card_scope d).trans
      (Finset.card_le_card hs)).trans_eq hn.symm⟩
  exact hread ⟨d, hd⟩

/-- Both actual ordered faces, not merely numerical readout functions, retain
the selected original labels in the whole display. -/
theorem exists_whole_faces {S : State I.left I.right} (hS : F.Admissible A.card S) :
    ∃ w : Cell (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier → ExtOrd,
      RespectsSemantics (build I F hroot hA hB hC (A.card - 2) (by omega)).rows w ∧
      (∀ d, w ((donorFace I F hroot hA hB hC (A.card - 2) (by omega)).map d) = S.u d) ∧
      ∀ d, w ((privateFace I F hroot hA hB hC (A.card - 2) (by omega)).map d) = S.v d := by
  obtain ⟨w, hw, hread⟩ := exists_whole_section I F hroot hA hB hC hS
  refine ⟨w, hw, ?_, ?_⟩
  · intro d
    rw [donorFace, face_map]
    exact (hread (I.leftFace.map d)).trans
      ((field_read I S (I.leftFace.map d)).trans (I.paste_left S.u S.v d))
  · intro d
    rw [privateFace, face_map]
    exact (hread (I.rightFace.map d)).trans
      (field_private I F hroot
        (LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega) hS) d)

end
end VaughtConjecture.Knight.LowOnlyPaddedEndpoints
