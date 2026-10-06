/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedPairLift
public import VaughtConjecture.Knight.LowOnlyPaddedRendering
public import VaughtConjecture.Knight.TargetGradeLifting

/-! # Checked lower lifting and incoming rendering on the same padded carrier

The renderer is ported unchanged from integration commit
49f4d94eb2b5fca4a0232e3f96a80f629441b109. Both the lifting invariant and the
incoming semantic contract are now proved on its actual predecessor, not
fields of an assumed successor record. No grade-three layer is installed here.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedLiftingReady
open Transform Value ExtOrd CappedDonor LowOnly AmalgamationPlan
open LowOnlyPaddedSuccessor LowOnlyPaddedRendering
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)

include hcover

theorem through_two : TargetGradeLifting.Through (rows I F hroot hA hB hC) 2 :=
  fun hU hV h hj => LowOnlyPaddedPairLift.lift I F hroot hA hB hC hcover hU hV h hj

/-- Only the actual grade cut is bountiful. This neither fills nor asserts
completeness at higher indices of the full carrier. -/
theorem grade_two_bountiful :
    (GradeCutBoundary.rows (carrier I F hroot hA hB hC) 2
      (rows I F hroot hA hB hC)).IsBountiful :=
  TargetGradeLifting.gradeCut_bountiful _ (by decide)
    (through_two I F hroot hA hB hC hcover)

/-- Integration's selected incoming section and the complete lower lifting
invariant coexist on these exact rows. Properness is required only for the
selected source profile, not for arbitrary physical lifting prescriptions. -/
theorem incoming_ready {j : ℕ} (hj : 2 ≤ j) (S : State I.left I.right)
    (hS : F.Admissible j S) (hp : ∀ d, S.profile d ≠ ⊤)
    {G : Finset ExtOrd} {H : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H) (hHG : H ∈ G)
    (hb : ∀ d, S.profile d ≤ H) :
    RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, j)
      (fun d => render I F hroot hA hB hC hj S hS hp G H d.1) ∧
    TargetGradeLifting.Through (rows I F hroot hA hB hC) 2 ∧
    (∀ d, render I F hroot hA hB hC hj S hS hp G H d ≤ H) ∧
    (∀ d, OrbitPrefixSupport.Supported j (G : Set ExtOrd) S.profile
      (render I F hroot hA hB hC hj S hS hp G H d)) ∧
    ∀ d : Cell I.boundary,
      render I F hroot hA hB hC hj S hS hp G H (original I F hroot hA hB hC d) =
        S.profile (LowOnlyOrderedLadder.field I d) :=
  ⟨render_lawful I F hroot hA hB hC hj S hS hp hG hH hb,
    through_two I F hroot hA hB hC hcover,
    render_bound I F hroot hA hB hC hj S hS hp hH hb,
    render_supported I F hroot hA hB hC hj S hS hp hj hHG,
    render_original I F hroot hA hB hC hj S hS hp hG hH⟩

end
end VaughtConjecture.Knight.LowOnlyPaddedLiftingReady
