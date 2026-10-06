/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedLiftingInduction
public import VaughtConjecture.Knight.LowOnlyPaddedEndpoints
public import VaughtConjecture.Knight.OrderedFaceRestriction

/-! # The legal full-height padded LOW scheme

Integration's unchanged coding, ordered faces and whole displays compose with
the closed all-cap induction. Both inputs are literal semantic restrictions,
with their actual occurrence order and every row retained. Scope coverage is
derived for the intended two-coface plan, not asserted for extra mixed scopes.

This packages finite legality and admitted selected sections. It does not
assert stage bounds, separator realization or an exact receiving theorem.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedLegal
open Transform Value ExtOrd AmalgamationPlan LowOnly
open LowOnlyPaddedIteration LowOnlyPaddedInstallation
noncomputable section

/-- An ordered exact face of a legal output is the literal semantic restriction. -/
theorem restrict_eq_of_face {a b : ℕ} (D : SemScheme a) (E : SemScheme b)
    (f : Fin a ↪ Fin b) {T : Finset (Fin b)} (hf : Finset.univ.image f = T)
    (G : ExactSemanticFace (PointImageSemantics.rows D.scheme f hf D.rows) E.rows)
    (hm : StrictMono G.map)
    (hp : Plan.restrictPlan E.scheme.plan T = D.scheme.plan.image (Finset.image f)) :
    E.restrictFace f (OrderedFaceRestriction.visible D E.scheme f hf hp) = D := by
  have he := OrderedFaceRestriction.scheme_eq D E.scheme E.rows f hf G hm hp
  refine SemScheme.ext_of_components (congrArg CellScheme.plan he)
    (congrArg CellScheme.card he) (CellScheme.cell_cast_of_eq he) ?_
  exact OrderedFaceRestriction.row_eq D E.scheme E.rows f hf G hm hp

variable {l m n K : ℕ} {B C : Finset (Fin l)}
  {R : Finset (Finset (Fin l))}
  (I : WholeDonorBoundary.Input Finset.univ B C R m n n)
  (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ (Finset.univ : Finset (Fin l)).card)
  (hB : B ⊂ Finset.univ) (hC : C ⊂ Finset.univ)
  (hcover : ∀ S ∈ R, S ≠ Finset.univ → S ⊆ B ∨ S ⊆ C)

/-- The actual completed carrier, with no supplied output lifting premise. -/
def semScheme : SemScheme l where
  scheme := (build I F hroot hA hB hC
    ((Finset.univ : Finset (Fin l)).card - 2) (by omega)).carrier
  rows := (build I F hroot hA hB hC
    ((Finset.univ : Finset (Fin l)).card - 2) (by omega)).rows
  rows_coded := build_coded I F hroot hA hB hC _ _
  consistent := build_consistent I F hroot hA hB hC _ _
  bountiful := LowOnlyPaddedLiftingInduction.full_bountiful I F hroot hA hB hC hcover
  complete := LowOnlyPaddedLiftingInduction.full_complete I F hroot hA hB hC hcover

local notation "E" => semScheme I F hroot hA hB hC hcover

theorem plan : (E).scheme.plan = R := build_plan I F hroot hA hB hC _ _

def donor : ExactSemanticFace I.leftRows (E).rows :=
  donorFace I F hroot hA hB hC _ _

def privateFace : ExactSemanticFace I.rightRows (E).rows :=
  LowOnlyPaddedInstallation.privateFace I F hroot hA hB hC _ _

theorem donor_plan : Plan.restrictPlan (E).scheme.plan B =
    I.left.scheme.plan.image (Finset.image I.placeLeft) := by
  rw [plan]; exact I.planLeft

theorem private_plan : Plan.restrictPlan (E).scheme.plan C =
    I.right.scheme.plan.image (Finset.image I.placeRight) := by
  rw [plan]; exact I.planRight

theorem donor_visible : Finset.univ.image I.placeLeft ∈ (E).scheme.plan :=
  OrderedFaceRestriction.visible I.left (E).scheme I.placeLeft I.imageLeft
    (donor_plan I F hroot hA hB hC hcover)

theorem private_visible : Finset.univ.image I.placeRight ∈ (E).scheme.plan :=
  OrderedFaceRestriction.visible I.right (E).scheme I.placeRight I.imageRight
    (private_plan I F hroot hA hB hC hcover)

/-- Literal equality includes row data, not just a lower-domain equivalence. -/
theorem restrict_donor :
    (E).restrictFace I.placeLeft (donor_visible I F hroot hA hB hC hcover) = I.left :=
  restrict_eq_of_face I.left (E) I.placeLeft I.imageLeft
    (donor I F hroot hA hB hC hcover) (donor_order I F hroot hA hB hC _ _)
    (donor_plan I F hroot hA hB hC hcover)

theorem restrict_private :
    (E).restrictFace I.placeRight (private_visible I F hroot hA hB hC hcover) = I.right :=
  restrict_eq_of_face I.right (E) I.placeRight I.imageRight
    (privateFace I F hroot hA hB hC hcover) (private_order I F hroot hA hB hC _ _)
    (private_plan I F hroot hA hB hC hcover)

/-- The restriction's canonical enumeration is the installed donor map. -/
theorem donor_occurrence (d : Cell I.left.scheme) :
    CellScheme.restrictFace.toCell (E).scheme I.placeLeft
      (donor_visible I F hroot hA hB hC hcover)
      (Fin.cast (congrArg (fun D : SemScheme n => D.scheme.card)
        (restrict_donor I F hroot hA hB hC hcover)).symm d) =
      (donor I F hroot hA hB hC hcover).map d :=
  OrderedFaceRestriction.toCell_eq I.left (E).scheme (E).rows I.placeLeft I.imageLeft
    (donor I F hroot hA hB hC hcover) (donor_order I F hroot hA hB hC _ _)
    (donor_plan I F hroot hA hB hC hcover) d

theorem private_occurrence (d : Cell I.right.scheme) :
    CellScheme.restrictFace.toCell (E).scheme I.placeRight
      (private_visible I F hroot hA hB hC hcover)
      (Fin.cast (congrArg (fun D : SemScheme n => D.scheme.card)
        (restrict_private I F hroot hA hB hC hcover)).symm d) =
      (privateFace I F hroot hA hB hC hcover).map d :=
  OrderedFaceRestriction.toCell_eq I.right (E).scheme (E).rows I.placeRight I.imageRight
    (privateFace I F hroot hA hB hC hcover) (private_order I F hroot hA hB hC _ _)
    (private_plan I F hroot hA hB hC hcover) d

/-- Admitted native states, including literal top, have actual lawful displays
on the packaged legal scheme. This is not a stage-bound statement. -/
theorem exists_display {S : State I.left I.right}
    (hS : F.Admissible (Finset.univ : Finset (Fin l)).card S) :
    ∃ w : Cell (E).scheme → ExtOrd, RespectsSemantics (E).rows w ∧
      (∀ d, w ((donor I F hroot hA hB hC hcover).map d) = S.u d) ∧
      ∀ d, w ((privateFace I F hroot hA hB hC hcover).map d) = S.v d :=
  LowOnlyPaddedEndpoints.exists_whole_faces I F hroot hA hB hC hS

/-- Coverage is derived from the actual two-coface plan. Extra mixed scopes
cannot be inserted under this specialization without a new lifting argument. -/
def twoCofaces (s : AmalgamatedBoundaryPlan.Step (Finset.univ : Finset (Fin l)))
    (hR : R = s.plan) (hleft : B = Finset.univ.erase s.a)
    (hright : C = Finset.univ.erase s.b) : SemScheme l :=
  semScheme I F hroot hA hB hC
    (LowOnlyPaddedPairLift.cover_two_cofaces s hR hleft hright)

end
end VaughtConjecture.Knight.LowOnlyPaddedLegal
