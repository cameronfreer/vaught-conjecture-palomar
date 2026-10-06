/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedOriginalLifts
public import VaughtConjecture.Knight.SeparatedLayerFace

/-! # Actual inherited faces of the padded LOW successor

Both source layers retain each proper semantic face, including every inherited
owner domain. No bound on the grades of the old schemes is used.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedFaces
open Transform Value ExtOrd CappedDonor LowOnly AmalgamationPlan CoatomBoundaryExtension
open LowOnlyPaddedSuccessor
noncomputable section

section FullFace
variable {ι : Type*} [DecidableEq ι] {A B : Finset ι} {n : ℕ}
  (P : SemScheme n) (e : Fin n ↪ ι) (he : Finset.univ.image e = B)
  {D : CellScheme A} {sem : Semantics D}
  (G : ExactSemanticFace (PointImageSemantics.rows P.scheme e he P.rows) sem)

/-- Effective full-face domain, retaining the actual occurrence order and values. -/
def fullEquiv (j : ℕ) : P.scheme.below (effC n j) ≃ D.below (B, j) :=
  (show P.scheme.below (effC n j) ≃
      (AmalgamatedBoundary.pointImage P.scheme e he).below (B, j) from {
    toFun := fun d => ⟨d.1,
      (Finset.image_subset_image (Finset.subset_univ _)).trans he.subset,
      d.2.2.trans (min_le_left _ _)⟩
    invFun := fun d => ⟨d.1, Finset.subset_univ _, le_min d.2.2 (gradeC_le d.1)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }).trans (G.belowEquiv (B, j) (Finset.Subset.refl _))

theorem full_respects_iff (j : ℕ) (q : D.below (B, j) → ExtOrd) :
    RespectsSemanticsBelow sem (B, j) q ↔
      RespectsSemanticsBelow P.rows (effC n j) (q ∘ fullEquiv P e he G j) := by
  have h := respects_iff_of_equiv (sem' := P.rows) (sem := sem)
    (fullEquiv P e he G j) (fun d => (congrArg Prod.snd (G.index d.1)).symm)
    (fun d f => ?_) (fun c d _ => ?_)
    (q ∘ fullEquiv P e he G j)
  · simpa only [Function.comp_def, Equiv.apply_symm_apply] using h.symm
  · change P.scheme.scope d.1 ⊆ P.scheme.scope f.1 ↔
      D.scope (G.map d.1) ⊆ D.scope (G.map f.1)
    change (P.scheme.cell d.1).1 ⊆ (P.scheme.cell f.1).1 ↔
      (D.cell (G.map d.1)).1 ⊆ (D.cell (G.map f.1)).1
    rw [G.index d.1, G.index f.1]
    exact (Finset.image_subset_image_iff e.injective).symm
  · exact (G.row c.1 (PointImageSemantics.belowEquiv P.scheme e he c.1 d)).symm

end FullFace

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

def face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows (rows I F hroot hA hB hC) := by
  let J := input I F hroot hA hB hC
  let lowerFace := SeparatedLayerFace.face I.boundary
    (RelativeLadderLayer.Point (X := Field I.left I.right) (Q := F.Anchor 1))
    1 Nat.one_pos (by omega) (RelativeLadderLayer.separated I.boundary
      (LowOnlyOrderedLadder.proper I hB hC)) I.rows J.lowerRows
    (RelativeLadderLayer.inherited_row I.boundary I.rows (by omega)
      (LowOnlyOrderedLadder.field I) (F.fields 1) (LowOnlyOrderedLadder.proper I hB hC)) G hT
  exact SeparatedLayerFace.face J.lower
    (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty)) 2
    (by decide) hA J.separation J.lowerRows J.rows J.inherited_row lowerFace hT

def donorFace : ExactSemanticFace I.leftRows (rows I F hroot hA hB hC) :=
  face I F hroot hA hB hC I.leftFace hB.not_ge

def privateFace : ExactSemanticFace I.rightRows (rows I F hroot hA hB hC) :=
  face I F hroot hA hB hC I.rightFace hC.not_ge

theorem donor_map (d : Cell I.left.scheme) :
    (donorFace I F hroot hA hB hC).map d = original I F hroot hA hB hC (I.leftFace.map d) := rfl

theorem private_map (d : Cell I.right.scheme) :
    (privateFace I F hroot hA hB hC).map d = original I F hroot hA hB hC (I.rightFace.map d) := rfl

/-- All caps, all inherited target grades, and equal indices. -/
theorem inherited_lift {U V : Finset ι × ℕ}
    (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V) (hv : V.1 ⊆ B ∨ V.1 ⊆ C) :
    CappedLift (rows I F hroot hA hB hC) h := by
  by_cases he : U = V
  · subst V; exact lift_refl
  rcases hv with hb | hc
  · exact (donorFace I F hroot hA hB hC).lift hb
      (I.left_mem hU (h.1.trans hb)) (I.left_mem hV hb) h he
      (PointImageSemantics.bountiful _ _ _ _ I.left.complete I.left.bountiful)
  · exact (privateFace I F hroot hA hB hC).lift hc
      (I.right_mem hU (h.1.trans hc)) (I.right_mem hV hc) h he
      (PointImageSemantics.bountiful _ _ _ _ I.right.complete I.right.bountiful)

end
end VaughtConjecture.Knight.LowOnlyPaddedFaces
