/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedOriginalInduction
public import VaughtConjecture.Knight.SeparatedLayerFace

/-! # Literal original faces of every installed growth layer

The geometric argument follows LowOnlyPaddedStepFaces, with actual growth
occurrences and rows. No selected-rendering equality or LOW fibre is used.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedLayerFaces
open Transform Value ExtOrd Growth GrowthOrderedBase
open GrowthPaddedContract AmalgamationPlan CoatomBoundaryExtension
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k)

/-- Literal faces survive the entire installed tower, not just its field readings. -/
def layerFace {S : Finset ι} {E : CellScheme S} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ S) :
    ExactSemanticFace oldRows P.rows := by
  let L := SeparatedLayerFace.face I.boundary
    (RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1))
    1 Nat.one_pos (by omega) (RelativeLadderLayer.separated I.boundary
      (GrowthOrderedBase.proper I hB hC)) I.rows (baseRows I X T hA hB hC)
    (RelativeLadderLayer.inherited_row I.boundary I.rows (by omega)
      (field I) (GrowthHigherSources.fields X 1) (GrowthOrderedBase.proper I hB hC)) G hT
  exact {
    map := L.map.trans ⟨P.baseMap, P.base_mono.injective⟩
    index := fun d => (P.base_index _).trans (L.index d)
    exhaustive := fun z hz => by
      rcases P.cases z with ⟨d, rfl⟩ | ⟨hs, _, _⟩
      · obtain ⟨c, rfl⟩ := L.exhaustive d (by
          change (P.carrier.cell (P.baseMap d)).1 ⊆ S at hz
          rwa [P.base_index] at hz)
        exact ⟨c, rfl⟩
      · exact False.elim (hT (hs ▸ hz))
    row := fun c d => (P.base_row (L.map c)
      ⟨L.map d.1, by rw [L.index, L.index]; exact d.2⟩).trans (L.row c d) }

def privateFace : ExactSemanticFace I.rightRows P.rows :=
  layerFace P I.rightFace hC.not_ge

def donorFace : ExactSemanticFace I.leftRows P.rows :=
  layerFace P I.leftFace hB.not_ge

theorem private_map (d : Cell I.right.scheme) :
    (privateFace P).map d =
      P.baseMap (RelativeLadderLayer.old I.boundary (by omega) (I.rightFace.map d)) := rfl

theorem donor_map (d : Cell I.left.scheme) :
    (donorFace P).map d =
      P.baseMap (RelativeLadderLayer.old I.boundary (by omega) (I.leftFace.map d)) := rfl

theorem inherited_lift {U V : Finset ι × ℕ}
    (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V) (hv : V.1 ⊆ B ∨ V.1 ⊆ C) :
    CappedLift P.rows h := by
  by_cases he : U = V
  · subst V; exact lift_refl
  rcases hv with hb | hc
  · exact (donorFace P).lift hb
      (I.left_mem hU (h.1.trans hb)) (I.left_mem hV hb) h he
      (PointImageSemantics.bountiful _ _ _ _ I.left.complete I.left.bountiful)
  · exact (privateFace P).lift hc
      (I.right_mem hU (h.1.trans hc)) (I.right_mem hV hc) h he
      (PointImageSemantics.bountiful _ _ _ _ I.right.complete I.right.bountiful)

section FullFace
variable {κ : Type*} [DecidableEq κ] {U V : Finset κ} {a : ℕ}
  (S : SemScheme a) (e : Fin a ↪ κ) (he : Finset.univ.image e = V)
  {D : CellScheme U} {sem : Semantics D}
  (G : ExactSemanticFace (PointImageSemantics.rows S.scheme e he S.rows) sem)

/-- Literal full original face at a nominal cutoff, even above its arity. -/
def fullEquiv (j : ℕ) : S.scheme.below (Finset.univ, j) ≃ D.below (V, j) :=
  (show S.scheme.below (Finset.univ, j) ≃
      (AmalgamatedBoundary.pointImage S.scheme e he).below (V, j) from {
    toFun := fun d => ⟨d.1,
      (Finset.image_subset_image (Finset.subset_univ _)).trans he.subset, d.2.2⟩
    invFun := fun d => ⟨d.1, Finset.subset_univ _, d.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }).trans (G.belowEquiv (V, j) (Finset.Subset.refl _))

theorem full_respects_iff (j : ℕ) (q : D.below (V, j) → ExtOrd) :
    RespectsSemanticsBelow sem (V, j) q ↔
      RespectsSemanticsBelow S.rows (Finset.univ, j) (q ∘ fullEquiv S e he G j) := by
  have h := respects_iff_of_equiv (sem' := S.rows) (sem := sem)
    (fullEquiv S e he G j) (fun d => (congrArg Prod.snd (G.index d.1)).symm)
    (fun d f => ?_) (fun c d _ => ?_) (q ∘ fullEquiv S e he G j)
  · simpa only [Function.comp_def, Equiv.apply_symm_apply] using h.symm
  · change S.scheme.scope d.1 ⊆ S.scheme.scope f.1 ↔
      D.scope (G.map d.1) ⊆ D.scope (G.map f.1)
    change (S.scheme.cell d.1).1 ⊆ (S.scheme.cell f.1).1 ↔
      (D.cell (G.map d.1)).1 ⊆ (D.cell (G.map f.1)).1
    rw [G.index d.1, G.index f.1]
    exact (Finset.image_subset_image_iff e.injective).symm
  · exact (G.row c.1 (PointImageSemantics.belowEquiv S.scheme e he c.1 d)).symm
end FullFace

end
end VaughtConjecture.Knight.GrowthPaddedLayerFaces
