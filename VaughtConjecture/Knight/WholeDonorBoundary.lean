/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SemSchemeBoundaryInput
public import VaughtConjecture.Knight.OrderedFaceBoundarySemantics

/-! # The ordered inherited boundary from literal legal input faces

Generalizes `SemSchemeBoundaryInput` beyond coatom geometry, reusing its
restriction-derived face maps. The inputs give actual schemes, a common literal
face, point placements and a common support plan. Shared rows, exact semantic
faces, consistency, coding and lawful pasting are outputs, not hypotheses.

This constructs no mixed owners and does not claim bountifulness of the union.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.WholeDonorBoundary

open AmalgamationPlan Transform Value ExtOrd
open AmalgamatedBoundary (Overlap pointImage pointImage_complete)
open SemSchemeBoundaryInput (faceMap faceMap_index faceMap_exhaustive faceMap_total)
noncomputable section

variable {ι : Type*} [DecidableEq ι] (A B C : Finset ι)
variable (R : Finset (Finset ι))

/-- Two legal inputs on arbitrary faces with one literal common face.
Only point placements, plan restrictions, and input equalities are fields;
output consistency, row compatibility, and lower-domain transport are derived. -/
structure Input (m nL nR : ℕ) where
  isPlan : Plan.IsPlan A R
  left : SemScheme nL
  right : SemScheme nR
  common : SemScheme m
  placeLeft : Fin nL ↪ ι
  placeRight : Fin nR ↪ ι
  imageLeft : Finset.univ.image placeLeft = B
  imageRight : Finset.univ.image placeRight = C
  commonLeft : Fin m ↪ Fin nL
  commonRight : Fin m ↪ Fin nR
  visibleLeft : Finset.univ.image commonLeft ∈ left.scheme.plan
  visibleRight : Finset.univ.image commonRight ∈ right.scheme.plan
  faceLeft : left.restrictFace commonLeft visibleLeft = common
  faceRight : right.restrictFace commonRight visibleRight = common
  commute : commonLeft.trans placeLeft = commonRight.trans placeRight
  intersection : (Finset.univ.image commonLeft).image placeLeft =
    B ∩ C
  planLeft : Plan.restrictPlan R B = left.scheme.plan.image (Finset.image placeLeft)
  planRight : Plan.restrictPlan R C = right.scheme.plan.image (Finset.image placeRight)

namespace Input

variable {A B C R} {m nL nR : ℕ} (I : Input A B C R m nL nR)

abbrev leftScheme := pointImage I.left.scheme I.placeLeft I.imageLeft
abbrev rightScheme := pointImage I.right.scheme I.placeRight I.imageRight
abbrev leftRows := PointImageSemantics.rows I.left.scheme I.placeLeft I.imageLeft I.left.rows
abbrev rightRows := PointImageSemantics.rows I.right.scheme I.placeRight I.imageRight I.right.rows

private theorem common_image_right :
    (Finset.univ.image I.commonRight).image I.placeRight =
      B ∩ C := by
  rw [Finset.image_image, ← I.intersection, Finset.image_image]
  exact congrArg (fun e : Fin m ↪ ι => Finset.univ.image e) I.commute.symm

private theorem image_common (T : Finset (Fin m)) :
    (T.image I.commonLeft).image I.placeLeft =
      (T.image I.commonRight).image I.placeRight := by
  rw [Finset.image_image, Finset.image_image]
  exact congrArg (fun e : Fin m ↪ ι => T.image e) I.commute

/-- The overlap is derived from the actual restricted occurrence enumerations. -/
def shared : Overlap I.leftScheme I.rightScheme I.common.scheme.card where
  f := (faceMap I.left I.common I.commonLeft I.visibleLeft I.faceLeft).toEmbedding
  g := (faceMap I.right I.common I.commonRight I.visibleRight I.faceRight).toEmbedding
  f_mono := (faceMap I.left I.common I.commonLeft I.visibleLeft I.faceLeft).strictMono
  g_mono := (faceMap I.right I.common I.commonRight I.visibleRight I.faceRight).strictMono
  shared d := by
    change ((I.left.scheme.cell
        (faceMap I.left I.common I.commonLeft I.visibleLeft I.faceLeft d)).1.image I.placeLeft,
        (I.left.scheme.cell
          (faceMap I.left I.common I.commonLeft I.visibleLeft I.faceLeft d)).2) =
      ((I.right.scheme.cell
        (faceMap I.right I.common I.commonRight I.visibleRight I.faceRight d)).1.image I.placeRight,
        (I.right.scheme.cell
          (faceMap I.right I.common I.commonRight I.visibleRight I.faceRight d)).2)
    rw [faceMap_index I.left I.common I.commonLeft I.visibleLeft I.faceLeft d,
      faceMap_index I.right I.common I.commonRight I.visibleRight I.faceRight d]
    exact Prod.ext (image_common I _) rfl
  left_exhaustive d hd := by
    apply faceMap_exhaustive
    apply (Finset.image_subset_image_iff I.placeLeft.injective).mp
    rw [I.intersection]
    exact Finset.subset_inter
      ((Finset.image_subset_image (Finset.subset_univ _)).trans
        (Finset.subset_of_eq I.imageLeft)) hd
  right_exhaustive d hd := by
    apply faceMap_exhaustive
    apply (Finset.image_subset_image_iff I.placeRight.injective).mp
    rw [common_image_right I]
    exact Finset.subset_inter hd
      ((Finset.image_subset_image (Finset.subset_univ _)).trans
        (Finset.subset_of_eq I.imageRight))

theorem compatible : OrderedFaceBoundaryRows.Compatible I.leftScheme I.rightScheme
    I.shared I.leftRows I.rightRows := by
  intro c d
  exact (PointImageSemantics.total_eq I.left.scheme I.placeLeft I.imageLeft I.left.rows
    (I.shared.f c) (I.shared.f d)).trans
    (((faceMap_total I.left I.common I.commonLeft I.visibleLeft I.faceLeft c d).trans
      (faceMap_total I.right I.common I.commonRight I.visibleRight I.faceRight c d).symm).trans
      (PointImageSemantics.total_eq I.right.scheme I.placeRight I.imageRight I.right.rows
        (I.shared.g c) (I.shared.g d)).symm)

theorem leftPlan_le : I.leftScheme.plan ⊆ R := by
  intro S hS
  change S ∈ I.left.scheme.plan.image (Finset.image I.placeLeft) at hS
  rw [← I.planLeft] at hS
  exact (Finset.mem_inter.mp hS).1

theorem rightPlan_le : I.rightScheme.plan ⊆ R := by
  intro S hS
  change S ∈ I.right.scheme.plan.image (Finset.image I.placeRight) at hS
  rw [← I.planRight] at hS
  exact (Finset.mem_inter.mp hS).1

abbrev boundary := OrderedFaceBoundary.scheme I.leftScheme I.rightScheme I.shared
  R I.isPlan I.leftPlan_le I.rightPlan_le
abbrev rows := OrderedFaceBoundaryRows.rows I.leftScheme I.rightScheme I.shared
  R I.isPlan I.leftPlan_le I.rightPlan_le I.leftRows I.rightRows I.compatible

def leftFace : ExactSemanticFace I.leftRows I.rows :=
  OrderedFaceBoundarySemantics.leftFace I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le I.leftRows I.rightRows I.compatible

def rightFace : ExactSemanticFace I.rightRows I.rows :=
  OrderedFaceBoundarySemantics.rightFace I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le I.leftRows I.rightRows I.compatible

theorem consistent : I.rows.IsConsistent :=
  OrderedFaceBoundarySemantics.consistent I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le I.leftRows I.rightRows I.compatible
    (PointImageSemantics.consistent _ _ _ _ I.left.consistent)
    (PointImageSemantics.consistent _ _ _ _ I.right.consistent)

theorem coded : I.rows.IsCoded :=
  OrderedFaceBoundarySemantics.coded I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le I.leftRows I.rightRows I.compatible
    (PointImageSemantics.coded _ _ _ _ I.left.rows_coded)
    (PointImageSemantics.coded _ _ _ _ I.right.rows_coded)


theorem left_order : StrictMono I.leftFace.map :=
  OrderedFaceBoundary.left_order I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le

theorem right_order : StrictMono I.rightFace.map :=
  OrderedFaceBoundary.right_order I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le

theorem shared_cell (d : Cell I.common.scheme) :
    I.leftFace.map (I.shared.f d) = I.rightFace.map (I.shared.g d) :=
  OrderedFaceBoundaryRows.shared_cell I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le d

/-- A complete target vector is lawful precisely when both literal inputs are. -/
theorem respects_iff (p : Cell I.boundary → ExtOrd) :
    RespectsSemantics I.rows p ↔
      RespectsSemantics I.left.rows (p ∘ I.leftFace.map) ∧
      RespectsSemantics I.right.rows (p ∘ I.rightFace.map) := by
  rw [OrderedFaceBoundarySemantics.respects_iff]
  exact and_congr
    (PointImageSemantics.respects_iff _ _ _ _ _)
    (PointImageSemantics.respects_iff _ _ _ _ _)

def paste (p : Cell I.left.scheme → ExtOrd) (q : Cell I.right.scheme → ExtOrd) :
    Cell I.boundary → ExtOrd :=
  OrderedFaceBoundarySemantics.paste I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le p q

theorem paste_left (p : Cell I.left.scheme → ExtOrd) (q : Cell I.right.scheme → ExtOrd)
    (d : Cell I.left.scheme) : I.paste p q (I.leftFace.map d) = p d :=
  OrderedFaceBoundarySemantics.paste_left I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le p q d

theorem paste_right (p : Cell I.left.scheme → ExtOrd) (q : Cell I.right.scheme → ExtOrd)
    (h : ∀ i, p (I.shared.f i) = q (I.shared.g i)) (d : Cell I.right.scheme) :
    I.paste p q (I.rightFace.map d) = q d :=
  OrderedFaceBoundarySemantics.paste_right I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le p q h d

/-- The selected inherited display needs agreement only on the literal common face. -/
theorem paste_respects {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
    (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
    (h : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    RespectsSemantics I.rows (I.paste p q) := by
  apply (I.respects_iff _).mpr
  constructor
  · have he : I.paste p q ∘ I.leftFace.map = p := funext (I.paste_left p q)
    exact he.symm ▸ hp
  · have he : I.paste p q ∘ I.rightFace.map = q := funext (I.paste_right p q h)
    exact he.symm ▸ hq

/-- No selected source inventory is needed to paste arbitrary compatible lawful inputs. -/
theorem exists_section {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
    (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
    (h : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∃ t, RespectsSemantics I.rows t ∧
      (∀ d, t (I.leftFace.map d) = p d) ∧ ∀ d, t (I.rightFace.map d) = q d :=
  ⟨I.paste p q, I.paste_respects hp hq h, I.paste_left p q, I.paste_right p q h⟩

theorem left_mem {J : Finset ι × ℕ} (hJ : J ∈ Plan.gradedPlan R) (hB : J.1 ⊆ B) :
    J ∈ Plan.gradedPlan I.leftScheme.plan := by
  obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp hJ
  refine Plan.mem_gradedPlan.mpr ⟨?_, hp, hc⟩
  change J.1 ∈ I.left.scheme.plan.image (Finset.image I.placeLeft)
  rw [← I.planLeft]
  exact Finset.mem_inter.mpr ⟨hm, Finset.mem_powerset.mpr hB⟩

theorem right_mem {J : Finset ι × ℕ} (hJ : J ∈ Plan.gradedPlan R) (hC : J.1 ⊆ C) :
    J ∈ Plan.gradedPlan I.rightScheme.plan := by
  obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp hJ
  refine Plan.mem_gradedPlan.mpr ⟨?_, hp, hc⟩
  change J.1 ∈ I.right.scheme.plan.image (Finset.image I.placeRight)
  rw [← I.planRight]
  exact Finset.mem_inter.mpr ⟨hm, Finset.mem_powerset.mpr hC⟩

/-- Exactly the old point scopes are occupied; no mixed owner is hidden in this boundary. -/
theorem occupied_iff {J : Finset ι × ℕ} (hJ : J ∈ Plan.gradedPlan R) :
    (∃ d, I.boundary.cell d = J) ↔ J.1 ⊆ B ∨ J.1 ⊆ C := by
  constructor
  · rintro ⟨d, rfl⟩
    rcases OrderedFaceBoundaryRows.covered I.leftScheme I.rightScheme I.shared
      R I.isPlan I.leftPlan_le I.rightPlan_le d with ⟨d, rfl⟩ | ⟨d, rfl⟩
    · exact Or.inl (by
        rw [OrderedFaceBoundary.left_index]
        exact I.leftScheme.isPlan.subset_of_mem (I.leftScheme.scope_mem_plan d))
    · exact Or.inr (by
        rw [OrderedFaceBoundary.right_index]
        exact I.rightScheme.isPlan.subset_of_mem (I.rightScheme.scope_mem_plan d))
  · intro h
    apply OrderedFaceBoundary.complete_on_input I.leftScheme I.rightScheme I.shared
      R I.isPlan I.leftPlan_le I.rightPlan_le
      (pointImage_complete _ _ _ I.left.complete)
      (pointImage_complete _ _ _ I.right.complete)
    exact h.imp (I.left_mem hJ) (I.right_mem hJ)

/-- Every lifting problem whose upper scope stays inside either original face
is inherited at the original cap, for arbitrary lawful target-local ambients. -/
theorem inherited_lift {CI BJ : Finset ι × ℕ}
    (hCI : CI ∈ Plan.gradedPlan R) (hBJ : BJ ∈ Plan.gradedPlan R)
    (h : GradedLe CI BJ) (hne : CI ≠ BJ) (hscope : BJ.1 ⊆ B ∨ BJ.1 ⊆ C)
    (p : I.boundary.below CI → ExtOrd) (q : I.boundary.below BJ → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow I.rows CI p) (hq : RespectsSemanticsBelow I.rows BJ q)
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ)
    (ha : ∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q', RespectsSemanticsBelow I.rows BJ q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      ∀ d, q' (CellScheme.below.mono h d) = p d := by
  rcases hscope with hl | hr
  · exact I.leftFace.lift hl (I.left_mem hCI (h.1.trans hl)) (I.left_mem hBJ hl) h hne
      (PointImageSemantics.bountiful _ _ _ _ I.left.complete I.left.bountiful)
      p q γ hp hq hγ ha
  · exact I.rightFace.lift hr (I.right_mem hCI (h.1.trans hr)) (I.right_mem hBJ hr) h hne
      (PointImageSemantics.bountiful _ _ _ _ I.right.complete I.right.bountiful)
      p q γ hp hq hγ ha

end Input
end
end VaughtConjecture.Knight.WholeDonorBoundary
