/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PointImageBountiful
public import VaughtConjecture.Knight.AmalgamatedBoundarySemantics

/-! # Proper boundary from two compatible legal input schemes

The inputs are two actual `SemScheme`s, their point placements, and literal
equality of their common face. Shared occurrence maps and row compatibility
are constructed from restriction; no semantic transport or lifting clause is
an input. The resulting boundary retains all old occurrences and is complete
at proper indices. It has no full-scope cells and is not yet an amalgam.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.SemSchemeBoundaryInput

open AmalgamationPlan AmalgamatedBoundaryPlan AmalgamatedBoundary
open Transform Value ExtOrd

noncomputable section

section Face

variable {m n : ℕ} (D : SemScheme n) (F : SemScheme m) (f : Fin m ↪ Fin n)
  (hv : Finset.univ.image f ∈ D.scheme.plan) (hf : D.restrictFace f hv = F)

/-- The original ordered occurrence map, transported through literal face equality. -/
def faceMap : Cell F.scheme ↪o Cell D.scheme := by
  subst F
  exact CellScheme.restrictFace.toCell D.scheme f hv

theorem faceMap_index (d : Cell F.scheme) :
    D.scheme.cell (faceMap D F f hv hf d) =
      ((F.scheme.scope d).image f, F.scheme.grade d) := by
  subst F
  exact (CellScheme.restrictFace.pushGraded_cell D.scheme f hv d).symm

theorem faceMap_exhaustive (d : Cell D.scheme)
    (hd : D.scheme.scope d ⊆ Finset.univ.image f) :
    ∃ i, faceMap D F f hv hf i = d := by
  subst F
  exact CellScheme.restrictFace.exists_toCell_eq D.scheme f hv hd

/-- Equality includes every actual shared row argument, and bottom outside its lower set. -/
theorem faceMap_total (c d : Cell F.scheme) :
    AmalgamatedBoundaryRows.total D.rows (faceMap D F f hv hf c)
      (faceMap D F f hv hf d) = AmalgamatedBoundaryRows.total F.rows c d := by
  subst F
  classical
  change AmalgamatedBoundaryRows.total D.rows
      (CellScheme.restrictFace.toCell D.scheme f hv c)
      (CellScheme.restrictFace.toCell D.scheme f hv d) = _
  by_cases h : GradedLe ((D.restrictFace f hv).scheme.cell d)
      ((D.restrictFace f hv).scheme.cell c)
  · have h' := CellScheme.restrictFace.gradedLe_of_restrictFace D.scheme f hv h
    rw [AmalgamatedBoundaryRows.total_below _ _ ⟨_, h'⟩,
      AmalgamatedBoundaryRows.total_below _ _ ⟨_, h⟩]
    rfl
  · rw [AmalgamatedBoundaryRows.total_outside _ _ _ h,
      AmalgamatedBoundaryRows.total_outside _ _ _ (fun h' =>
        h ((CellScheme.restrictFace.gradedLe_restrictFace_iff D.scheme f hv).mpr h'))]

end Face

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (s : Step A)

/-- Geometric presentation of two legal coatom inputs with one literal common face.
There are no output consistency, completion, or lifting fields. -/
structure Input (m nL nR : ℕ) where
  left : SemScheme nL
  right : SemScheme nR
  common : SemScheme m
  placeLeft : Fin nL ↪ ι
  placeRight : Fin nR ↪ ι
  imageLeft : Finset.univ.image placeLeft = A.erase s.a
  imageRight : Finset.univ.image placeRight = A.erase s.b
  commonLeft : Fin m ↪ Fin nL
  commonRight : Fin m ↪ Fin nR
  visibleLeft : Finset.univ.image commonLeft ∈ left.scheme.plan
  visibleRight : Finset.univ.image commonRight ∈ right.scheme.plan
  faceLeft : left.restrictFace commonLeft visibleLeft = common
  faceRight : right.restrictFace commonRight visibleRight = common
  commute : commonLeft.trans placeLeft = commonRight.trans placeRight
  intersection : (Finset.univ.image commonLeft).image placeLeft =
    A.erase s.a ∩ A.erase s.b
  planLeft : left.scheme.plan.image (Finset.image placeLeft) = s.left
  planRight : right.scheme.plan.image (Finset.image placeRight) = s.right

namespace Input

variable {s} {m nL nR : ℕ} (I : Input s m nL nR)

abbrev leftScheme := pointImage I.left.scheme I.placeLeft I.imageLeft
abbrev rightScheme := pointImage I.right.scheme I.placeRight I.imageRight
abbrev leftRows := PointImageSemantics.rows I.left.scheme I.placeLeft I.imageLeft I.left.rows
abbrev rightRows := PointImageSemantics.rows I.right.scheme I.placeRight I.imageRight I.right.rows

private theorem common_image_right :
    (Finset.univ.image I.commonRight).image I.placeRight =
      A.erase s.a ∩ A.erase s.b := by
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
      (by rw [← I.imageLeft]; exact Finset.image_subset_image (Finset.subset_univ _)) hd
  right_exhaustive d hd := by
    apply faceMap_exhaustive
    apply (Finset.image_subset_image_iff I.placeRight.injective).mp
    rw [common_image_right I]
    exact Finset.subset_inter hd
      (by rw [← I.imageRight]; exact Finset.image_subset_image (Finset.subset_univ _))

theorem compatible : AmalgamatedBoundaryRows.Compatible s I.leftScheme I.rightScheme
    I.shared I.leftRows I.rightRows := by
  intro c d
  exact (PointImageSemantics.total_eq I.left.scheme I.placeLeft I.imageLeft I.left.rows
    (I.shared.f c) (I.shared.f d)).trans
    (((faceMap_total I.left I.common I.commonLeft I.visibleLeft I.faceLeft c d).trans
      (faceMap_total I.right I.common I.commonRight I.visibleRight I.faceRight c d).symm).trans
      (PointImageSemantics.total_eq I.right.scheme I.placeRight I.imageRight I.right.rows
        (I.shared.g c) (I.shared.g d)).symm)

abbrev boundary := AmalgamatedBoundary.scheme s I.leftScheme I.rightScheme I.shared
  I.planLeft I.planRight
abbrev rows := AmalgamatedBoundaryRows.rows s I.leftScheme I.rightScheme I.shared
  I.planLeft I.planRight I.leftRows I.rightRows I.compatible

def leftFace : ExactSemanticFace I.leftRows I.rows :=
  AmalgamatedBoundarySemantics.leftFace s I.leftScheme I.rightScheme I.shared
    I.planLeft I.planRight I.leftRows I.rightRows I.compatible

def rightFace : ExactSemanticFace I.rightRows I.rows :=
  AmalgamatedBoundarySemantics.rightFace s I.leftScheme I.rightScheme I.shared
    I.planLeft I.planRight I.leftRows I.rightRows I.compatible

theorem consistent : I.rows.IsConsistent :=
  AmalgamatedBoundarySemantics.consistent s I.leftScheme I.rightScheme I.shared
    I.planLeft I.planRight I.leftRows I.rightRows I.compatible
    (PointImageSemantics.consistent _ _ _ _ I.left.consistent)
    (PointImageSemantics.consistent _ _ _ _ I.right.consistent)

theorem coded : I.rows.IsCoded :=
  AmalgamatedBoundarySemantics.coded s I.leftScheme I.rightScheme I.shared
    I.planLeft I.planRight I.leftRows I.rightRows I.compatible
    (PointImageSemantics.coded _ _ _ _ I.left.rows_coded)
    (PointImageSemantics.coded _ _ _ _ I.right.rows_coded)

theorem proper (d : Cell I.boundary) : I.boundary.scope d ≠ A :=
  AmalgamatedBoundary.scope_proper s I.leftScheme I.rightScheme I.shared
    I.planLeft I.planRight d

theorem complete_proper {J : Finset ι × ℕ} (hJ : J ∈ Plan.gradedPlan I.boundary.plan)
    (hproper : J.1 ≠ A) : ∃ d, I.boundary.cell d = J :=
  AmalgamatedBoundary.complete_proper s I.leftScheme I.rightScheme I.shared
    I.planLeft I.planRight
    (pointImage_complete _ _ _ I.left.complete)
    (pointImage_complete _ _ _ I.right.complete) hJ hproper

theorem covered (d : Cell I.boundary) :
    I.boundary.scope d ⊆ A.erase s.a ∨ I.boundary.scope d ⊆ A.erase s.b := by
  rcases AmalgamatedBoundaryRows.covered s I.leftScheme I.rightScheme I.shared
    I.planLeft I.planRight d with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · exact Or.inl (by
      change (I.boundary.cell _).1 ⊆ _
      rw [AmalgamatedBoundary.left_index s I.leftScheme I.rightScheme I.shared
        I.planLeft I.planRight d]
      exact I.leftScheme.isPlan.subset_of_mem (I.leftScheme.scope_mem_plan d))
  · exact Or.inr (by
      change (I.boundary.cell _).1 ⊆ _
      rw [AmalgamatedBoundary.right_index s I.leftScheme I.rightScheme I.shared
        I.planLeft I.planRight d]
      exact I.rightScheme.isPlan.subset_of_mem (I.rightScheme.scope_mem_plan d))

theorem grade_le (d : Cell I.boundary) : I.boundary.grade d ≤ max nL nR := by
  rcases AmalgamatedBoundaryRows.covered s I.leftScheme I.rightScheme I.shared
    I.planLeft I.planRight d with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · change (I.boundary.cell _).2 ≤ _
    rw [AmalgamatedBoundary.left_index s I.leftScheme I.rightScheme I.shared
      I.planLeft I.planRight d]
    have hd : I.left.scheme.grade d ≤ nL := by
      simpa using (I.left.scheme.grade_le_card_scope d).trans (Finset.card_le_univ _)
    exact hd.trans (le_max_left _ _)
  · change (I.boundary.cell _).2 ≤ _
    rw [AmalgamatedBoundary.right_index s I.leftScheme I.rightScheme I.shared
      I.planLeft I.planRight d]
    have hd : I.right.scheme.grade d ≤ nR := by
      simpa using (I.right.scheme.grade_le_card_scope d).trans (Finset.card_le_univ _)
    exact hd.trans (le_max_right _ _)

include I in
theorem card_left : (A.erase s.a).card = nL := by
  rw [← I.imageLeft, Finset.card_image_of_injective _ I.placeLeft.injective]
  exact Finset.card_fin nL

include I in
theorem card_right : (A.erase s.b).card = nR := by
  rw [← I.imageRight, Finset.card_image_of_injective _ I.placeRight.injective]
  exact Finset.card_fin nR

theorem left_visible : A.erase s.a ∈ I.boundary.plan :=
  Finset.mem_union_left _ (Finset.mem_union_left _ s.left_plan.domain_mem)

theorem right_visible : A.erase s.b ∈ I.boundary.plan :=
  Finset.mem_union_left _ (Finset.mem_union_right _ s.right_plan.domain_mem)

theorem intersection_visible : A.erase s.a ∩ A.erase s.b ∈ I.boundary.plan := by
  rw [AmalgamatedBoundaryPlan.erased_inter s]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ s.common_left)

theorem proper_scope_cover {C : Finset ι} (hC : C ∈ I.boundary.plan) (hne : C ≠ A) :
    C ⊆ A.erase s.a ∨ C ⊆ A.erase s.b := by
  change C ∈ s.left ∪ s.right ∪ {A} at hC
  rcases Finset.mem_union.mp hC with hC | hC
  · exact (Finset.mem_union.mp hC).imp s.left_plan.subset_of_mem s.right_plan.subset_of_mem
  · exact False.elim (hne (Finset.mem_singleton.mp hC))

/-- The proper-target lifting hypotheses come from the original legal inputs. -/
theorem proper_lift {CI BJ : Finset ι × ℕ}
    (hCI : CI ∈ Plan.gradedPlan I.boundary.plan)
    (hBJ : BJ ∈ Plan.gradedPlan I.boundary.plan) (h : GradedLe CI BJ)
    (hne : CI ≠ BJ) (hB : BJ.1 ≠ A)
    (p : I.boundary.below CI → ExtOrd) (q : I.boundary.below BJ → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow I.rows CI p) (hq : RespectsSemanticsBelow I.rows BJ q)
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ)
    (ha : ∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q', RespectsSemanticsBelow I.rows BJ q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      ∀ d, q' (CellScheme.below.mono h d) = p d :=
  AmalgamatedBoundarySemantics.proper_lift s I.leftScheme I.rightScheme I.shared
    I.planLeft I.planRight I.leftRows I.rightRows I.compatible
    (PointImageSemantics.bountiful _ _ _ _ I.left.complete I.left.bountiful)
    (PointImageSemantics.bountiful _ _ _ _ I.right.complete I.right.bountiful)
    hCI hBJ h hne hB p q γ hp hq hγ ha

end Input
end
end VaughtConjecture.Knight.SemSchemeBoundaryInput
