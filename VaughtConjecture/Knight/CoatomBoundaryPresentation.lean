/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SemSchemeBoundaryInput
public import VaughtConjecture.Knight.CoatomAmalgamation
public import VaughtConjecture.Knight.RequestAttachment

/-! # Deriving the placed boundary from abstract coatom inputs

The two embeddings and literal common-face restrictions determine every
geometric field of `SemSchemeBoundaryInput.Input`. No plan, overlap map,
semantic compatibility, or old-face lifting hypothesis is supplied separately.
This constructs the proper boundary, not full-scope rows or an amalgam type.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.CoatomBoundaryPresentation

open AmalgamationPlan AmalgamatedBoundaryPlan SemSchemeBoundaryInput

noncomputable section

variable {n : ℕ}

theorem exists_missing (f : Fin (n + 1) ↪ Fin (n + 2)) :
    ∃ a, Finset.univ.image f = Finset.univ.erase a := by
  classical
  have hc : (Finset.univ \ Finset.univ.image f).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_image_of_injective _ f.injective]
    simp
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  refine ⟨a, ?_⟩
  ext x
  have hx := Finset.ext_iff.mp ha x
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] at hx
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

def missing (f : Fin (n + 1) ↪ Fin (n + 2)) : Fin (n + 2) :=
  Classical.choose (exists_missing f)

theorem image_missing (f : Fin (n + 1) ↪ Fin (n + 2)) :
    Finset.univ.image f = Finset.univ.erase (missing f) :=
  Classical.choose_spec (exists_missing f)

variable (C : CoatomPair n)

theorem missing_ne : missing C.f₁ ≠ missing C.f₂ := by
  intro h
  apply C.ne
  rw [image_missing, image_missing, h]

/-- Commutation and cardinalities force the shared image to be the full intersection. -/
theorem common_image :
    (Finset.univ.image C.g₁).image C.f₁ =
      (Finset.univ.erase (missing C.f₁)).erase (missing C.f₂) := by
  classical
  have hcomm : (Finset.univ.image C.g₁).image C.f₁ =
      (Finset.univ.image C.g₂).image C.f₂ := by
    rw [Finset.image_image, Finset.image_image]
    exact congrArg (fun e : Fin n ↪ Fin (n + 2) => Finset.univ.image e) C.comm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    have hl : x ∈ Finset.univ.image C.f₁ :=
      Finset.image_subset_image (Finset.subset_univ _) hx
    have hr : x ∈ Finset.univ.image C.f₂ :=
      Finset.image_subset_image (Finset.subset_univ _) (hcomm ▸ hx)
    rw [image_missing] at hl hr
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hr).1, hl⟩
  · rw [Finset.card_image_of_injective _ C.f₁.injective,
      Finset.card_image_of_injective _ C.g₁.injective,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr
        ⟨(missing_ne C).symm, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp

/-- Only literal legal input schemes and their visible common restriction. -/
structure Data where
  left : SemScheme (n + 1)
  right : SemScheme (n + 1)
  common : SemScheme n
  visibleLeft : Finset.univ.image C.g₁ ∈ left.scheme.plan
  visibleRight : Finset.univ.image C.g₂ ∈ right.scheme.plan
  faceLeft : left.restrictFace C.g₁ visibleLeft = common
  faceRight : right.restrictFace C.g₂ visibleRight = common

namespace Data

variable {C} (D : Data C)

theorem common_image_right :
    (Finset.univ.image C.g₂).image C.f₂ =
      (Finset.univ.erase (missing C.f₁)).erase (missing C.f₂) := by
  rw [← common_image C, Finset.image_image, Finset.image_image]
  exact congrArg (fun e : Fin n ↪ Fin (n + 2) => Finset.univ.image e) C.comm.symm

theorem common_plan :
    Plan.restrictPlan (D.left.scheme.plan.image (Finset.image C.f₁))
        ((Finset.univ.erase (missing C.f₁)).erase (missing C.f₂)) =
      Plan.restrictPlan (D.right.scheme.plan.image (Finset.image C.f₂))
        ((Finset.univ.erase (missing C.f₁)).erase (missing C.f₂)) := by
  rw [← common_image C, restrictPlan_image,
    ← image_restrictFace_plan D.left.scheme C.g₁ D.visibleLeft]
  rw [common_image C, ← common_image_right (C := C), restrictPlan_image,
    ← image_restrictFace_plan D.right.scheme C.g₂ D.visibleRight]
  have hl := congrArg (fun E : SemScheme n => E.scheme.plan) D.faceLeft
  have hr := congrArg (fun E : SemScheme n => E.scheme.plan) D.faceRight
  change (D.left.scheme.restrictFace C.g₁ D.visibleLeft).plan = _ at hl
  change (D.right.scheme.restrictFace C.g₂ D.visibleRight).plan = _ at hr
  rw [hl, hr, Finset.image_image, Finset.image_image]
  congr 1
  funext T
  simp only [Function.comp_apply, Finset.image_image]
  exact congrArg (fun e : Fin n ↪ Fin (n + 2) => T.image e) C.comm

/-- The step plan is derived, including its common restriction equation. -/
def step : Step (Finset.univ : Finset (Fin (n + 2))) where
  a := missing C.f₁
  b := missing C.f₂
  ha := Finset.mem_univ _
  hb := Finset.mem_univ _
  different := missing_ne C
  left := D.left.scheme.plan.image (Finset.image C.f₁)
  right := D.right.scheme.plan.image (Finset.image C.f₂)
  left_plan := image_missing C.f₁ ▸ Plan.isPlan_image C.f₁ D.left.scheme.isPlan
  right_plan := image_missing C.f₂ ▸ Plan.isPlan_image C.f₂ D.right.scheme.isPlan
  common_left := common_image C ▸ Finset.mem_image_of_mem _ D.visibleLeft
  common_right := common_image_right (C := C) ▸ Finset.mem_image_of_mem _ D.visibleRight
  common := common_plan D

/-- Canonical adapter to the proper-boundary constructor; all geometry is proved. -/
def input : Input D.step n (n + 1) (n + 1) where
  left := D.left
  right := D.right
  common := D.common
  placeLeft := C.f₁
  placeRight := C.f₂
  imageLeft := image_missing C.f₁
  imageRight := image_missing C.f₂
  commonLeft := C.g₁
  commonRight := C.g₂
  visibleLeft := D.visibleLeft
  visibleRight := D.visibleRight
  faceLeft := D.faceLeft
  faceRight := D.faceRight
  commute := C.comm
  intersection := by
    rw [AmalgamatedBoundaryPlan.erased_inter]
    exact common_image C
  planLeft := rfl
  planRight := rfl

end Data

/-- Compatible stage types provide the raw input data, with their original schemes literal.
The labels are not extended here. -/
def of_compatible {α : Ordinal.{0}} {pa pb : S α (n + 1)}
    (h : C.Compatible pa pb) : Data C := by
  classical
  let r := Classical.choose h
  have hl := (Classical.choose_spec h).1
  have hr := (Classical.choose_spec h).2
  let vl := Classical.choose (face_of_typeMap_eq_some C.g₁ hl)
  let vr := Classical.choose (face_of_typeMap_eq_some C.g₂ hr)
  exact ⟨pa.scheme, pb.scheme, r.scheme, vl, vr,
    Classical.choose_spec (face_of_typeMap_eq_some C.g₁ hl),
    Classical.choose_spec (face_of_typeMap_eq_some C.g₂ hr)⟩

end
end VaughtConjecture.Knight.CoatomBoundaryPresentation
