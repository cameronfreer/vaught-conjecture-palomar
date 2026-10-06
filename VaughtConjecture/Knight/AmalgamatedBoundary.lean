/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AmalgamatedBoundaryPlan
public import VaughtConjecture.Knight.ProfileBoundaryOrder

/-! # An ordered boundary on an arbitrary binary support plan

The constructor retains every occurrence of both old schemes, identifying
only the specified entire overlap. Both old orders and every inherited
lower domain are exact. Completeness is proved at every proper index.
Full-scope cells and their semantics are not supplied by this boundary.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.AmalgamatedBoundary

open AmalgamationPlan AmalgamatedBoundaryPlan

variable {ι : Type*} [DecidableEq ι]

/-- Put a scheme on an injective image of its point domain, without changing
its occurrence enumeration. -/
def pointImage {κ : Type*} [DecidableEq κ] {B : Finset ι} {C : Finset κ}
    (D : CellScheme B) (e : ι ↪ κ) (he : B.image e = C) : CellScheme C where
  plan := D.plan.image (Finset.image e)
  isPlan := he ▸ Plan.isPlan_image e D.isPlan
  card := D.card
  cell d := ((D.scope d).image e, D.grade d)
  cell_mem d := by
    obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (D.cell_mem d)
    refine Plan.mem_gradedPlan.mpr ⟨Finset.mem_image.mpr ⟨_, hm, rfl⟩, hp, ?_⟩
    change D.grade d ≤ (D.scope d).card at hc
    simpa only [Finset.card_image_of_injective _ e.injective] using hc

theorem pointImage_complete {κ : Type*} [DecidableEq κ] {B : Finset ι} {C : Finset κ}
    (D : CellScheme B) (e : ι ↪ κ) (he : B.image e = C) (hD : D.IsComplete) :
    (pointImage D e he).IsComplete := by
  intro BJ hBJ
  obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp hBJ
  obtain ⟨K, hK, hKB⟩ := Finset.mem_image.mp hm
  have hj : BJ.2 ≤ K.card := by
    rw [← hKB, Finset.card_image_of_injective _ e.injective] at hc
    exact hc
  obtain ⟨d, hd⟩ := hD (K, BJ.2) (Plan.mem_gradedPlan.mpr ⟨hK, hp, hj⟩)
  refine ⟨d, ?_⟩
  change ((D.cell d).1.image e, (D.cell d).2) = BJ
  rw [hd]
  exact Prod.ext hKB rfl

/-- Exact shared occurrences of two ordered faces in one ambient point set.
The exhaustion fields concern geometry only, not labels or transformations. -/
structure Overlap {B C : Finset ι} (D : CellScheme B) (E : CellScheme C) (k : ℕ) where
  f : Fin k ↪ Cell D
  g : Fin k ↪ Cell E
  f_mono : StrictMono f
  g_mono : StrictMono g
  shared : ∀ i, D.cell (f i) = E.cell (g i)
  left_exhaustive : ∀ d, D.scope d ⊆ C → ∃ i, f i = d
  right_exhaustive : ∀ e, E.scope e ⊆ B → ∃ i, g i = e

variable {A : Finset ι} (s : Step A)
variable (D : CellScheme (A.erase s.a)) (E : CellScheme (A.erase s.b))
variable {k : ℕ} (w : Overlap D E k)

variable {s}

abbrev Boundary := ProfileFaceUnion.Carrier (X := Cell D) w.g

noncomputable def index : Boundary D E w → Finset ι × ℕ :=
  ProfileFaceUnion.paste w.g D.cell E.cell

theorem index_left (d : Cell D) :
    index D E w (ProfileFaceUnion.left w.g d) = D.cell d := rfl

theorem index_right (e : Cell E) :
    index D E w (ProfileFaceUnion.right w.f w.g e) = E.cell e :=
  ProfileFaceUnion.paste_right w.f w.g w.shared e

variable (s)

theorem inside_left (z : Boundary D E w) (hz : (index D E w z).1 ⊆ A.erase s.a) :
    ∃ d, ProfileFaceUnion.left w.g d = z := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · exact ⟨d, rfl⟩
  · rw [index_right] at hz
    obtain ⟨i, rfl⟩ := w.right_exhaustive e hz
    exact ⟨w.f i, (ProfileFaceUnion.right_shared w.f w.g i).symm⟩

theorem inside_right (z : Boundary D E w) (hz : (index D E w z).1 ⊆ A.erase s.b) :
    ∃ e, ProfileFaceUnion.right w.f w.g e = z := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · obtain ⟨i, rfl⟩ := w.left_exhaustive d hz
    exact ⟨w.g i, ProfileFaceUnion.right_shared w.f w.g i⟩
  · exact ⟨e, rfl⟩

theorem below_left (d : Cell D) (z : Boundary D E w) :
    GradedLe (index D E w z) (D.cell d) ↔
      ∃ e : D.below (D.cell d), ProfileFaceUnion.left w.g e.1 = z := by
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := inside_left s D E w z
      (h.1.trans (D.isPlan.subset_of_mem (D.scope_mem_plan d)))
    exact ⟨⟨e, h⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    exact e.2

theorem below_right (d : Cell E) (z : Boundary D E w) :
    GradedLe (index D E w z) (E.cell d) ↔
      ∃ e : E.below (E.cell d), ProfileFaceUnion.right w.f w.g e.1 = z := by
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := inside_right s D E w z
      (h.1.trans (E.isPlan.subset_of_mem (E.scope_mem_plan d)))
    rw [index_right] at h
    exact ⟨⟨e, h⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    rw [index_right]
    exact e.2

theorem no_full (z : Boundary D E w) : (index D E w z).1 ≠ A := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · intro h
    have hs := D.isPlan.subset_of_mem (D.scope_mem_plan d)
    change D.scope d = A at h
    rw [h] at hs
    exact Finset.notMem_erase s.a A (hs s.ha)
  · rw [index_right]
    intro h
    have hs := E.isPlan.subset_of_mem (E.scope_mem_plan e)
    change E.scope e = A at h
    rw [h] at hs
    exact Finset.notMem_erase s.b A (hs s.hb)

variable (hD : D.plan = s.left) (hE : E.plan = s.right)

include hD hE in
theorem index_mem (z : Boundary D E w) : index D E w z ∈ Plan.gradedPlan s.plan := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (D.cell_mem d)
    rw [hD] at hm
    exact Plan.mem_gradedPlan.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hm), hp, hc⟩
  · rw [index_right]
    obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (E.cell_mem e)
    rw [hE] at hm
    exact Plan.mem_gradedPlan.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hm), hp, hc⟩

section
variable {s}

noncomputable def enumeration : Boundary D E w ≃ Fin (Fintype.card (Boundary D E w)) :=
  ProfileBoundaryOrder.enumeration w.f w.g w.f_mono w.g_mono

end

/-- The ordered proper boundary, before installing full-scope cells. -/
noncomputable def scheme : CellScheme A where
  plan := s.plan
  isPlan := isPlan s
  card := Fintype.card (Boundary D E w)
  cell d := index D E w ((enumeration D E w).symm d)
  cell_mem _ := index_mem s D E w hD hE _

theorem scope_proper (c : Cell (scheme s D E w hD hE)) :
    (scheme s D E w hD hE).scope c ≠ A :=
  no_full s D E w ((enumeration D E w).symm c)

noncomputable def leftCell (d : Cell D) : Cell (scheme s D E w hD hE) :=
  enumeration D E w (ProfileFaceUnion.left w.g d)

noncomputable def rightCell (e : Cell E) : Cell (scheme s D E w hD hE) :=
  enumeration D E w (ProfileFaceUnion.right w.f w.g e)

theorem left_index (d : Cell D) :
    (scheme s D E w hD hE).cell (leftCell s D E w hD hE d) = D.cell d := by
  change index D E w ((enumeration D E w).symm (enumeration D E w _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem right_index (e : Cell E) :
    (scheme s D E w hD hE).cell (rightCell s D E w hD hE e) = E.cell e := by
  change index D E w ((enumeration D E w).symm (enumeration D E w _)) = _
  rw [Equiv.symm_apply_apply, index_right]

theorem left_order : StrictMono (leftCell s D E w hD hE) :=
  ProfileBoundaryOrder.enumeration_left w.f w.g w.f_mono w.g_mono

theorem right_order : StrictMono (rightCell s D E w hD hE) :=
  ProfileBoundaryOrder.enumeration_right w.f w.g w.f_mono w.g_mono

theorem left_exhaustive (c : Cell (scheme s D E w hD hE))
    (hc : (scheme s D E w hD hE).scope c ⊆ A.erase s.a) :
    ∃ d, leftCell s D E w hD hE d = c := by
  obtain ⟨d, hd⟩ := inside_left s D E w ((enumeration D E w).symm c) hc
  exact ⟨d, (congrArg (enumeration D E w) hd).trans ((enumeration D E w).apply_symm_apply c)⟩

theorem right_exhaustive (c : Cell (scheme s D E w hD hE))
    (hc : (scheme s D E w hD hE).scope c ⊆ A.erase s.b) :
    ∃ e, rightCell s D E w hD hE e = c := by
  obtain ⟨e, he⟩ := inside_right s D E w ((enumeration D E w).symm c) hc
  exact ⟨e, (congrArg (enumeration D E w) he).trans ((enumeration D E w).apply_symm_apply c)⟩

theorem overlap (d : Cell D) (e : Cell E) :
    leftCell s D E w hD hE d = rightCell s D E w hD hE e ↔
      ∃ i, w.f i = d ∧ w.g i = e := by
  change enumeration D E w _ = enumeration D E w _ ↔ _
  rw [Equiv.apply_eq_iff_eq]
  exact ProfileFaceUnion.overlap w.f w.g d e

noncomputable def leftBelow (d : Cell D) : D.below (D.cell d) ≃
    (scheme s D E w hD hE).below ((scheme s D E w hD hE).cell (leftCell s D E w hD hE d)) :=
  Equiv.ofBijective (fun e => ⟨leftCell s D E w hD hE e.1, by
    rw [left_index, left_index]
    exact e.2⟩) ⟨by
    intro e f h
    exact Subtype.ext ((left_order s D E w hD hE).injective (congrArg Subtype.val h)), by
    intro e
    have he := e.2.trans (show GradedLe
      ((scheme s D E w hD hE).cell (leftCell s D E w hD hE d)) (D.cell d) from by
      rw [left_index]
      exact GradedLe.refl _)
    obtain ⟨f, hf⟩ := (below_left s D E w d ((enumeration D E w).symm e.1)).mp he
    exact ⟨f, Subtype.ext ((congrArg (enumeration D E w) hf).trans
      ((enumeration D E w).apply_symm_apply e.1))⟩⟩

noncomputable def rightBelow (d : Cell E) : E.below (E.cell d) ≃
    (scheme s D E w hD hE).below ((scheme s D E w hD hE).cell (rightCell s D E w hD hE d)) :=
  Equiv.ofBijective (fun e => ⟨rightCell s D E w hD hE e.1, by
    rw [right_index, right_index]
    exact e.2⟩) ⟨by
    intro e f h
    exact Subtype.ext ((right_order s D E w hD hE).injective (congrArg Subtype.val h)), by
    intro e
    have he := e.2.trans (show GradedLe
      ((scheme s D E w hD hE).cell (rightCell s D E w hD hE d)) (E.cell d) from by
      rw [right_index]
      exact GradedLe.refl _)
    obtain ⟨f, hf⟩ := (below_right s D E w d ((enumeration D E w).symm e.1)).mp he
    exact ⟨f, Subtype.ext ((congrArg (enumeration D E w) hf).trans
      ((enumeration D E w).apply_symm_apply e.1))⟩⟩

/-- No new proper graded index is left uninhabited by the boundary. -/
theorem complete_proper (hDc : D.IsComplete) (hEc : E.IsComplete)
    {BJ : Finset ι × ℕ} (hBJ : BJ ∈ Plan.gradedPlan s.plan) (hB : BJ.1 ≠ A) :
    ∃ c, (scheme s D E w hD hE).cell c = BJ := by
  rcases proper_index_cover s hBJ hB with hl | hr
  · rw [← hD] at hl
    obtain ⟨d, hd⟩ := hDc BJ hl
    exact ⟨leftCell s D E w hD hE d, (left_index s D E w hD hE d).trans hd⟩
  · rw [← hE] at hr
    obtain ⟨e, he⟩ := hEc BJ hr
    exact ⟨rightCell s D E w hD hE e, (right_index s D E w hD hE e).trans he⟩

end VaughtConjecture.Knight.AmalgamatedBoundary
