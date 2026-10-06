/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AmalgamatedBoundary

/-! # Ordered inherited boundary for two arbitrary visible faces

Generalizes the occurrence construction of `AmalgamatedBoundary` beyond coatom
geometry. The common plan is supplied, every occurrence of both inputs is retained,
and exactly the specified overlap is identified. Both original orders and complete
lower domains are preserved. No cells at new mixed indices are constructed here.

This is the ordered-boundary part of new25, not a receiving probe.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.OrderedFaceBoundary

open AmalgamationPlan
open AmalgamatedBoundary (Overlap)

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
variable (D : CellScheme B) (E : CellScheme C)
variable {k : ℕ} (w : Overlap D E k)

abbrev Boundary := ProfileFaceUnion.Carrier (X := Cell D) w.g

noncomputable def index : Boundary D E w → Finset ι × ℕ :=
  ProfileFaceUnion.paste w.g D.cell E.cell

theorem index_left (d : Cell D) :
    index D E w (ProfileFaceUnion.left w.g d) = D.cell d := rfl

theorem index_right (e : Cell E) :
    index D E w (ProfileFaceUnion.right w.f w.g e) = E.cell e :=
  ProfileFaceUnion.paste_right w.f w.g w.shared e

theorem inside_left (z : Boundary D E w) (hz : (index D E w z).1 ⊆ B) :
    ∃ d, ProfileFaceUnion.left w.g d = z := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · exact ⟨d, rfl⟩
  · rw [index_right] at hz
    obtain ⟨i, rfl⟩ := w.right_exhaustive e hz
    exact ⟨w.f i, (ProfileFaceUnion.right_shared w.f w.g i).symm⟩

theorem inside_right (z : Boundary D E w) (hz : (index D E w z).1 ⊆ C) :
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
    obtain ⟨e, rfl⟩ := inside_left D E w z
      (h.1.trans (D.isPlan.subset_of_mem (D.scope_mem_plan d)))
    exact ⟨⟨e, h⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    exact e.2

theorem below_right (d : Cell E) (z : Boundary D E w) :
    GradedLe (index D E w z) (E.cell d) ↔
      ∃ e : E.below (E.cell d), ProfileFaceUnion.right w.f w.g e.1 = z := by
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := inside_right D E w z
      (h.1.trans (E.isPlan.subset_of_mem (E.scope_mem_plan d)))
    rw [index_right] at h
    exact ⟨⟨e, h⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    rw [index_right]
    exact e.2

variable (R : Finset (Finset ι)) (hR : Plan.IsPlan A R)
variable (hD : D.plan ⊆ R) (hE : E.plan ⊆ R)

include hD hE in
theorem index_mem (z : Boundary D E w) : index D E w z ∈ Plan.gradedPlan R := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (D.cell_mem d)
    exact Plan.mem_gradedPlan.mpr ⟨hD hm, hp, hc⟩
  · rw [index_right]
    obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (E.cell_mem e)
    exact Plan.mem_gradedPlan.mpr ⟨hE hm, hp, hc⟩

noncomputable def enumeration : Boundary D E w ≃ Fin (Fintype.card (Boundary D E w)) :=
  ProfileBoundaryOrder.enumeration w.f w.g w.f_mono w.g_mono

/-- The ordered inherited boundary, with no mixed cells installed. -/
noncomputable def scheme : CellScheme A where
  plan := R
  isPlan := hR
  card := Fintype.card (Boundary D E w)
  cell d := index D E w ((enumeration D E w).symm d)
  cell_mem _ := index_mem D E w R hD hE _

noncomputable def leftCell (d : Cell D) : Cell (scheme D E w R hR hD hE) :=
  enumeration D E w (ProfileFaceUnion.left w.g d)

noncomputable def rightCell (e : Cell E) : Cell (scheme D E w R hR hD hE) :=
  enumeration D E w (ProfileFaceUnion.right w.f w.g e)

theorem left_index (d : Cell D) :
    (scheme D E w R hR hD hE).cell (leftCell D E w R hR hD hE d) = D.cell d := by
  change index D E w ((enumeration D E w).symm (enumeration D E w _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem right_index (e : Cell E) :
    (scheme D E w R hR hD hE).cell (rightCell D E w R hR hD hE e) = E.cell e := by
  change index D E w ((enumeration D E w).symm (enumeration D E w _)) = _
  rw [Equiv.symm_apply_apply, index_right]

theorem left_order : StrictMono (leftCell D E w R hR hD hE) :=
  ProfileBoundaryOrder.enumeration_left w.f w.g w.f_mono w.g_mono

theorem right_order : StrictMono (rightCell D E w R hR hD hE) :=
  ProfileBoundaryOrder.enumeration_right w.f w.g w.f_mono w.g_mono

theorem left_exhaustive (c : Cell (scheme D E w R hR hD hE))
    (hc : (scheme D E w R hR hD hE).scope c ⊆ B) :
    ∃ d, leftCell D E w R hR hD hE d = c := by
  obtain ⟨d, hd⟩ := inside_left D E w ((enumeration D E w).symm c) hc
  exact ⟨d, (congrArg (enumeration D E w) hd).trans
    ((enumeration D E w).apply_symm_apply c)⟩

theorem right_exhaustive (c : Cell (scheme D E w R hR hD hE))
    (hc : (scheme D E w R hR hD hE).scope c ⊆ C) :
    ∃ e, rightCell D E w R hR hD hE e = c := by
  obtain ⟨e, he⟩ := inside_right D E w ((enumeration D E w).symm c) hc
  exact ⟨e, (congrArg (enumeration D E w) he).trans
    ((enumeration D E w).apply_symm_apply c)⟩

theorem overlap (d : Cell D) (e : Cell E) :
    leftCell D E w R hR hD hE d = rightCell D E w R hR hD hE e ↔
      ∃ i, w.f i = d ∧ w.g i = e := by
  change enumeration D E w _ = enumeration D E w _ ↔ _
  rw [Equiv.apply_eq_iff_eq]
  exact ProfileFaceUnion.overlap w.f w.g d e

noncomputable def leftBelow (d : Cell D) : D.below (D.cell d) ≃
    (scheme D E w R hR hD hE).below
      ((scheme D E w R hR hD hE).cell (leftCell D E w R hR hD hE d)) :=
  Equiv.ofBijective (fun e => ⟨leftCell D E w R hR hD hE e.1, by
    rw [left_index, left_index]
    exact e.2⟩) ⟨by
    intro e f h
    exact Subtype.ext ((left_order D E w R hR hD hE).injective (congrArg Subtype.val h)), by
    intro e
    have he := e.2.trans (show GradedLe
      ((scheme D E w R hR hD hE).cell (leftCell D E w R hR hD hE d)) (D.cell d) from by
      rw [left_index]
      exact GradedLe.refl _)
    obtain ⟨f, hf⟩ := (below_left D E w d ((enumeration D E w).symm e.1)).mp he
    exact ⟨f, Subtype.ext ((congrArg (enumeration D E w) hf).trans
      ((enumeration D E w).apply_symm_apply e.1))⟩⟩

noncomputable def rightBelow (d : Cell E) : E.below (E.cell d) ≃
    (scheme D E w R hR hD hE).below
      ((scheme D E w R hR hD hE).cell (rightCell D E w R hR hD hE d)) :=
  Equiv.ofBijective (fun e => ⟨rightCell D E w R hR hD hE e.1, by
    rw [right_index, right_index]
    exact e.2⟩) ⟨by
    intro e f h
    exact Subtype.ext ((right_order D E w R hR hD hE).injective (congrArg Subtype.val h)), by
    intro e
    have he := e.2.trans (show GradedLe
      ((scheme D E w R hR hD hE).cell (rightCell D E w R hR hD hE d)) (E.cell d) from by
      rw [right_index]
      exact GradedLe.refl _)
    obtain ⟨f, hf⟩ := (below_right D E w d ((enumeration D E w).symm e.1)).mp he
    exact ⟨f, Subtype.ext ((congrArg (enumeration D E w) hf).trans
      ((enumeration D E w).apply_symm_apply e.1))⟩⟩

/-- Completeness at an old index is inherited; new mixed indices are not claimed complete. -/
theorem complete_on_input (hDc : D.IsComplete) (hEc : E.IsComplete)
    {BJ : Finset ι × ℕ}
    (hBJ : BJ ∈ Plan.gradedPlan D.plan ∨ BJ ∈ Plan.gradedPlan E.plan) :
    ∃ c, (scheme D E w R hR hD hE).cell c = BJ := by
  rcases hBJ with hl | hr
  · obtain ⟨d, hd⟩ := hDc BJ hl
    exact ⟨leftCell D E w R hR hD hE d, (left_index D E w R hR hD hE d).trans hd⟩
  · obtain ⟨e, he⟩ := hEc BJ hr
    exact ⟨rightCell D E w R hR hD hE e, (right_index D E w R hR hD hE e).trans he⟩

end VaughtConjecture.Knight.OrderedFaceBoundary
