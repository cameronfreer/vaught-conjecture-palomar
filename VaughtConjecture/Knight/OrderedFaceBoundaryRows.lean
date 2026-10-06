/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrderedFaceBoundary
public import VaughtConjecture.Knight.AmalgamatedBoundaryRows

/-! # Literal semantics on two arbitrary ordered inherited faces

The two inherited tables are glued on their exact occurrence overlap.
No display is recoded and no faithful transformations are composed.
Only equality of the shared source rows is required for row installation.
Generalizes `AmalgamatedBoundaryRows` without requiring coatom geometry.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.OrderedFaceBoundaryRows

open AmalgamationPlan OrderedFaceBoundary Transform Value ExtOrd
open AmalgamatedBoundary (Overlap)
open AmalgamatedBoundaryRows (total total_below pushRow pushRow_at pushRow_outside)

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
variable (D : CellScheme B) (E : CellScheme C)
variable {k : ℕ} (w : Overlap D E k)
variable (R : Finset (Finset ι)) (hR : Plan.IsPlan A R)
variable (hD : D.plan ⊆ R) (hE : E.plan ⊆ R)
variable (semD : Semantics D) (semE : Semantics E)

local notation "K" => scheme D E w R hR hD hE
local notation "l" => leftCell D E w R hR hD hE
local notation "r" => rightCell D E w R hR hD hE

/-- Source equality on all shared occurrences, including every auxiliary. -/
def Compatible : Prop :=
  ∀ i j, total semD (w.f i) (w.f j) = total semE (w.g i) (w.g j)

theorem shared_cell (i : Fin k) : l (w.f i) = r (w.g i) :=
  (overlap D E w R hR hD hE _ _).mpr ⟨i, rfl, rfl⟩

theorem covered (c : Cell K) : (∃ d, l d = c) ∨ ∃ e, r e = c := by
  rcases ProfileFaceUnion.covered w.f w.g ((enumeration D E w).symm c) with
    ⟨d, hd⟩ | ⟨e, he⟩
  · exact Or.inl ⟨d, (congrArg (enumeration D E w) hd).trans
      ((enumeration D E w).apply_symm_apply c)⟩
  · exact Or.inr ⟨e, (congrArg (enumeration D E w) he).trans
      ((enumeration D E w).apply_symm_apply c)⟩

theorem pushRow_shared (hc : Compatible D E w semD semE) (i : Fin k) :
    pushRow l semD (w.f i) = pushRow r semE (w.g i) := by
  funext z
  by_cases hz : GradedLe ((K).cell z) (D.cell (w.f i))
  · have hzl : GradedLe ((K).cell z) ((K).cell (l (w.f i))) := by
      rw [left_index]
      exact hz
    obtain ⟨d, hd⟩ := (leftBelow D E w R hR hD hE (w.f i)).surjective ⟨z, hzl⟩
    have he : l d.1 = z := congrArg Subtype.val hd
    have hdc : D.scope d.1 ⊆ C := by
      have hs := d.2.1
      change D.scope d.1 ⊆ (D.cell (w.f i)).1 at hs
      have hs' : (D.cell (w.f i)).1 ⊆ (E.cell (w.g i)).1 :=
        subset_of_eq (congrArg Prod.fst (w.shared i))
      exact hs.trans (hs'.trans (E.isPlan.subset_of_mem (E.scope_mem_plan _)))
    obtain ⟨j, hj⟩ := w.left_exhaustive d.1 hdc
    rw [← he, ← hj, pushRow_at l (left_order D E w R hR hD hE).injective,
      shared_cell, pushRow_at r (right_order D E w R hR hD hE).injective]
    exact hc i j
  · rw [pushRow_outside l (left_order D E w R hR hD hE).injective
      (left_index D E w R hR hD hE) semD _ _ hz,
      pushRow_outside r (right_order D E w R hR hD hE).injective
      (right_index D E w R hR hD hE) semE]
    rwa [← w.shared]

noncomputable def table (c : Cell K) : Cell K → ExtOrd :=
  ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE)
    ((enumeration D E w).symm c)

theorem table_left (c d : Cell D) : table D E w R hR hD hE semD semE (l c) (l d) =
    total semD c d := by
  change ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE)
    ((enumeration D E w).symm
    (enumeration D E w (ProfileFaceUnion.left w.g c))) (l d) = _
  rw [Equiv.symm_apply_apply]
  exact pushRow_at l (left_order D E w R hR hD hE).injective semD c d

theorem table_right (hc : Compatible D E w semD semE) (c d : Cell E) :
    table D E w R hR hD hE semD semE (r c) (r d) = total semE c d := by
  change ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE)
    ((enumeration D E w).symm
    (enumeration D E w (ProfileFaceUnion.right w.f w.g c))) (r d) = _
  rw [Equiv.symm_apply_apply, ProfileFaceUnion.paste_right w.f w.g
    (pushRow_shared D E w R hR hD hE semD semE hc)]
  exact pushRow_at r (right_order D E w R hR hD hE).injective semE c d

variable (hc : Compatible D E w semD semE)

include hc in
theorem table_orderly (c : Cell K) (d : (K).below ((K).cell c)) :
    table D E w R hR hD hE semD semE c d.1 =
      extVisibilityReplace (table D E w R hR hD hE semD semE c d.1)
        ((K).grade d.1) ((K).grade d.1) := by
  rcases covered D E w R hR hD hE c with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨e, rfl⟩ := (leftBelow D E w R hR hD hE c).surjective d
    change table D E w R hR hD hE semD semE (l c) (l e.1) =
      extVisibilityReplace (table D E w R hR hD hE semD semE (l c) (l e.1))
        ((K).cell (l e.1)).2 ((K).cell (l e.1)).2
    rw [table_left, total_below, left_index]
    exact semD.orderly c e
  · obtain ⟨e, rfl⟩ := (rightBelow D E w R hR hD hE c).surjective d
    change table D E w R hR hD hE semD semE (r c) (r e.1) =
      extVisibilityReplace (table D E w R hR hD hE semD semE (r c) (r e.1))
        ((K).cell (r e.1)).2 ((K).cell (r e.1)).2
    rw [table_right D E w R hR hD hE semD semE hc, total_below, right_index]
    exact semE.orderly c e

/-- Both rows are copied literally; the common rows agree by compatibility. -/
noncomputable def rows : Semantics K where
  E c d := table D E w R hR hD hE semD semE c d.1
  orderly := table_orderly D E w R hR hD hE semD semE hc

theorem rows_left (c : Cell D) (d : D.below (D.cell c)) :
    (rows D E w R hR hD hE semD semE hc).E (l c) (leftBelow D E w R hR hD hE c d) =
      semD.E c d :=
  (table_left D E w R hR hD hE semD semE c d.1).trans (total_below semD c d)

theorem rows_right (c : Cell E) (d : E.below (E.cell c)) :
    (rows D E w R hR hD hE semD semE hc).E (r c) (rightBelow D E w R hR hD hE c d) =
      semE.E c d :=
  (table_right D E w R hR hD hE semD semE hc c d.1).trans (total_below semE c d)

end VaughtConjecture.Knight.OrderedFaceBoundaryRows
