/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AmalgamatedBoundary
public import VaughtConjecture.Knight.PartialSections

/-! # Literal semantics on a uniformly ordered proper boundary

The two inherited tables are glued on their exact occurrence overlap.
No display is recoded and no faithful transformations are composed.
Only equality of the shared source rows is required for row installation.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.AmalgamatedBoundaryRows

open AmalgamationPlan AmalgamatedBoundaryPlan AmalgamatedBoundary
open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι]

open Classical in
/-- Extend a semantic row by bottom outside its actual lower domain. -/
noncomputable def total {B : Finset ι} {D : CellScheme B} (sem : Semantics D)
    (c d : Cell D) : ExtOrd :=
  if h : GradedLe (D.cell d) (D.cell c) then sem.E c ⟨d, h⟩ else ⊥

theorem total_below {B : Finset ι} {D : CellScheme B} (sem : Semantics D)
    (c : Cell D) (d : D.below (D.cell c)) : total sem c d.1 = sem.E c d := by
  rw [total, dite_eq_left d.2]
  exact congrArg (sem.E c) (Subtype.ext rfl)

theorem total_outside {B : Finset ι} {D : CellScheme B} (sem : Semantics D)
    (c d : Cell D) (h : ¬ GradedLe (D.cell d) (D.cell c)) : total sem c d = ⊥ := by
  simp only [total, dite_eq_right h]

section Push
variable {B C : Finset ι} {D : CellScheme B} {K : CellScheme C}
variable (f : Cell D → Cell K) (hf : Function.Injective f)
variable (hi : ∀ d, K.cell (f d) = D.cell d) (sem : Semantics D)

noncomputable def pushRow (c : Cell D) : Cell K → ExtOrd :=
  Function.extend f (total sem c) (fun _ => ⊥)

include hf in
theorem pushRow_at (c d : Cell D) : pushRow f sem c (f d) = total sem c d :=
  hf.extend_apply _ _ _

include hf hi in
theorem pushRow_outside (c : Cell D) (z : Cell K)
    (hz : ¬ GradedLe (K.cell z) (D.cell c)) : pushRow f sem c z = ⊥ := by
  classical
  by_cases h : ∃ d, f d = z
  · obtain ⟨d, rfl⟩ := h
    rw [pushRow_at f hf]
    apply total_outside
    simpa only [hi] using hz
  · exact Function.extend_apply' _ _ _ h

end Push

variable {A : Finset ι} (s : Step A)
variable (D : CellScheme (A.erase s.a)) (E : CellScheme (A.erase s.b))
variable {k : ℕ} (w : Overlap D E k) (hD : D.plan = s.left) (hE : E.plan = s.right)
variable (semD : Semantics D) (semE : Semantics E)

local notation "K" => scheme s D E w hD hE
local notation "l" => leftCell s D E w hD hE
local notation "r" => rightCell s D E w hD hE

/-- Source equality on all shared occurrences, including every auxiliary. -/
def Compatible : Prop :=
  ∀ i j, total semD (w.f i) (w.f j) = total semE (w.g i) (w.g j)

theorem shared_cell (i : Fin k) : l (w.f i) = r (w.g i) :=
  (overlap s D E w hD hE _ _).mpr ⟨i, rfl, rfl⟩

theorem covered (c : Cell K) : (∃ d, l d = c) ∨ ∃ e, r e = c := by
  rcases ProfileFaceUnion.covered w.f w.g ((enumeration D E w).symm c) with
    ⟨d, hd⟩ | ⟨e, he⟩
  · exact Or.inl ⟨d, (congrArg (enumeration D E w) hd).trans
      ((enumeration D E w).apply_symm_apply c)⟩
  · exact Or.inr ⟨e, (congrArg (enumeration D E w) he).trans
      ((enumeration D E w).apply_symm_apply c)⟩

theorem pushRow_shared (hc : Compatible s D E w semD semE) (i : Fin k) :
    pushRow l semD (w.f i) = pushRow r semE (w.g i) := by
  funext z
  by_cases hz : GradedLe ((K).cell z) (D.cell (w.f i))
  · have hzl : GradedLe ((K).cell z) ((K).cell (l (w.f i))) := by
      rw [left_index]
      exact hz
    obtain ⟨d, hd⟩ := (leftBelow s D E w hD hE (w.f i)).surjective ⟨z, hzl⟩
    have he : l d.1 = z := congrArg Subtype.val hd
    have hdc : D.scope d.1 ⊆ A.erase s.b := by
      have hs := d.2.1
      change D.scope d.1 ⊆ (D.cell (w.f i)).1 at hs
      have hs' : (D.cell (w.f i)).1 ⊆ (E.cell (w.g i)).1 :=
        subset_of_eq (congrArg Prod.fst (w.shared i))
      exact hs.trans (hs'.trans (E.isPlan.subset_of_mem (E.scope_mem_plan _)))
    obtain ⟨j, hj⟩ := w.left_exhaustive d.1 hdc
    rw [← he, ← hj, pushRow_at l (left_order s D E w hD hE).injective,
      shared_cell, pushRow_at r (right_order s D E w hD hE).injective]
    exact hc i j
  · rw [pushRow_outside l (left_order s D E w hD hE).injective
      (left_index s D E w hD hE) semD _ _ hz,
      pushRow_outside r (right_order s D E w hD hE).injective
      (right_index s D E w hD hE) semE]
    rwa [← w.shared]

noncomputable def table (c : Cell K) : Cell K → ExtOrd :=
  ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE)
    ((enumeration D E w).symm c)

theorem table_left (c d : Cell D) : table s D E w hD hE semD semE (l c) (l d) =
    total semD c d := by
  change ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE)
    ((enumeration D E w).symm
    (enumeration D E w (ProfileFaceUnion.left w.g c))) (l d) = _
  rw [Equiv.symm_apply_apply]
  exact pushRow_at l (left_order s D E w hD hE).injective semD c d

theorem table_right (hc : Compatible s D E w semD semE) (c d : Cell E) :
    table s D E w hD hE semD semE (r c) (r d) = total semE c d := by
  change ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE)
    ((enumeration D E w).symm
    (enumeration D E w (ProfileFaceUnion.right w.f w.g c))) (r d) = _
  rw [Equiv.symm_apply_apply, ProfileFaceUnion.paste_right w.f w.g
    (pushRow_shared s D E w hD hE semD semE hc)]
  exact pushRow_at r (right_order s D E w hD hE).injective semE c d

variable (hc : Compatible s D E w semD semE)

include hc in
theorem table_orderly (c : Cell K) (d : (K).below ((K).cell c)) :
    table s D E w hD hE semD semE c d.1 =
      extVisibilityReplace (table s D E w hD hE semD semE c d.1)
        ((K).grade d.1) ((K).grade d.1) := by
  rcases covered s D E w hD hE c with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨e, rfl⟩ := (leftBelow s D E w hD hE c).surjective d
    change table s D E w hD hE semD semE (l c) (l e.1) =
      extVisibilityReplace (table s D E w hD hE semD semE (l c) (l e.1))
        ((K).cell (l e.1)).2 ((K).cell (l e.1)).2
    rw [table_left, total_below, left_index]
    exact semD.orderly c e
  · obtain ⟨e, rfl⟩ := (rightBelow s D E w hD hE c).surjective d
    change table s D E w hD hE semD semE (r c) (r e.1) =
      extVisibilityReplace (table s D E w hD hE semD semE (r c) (r e.1))
        ((K).cell (r e.1)).2 ((K).cell (r e.1)).2
    rw [table_right s D E w hD hE semD semE hc, total_below, right_index]
    exact semE.orderly c e

/-- Both rows are copied literally; the common rows agree by compatibility. -/
noncomputable def rows : Semantics K where
  E c d := table s D E w hD hE semD semE c d.1
  orderly := table_orderly s D E w hD hE semD semE hc

theorem rows_left (c : Cell D) (d : D.below (D.cell c)) :
    (rows s D E w hD hE semD semE hc).E (l c) (leftBelow s D E w hD hE c d) =
      semD.E c d :=
  (table_left s D E w hD hE semD semE c d.1).trans (total_below semD c d)

theorem rows_right (c : Cell E) (d : E.below (E.cell c)) :
    (rows s D E w hD hE semD semE hc).E (r c) (rightBelow s D E w hD hE c d) =
      semE.E c d :=
  (table_right s D E w hD hE semD semE hc c d.1).trans (total_below semE c d)

end VaughtConjecture.Knight.AmalgamatedBoundaryRows
