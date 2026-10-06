/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoatomBoundaryExtension
public import VaughtConjecture.Knight.SameScopeBountiful

/-! # Composition of literal original-cap lifting clauses

The intermediate ambient is an actual restriction of the target-local input.
No whole ambient extension or output bountifulness is assumed.
-/
@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CoatomBoundaryExtension
open Transform Value ExtOrd
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {I J K : Finset ι × ℕ}


/-- Raise only the target grade after a proved same-grade scope lift. -/
theorem CappedLift.raise_target {B C : Finset ι} {i j : ℕ}
    {h : B ⊆ C} (hl : CappedLift sem (show GradedLe (B, i) (C, i) from ⟨h, le_rfl⟩))
    (hij : i ≤ j) : CappedLift sem (show GradedLe (B, i) (C, j) from ⟨h, hij⟩) :=
  hl.comp (hJK := show GradedLe (C, i) (C, j) from ⟨Finset.Subset.refl _, hij⟩)
    (bountiful_same_scope sem (B := C) (i := i) (j := j) ⟨Finset.Subset.refl _, hij⟩)

end VaughtConjecture.Knight.CoatomBoundaryExtension
