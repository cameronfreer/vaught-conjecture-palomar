/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveBountiful

/-! # Same-contract bountifulness recurrence on the constructed stack

The semantic and selected-section data are the actual recursively constructed
state. Readiness adds consistency of the retained boundary and bountifulness
of the current grade cut. Higher proper owners are retained, not discarded.

Initialization of bountifulness on this exact recursive seed remains explicit.
An unrelated three-grade catalogue equivalence is not used to discharge it.
This is not ordered coatom installation or receiving-family realization.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveRecurrence
open Transform Value ExtOrd
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : ∀ d : Cell D, D.scope d ≠ A)

def Ready (m : ℕ) (hm : m + 3 ≤ A.card) : Prop :=
  sem.IsConsistent ∧
    (GradeCutBoundary.rows (CanonicalRecursiveContract.carrier sem m hm) (m + 3)
      (CanonicalRecursiveSemantics.rows sem hp m hm)).IsBountiful

variable (hold : CanonicalCoatomBountiful.OldLifts sem) {L R : Finset ι}
variable (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
variable (hO : L ∩ R ∈ D.plan)
variable (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)

include hold hL hR hLA hRA hO hcover in
/-- One constructor preserves the identical readiness predicate at the next
grade. All selected-section fields belong to its constructed state. -/
theorem successor (n : ℕ) (hA : n + 4 ≤ A.card)
    (hready : Ready sem hp n (Nat.le_of_succ_le hA))
    (hLc : n + 4 ≤ L.card) (hRc : n + 4 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → n + 4 ≤ C.card →
      ∃ d : Cell D, D.cell d = (C, n + 4)) :
    Ready sem hp (n + 1) hA :=
  ⟨hready.1, CanonicalRecursiveBountiful.bountiful sem n hA hp hready.2 hold
    hL hR hLA hRA hLc hRc hO hcover hcomplete⟩

include hold hL hR hLA hRA hO hcover in
/-- The grade-four case is the same successor theorem. Arbitrary physical
inputs may have distinct lower values above the owner, invisible values,
and literal top; none is excluded by readiness. -/
theorem grade_four (hA : 4 ≤ A.card)
    (hready : Ready sem hp 0 (Nat.le_of_succ_le hA))
    (hLc : 4 ≤ L.card) (hRc : 4 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → 4 ≤ C.card →
      ∃ d : Cell D, D.cell d = (C, 4)) :
    Ready sem hp 1 hA :=
  successor sem hp hold hL hR hLA hRA hO hcover 0 hA hready hLc hRc hcomplete

include hold hL hR hLA hRA hO hcover in
/-- Finite grade iteration, conditional on readiness of the actual seed.
The fixed coatom sizes bound this iteration; it is not arbitrary request or
stage iteration and does not manufacture initial bountifulness. -/
theorem iterate (n : ℕ) (hA : n + 3 ≤ A.card)
    (hseed : Ready sem hp 0 (by omega : 3 ≤ A.card))
    (hLc : n + 3 ≤ L.card) (hRc : n + 3 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ n + 3 →
      ∃ d : Cell D, D.cell d = (C, i)) :
    Ready sem hp n hA := by
  induction n with
  | zero => exact hseed
  | succ n ih =>
    have ha : n + 3 ≤ A.card := Nat.le_of_succ_le hA
    have hl : n + 3 ≤ L.card := Nat.le_of_succ_le hLc
    have hr : n + 3 ≤ R.card := Nat.le_of_succ_le hRc
    have hs := ih ha hseed hl hr
      (fun C hC hCA i hi hic hin => hcomplete C hC hCA i hi hic (by omega))
    exact successor sem hp hold hL hR hLA hRA hO hcover n hA hs hLc hRc
      (fun C hC hCA hic => hcomplete C hC hCA (n + 4) (by omega) hic le_rfl)

theorem consistent {n : ℕ} {hA : n + 3 ≤ A.card} (h : Ready sem hp n hA) :
    (CanonicalRecursiveSemantics.rows sem hp n hA).IsConsistent :=
  CanonicalRecursiveSemantics.consistent sem hp h.1 n hA

end
end VaughtConjecture.Knight.CanonicalRecursiveRecurrence
