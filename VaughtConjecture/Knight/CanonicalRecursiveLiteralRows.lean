/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport

/-! # Literal boundary rows on the recursive inventory -/
@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveLiteralRows
open Transform Value ExtOrd CanonicalRecursiveContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : ∀ d : Cell D, D.scope d ≠ A)

theorem row (n : ℕ) (hA : n + 3 ≤ A.card) (c : Cell D) (d : D.below (D.cell c)) :
    (CanonicalRecursiveSemantics.rows sem hp n hA).E (boundary sem n hA c)
      ⟨boundary sem n hA d.1, by
        rw [CanonicalRecursiveInventory.boundary_cell, CanonicalRecursiveInventory.boundary_cell]
        exact d.2⟩ = sem.E c d := by
  induction n with
  | zero =>
    let h2 := CanonicalRecursiveSeedRows.two_le hA
    let h1 := CanonicalPairLocalSections.one_le h2
    let cp := CanonicalPairLocalSections.original sem h2 c
    let dp : (CanonicalRecursiveSeedRows.predecessor sem hA).below
        ((CanonicalRecursiveSeedRows.predecessor sem hA).cell cp) :=
      ⟨CanonicalPairLocalSections.original sem h2 d.1, by
        simpa only [cp, CanonicalPairLocalSections.original, CanonicalPairBoundary.old,
          GradeCutPairCarrier.old, GradeCutPairCarrier.cell_idx, GradeCutPairCarrier.idx]
          using d.2⟩
    exact (CanonicalRecursiveSeedRows.inherited_row sem hA hp cp dp).trans
      (GradeCutPairRows.old_row D _ _ 1 2 (by decide) h1 (by decide) h2 hp (by decide)
        sem (CanonicalPairLocalSections.smallRows sem h2 hp) c d)
  | succ n ih =>
    let hn := Nat.le_of_succ_le hA
    let c' := boundary sem n hn c
    let d' : (carrier sem n hn).below ((carrier sem n hn).cell c') :=
      ⟨boundary sem n hn d.1, by
        rw [CanonicalRecursiveInventory.boundary_cell, CanonicalRecursiveInventory.boundary_cell]
        exact d.2⟩
    exact (CanonicalRecursiveSuccessorRows.inherited_row sem n hA hp
      (CanonicalRecursiveSemantics.state sem hp n hn) c' d').trans (ih hn)

end
end VaughtConjecture.Knight.CanonicalRecursiveLiteralRows
