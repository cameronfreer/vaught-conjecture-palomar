/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSeedCoding
public import VaughtConjecture.Knight.CoatomRecursiveInput

/-! # Coding of every installed recursive source row

Old rows are literal. New rows use the proved orbit support, finite canonical
fields, and coded grids. The statement is uniform in the constructed height.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveCoding
open Transform Value ExtOrd CanonicalCodingSupport
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : ∀ d : Cell D, D.scope d ≠ A)

theorem seed (hA : 3 ≤ A.card) (hc : sem.IsCoded) :
    (CanonicalRecursiveSeedRows.rows sem hA hp).IsCoded := by
  apply layer (CanonicalRecursiveSeedRows.predecessor sem hA) _ 3 (by decide) hA
    (CanonicalRecursiveSeedRows.separation sem hA hp)
    (CanonicalRecursiveSeedRows.predecessorRows sem hA hp) _
    (CanonicalSeedCoding.pair sem _ hp hc)
    (CanonicalRecursiveSeedRows.inherited_row sem hA hp)
  intro q d
  let F := CanonicalRecursiveSeedRows.data sem hA hp
  change IsCodedLabel 3 (F.rows.E (CanonicalRecursiveSeedRows.controller sem hA q).1 d)
  rw [F.row_new (CanonicalRecursiveSeedRows.controller sem hA q) d]
  apply supported (fun _ hh => grid 3 _ hh)
    (field (GradeCutBoundary.rows D 3 sem) 3 (GradeCutBoundary.toCell D 3) q)
  exact CanonicalRecursiveSeedRows.source_supported sem hA hp q d.1

theorem successor (n : ℕ) (hA : n + 4 ≤ A.card)
    (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))
    (hc : P.rows.IsCoded) : (CanonicalRecursiveSuccessorRows.rows sem n hA hp P).IsCoded := by
  apply layer (CanonicalRecursiveSuccessorRows.predecessor sem n hA) _
    (n + 4) (Nat.succ_pos (n + 3)) hA (CanonicalRecursiveSuccessorRows.separation sem n hA hp)
    P.rows _ hc (CanonicalRecursiveSuccessorRows.inherited_row sem n hA hp P)
  intro q d
  let F := CanonicalRecursiveSuccessorRows.data sem n hA hp P
  change IsCodedLabel (n + 4)
    (F.rows.E (CanonicalRecursiveSuccessorRows.controller sem n hA q).1 d)
  rw [F.row_new (CanonicalRecursiveSuccessorRows.controller sem n hA q) d]
  apply supported (fun _ hh => grid (n + 4) _ hh)
    (field (GradeCutBoundary.rows D (n + 4) sem) (n + 4)
      (GradeCutBoundary.toCell D (n + 4)) q)
  exact CanonicalRecursiveSuccessorRows.source_supported sem n hA hp P q d.1

theorem coded (hc : sem.IsCoded) (n : ℕ) (hA : n + 3 ≤ A.card) :
    (CanonicalRecursiveSemantics.rows sem hp n hA).IsCoded := by
  induction n with
  | zero => exact seed sem hp hA hc
  | succ n ih =>
    exact successor sem hp n hA
      (CanonicalRecursiveSemantics.state sem hp n (Nat.le_of_succ_le hA))
      (ih (Nat.le_of_succ_le hA))

/-- The old coding premise comes from the two legal input schemes. -/
theorem coatom {s : AmalgamatedBoundaryPlan.Step A} {m n : ℕ}
    (I : SemSchemeBoundaryInput.Input s m (n + 3) (n + 3)) :
    (CoatomRecursiveInput.rows I).IsCoded :=
  coded I.rows I.proper I.coded n (CoatomRecursiveInput.height_le I)

end
end VaughtConjecture.Knight.CanonicalRecursiveCoding
