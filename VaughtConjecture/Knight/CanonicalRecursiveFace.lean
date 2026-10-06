/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveLiteralRows
public import VaughtConjecture.Knight.ExactSemanticFace

/-! # Exact faces survive ordinary full-scope recursion

This is occurrence-level transport for composing the ordinary constructor
across scopes. Entire old lower domains and rows are retained; no shortness
or bound on the grades of inherited owners is used.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveFace
open Transform Value ExtOrd CanonicalRecursiveContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}
variable {D : CellScheme A} {E : CellScheme B}
variable {sem : Semantics D} {old : Semantics E}
variable (F : ExactSemanticFace old sem) (hB : ¬ A ⊆ B)
variable (hp : ∀ d : Cell D, D.scope d ≠ A) (n : ℕ) (hA : n + 3 ≤ A.card)

def face : ExactSemanticFace old (CanonicalRecursiveSemantics.rows sem hp n hA) where
  map := F.map.trans (boundary sem n hA).toEmbedding
  index c := (CanonicalRecursiveInventory.boundary_cell sem (n + 3) hA (F.map c)).trans
    (F.index c)
  exhaustive z hz := by
    rcases RecursiveSourceCarrier.classify D (CanonicalRecursiveInventory.Profile sem)
      (n + 3) hA z with ⟨d, rfl⟩ | ⟨j, _, _, he⟩
    · have hd : D.scope d ⊆ B := by
        change (D.cell d).1 ⊆ B
        change ((carrier sem n hA).cell (boundary sem n hA d)).1 ⊆ B at hz
        simpa only [CanonicalRecursiveInventory.boundary_cell] using hz
      obtain ⟨c, rfl⟩ := F.exhaustive d hd
      exact ⟨c, rfl⟩
    · change ((carrier sem n hA).cell z).1 ⊆ B at hz
      rw [he] at hz
      exact (hB hz).elim
  row c d := (CanonicalRecursiveLiteralRows.row sem hp n hA (F.map c)
    (F.belowMap c d)).trans (F.row c d)

theorem map_order (hF : StrictMono F.map) : StrictMono (face F hB hp n hA).map :=
  (boundary sem n hA).strictMono.comp hF

end
end VaughtConjecture.Knight.CanonicalRecursiveFace
