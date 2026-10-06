/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.OwnerwiseDecoding

/-! # Decode short new rows and long original rows together

At each owner, either its row is short at its own grade, or the outer witness
reflects bottom on its actual lower-domain values. The former uses repaired
composition; the latter uses the source-block criterion. No global bottom
reflection, shortness of original rows, or lawful-image hypothesis is needed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.SharpWitnessComposition
open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable {sem : Semantics D} {BJ : Finset ι × ℕ}

/-- Ownerwise mixed transport: short new rows and finitely reflecting old rows
can coexist on one actual scheme. -/
theorem map_respects_of_short_or_reflecting {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) {K : ℕ} {ν : ExtOrd → ExtOrd}
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) (hν : Witness (gTop K) ν)
    (hc : ∀ c : D.below BJ,
      (∀ d : D.below (D.cell c.1), Short (D.grade c.1) (sem.E c.1 d)) ∨
      (∀ d : D.below (D.cell c.1),
        ν (r (CellScheme.below.incl c d)) = ⊥ ↔ r (CellScheme.below.incl c d) = ⊥)) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) := by
  apply map_respects_of_short_or_local hr hK hν
  intro c
  rcases hc c with hs | hb
  · exact Or.inl hs
  · right
    have hlocal := (map_respects_iff_rowBlockBottom (hr.mono c.2)
      (fun d => d.2.2.trans (hK c)) (boundedMap_of_witness hν)).mpr
      (rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects (hr.mono c.2)) hb)
    exact hlocal.locality ⟨c.1, GradedLe.refl _⟩

end VaughtConjecture.Knight.SharpWitnessComposition
