/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Type

/-! # Finite row readback at top-labelled cells

Elementary locality readback shared by lawful provisional lifts and the
arbitrary-ordinal ratchet, before provisional or model definitions.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Value ExtOrd

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-- Locality of the labelling (Def. 2.5.4(1)): the row of an `∞`-cell `Θ` at an `∞`-cell
below it is not `-∞` (else the transform could not reach the label `∞`). -/
theorem row_ne_bot_of_label_top (p : S α n) {Θ : Cell p.scheme.scheme}
    (hΘ : p.label Θ = ⊤) (Sg : p.scheme.scheme.below (p.scheme.scheme.cell Θ))
    (hSg : p.label Sg.1 = ⊤) : p.scheme.rows.E Θ Sg ≠ ⊥ := by
  obtain ⟨g, σ, -, -, hσbot, -, -, hloc⟩ := p.respects.locality Θ
  have h : min (p.label Sg.1) (p.label Θ) =
      min (σ (p.scheme.rows.E Θ Sg)) (g (p.scheme.scheme.grade Sg.1)) := hloc Sg
  rw [hSg, hΘ, min_self] at h
  intro hbot
  rw [hbot, hσbot] at h
  exact absurd h.symm (by simp)

end StageType

end VaughtConjecture.Knight
