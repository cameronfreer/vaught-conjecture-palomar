/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Value

/-! # Elementary visibility band arithmetic

The arithmetic shared by finite lawful provisional lifts and the arbitrary-ordinal
ratchet. Public declarations retain their original statements and proofs.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Value ExtOrd

namespace Value

theorem limitPart_limitPart (μ : Ordinal.{0}) : limitPart (limitPart μ) = limitPart μ := by
  have h := limitPart_limitPart_add_nat μ 0
  simpa using h

/-- A value between `limitPart μ` and `limitPart μ + K'` has the limit part of `μ`. -/
theorem limitPart_eq_of_le_of_lt {μ z : Ordinal.{0}} {K' : ℕ} (h1 : limitPart μ ≤ z)
    (h2 : z < limitPart μ + K') : limitPart z = limitPart μ := by
  apply le_antisymm
  · have := limitPart_mono h2.le
    rwa [limitPart_limitPart_add_nat] at this
  · have := limitPart_mono h1
    rwa [limitPart_limitPart] at this

theorem le_visibilityReplace_self (μ : Ordinal.{0}) (K : ℕ) : μ ≤ visibilityReplace μ K K := by
  unfold visibilityReplace ordinalReplace
  split
  · next h =>
    calc μ = limitPart μ + finitePart μ := (decomposition μ).symm
      _ ≤ limitPart μ + K := add_le_add (le_refl _) ((Nat.cast_le (α := Ordinal.{0})).mpr h.le)
  · exact le_rfl

theorem le_extVisibilityReplace_self (v : ExtOrd) (K : ℕ) : v ≤ extVisibilityReplace v K K := by
  rcases ExtOrd.cases v with rfl | rfl | ⟨μ, rfl⟩
  · simp
  · simp
  · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
    exact le_visibilityReplace_self μ K

end Value

end VaughtConjecture.Knight
