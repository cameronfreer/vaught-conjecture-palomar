/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Value

/-! # Ordinal bands below a successor limit

The ordinal arithmetic used by model reduction and finite restricted composition,
with no stage-type, model or receiving imports.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open Value

/-- Below a limit ordinal `α`, the band `[γ, γ + ω)` of any `γ < α` lies below `α`: write
`γ = limitPart γ + finitePart γ`, so `γ + ω = limitPart γ + ω`, and `limitPart γ < α` are both
multiples of `ω`. -/
theorem add_omega0_le_of_lt_isSuccLimit {γ α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    (h : γ < α) : γ + Ordinal.omega0 ≤ α := by
  obtain ⟨k, rfl⟩ : Ordinal.omega0 ∣ α :=
    Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hα.isSuccPrelimit
  have h1 : limitPart γ < Ordinal.omega0 * k := (limitPart_le γ).trans_lt h
  rw [← decomposition γ, add_assoc, Ordinal.natCast_add_omega0, limitPart, ← Ordinal.mul_succ]
  exact mul_le_mul_right
    (Order.succ_le_of_lt ((mul_lt_mul_iff_right₀ Ordinal.omega0_pos).mp h1)) _

end VaughtConjecture.Knight
