/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Tower

/-! # The block schedule, without stopping-rank machinery

Elementary stage arithmetic used by both receiving and the later rank analysis. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value

/-! ### The canonical block schedule -/

/-- The canonical block levels as limit stages: `blockStage ξ := ⟨blockLevel ξ, _⟩` with
`blockLevel ξ = ω + ω·ξ` (`Knight/Value.lean`).  The stage schedule of the Knight stopping rank:
block `ξ` runs from its terminal level `blockStage ξ` to its failed target `blockStage (ξ + 1)`. -/
noncomputable def blockStage (ξ : Ordinal.{0}) : LimitStage :=
  ⟨blockLevel ξ, isSuccLimit_blockLevel ξ⟩

@[simp] theorem blockStage_toOrdinal (ξ : Ordinal.{0}) :
    (blockStage ξ).toOrdinal = blockLevel ξ := rfl

theorem blockStage_strictMono : StrictMono blockStage :=
  fun _ _ h => Subtype.mk_lt_mk.mpr (blockLevel_strictMono h)

theorem blockStage_mono : Monotone blockStage := blockStage_strictMono.monotone

theorem blockStage_le_blockStage_iff {ξ η : Ordinal.{0}} :
    blockStage ξ ≤ blockStage η ↔ ξ ≤ η := blockStage_strictMono.le_iff_le

theorem blockStage_lt_blockStage_iff {ξ η : Ordinal.{0}} :
    blockStage ξ < blockStage η ↔ ξ < η := blockStage_strictMono.lt_iff_lt

/-- The base stage is `ω`: sources of the Knight rank are models of `S^ω`. -/
theorem blockStage_zero : blockStage 0 = ⟨Ordinal.omega0, Ordinal.isSuccLimit_omega0⟩ :=
  Subtype.ext blockLevel_zero

/-- The failed target of block `0` is `ω + ω`. -/
theorem blockStage_one_toOrdinal : (blockStage 1).toOrdinal = Ordinal.omega0 + Ordinal.omega0 := by
  simp [blockLevel]

/-- The failed target of block `ξ` is one `ω`-block above its terminal level. -/
theorem blockStage_succ_toOrdinal (ξ : Ordinal.{0}) :
    (blockStage (ξ + 1)).toOrdinal = blockLevel ξ + Ordinal.omega0 := by
  rw [blockStage_toOrdinal, ← Order.succ_eq_add_one, blockLevel_succ]

namespace KnightRealization

/-- The base-source stage bound. -/
theorem blockStage_zero_le (ξ : Ordinal.{0}) : blockStage 0 ≤ blockStage ξ :=
  blockStage_mono (zero_le : (0 : Ordinal.{0}) ≤ ξ)

/-- Terminal stage to failed target of the same block. -/
theorem blockStage_le_succ (ξ : Ordinal.{0}) : blockStage ξ ≤ blockStage (ξ + 1) :=
  blockStage_mono (le_self_add : ξ ≤ ξ + 1)

end KnightRealization


end VaughtConjecture.Knight
