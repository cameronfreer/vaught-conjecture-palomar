/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.BlockStages
public import VaughtConjecture.Knight.BlockReflection

/-! # Successor stages and the next block

This arithmetic bridge is independent of terminal defects and occurrence supply.
-/

@[expose] public section

namespace VaughtConjecture.Knight
open Value

/-- Successor block stages are next blocks. -/
theorem blockStage_succ_eq_nextBlock (ρ : Ordinal.{0}) :
    blockStage (ρ + 1) = (blockStage ρ).nextBlock := by
  apply Subtype.ext
  change blockLevel (ρ + 1) = blockLevel ρ + Ordinal.omega0
  have h := blockLevel_succ ρ
  rwa [Order.succ_eq_add_one] at h

end VaughtConjecture.Knight
