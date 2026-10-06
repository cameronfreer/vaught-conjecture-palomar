/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.BlockStages
public import VaughtConjecture.Knight.Rank

/-! # Block geometry: compatibility import

The elementary schedule and comparison lemmas live in `BlockStages`. This old
entry point also reexports `Rank`, preserving its historical import interface.
-/
@[expose] public section

