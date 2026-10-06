/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FullScopeBountiful

/-! # Same-scope grade extension: compatibility import

The general theorem `bountiful_same_scope` now lives with its full-scope
specialization in `FullScopeBountiful`. Both are derived from the common
bounded-tail splice; this path preserves all previous imports.
-/
@[expose] public section

