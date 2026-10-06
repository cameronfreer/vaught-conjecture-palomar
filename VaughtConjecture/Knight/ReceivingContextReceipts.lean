/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingContext

/-! # Literal root and private-class receipts for the receiving template

Compatibility import for `exists_relativeData_of_context_with_root`. The constructor now
lives in `ReceivingContext` and retains the literal root, top, root map and private bottom
class from the outset. Its original weaker interface is a projection of the same theorem.
-/
@[expose] public section

