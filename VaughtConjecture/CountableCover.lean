/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Set.Countable

/-! # Countability from an overlapping cover by subsingleton conditions

The descriptions need not form a partition or a canonical invariant. Choosing any covering
description gives an injection into the countable index type. No model theory is used.
-/

@[expose] public section

namespace VaughtConjecture.CountableCover

/-- Countably many conditions, each met by at most one member of a family and jointly
covering it, make the family countable. -/
theorem countable_of_cover {ι κ : Type*} [Countable κ] (P : κ → ι → Prop)
    (hsub : ∀ c i j, P c i → P c j → i = j) (hcover : ∀ i, ∃ c, P c i) : Countable ι := by
  choose c hc using hcover
  refine Function.Injective.countable (f := c) fun i j h => hsub (c i) i j (hc i) ?_
  rw [h]
  exact hc j

end VaughtConjecture.CountableCover
