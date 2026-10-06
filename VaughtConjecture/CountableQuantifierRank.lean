/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Lomega1omega.QuantifierRank

/-! # Countable quantifier ranks for countably branching infinitary formulas

This is general logic: no Knight language, model construction, or stopping rank is imported. -/

@[expose] public section

namespace VaughtConjecture

open FirstOrder Language Cardinal

universe u v u'

/-- The quantifier rank of an `L_{ω₁ω}` formula (countable branching) is a countable ordinal. -/
theorem qrank_lt_ord_aleph_one {L : Language.{u, v}} {γ : Type u'} :
    ∀ {n : ℕ} (φ : L.BoundedFormulaInf ℕ γ n), φ.qrank < (aleph 1).ord := by
  intro n φ
  simpa only [Cardinal.ord_aleph] using BoundedFormulaω.qrank_lt_omega1 φ

end VaughtConjecture
