/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Lattice.Nat

/-! # Stabilization of directed natural-valued observations

These elementary order/filter facts have no model-theoretic hypotheses. A monotone
natural-valued observation on a nonempty directed preorder either attains a maximum and
is eventually constant, or tends to infinity. Finite synchronization is filter intersection.
-/

@[expose] public section

namespace VaughtConjecture.DirectedNat

open Filter

variable {D : Type*} [Preorder D] [Nonempty D] [IsDirectedOrder D]
  {f : D → ℕ}

/-- A bounded monotone observation attains its eventual constant value. -/
theorem eventually_eq_of_bddAbove (hf : Monotone f) (hb : BddAbove (Set.range f)) :
    ∃ i : D, ∀ᶠ j in atTop, f j = f i := by
  obtain ⟨i, hi⟩ := Nat.sSup_mem (Set.range_nonempty f) hb
  refine ⟨i, eventually_atTop.mpr ⟨i, fun j hij => ?_⟩⟩
  exact le_antisymm ((le_csSup hb ⟨j, rfl⟩).trans_eq hi.symm) (hf hij)

/-- Cofinal occurrences of one value of a monotone observation are eventual constancy. -/
theorem frequently_eq_iff_eventually_eq (hf : Monotone f) (k : ℕ) :
    (∃ᶠ i in atTop, f i = k) ↔ ∀ᶠ i in atTop, f i = k := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := frequently_atTop.mp h (Classical.arbitrary D)
    refine eventually_atTop.mpr ⟨i, fun j hij => ?_⟩
    obtain ⟨l, hjl, hl⟩ := frequently_atTop.mp h j
    exact le_antisymm (hl ▸ hf hjl) (hi ▸ hf hij)
  · exact Eventually.frequently

/-- The bounded/unbounded dichotomy for monotone natural-valued observations. -/
theorem eventually_constant_or_tendsto (hf : Monotone f) :
    (∃ k : ℕ, ∀ᶠ i in atTop, f i = k) ∨ Tendsto f atTop atTop := by
  by_cases hb : BddAbove (Set.range f)
  · obtain ⟨i, hi⟩ := eventually_eq_of_bddAbove hf hb
    exact Or.inl ⟨f i, hi⟩
  · right
    apply hf.tendsto_atTop_atTop_iff.mpr
    intro k
    by_contra h
    push Not at h
    exact hb ⟨k, by rintro _ ⟨i, rfl⟩; exact (h i).le⟩

/-- Finitely many eventual requirements hold on a common tail above any chosen base. -/
theorem synchronize {ι : Type*} [Finite ι] (P : ι → D → Prop)
    (hP : ∀ i, ∀ᶠ d in atTop, P i d) (base : D) :
    ∃ d, base ≤ d ∧ ∀ e, d ≤ e → ∀ i, P i e := by
  obtain ⟨d, hd⟩ := eventually_atTop.mp (Filter.eventually_all.mpr hP)
  obtain ⟨e, hbe, hde⟩ := exists_ge_ge base d
  exact ⟨e, hbe, fun e' he' => hd e' (hde.trans he')⟩

end VaughtConjecture.DirectedNat
