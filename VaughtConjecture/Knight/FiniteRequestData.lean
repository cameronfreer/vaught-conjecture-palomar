/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model

/-! # Finite request data and elementary countability

Pattern codes retain their original admissibility predicate. This module contains no
request enumeration, scheduler, or stopping-rank theory.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

variable {α : Ordinal.{0}} {n : ℕ}

/-! ### The bottom-pattern quotient theorem -/

/-- **The bottom-pattern quotient** (scratch-compiled by the user, 2026-08-26):
`BottomPatternFamily D q'` depends only on the finite bottom/non-bottom pattern of `q'` on
the cells of grade at most `n`, not on the full unbounded labelling. -/
theorem bottomPatternFamily_eq_of_pattern_eq {D : SemScheme (n + 1)}
    (q₁ q₂ : Cell D.scheme → ExtOrd)
    (hpat : ∀ Θ : D.scheme.below (Finset.univ, n),
      q₁ Θ.1 = ⊥ ↔ q₂ Θ.1 = ⊥) :
    BottomPatternFamily (α := α) D q₁ = BottomPatternFamily D q₂ := by
  ext q
  constructor
  · rintro ⟨hD, hq⟩
    exact ⟨hD, fun Θ => (hq Θ).trans (hpat Θ)⟩
  · rintro ⟨hD, hq⟩
    exact ⟨hD, fun Θ => (hq Θ).trans (hpat Θ).symm⟩

namespace FixedHeight

/-! ### Pattern codes at an arbitrary limit stage

The stage-`ω` versions live in `Knight/Sentence.lean` (`BotPattern`, `PatternFamily`,
`IsPatternOf`); they are reproduced here at an arbitrary stage, namespaced `FixedHeight` to
keep the lane quarantined. -/

/-- A `−∞`-pattern on `D^{≤ n} = D⟨A, n⟩` (the cells of grade `≤ n`): a finite code. -/
abbrev BotPattern (D : SemScheme (n + 1)) : Type :=
  D.scheme.below (Finset.univ, n) → Bool

/-- The cofaces with domain `D` and `−∞`-pattern `π` on `D^{≤ n}`. -/
def PatternFamily (α : Ordinal.{0}) (D : SemScheme (n + 1)) (π : BotPattern D) :
    Set (S α (n + 1)) :=
  {q | ∃ h : q.scheme = D, ∀ Θ : D.scheme.below (Finset.univ, n),
    q.label (SemScheme.castCell h.symm Θ.1) = ⊥ ↔ π Θ = true}

/-- `BottomPatternFamily D q'` is the pattern family of the pattern of `q'`: the census may
enumerate codes in place of labellings. -/
theorem bottomPatternFamily_eq_patternFamily {D : SemScheme (n + 1)}
    (q' : Cell D.scheme → ExtOrd) (π : BotPattern D)
    (hπ : ∀ Θ, q' Θ.1 = ⊥ ↔ π Θ = true) :
    BottomPatternFamily (α := α) D q' = PatternFamily α D π := by
  ext q
  simp only [BottomPatternFamily, PatternFamily, Set.mem_ofPred_eq, hπ]

/-- `π` is the `−∞`-pattern of some labelling `q'` of `D` respecting the semantics of `D`
(faithfully, no stage bound) and extending `p` along the initial face — the paper's clause
(4)(a)(ii) parameter, seen through its pattern. -/
def IsPatternOf (p : S α n) (D : SemScheme (n + 1)) (π : BotPattern D) : Prop :=
  ∃ hD : ExtendsDomain p D, ∃ q' : Cell D.scheme → ExtOrd,
    RespectsSemantics D.rows q' ∧ (∀ d, q' (hD.cellOf d) = p.label d) ∧
      ∀ Θ, (q' Θ.1 = ⊥ ↔ π Θ = true)

/-! ### Elementary countability -/

variable {M : Type w}

/-- Injective tuples on a countable carrier are countable. -/
instance countable_emb [Countable M] (n : ℕ) : Countable (Fin n ↪ M) :=
  Function.Injective.countable (f := fun f : Fin n ↪ M => (f : Fin n → M))
    DFunLike.coe_injective

/-- The ordinals strictly below a countable ordinal are countable. -/
theorem countable_lt (hβ : α.card ≤ Cardinal.aleph0) :
    Countable {γ : Ordinal.{0} // γ < α} :=
  ((Ordinal.countable_Iic_of_card_le_aleph0 hβ).mono Set.Iio_subset_Iic_self).to_subtype

end FixedHeight
end VaughtConjecture.Knight
