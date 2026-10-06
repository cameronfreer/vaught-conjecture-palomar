/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model

/-! # Finite-cut receiving: the observation interface

This is the existing receiving predicate, moved unchanged below its producers and
applications. Cutoffs are observations; no claim that arbitrary capping preserves
lawfulness is made. Exact consistency separately supplies literal root retention.
-/

@[expose] public section

namespace VaughtConjecture.Knight
open TypeTower StageType KnightRealization Value ExtOrd
universe w
variable {α : LimitStage} {M : Type w}

/-- **Finite-cut receiving** (FC): over a realized root `t ↦ p`, a legal one-point candidate `P`
over `p`, and a proper cutoff `δ` below the stage, some actual coface `q` over `t` on the exact
scheme of `P` agrees with `P` below `δ`. -/
def FiniteCutReceiving (R : KnightRealization α M) : Prop :=
  ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
    ∀ (P : S α.1 (n + 1)), IsCoface p P →
      ∀ δ : ExtOrd, ⊥ < δ → δ < ofOrd α.1 →
        ∃ (y : M) (hy : y ∉ Set.range t) (q : S α.1 (n + 1)), R.eval (snoc t y hy) = some q ∧
          ∃ h : q.scheme = P.scheme,
            ∀ d, min (q.label d) δ = min (P.label (SemScheme.castCell h d)) δ

end VaughtConjecture.Knight
