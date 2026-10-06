/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProlongationNormalization
public import VaughtConjecture.Knight.ReductModel

/-! # The source `⊤`-flag and its production from certified prolongability (#47)

The forward half of the progress-or-stop branch of #47, lowered out of the rank layer so the
producer (`Knight/SelfCopyProducer.lean`, #42) can consume it without reaching `Knight/Rank`:

* `KnightRealization.SourceTopProduction` — the supplied `⊤`-flag obligation of the
  finite-block step (#42/#151), as a predicate on the source: over every labelled source
  tuple, a one-point extension carrying an `∞` cell of full grade is realized.

* `KnightRealization.sourceTopProduction_of_prolongsToIn` — certified prolongability
  produces the flag, by the three-move route: same-carrier normalization
  (`prolongsToIn_isModelClass_iff_on`), high-grade dominance of the normalized target at
  `γ = A₀` (clause (4)(c) of Def. 3.2.1), and the forcing certificate
  (`truncExt_eq_top_of_ge`) under reduction.

The contrapositive (`noProlongationToIn_of_not_sourceTopProduction`) and the stopping-rank
corollaries (`HasFailure`, `stopRank = 0`) remain in `Knight/TopProduction.lean`, which
legitimately imports the rank layer they are about.  This module imports only the
normalization layer and the reduct-of-a-model layer (the same boundary as
`Knight/EndogenousExtension.lean`). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe w

namespace KnightRealization

variable {A₀ : LimitStage} {M : Type w}

/-- **The `⊤`-flag production** (the FIRST unresolved producer obligation of the #146
verdict, isolated as supplied data): over every labelled source tuple, the source realizes
a one-point extension carrying an `∞` cell of full grade.  No compiled clause of
`IsModel` produces this (clauses (4)(b)/(c) bound their witnesses only from below by
ordinals `< α`, and a witness may always be proper); by the forcing certificate it cannot
be replaced by row construction on the target side.  It is exactly the block-level form of
the flag `step_highGradeDominance_topFlagged` consumes pointwise. -/
def SourceTopProduction (Rs : KnightRealization A₀ M) : Prop :=
  ∀ {k : ℕ} (e : Fin k ↪ M) (s : S A₀.1 k), Rs.eval e = some s →
    ∃ (z : M) (hz : z ∉ Set.range e) (s' : S A₀.1 (k + 1)),
      Rs.eval (snoc e z hz) = some s' ∧
      ∃ Sig : Cell s'.scheme.scheme, s'.scheme.scheme.grade Sig = k + 1 ∧
        s'.label Sig = ⊤

variable {Rs : KnightRealization A₀ M}

/-- **Certified prolongability produces the `⊤`-flag** (#47, progress branch): if `Rs`
prolongs through actual models to a strictly higher limit stage `B`, then over every
labelled source tuple the source realizes a one-point extension carrying an `∞` cell of
full grade.  Same-carrier normalization + high-grade dominance at `γ = A₀` + the forcing
certificate `truncExt_eq_top_of_ge`. -/
theorem sourceTopProduction_of_prolongsToIn {B : LimitStage} (hlt : A₀ < B)
    (hp : Rs.ProlongsToIn IsModelClass hlt.le) : Rs.SourceTopProduction := by
  -- 1. Normalize to a literal fixed-carrier reduct: an actual model on `M` itself.
  obtain ⟨R', hR', hred⟩ := (prolongsToIn_isModelClass_iff_on Rs hlt.le).mp hp
  intro k e s hs
  -- Lift the source label to a target label.
  have hs' : (R'.reduct hlt.le).eval e = some s := by rw [hred]; exact hs
  obtain ⟨p, hpe, -⟩ := eval_reduct_eq_some hlt.le hs'
  -- 2. High-grade dominance at `γ = A₀ < B` over the lifted tuple.
  obtain ⟨y, hy, q, ⟨Sig, hgrade, hlab⟩, -, hq⟩ :=
    hR'.highGradeDominance e p hpe A₀.1 hlt
  -- 3. Reduce the witness: the proper target-high label truncates to `⊤`.
  refine ⟨y, hy, reduceType A₀.2 hlt.le q, ?_, Sig, hgrade, truncExt_eq_top_of_ge hlab.le⟩
  have : (R'.reduct hlt.le).eval (snoc e y hy) = some (reduceType A₀.2 hlt.le q) := by
    rw [Realization.reduct_eval, hq]; rfl
  rwa [hred] at this

end KnightRealization

end VaughtConjecture.Knight
