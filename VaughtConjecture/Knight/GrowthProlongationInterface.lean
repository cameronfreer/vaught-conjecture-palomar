/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProlongationNormalization
public import VaughtConjecture.Knight.BlockStages
public import VaughtConjecture.Knight.Directedness

/-! # The growth continuation obligation, without characteristic compatibility

This interface states only the implication consumed by terminal counting. Its equivalence
with the characteristic-phrased boundary remains in `GrowthProlongationBoundary`, downstream
of the interface. Neither a continuation producer nor expansion uniqueness is assumed here.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower KnightRealization

universe w

/-- Lemma 5.5.1 in the paper's operational vocabulary: an infinity anchor
(non-hollowness) plus unbounded top grade produces the next-block expansion. -/
def GrowthAnchorProlongationAt {M : Type w} {rho : Ordinal.{0}}
    (W : KnightRealization (blockStage rho) M) : Prop :=
  (¬ W.IsHollow ∧ W.HasTopGradeGrowth) →
    W.ProlongsToIn IsModelClass (blockStage_le_succ rho)

end VaughtConjecture.Knight
