/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Directedness

/-! # Top-grade growth or eventual constancy

The order-theoretic half of the top-grade split used in Cor. 5.3.8: on the directed
labelled-cover poset the monotone top grade either grows cofinally (`HasTopGradeGrowth`) or is
constant on a coinitial tail (`hasTopGradeGrowth_or_coinitial_constant`).  Uses only
directedness and monotonicity of `topGrade`.  The semantic bridge — growth excludes finite
characteristic arity; a coinitial constant top grade `K` gives characteristic arity `K` — is
the next lane.

Construction-private (not root-exported).  Reviewer probe (2026-09-03), graduated. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower KnightRealization

universe w

variable {alpha : LimitStage} {M : Type w} {R : KnightRealization alpha M}

/-- The monotone natural-valued top grade on the directed labelled-cover poset either grows
cofinally or is constant on a coinitial tail.  This is the order-theoretic half of the
top-grade split used in Cor. 5.3.8. -/
theorem KnightRealization.hasTopGradeGrowth_or_coinitial_constant
    (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering) :
    R.HasTopGradeGrowth ∨
      ∃ K : ℕ, IsCoinitial {x : R.LabelledExt | x.type.topGrade = K} := by
  let := KnightRealization.nonempty_labelledExt hcov
  let := labelledExt_isDirectedOrder hcons hcov
  rcases DirectedNat.eventually_constant_or_tendsto
      (f := fun x : R.LabelledExt => x.type.topGrade)
      (fun _ _ h => LabelledExt.topGrade_mono h) with ⟨K, hK⟩ | hg
  · exact Or.inr ⟨K, (isCoinitial_iff_eventually hcons hcov _).mpr hK⟩
  · left
    intro K x
    obtain ⟨y, hy⟩ := Filter.tendsto_atTop_atTop.mp hg (K + 1)
    obtain ⟨z, hxz, hyz⟩ := exists_ge_ge x y
    exact ⟨z, hy z hyz, hxz⟩

/-- Model-facing compatibility wrapper. -/
theorem KnightRealization.IsModel.hasTopGradeGrowth_or_coinitial_constant
    (hR : R.IsModel) :
    R.HasTopGradeGrowth ∨ ∃ K : ℕ, IsCoinitial {x : R.LabelledExt | x.type.topGrade = K} :=
  KnightRealization.hasTopGradeGrowth_or_coinitial_constant hR.consistent hR.covering

end VaughtConjecture.Knight
