/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ActualLabelling
public import VaughtConjecture.Knight.StableLiftCore

/-! # Stable labels as an evaluator, before stable modelhood

Lawfulness needs consistency and covering of the source. Literal restriction
compatibility needs only consistency. No occurrence supply for the stable lift
or modelhood of that lift is used here.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.KnightRealization
open TypeTower StageType
noncomputable section
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}

/-- Stable labels form a lawful evaluator of actual source occurrences. -/
def stableActualLabelling (hcons : W.IsExactParentConsistent)
    (hcov : W.IsInitialSegmentCovering) : W.ActualLabelling where
  label := W.stableValue
  lawful := by intro n u p hp; exact stableLiftRespects_of_consistent hcons hcov hp
  mapCell := by
    intro n m u p v q hv f hfu hpq d
    exact stableValue_mapCell' hcons hv hfu hpq d

end
end VaughtConjecture.Knight.KnightRealization
