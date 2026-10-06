/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CapStableModel

/-! # Non-hollow growth prolongs through cap-native stable modelhood

The stable candidate is consistent and covering before it is known to be a
model. Positive-root stable receiving supplies cap requests; finite attachment
handles the empty root. The general cap-to-model theorem then supplies modelhood.
The literal stable reduct equation gives an actual next-block expansion on the
same carrier, without passing through the selected occurrence package.

The historical theorem names are retained and reexported by
`NonHollowGrowthReceiving`, which keeps the optional selected-donor application.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.NonHollowGrowthReceiving
open TypeTower KnightRealization
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}

/-- Modelhood of the canonical stable lift from constructed cap receiving,
without assuming stable modelhood or an occurrence supply. -/
theorem stableLift_isModel (hM : W.IsModel) (hh : ¬ W.IsHollow)
    (hg : W.HasTopGradeGrowth) : (KnightRealization.stableLift hM).IsModel :=
  CapStableModel.isModel hM hh hg

/-- An actual next-block model on the same carrier, reducing literally to
the original non-hollow growth model. -/
theorem exists_nextBlock_model (hM : W.IsModel) (hh : ¬ W.IsHollow)
    (hg : W.HasTopGradeGrowth) :
    ∃ V : KnightRealization α.nextBlock M, V.IsModel ∧ V.reduct α.le_nextBlock = W :=
  ⟨KnightRealization.stableLift hM, stableLift_isModel hM hh hg, stableLift_reduct hM⟩

/-- The same expansion at any target equal to the next block; the stage
inequality proof does not affect the literal reduct equation. -/
theorem prolongsToOnIn_of_eq_nextBlock (hM : W.IsModel) (hh : ¬ W.IsHollow)
    (hg : W.HasTopGradeGrowth) {β : LimitStage} (hβ : β = α.nextBlock)
    (hle : α ≤ β) : W.ProlongsToOnIn IsModelClass hle := by
  subst β
  exact exists_nextBlock_model hM hh hg

end VaughtConjecture.Knight.NonHollowGrowthReceiving
