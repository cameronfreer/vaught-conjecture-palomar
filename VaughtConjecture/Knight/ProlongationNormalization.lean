/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Approximation.Prolongation
public import VaughtConjecture.Knight.ModelMap

/-! # Same-carrier normalization of certified links (#166 follow-up)

The target class `IsModelClass` (Knight's model axioms, Def. 3.2.1, as a class for certified
prolongation) and the normalization theorem `prolongsToIn_isModelClass_iff_on`: by
`IsModel.map` (`Knight/ModelMap.lean`) the model class is closed under push-forward, so by
the generic `prolongsToIn_iff_prolongsToOnIn` every certified link `ProlongsToIn IsModel`
normalizes to Knight's literal Def. 5.1.1 shape — an actual model **on the carrier of the
source** whose reduct **equals** the source.

This sits just above `Knight/ModelMap.lean` and below `Knight/Rank.lean`: the source
construction (`Knight/EndogenousExtension.lean`) consumes normalization without importing
the intrinsic-rank lower-bound layer.  Reduct-closure of the class (`isModelClass_reduct`)
stays in `Knight/Rank.lean` with the block machinery it serves. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

namespace KnightRealization

/-- Knight's model axioms (Def. 3.2.1) as a **target class** for certified prolongation
(`ProlongsToIn IsModelClass` is Knight-VC's `PaperExactModelExpandsTo`). -/
abbrev IsModelClass : ∀ {δ : LimitStage} {N : Type w}, KnightRealization δ N → Prop :=
  fun R => R.IsModel

/-- The model class is closed under push-forward along a bijection of carriers
(`IsModel.map`, `Knight/ModelMap.lean`; the missing lemma of the #73 audit): the map-closure
hypothesis of `prolongsToIn_iff_prolongsToOnIn`, discharged once for Knight. -/
theorem isModelClass_map {δ : LimitStage} {N N' : Type w} (e : N ≃ N')
    (R' : KnightRealization δ N) (hR' : IsModelClass R') : IsModelClass (R'.map e) :=
  hR'.map e

/-- **Every certified link normalizes to a literal fixed-carrier reduct equation** (Knight's
Def. 5.1.1 verbatim): `R` prolongs to `δ'` through actual models iff some actual model **on
the carrier of `R` itself** reduces **exactly** to `R`.  Immediate from `IsModel.map` via the
generic `prolongsToIn_iff_prolongsToOnIn`; this is what lets the #46 limit construction
consume chains of literal reduct equations (`KnightRealization.IsReductChain`) with no loss
against the up-to-isomorphism links. -/
theorem prolongsToIn_isModelClass_iff_on {δ δ' : LimitStage} {N : Type w}
    (R : KnightRealization δ N) (h : δ ≤ δ') :
    R.ProlongsToIn IsModelClass h ↔ R.ProlongsToOnIn IsModelClass h :=
  Realization.prolongsToIn_iff_prolongsToOnIn
    (fun e R' hR' => isModelClass_map e R' hR') R h

end KnightRealization

end VaughtConjecture.Knight
