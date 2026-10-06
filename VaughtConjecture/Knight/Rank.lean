/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.BlockStages
public import VaughtConjecture.Approximation.Rank
public import VaughtConjecture.Knight.ProlongationNormalization
public import VaughtConjecture.Knight.ReductModel

/-! # Knight's stopping rank along the canonical block levels

The Knight façade of `Approximation/Rank.lean` (issue #70): the generic intrinsic
prolongability-through-a-block predicate and stopping rank, instantiated at

* the tower `knightTower` over the limit stages;
* the target class `C := IsModel` (Def. 3.2.1; `KnightRealization.IsModelClass`) — the rank
  measures **certified** prolongation through actual models (`ProlongsToIn IsModel`,
  `ProlongsToClassIn IsModel`, #111), never raw `ProlongsTo`;
* the schedule `blockStage ξ := ⟨blockLevel ξ, _⟩ : LimitStage`, the canonical block levels
  `ω + ω·ξ` of `Knight/Value.lean` (monotone — indeed strictly — by `blockLevel_strictMono`).

Reduct-closure of the target class is the strict model-reduction theorem `IsModel.reduct`
(#101/#112, `Knight/ReductModel.lean`), proved for arbitrary models, so downward closure of
`KnightRealization.ProlongsThroughBlock` is **unconditional** (`prolongsThroughBlock_mono`) —
no receipt, no selected history.

**Endpoint convention** (the `ξ = 0` sanity lemma `prolongsThroughBlock_zero_iff`,
`not_prolongsThroughBlock_zero_iff`): block `ξ` has *terminal level* `blockLevel ξ` and *failed
target* `blockLevel (ξ + 1) = blockLevel ξ + ω`; sources are models of `S^ω`, i.e. live at
`blockStage 0` (`blockStage_zero : blockStage 0 = ⟨ω, _⟩`), and
`¬ ProlongsThroughBlock R 0 ↔ NoProlongationToIn IsModel (blockStage 0 ≤ blockStage 1)` — from
`ω` to `ω + ω` (`blockStage_one_toOrdinal`) — is Knight-VC's `FailsAtAlphaOmega` at `α = ω`.

**Guard.**  `stopRank` is `sInf` of the failure set, so `sInf ∅ = 0`: it is a genuine first
failed block only under `HasFailure` (`stopRank_mem`, `prolongsThroughBlock_iff_lt_stopRank`,
`stopRank_eq_zero_iff`).  `HasFailure` is **termination** (a failure exists); the counting
kernel additionally needs `stopRank R < ω₁` (totality).  That every model of `S^ω` has a
countable failure — both facts — is the theorem of the history / linked-stop layer (#30/#31),
not assumed here.
`stopLevel R := blockLevel (stopRank R)` is the *terminal* level of the stopping block
(TERMINOLOGY: stopping index / stopping level), not the failed target. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value

universe w

namespace KnightRealization

variable {M : Type w}

/-- The model class is closed under reduction (`IsModel.reduct`, #101/#112): the reduct-closure
hypothesis of the generic layer, discharged once for Knight. -/
theorem isModelClass_reduct {δ δ' : LimitStage} (h : δ ≤ δ') {N : Type w}
    (R' : KnightRealization δ' N) (hR' : IsModelClass R') : IsModelClass (R'.reduct h) :=
  hR'.reduct h

/-! ### Prolongation through a block -/

/-- A model of `S^ω` (a realization at `blockStage 0`) **prolongs through block `ξ`**: it
prolongs, through actual models, to the failed target `blockStage (ξ + 1)` of block `ξ`
(terminal level `blockStage ξ`).  Intrinsic — defined from `ProlongsToIn IsModel`, not from a
selected history. -/
def ProlongsThroughBlock (R : KnightRealization (blockStage 0) M) (ξ : Ordinal.{0}) : Prop :=
  Realization.ProlongsThroughBlock IsModelClass blockStage blockStage_mono R ξ

theorem prolongsThroughBlock_iff (R : KnightRealization (blockStage 0) M) (ξ : Ordinal.{0})
    (h : blockStage 0 ≤ blockStage (ξ + 1)) :
    R.ProlongsThroughBlock ξ ↔ R.ProlongsToIn IsModelClass h := Iff.rfl

/-- **Endpoint sanity lemma**: through block `0` means certified prolongation from the terminal
level `blockStage 0` (`= ω`) to the failed target `blockStage 1` (`= ω + ω`). -/
theorem prolongsThroughBlock_zero_iff (R : KnightRealization (blockStage 0) M) :
    R.ProlongsThroughBlock 0 ↔
      R.ProlongsToIn IsModelClass (blockStage_mono (zero_le : (0 : Ordinal.{0}) ≤ 1)) :=
  Realization.prolongsThroughBlock_zero_iff R

/-- **Knight-VC's `FailsAtAlphaOmega` at `α = ω`**: failure at block `0` is no model prolongation
from `ω` to `ω + ω`. -/
theorem not_prolongsThroughBlock_zero_iff (R : KnightRealization (blockStage 0) M) :
    ¬ R.ProlongsThroughBlock 0 ↔
      R.NoProlongationToIn IsModelClass (blockStage_mono (zero_le : (0 : Ordinal.{0}) ≤ 1)) :=
  Realization.not_prolongsThroughBlock_zero_iff R

/-- **Unconditional downward closure** (reduct-closure of `IsModel` is `IsModel.reduct`). -/
theorem prolongsThroughBlock_mono {R : KnightRealization (blockStage 0) M}
    {ξ η : Ordinal.{0}} (hηξ : η ≤ ξ) (h : R.ProlongsThroughBlock ξ) :
    R.ProlongsThroughBlock η :=
  Realization.ProlongsThroughBlock.mono isModelClass_reduct hηξ h

theorem not_prolongsThroughBlock_of_le {R : KnightRealization (blockStage 0) M}
    {ξ η : Ordinal.{0}} (hηξ : η ≤ ξ) (h : ¬ R.ProlongsThroughBlock η) :
    ¬ R.ProlongsThroughBlock ξ :=
  fun h' => h (prolongsThroughBlock_mono hηξ h')

theorem IsIso.prolongsThroughBlock_iff {N : Type w} {R : KnightRealization (blockStage 0) M}
    {R₂ : KnightRealization (blockStage 0) N} {e : M ≃ N} (hi : R.IsIso R₂ e)
    (ξ : Ordinal.{0}) : R.ProlongsThroughBlock ξ ↔ R₂.ProlongsThroughBlock ξ :=
  Realization.IsIso.prolongsThroughBlock_iff hi ξ

theorem prolongsThroughBlock_iff_of_iso {N : Type w} {R : KnightRealization (blockStage 0) M}
    {R₂ : KnightRealization (blockStage 0) N} (h : Nonempty (R.Iso R₂)) (ξ : Ordinal.{0}) :
    R.ProlongsThroughBlock ξ ↔ R₂.ProlongsThroughBlock ξ :=
  Realization.prolongsThroughBlock_iff_of_iso h ξ

/-- Prolongation through block `ξ` of an **isomorphism class of stage-`ω` realizations with
model-certified prolongation targets** (lift of the certified `ProlongsToClassIn IsModel`;
`IsModelClass` constrains the target, not the source — the quotient contains all stage-`ω`
realizations; restricting/transporting to `knightModelSetoid` and the sentence-model quotient
is #77). -/
def ProlongsThroughBlockClass (q : Quotient (Realization.isoSetoid knightTower (blockStage 0) M))
    (ξ : Ordinal.{0}) : Prop :=
  Realization.ProlongsThroughBlockClass IsModelClass blockStage blockStage_mono q ξ

@[simp]
theorem prolongsThroughBlockClass_mk (R : KnightRealization (blockStage 0) M) (ξ : Ordinal.{0}) :
    ProlongsThroughBlockClass (Quotient.mk _ R) ξ ↔ R.ProlongsThroughBlock ξ := Iff.rfl

theorem ProlongsThroughBlockClass.mono
    {q : Quotient (Realization.isoSetoid knightTower (blockStage 0) M)} {ξ η : Ordinal.{0}}
    (hηξ : η ≤ ξ) (h : ProlongsThroughBlockClass q ξ) : ProlongsThroughBlockClass q η :=
  Realization.ProlongsThroughBlockClass.mono isModelClass_reduct hηξ h

/-! ### The stopping rank -/

/-- `R` **has a failure**: some block is not prolonged through.  Totality (every model of `S^ω`
has a failure below `ω₁`) is #30/#31's theorem. -/
def HasFailure (R : KnightRealization (blockStage 0) M) : Prop :=
  Realization.HasFailure IsModelClass blockStage blockStage_mono R

/-- The **stopping rank** (stopping index) of a model of `S^ω`: the least block it does not
prolong through, `sInf {ξ | ¬ R.ProlongsThroughBlock ξ}`.  Caveat: `sInf ∅ = 0`, so without
`HasFailure` the value `0` carries no information; under `HasFailure` it is the first failed
block (`stopRank_mem`, `prolongsThroughBlock_iff_lt_stopRank`).  Its terminal level is
`stopLevel R = blockLevel (stopRank R)`; its failed target is `blockLevel (stopRank R + 1)`. -/
noncomputable def stopRank (R : KnightRealization (blockStage 0) M) : Ordinal.{0} :=
  Realization.stopRank IsModelClass blockStage blockStage_mono R

/-- The **stopping level**: the terminal level `ω + ω · stopRank R` of the stopping block (where
a terminal witness lives), not the failed target `stopLevel R + ω`. -/
noncomputable def stopLevel (R : KnightRealization (blockStage 0) M) : Ordinal.{0} :=
  blockLevel (stopRank R)

theorem stopLevel_def (R : KnightRealization (blockStage 0) M) :
    stopLevel R = Ordinal.omega0 + Ordinal.omega0 * stopRank R := rfl

theorem stopRank_le_of_not {R : KnightRealization (blockStage 0) M} {ξ : Ordinal.{0}}
    (h : ¬ R.ProlongsThroughBlock ξ) : stopRank R ≤ ξ :=
  Realization.stopRank_le_of_not h

/-- Under `HasFailure`, `R` fails at its stopping rank. -/
theorem stopRank_mem {R : KnightRealization (blockStage 0) M} (h : HasFailure R) :
    ¬ R.ProlongsThroughBlock (stopRank R) :=
  Realization.stopRank_mem h

theorem prolongsThroughBlock_of_lt_stopRank {R : KnightRealization (blockStage 0) M}
    {ξ : Ordinal.{0}} (h : ξ < stopRank R) : R.ProlongsThroughBlock ξ :=
  Realization.prolongsThroughBlock_of_lt_stopRank h

/-- **First-failure characterisation** under `HasFailure` (downward closure is unconditional). -/
theorem prolongsThroughBlock_iff_lt_stopRank {R : KnightRealization (blockStage 0) M}
    (hR : HasFailure R) (ξ : Ordinal.{0}) : R.ProlongsThroughBlock ξ ↔ ξ < stopRank R :=
  Realization.prolongsThroughBlock_iff_lt_stopRank isModelClass_reduct hR ξ

theorem not_prolongsThroughBlock_iff_stopRank_le {R : KnightRealization (blockStage 0) M}
    (hR : HasFailure R) (ξ : Ordinal.{0}) : ¬ R.ProlongsThroughBlock ξ ↔ stopRank R ≤ ξ :=
  Realization.not_prolongsThroughBlock_iff_stopRank_le isModelClass_reduct hR ξ

/-- Under `HasFailure`, rank `0` is failure at block `0`: no model prolongation from `ω` to
`ω + ω` (`FailsAtAlphaOmega`). -/
theorem stopRank_eq_zero_iff {R : KnightRealization (blockStage 0) M} (hR : HasFailure R) :
    stopRank R = 0 ↔ ¬ R.ProlongsThroughBlock 0 :=
  Realization.stopRank_eq_zero_iff hR

theorem stopRank_eq_zero_of_not_hasFailure {R : KnightRealization (blockStage 0) M}
    (h : ¬ HasFailure R) : stopRank R = 0 :=
  Realization.stopRank_eq_zero_of_not_hasFailure h

theorem HasFailure.of_stopRank_pos {R : KnightRealization (blockStage 0) M}
    (h : 0 < stopRank R) : HasFailure R :=
  Realization.HasFailure.of_stopRank_pos h

/-! ### Isomorphism invariance and the class rank -/

theorem IsIso.hasFailure_iff {N : Type w} {R : KnightRealization (blockStage 0) M}
    {R₂ : KnightRealization (blockStage 0) N} {e : M ≃ N} (hi : R.IsIso R₂ e) :
    HasFailure R ↔ HasFailure R₂ :=
  Realization.IsIso.hasFailure_iff hi

/-- **The stopping rank is an isomorphism invariant** (unconditional). -/
theorem IsIso.stopRank_eq {N : Type w} {R : KnightRealization (blockStage 0) M}
    {R₂ : KnightRealization (blockStage 0) N} {e : M ≃ N} (hi : R.IsIso R₂ e) :
    stopRank R = stopRank R₂ :=
  Realization.IsIso.stopRank_eq hi

theorem stopRank_eq_of_iso {N : Type w} {R : KnightRealization (blockStage 0) M}
    {R₂ : KnightRealization (blockStage 0) N} (h : Nonempty (R.Iso R₂)) :
    stopRank R = stopRank R₂ :=
  Realization.stopRank_eq_of_iso h

theorem stopLevel_eq_of_iso {N : Type w} {R : KnightRealization (blockStage 0) M}
    {R₂ : KnightRealization (blockStage 0) N} (h : Nonempty (R.Iso R₂)) :
    stopLevel R = stopLevel R₂ :=
  congrArg blockLevel (stopRank_eq_of_iso h)

/-- Termination (`HasFailure`) on isomorphism classes of stage-`ω` realizations with
model-certified prolongation targets. -/
def HasFailureClass (q : Quotient (Realization.isoSetoid knightTower (blockStage 0) M)) : Prop :=
  Realization.HasFailureClass IsModelClass blockStage blockStage_mono q

@[simp]
theorem hasFailureClass_mk (R : KnightRealization (blockStage 0) M) :
    HasFailureClass (Quotient.mk _ R) ↔ HasFailure R := Iff.rfl

/-- The **stopping rank of an isomorphism class of stage-`ω` realizations with model-certified
prolongation targets** — the rank the counting kernel consumes once the `stopRank < ω₁` bound
(totality) and countable fibres are supplied (#30/#31; #77 transports the `< ω₁` theorem, not
merely `HasFailure`). -/
noncomputable def stopRankClass
    (q : Quotient (Realization.isoSetoid knightTower (blockStage 0) M)) : Ordinal.{0} :=
  Realization.stopRankClass IsModelClass blockStage blockStage_mono q

@[simp]
theorem stopRankClass_mk (R : KnightRealization (blockStage 0) M) :
    stopRankClass (Quotient.mk _ R) = stopRank R := rfl

theorem prolongsThroughBlockClass_iff_lt_stopRankClass
    {q : Quotient (Realization.isoSetoid knightTower (blockStage 0) M)} (hq : HasFailureClass q)
    (ξ : Ordinal.{0}) : ProlongsThroughBlockClass q ξ ↔ ξ < stopRankClass q :=
  Realization.prolongsThroughBlockClass_iff_lt_stopRankClass isModelClass_reduct hq ξ

end KnightRealization

end VaughtConjecture.Knight
