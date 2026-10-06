/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.SetTheory.Ordinal.Basic
public import VaughtConjecture.Approximation.Prolongation

/-! # Intrinsic prolongability through blocks and the stopping rank

The **intrinsic, isomorphism-invariant stopping rank** of a realization (issue #70; TERMINOLOGY:
*stopping index* / *stopping rank*), defined from the certified prolongation predicate
`Realization.ProlongsToIn C` of `Approximation/Prolongation.lean` along a **supplied stage
schedule** — never from a selected coherent history (DESIGN §3, EXPERIMENTS A2/B1; banned
identification 4).

**Schedule.**  The generic layer does not know Knight's canonical block levels
`blockLevel ξ = ω + ω·ξ` (DESIGN §2: `Approximation/` imports `TypeTower/` only).  A schedule is
just a monotone map `sched : Ordinal → Λ` from ordinals into the stages: `sched ξ` is the
*terminal level* of block `ξ` (the last level reached by a realization that gets through blocks
`< ξ`), and `sched (ξ + 1)` is the *failed target* of block `ξ`.  Monotonicity is exactly what
the theorems consume (`sched 0 ≤ sched (ξ + 1)` to state the predicate, `sched (η + 1) ≤
sched (ξ + 1)` for downward closure); strictness plays no role here (it matters for totality and
cofinality, which are #30/#31's business).  No schedule structure or class is introduced.

**Sources** live at the base stage `sched 0` (Knight: models of `S^ω`, `blockLevel 0 = ω`);
this keeps every statement free of "`ξ₀ ≤ ξ`" bookkeeping.

**Endpoint convention** (pinned by `prolongsThroughBlock_zero_iff`): `ProlongsThroughBlock C
sched hmono R ξ` says that `R` prolongs, within `C`, to the failed target `sched (ξ + 1)` of
block `ξ` — so "through block `0`" means from `sched 0` to `sched 1` (Knight-VC's
`FailsAtAlphaOmega` at `α = ω` is `¬ ProlongsThroughBlock … 0`), and the *terminal level* of
a realization of rank `ξ` is `sched ξ`, not `sched (ξ + 1)`.

**Rank.**  `stopRank C sched hmono R := sInf {ξ | ¬ ProlongsThroughBlock C sched hmono R ξ}`.
This is a total function because `sInf ∅ = 0` on ordinals — so **`stopRank` is a genuine first
failure only when a failure exists**, which is the explicit predicate `HasFailure` (`∃ ξ, ¬
ProlongsThroughBlock … R ξ`, isomorphism-invariant).  Every "fails at `stopRank`" / "first
failure" lemma takes `HasFailure` as a hypothesis (`stopRank_mem`,
`prolongsThroughBlock_iff_lt_stopRank`, `stopRank_eq_zero_iff`).  `HasFailure` is
**termination** (existence of a failure), not the counting kernel's totality: the kernel
(`Spectrum/RankCount.lean`) needs the stronger `stopRank R < ω₁`.  Both are theorems of the
history / linked-stop layer (#30/#31), not assumed here.
Isomorphism invariance (`IsIso.stopRank_eq`, the class lift `stopRankClass`) and downward closure
(`ProlongsThroughBlock.mono`, under reduct-closure of `C`) are unconditional.

**Acceptance (#70):** `stopRank` is a function of the isomorphism class (`stopRankClass`), and
`ProlongsThroughBlock` is downward closed; this module imports no Knight module.  The Knight
façade is `Knight/Rank.lean` (`sched := blockStage`, `C := IsModel`, reduct-closure by
`IsModel.reduct`). -/

@[expose] public section

namespace VaughtConjecture

universe u v w o

namespace TypeTower.Realization

variable {Λ : Type v} [Preorder Λ] {T : TypeTower.{u} Λ} {M : Type w}
variable (C : ∀ {δ : Λ} {N : Type w}, T.Realization δ N → Prop)
variable (sched : Ordinal.{o} → Λ) (hmono : Monotone sched)

/-! ### Prolongation through a block -/

/-- `R` (at the base stage `sched 0`) **prolongs through block `ξ`**: it prolongs, within the
target class `C`, to the failed target `sched (ξ + 1)` of block `ξ` (whose terminal level is
`sched ξ`).  Defined intrinsically from `ProlongsToIn`, never from a selected history. -/
def ProlongsThroughBlock (R : T.Realization (sched 0) M) (ξ : Ordinal.{o}) : Prop :=
  R.ProlongsToIn C (hmono (zero_le : 0 ≤ ξ + 1))

variable {C sched hmono}

/-- Unfolding lemma, for an arbitrary proof of `sched 0 ≤ sched (ξ + 1)`. -/
theorem prolongsThroughBlock_iff (R : T.Realization (sched 0) M) (ξ : Ordinal.{o})
    (h : sched 0 ≤ sched (ξ + 1)) :
    ProlongsThroughBlock C sched hmono R ξ ↔ R.ProlongsToIn C h := Iff.rfl

/-- **Endpoint sanity lemma**: through block `0` means from the terminal level `sched 0` to the
failed target `sched 1`. -/
theorem prolongsThroughBlock_zero_iff (R : T.Realization (sched 0) M) :
    ProlongsThroughBlock C sched hmono R 0 ↔
      R.ProlongsToIn C (hmono (zero_le : (0 : Ordinal.{o}) ≤ 1)) := by
  have key : ∀ (ξ : Ordinal.{o}), ξ = 1 →
      (R.ProlongsToIn C (hmono (zero_le : 0 ≤ ξ)) ↔
        R.ProlongsToIn C (hmono (zero_le : (0 : Ordinal.{o}) ≤ 1))) := by
    rintro ξ rfl
    exact Iff.rfl
  exact key (0 + 1) (zero_add 1)

/-- Failure at block `0` is failure of certified prolongation from `sched 0` to `sched 1`
(Knight-VC's `FailsAtAlphaOmega` at the base stage). -/
theorem not_prolongsThroughBlock_zero_iff (R : T.Realization (sched 0) M) :
    ¬ ProlongsThroughBlock C sched hmono R 0 ↔
      R.NoProlongationToIn C (hmono (zero_le : (0 : Ordinal.{o}) ≤ 1)) :=
  not_congr (prolongsThroughBlock_zero_iff R)

/-- **Downward closure**: if `C` is closed under reduction, prolonging through block `ξ` gives
prolonging through every block `η ≤ ξ` (`ProlongsToIn.mono`). -/
theorem ProlongsThroughBlock.mono
    (hC : ∀ {δ δ' : Λ} (h : δ ≤ δ') {N : Type w} (R' : T.Realization δ' N),
      C R' → C (R'.reduct h))
    {R : T.Realization (sched 0) M} {ξ η : Ordinal.{o}} (hηξ : η ≤ ξ)
    (h : ProlongsThroughBlock C sched hmono R ξ) : ProlongsThroughBlock C sched hmono R η :=
  ProlongsToIn.mono hC (hmono (add_le_add hηξ le_rfl)) h

/-- Failure is upward closed under reduct-closure of `C`. -/
theorem not_prolongsThroughBlock_of_le
    (hC : ∀ {δ δ' : Λ} (h : δ ≤ δ') {N : Type w} (R' : T.Realization δ' N),
      C R' → C (R'.reduct h))
    {R : T.Realization (sched 0) M} {ξ η : Ordinal.{o}} (hηξ : η ≤ ξ)
    (h : ¬ ProlongsThroughBlock C sched hmono R η) : ¬ ProlongsThroughBlock C sched hmono R ξ :=
  fun h' => h (h'.mono hC hηξ)

/-! ### Isomorphism invariance -/

theorem IsIso.prolongsThroughBlock_iff {N : Type w} {R : T.Realization (sched 0) M}
    {R₂ : T.Realization (sched 0) N} {e : M ≃ N} (hi : R.IsIso R₂ e) (ξ : Ordinal.{o}) :
    ProlongsThroughBlock C sched hmono R ξ ↔ ProlongsThroughBlock C sched hmono R₂ ξ :=
  IsIso.prolongsToIn_iff hi _

theorem Iso.prolongsThroughBlock_iff {N : Type w} {R : T.Realization (sched 0) M}
    {R₂ : T.Realization (sched 0) N} (i : R.Iso R₂) (ξ : Ordinal.{o}) :
    ProlongsThroughBlock C sched hmono R ξ ↔ ProlongsThroughBlock C sched hmono R₂ ξ :=
  IsIso.prolongsThroughBlock_iff i.2 ξ

theorem prolongsThroughBlock_iff_of_iso {N : Type w} {R : T.Realization (sched 0) M}
    {R₂ : T.Realization (sched 0) N} (h : Nonempty (R.Iso R₂)) (ξ : Ordinal.{o}) :
    ProlongsThroughBlock C sched hmono R ξ ↔ ProlongsThroughBlock C sched hmono R₂ ξ :=
  h.elim fun i => i.prolongsThroughBlock_iff ξ

variable (C sched hmono) in
/-- Prolongation through block `ξ` of an **isomorphism class of base-stage realizations with
`C`-certified prolongation targets** (the lift of the certified `ProlongsToClassIn C`, not of
raw `ProlongsToClass`).  The class `C` constrains the *target*, not the source: the quotient
ranges over all base-stage realizations. -/
def ProlongsThroughBlockClass (q : Quotient (isoSetoid T (sched 0) M)) (ξ : Ordinal.{o}) :
    Prop :=
  ProlongsToClassIn C (hmono (zero_le : 0 ≤ ξ + 1)) q

@[simp]
theorem prolongsThroughBlockClass_mk (R : T.Realization (sched 0) M) (ξ : Ordinal.{o}) :
    ProlongsThroughBlockClass C sched hmono (Quotient.mk (isoSetoid T (sched 0) M) R) ξ ↔
      ProlongsThroughBlock C sched hmono R ξ := Iff.rfl

theorem ProlongsThroughBlockClass.mono
    (hC : ∀ {δ δ' : Λ} (h : δ ≤ δ') {N : Type w} (R' : T.Realization δ' N),
      C R' → C (R'.reduct h))
    {q : Quotient (isoSetoid T (sched 0) M)} {ξ η : Ordinal.{o}} (hηξ : η ≤ ξ)
    (h : ProlongsThroughBlockClass C sched hmono q ξ) :
    ProlongsThroughBlockClass C sched hmono q η := by
  induction q using Quotient.inductionOn with
  | h R =>
    rw [prolongsThroughBlockClass_mk] at h ⊢
    exact h.mono hC hηξ

/-! ### The stopping rank -/

variable (C sched hmono) in
/-- `R` **has a failure** (termination): some block is not prolonged through.  This is the
hypothesis under which `stopRank` is a genuine first failure.  It is *not* the counting
kernel's totality — that is the stronger `stopRank R < ω₁`; both are theorems of the history /
linked-stop layer (#30/#31), not assumed here. -/
def HasFailure (R : T.Realization (sched 0) M) : Prop :=
  ∃ ξ : Ordinal.{o}, ¬ ProlongsThroughBlock C sched hmono R ξ

variable (C sched hmono) in
/-- The **stopping rank** (stopping index) of `R`: the least block it does not prolong through,
`sInf {ξ | ¬ ProlongsThroughBlock C sched hmono R ξ}`.  Intrinsic (no selected history) and
isomorphism-invariant (`IsIso.stopRank_eq`, `stopRankClass`).

**Caveat.**  `sInf ∅ = 0` on ordinals, so a realization with no failure at all
(`¬ HasFailure`) gets rank `0`; only under `HasFailure` is `stopRank` the first failed block
(`stopRank_mem`, `prolongsThroughBlock_iff_lt_stopRank`).  The terminal level of a realization
of rank `ξ` is `sched ξ`; its failed target is `sched (ξ + 1)`. -/
noncomputable def stopRank (R : T.Realization (sched 0) M) : Ordinal.{o} :=
  sInf {ξ : Ordinal.{o} | ¬ ProlongsThroughBlock C sched hmono R ξ}

theorem stopRank_le_of_not {R : T.Realization (sched 0) M} {ξ : Ordinal.{o}}
    (h : ¬ ProlongsThroughBlock C sched hmono R ξ) : stopRank C sched hmono R ≤ ξ :=
  csInf_le' h

/-- Under `HasFailure`, `R` fails at its stopping rank. -/
theorem stopRank_mem {R : T.Realization (sched 0) M} (h : HasFailure C sched hmono R) :
    ¬ ProlongsThroughBlock C sched hmono R (stopRank C sched hmono R) :=
  csInf_mem h

/-- Every block strictly below the stopping rank is prolonged through.  (This needs neither
downward closure nor `HasFailure`: it is `ξ < sInf S → ξ ∉ S`; when `¬ HasFailure` it is
vacuous, since then `stopRank = 0`.) -/
theorem prolongsThroughBlock_of_lt_stopRank {R : T.Realization (sched 0) M} {ξ : Ordinal.{o}}
    (h : ξ < stopRank C sched hmono R) : ProlongsThroughBlock C sched hmono R ξ :=
  not_not.mp (notMem_of_lt_csInf' h)

/-- **First-failure characterisation** (under reduct-closure of `C` and `HasFailure`): `R`
prolongs through block `ξ` iff `ξ < stopRank`. -/
theorem prolongsThroughBlock_iff_lt_stopRank
    (hC : ∀ {δ δ' : Λ} (h : δ ≤ δ') {N : Type w} (R' : T.Realization δ' N),
      C R' → C (R'.reduct h))
    {R : T.Realization (sched 0) M} (hR : HasFailure C sched hmono R) (ξ : Ordinal.{o}) :
    ProlongsThroughBlock C sched hmono R ξ ↔ ξ < stopRank C sched hmono R := by
  refine ⟨fun h => lt_of_not_ge fun hle => stopRank_mem hR (h.mono hC hle),
    prolongsThroughBlock_of_lt_stopRank⟩

theorem not_prolongsThroughBlock_iff_stopRank_le
    (hC : ∀ {δ δ' : Λ} (h : δ ≤ δ') {N : Type w} (R' : T.Realization δ' N),
      C R' → C (R'.reduct h))
    {R : T.Realization (sched 0) M} (hR : HasFailure C sched hmono R) (ξ : Ordinal.{o}) :
    ¬ ProlongsThroughBlock C sched hmono R ξ ↔ stopRank C sched hmono R ≤ ξ := by
  rw [prolongsThroughBlock_iff_lt_stopRank hC hR, not_lt]

/-- Under `HasFailure`, rank `0` means failure at block `0` (from `sched 0` to `sched 1`). -/
theorem stopRank_eq_zero_iff {R : T.Realization (sched 0) M} (hR : HasFailure C sched hmono R) :
    stopRank C sched hmono R = 0 ↔ ¬ ProlongsThroughBlock C sched hmono R 0 :=
  ⟨fun h => h ▸ stopRank_mem hR, fun h => le_antisymm (stopRank_le_of_not h) zero_le⟩

/-- Without a failure the `sInf` is over the empty set: rank `0` by convention, not a failure. -/
theorem stopRank_eq_zero_of_not_hasFailure {R : T.Realization (sched 0) M}
    (h : ¬ HasFailure C sched hmono R) : stopRank C sched hmono R = 0 := by
  have hempty : {ξ : Ordinal.{o} | ¬ ProlongsThroughBlock C sched hmono R ξ} = ∅ :=
    Set.eq_empty_of_forall_notMem fun ξ hξ => h ⟨ξ, hξ⟩
  rw [stopRank, hempty, Ordinal.sInf_empty]

/-- A positive stopping rank is a failure. -/
theorem HasFailure.of_stopRank_pos {R : T.Realization (sched 0) M}
    (h : 0 < stopRank C sched hmono R) : HasFailure C sched hmono R :=
  by_contra fun hn => h.ne' (stopRank_eq_zero_of_not_hasFailure hn)

/-! ### Isomorphism invariance of the rank, and the class lift -/

theorem IsIso.hasFailure_iff {N : Type w} {R : T.Realization (sched 0) M}
    {R₂ : T.Realization (sched 0) N} {e : M ≃ N} (hi : R.IsIso R₂ e) :
    HasFailure C sched hmono R ↔ HasFailure C sched hmono R₂ :=
  exists_congr fun ξ => not_congr (hi.prolongsThroughBlock_iff ξ)

theorem hasFailure_iff_of_iso {N : Type w} {R : T.Realization (sched 0) M}
    {R₂ : T.Realization (sched 0) N} (h : Nonempty (R.Iso R₂)) :
    HasFailure C sched hmono R ↔ HasFailure C sched hmono R₂ :=
  h.elim fun i => IsIso.hasFailure_iff i.2

/-- **Isomorphism invariance of the stopping rank** (unconditional). -/
theorem IsIso.stopRank_eq {N : Type w} {R : T.Realization (sched 0) M}
    {R₂ : T.Realization (sched 0) N} {e : M ≃ N} (hi : R.IsIso R₂ e) :
    stopRank C sched hmono R = stopRank C sched hmono R₂ :=
  congrArg sInf (Set.ext fun ξ => not_congr (hi.prolongsThroughBlock_iff ξ))

theorem Iso.stopRank_eq {N : Type w} {R : T.Realization (sched 0) M}
    {R₂ : T.Realization (sched 0) N} (i : R.Iso R₂) :
    stopRank C sched hmono R = stopRank C sched hmono R₂ :=
  IsIso.stopRank_eq i.2

theorem stopRank_eq_of_iso {N : Type w} {R : T.Realization (sched 0) M}
    {R₂ : T.Realization (sched 0) N} (h : Nonempty (R.Iso R₂)) :
    stopRank C sched hmono R = stopRank C sched hmono R₂ :=
  h.elim fun i => i.stopRank_eq

variable (C sched hmono) in
/-- Termination (`HasFailure`) on isomorphism classes of base-stage realizations with
`C`-certified prolongation targets. -/
def HasFailureClass (q : Quotient (isoSetoid T (sched 0) M)) : Prop :=
  Quotient.lift (fun R : T.Realization (sched 0) M => HasFailure C sched hmono R)
    (fun _ _ h => propext (hasFailure_iff_of_iso h)) q

@[simp]
theorem hasFailureClass_mk (R : T.Realization (sched 0) M) :
    HasFailureClass C sched hmono (Quotient.mk (isoSetoid T (sched 0) M) R) ↔
      HasFailure C sched hmono R := Iff.rfl

variable (C sched hmono) in
/-- The **stopping rank of an isomorphism class of base-stage realizations with `C`-certified
prolongation targets** — the rank the counting kernel (`Spectrum/RankCount.lean`) consumes,
once the `stopRank < ω₁` bound (totality) and countable fibres are supplied (#30/#31/#77). -/
noncomputable def stopRankClass (q : Quotient (isoSetoid T (sched 0) M)) : Ordinal.{o} :=
  Quotient.lift (fun R : T.Realization (sched 0) M => stopRank C sched hmono R)
    (fun _ _ h => stopRank_eq_of_iso h) q

@[simp]
theorem stopRankClass_mk (R : T.Realization (sched 0) M) :
    stopRankClass C sched hmono (Quotient.mk (isoSetoid T (sched 0) M) R) =
      stopRank C sched hmono R := rfl

/-- The class rank is the first failed block of the class (under reduct-closure and
`HasFailureClass`). -/
theorem prolongsThroughBlockClass_iff_lt_stopRankClass
    (hC : ∀ {δ δ' : Λ} (h : δ ≤ δ') {N : Type w} (R' : T.Realization δ' N),
      C R' → C (R'.reduct h))
    {q : Quotient (isoSetoid T (sched 0) M)} (hq : HasFailureClass C sched hmono q)
    (ξ : Ordinal.{o}) :
    ProlongsThroughBlockClass C sched hmono q ξ ↔ ξ < stopRankClass C sched hmono q := by
  induction q using Quotient.inductionOn with
  | h R =>
    rw [hasFailureClass_mk] at hq
    rw [prolongsThroughBlockClass_mk, stopRankClass_mk]
    exact prolongsThroughBlock_iff_lt_stopRank hC hq ξ

end TypeTower.Realization

end VaughtConjecture
