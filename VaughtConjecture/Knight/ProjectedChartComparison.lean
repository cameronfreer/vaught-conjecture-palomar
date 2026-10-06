/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.ModelTheory.ProjectedExtension
public import VaughtConjecture.Knight.OrdinaryFiniteCutReceiving
public import VaughtConjecture.Knight.ChartLanguage
public import VaughtConjecture.Knight.FiniteCoverCoordinates
public import VaughtConjecture.Knight.OneSidedTransfer
public import VaughtConjecture.Knight.StructuralChartComparison

/-! # A receiving-produced client of generic projected extension comparison

Receipts are actual block expansions of fixed base structures with common finite charts.
The extension producer returns a lower chart, not a BF hypothesis. The generic theorem
provides the only ordinal induction. Existing comparison declarations are unchanged.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower FirstOrder Language Structure KnightRealization StageType
open VaughtConjecture.ModelTheory

universe w

/-- The base chart language, before the sentence/spectrum entry points. `blockStage_zero`
identifies this stage with `ω`. -/
noncomputable abbrev projectedBaseLang := stageLang (blockStage 0)

theorem lowerChart {α β : LimitStage} (h : β ≤ α) {M N : Type w}
    {W : KnightRealization α M} {W' : KnightRealization α N} {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (hc : HasCommonChart W W' a b) :
    HasCommonChart (W.reduct h) (W'.reduct h) a b := by
  obtain ⟨k, ta, tb, σ, p, hta, htb, ha, hb⟩ := hc
  refine ⟨k, ta, tb, σ, reduceType β.2 h p, ?_, ?_, ha, hb⟩
  · rw [Realization.reduct_eval, hta]; rfl
  · rw [Realization.reduct_eval, htb]; rfl

theorem reverseChart {α : LimitStage} {M N : Type w}
    {W : KnightRealization α M} {W' : KnightRealization α N} {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (hc : HasCommonChart W W' a b) :
    HasCommonChart W' W b a := by
  obtain ⟨k, ta, tb, σ, p, hta, htb, ha, hb⟩ := hc
  exact ⟨k, tb, ta, σ, p, htb, hta, hb, ha⟩

/-- One requested element is covered and received, retaining the root literally and matching
only the lower chart. This extracts the finite-cover step from `forth_uniform` without its
BF induction hypothesis or conclusion. Repeated points reuse the existing selector. -/
theorem extend_commonChart_projected (α : Ordinal.{0}) {M N : Type w}
    (W : KnightRealization (blockStage (α + 1)) M)
    (W' : KnightRealization (blockStage (α + 1)) N) (hW : W.IsModel) (hW' : W'.IsModel)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} (hc : HasCommonChart W W' a b) (x : M) :
    ∃ y : N, HasCommonChart (W.reduct (blockStage_le_succ α))
      (W'.reduct (blockStage_le_succ α)) (Fin.snoc a x) (Fin.snoc b y) :=
  StructuralChartComparison.extend_commonChart α W W' hW.consistent hW.isCovering
    hW'.consistent (OrdinaryModelReceiving.finiteCutReceiving hW') hc x

/-- Model expansions at the requested block, reducing to specified fixed base structures.
Existence of this data, including the chart, is required for an initial match. -/
structure ProjectedChartReceipt (M N : Type w)
    (baseM : projectedBaseLang.Structure M) (baseN : projectedBaseLang.Structure N)
    (α : Ordinal.{0}) (n : ℕ) (a : Fin n → M) (b : Fin n → N) where
  source : KnightRealization (blockStage α) M
  target : KnightRealization (blockStage α) N
  source_model : source.IsModel
  target_model : target.IsModel
  source_base : stageStructureOf (source.reduct (blockStage_zero_le α)) = baseM
  target_base : stageStructureOf (target.reduct (blockStage_zero_le α)) = baseN
  chart : HasCommonChart source target a b

namespace ProjectedChartReceipt

variable {M N : Type w}
variable {baseM : projectedBaseLang.Structure M} {baseN : projectedBaseLang.Structure N}

/-- Lower the expansion and chart without changing either base structure or tuple. -/
noncomputable def lower {α β : Ordinal.{0}} (h : β ≤ α)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (r : ProjectedChartReceipt M N baseM baseN α n a b) :
    ProjectedChartReceipt M N baseM baseN β n a b where
  source := r.source.reduct (blockStage_mono h)
  target := r.target.reduct (blockStage_mono h)
  source_model := r.source_model.reduct _
  target_model := r.target_model.reduct _
  source_base := by rw [Realization.reduct_reduct]; exact r.source_base
  target_base := by rw [Realization.reduct_reduct]; exact r.target_base
  chart := lowerChart _ r.chart

/-- Every receipt reads back the full atomic base-language diagram. -/
theorem atomic {α : Ordinal.{0}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (r : ProjectedChartReceipt M N baseM baseN α n a b) :
    @SameAtomicType projectedBaseLang M baseM n N baseN a b := by
  have h := sameAtomicType_of_commonChart
    (r.source_model.consistent_reduct (blockStage_zero_le α))
    (r.target_model.consistent_reduct (blockStage_zero_le α))
    (lowerChart (blockStage_zero_le α) r.chart)
  rw [r.source_base, r.target_base] at h
  exact h

/-- Receive a requested source element and package the lower expansions as a new receipt. -/
theorem forth {α : Ordinal.{0}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (r : ProjectedChartReceipt M N baseM baseN (α + 1) n a b) (x : M) :
    ∃ y : N, Nonempty (ProjectedChartReceipt M N baseM baseN α (n + 1)
      (Fin.snoc a x) (Fin.snoc b y)) := by
  obtain ⟨y, hc⟩ := extend_commonChart_projected α r.source r.target
    r.source_model r.target_model r.chart x
  refine ⟨y, ⟨{
    source := r.source.reduct (blockStage_le_succ α)
    target := r.target.reduct (blockStage_le_succ α)
    source_model := r.source_model.reduct _
    target_model := r.target_model.reduct _
    source_base := ?_
    target_base := ?_
    chart := hc }⟩⟩
  · rw [Realization.reduct_reduct]; exact r.source_base
  · rw [Realization.reduct_reduct]; exact r.target_base

/-- Reverse the two expansions, retaining their exact realization data. -/
def symm {α : Ordinal.{0}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (r : ProjectedChartReceipt M N baseM baseN α n a b) :
    ProjectedChartReceipt N M baseN baseM α n b a where
  source := r.target
  target := r.source
  source_model := r.target_model
  target_model := r.source_model
  source_base := r.target_base
  target_base := r.source_base
  chart := reverseChart r.chart

end ProjectedChartReceipt

/-- The generic ranked family on fixed base structures, supplied by actual receiving.
The receipt type allows different block expansions at different indices. -/
noncomputable def projectedChartFamily {M N : Type w} [baseM : projectedBaseLang.Structure M]
    [baseN : projectedBaseLang.Structure N] (height : Ordinal.{0}) :
    RankedMatchingFamily projectedBaseLang M N height where
  Receipt := ProjectedChartReceipt M N baseM baseN
  atomic := ProjectedChartReceipt.atomic
  lower := fun h _ r => ⟨r.lower h⟩
  forth := fun _ r x => r.forth x
  back := by
    intro α n a b _ r y
    obtain ⟨x, ⟨r'⟩⟩ := r.symm.forth y
    exact ⟨x, ⟨r'.symm⟩⟩

/-- An explicitly supplied expansion/chart receipt gives BF equivalence of fixed bases. -/
theorem bfEquiv_of_projectedChartReceipt {M N : Type w}
    [baseM : projectedBaseLang.Structure M] [baseN : projectedBaseLang.Structure N]
    {α : Ordinal.{0}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (r : ProjectedChartReceipt M N baseM baseN α n a b) :
    BFEquiv (L := projectedBaseLang) α n a b :=
  (projectedChartFamily α).bfEquiv le_rfl r

/-- Additive alternative to uniform comparison: finite-cover receiving supplies receipts
to the generic projected-extension kernel. No old BF comparison theorem is invoked. -/
theorem bfEquiv_of_commonChart_projected (α : Ordinal.{0}) {M N : Type w}
    (W : KnightRealization (blockStage α) M) (W' : KnightRealization (blockStage α) N)
    (hW : W.IsModel) (hW' : W'.IsModel) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hc : HasCommonChart W W' a b) :
    @BFEquiv projectedBaseLang M (stageStructureOf (W.reduct (blockStage_zero_le α)))
      N (stageStructureOf (W'.reduct (blockStage_zero_le α))) α n a b := by
  let : projectedBaseLang.Structure M := stageStructureOf (W.reduct (blockStage_zero_le α))
  let : projectedBaseLang.Structure N := stageStructureOf (W'.reduct (blockStage_zero_le α))
  exact bfEquiv_of_projectedChartReceipt {
    source := W
    target := W'
    source_model := hW
    target_model := hW'
    source_base := rfl
    target_base := rfl
    chart := hc }

end VaughtConjecture.Knight
