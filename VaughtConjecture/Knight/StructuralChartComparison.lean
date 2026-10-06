/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.ModelTheory.ProjectedExtension
public import VaughtConjecture.Knight.CapReceivingReduction
public import VaughtConjecture.Knight.ChartLanguage
public import VaughtConjecture.Knight.OneSidedTransfer

/-! # Structural chart comparison without modelhood

Exactly parent-consistent, covering, finite-cut receiving realizations supply actual
chart receipts at each block. Lowering uses the structural reduct laws and the existing
capped receiving reduction, not a modelhood theorem or inverse donor lifting. The one-sided
step needs covering only on the source and receiving only on the target. Both sides supply
these hypotheses for BF comparison.

Tuples are arbitrary coordinate selections from injective actual containers. Repeated
coordinates and empty roots are retained. Fixed block-zero structures are part of the
receipt, and an initial common chart is explicit. `RankedMatchingFamily` supplies the only
ordinal induction; this module constructs receipts and finite extension steps only.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.StructuralChartComparison

open TypeTower FirstOrder Language KnightRealization
open VaughtConjecture.ModelTheory

universe w w'

/-- The fixed block-zero chart language, identified with the ω-stage by `blockStage_zero`. -/
noncomputable abbrev baseLang := stageLang (blockStage 0)

theorem lowerChart {α β : LimitStage} (h : β ≤ α) {M : Type w} {N : Type w'}
    {W : KnightRealization α M} {W' : KnightRealization α N} {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (hc : HasCommonChart W W' a b) :
    HasCommonChart (W.reduct h) (W'.reduct h) a b := by
  obtain ⟨k, ta, tb, σ, p, hta, htb, ha, hb⟩ := hc
  refine ⟨k, ta, tb, σ, reduceType β.2 h p, ?_, ?_, ha, hb⟩
  · rw [Realization.reduct_eval, hta]; rfl
  · rw [Realization.reduct_eval, htb]; rfl

theorem reverseChart {α : LimitStage} {M : Type w} {N : Type w'}
    {W : KnightRealization α M} {W' : KnightRealization α N} {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (hc : HasCommonChart W W' a b) :
    HasCommonChart W' W b a := by
  obtain ⟨k, ta, tb, σ, p, hta, htb, ha, hb⟩ := hc
  exact ⟨k, tb, ta, σ, p, htb, hta, hb, ha⟩

/-- One structural forth step. Source consistency and generic covering produce a lawful
donor over the literal root; target consistency and receiving transfer it with one strict
block drop. No receiving on the source or covering on the target is needed. -/
theorem extend_commonChart (α : Ordinal.{0}) {M : Type w} {N : Type w'}
    (W : KnightRealization (blockStage (α + 1)) M)
    (W' : KnightRealization (blockStage (α + 1)) N)
    (hc : W.IsExactParentConsistent) (hcover : W.IsCovering)
    (hc' : W'.IsExactParentConsistent) (hr' : FiniteCutReceiving W')
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} (seed : HasCommonChart W W' a b) (x : M) :
    ∃ y : N, HasCommonChart (W.reduct (blockStage_le_succ α))
      (W'.reduct (blockStage_le_succ α)) (Fin.snoc a x) (Fin.snoc b y) := by
  obtain ⟨k, ta, tb, σ, p, hta, htb, ha, hb⟩ := seed
  by_cases hmem : x ∈ Set.range ta
  · obtain ⟨j, hj⟩ := hmem
    refine ⟨tb j, lowerChart (blockStage_le_succ α) ?_⟩
    refine ⟨k, ta, tb, Fin.snoc σ j, p, hta, htb, ?_, ?_⟩
    · rw [Fin.comp_snoc, ha, hj]
    · rw [Fin.comp_snoc, hb]
  · obtain ⟨l, s, f, hfs, hsome⟩ := hcover (snoc ta x hmem)
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hsome
    let g : Fin k ↪ Fin l := Fin.castSuccEmb.trans f
    have hseg : g.trans s = ta := by
      change (Fin.castSuccEmb.trans f).trans s = ta
      rw [Function.Embedding.trans_assoc, hfs, castSuccEmb_trans_snoc]
    have hface : typeMap g P = some p := by
      have he := hc s P g hP
      rw [hseg, hta] at he
      exact he.symm
    obtain ⟨ub, Q, hroot, hub, hred⟩ :=
      receive_donor_uniform α hc' hr' P g tb p hface htb
    have hx : s (f (Fin.last k)) = x := by
      have he := congrArg (fun t : Fin (k + 1) ↪ M => t (Fin.last k)) hfs
      simpa only [Function.Embedding.trans_apply, snoc_apply_last] using he
    have hsource : (s : Fin l → M) ∘ (fun i => g (σ i)) = a := by
      funext i
      have hi := congrArg (fun t : Fin k ↪ M => t (σ i)) hseg
      exact hi.trans (congrFun ha i)
    have htarget : (ub : Fin l → N) ∘ (fun i => g (σ i)) = b := by
      funext i
      have hi := congrArg (fun t : Fin k ↪ N => t (σ i)) hroot
      exact hi.trans (congrFun hb i)
    refine ⟨ub (f (Fin.last k)), ?_⟩
    refine ⟨l, s, ub, Fin.snoc (fun i => g (σ i)) (f (Fin.last k)),
      reduceType (blockStage α).2 (blockStage_le_succ α) P, ?_, ?_, ?_, ?_⟩
    · rw [Realization.reduct_eval, hP]; rfl
    · rw [Realization.reduct_eval, hub, ← hred]; rfl
    · rw [Fin.comp_snoc, hsource, hx]
    · rw [Fin.comp_snoc, htarget]

/-- Structural expansions with fixed bases and an actual common chart. Consistency,
covering and receiving are supplied directly; the carrier universes are independent. -/
structure Receipt (M : Type w) (N : Type w')
    (baseM : baseLang.Structure M) (baseN : baseLang.Structure N)
    (α : Ordinal.{0}) (n : ℕ) (a : Fin n → M) (b : Fin n → N) where
  source : KnightRealization (blockStage α) M
  target : KnightRealization (blockStage α) N
  source_consistent : source.IsExactParentConsistent
  target_consistent : target.IsExactParentConsistent
  source_covering : source.IsCovering
  target_covering : target.IsCovering
  source_receiving : FiniteCutReceiving source
  target_receiving : FiniteCutReceiving target
  source_base : stageStructureOf (source.reduct (blockStage_zero_le α)) = baseM
  target_base : stageStructureOf (target.reduct (blockStage_zero_le α)) = baseN
  chart : HasCommonChart source target a b

namespace Receipt

variable {M : Type w} {N : Type w'}
variable {baseM : baseLang.Structure M} {baseN : baseLang.Structure N}

/-- Lower every structural input with its existing reduct law, keeping the bases and tuples.
The receiving law is capped repair, not exact lifting of arbitrary lower donors. -/
noncomputable def lower {α β : Ordinal.{0}} (h : β ≤ α)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (r : Receipt M N baseM baseN α n a b) : Receipt M N baseM baseN β n a b where
  source := r.source.reduct (blockStage_mono h)
  target := r.target.reduct (blockStage_mono h)
  source_consistent := r.source_consistent.reduct _
  target_consistent := r.target_consistent.reduct _
  source_covering := r.source_covering.reduct _
  target_covering := r.target_covering.reduct _
  source_receiving := FiniteCutReceiving.reduct r.source_receiving _
  target_receiving := FiniteCutReceiving.reduct r.target_receiving _
  source_base := by rw [Realization.reduct_reduct]; exact r.source_base
  target_base := by rw [Realization.reduct_reduct]; exact r.target_base
  chart := lowerChart _ r.chart

/-- Read back the complete atomic base diagram at the actual tuples, including repetitions. -/
theorem atomic {α : Ordinal.{0}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (r : Receipt M N baseM baseN α n a b) :
    @SameAtomicType baseLang M baseM n N baseN a b := by
  have he := sameAtomicType_of_commonChart
    (r.source_consistent.reduct (blockStage_zero_le α))
    (r.target_consistent.reduct (blockStage_zero_le α))
    (lowerChart (blockStage_zero_le α) r.chart)
  rw [r.source_base, r.target_base] at he
  exact he

/-- Receive one requested source point and retain a structural receipt one block lower. -/
theorem forth {α : Ordinal.{0}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (r : Receipt M N baseM baseN (α + 1) n a b) (x : M) :
    ∃ y : N, Nonempty (Receipt M N baseM baseN α (n + 1)
      (Fin.snoc a x) (Fin.snoc b y)) := by
  obtain ⟨y, he⟩ := extend_commonChart α r.source r.target
    r.source_consistent r.source_covering r.target_consistent r.target_receiving r.chart x
  let low := r.lower (show α ≤ α + 1 from le_self_add)
  exact ⟨y, ⟨{
    source := low.source
    target := low.target
    source_consistent := low.source_consistent
    target_consistent := low.target_consistent
    source_covering := low.source_covering
    target_covering := low.target_covering
    source_receiving := low.source_receiving
    target_receiving := low.target_receiving
    source_base := low.source_base
    target_base := low.target_base
    chart := he }⟩⟩

/-- Exchange sides for the back step. This does not assume the matching relation is symmetric. -/
def symm {α : Ordinal.{0}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (r : Receipt M N baseM baseN α n a b) : Receipt N M baseN baseM α n b a where
  source := r.target
  target := r.source
  source_consistent := r.target_consistent
  target_consistent := r.source_consistent
  source_covering := r.target_covering
  target_covering := r.source_covering
  source_receiving := r.target_receiving
  target_receiving := r.source_receiving
  source_base := r.target_base
  target_base := r.source_base
  chart := reverseChart r.chart

end Receipt

/-- Structural receipts form the existing graded family. The library, not this adapter,
owns the ordinal induction; an actual seed is still required for every comparison. -/
noncomputable def rankedFamily {M : Type w} {N : Type w'} [baseM : baseLang.Structure M]
    [baseN : baseLang.Structure N] (height : Ordinal.{0}) :
    RankedMatchingFamily baseLang M N height where
  Receipt := Receipt M N baseM baseN
  atomic := Receipt.atomic
  lower := fun h _ r => ⟨r.lower h⟩
  forth := fun _ r x => r.forth x
  back := by
    intro α n a b _ r y
    obtain ⟨x, ⟨r'⟩⟩ := r.symm.forth y
    exact ⟨x, ⟨r'.symm⟩⟩

/-- An explicit structural expansion/chart receipt gives bounded BF of the fixed bases. -/
theorem bfEquiv_of_receipt {M : Type w} {N : Type w'}
    [baseM : baseLang.Structure M] [baseN : baseLang.Structure N]
    {α : Ordinal.{0}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (r : Receipt M N baseM baseN α n a b) : BFEquiv (L := baseLang) α n a b :=
  (rankedFamily α).bfEquiv le_rfl r

/-- Exactly parent-consistent, covering, receiving realizations with an initial common
chart compare through their block index. No modelhood, countability or nonempty instance
is assumed, and the carriers may live in different universes. -/
theorem bfEquiv_of_commonChart (α : Ordinal.{0}) {M : Type w} {N : Type w'}
    (W : KnightRealization (blockStage α) M) (W' : KnightRealization (blockStage α) N)
    (hc : W.IsExactParentConsistent) (hcover : W.IsCovering) (hr : FiniteCutReceiving W)
    (hc' : W'.IsExactParentConsistent) (hcover' : W'.IsCovering) (hr' : FiniteCutReceiving W')
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} (seed : HasCommonChart W W' a b) :
    @BFEquiv baseLang M (stageStructureOf (W.reduct (blockStage_zero_le α)))
      N (stageStructureOf (W'.reduct (blockStage_zero_le α))) α n a b := by
  let : baseLang.Structure M := stageStructureOf (W.reduct (blockStage_zero_le α))
  let : baseLang.Structure N := stageStructureOf (W'.reduct (blockStage_zero_le α))
  exact bfEquiv_of_receipt {
    source := W
    target := W'
    source_consistent := hc
    target_consistent := hc'
    source_covering := hcover
    target_covering := hcover'
    source_receiving := hr
    target_receiving := hr'
    source_base := rfl
    target_base := rfl
    chart := seed }

end VaughtConjecture.Knight.StructuralChartComparison
