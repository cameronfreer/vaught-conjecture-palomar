/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RootedPotentialIso
public import VaughtConjecture.Knight.SelectedCommonCharts
public import VaughtConjecture.Knight.CommonChartChain

/-! # Root-preserving classification: chain adapters and compatibility signatures

This module is the historical import path for root-preserving classification. It re-exports

* `Knight/RootedPotentialIso.lean` — `rootedPotentialIso`, `exists_equiv_of_mem`,
  `exists_iso_of_potentialIso_mem`, `exists_iso_of_commonCharts_mem`: a potential isomorphism
  yields, on countable carriers, an isomorphism extending any member pair literally;
* `Knight/SelectedCommonCharts.lean` — the direct consumer
  `exists_iso_of_selectedCommonCharts`: one good seed and restricted one-step supply already
  give the root-preserving isomorphism, with no fair chart chain and no `Nonempty` carriers;
* `Knight/CommonChartChain.lean` — the historical fair-chain vocabulary.

It keeps the chain adapter `exists_iso_of_fairCommonChartChain`, for applications that have an
actual chain, and the compatibility signatures `exists_iso_of_commonChartStepSupply` and
`exists_iso_of_restrictedCommonChartStepSupply`, which are now proved by the direct consumer and
build no chain. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

namespace KnightRealization

variable {M₁ M₂ : Type w} {α : LimitStage}
variable {A₁ : KnightRealization α M₁} {A₂ : KnightRealization α M₂}

/-- Root-preserving classification cashout: the isomorphism from an exhaustive chain extends
every node's tuple correspondence literally. -/
theorem exists_iso_of_fairCommonChartChain [Countable M₁] [Countable M₂]
    (hA₁ : A₁.IsExactParentConsistent) (hA₂ : A₂.IsExactParentConsistent)
    (c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂)) (k : ℕ) :
    ∃ e : A₁.Iso A₂, ∀ i, e.1 ((c.node k).tuple₁ i) = (c.node k).tuple₂ i :=
  exists_iso_of_commonCharts_mem hA₁ hA₂ c.family c.family_empty_mem c.family_commonChart
    c.family_forth c.family_back (c.node_mem_family k)

/-- Root-preserving one-step-density cashout: the isomorphism extends the seed chart. This is
the direct consumer with every chart good; the `Nonempty` instances are no longer used. -/
theorem exists_iso_of_commonChartStepSupply
    [Countable M₁] [Countable M₂] [Nonempty M₁] [Nonempty M₂]
    (hA₁ : A₁.IsExactParentConsistent) (hA₂ : A₂.IsExactParentConsistent)
    (seed : CommonChartNode (A₁ := A₁) (A₂ := A₂))
    (supply : CommonChartStepSupply (A₁ := A₁) (A₂ := A₂)) :
    ∃ e : A₁.Iso A₂, ∀ i, e.1 (seed.tuple₁ i) = seed.tuple₂ i :=
  exists_iso_of_selectedCommonCharts hA₁ hA₂ (fun _ => True) seed trivial
    (restrictedCommonChartStepSupply_true supply)

/-- Root-preserving restricted cashout: the isomorphism extends the good seed chart. Kept as the
compatibility signature of `exists_iso_of_selectedCommonCharts`; the `Nonempty` instances are no
longer used. -/
theorem exists_iso_of_restrictedCommonChartStepSupply
    [Countable M₁] [Countable M₂] [Nonempty M₁] [Nonempty M₂]
    (hA₁ : A₁.IsExactParentConsistent) (hA₂ : A₂.IsExactParentConsistent)
    (Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop)
    (seed : CommonChartNode (A₁ := A₁) (A₂ := A₂))
    (seed_good : Good seed)
    (supply : RestrictedCommonChartStepSupply (A₁ := A₁) (A₂ := A₂) Good) :
    ∃ e : A₁.Iso A₂, ∀ i, e.1 (seed.tuple₁ i) = seed.tuple₂ i :=
  exists_iso_of_selectedCommonCharts hA₁ hA₂ Good seed seed_good supply

end KnightRealization

end VaughtConjecture.Knight
