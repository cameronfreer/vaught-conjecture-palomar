/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CommonChartSupply
public import VaughtConjecture.Knight.RootedPotentialIso

/-! # Root-preserving classification from selected good charts

Given a predicate `Good` on common source charts, one good seed, and the restricted one-step
supply (`RestrictedCommonChartStepSupply Good`), a tuple pair is *selected* when it is read from
one good containing chart along an arbitrary coordinate selection:

  `(a, b)` is selected iff `a = c.tuple₁ ∘ σ` and `b = c.tuple₂ ∘ σ` for a good chart `c`.

* `selectedChartFamily` — the selected pairs; a selection may repeat or omit coordinates, and
  its image need not be a visible face;
* `selectedChartFamily_empty_mem` / `selectedChartFamily_commonChart` — the empty selection from
  any good chart, and the containing chart as the common-chart certificate of every member;
* `selectedChartFamily_forth` / `selectedChartFamily_back` — one restricted supply step at the
  good containing chart `c` gives a good chart `c'`, an embedding `e`, and a coordinate `j` of
  the requested point; the enlarged pair is selected by `snoc (e ∘ σ) j`;
* `exists_iso_of_selectedCommonCharts` — the family is a potential isomorphism containing the
  seed (identity selection), so the rooted consumer (`exists_iso_of_commonCharts_mem`) gives an
  isomorphism carrying the seed's first tuple onto its second coordinatewise.
* `restrictedCommonChartStepSupply_true` — unrestricted supply is the case where every chart is
  good.

`Good` need not be closed under subtuples or faces: the good *containing* chart is kept as the
witness. No fair chain of charts is scheduled before the countable back-and-forth, so countability
is used only once, at the standard isomorphism extraction, and no `Nonempty` carrier hypothesis
is needed. This module imports neither `Knight/CommonChartChain.lean` nor
`Knight/RootedKarp.lean`; the latter keeps the historical chain adapters and the compatibility
signatures. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

namespace KnightRealization

variable {M₁ M₂ : Type w}
variable {α : LimitStage}
variable {A₁ : KnightRealization α M₁} {A₂ : KnightRealization α M₂}

/-- The tuple pairs read from one good containing chart along a coordinate selection. The
selection may repeat or omit coordinates, and its image need not be a visible face. -/
def selectedChartFamily (Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop) :
    Set (Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) :=
  {x | ∃ nd, Good nd ∧ ∃ σ : Fin x.1 → Fin nd.arity,
    nd.tuple₁ ∘ σ = x.2.1 ∧ nd.tuple₂ ∘ σ = x.2.2}

/-- A good chart's own tuple pair is selected, by the identity selection. -/
theorem node_mem_selectedChartFamily {Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop}
    {nd : CommonChartNode (A₁ := A₁) (A₂ := A₂)} (hnd : Good nd) :
    (⟨nd.arity, ⇑nd.tuple₁, ⇑nd.tuple₂⟩ : Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈
      selectedChartFamily Good :=
  ⟨nd, hnd, id, rfl, rfl⟩

/-- The empty pair is selected from any good chart, by the empty selection. -/
theorem selectedChartFamily_empty_mem
    {Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop}
    {nd : CommonChartNode (A₁ := A₁) (A₂ := A₂)} (hnd : Good nd) :
    (⟨0, Fin.elim0, Fin.elim0⟩ : Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈
      selectedChartFamily Good :=
  ⟨nd, hnd, Fin.elim0, funext fun i => i.elim0, funext fun i => i.elim0⟩

/-- Every selected pair is certified by the common chart containing it. -/
theorem selectedChartFamily_commonChart
    (Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop) :
    ∀ x ∈ selectedChartFamily Good, HasCommonChart A₁ A₂ x.2.1 x.2.2 := by
  rintro x ⟨nd, -, σ, hσ₁, hσ₂⟩
  exact ⟨nd.arity, nd.tuple₁, nd.tuple₂, σ, nd.type, nd.eval₁, nd.eval₂, hσ₁, hσ₂⟩

/-- One good extension of a containing chart selects the pair enlarged by any coordinate of the
next chart: the old selection is pushed forward along the extension embedding. -/
theorem snoc_mem_selectedChartFamily {Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop}
    {x : Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)} {nd : CommonChartNode (A₁ := A₁) (A₂ := A₂)}
    {z : M₁ ⊕ M₂} (d : GoodCommonChartExtension Good nd z) {σ : Fin x.1 → Fin nd.arity}
    (hσ₁ : nd.tuple₁ ∘ σ = x.2.1) (hσ₂ : nd.tuple₂ ∘ σ = x.2.2)
    (j : Fin d.extension.next.arity) :
    (⟨x.1 + 1, Fin.snoc x.2.1 (d.extension.next.tuple₁ j),
      Fin.snoc x.2.2 (d.extension.next.tuple₂ j)⟩ :
        Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈ selectedChartFamily Good := by
  refine ⟨d.extension.next, d.good_next, Fin.snoc (d.extension.emb ∘ σ) j, ?_, ?_⟩
  · rw [Fin.comp_snoc, ← hσ₁, ← d.extension.trans₁]
    rfl
  · rw [Fin.comp_snoc, ← hσ₂, ← d.extension.trans₂]
    rfl

/-- Forth: the restricted supply at the good containing chart absorbs the requested point. -/
theorem selectedChartFamily_forth {Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop}
    (supply : RestrictedCommonChartStepSupply (A₁ := A₁) (A₂ := A₂) Good) :
    ∀ x ∈ selectedChartFamily Good, ∀ m : M₁, ∃ n' : M₂,
      (⟨x.1 + 1, Fin.snoc x.2.1 m, Fin.snoc x.2.2 n'⟩ :
        Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈ selectedChartFamily Good := by
  rintro x ⟨nd, hnd, σ, hσ₁, hσ₂⟩ m
  obtain ⟨d⟩ := supply nd hnd (Sum.inl m)
  obtain ⟨j, hj⟩ := d.extension.serves_left m rfl
  rw [← hj]
  exact ⟨_, snoc_mem_selectedChartFamily d hσ₁ hσ₂ j⟩

/-- Back: the restricted supply at the good containing chart absorbs the requested point. -/
theorem selectedChartFamily_back {Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop}
    (supply : RestrictedCommonChartStepSupply (A₁ := A₁) (A₂ := A₂) Good) :
    ∀ x ∈ selectedChartFamily Good, ∀ n' : M₂, ∃ m : M₁,
      (⟨x.1 + 1, Fin.snoc x.2.1 m, Fin.snoc x.2.2 n'⟩ :
        Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈ selectedChartFamily Good := by
  rintro x ⟨nd, hnd, σ, hσ₁, hσ₂⟩ n'
  obtain ⟨d⟩ := supply nd hnd (Sum.inr n')
  obtain ⟨j, hj⟩ := d.extension.serves_right n' rfl
  rw [← hj]
  exact ⟨_, snoc_mem_selectedChartFamily d hσ₁ hσ₂ j⟩

/-- Unrestricted one-step supply is restricted supply for the predicate selecting every chart. -/
theorem restrictedCommonChartStepSupply_true
    (supply : CommonChartStepSupply (A₁ := A₁) (A₂ := A₂)) :
    RestrictedCommonChartStepSupply (A₁ := A₁) (A₂ := A₂) fun _ => True :=
  fun nd _ z => (supply nd z).map fun d => ⟨d, trivial⟩

/-- **The direct root-preserving consumer.** On countable carriers, one good seed and the
restricted one-step supply give an isomorphism extending the seed's tuple correspondence
literally. The selected family is already a potential isomorphism, so no fair chain of charts
is built; `Good` need not be closed under restrictions, and the carriers may be empty. -/
theorem exists_iso_of_selectedCommonCharts [Countable M₁] [Countable M₂]
    (hA₁ : A₁.IsExactParentConsistent) (hA₂ : A₂.IsExactParentConsistent)
    (Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop)
    (seed : CommonChartNode (A₁ := A₁) (A₂ := A₂))
    (seed_good : Good seed)
    (supply : RestrictedCommonChartStepSupply (A₁ := A₁) (A₂ := A₂) Good) :
    ∃ e : A₁.Iso A₂, ∀ i, e.1 (seed.tuple₁ i) = seed.tuple₂ i :=
  exists_iso_of_commonCharts_mem hA₁ hA₂ (selectedChartFamily Good)
    (selectedChartFamily_empty_mem seed_good) (selectedChartFamily_commonChart Good)
    (selectedChartFamily_forth supply) (selectedChartFamily_back supply)
    (node_mem_selectedChartFamily seed_good)

end KnightRealization

end VaughtConjecture.Knight
