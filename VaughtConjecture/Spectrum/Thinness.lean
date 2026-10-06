/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.RankedThinness
public import InfinitaryLogic.Descriptive.StructureIsoSetoid
public import InfinitaryLogic.Descriptive.Polish
public import InfinitaryLogic.Descriptive.PerfectSetDichotomy
public import VaughtConjecture.Spectrum.Sentence

/-! # Thinness and the perfect-set form of Vaught's conjecture

`Spectrum.Sentence` handles the *cardinal* form, which `I(φ,ℵ₀) = ℵ₁` refutes only under
`¬CH`.  The CH-independent formulation is the *perfect-set* form: either countably many
countable models, or a perfect set of pairwise non-isomorphic countable models.

* `VaughtConjecturePerfectSetFor φ` (`ℕ`-tier, the conventional form): `I(φ,ℵ₀) ≤ ℵ₀` or a
  perfect set of pairwise non-isomorphic `ℕ`-models
  (`InfinitaryLogic`'s `Sentenceω.HasPerfectSetOfPairwiseNonisomorphicNatModels`).
* `AllCountableVaughtConjecturePerfectSetFor φ` (all carrier tiers): the perfect set may also
  live in a finite tier `Fin n` — a sentence with no infinite models can still have continuum
  many pairwise non-isomorphic one-element models — so refuting this variant from `ℕ`-tier
  thinness needs the explicit hypothesis `HasNoFiniteModels`.

`InfinitaryLogic.Descriptive.RankedThinness` supplies the standard route to `ℕ`-tier thinness
from a countable-ordinal rank (`ThinRankAnalysis`).  The adapter `thinRankAnalysisOfClassRank`
builds it from a rank on *isomorphism classes* of `ℕ`-models with (i) values `< ω₁` and
(ii) countable fibres — the same two inputs as the cardinal count — leaving exactly one new
obligation: (iii) the rank is **bounded on continuous Cantor isomorphism-antichains** (images of
Cantor space, hence compact, consisting of pairwise non-isomorphic models).  Note that (iii) is
antichain-relative: a rank bounded on *every* analytic subset of `ModelsOf φ` would be bounded
on `ModelsOf φ` itself, contradicting cofinal ranks.  For Knight's sentence the rank is the
stopping rank; (iii) is the open content (issue #1).

`not_vaughtConjecturePerfectSetFor_of_classRank` is the single-rank headline shape: one rank on
the isomorphism classes of `ℕ`-models with totality, countable fibres, cofinal range and
antichain-boundedness refutes the perfect-set form with no CH; the all-countable variant adds
`HasNoFiniteModels`.

**Terminology.**  "Thin" here is descriptive-set-theoretic: an equivalence relation is *thin*
when there is no perfect set of pairwise inequivalent elements — here, no perfect set of
pairwise non-isomorphic countable models.  For an `L_{ω₁ω}`-sentence this is
the usual *scatteredness* condition (on the `ℕ`-model tier; the all-countable formulation
additionally requires control of the finite tiers — the no-finite-model bridge above); the
identification of thinness with scatteredness in this form is as in Harrison-Trainor,
Theorem 6.3.  It is **unrelated** to the Knight–Millar notion of a computable *thin tree*,
where ordinal node ranks are bounded separately at each finite tree level: the shared word is
accidental, and no implication is intended in either direction.  Likewise, per-model effective
bounds such as `ρ(M) < ω₁^M` are potentially useful refinements but do not by themselves uniformly
bound `ρ` on a continuous Cantor antichain — the uniform antichain bound is the input
`ThinRankAnalysis` actually consumes. -/

@[expose] public section

namespace VaughtConjecture.Spectrum

open FirstOrder Language Cardinal

universe u v

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- The perfect-set form of Vaught's conjecture for `φ` (`ℕ`-tier): countably many countable
models, or a perfect set of pairwise non-isomorphic `ℕ`-models. -/
def VaughtConjecturePerfectSetFor (φ : L.Sentenceω) : Prop :=
  natModelSpectrum φ ≤ ℵ₀ ∨ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels

/-- The all-countable variant of the perfect-set form: countably many countable models over all
tiers, or a perfect set of pairwise non-isomorphic models in some carrier tier (`ℕ` or
`Fin n`, the latter via `InfinitaryLogic`'s
`Sentenceω.HasPerfectSetOfPairwiseNonisomorphicFinModels`). -/
def AllCountableVaughtConjecturePerfectSetFor (φ : L.Sentenceω) : Prop :=
  allCountableSpectrum φ ≤ ℵ₀ ∨ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels ∨
    ∃ n : ℕ, φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n

/-- **Adapter.**  A rank on the isomorphism classes of `ℕ`-models of `φ` with values below
`ω₁`, countable fibres below `ω₁`, and bounded on a continuous injective Cantor **subcopy**
of every isomorphism-antichain yields a `ThinRankAnalysis` for the isomorphism relation on
`ModelsOf φ`.  The extension of the rank outside `ModelsOf φ` (by `0`) is hidden here. -/
noncomputable def thinRankAnalysisOfClassRank (φ : L.Sentenceω)
    (ρ : Quotient (isoSetoid φ) → Ordinal.{0})
    (hlt : ∀ q, ρ q < (aleph 1).ord)
    (hfib : ∀ δ < (aleph 1).ord, Countable {q // ρ q = δ})
    (hbdd : ∀ f : (ℕ → Bool) → StructureSpace L, Continuous f →
      ∀ hf : ∀ x, f x ∈ ModelsOf φ, (∀ x y, x ≠ y → ¬ (structureIsoSetoid L).r (f x) (f y)) →
        ∃ e : (ℕ → Bool) → (ℕ → Bool), Continuous e ∧ Function.Injective e ∧
          ∃ β < (aleph 1).ord, ∀ x,
            ρ (Quotient.mk (isoSetoid φ) ⟨f (e x), hf (e x)⟩) < β) :
    ThinRankAnalysis (structureIsoSetoid L) (ModelsOf φ) where
  rank c := open scoped Classical in
    if h : c ∈ ModelsOf φ then ρ (Quotient.mk (isoSetoid φ) ⟨c, h⟩) else 0
  rank_lt_omega1 c hc := by
    rw [dite_eq_left hc, ← ord_aleph]; exact hlt _
  fixedRankAntichains_countable α hα B hBA hrank hanti := by
    rw [← ord_aleph] at hα
    have := hfib α hα
    -- `B` injects into the fibre `{q // ρ q = α}` via the class of the code
    have hinj : Function.Injective
        (fun c : B => (⟨Quotient.mk (isoSetoid φ) ⟨c.1, hBA c.2⟩, by
          have := hrank c.1 c.2
          rwa [dite_eq_left (hBA c.2)] at this⟩ : {q // ρ q = α})) := by
      intro c₁ c₂ h
      have hq := Subtype.mk.inj h
      have hr : (isoSetoid φ).r ⟨c₁.1, hBA c₁.2⟩ ⟨c₂.1, hBA c₂.2⟩ := Quotient.exact hq
      exact Subtype.ext (hanti c₁.1 c₁.2 c₂.1 c₂.2 (isoSetoid_r_iff.mp hr))
    exact Set.countable_coe_iff.mp hinj.countable
  bounded_on_refined_cantor_antichains f hcont hmem hanti := by
    obtain ⟨e, hec, hei, β, hβ, hb⟩ := hbdd f hcont hmem hanti
    refine ⟨e, hec, hei, β, by rwa [ord_aleph] at hβ, fun x => ?_⟩
    rw [dite_eq_left (hmem (e x))]; exact hb x

/-- A countable-ordinal rank analysis of the isomorphism relation on the coded `ℕ`-models of
`φ` makes `φ` thin on them.  (`StructureSpace L` is Polish; the metric is chosen here, the
topology is unchanged.) -/
theorem isThinOnNatModels_of_thinRankAnalysis (φ : L.Sentenceω)
    (T : ThinRankAnalysis (structureIsoSetoid L) (ModelsOf φ)) : φ.IsThinOnNatModels := by
  let _ := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace L)
  exact T.isThinOn

/-- **The standard upper bound**: thinness of an `L_{ω₁ω}` sentence gives at most `ℵ₁`
isomorphism classes of `ℕ`-models, by witnessed Morley counting (at most `ℵ₁` classes or a
perfect set of pairwise non-isomorphic `ℕ`-models). -/
theorem natModelSpectrum_le_aleph_one_of_thin {φ : L.Sentenceω} (hthin : φ.IsThinOnNatModels) :
    natModelSpectrum φ ≤ aleph 1 :=
  (natModelSpectrum_le_aleph_one_or_perfectSet φ).resolve_right
    (Sentenceω.isThinOnNatModels_iff.mp hthin)

omit [Countable (Σ l, L.Relations l)] in
/-- Uncountably many `ℕ`-models and `ℕ`-tier thinness refute the perfect-set form, with no
continuum hypothesis. -/
theorem not_vaughtConjecturePerfectSetFor_of_thin {φ : L.Sentenceω}
    (h : ℵ₀ < natModelSpectrum φ) (hthin : φ.IsThinOnNatModels) :
    ¬ VaughtConjecturePerfectSetFor φ :=
  Sentenceω.not_perfectSetDichotomyNat_of_thin hthin h

omit [Countable (Σ l, L.Relations l)] in
/-- Uncountably many countable models, `ℕ`-tier thinness, and no finite models refute the
all-countable perfect-set form, with no continuum hypothesis. -/
theorem not_allCountableVaughtConjecturePerfectSetFor_of_thin {φ : L.Sentenceω}
    (h : ℵ₀ < allCountableSpectrum φ) (hthin : φ.IsThinOnNatModels)
    (hfin : HasNoFiniteModels φ) : ¬ AllCountableVaughtConjecturePerfectSetFor φ := by
  have hnat : ℵ₀ < natModelSpectrum φ := by
    simpa only [allCountableSpectrum_eq_natModelSpectrum hfin] using h
  exact Sentenceω.not_perfectSetDichotomyAllCountable_of_thin hthin hnat hfin

/-- **Single-rank headline shape.**  One rank on the isomorphism classes of the `ℕ`-models of
`φ` with totality, countable fibres, cofinal range and boundedness on Cantor
isomorphism-antichains gives `I(φ,ℵ₀) = ℵ₁` *and* thinness, hence refutes the perfect-set form
of Vaught's conjecture outright. -/
theorem not_vaughtConjecturePerfectSetFor_of_classRank (φ : L.Sentenceω)
    (ρ : Quotient (isoSetoid φ) → Ordinal.{0})
    (hlt : ∀ q, ρ q < (aleph 1).ord)
    (hfib : ∀ δ < (aleph 1).ord, Countable {q // ρ q = δ})
    (hcof : ∀ δ < (aleph 1).ord, ∃ q, δ < ρ q)
    (hbdd : ∀ f : (ℕ → Bool) → StructureSpace L, Continuous f →
      ∀ hf : ∀ x, f x ∈ ModelsOf φ, (∀ x y, x ≠ y → ¬ (structureIsoSetoid L).r (f x) (f y)) →
        ∃ e : (ℕ → Bool) → (ℕ → Bool), Continuous e ∧ Function.Injective e ∧
          ∃ β < (aleph 1).ord, ∀ x,
            ρ (Quotient.mk (isoSetoid φ) ⟨f (e x), hf (e x)⟩) < β) :
    ¬ VaughtConjecturePerfectSetFor φ := by
  refine not_vaughtConjecturePerfectSetFor_of_thin ?_ ?_
  · rw [natModelSpectrum_eq_aleph_one_of_rank φ ρ hlt hfib hcof]; exact aleph0_lt_aleph_one
  · exact isThinOnNatModels_of_thinRankAnalysis φ (thinRankAnalysisOfClassRank φ ρ hlt hfib hbdd)

/-- The all-countable variant of the single-rank headline, for a sentence without finite
models. -/
theorem not_allCountableVaughtConjecturePerfectSetFor_of_classRank (φ : L.Sentenceω)
    (hfin : HasNoFiniteModels φ)
    (ρ : Quotient (isoSetoid φ) → Ordinal.{0})
    (hlt : ∀ q, ρ q < (aleph 1).ord)
    (hfib : ∀ δ < (aleph 1).ord, Countable {q // ρ q = δ})
    (hcof : ∀ δ < (aleph 1).ord, ∃ q, δ < ρ q)
    (hbdd : ∀ f : (ℕ → Bool) → StructureSpace L, Continuous f →
      ∀ hf : ∀ x, f x ∈ ModelsOf φ, (∀ x y, x ≠ y → ¬ (structureIsoSetoid L).r (f x) (f y)) →
        ∃ e : (ℕ → Bool) → (ℕ → Bool), Continuous e ∧ Function.Injective e ∧
          ∃ β < (aleph 1).ord, ∀ x,
            ρ (Quotient.mk (isoSetoid φ) ⟨f (e x), hf (e x)⟩) < β) :
    ¬ AllCountableVaughtConjecturePerfectSetFor φ := by
  refine not_allCountableVaughtConjecturePerfectSetFor_of_thin ?_ ?_ hfin
  · rw [allCountableSpectrum_eq_natModelSpectrum hfin,
      natModelSpectrum_eq_aleph_one_of_rank φ ρ hlt hfib hcof]
    exact aleph0_lt_aleph_one
  · exact isThinOnNatModels_of_thinRankAnalysis φ (thinRankAnalysisOfClassRank φ ρ hlt hfib hbdd)

end VaughtConjecture.Spectrum
