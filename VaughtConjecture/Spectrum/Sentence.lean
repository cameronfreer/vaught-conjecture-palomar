/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.ModelTheory.MorleyCounting
public import InfinitaryLogic.Conditional.GandyHarrington
public import InfinitaryLogic.Conditional.MorleyPerfect
public import VaughtConjecture.Spectrum.RankCount

/-! # The countable spectrum of an `L_{ω₁,ω}` sentence

We take the notion of "countable models up to isomorphism" from
`InfinitaryLogic`.  Two counts are kept apart:

* `natModelSpectrum φ := #(Quotient (isoSetoid φ))` — isomorphism classes of `ℕ`-models,
  i.e. models of cardinality exactly `ℵ₀`.  This is the standard `I(φ, ℵ₀)`.
* `allCountableSpectrum φ := #(AllCodedIsoClasses φ)` — all carrier tiers (`ℕ` and every
  `Fin n`), faithfully representing all countable models by `codeModel`,
  `codeModel_eq_of_iso`, `iso_of_codeModel_eq`, `codeModel_surjective`.

The two agree when `φ` has no finite models (`HasNoFiniteModels`,
`allCountableSpectrum_eq_natModelSpectrum`).  Conventional names
(`CardinalVaughtConjectureFor`, and `VaughtConjecturePerfectSetFor` in `Spectrum.Thinness`)
refer to the `ℕ`-tier forms; the all-tier variants carry the prefix `AllCountable`.

* Morley's theorem (`morley_counting_coded` / `morley_counting`, unconditional in
  `InfinitaryLogic` via its proof of the Silver–Burgess dichotomy) gives
  `I(φ,ℵ₀) ≤ ℵ₁ ∨ I(φ,ℵ₀) = 2^ℵ₀` in both forms.  The witnessed refinements
  (`morley_counting_coded_or_perfect` / `morley_counting_or_perfect`) put a perfect set of
  pairwise non-isomorphic models in the second alternative; their spectrum-named adapters are
  `natModelSpectrum_le_aleph_one_or_perfectSet` /
  `allCountableSpectrum_le_aleph_one_or_perfectSet`.
* `natModelSpectrum_eq_aleph_one_of_rank` / `allCountableSpectrum_eq_aleph_one_of_rank`: the
  shape of Knight's headline — a total rank into `ω₁` with countable fibres and cofinal range
  on the isomorphism classes forces exactly `ℵ₁` classes.
* `not_cardinalVaughtConjectureFor_of_eq_aleph_one`: under `¬CH`, `I(φ,ℵ₀) = ℵ₁` refutes the
  cardinal form.  The CH-independent (perfect-set) form needs the separate thinness statement;
  see `Spectrum.Thinness` and `docs/DESIGN.md`. -/

@[expose] public section

namespace VaughtConjecture.Spectrum

open FirstOrder Language Cardinal

universe u v w

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- The standard `I(φ, ℵ₀)`: isomorphism classes of `ℕ`-models of `φ` (models of cardinality
exactly `ℵ₀`). -/
noncomputable def natModelSpectrum (φ : L.Sentenceω) : Cardinal :=
  #(Quotient (isoSetoid φ))

/-- The all-countable variant: isomorphism classes of countable models of `φ` over **all**
carrier tiers (`ℕ`-models and every `Fin n` tier). -/
noncomputable def allCountableSpectrum (φ : L.Sentenceω) : Cardinal :=
  #(AllCodedIsoClasses φ)

/-- `φ` has no finite models (every `Fin n` tier of coded models is empty). -/
def HasNoFiniteModels (φ : L.Sentenceω) : Prop :=
  ∀ n : ℕ, ModelsOfOn (α := Fin n) φ = ∅

omit [Countable (Σ l, L.Relations l)] in
/-- Without finite models, the all-countable spectrum is the standard `I(φ, ℵ₀)`. -/
theorem allCountableSpectrum_eq_natModelSpectrum {φ : L.Sentenceω} (h : HasNoFiniteModels φ) :
    allCountableSpectrum φ = natModelSpectrum φ := by
  have hempty : IsEmpty (Σ n, Quotient (isoSetoidOn φ n)) := by
    refine ⟨fun ⟨n, q⟩ => ?_⟩
    induction q using Quotient.inductionOn with
    | h c => exact (Set.eq_empty_iff_forall_notMem.mp (h n)) c.1 c.2
  unfold allCountableSpectrum natModelSpectrum AllCodedIsoClasses
  rw [mk_sum, mk_eq_zero (Σ n, Quotient (isoSetoidOn φ n)), lift_zero, add_zero, lift_id]

/-- The **cardinal** form of Vaught's conjecture for `φ` (`ℕ`-tier): countably many or
continuum many countable models.  (The CH-independent perfect-set form is
`VaughtConjecturePerfectSetFor` in `Spectrum.Thinness`.) -/
def CardinalVaughtConjectureFor (φ : L.Sentenceω) : Prop :=
  natModelSpectrum φ ≤ ℵ₀ ∨ natModelSpectrum φ = continuum

/-- The all-countable variant of the cardinal form (all carrier tiers). -/
def AllCountableCardinalVaughtConjectureFor (φ : L.Sentenceω) : Prop :=
  allCountableSpectrum φ ≤ ℵ₀ ∨ allCountableSpectrum φ = continuum

/-- Morley's theorem, `ℕ`-tier: `I(φ, ℵ₀) ≤ ℵ₁` or `I(φ, ℵ₀) = 2^ℵ₀`. -/
theorem natModelSpectrum_le_aleph_one_or_eq_continuum (φ : L.Sentenceω) :
    natModelSpectrum φ ≤ aleph 1 ∨ natModelSpectrum φ = continuum :=
  morley_counting_coded silverBurgessDichotomy φ

/-- Morley's theorem, all-countable variant.  Proved from the witnessed dichotomy
(`morley_counting_or_perfect_cardinal`), so no `SilverBurgessDichotomy` argument is needed. -/
theorem allCountableSpectrum_le_aleph_one_or_eq_continuum (φ : L.Sentenceω) :
    allCountableSpectrum φ ≤ aleph 1 ∨ allCountableSpectrum φ = continuum :=
  morley_counting_or_perfect_cardinal φ

/-- Morley counting with a witness, `ℕ`-tier: at most `ℵ₁` isomorphism classes, or a perfect
set of pairwise non-isomorphic `ℕ`-models. -/
theorem natModelSpectrum_le_aleph_one_or_perfectSet (φ : L.Sentenceω) :
    natModelSpectrum φ ≤ aleph 1 ∨ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels :=
  morley_counting_coded_or_perfect φ

/-- Morley counting with a witness, all-countable variant: at most `ℵ₁` classes over all
tiers, or a perfect set of pairwise non-isomorphic models in some carrier tier. -/
theorem allCountableSpectrum_le_aleph_one_or_perfectSet (φ : L.Sentenceω) :
    allCountableSpectrum φ ≤ aleph 1 ∨ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels ∨
      ∃ n, φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n :=
  morley_counting_or_perfect φ

omit [Countable (Σ l, L.Relations l)] in
/-- The ranked-realization kernel on the isomorphism classes of `ℕ`-models: a total,
countable-fibred, cofinal rank into `ω₁` gives `I(φ, ℵ₀) = ℵ₁`. -/
theorem natModelSpectrum_eq_aleph_one_of_rank (φ : L.Sentenceω)
    (ρ : Quotient (isoSetoid φ) → Ordinal.{w})
    (hlt : ∀ x, ρ x < (aleph 1).ord)
    (hfib : ∀ δ < (aleph 1).ord, Countable {x // ρ x = δ})
    (hcof : ∀ δ < (aleph 1).ord, ∃ x, δ < ρ x) :
    natModelSpectrum φ = aleph 1 :=
  mk_eq_aleph_one_of_rank ρ hlt hfib hcof

omit [Countable (Σ l, L.Relations l)] in
/-- The ranked-realization kernel on all coded isomorphism classes (all tiers). -/
theorem allCountableSpectrum_eq_aleph_one_of_rank (φ : L.Sentenceω)
    (ρ : AllCodedIsoClasses φ → Ordinal.{w})
    (hlt : ∀ x, ρ x < (aleph 1).ord)
    (hfib : ∀ δ < (aleph 1).ord, Countable {x // ρ x = δ})
    (hcof : ∀ δ < (aleph 1).ord, ∃ x, δ < ρ x) :
    allCountableSpectrum φ = aleph 1 :=
  mk_eq_aleph_one_of_rank ρ hlt hfib hcof

omit [Countable (Σ l, L.Relations l)] in
/-- Under `¬CH`, exactly `ℵ₁` countable models refutes the cardinal form of the conjecture. -/
theorem not_cardinalVaughtConjectureFor_of_eq_aleph_one {φ : L.Sentenceω}
    (h : natModelSpectrum φ = aleph 1) (hnCH : (aleph 1 : Cardinal.{v}) < continuum) :
    ¬ CardinalVaughtConjectureFor φ := by
  rintro (h1 | h1)
  · rw [h] at h1
    exact absurd h1 (not_le.mpr (aleph0_lt_aleph_one))
  · rw [h] at h1
    exact absurd h1 (ne_of_lt hnCH)

omit [Countable (Σ l, L.Relations l)] in
/-- Under `¬CH`, exactly `ℵ₁` countable models (all tiers) refutes the all-countable cardinal
form. -/
theorem not_allCountableCardinalVaughtConjectureFor_of_eq_aleph_one {φ : L.Sentenceω}
    (h : allCountableSpectrum φ = aleph 1) (hnCH : (aleph 1 : Cardinal.{v}) < continuum) :
    ¬ AllCountableCardinalVaughtConjectureFor φ := by
  rintro (h1 | h1)
  · rw [h] at h1
    exact absurd h1 (not_le.mpr (aleph0_lt_aleph_one))
  · rw [h] at h1
    exact absurd h1 (ne_of_lt hnCH)

end VaughtConjecture.Spectrum
