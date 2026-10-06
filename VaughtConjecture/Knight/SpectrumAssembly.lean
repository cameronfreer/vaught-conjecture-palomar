/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Correspondence
public import VaughtConjecture.Knight.Rank
public import VaughtConjecture.Spectrum.RankCount

/-! # Conditional spectrum assembly for Knight's sentence (#61)

The final-assembly façade: everything between the open construction items and
`natModelSpectrum knightSentence = ℵ₁` is glue, and this module compiles all of it.

* `knightNatStopRank` — the intrinsic stopping rank on the actual quotient counted by
  the sentence, `Quotient knightModelSetoid`: descend
  `R ↦ stopRank R.atBlockZero` along `stopRank_eq_of_iso` (rank transport across
  isomorphism, `Iso.reduct`).
* `natModelSpectrum_knightSentence_eq_aleph_one_of_code_and_stopRank` — the
  **conditional** final theorem: an injective receipt code on the quotient (the #47/#57
  lane), pointwise totality `knightNatStopRank < ω₁` (the #30/#47 classification lane),
  and cofinality of the stopping ranks in `ω₁` (the #58 lane,
  `Knight/RankCofinality.lean`) give `natModelSpectrum knightSentence = ℵ₁`, via the
  compiled hybrid kernel (`mk_eq_aleph_one_of_code_and_cofinal`, applied through its
  pair-code instantiation `mk_eq_aleph_one_of_pair_code_and_cofinal`) and the
  correspondence `natModelSpectrum_knightSentence`.
* `natModelSpectrum_knightSentence_eq_aleph_one_of_code_and_modelwise_stopRank` — the
  modelwise façade: the rank hypotheses may be supplied directly on concrete
  `KnightNatModel`s; quotient transport is entirely automatic, so the #30/#58 results
  never need to be stated on quotients.

**CONDITIONAL.**  The hypotheses of both final theorems are exactly the open items of
the canonical remaining chain (docs/STATUS.md): the injective (failure level, cutoff)
receipt code (#47/#57), totality of the stopping rank below `ω₁` (#30/#47 +
classification), and rank cofinality's own inputs (#42 model existence + termination,
see `Knight/RankCofinality.lean`).  This module is assembly, not a claim of
completion: it certifies that no hidden correspondence, transport, or universe
obligation remains between those items and the exact spectrum.

**Provenance.**  Extracted from the user's finish-line probe
(`/tmp/VaughtFinishLineProbe.lean`, 2026-08-26, independently typechecked); the
trace-boundary probes of that file are out of scope here.

Construction-private: not exported from the root module (`TopProduction` precedent) —
conditional assembly stays out of the root cone until its hypotheses are discharged. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Spectrum Cardinal

theorem blockStage_zero_le_omegaStage : blockStage 0 ≤ omegaStage := by
  rw [blockStage_zero]
  exact le_rfl

/-- The source-stage presentation used by `KnightNatModel`, recast at `blockStage 0`
(the stage of the rank layer, equal to `omegaStage` by `blockStage_zero`). -/
noncomputable def KnightNatModel.atBlockZero (R : KnightNatModel) :
    KnightRealization (blockStage 0) ℕ :=
  R.1.reduct blockStage_zero_le_omegaStage

/-- Rank transport across isomorphism, in the form the quotient descent needs:
isomorphic models have isomorphic block-zero recasts (`Iso.reduct`). -/
theorem KnightNatModel.iso_atBlockZero {R R' : KnightNatModel}
    (hi : Nonempty (R.1.Iso R'.1)) : Nonempty (R.atBlockZero.Iso R'.atBlockZero) := by
  obtain ⟨i⟩ := hi
  exact ⟨i.reduct blockStage_zero_le_omegaStage⟩

/-- **The intrinsic stopping rank on the actual quotient counted by the sentence**:
`stopRank ∘ atBlockZero` descends to `Quotient knightModelSetoid` along
`stopRank_eq_of_iso`. -/
noncomputable def knightNatStopRank : Quotient knightModelSetoid → Ordinal.{0} :=
  Quotient.lift
    (fun R : KnightNatModel =>
      KnightRealization.stopRank R.atBlockZero)
    (fun R R' h => by
      have hi : Nonempty (R.1.Iso R'.1) := knightModelSetoid_r_iff.mp h
      have hi' : Nonempty (R.atBlockZero.Iso R'.atBlockZero) :=
        KnightNatModel.iso_atBlockZero hi
      exact KnightRealization.stopRank_eq_of_iso hi')

@[simp] theorem knightNatStopRank_mk (R : KnightNatModel) :
    knightNatStopRank (Quotient.mk knightModelSetoid R) =
      KnightRealization.stopRank R.atBlockZero := rfl

/-- **Conditional final theorem** (#61 assembly; hypotheses are the open #47/#57, #30/#47,
and #58 items — see the module docstring): an injective receipt code on the quotient,
pointwise `knightNatStopRank < ω₁`, and cofinal stopping ranks give the exact spectrum
`natModelSpectrum knightSentence = ℵ₁`, via `natModelSpectrum_knightSentence` and the
hybrid kernel `mk_eq_aleph_one_of_pair_code_and_cofinal`.  No further glue obligation
remains. -/
theorem natModelSpectrum_knightSentence_eq_aleph_one_of_code_and_stopRank
    (code : Quotient knightModelSetoid →
      { δ : Ordinal.{0} // δ < (aleph 1).ord } × ℕ)
    (hinj : Function.Injective code)
    (hlt : ∀ q, knightNatStopRank q < (aleph 1).ord)
    (hcof : ∀ δ < (aleph 1).ord, ∃ q, δ < knightNatStopRank q) :
    Spectrum.natModelSpectrum knightSentence = aleph 1 := by
  rw [natModelSpectrum_knightSentence]
  exact Spectrum.mk_eq_aleph_one_of_pair_code_and_cofinal code hinj
    knightNatStopRank hlt hcof

/-- **Modelwise façade** for the conditional final theorem (#61; same open hypotheses):
the rank hypotheses may be supplied directly on concrete `KnightNatModel`s — as the
#30 totality and #58 cofinality lanes naturally produce them — with quotient transport
entirely automatic. -/
theorem natModelSpectrum_knightSentence_eq_aleph_one_of_code_and_modelwise_stopRank
    (code : Quotient knightModelSetoid →
      { δ : Ordinal.{0} // δ < (aleph 1).ord } × ℕ)
    (hinj : Function.Injective code)
    (hlt : ∀ R : KnightNatModel,
      KnightRealization.stopRank R.atBlockZero < (aleph 1).ord)
    (hcof : ∀ δ < (aleph 1).ord, ∃ R : KnightNatModel,
      δ < KnightRealization.stopRank R.atBlockZero) :
    Spectrum.natModelSpectrum knightSentence = aleph 1 := by
  apply natModelSpectrum_knightSentence_eq_aleph_one_of_code_and_stopRank code hinj
  · intro q
    refine Quotient.inductionOn q ?_
    exact hlt
  · intro δ hδ
    obtain ⟨R, hR⟩ := hcof δ hδ
    exact ⟨Quotient.mk knightModelSetoid R, hR⟩

end VaughtConjecture.Knight
