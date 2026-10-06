/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Correspondence

/-! # Infinitary truth on actual model classes

Satisfaction descends to isomorphism classes through the sentence/model
correspondence alone. No receiving, terminal classification or stopping-rank
theorem enters. The historical namespace is retained for compatibility.
-/

@[expose] public section

namespace VaughtConjecture.Knight.StoppingRankFiltration
open TypeTower FirstOrder Language

/-- These are the isomorphism classes counted by Knight's sentence, via
`isoClassEquiv`; no second equivalence relation is introduced. -/
abbrev Classes := Quotient knightModelSetoid

/-- Infinitary truth descends to isomorphism classes by ordinary isomorphism
invariance of satisfaction. -/
def realizes (φ : knightLang.Sentenceω) : Classes → Prop :=
  Quotient.lift (fun R : KnightNatModel =>
    @Sentenceω.Realize knightLang φ ℕ (structureOf R.1)) (by
      intro R S h
      obtain ⟨e⟩ := knightModelSetoid_r_iff.mp h
      exact propext (@LomegaEquiv.of_equiv knightLang ℕ ℕ
        (structureOf R.1) (structureOf S.1)
        (KnightRealization.IsIso.structureOfEquiv e.2) φ))

@[simp] theorem realizes_mk (φ : knightLang.Sentenceω) (R : KnightNatModel) :
    realizes φ (Quotient.mk knightModelSetoid R) ↔
      @Sentenceω.Realize knightLang φ ℕ (structureOf R.1) := Iff.rfl

end VaughtConjecture.Knight.StoppingRankFiltration
