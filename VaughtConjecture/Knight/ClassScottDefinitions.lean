/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ClassPresentation
public import InfinitaryLogic.Descriptive.ScottDefinability

/-! # Scott sentences define every countable set of classes

This is the ordinary Scott-sentence argument through the sentence/model
correspondence. It uses no receiving, classification or rank analysis. In
particular countable disjunction includes empty and finite sets, and it asserts
neither effective enumeration nor a measurable choice of Scott sentences.
-/

@[expose] public section

namespace VaughtConjecture.Knight.StoppingRankFiltration
open FirstOrder Language

/-- Truth respects ordinary infinitary negation on the class quotient. -/
theorem realizes_not (φ : knightLang.Sentenceω) (q : Classes) :
    realizes φ.not q ↔ ¬ realizes φ q := by
  refine Quotient.inductionOn q fun R => ?_
  let := structureOf R.1
  exact BoundedFormulaω.realize_not φ

/-- Truth respects countable disjunction, including the empty disjunction. -/
theorem realizes_esup {ι : Type*} [Encodable ι] (φ : ι → knightLang.Sentenceω)
    (q : Classes) : realizes (BoundedFormulaω.esup φ) q ↔ ∃ i, realizes (φ i) q := by
  refine Quotient.inductionOn q fun R => ?_
  let := structureOf R.1
  exact BoundedFormulaω.realize_esup φ

/-- Ordinary Scott sentences isolate each class among the actual Knight models
(`InfinitaryLogic`'s `isolatedPresentation_of_surjective` on the class presentation).
This does not assign an effective or measurable Scott sentence to classes. -/
theorem exists_isolating_sentence (q : Classes) :
    ∃ φ : knightLang.Sentenceω, ∀ s : Classes, realizes φ s ↔ s = q :=
  isolatedPresentation_of_surjective (fun c : ModelsOf knightSentence => c.1) modelClass
    modelClass_surjective (fun _ _ h => modelClass_eq_of_iso h) realizes realizes_modelClass q

/-- Every countable class set is sentence-definable, by the standard Scott
sentence disjunction (`InfinitaryLogic`'s `exists_sentence_of_countable_of_presentation`).
The set may be empty. -/
theorem exists_sentence_of_countable {S : Set Classes} (hS : S.Countable) :
    ∃ φ : knightLang.Sentenceω, ∀ q : Classes, realizes φ q ↔ q ∈ S :=
  exists_sentence_of_countable_of_presentation (fun c : ModelsOf knightSentence => c.1)
    modelClass modelClass_surjective (fun _ _ h => modelClass_eq_of_iso h) realizes
    realizes_modelClass hS

end VaughtConjecture.Knight.StoppingRankFiltration
