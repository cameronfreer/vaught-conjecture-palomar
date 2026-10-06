/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ClassTruth
public import InfinitaryLogic.Descriptive.SmallVocabularyTransport

/-! # The class quotient as a presentation of the coded models

`InfinitaryLogic`'s descriptive theorems for a countable relational language take a
**presentation** of the isomorphism classes: a map `classOf` from codes to a type `Q`,
surjective and constant on isomorphic codes, with a truth predicate on `Q` that reads back as
satisfaction on codes.  The counted class quotient `Classes` is such a presentation of the coded
models of `knightSentence`:

* `modelClass c` is the class of the coded model `c` (`isoClassEquiv` after `Quotient.mk`);
* `modelClass_surjective`, `modelClass_eq_of_iso`: the presentation laws;
* `realizes_modelClass`: class truth is satisfaction on the code.

Countability of classes and countability of codes remain distinct: `Q` carries no measurable
structure, and no measurable section of `modelClass` is chosen.  These are the actual
satisfaction equations consumed by the sentence-split, observable-constancy and
Scott-definability applications. -/

@[expose] public section

namespace VaughtConjecture.Knight.StoppingRankFiltration

open FirstOrder Language

/-- The canonical class of a coded model.  No measurability of this map is asserted. -/
noncomputable def modelClass (c : ModelsOf knightSentence) : Classes :=
  isoClassEquiv (Quotient.mk (isoSetoid knightSentence) c)

theorem modelClass_surjective : Function.Surjective modelClass := by
  intro q
  obtain ⟨c, hc⟩ := Quotient.mk_surjective (isoClassEquiv.symm q)
  exact ⟨c, by rw [modelClass, hc, Equiv.apply_symm_apply]⟩

/-- Isomorphic codes have the same class. -/
theorem modelClass_eq_of_iso {c d : ModelsOf knightSentence}
    (h : (structureIsoSetoid knightLang).r c.1 d.1) : modelClass c = modelClass d :=
  congrArg isoClassEquiv (Quotient.sound (isoSetoid_r_iff.mpr h))

/-- **Class truth is satisfaction on the code.** -/
theorem realizes_modelClass (φ : knightLang.Sentenceω) (c : ModelsOf knightSentence) :
    realizes φ (modelClass c) ↔ c.1 ∈ ModelsOf φ := by
  change @Sentenceω.Realize knightLang φ ℕ (structureOf (realizationOfCode c).1) ↔ _
  exact (@LomegaEquiv.of_equiv knightLang ℕ ℕ
    (structureOf (realizationOfCode c).1) c.1.toStructure
    (isKnightModel_of_mem c).structureOfToRealizationEquiv φ).trans
    (FirstOrder.Language.SmallVocabulary.mem_modelsOf_iff_realize knightLang c.1 φ).symm

end VaughtConjecture.Knight.StoppingRankFiltration
