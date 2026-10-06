/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionDomainEndpoint

/-!
# Proof of the independent infinitary counterexample statement

This module deliberately does not import Challenge: its conventional infinitary
syntax and semantics are supplied by the proof library instead. Comparator must
compare their actual definitions as well as the final theorem. The finite model
and perfect-set assertions use the same sentence as the cardinality assertion.

This module consumes the migrated proof closure. Verification of the full migrated
package and its independent replay are prerequisites for submission.
-/

@[expose] public section

namespace PalomarChallenge

variable (R : ℕ → Type 1)

/-- A purely relational language, with no functions or constants. -/
def language : FirstOrder.Language := ⟨fun _ => Empty, R⟩

instance : (language R).IsRelational := fun _ => (inferInstance : IsEmpty Empty)

/-- A relation symbol together with a tuple of arguments. -/
abbrev RelQueryOn (M : Type) := Σ r : (Σ n, R n), (Fin r.1 → M)

/-- A Boolean relation truth table. -/
abbrev Code (M : Type) := RelQueryOn R M → Bool

/-- Codes for structures on the natural numbers. -/
abbrev StructureSpace := Code R ℕ

/-- Decode every relation coordinate. -/
@[instance_reducible]
def structureOfCode {M : Type} (c : Code R M) : (language R).Structure M where
  funMap := fun f => isEmptyElim f
  RelMap := fun {n} r xs => c ⟨⟨n, r⟩, xs⟩ = true

/-- Ordinary satisfaction in the decoded structure. -/
def Satisfies {M : Type} (φ : (language R).Sentenceω) (c : Code R M) : Prop :=
  letI := structureOfCode R c
  FirstOrder.Language.BoundedFormulaInf.Realize (M := M) φ Empty.elim Fin.elim0

/-- The set of sentence models in the ordinary coding space. -/
def ModelsOf (φ : (language R).Sentenceω) : Set (StructureSpace R) :=
  {c | Satisfies R φ c}

/-- Isomorphism by a permutation preserving every relation truth value. -/
def Isomorphic (c d : Code R ℕ) : Prop :=
  ∃ e : ℕ ≃ ℕ, ∀ n (r : R n) (xs : Fin n → ℕ), c ⟨⟨n, r⟩, xs⟩ = d ⟨⟨n, r⟩, e ∘ xs⟩

/-- The genuine equivalence relation on codes. -/
theorem isomorphic_equivalence : Equivalence (Isomorphic R) := ⟨
    fun c => ⟨Equiv.refl ℕ, fun _ _ _ => rfl⟩,
    by
      rintro c d ⟨e, h⟩
      refine ⟨e.symm, fun n r xs => ?_⟩
      simpa [Function.comp_def] using (h n r (e.symm ∘ xs)).symm,
    by
      rintro c d f ⟨e, h⟩ ⟨e', h'⟩
      exact ⟨e.trans e', fun n r xs => (h n r xs).trans (h' n r (e ∘ xs))⟩⟩

/-- The genuine equivalence relation on codes. -/
def isoSetoid : Setoid (Code R ℕ) := ⟨Isomorphic R, isomorphic_equivalence R⟩

/-- Actual models, not arbitrary codes or chosen representatives. -/
abbrev NatModel (φ : (language R).Sentenceω) := {c : Code R ℕ // Satisfies R φ c}

/-- Isomorphism restricted to the models. -/
def modelSetoid (φ : (language R).Sentenceω) : Setoid (NatModel R φ) :=
  Setoid.comap Subtype.val (isoSetoid R)

/-- Isomorphism classes of models. -/
abbrev IsoClasses (φ : (language R).Sentenceω) := Quotient (modelSetoid R φ)

/-- No finite coded model, including on the empty carrier. -/
def NoFiniteModels (φ : (language R).Sentenceω) : Prop :=
  ∀ n (c : Code R (Fin n)), ¬ Satisfies R φ c

/-- Thinness in the ordinary product topology on Boolean relation coordinates. -/
def NoPerfectAntichain (φ : (language R).Sentenceω) : Prop :=
  ¬ ∃ P : Set (StructureSpace R), P.Nonempty ∧ Perfect P ∧
    (∀ c ∈ P, Satisfies R φ c) ∧
      ∀ c ∈ P, ∀ d ∈ P, c ≠ d → ¬ Isomorphic R c d

open FirstOrder.Language
open VaughtConjecture.Knight

abbrev knightRelations := knightLang.Relations

/-- The ordinary permutation definition agrees with the library's structure isomorphisms. -/
theorem isomorphic_iff_library (c d : Code knightRelations ℕ) :
    Isomorphic knightRelations c d ↔
      (structureIsoSetoid knightLang).r c d := by
  change Isomorphic knightRelations c d ↔
    Nonempty (@FirstOrder.Language.Equiv knightLang ℕ ℕ
      (FirstOrder.Language.StructureSpaceOn.toStructure c)
      (FirstOrder.Language.StructureSpaceOn.toStructure d))
  constructor
  · rintro ⟨e, h⟩
    refine ⟨@FirstOrder.Language.Equiv.mk knightLang ℕ ℕ
      (FirstOrder.Language.StructureSpaceOn.toStructure c)
      (FirstOrder.Language.StructureSpaceOn.toStructure d) e
      (fun f => isEmptyElim f) (fun {n} r xs => ?_)⟩
    change d ⟨⟨n, r⟩, e ∘ xs⟩ = true ↔ c ⟨⟨n, r⟩, xs⟩ = true
    rw [h n r xs]
  · rintro ⟨e⟩
    let σ := @FirstOrder.Language.Equiv.toEquiv knightLang ℕ ℕ
      (FirstOrder.Language.StructureSpaceOn.toStructure c)
      (FirstOrder.Language.StructureSpaceOn.toStructure d) e
    refine ⟨σ, fun n r xs => ?_⟩
    have h := @FirstOrder.Language.Equiv.map_rel' knightLang ℕ ℕ
      (FirstOrder.Language.StructureSpaceOn.toStructure c)
      (FirstOrder.Language.StructureSpaceOn.toStructure d) e n r xs
    change (d ⟨⟨n, r⟩, σ ∘ xs⟩ = true ↔ c ⟨⟨n, r⟩, xs⟩ = true) at h
    cases hc : c ⟨⟨n, r⟩, xs⟩ <;>
      cases hd : d ⟨⟨n, r⟩, σ ∘ xs⟩ <;> simp_all

/-- The independently stated model relation is the one used by the proved endpoint. -/
theorem knight_modelSetoid_eq :
    modelSetoid knightRelations knightSentence = FirstOrder.Language.isoSetoid knightSentence := by
  ext c d
  exact isomorphic_iff_library c.1 d.1

/-- A countable relational infinitary sentence with exact spectrum and CH-independent thinness. -/
theorem independent_challenge :
    ∃ (R : ℕ → Type 1) (_ : Countable (Σ n, R n)) (φ : (language R).Sentenceω),
      Cardinal.mk (IsoClasses R φ) = Cardinal.aleph 1 ∧
      NoFiniteModels R φ ∧ NoPerfectAntichain R φ := by
  refine ⟨knightRelations, knightLang.countable_relations, knightSentence, ?_, ?_, ?_⟩
  · change Cardinal.mk (Quotient (modelSetoid knightRelations knightSentence)) = _
    rw [knight_modelSetoid_eq]
    exact ExpansionDomainEndpoint.natModelSpectrum_eq_aleph_one
  · intro n c hc
    have hmem : c ∈ ModelsOfOn (α := Fin n) knightSentence := hc
    rw [hasNoFiniteModels_knightSentence n] at hmem
    exact hmem
  · rintro ⟨P, hne, hperfect, hmodels, hanti⟩
    apply ExpansionDomainEndpoint.isThinOnNatModels
    refine ⟨P, hperfect, hne, hmodels, ?_⟩
    intro c hc d hd hcd
    by_contra hne
    exact hanti c hc d hd hne ((isomorphic_iff_library c d).mpr hcd)

end PalomarChallenge
