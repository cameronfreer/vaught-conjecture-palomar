/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Sentence

/-! # Prop. 3.3.5: countable models of `T` ↔ countable models of `S^ω`, up to isomorphism

`Knight/Sentence.lean` gives the **pointwise** correspondence between `L`-structures satisfying
Knight's sentence `T` (`knightSentence`) and models of `S^ω` (`KnightRealization.IsModel`):
`toRealization M` / `structureOf R`, both directions, with round trips.  This file does the
**isomorphism-class bookkeeping**, so that the count `Spectrum.natModelSpectrum knightSentence`
(`I(T, ℵ₀)`, isomorphism classes of coded `ℕ`-models of `T`, `InfinitaryLogic`'s `isoSetoid`)
is the number of models of `S^ω` on the carrier `ℕ` up to isomorphism.

**Isomorphism of realizations.**  Generic: `TypeTower.Realization.IsIso R R' e` (`e : M ≃ N`
transports labels, `R'.eval (t.trans e) = R.eval t`), `Realization.Iso`, and the ambient setoid
`Realization.isoSetoid T α M` (`TypeTower/Basic.lean`).  Here `knightModelSetoid` is its pullback
to the `ℕ`-carrier models of `S^ω`, `KnightNatModel := {R : KnightRealization omegaStage ℕ //
R.IsModel}`.

**Transfer.**  An `L`-isomorphism `e : M ≃[knightLang] N` of structures satisfying `T` is an
isomorphism `toRealization M ≅ toRealization N` (`IsKnightModel.isIso_toRealization`); conversely
an isomorphism of realizations `R ≅ R'` is an `L`-isomorphism `structureOf R ≃[knightLang]
structureOf R'` (`IsIso.structureOfEquiv`), and an `L`-isomorphism of the structures of two
models is an isomorphism of the models (`IsIso.of_structureOf`).

**The bijection.**  `isoClassEquiv : Quotient (isoSetoid knightSentence) ≃ Quotient
knightModelSetoid`, built from `realizationOfCode` (decode, then `toRealization`) and
`codeOfModel` (`structureOf`, then `ofStructure`), each respecting isomorphism, inverse to each
other up to isomorphism by the round trips of `Knight/Sentence.lean`.  Hence
`natModelSpectrum_knightSentence : natModelSpectrum knightSentence = #(Quotient knightModelSetoid)`
(both sides in `Cardinal.{1}`: `knightLang : Language.{0, 1}`, so `StructureSpace knightLang :
Type 1`, and `S ω n : Type 1`, so `KnightRealization omegaStage ℕ : Type 1` — no lifts), and, with
`hasNoFiniteModels_knightSentence`, `allCountableSpectrum_knightSentence : allCountableSpectrum
knightSentence = natModelSpectrum knightSentence` (all carrier tiers agree with the `ℕ` tier).

**All tiers, by `codeModel`.**  For a countable model `R` of `S^ω` on any carrier,
`IsModel.codedClass hR := codeModel hR.realize_knightSentence : AllCodedIsoClasses knightSentence`;
isomorphic models have the same class (`codedClass_eq_of_iso`), models with the same class are
isomorphic (`iso_of_codedClass_eq`), and every class arises (`codedClass_surjective`).

The only structure-coding bridge not in `InfinitaryLogic` is `ofStructureEquiv`: an `L`-structure
on `ℕ` is `L`-isomorphic (by the identity) to the decoding of its own code — stated here
generically in `L` (candidate for `StructureSpace.ofStructure` in `InfinitaryLogic`). -/

@[expose] public section

namespace VaughtConjecture.Knight

open FirstOrder Language Structure TypeTower Spectrum Cardinal
open scoped Lomega1omega

universe u v w w'

/-! ### Coding bridge: a structure on `ℕ` and the decoding of its code -/

section Coding

variable {L : Language.{u, v}} [L.IsRelational]

/-- An `L`-structure on `ℕ` is `L`-isomorphic, by the identity, to the decoding of its code
(`StructureSpace.ofStructure`): relation-wise the two agree (`toStructure_ofStructure`). -/
def ofStructureEquiv (inst : L.Structure ℕ) :
    @Language.Equiv L ℕ ℕ inst (StructureSpace.ofStructure inst).toStructure :=
  @Language.Equiv.mk L ℕ ℕ inst (StructureSpace.ofStructure inst).toStructure (Equiv.refl ℕ)
    (fun f => isEmptyElim f) (fun R xs => StructureSpace.toStructure_ofStructure inst R xs)

/-- A sentence holds in the decoding of the code of a structure on `ℕ` iff it holds in the
structure. -/
theorem realize_toStructure_ofStructure (inst : L.Structure ℕ) (φ : L.Sentenceω) :
    @Sentenceω.Realize L φ ℕ (StructureSpace.ofStructure inst).toStructure ↔
      @Sentenceω.Realize L φ ℕ inst :=
  (@LomegaEquiv.of_equiv L ℕ ℕ inst (StructureSpace.ofStructure inst).toStructure
    (ofStructureEquiv inst) φ).symm

end Coding

/-! ### Isomorphism transfer between structures and realizations -/

section Transfer

variable {M : Type w} {N : Type w'}

/-- **Structures to realizations.**  An `L`-isomorphism of structures satisfying (the
uniqueness clause of) `T` is an isomorphism of their realizations. -/
theorem IsKnightModel.isIso_toRealization {instM : knightLang.Structure M}
    {instN : knightLang.Structure N} (hM : IsKnightModel M) (hN : IsKnightModel N)
    (e : M ≃[knightLang] N) :
    (toRealization M).IsIso (toRealization N) e.toEquiv := by
  intro n t
  have key : ∀ p : S Ordinal.omega0 n,
      Holds p ⇑(t.trans e.toEquiv.toEmbedding) ↔ Holds p ⇑t := fun p =>
    StrongHomClass.map_rel e p ⇑t
  cases h : (toRealization M).eval t with
  | none =>
    rw [toRealization_eval_eq_none_iff] at h ⊢
    exact fun p hp => h p ((key p).mp hp)
  | some p =>
    exact (hN.eval_eq_some_iff _ p).mpr ((key p).mpr ((hM.eval_eq_some_iff t p).mp h))

/-- **Realizations to structures.**  An isomorphism of realizations is an `L`-isomorphism of
their structures (no model hypothesis needed). -/
def KnightRealization.IsIso.structureOfEquiv {R : KnightRealization omegaStage M}
    {R' : KnightRealization omegaStage N} {e : M ≃ N} (h : R.IsIso R' e) :
    @Language.Equiv knightLang M N (structureOf R) (structureOf R') :=
  @Language.Equiv.mk knightLang M N (structureOf R) (structureOf R') e (fun f => isEmptyElim f)
    fun {n} p xs => by
      change (∃ hi : Function.Injective (⇑e ∘ xs), R'.eval ⟨⇑e ∘ xs, hi⟩ = some p) ↔
        ∃ hi : Function.Injective xs, R.eval ⟨xs, hi⟩ = some p
      constructor
      · rintro ⟨hi, hp⟩
        exact ⟨hi.of_comp, (h ⟨xs, hi.of_comp⟩).symm.trans hp⟩
      · rintro ⟨hi, hp⟩
        exact ⟨e.injective.comp hi, (h ⟨xs, hi⟩).trans hp⟩

/-- **Structures of models to models.**  An `L`-isomorphism between the structures of two
models of `S^ω` is an isomorphism of the models (through the round trip
`toRealization_structureOf_eval`). -/
theorem KnightRealization.IsIso.of_structureOf {R : KnightRealization omegaStage M}
    {R' : KnightRealization omegaStage N} (hR : R.IsModel) (hR' : R'.IsModel)
    (e : @Language.Equiv knightLang M N (structureOf R) (structureOf R')) :
    R.IsIso R' (@Language.Equiv.toEquiv knightLang M N (structureOf R) (structureOf R') e) := by
  intro n t
  have h := (IsKnightModel.isIso_toRealization hR.isKnightModel hR'.isKnightModel e) t
  rwa [toRealization_structureOf_eval, toRealization_structureOf_eval] at h

/-- Under `T`, the structure of the realization of `M` is `L`-isomorphic to `M` by the identity
(`holds_structureOf_toRealization`). -/
def IsKnightModel.structureOfToRealizationEquiv {inst : knightLang.Structure M}
    (h : IsKnightModel M) :
    @Language.Equiv knightLang M M (structureOf (toRealization M)) inst :=
  @Language.Equiv.mk knightLang M M (structureOf (toRealization M)) inst (Equiv.refl M)
    (fun f => isEmptyElim f) fun p xs => (holds_structureOf_toRealization h p xs).symm

end Transfer

/-! ### `ℕ`-carrier models of `S^ω` up to isomorphism, and the bijection with `I(T, ℵ₀)` -/

/-- The models of `S^ω` on the carrier `ℕ`. -/
abbrev KnightNatModel : Type 1 := {R : KnightRealization omegaStage ℕ // R.IsModel}

/-- **Models of `S^ω` on `ℕ` up to isomorphism**: the ambient `Realization.isoSetoid` pulled
back to the models. -/
noncomputable def knightModelSetoid : Setoid KnightNatModel :=
  (Realization.isoSetoid knightTower omegaStage ℕ).comap Subtype.val

theorem knightModelSetoid_r_iff {R R' : KnightNatModel} :
    knightModelSetoid.r R R' ↔ Nonempty (R.1.Iso R'.1) := Iff.rfl

/-- A coded `ℕ`-model of `T` decodes to a structure satisfying the clauses of `T`. -/
theorem isKnightModel_of_mem (c : ModelsOf knightSentence) :
    @IsKnightModel ℕ c.1.toStructure :=
  (@realize_knightSentence_iff ℕ c.1.toStructure).mp c.2

/-- Decode a coded `ℕ`-model of `T` and take its realization: a model of `S^ω` on `ℕ`. -/
noncomputable def realizationOfCode (c : ModelsOf knightSentence) : KnightNatModel :=
  ⟨@toRealization ℕ c.1.toStructure, @isModel_toRealization_of_realize ℕ c.1.toStructure c.2⟩

/-- The structure of a model of `S^ω` on `ℕ`, coded: a coded `ℕ`-model of `T`. -/
noncomputable def codeOfModel (R : KnightNatModel) : ModelsOf knightSentence :=
  ⟨StructureSpace.ofStructure (structureOf R.1),
    (realize_toStructure_ofStructure (structureOf R.1) knightSentence).mpr
      R.2.realize_knightSentence⟩

theorem codeOfModel_val (R : KnightNatModel) :
    (codeOfModel R).1 = StructureSpace.ofStructure (structureOf R.1) := rfl

/-- The decoded structure of the code of an `ℕ`-model of `S^ω` (isomorphic to `structureOf R.1`
by the identity, `ofStructureEquiv`). -/
noncomputable abbrev codeStructure (R : KnightNatModel) : knightLang.Structure ℕ :=
  (StructureSpace.ofStructure (structureOf R.1)).toStructure

/-- `realizationOfCode` respects isomorphism. -/
theorem realizationOfCode_rel {c₁ c₂ : ModelsOf knightSentence}
    (h : (isoSetoid knightSentence).r c₁ c₂) :
    knightModelSetoid.r (realizationOfCode c₁) (realizationOfCode c₂) := by
  obtain ⟨e⟩ := isoSetoid_r_iff.mp h
  exact ⟨⟨@Language.Equiv.toEquiv knightLang ℕ ℕ c₁.1.toStructure c₂.1.toStructure e,
    (isKnightModel_of_mem c₁).isIso_toRealization (isKnightModel_of_mem c₂) e⟩⟩

/-- `codeOfModel` respects isomorphism. -/
theorem codeOfModel_rel {R R' : KnightNatModel} (h : knightModelSetoid.r R R') :
    (isoSetoid knightSentence).r (codeOfModel R) (codeOfModel R') := by
  obtain ⟨⟨e, he⟩⟩ := h
  refine isoSetoid_r_iff.mpr ⟨?_⟩
  -- code R ≃ structureOf R ≃ structureOf R' ≃ code R'
  exact @Language.Equiv.comp knightLang ℕ ℕ (codeStructure R) (structureOf R'.1) ℕ
    (codeStructure R') (ofStructureEquiv (structureOf R'.1))
    (@Language.Equiv.comp knightLang ℕ ℕ (codeStructure R) (structureOf R.1) ℕ
      (structureOf R'.1) (KnightRealization.IsIso.structureOfEquiv he)
      (@Language.Equiv.symm knightLang ℕ ℕ (structureOf R.1) (codeStructure R)
        (ofStructureEquiv (structureOf R.1))))

/-- Isomorphism classes of coded `ℕ`-models of `T` to isomorphism classes of `ℕ`-models of
`S^ω`. -/
noncomputable def classOfCode :
    Quotient (isoSetoid knightSentence) → Quotient knightModelSetoid :=
  Quotient.map realizationOfCode fun _ _ h => realizationOfCode_rel h

/-- Isomorphism classes of `ℕ`-models of `S^ω` to isomorphism classes of coded `ℕ`-models of
`T`. -/
noncomputable def classOfModel :
    Quotient knightModelSetoid → Quotient (isoSetoid knightSentence) :=
  Quotient.map codeOfModel fun _ _ h => codeOfModel_rel h

/-- **Prop. 3.3.5, isomorphism classes**: the countable (`ℕ`-carrier) models of `T` up to
isomorphism are in bijection with the models of `S^ω` on `ℕ` up to isomorphism. -/
noncomputable def isoClassEquiv :
    Quotient (isoSetoid knightSentence) ≃ Quotient knightModelSetoid where
  toFun := classOfCode
  invFun := classOfModel
  left_inv := by
    refine Quotient.ind fun c => Quotient.sound ?_
    refine isoSetoid_r_iff.mpr ⟨?_⟩
    -- code (structureOf (toRealization c)) ≃ structureOf (toRealization c) ≃ c
    exact @Language.Equiv.comp knightLang ℕ ℕ (codeStructure (realizationOfCode c))
      (structureOf (@toRealization ℕ c.1.toStructure)) ℕ c.1.toStructure
      (isKnightModel_of_mem c).structureOfToRealizationEquiv
      (@Language.Equiv.symm knightLang ℕ ℕ (structureOf (@toRealization ℕ c.1.toStructure))
        (codeStructure (realizationOfCode c)) (ofStructureEquiv _))
  right_inv := by
    refine Quotient.ind fun R => Quotient.sound ?_
    refine ⟨⟨Equiv.refl ℕ, fun t => ?_⟩⟩
    -- toRealization (code (structureOf R)) ≅ toRealization (structureOf R) = R
    have h := (IsKnightModel.isIso_toRealization (isKnightModel_of_mem (codeOfModel R))
      R.2.isKnightModel
      (@Language.Equiv.symm knightLang ℕ ℕ (structureOf R.1) (codeStructure R)
        (ofStructureEquiv _))) t
    rw [toRealization_structureOf_eval] at h
    exact h

/-- **`I(T, ℵ₀)` is the number of models of `S^ω` on `ℕ` up to isomorphism** (the transfer
#61 consumes).  Both sides live in `Cardinal.{1}` (`knightLang : Language.{0, 1}`;
`S ω n : Type 1`); no universe lifts are involved. -/
theorem natModelSpectrum_knightSentence :
    natModelSpectrum knightSentence = #(Quotient knightModelSetoid) :=
  mk_congr isoClassEquiv

/-- **All carrier tiers agree with the `ℕ` tier**: `T` has no finite models
(`hasNoFiniteModels_knightSentence`), so `allCountableSpectrum_eq_natModelSpectrum` applies. -/
theorem allCountableSpectrum_knightSentence :
    allCountableSpectrum knightSentence = natModelSpectrum knightSentence :=
  allCountableSpectrum_eq_natModelSpectrum hasNoFiniteModels_knightSentence

/-- The all-tier count is the number of models of `S^ω` on `ℕ` up to isomorphism. -/
theorem allCountableSpectrum_knightSentence_eq_mk :
    allCountableSpectrum knightSentence = #(Quotient knightModelSetoid) :=
  allCountableSpectrum_knightSentence.trans natModelSpectrum_knightSentence

/-! ### All countable carriers, through `codeModel` -/

section Coded

variable {M N : Type} [Countable M] [Countable N]

/-- The coded isomorphism class (`AllCodedIsoClasses knightSentence`) of a countable model of
`S^ω`: `codeModel` of its structure. -/
noncomputable def KnightRealization.IsModel.codedClass {R : KnightRealization omegaStage M}
    (hR : R.IsModel) : AllCodedIsoClasses knightSentence :=
  @codeModel knightLang _ knightSentence M (structureOf R) _ hR.realize_knightSentence

/-- Isomorphic countable models of `S^ω` have the same coded class. -/
theorem KnightRealization.IsModel.codedClass_eq_of_iso {R : KnightRealization omegaStage M}
    {R' : KnightRealization omegaStage N} (hR : R.IsModel) (hR' : R'.IsModel) {e : M ≃ N}
    (h : R.IsIso R' e) : hR.codedClass = hR'.codedClass :=
  @codeModel_eq_of_iso knightLang _ knightSentence M N (structureOf R) (structureOf R') _ _
    hR.realize_knightSentence hR'.realize_knightSentence
    (KnightRealization.IsIso.structureOfEquiv h)

/-- Countable models of `S^ω` with the same coded class are isomorphic. -/
theorem KnightRealization.IsModel.iso_of_codedClass_eq {R : KnightRealization omegaStage M}
    {R' : KnightRealization omegaStage N} (hR : R.IsModel) (hR' : R'.IsModel)
    (h : hR.codedClass = hR'.codedClass) : Nonempty (R.Iso R') := by
  obtain ⟨e⟩ := @iso_of_codeModel_eq knightLang _ knightSentence M N (structureOf R)
    (structureOf R') _ _ hR.realize_knightSentence hR'.realize_knightSentence h
  exact ⟨⟨@Language.Equiv.toEquiv knightLang M N (structureOf R) (structureOf R') e,
    KnightRealization.IsIso.of_structureOf hR hR' e⟩⟩

/-- **Every coded isomorphism class of countable models of `T` arises** from a countable model
of `S^ω`. -/
theorem KnightRealization.IsModel.codedClass_surjective (q : AllCodedIsoClasses knightSentence) :
    ∃ (M : Type) (_ : Countable M) (R : KnightRealization omegaStage M) (hR : R.IsModel),
      hR.codedClass = q := by
  obtain ⟨M, inst, hcount, hφ, rfl⟩ := codeModel_surjective q
  refine ⟨M, hcount, @toRealization M inst, @isModel_toRealization_of_realize M inst hφ, ?_⟩
  exact @codeModel_eq_of_iso knightLang _ knightSentence M M
    (structureOf (@toRealization M inst)) inst _ _ _ hφ
    ((@realize_knightSentence_iff M inst).mp hφ).structureOfToRealizationEquiv

end Coded

end VaughtConjecture.Knight
