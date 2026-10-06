/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.ModelTheory.Semantics
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order
public import Mathlib.Topology.Perfect

/-!
# Independent infinitary model-counting challenge (prototype)

Only the final existential theorem is deliberately unproved. Syntax and semantics below
are the small conventional core of infinitary first-order logic, restated without importing
the fork-only Infinitary modules. Countable branching and finitely many variable slots
give genuine `L_{ω₁,ω}` sentences. No external model predicate is a parameter.
-/

@[expose] public section

universe u v u' uι w

namespace FirstOrder.Language

variable (L : FirstOrder.Language.{u, v})

/-- Well-founded infinitary syntax with a fixed branching carrier. -/
inductive BoundedFormulaInf (ι : Type uι) (α : Type u') : ℕ → Type (max u v u' uι) where
  | falsum {n} : BoundedFormulaInf ι α n
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) : BoundedFormulaInf ι α n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
      BoundedFormulaInf ι α n
  | imp {n} (φ ψ : BoundedFormulaInf ι α n) : BoundedFormulaInf ι α n
  | all {n} (φ : BoundedFormulaInf ι α (n + 1)) : BoundedFormulaInf ι α n
  | iSup {n} (φs : ι → BoundedFormulaInf ι α n) : BoundedFormulaInf ι α n
  | iInf {n} (φs : ι → BoundedFormulaInf ι α n) : BoundedFormulaInf ι α n

/-- Countably branching bounded formulas. -/
abbrev BoundedFormulaω (α : Type u') (n : ℕ) := L.BoundedFormulaInf ℕ α n
/-- Formulas with no available bound-variable slots. -/
abbrev FormulaInf (ι : Type uι) (α : Type u') := L.BoundedFormulaInf ι α 0
/-- Closed infinitary formulas. -/
abbrev SentenceInf (ι : Type uι) := L.FormulaInf ι Empty
/-- `L_{ω₁,ω}` formulas. -/
abbrev Formulaω (α : Type u') := L.BoundedFormulaω α 0
/-- `L_{ω₁,ω}` sentences. -/
abbrev Sentenceω := L.Formulaω Empty

variable {L} {ι : Type uι} {α : Type u'}

/-- Tarskian semantics: quantification extends the valuation at the last slot. -/
def BoundedFormulaInf.Realize {M : Type w} [L.Structure M] :
    ∀ {n}, L.BoundedFormulaInf ι α n → (α → M) → (Fin n → M) → Prop
  | _, .falsum, _, _ => False
  | _, .equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, .rel R ts, v, xs => Structure.RelMap R fun i ↦ (ts i).realize (Sum.elim v xs)
  | _, .imp φ ψ, v, xs => Realize φ v xs → Realize ψ v xs
  | _, .all φ, v, xs => ∀ y : M, Realize φ v (Fin.snoc xs y)
  | _, .iSup φs, v, xs => ∃ i, Realize (φs i) v xs
  | _, .iInf φs, v, xs => ∀ i, Realize (φs i) v xs

/-- Formula satisfaction with a free-variable valuation. -/
def FormulaInf.Realize {M : Type w} [L.Structure M]
    (φ : L.FormulaInf ι α) (v : α → M) : Prop :=
  BoundedFormulaInf.Realize φ v default

/-- Sentence satisfaction in an actual first-order structure. -/
def SentenceInf.Realize (φ : L.SentenceInf ι) (M : Type w) [L.Structure M] : Prop :=
  FormulaInf.Realize (M := M) φ Empty.elim

end FirstOrder.Language

namespace PalomarChallenge

variable (R : ℕ → Type 1)

/-- A purely relational language; there are no function or constant symbols. -/
def language : FirstOrder.Language := ⟨fun _ => Empty, R⟩

instance : (language R).IsRelational := fun _ => (inferInstance : IsEmpty Empty)

/-- A Boolean coordinate for every relation symbol and tuple, including nullary relations. -/
abbrev RelQueryOn (M : Type) := Σ r : (Σ n, R n), (Fin r.1 → M)

/-- Relation truth tables with the ordinary product topology. -/
abbrev Code (M : Type) := RelQueryOn R M → Bool

/-- The conventional space of relational structures on the naturals. -/
abbrev StructureSpace := Code R ℕ

/-- The genuine structure encoded by a relation truth table. -/
@[instance_reducible]
def structureOfCode {M : Type} (c : Code R M) : (language R).Structure M where
  funMap := fun f => isEmptyElim f
  RelMap := fun {n} r xs => c ⟨⟨n, r⟩, xs⟩ = true

/-- Satisfaction of the specified sentence by the specified code. -/
def Satisfies {M : Type} (φ : (language R).Sentenceω) (c : Code R M) : Prop :=
  letI := structureOfCode R c
  FirstOrder.Language.BoundedFormulaInf.Realize (M := M) φ Empty.elim Fin.elim0

/-- The set of sentence models, using the same empty valuations as the conventional coding. -/
def ModelsOf (φ : (language R).Sentenceω) : Set (StructureSpace R) :=
  {c | Satisfies R φ c}

/-- Isomorphism is a permutation preserving every relation coordinate in both directions. -/
def Isomorphic (c d : Code R ℕ) : Prop :=
  ∃ e : ℕ ≃ ℕ, ∀ n (r : R n) (xs : Fin n → ℕ), c ⟨⟨n, r⟩, xs⟩ = d ⟨⟨n, r⟩, e ∘ xs⟩

/-- Isomorphism really is an equivalence relation, without proof holes. -/
theorem isomorphic_equivalence : Equivalence (Isomorphic R) := ⟨
    fun c => ⟨Equiv.refl ℕ, fun _ _ _ => rfl⟩,
    by
      rintro c d ⟨e, h⟩
      refine ⟨e.symm, fun n r xs => ?_⟩
      simpa [Function.comp_def] using (h n r (e.symm ∘ xs)).symm,
    by
      rintro c d f ⟨e, h⟩ ⟨e', h'⟩
      exact ⟨e.trans e', fun n r xs => (h n r xs).trans (h' n r (e ∘ xs))⟩⟩

/-- The equivalence relation used in the quotient. -/
def isoSetoid : Setoid (Code R ℕ) := ⟨Isomorphic R, isomorphic_equivalence R⟩

/-- Codes on `ℕ` satisfying the sentence. -/
abbrev NatModel (φ : (language R).Sentenceω) := {c : Code R ℕ // Satisfies R φ c}

/-- Restriction of permutation isomorphism to the models. -/
def modelSetoid (φ : (language R).Sentenceω) : Setoid (NatModel R φ) :=
  Setoid.comap Subtype.val (isoSetoid R)

/-- The type of isomorphism classes, rather than a chosen set of representatives. -/
abbrev IsoClasses (φ : (language R).Sentenceω) := Quotient (modelSetoid R φ)

/-- Excludes every finite carrier, including the empty one. -/
def NoFiniteModels (φ : (language R).Sentenceω) : Prop :=
  ∀ n (c : Code R (Fin n)), ¬ Satisfies R φ c

/-- No nonempty perfect set of models is an isomorphism antichain in the product topology. -/
def NoPerfectAntichain (φ : (language R).Sentenceω) : Prop :=
  ¬ ∃ P : Set (StructureSpace R), P.Nonempty ∧ Perfect P ∧
    (∀ c ∈ P, Satisfies R φ c) ∧
      ∀ c ∈ P, ∀ d ∈ P, c ≠ d → ¬ Isomorphic R c d

/-- Prototype challenge: a countable relational `L_{ω₁,ω}` sentence with exactly `ℵ₁`
countably infinite isomorphism types, no finite models, and no nonempty perfect antichain.
The sole authorized proof hole is here; this file does not establish the existence claim. -/
theorem independent_challenge :
    ∃ (R : ℕ → Type 1) (_ : Countable (Σ n, R n)) (φ : (language R).Sentenceω),
      Cardinal.mk (IsoClasses R φ) = Cardinal.aleph 1 ∧
      NoFiniteModels R φ ∧ NoPerfectAntichain R φ := by
  sorry

end PalomarChallenge
