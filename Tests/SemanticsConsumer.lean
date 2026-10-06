/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Lomega1omega.Semantics

/-!
# Imported infinitary syntax and semantics smoke tests

These checks use only the public interface re-exported by the converted semantics
facade. They exercise imported definitions, constructor patterns, scoped notation,
realization aliases and the historical explicit argument order.
-/

public section

open FirstOrder.Language
open scoped Lomega1omega FirstOrder.Language.Sentenceω

universe u v w u'

namespace Tests.SemanticsConsumer

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]
variable {α : Type u'} {n : ℕ}

example : L.BoundedFormulaω α n = L.BoundedFormulaInf ℕ α n := rfl

example (φ : L.BoundedFormulaω α n) : L.BoundedFormulaInf ℕ α n := φ

example (φ : L.BoundedFormulaInf ℕ α n) : L.BoundedFormulaω α n := φ

example (L : FirstOrder.Language.{u, v}) (α : Type u') (n : ℕ) :
    Type max u v u' := L.BoundedFormulaω α n

example : L.Formulaω α = L.BoundedFormulaω α 0 := rfl

example : L.Sentenceω = L.Formulaω Empty := rfl

example (φ ψ : L.BoundedFormulaω α n) :
    (φ ⟹ω ψ) = BoundedFormulaω.imp φ ψ := rfl

example (φ ψ : L.BoundedFormulaω α n) :
    φ.and ψ = (φ.imp ψ.not).not := rfl

example (φ : L.BoundedFormulaω α n) : Bool :=
  match φ with
  | BoundedFormulaω.falsum => false
  | BoundedFormulaω.equal _ _ => true
  | BoundedFormulaω.rel _ _ => true
  | BoundedFormulaω.imp _ _ => true
  | BoundedFormulaω.all _ => true
  | BoundedFormulaω.iSup _ => true
  | BoundedFormulaω.iInf _ => true

example (φ : L.BoundedFormulaω α n) : True := by
  induction φ <;> trivial

example (φ ψ : L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    (φ.and ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs :=
  BoundedFormulaω.realize_and φ ψ

example (φ ψ : L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    (φ.and ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp only [BoundedFormulaω.and, BoundedFormulaInf.realize_not,
    BoundedFormulaInf.realize_imp]
  tauto

example (φ : L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    BoundedFormulaω.Realize φ v xs ↔ BoundedFormulaInf.Realize φ v xs := Iff.rfl

example (φ : L.Formulaω α) (v : α → M) :
    Formulaω.Realize φ v ↔ FormulaInf.Realize φ v := Iff.rfl

example (φ : L.Formulaω α) (v : α → M) :
    Formulaω.Realize φ v ↔ BoundedFormulaω.Realize φ v Fin.elim0 := Iff.rfl

example (φ : L.Sentenceω) :
    Sentenceω.Realize φ M ↔ SentenceInf.Realize φ M := Iff.rfl

example (φ : L.Sentenceω) :
    (M ⊨ω φ) ↔
      BoundedFormulaω.Realize φ (Empty.elim : Empty → M) Fin.elim0 := Iff.rfl

example (inst : L.Structure M) (φ : L.BoundedFormulaω α n)
    (v : α → M) (xs : Fin n → M) :
    @BoundedFormulaω.Realize L M inst α n φ v xs ↔
      @BoundedFormulaInf.Realize L ℕ α M inst n φ v xs := Iff.rfl

end Tests.SemanticsConsumer
