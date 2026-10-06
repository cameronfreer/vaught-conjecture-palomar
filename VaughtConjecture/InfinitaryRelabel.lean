/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import PalomarProof.Infinitary.QuantifierRank

/-! # Relabelling free variables in infinitary formulas

General syntax, satisfaction, and quantifier-rank transport, independent of the
Knight comparison construction. Extracted unchanged from `Knight/SentenceAgreement`.
-/

@[expose] public section

namespace FirstOrder.Language.BoundedFormulaInf

universe u v u' u'' uι w

variable {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {β : Type u''}

/-- Relabelling the free variables of an infinitary formula along `g : α → β`. -/
def relabelFree (g : α → β) : ∀ {n : ℕ}, L.BoundedFormulaInf ι α n → L.BoundedFormulaInf ι β n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (t₁.relabel (Sum.map g id)) (t₂.relabel (Sum.map g id))
  | _, .rel R ts => .rel R fun i => (ts i).relabel (Sum.map g id)
  | _, .imp φ ψ => .imp (relabelFree g φ) (relabelFree g ψ)
  | _, .all φ => .all (relabelFree g φ)
  | _, .iSup φs => .iSup fun i => relabelFree g (φs i)
  | _, .iInf φs => .iInf fun i => relabelFree g (φs i)

variable {M : Type w} [L.Structure M]

/-- Relabelling free variables is realized along the composite valuation. -/
theorem realize_relabelFree (g : α → β) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaInf ι α n) (v : β → M) (xs : Fin n → M),
      (relabelFree g φ).Realize v xs ↔ φ.Realize (v ∘ g) xs := by
  intro n φ
  induction φ with
  | falsum => intro v xs; exact Iff.rfl
  | equal t₁ t₂ =>
    intro v xs
    change (t₁.relabel (Sum.map g id)).realize (Sum.elim v xs) =
        (t₂.relabel (Sum.map g id)).realize (Sum.elim v xs) ↔
      t₁.realize (Sum.elim (v ∘ g) xs) = t₂.realize (Sum.elim (v ∘ g) xs)
    rw [Term.realize_relabel, Term.realize_relabel, Sum.elim_comp_map]
    rfl
  | rel R ts =>
    intro v xs
    change Structure.RelMap R (fun i => ((ts i).relabel (Sum.map g id)).realize (Sum.elim v xs)) ↔
      Structure.RelMap R fun i => (ts i).realize (Sum.elim (v ∘ g) xs)
    simp only [Term.realize_relabel, Sum.elim_comp_map]
    rfl
  | imp φ ψ ihφ ihψ =>
    intro v xs
    exact imp_congr (ihφ v xs) (ihψ v xs)
  | all φ ih =>
    intro v xs
    exact forall_congr' fun y => ih v (Fin.snoc xs y)
  | iSup φs ih =>
    intro v xs
    exact exists_congr fun i => ih i v xs
  | iInf φs ih =>
    intro v xs
    exact forall_congr' fun i => ih i v xs

/-- Relabelling free variables preserves the quantifier rank. -/
theorem qrank_relabelFree (g : α → β) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaInf ι α n), (relabelFree g φ).qrank = φ.qrank := by
  intro n φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ =>
    change max (relabelFree g φ).qrank (relabelFree g ψ).qrank = max φ.qrank ψ.qrank
    rw [ihφ, ihψ]
  | all φ ih =>
    change Order.succ (relabelFree g φ).qrank = Order.succ φ.qrank
    rw [ih]
  | iSup φs ih =>
    change (⨆ i, (relabelFree g (φs i)).qrank) = ⨆ i, (φs i).qrank
    exact iSup_congr ih
  | iInf φs ih =>
    change (⨆ i, (relabelFree g (φs i)).qrank) = ⨆ i, (φs i).qrank
    exact iSup_congr ih

end FirstOrder.Language.BoundedFormulaInf
