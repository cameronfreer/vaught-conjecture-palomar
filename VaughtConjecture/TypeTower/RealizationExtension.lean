/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.TypeTower.Basic

/-! # Extension of partial realizations

Preservation of defined evaluations, without chains, request enumeration, or modelhood. -/

@[expose] public section

namespace VaughtConjecture.TypeTower.Realization

universe u v w
variable {Λ : Type v} [Preorder Λ] {T : TypeTower.{u} Λ} {α : Λ} {M : Type w}

/-- Preservation of every defined evaluation. -/
def Extends (A B : T.Realization α M) : Prop :=
  ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : T.Ty α n), A.eval t = some p → B.eval t = some p

theorem Extends.refl (A : T.Realization α M) : A.Extends A := fun _ _ _ h => h

theorem Extends.trans {A B C : T.Realization α M} (h : A.Extends B) (h' : B.Extends C) :
    A.Extends C := fun _ t p hp => h' t p (h t p hp)

end VaughtConjecture.TypeTower.Realization
