/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteCoverReceivingCore
public import VaughtConjecture.Knight.OrdinaryFiniteCutReceiving
public import VaughtConjecture.Knight.BlockCode

/-! # Finite-cover receiving for models

Compatibility entry point. The construction in `FiniteCoverReceivingCore` uses
only exact consistency and finite-cut receiving. These old modelhood endpoints
specialize it using the constructed ordinary receiver.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FiniteCoverReceiving
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CellScheme.restrictFace
universe w
variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

theorem receive_cover_at_cap (hM : R.IsModel) {γ : ExtOrd} (hγbot : ⊥ < γ)
    (hγα : γ < ofOrd α.1) (r : ℕ) :
    ∀ {n m : ℕ} (Q : S α.1 m), SelfVis m γ → ∀ (f : Fin n ↪ Fin m), n + r = m →
      ∀ (t : Fin n ↪ M) (p : S α.1 n), typeMap f Q = some p → R.eval t = some p →
        ∃ (u : Fin m ↪ M) (Q' : S α.1 m), f.trans u = t ∧ R.eval u = some Q' ∧
          ∃ h : Q'.scheme = Q.scheme,
            ∀ d, min (Q'.label d) γ = min (Q.label (SemScheme.castCell h d)) γ :=
  receive_cover_at_cap_of_receiving hM.consistent
    (OrdinaryModelReceiving.finiteCutReceiving hM) hγbot hγα r

theorem finiteCoverReceiving (hM : R.IsModel) {n m : ℕ} (Q : S α.1 m) (f : Fin n ↪ Fin m)
    (t : Fin n ↪ M) (p : S α.1 n) (hp : typeMap f Q = some p) (ht : R.eval t = some p)
    (δ : ExtOrd) (hδbot : ⊥ < δ) (hδα : δ < ofOrd α.1) :
    ∃ (u : Fin m ↪ M) (Q' : S α.1 m), f.trans u = t ∧ R.eval u = some Q' ∧
      ∃ h : Q'.scheme = Q.scheme,
        ∀ d, min (Q'.label d) δ = min (Q.label (SemScheme.castCell h d)) δ :=
  finiteCoverReceiving_of_receiving hM.consistent
    (OrdinaryModelReceiving.finiteCutReceiving hM) Q f t p hp ht δ hδbot hδα

end VaughtConjecture.Knight.FiniteCoverReceiving
