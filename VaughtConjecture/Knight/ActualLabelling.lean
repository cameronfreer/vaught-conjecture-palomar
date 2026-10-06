/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ActualOccurrence

/-! # Lawful, restriction-compatible labels on actual occurrences

The evaluator is not a model and need not have stage-bounded values. Its two
laws concern only actual occurrences of the original realization. In particular,
realizing a legal scheme in that realization does not realize chosen labels.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.KnightRealization
open TypeTower StageType Value ExtOrd
universe w
variable {M : Type w} {α : LimitStage} (W : KnightRealization α M)

/-- An evaluator of actual finite occurrences, with lawful rows and literal face
compatibility. No saturation, modelhood or stage bound is required of the evaluator. -/
structure ActualLabelling where
  label : {n : ℕ} → (Fin n ↪ M) → (p : S α.1 n) → Cell p.scheme.scheme → ExtOrd
  lawful : ∀ {n : ℕ} {u : Fin n ↪ M} {p : S α.1 n}, W.eval u = some p →
    RespectsSemantics p.scheme.rows (label u p)
  mapCell : ∀ {n m : ℕ} {u : Fin n ↪ M} {p : S α.1 n}
    {v : Fin m ↪ M} {q : S α.1 m} (_hv : W.eval v = some q)
    {f : Fin n ↪ Fin m} (_hfu : f.trans v = u) (hpq : typeMap f q = some p)
    (d : Cell p.scheme.scheme), label v q (StageType.mapCell hpq d) = label u p d

/-- The original labels are an evaluator without any model hypothesis. -/
def actualLabelling : W.ActualLabelling where
  label _ p := p.label
  lawful := by intro n u p _; exact p.respects
  mapCell := by intro n m u p v q _ f _ hpq d; exact StageType.label_mapCell hpq d

end VaughtConjecture.Knight.KnightRealization
