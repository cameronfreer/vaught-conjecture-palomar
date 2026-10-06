/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.BlockStages
public import VaughtConjecture.Knight.Model

/-! # The ordinary one-block receiving interface

Exact common upper roots and one-point receiving after one block of reduction.
Logical comparison and descriptive applications are downstream consumers. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower KnightRealization

universe w

/-! ## The hypothesis -/

/-- **One-block readback**: over an exact common labelled root at `blockStage (γ + 1)`, every
realized one-point coface has a receiving one-point coface with the same reduction to
`blockStage γ`. -/
def OneBlockReadback : Prop :=
  ∀ (γ : Ordinal.{0}) {M N : Type w} (W : KnightRealization (blockStage (γ + 1)) M)
    (W' : KnightRealization (blockStage (γ + 1)) N), W.IsModel → W'.IsModel →
    ∀ {n : ℕ} (t : Fin n ↪ M) (t' : Fin n ↪ N) (p : S (blockStage (γ + 1)).1 n),
      W.eval t = some p → W'.eval t' = some p →
      ∀ (y : M) (hy : y ∉ Set.range t) (q : S (blockStage (γ + 1)).1 (n + 1)),
        W.eval (snoc t y hy) = some q →
        ∃ (y' : N) (hy' : y' ∉ Set.range t') (q' : S (blockStage (γ + 1)).1 (n + 1)),
          W'.eval (snoc t' y' hy') = some q' ∧
          reduceType (blockStage γ).2 (blockStage_le_succ γ) q' =
            reduceType (blockStage γ).2 (blockStage_le_succ γ) q

/-- OBR at a stage presented as `blockStage (γ + 1)`. -/
theorem OneBlockReadback.at (h : OneBlockReadback.{w}) (γ : Ordinal.{0}) {δ : LimitStage}
    (hδ : δ = blockStage (γ + 1)) (hγ : blockStage γ ≤ δ) {M N : Type w}
    (W : KnightRealization δ M) (W' : KnightRealization δ N) (hW : W.IsModel) (hW' : W'.IsModel)
    {n : ℕ} (t : Fin n ↪ M) (t' : Fin n ↪ N) (p : S δ.1 n) (ht : W.eval t = some p)
    (ht' : W'.eval t' = some p) (y : M) (hy : y ∉ Set.range t) (q : S δ.1 (n + 1))
    (hq : W.eval (snoc t y hy) = some q) :
    ∃ (y' : N) (hy' : y' ∉ Set.range t') (q' : S δ.1 (n + 1)),
      W'.eval (snoc t' y' hy') = some q' ∧
      reduceType (blockStage γ).2 hγ q' = reduceType (blockStage γ).2 hγ q := by
  subst hδ
  exact h γ W W' hW hW' t t' p ht ht' y hy q hq

end VaughtConjecture.Knight
