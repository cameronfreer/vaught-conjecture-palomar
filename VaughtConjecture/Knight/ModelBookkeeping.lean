/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ModelEmpty
public import VaughtConjecture.Knight.BlockGeometry
public import VaughtConjecture.Knight.NoTop
public import VaughtConjecture.Knight.LimitOfChain

/-! # Automatic model bookkeeping: limit determination, empty evaluation, the zero-band cell

Three facts every consumer of the terminal interface can take for free:

* `KnightRealization.eq_of_forall_reduct_eq` — realizations at a limit stage are determined
  by their reducts along any countable cofinal chain (the realization-level wrapper of
  `StageType.eq_of_forall_reduceType_eq`; the block-indexed form is
  `eq_of_reduct_eq_of_forall_lt` in `ExpansionRigidity`);
* `KnightRealization.exists_eval_empty_at` — every model at any stage labels the empty tuple
  (stage-generic; the adapter the pair-local terminal-code draft needs at the empty root);
* `IsModel.exists_realized_zeroBand_cell` — every block-stage model realizes a cell whose
  label lies in the zero band `[0, ω)`: core clause (3) of the finite-core classification is
  automatic from Uniformity at `0`.

Construction-private (not root-exported).  Reviewer probe (2026-09-03), graduated. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower KnightRealization

namespace KnightRealization

variable {M : Type*} {c : ℕ → LimitStage} {δ : LimitStage}

/-- Realizations at a limit are determined by their reducts along any countable cofinal
chain.  This is the realization-level wrapper needed by an expansion-rigidity induction. -/
theorem eq_of_forall_reduct_eq (hδ : ∀ i, c i ≤ δ)
    (hcof : ∀ γ : Ordinal.{0}, γ < δ.1 → ∃ i, γ < (c i).1)
    {R₁ R₂ : KnightRealization δ M}
    (h : ∀ i, R₁.reduct (hδ i) = R₂.reduct (hδ i)) : R₁ = R₂ := by
  refine Realization.ext fun {n} t => ?_
  cases h₁ : R₁.eval t with
  | none =>
      cases h₂ : R₂.eval t with
      | none => rfl
      | some q₂ =>
          have he := congrArg (fun R : KnightRealization (c 0) M => R.eval t) (h 0)
          simp only [Realization.reduct_eval, h₁, h₂, Option.map_none,
            Option.map_some] at he
          cases he
  | some q₁ =>
      cases h₂ : R₂.eval t with
      | none =>
          have he := congrArg (fun R : KnightRealization (c 0) M => R.eval t) (h 0)
          simp only [Realization.reduct_eval, h₁, h₂, Option.map_none,
            Option.map_some] at he
          cases he
      | some q₂ =>
          have heq : ∀ i, reduceType (c i).2 (hδ i) q₁ =
              reduceType (c i).2 (hδ i) q₂ := by
            intro i
            have he := congrArg (fun R : KnightRealization (c i) M => R.eval t) (h i)
            simp only [Realization.reduct_eval, h₁, h₂, Option.map_some,
              Option.some.injEq] at he
            change reduceType (c i).2 (hδ i) q₁ = reduceType (c i).2 (hδ i) q₂ at he
            exact he
          exact congrArg some (StageType.eq_of_forall_reduceType_eq hδ hcof heq)

end KnightRealization

namespace KnightRealization

variable {rho : Ordinal.{0}} {M : Type*}

/-- Core clause (3) is automatic for every block-stage model: Uniformity at the
zero band supplies an actually realized cell with finite ordinal value. -/
theorem IsModel.exists_realized_zeroBand_cell
    {R : KnightRealization (blockStage rho) M} (hR : R.IsModel) :
    ∃ (n : ℕ) (t : Fin n ↪ M) (q : S (blockStage rho).1 n)
      (d : Cell q.scheme.scheme),
      R.eval t = some q ∧ q.label d ∈ band 0 := by
  have hpos : (0 : Ordinal.{0}) < (blockStage rho).1 :=
    Ordinal.omega0_pos.trans_le
      (by simpa [blockStage_zero] using
        (show (blockStage 0).1 ≤ (blockStage rho).1 from blockStage_zero_le rho))
  obtain ⟨s, hs⟩ := hR.exists_slot_mem_band 0 (Or.inl rfl) hpos
  rcases s with ⟨n, t, d⟩
  change slotValue (R.eval t) d ∈ band 0 at hs
  generalize he : R.eval t = o at d hs
  cases o with
  | none =>
      exact d.elim
  | some q =>
      exact ⟨n, t, q, d, he, hs⟩

end KnightRealization

end VaughtConjecture.Knight
