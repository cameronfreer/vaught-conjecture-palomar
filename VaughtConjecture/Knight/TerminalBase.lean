/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SpectrumAssembly
public import VaughtConjecture.Knight.BlockGeometry
public import VaughtConjecture.Knight.NoTop

/-! # Terminal models: the low-level definitions

`TerminalModel`, the terminal setoid and classes, the block-zero lift, and the reduct map to
the counted classes — extracted from `TerminalClassBound.lean` so that the rank spine can
speak about terminal models without the receipt/Zorn cone.  The surjection onto the counted
classes (linked terminal totality) and the spectrum bounds stay behind in
`TerminalClassBound.lean`. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower KnightRealization Cardinal

/-- The terminal models at block `ρ` on `ℕ`. -/
abbrev TerminalModel (ρ : Ordinal.{0}) : Type 1 :=
  {W : KnightRealization (blockStage ρ) ℕ //
    W.IsModel ∧ W.NoProlongationToIn IsModelClass (blockStage_le_succ ρ)}

/-- Terminal models up to isomorphism. -/
noncomputable def terminalSetoid (ρ : Ordinal.{0}) : Setoid (TerminalModel ρ) :=
  (Realization.isoSetoid knightTower (blockStage ρ) ℕ).comap Subtype.val

/-- **The terminal classes at block `ρ`.** -/
abbrev TerminalClass (ρ : Ordinal.{0}) : Type 1 := Quotient (terminalSetoid ρ)

theorem omegaStage_le_blockStage_zero : omegaStage ≤ blockStage 0 :=
  le_of_eq blockStage_zero.symm

/-- Lift a block-`0` realization back to the counted stage (the stages are equal; the
reduct along the equality changes no label). -/
noncomputable def liftBlockZero (W₀ : KnightRealization (blockStage 0) ℕ) :
    KnightRealization omegaStage ℕ :=
  W₀.reduct omegaStage_le_blockStage_zero

theorem liftBlockZero_reduct (R : KnightRealization omegaStage ℕ) :
    liftBlockZero (R.reduct blockStage_zero_le_omegaStage) = R := by
  unfold liftBlockZero
  rw [Realization.reduct_reduct]
  exact Realization.reduct_refl R

/-- The counted model underlying a terminal model: reduct to block `0`, lifted. -/
noncomputable def TerminalModel.toNatModel {ρ : Ordinal.{0}} (W : TerminalModel ρ) :
    KnightNatModel :=
  ⟨liftBlockZero (W.1.reduct (blockStage_zero_le ρ)),
    (W.2.1.reduct (blockStage_zero_le ρ)).reduct omegaStage_le_blockStage_zero⟩

/-- Isomorphic terminal models have isomorphic underlying counted models. -/
theorem TerminalModel.toNatModel_iso {ρ : Ordinal.{0}} {W W' : TerminalModel ρ}
    (h : (terminalSetoid ρ).r W W') : knightModelSetoid.r W.toNatModel W'.toNatModel := by
  obtain ⟨i⟩ := h
  exact ⟨(i.reduct (blockStage_zero_le ρ)).reduct omegaStage_le_blockStage_zero⟩

/-- **Reduct on classes**: the terminal classes at block `ρ` map to the counted classes. -/
noncomputable def terminalToClass (ρ : Ordinal.{0}) :
    TerminalClass ρ → Quotient knightModelSetoid :=
  Quotient.lift (fun W => Quotient.mk knightModelSetoid W.toNatModel)
    (fun _ _ h => Quotient.sound (TerminalModel.toNatModel_iso h))

/-- Stage types are countable at every countable block. -/
theorem countable_S_blockStage {ρ : Ordinal.{0}} (hρ : ρ < (Cardinal.aleph 1).ord) (n : ℕ) :
    Countable (S (blockStage ρ).1 n) :=
  StageType.countable_S
    (Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_ord.mp (blockLevel_lt_ord_aleph_one hρ))) n

/-- Countable models occur at an unbounded set of countable block indices. -/
def CofinalHighStageModels : Prop :=
  ∀ δ : Ordinal.{0}, δ < (Cardinal.aleph 1).ord →
    ∃ β : Ordinal.{0}, δ < β ∧ β < (Cardinal.aleph 1).ord ∧
      ∃ W : KnightRealization (blockStage β) ℕ, W.IsModel

end VaughtConjecture.Knight
