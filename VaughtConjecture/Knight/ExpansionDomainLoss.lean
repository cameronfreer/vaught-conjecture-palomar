/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionDomain
public import VaughtConjecture.Knight.ExpansionInjectivity

/-! # Terminal models are precisely the successor losses

`ExpansionDomain.loss_subset_range` assigns a terminal model to a class lost at a
successor. The converse uses uniqueness of expansions: a later expansion of the
base class would, after same-carrier normalization, reduce to the given terminal
model. Neither direction requires global termination or a canonical stopping
expansion. In particular terminal models can supply nonempty losses independently
of the theorem counting terminal classes.
-/

@[expose] public section

namespace VaughtConjecture.Knight.ExpansionDomain

open TypeTower KnightRealization Cardinal StoppingRankFiltration

/-- The counted base of a terminal model reduces back to its block-zero reduct. -/
theorem terminal_atBlockZero {ξ : Ordinal.{0}} (W : TerminalModel ξ) :
    W.toNatModel.atBlockZero = W.1.reduct (blockStage_zero_le ξ) := by
  change (liftBlockZero (W.1.reduct (blockStage_zero_le ξ))).reduct
    blockStage_zero_le_omegaStage = _
  unfold liftBlockZero
  rw [Realization.reduct_reduct, Realization.reduct_refl]

/-- A terminal model's counted base is lost exactly at the next block. This is
the direction of the correspondence that uses injectivity of reduction. -/
theorem terminalModel_mem_loss {ξ : Ordinal.{0}} (W : TerminalModel ξ) :
    Quotient.mk knightModelSetoid W.toNatModel ∈ domain ξ \ domain (ξ + 1) := by
  refine ⟨mem_domain_of_model W.2.1 (terminal_atBlockZero W).symm, ?_⟩
  intro hnext
  obtain ⟨V, hV, hVr⟩ := exists_model_of_mem_domain hnext
  apply W.2.2
  apply Realization.ProlongsToOnIn.prolongsToIn
  refine ⟨V, hV, eq_of_reduct_eq_of_le ξ 0 zero_le _ _ (hV.reduct _) W.2.1 ?_⟩
  rw [Realization.reduct_reduct, hVr, terminal_atBlockZero W]

/-- Every terminal class maps into the corresponding successor loss. -/
theorem range_subset_loss (ξ : Ordinal.{0}) :
    Set.range (terminalToClass ξ) ⊆ domain ξ \ domain (ξ + 1) := by
  rintro q ⟨t, rfl⟩
  refine Quotient.inductionOn t fun W => ?_
  exact terminalModel_mem_loss W

/-- The successor loss equals the image of the terminal classes at that block.
No assertion that all classes eventually belong to such an image is needed. -/
theorem loss_eq_range (ξ : Ordinal.{0}) :
    domain ξ \ domain (ξ + 1) = Set.range (terminalToClass ξ) :=
  Set.Subset.antisymm (loss_subset_range ξ) (range_subset_loss ξ)

end VaughtConjecture.Knight.ExpansionDomain
