/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ConstructedTerminalLoss

/-! # Terminal witnesses from exact top-free extension

This file isolates what the capped scheduler of `TopFreeCapHenkin` is used for. A
realization is a *top-free extension realization* when it is exactly consistent,
initial-segment covering, has no top label on any defined tuple, and realizes every
top-free one-point donor over a realized root exactly, over that same literal root.

Proved here, with the existing statements unchanged:

* finite-cut receiving, with its capped agreement, at every proper cutoff
  (`IsTopFreeExtension.finiteCutReceiving`);
* modelhood (`IsTopFreeExtension.isModel`);
* the terminal-witness conclusion of `TopFreeCapHenkin.exists_terminal_model`
  (`exists_terminal_model_of_isTopFreeExtension`) and the nonempty successor losses of
  `ExpansionDomain.loss_nonempty` (`loss_nonempty_of_isTopFreeExtension`).

Capped agreement enters only through the existing top-free pinned extension, applied
with the realized root as its own master. The existence of a top-free extension
realization is not proved in this file; it is a hypothesis of the last two theorems.
It is proved in `TopFreeExtensionExistence` from the shared finite-master scheduler.
-/

@[expose] public section

namespace VaughtConjecture.Knight
open TypeTower StageType KnightRealization Value ExtOrd FixedHeight
universe w
variable {β : LimitStage} {M : Type w}

namespace KnightRealization

/-- A **top-free extension realization**: exact consistency, initial-segment covering,
no top label on a defined tuple, and exact realization of every top-free one-point donor
over the literal realized root. No cutoff occurs in this definition. -/
structure IsTopFreeExtension (R : KnightRealization β M) : Prop where
  /-- Exact parent consistency (model clause (2)). -/
  consistent : R.IsExactParentConsistent
  /-- Initial-segment covering (model clause (3)). -/
  covering : R.IsInitialSegmentCovering
  /-- Every defined label is top-free. -/
  topFree : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S β.1 n), R.eval t = some p →
    ∀ d, p.label d ≠ ⊤
  /-- Exact top-free donor extension over the literal root `t`. -/
  extension : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S β.1 n), R.eval t = some p →
    ∀ q : S β.1 (n + 1), IsCoface p q → (∀ d, q.label d ≠ ⊤) →
      ∃ (y : M) (hy : y ∉ Set.range t), R.eval (snoc t y hy) = some q

namespace IsTopFreeExtension

variable {R : KnightRealization β M}

/-- Extending the identity face is the identity on a concatenation. -/
theorem extendFace_refl_trans_snoc {n : ℕ} (t : Fin n ↪ M) {y : M}
    (hy : y ∉ Set.range t) :
    (extendFace (Function.Embedding.refl (Fin n))).trans (snoc t y hy) = snoc t y hy := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [snoc]
  | cast i => simp [snoc]

/-- **Finite-cut receiving** (proved). A donor over a realized root, possibly with top
labels, is first replaced by a top-free coface with the same scheme and the same labels
below the cutoff; that coface is then realized exactly over the same literal root. -/
theorem finiteCutReceiving (h : R.IsTopFreeExtension) : FiniteCutReceiving R := by
  intro n t p hp P hP δ hδ hδβ
  -- The pinned extension accepts every cutoff below the stage, including bottom.
  clear hδ
  obtain ⟨Q, hQp, hQtop, q, hq, he, hcap⟩ := TopFreePinnedExtension.exists_pinned p
    (h.topFree t p hp) (Function.Embedding.refl _) p (typeMap_refl p) P hP δ hδβ
  obtain ⟨y, hy, hyQ⟩ := h.extension t p hp Q hQp hQtop
  refine ⟨y, hy, q, ?_, he, hcap⟩
  have hface := h.consistent (snoc t y hy) Q (extendFace (Function.Embedding.refl _)) hyQ
  rw [extendFace_refl_trans_snoc] at hface
  exact hface.trans hq

/-- The carrier is nonempty (proved): the empty tuple is covered by a realized tuple, and
some top-free coface of its label is realized over it. -/
theorem nonempty (h : R.IsTopFreeExtension) : Nonempty M := by
  obtain ⟨k, s, _, hs⟩ := h.covering (Function.Embedding.ofIsEmpty : Fin 0 ↪ M)
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨q, _, hq⟩ :=
    exists_highGrade_coface (CanonicalCoatomSupply.supply β.2) P 0 β.2.pos
  obtain ⟨Q, hQ, hQtop, _⟩ := TopFreePinnedExtension.exists_pinned P (h.topFree s P hP)
    (Function.Embedding.refl _) P (typeMap_refl P) q hq ⊥ (bot_lt_ofOrd _)
  obtain ⟨y, _⟩ := h.extension s P hP Q hQ hQtop
  exact ⟨y⟩

/-- **Modelhood** (proved), through the existing finite-cut receiving criterion. -/
theorem isModel (h : R.IsTopFreeExtension) : R.IsModel :=
  FiniteCutReceiving.isModel h.finiteCutReceiving h.nonempty h.consistent h.covering

/-- **Terminality** (proved): no prolongation to a model at any higher limit stage. -/
theorem noProlongationToIn (h : R.IsTopFreeExtension) (γ : LimitStage) (hβγ : β < γ) :
    R.NoProlongationToIn IsModelClass hβγ.le :=
  h.isModel.noProlongation_of_topFree hβγ h.topFree

end IsTopFreeExtension
end KnightRealization

/-- The conclusion of `TopFreeCapHenkin.exists_topFree_model` (proved), from a top-free
extension realization instead of the capped scheduler. -/
theorem exists_topFree_model_of_isTopFreeExtension
    (hW : ∃ R : KnightRealization β M, R.IsTopFreeExtension) :
    ∃ R : KnightRealization β M, R.IsModel ∧
      ∀ {n} (t : Fin n ↪ M) (p : S β.1 n), R.eval t = some p → ∀ d, p.label d ≠ ⊤ := by
  obtain ⟨R, hR⟩ := hW
  exact ⟨R, hR.isModel, hR.topFree⟩

/-- The terminal-witness conclusion of `TopFreeCapHenkin.exists_terminal_model` (proved),
verbatim, from a top-free extension realization instead of the capped scheduler. -/
theorem exists_terminal_model_of_isTopFreeExtension
    (hW : ∃ R : KnightRealization β M, R.IsTopFreeExtension) :
    ∃ R : KnightRealization β M, R.IsModel ∧
      ∀ (γ : LimitStage) (hβγ : β < γ), R.NoProlongationToIn IsModelClass hβγ.le := by
  obtain ⟨R, hR⟩ := hW
  exact ⟨R, hR.isModel, hR.noProlongationToIn⟩

namespace ExpansionDomain
open Cardinal StoppingRankFiltration

/-- The nonempty successor losses of `loss_nonempty` (proved), from top-free extension
realizations on `ℕ` at every countable block stage. Their existence is a hypothesis here. -/
theorem loss_nonempty_of_isTopFreeExtension
    (hW : ∀ ξ : Ordinal.{0}, ξ < (aleph 1).ord →
      ∃ R : KnightRealization (blockStage ξ) ℕ, R.IsTopFreeExtension)
    {ξ : Ordinal.{0}} (hξ : ξ < (aleph 1).ord) :
    (domain ξ \ domain (ξ + 1)).Nonempty := by
  obtain ⟨W, hW, hterm⟩ := exists_terminal_model_of_isTopFreeExtension (hW ξ hξ)
  exact ⟨_, terminalModel_mem_loss ⟨W, hW,
    hterm _ (blockStage_strictMono (Order.lt_add_one_iff.mpr le_rfl))⟩⟩

end ExpansionDomain
end VaughtConjecture.Knight
