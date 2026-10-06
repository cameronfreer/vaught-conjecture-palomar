/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model

/-! # Modelhood transports along a bijection of carriers (#46 probe, prerequisite; #73 audit)

`TypeTower/Basic.lean` (#111) transports the two consistency predicates and the two covering
predicates of a realization along an isomorphism of carriers (`IsIso.isExactParentConsistent`,
…), and shows that a realization isomorphic to `R` *is* a push-forward `R.map e`
(`IsIso.map_eq`).  What was missing — named by the #73 audit, and the prerequisite of the #46
bounded limit probe — is the same transport for the four existential-closure clauses of
Def. 3.2.1, i.e. for full modelhood: `KnightRealization.IsModel.map`.

Each clause is an existential over tuples and points of the carrier whose stage-type content
(family membership, the coface equation) does not mention the carrier at all, so the witnesses
push through `e : M ≃ N` verbatim: the tuple `t` of `N` pulls back to `t ∘ e⁻¹`, the clause at
`R` produces `y ∉ range (t ∘ e⁻¹)` and a stage type `q`, and `e y ∉ range t` realizes the same
`q` over `t` in `R.map e` (`RealizesSome.map`, from the concatenation identity
`snoc_trans_symm`: `(t⌢(e y)) ∘ e⁻¹ = (t ∘ e⁻¹)⌢y`).

Consequence (stated as `isModelClass_map` / `prolongsToIn_isModelClass_iff_on` in
`Knight/ProlongationNormalization.lean`, where the target class `IsModelClass` lives): the
model class is closed under push-forward, so by `prolongsToIn_iff_prolongsToOnIn` every certified link
`ProlongsToIn IsModel` normalizes to Knight's literal Def. 5.1.1 shape — an actual model **on
the carrier of the source** whose reduct **equals** the source. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w w'

namespace KnightRealization

variable {α : LimitStage} {M : Type w} {N : Type w'} {n : ℕ}

/-- If `y` avoids the pulled-back tuple `t ∘ e⁻¹`, then `e y` avoids `t`. -/
theorem not_mem_range_trans_of_not_mem {e : M ≃ N} {t : Fin n ↪ N} {y : M}
    (hy : y ∉ Set.range (t.trans e.symm.toEmbedding)) : e y ∉ Set.range t := by
  rintro ⟨i, hi⟩
  exact hy ⟨i, by simp [Function.Embedding.trans_apply, hi]⟩

/-- Concatenation commutes with pulling back along `e⁻¹`:
`(t⌢(e y)) ∘ e⁻¹ = (t ∘ e⁻¹)⌢y`. -/
theorem snoc_trans_symm (e : M ≃ N) (t : Fin n ↪ N) {y : M}
    (hy : y ∉ Set.range (t.trans e.symm.toEmbedding)) :
    (snoc t (e y) (not_mem_range_trans_of_not_mem hy)).trans e.symm.toEmbedding =
      snoc (t.trans e.symm.toEmbedding) y hy := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/-- **Realized families push forward along a bijection of carriers**: if `R` realizes some
member of `U` over the pulled-back tuple `t ∘ e⁻¹` as a coface of `p`, then `R.map e` realizes
the same member over `t`.  The stage-type data (`q ∈ U`, `IsCoface p q`) is untouched: only
the witnesses move, through `e`. -/
theorem RealizesSome.map {R : KnightRealization α M} (e : M ≃ N) {t : Fin n ↪ N}
    {p : S α.1 n} {U : Set (S α.1 (n + 1))}
    (h : R.RealizesSome (t.trans e.symm.toEmbedding) p U) :
    RealizesSome (R.map e) t p U := by
  obtain ⟨y, hy, q, hqU, hqc, hq⟩ := h
  refine ⟨e y, not_mem_range_trans_of_not_mem hy, q, hqU, hqc, ?_⟩
  rw [Realization.map_eval, snoc_trans_symm e t hy, hq]

/-- **Modelhood transports along a bijection of carriers** (the missing lemma of the #73
audit; the prerequisite of the #46 limit probe): the push-forward `R.map e` of a model is a
model.  Clauses (2)/(3) are the generic #111 transports; the four existential-closure clauses
push their witnesses through `e` (`RealizesSome.map`). -/
theorem IsModel.map {R : KnightRealization α M} (h : R.IsModel) (e : M ≃ N) :
    IsModel (R.map e) where
  nonempty := h.nonempty.map e
  consistent :=
    Realization.IsIso.isExactParentConsistent (Realization.isIso_map e R) h.consistent
  covering :=
    Realization.IsIso.isInitialSegmentCovering (Realization.isIso_map e R) h.covering
  genSat t p hp D hD := by
    rw [Realization.map_eval] at hp
    exact (h.genSat _ p hp D hD).map e
  bottomPattern t p hp D hD q' hq' hext := by
    rw [Realization.map_eval] at hp
    exact (h.bottomPattern _ p hp D hD q' hq' hext).map e
  uniformity t p hp γ hγ hγα := by
    rw [Realization.map_eval] at hp
    exact (h.uniformity _ p hp γ hγ hγα).map e
  highGradeDominance t p hp γ hγα := by
    rw [Realization.map_eval] at hp
    exact (h.highGradeDominance _ p hp γ hγα).map e

/-- Modelhood transports along any isomorphism of realizations (`IsIso.map_eq`: an isomorphic
realization *is* a push-forward). -/
theorem IsIso.isModel {R : KnightRealization α M} {R' : KnightRealization α N} {e : M ≃ N}
    (hi : R.IsIso R' e) (h : R.IsModel) : IsModel R' :=
  hi.map_eq ▸ h.map e

/-- Modelhood of the push-forward is modelhood (`map_symm_map`). -/
theorem isModel_map_iff {R : KnightRealization α M} (e : M ≃ N) :
    IsModel (R.map e) ↔ R.IsModel :=
  ⟨fun h => Realization.map_symm_map e R ▸ h.map e.symm, fun h => h.map e⟩

end KnightRealization

end VaughtConjecture.Knight
