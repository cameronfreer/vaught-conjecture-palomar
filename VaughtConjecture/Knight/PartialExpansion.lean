/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionIsomorphism

/-! # Expansion as a unique partial operation

The domain is the existing literal, same-carrier model-expansion predicate. On that domain,
reduct injectivity makes any chosen witness unique. Reduction gives downward domain closure
and coherent values; transport along a specified isomorphism retains its underlying bijection.
Nothing here produces a limit expansion or lifts an arbitrary embedding.
-/

@[expose] public section

namespace VaughtConjecture.Knight.PartialExpansion

open TypeTower KnightRealization

universe w w'
variable {M : Type w} {N : Type w'} {σ τ ρ : Ordinal.{0}}

/-- Realizations admitting an actual model expansion on the same carrier. -/
abbrev Domain (h : σ ≤ ρ) (M : Type w) :=
  {R : KnightRealization (blockStage σ) M //
    R.ProlongsToOnIn IsModelClass (blockStage_mono h)}

/-- Expansion is only defined on its existence domain. -/
noncomputable def value (h : σ ≤ ρ) (R : Domain h M) : KnightRealization (blockStage ρ) M :=
  R.2.choose

theorem isModel (h : σ ≤ ρ) (R : Domain h M) : (value h R).IsModel :=
  R.2.choose_spec.1

@[simp] theorem reduct_value (h : σ ≤ ρ) (R : Domain h M) :
    (value h R).reduct (blockStage_mono h) = R.1 :=
  R.2.choose_spec.2

/-- Independence from the particular expansion witness, not merely from its existence proof. -/
theorem value_eq (h : σ ≤ ρ) (R : Domain h M)
    {W : KnightRealization (blockStage ρ) M} (hW : W.IsModel)
    (hWR : W.reduct (blockStage_mono h) = R.1) : value h R = W :=
  eq_of_reduct_eq_of_le ρ σ h _ _ (isModel h R) hW ((reduct_value h R).trans hWR.symm)

/-- Different witnesses for membership in the same domain give exactly the same expansion. -/
theorem value_eq_of_base_eq (h : σ ≤ ρ) {R S : Domain h M} (hRS : R.1 = S.1) :
    value h R = value h S := by
  exact congrArg (value h) (Subtype.ext hRS)

/-- An expansion to a higher block supplies one at every intermediate block. -/
theorem downward (hστ : σ ≤ τ) (hτρ : τ ≤ ρ)
    {R : KnightRealization (blockStage σ) M}
    (hR : R.ProlongsToOnIn IsModelClass (blockStage_mono (hστ.trans hτρ))) :
    R.ProlongsToOnIn IsModelClass (blockStage_mono hστ) := by
  obtain ⟨W, hW, hWR⟩ := hR
  exact ⟨W.reduct (blockStage_mono hτρ), hW.reduct _, by
    rw [Realization.reduct_reduct]; exact hWR⟩

/-- Independently supplied existence proofs at two heights produce coherent values. -/
theorem coherent (hστ : σ ≤ τ) (hτρ : τ ≤ ρ)
    (R : Domain (hστ.trans hτρ) M) (S : Domain hστ M) (hRS : R.1 = S.1) :
    (value (hστ.trans hτρ) R).reduct (blockStage_mono hτρ) = value hστ S := by
  apply (value_eq hστ S ((isModel _ R).reduct _) ?_).symm
  rw [Realization.reduct_reduct, reduct_value, hRS]

/-- The higher expansion also exists over the canonical intermediate value. -/
theorem above (hστ : σ ≤ τ) (hτρ : τ ≤ ρ) (R : Domain (hστ.trans hτρ) M) :
    (value hστ ⟨R.1, downward hστ hτρ R.2⟩).ProlongsToOnIn IsModelClass
      (blockStage_mono hτρ) :=
  ⟨value _ R, isModel _ R, coherent hστ hτρ R _ rfl⟩

/-- Expanding in two steps agrees with the one-step partial operation. -/
theorem value_trans (hστ : σ ≤ τ) (hτρ : τ ≤ ρ) (R : Domain (hστ.trans hτρ) M) :
    value hτρ ⟨value hστ ⟨R.1, downward hστ hτρ R.2⟩, above hστ hτρ R⟩ =
      value (hστ.trans hτρ) R :=
  value_eq hτρ _ (isModel _ R) (coherent hστ hτρ R _ rfl)

/-- At equal stages the partial operation is the identity on models. -/
theorem value_self (R : KnightRealization (blockStage σ) M) (hR : R.IsModel) :
    value le_rfl ⟨R, ⟨R, hR, Realization.reduct_refl R⟩⟩ = R :=
  value_eq le_rfl _ hR (Realization.reduct_refl R)

/-- Domain membership transports along the given carrier bijection. -/
theorem map_domain (h : σ ≤ ρ) (R : Domain h M) (e : M ≃ N) :
    (R.1.map e).ProlongsToOnIn IsModelClass (blockStage_mono h) :=
  ⟨(value h R).map e, (isModel h R).map e, by
    rw [Realization.reduct_map, reduct_value]⟩

/-- Naturality is literal equality after push-forward, not a newly chosen isomorphism. -/
theorem value_map (h : σ ≤ ρ) (R : Domain h M) (e : M ≃ N) :
    value h ⟨R.1.map e, map_domain h R e⟩ = (value h R).map e :=
  value_eq h _ ((isModel h R).map e) (by rw [Realization.reduct_map, reduct_value])

/-- The specified isomorphism between bases is the isomorphism between their expansions. -/
theorem isIso_value (h : σ ≤ ρ) (R : Domain h M) (S : Domain h N) (e : M ≃ N)
    (he : R.1.IsIso S.1 e) : (value h R).IsIso (value h S) e := by
  apply isIso_of_reduct_isIso h (isModel h R) (isModel h S)
  rw [reduct_value, reduct_value]
  exact fun {n} t => he (n := n) t

end VaughtConjecture.Knight.PartialExpansion
