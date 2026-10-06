/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.AmbientGradeCharts

/-! # Preserve the output cap, not the old shifter's entire range

A relative lift needs capped prefix agreement only. Clipping the old normalized
witness at a visible output cap gives a canonical representative of that prefix.
A monotone replacement agreeing with the clipped prefix preserves all output caps
as soon as the old shifter reaches the output cap at the source cut. The source
cut and output cap are distinct parameters. No replacement member is constructed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CapFirstScalar

open Transform Value ExtOrd SharpWitnessComposition

/-- The old values above the output cap need not be retained literally. -/
theorem map_cap_agreement_of_capped_prefix {σ τ : ExtOrd → ExtOrd}
    (hσ : Monotone σ) (hτ : Monotone τ) {a x y γ : ExtOrd}
    (hprefix : ∀ z, z ≤ a → min (τ z) γ = min (σ z) γ)
    (hxy : min x a = min y a) (hactive : γ ≤ σ a) :
    min (τ x) γ = min (σ y) γ := by
  have hactive' : γ ≤ τ a := by
    have he := hprefix a le_rfl
    rw [min_eq_right hactive] at he
    exact (min_eq_right_iff.mp he)
  calc
    min (τ x) γ = min (τ (min x a)) γ := by
      rw [hτ.map_min, min_assoc, min_eq_right hactive']
    _ = min (σ (min x a)) γ := hprefix _ (min_le_right _ _)
    _ = min (σ (min y a)) γ := by rw [hxy]
    _ = min (σ y) γ := by
      rw [hσ.map_min, min_assoc, min_eq_right hactive]

/-- Keeping the clipped prefix is a sufficient, constructive form of capped agreement. -/
theorem map_cap_agreement_of_clipped_prefix {σ τ : ExtOrd → ExtOrd}
    (hσ : Monotone σ) (hτ : Monotone τ) {a x y γ : ExtOrd}
    (hprefix : ∀ z, z ≤ a → τ z = min (σ z) γ)
    (hxy : min x a = min y a) (hactive : γ ≤ σ a) :
    min (τ x) γ = min (σ y) γ := by
  apply map_cap_agreement_of_capped_prefix hσ hτ _ hxy hactive
  intro z hz
  rw [hprefix z hz, min_assoc, min_self]

/-- Clipping makes the join value exactly the external cap, even if the old value
at the source cut is larger. The old witness itself need never attain that cap. -/
theorem exists_clipped_prefix {K : ℕ} {σ : ExtOrd → ExtOrd} {a γ : ExtOrd}
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ) (hactive : γ ≤ σ a) :
    ∃ μ : ExtOrd → ExtOrd, Witness (gTop K) μ ∧ μ a = γ ∧
      (∀ x, μ x ≤ γ) ∧ (∀ x, μ x = min (σ x) γ) :=
  ⟨fun x => min (σ x) γ, FreeDiagonal.clip_witness hσ hγ,
    min_eq_right hactive, fun _ => min_le_right _ _, fun _ => rfl⟩

/-- Any faithful tail meeting the clipped prefix at the cap can be attached.
This is scalar interpolation; existence of a tail or a semantic row is not assumed
implicitly. No visibility above the owner's grade is imposed on the source cut. -/
theorem clipped_prefix_splice {K : ℕ} {σ τ : ExtOrd → ExtOrd} {a γ : ExtOrd}
    (hσ : Witness (gTop K) σ) (hτ : Witness (gTop K) τ)
    (ha : SelfVis K a) (hγ : SelfVis K γ) (hactive : γ ≤ σ a) (hta : τ a = γ) :
    Witness (gTop K) (prefixSplice a (fun x => min (σ x) γ) τ) ∧
      (∀ x, x ≤ a → prefixSplice a (fun z => min (σ z) γ) τ x = min (σ x) γ) ∧
      (∀ x, a < x → prefixSplice a (fun z => min (σ z) γ) τ x = τ x) :=
  ⟨prefixSplice_witness (FreeDiagonal.clip_witness hσ hγ) hτ ha
      ((min_eq_right hactive).trans hta.symm),
    fun _ hx => prefixSplice_of_le hx, fun _ hx => prefixSplice_of_gt hx⟩

/-- A positive-cap scalar lift is lawful once its source rows agree at a cut and
its replacement map preserves only the capped prefix. Every actual occurrence
is quantified; neither an off-row floor check nor faithful composition is used. -/
theorem respects_of_capped_prefix
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ}
    {r s q : D.below BJ → ExtOrd} {K : ℕ} {σ τ : ExtOrd → ExtOrd} {a γ : ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) (hq : RespectsSemanticsBelow sem BJ q)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hσ : Monotone σ) (hτ : BoundedMap K τ) (hγ : γ ≠ ⊥)
    (hprefix : ∀ x, x ≤ a → min (τ x) γ = min (σ x) γ)
    (hsource : ∀ d, min (r d) a = min (s d) a) (hactive : γ ≤ σ a)
    (hread : ∀ d, min (σ (s d)) γ = min (q d) γ) :
    RespectsSemanticsBelow sem BJ (fun d => τ (r d)) ∧
      ∀ d, min (τ (r d)) γ = min (q d) γ := by
  have hag d : min (τ (r d)) γ = min (q d) γ :=
    (map_cap_agreement_of_capped_prefix hσ hτ.mono hprefix (hsource d) hactive).trans
      (hread d)
  exact ⟨map_respects_of_positive_cap_agreement hr hq hK hτ hγ hag, hag⟩

end VaughtConjecture.Knight.CapFirstScalar
