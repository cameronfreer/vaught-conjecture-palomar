/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # Finite-tuple slots and the disjoint-band injection

The proof that Knight's top system `S^{ω₁}` has no countable model uses only
two facts, neither specific to Knight's cells:

* a carrier `M` has only `max ℵ₀ #M` *slots* — pairs of an injective finite
  tuple and a countable amount of per-tuple data (a cell of the realized type);
* if pairwise disjoint value bands `band j` (`j : J`) each require a witnessing
  slot whose value lies in that band, the witnesses are distinct, so `#J ≤ #slots`.

Together: `#J ≤ max ℵ₀ #M`.  At level `ω₁` Uniformity supplies `ℵ₁` disjoint bands,
so every model is uncountable (no separate infinitude argument is needed).  (Knight-VC analogue: the level-specific
no-countable-top theorem; see `docs/DESIGN.md`, experiment A1.) -/

@[expose] public section

namespace VaughtConjecture

open Cardinal

universe u v w w'

/-- Distinct pairwise-disjoint bands have distinct witnesses. -/
theorem injective_witness_of_pairwise_disjoint {J S V : Type*} {band : J → Set V}
    (hdisj : Pairwise fun i j => Disjoint (band i) (band j)) {value : S → V} {w : J → S}
    (hw : ∀ j, value (w j) ∈ band j) : Function.Injective w := by
  intro i j hij
  by_contra hne
  have hi : value (w i) ∈ band i := hw i
  have hj : value (w i) ∈ band j := hij ▸ hw j
  exact Set.disjoint_left.mp (hdisj hne) hi hj

/-- A family of pairwise-disjoint bands, each realized by a witness, injects into the witnesses. -/
theorem lift_mk_le_of_pairwise_disjoint_bands {J : Type u} {S : Type v} {V : Type w}
    {band : J → Set V} (hdisj : Pairwise fun i j => Disjoint (band i) (band j))
    {value : S → V} {w : J → S} (hw : ∀ j, value (w j) ∈ band j) :
    lift.{v} #J ≤ lift.{u} #S :=
  lift_mk_le'.mpr ⟨⟨w, injective_witness_of_pairwise_disjoint hdisj hw⟩⟩

/-- A carrier `M` has at most `max ℵ₀ #M` injective `n`-tuples. -/
theorem mk_embedding_fin_le (M : Type u) (n : ℕ) : #(Fin n ↪ M) ≤ max ℵ₀ #M := by
  rcases lt_or_ge #M ℵ₀ with hM | hM
  · have : Finite M := lt_aleph0_iff_finite.mp hM
    exact (lt_aleph0_of_finite _).le.trans (le_max_left _ _)
  · calc #(Fin n ↪ M) ≤ #(Fin n → M) := mk_embedding_le_arrow _ _
      _ = #M ^ (n : Cardinal) := by simp
      _ ≤ #M := pow_le hM (lt_aleph0.mpr ⟨n, rfl⟩)
      _ ≤ max ℵ₀ #M := le_max_right _ _

/-- **Slot bound.**  The slots `Σ n, Σ t : Fin n ↪ M, F n t` with countably many data per tuple
number at most `max ℵ₀ #M`. -/
theorem mk_sigma_slot_le (M : Type u) (F : ∀ n : ℕ, (Fin n ↪ M) → Type w)
    (hF : ∀ n t, #(F n t) ≤ ℵ₀) :
    #(Σ n : ℕ, Σ t : Fin n ↪ M, F n t) ≤ lift.{w} (max ℵ₀ #M) := by
  have hinner : ∀ n : ℕ, #(Σ t : Fin n ↪ M, F n t) ≤ lift.{w} (max ℵ₀ #M) := by
    intro n
    calc #(Σ t : Fin n ↪ M, F n t) = sum fun t => #(F n t) := mk_sigma _
      _ ≤ lift.{w} #(Fin n ↪ M) * ⨆ t, lift.{u} #(F n t) := sum_le_lift_mk_mul_iSup_lift _
      _ ≤ lift.{w} (max ℵ₀ #M) * ℵ₀ :=
          mul_le_mul' (lift_le.mpr (mk_embedding_fin_le M n))
            (ciSup_le' fun t => lift_le_aleph0.mpr (hF n t))
      _ = lift.{w} (max ℵ₀ #M) := by
          rw [mul_eq_left (by simp) (by simp) aleph0_ne_zero]
  calc #(Σ n : ℕ, Σ t : Fin n ↪ M, F n t) = sum fun n => #(Σ t : Fin n ↪ M, F n t) := mk_sigma _
    _ ≤ lift.{max u w} #ℕ * ⨆ n, #(Σ t : Fin n ↪ M, F n t) := sum_le_lift_mk_mul_iSup _
    _ ≤ ℵ₀ * lift.{w} (max ℵ₀ #M) := by
        rw [mk_nat, lift_aleph0]
        exact mul_le_mul' le_rfl (ciSup_le' hinner)
    _ = lift.{w} (max ℵ₀ #M) := by
        rw [mul_eq_right (by simp) (by simp) aleph0_ne_zero]

/-- **Cardinal Uniformity obstruction.**  If pairwise-disjoint bands indexed by `J` are each
witnessed by a slot over a carrier `M`, then `#J ≤ max ℵ₀ #M`. -/
theorem lift_mk_le_max_aleph0_carrier_of_pairwise_disjoint_bands {J : Type v} {V : Type w'}
    (M : Type u) (F : ∀ n : ℕ, (Fin n ↪ M) → Type w) (hF : ∀ n t, #(F n t) ≤ ℵ₀)
    {band : J → Set V} (hdisj : Pairwise fun i j => Disjoint (band i) (band j))
    {value : (Σ n : ℕ, Σ t : Fin n ↪ M, F n t) → V}
    {w : J → Σ n : ℕ, Σ t : Fin n ↪ M, F n t} (hw : ∀ j, value (w j) ∈ band j) :
    lift.{max u w} #J ≤ lift.{max v w} (max ℵ₀ #M) := by
  have h1 := lift_mk_le_of_pairwise_disjoint_bands hdisj hw
  have h2 := lift_le.{v}.mpr (mk_sigma_slot_le M F hF)
  rw [lift_lift] at h2
  exact h1.trans h2

/-- The obstruction with the witnesses chosen internally: if every band is realized by *some*
slot, then `#J ≤ max ℵ₀ #M`. -/
theorem lift_mk_le_max_aleph0_carrier_of_forall_exists_slot {J : Type v} {V : Type w'}
    (M : Type u) (F : ∀ n : ℕ, (Fin n ↪ M) → Type w) (hF : ∀ n t, #(F n t) ≤ ℵ₀)
    {band : J → Set V} (hdisj : Pairwise fun i j => Disjoint (band i) (band j))
    (value : (Σ n : ℕ, Σ t : Fin n ↪ M, F n t) → V)
    (hex : ∀ j, ∃ s, value s ∈ band j) :
    lift.{max u w} #J ≤ lift.{max v w} (max ℵ₀ #M) := by
  choose w hw using hex
  exact lift_mk_le_max_aleph0_carrier_of_pairwise_disjoint_bands M F hF hdisj (value := value) hw

end VaughtConjecture
