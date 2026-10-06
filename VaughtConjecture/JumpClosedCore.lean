/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite

/-! # The topology-free combinatorial core of finite-vector jumps

A jump keeps coordinates at most its natural cutoff and sends the others to
top. Finite-coordinate agreement and escape above one cutoff suffice to
reconstruct a completed vector. These APIs retain their original namespace,
statements, and proofs from `JumpClosed`.
-/

@[expose] public section

namespace VaughtConjecture.JumpClosed

open Filter

variable {I : Type*}

/-- The jump at `K` of a band vector: coordinates at most `K` stay, the others escape to `⊤`. -/
def jump (K : ℕ) (u : I → ℕ∞) : I → ℕ∞ := fun i => if u i ≤ K then u i else ⊤

/-- A vector is `K`-approximated by `u` when `u` agrees with it at its finite coordinates and
strictly exceeds `K` at its infinite ones. -/
def Approximates (K : ℕ) (u r : I → ℕ∞) : Prop :=
  ∀ i, (r i ≠ ⊤ → u i = r i) ∧ (r i = ⊤ → (K : ℕ∞) < u i)

/-- The jump at `K` of a `K`-approximation is the vector itself, once `K` bounds its finite
coordinates. -/
theorem jump_eq_of_approximates {K : ℕ} {u r : I → ℕ∞} (h : Approximates K u r)
    (hK : ∀ i, r i ≠ ⊤ → r i ≤ K) : jump K u = r := by
  funext i
  obtain ⟨h1, h2⟩ := h i
  by_cases hr : r i = ⊤
  · exact (ite_eq_right (not_le.mpr (h2 hr))).trans hr.symm
  · exact (ite_eq_left ((h1 hr).symm ▸ hK i hr)).trans (h1 hr)

variable [Finite I] {A : Set (I → ℕ∞)}

/-- **The combinatorial core**: if a set is closed under the jump at every sufficiently large
threshold, it contains every vector that has a `K`-approximation in it for every `K`. -/
theorem mem_of_approximates (hA : ∀ᶠ K : ℕ in atTop, ∀ u ∈ A, jump K u ∈ A) {r : I → ℕ∞}
    (hr : ∀ K : ℕ, ∃ u ∈ A, Approximates K u r) : r ∈ A := by
  have := Fintype.ofFinite I
  let B : ℕ := Finset.univ.sup fun i => (r i).toNat
  obtain ⟨K, hjump, hBK⟩ := (hA.and (eventually_ge_atTop B)).exists
  obtain ⟨u, hu, hur⟩ := hr K
  refine jump_eq_of_approximates hur (fun i hi => ?_) ▸ hjump u hu
  rw [← ENat.natCast_toNat hi]
  exact Nat.cast_le.mpr ((Finset.le_sup (f := fun i => (r i).toNat) (Finset.mem_univ i)).trans hBK)

omit [Finite I] in
/-- Every vector `K`-approximates itself. -/
theorem approximates_self (K : ℕ) (r : I → ℕ∞) : Approximates K r r :=
  fun _ => ⟨fun _ => rfl, fun h => h ▸ ENat.natCast_lt_top K⟩

end VaughtConjecture.JumpClosed
