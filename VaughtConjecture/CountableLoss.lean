/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.OrdinalCountability
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Regular

/-! # Countable successor losses and limit continuity give countable complements

A family of sets `D ξ` indexed by countable ordinals, starting at everything, losing only
countably many points at each successor step, and continuous at countable limits (the
intersection of the earlier sets is contained in the limit set), has a countable complement
at every countable index (`compl_countable_of_loss`).  The proof is transfinite induction:
the complement at `ξ + 1` is contained in the complement at `ξ` together with the successor
loss, and the complement at a limit is contained in the countable union of the earlier
complements (inclusions, not equalities: no monotonicity is assumed).

**Exact cardinality** (`mk_eq_aleph_one_of_domains`) needs more: decreasing domains whose
countable-index complements are countable, all nonempty below `ω₁`, and which every point
eventually leaves, exhaust a space of cardinality exactly `ℵ₁`.  Every point lies in some
countable-index complement (at most `ℵ₁ · ℵ₀` points), and a countable space would leave all
its points before one countable index, emptying that domain.  No rank function and no
canonical representatives are chosen.  Nothing here is construction-specific. -/

@[expose] public section

namespace VaughtConjecture.CountableLoss

open Cardinal Set

universe u

/-- The ordinals below a countable ordinal form a countable set. -/
theorem countable_Iio {l : Ordinal.{0}} (hl : l < (aleph 1).ord) : (Set.Iio l).Countable := by
  apply InfinitaryLogic.setCountable_Iio_of_lt_omega1
  simpa only [Cardinal.ord_aleph] using hl

/-- **Countable successor losses and limit continuity give countable complements.** -/
theorem compl_countable_of_loss {X : Type u} (D : Ordinal.{0} → Set X) (h0 : D 0 = Set.univ)
    (hsucc : ∀ ξ, ξ < (aleph 1).ord → (D ξ \ D (ξ + 1)).Countable)
    (hlim : ∀ l, Order.IsSuccLimit l → l < (aleph 1).ord → (⋂ ξ < l, D ξ) ⊆ D l) :
    ∀ β, β < (aleph 1).ord → (D β)ᶜ.Countable := by
  rw [Cardinal.ord_aleph] at hsucc hlim ⊢
  exact InfinitaryLogic.compl_countable_of_loss D h0 hsucc hlim

/-! ## Exact cardinality from decreasing domains

The space is taken in `Type 1`, where the counted quotients live; the ordinal indices are in
`Ordinal.{0}`.  A universe-polymorphic version would only add cardinal lifts. -/

/-- The ordinals below `ω₁` form a set of cardinality `ℵ₁`. -/
theorem mk_Iio_ord_aleph_one : #(Set.Iio (aleph 1).ord) = aleph 1 := by
  rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord, Cardinal.lift_aleph, Ordinal.lift_one]

/-- **At most `ℵ₁` points**: every point lies in the countable complement of some domain of
countable index. -/
theorem mk_le_aleph_one_of_domains {X : Type 1} (D : Ordinal.{0} → Set X)
    (hcompl : ∀ β, β < (aleph 1).ord → (D β)ᶜ.Countable)
    (hleave : ∀ x, ∃ β, β < (aleph 1).ord ∧ x ∉ D β) : #X ≤ aleph 1 := by
  choose β hβ hxβ using hleave
  let f : X → Σ b : Set.Iio (aleph 1).ord, ((D b.1)ᶜ : Set X) :=
    fun x => ⟨⟨β x, hβ x⟩, ⟨x, hxβ x⟩⟩
  have hf : Function.Injective f := fun x y hxy =>
    congrArg (fun z : Σ b : Set.Iio (aleph 1).ord, ((D b.1)ᶜ : Set X) => z.2.1) hxy
  calc #X ≤ #(Σ b : Set.Iio (aleph 1).ord, ((D b.1)ᶜ : Set X)) :=
        Cardinal.mk_le_of_injective hf
    _ = Cardinal.sum fun b : Set.Iio (aleph 1).ord => #((D b.1)ᶜ : Set X) :=
        Cardinal.mk_sigma _
    _ ≤ Cardinal.sum fun _ : Set.Iio (aleph 1).ord => aleph 1 :=
        Cardinal.sum_le_sum _ _ fun b =>
          (Cardinal.le_aleph0_iff_set_countable.mpr (hcompl b.1 b.2)).trans
            aleph0_lt_aleph_one.le
    _ = #(Set.Iio (aleph 1).ord) * aleph 1 := Cardinal.sum_const' _ _
    _ = aleph 1 := by
        rw [mk_Iio_ord_aleph_one]
        simp only [Cardinal.aleph_mul_aleph, max_self]

/-- **At least `ℵ₁` points**: a countable space would leave all its points before one
countable index, emptying that domain. -/
theorem aleph_one_le_of_domains {X : Type 1} (D : Ordinal.{0} → Set X) (hanti : Antitone D)
    (hne : ∀ β, β < (aleph 1).ord → (D β).Nonempty)
    (hleave : ∀ x, ∃ β, β < (aleph 1).ord ∧ x ∉ D β) : aleph 1 ≤ #X := by
  by_contra h
  have hX : #X ≤ Cardinal.aleph0 := Cardinal.lt_aleph_one_iff.mp (not_le.mp h)
  have hcount : Countable X := Cardinal.mk_le_aleph0_iff.mp hX
  obtain ⟨x₀, -⟩ := hne 0 (Cardinal.isSuccLimit_ord (aleph0_le_aleph 1)).pos
  have : Nonempty X := ⟨x₀⟩
  obtain ⟨e, he⟩ := exists_surjective_nat X
  choose β hβ hxβ using hleave
  have hsup : iSup (β ∘ e) < (aleph 1).ord :=
    Ordinal.iSup_lt_of_lt_cof
      (by rw [Cardinal.mk_nat, Cardinal.isRegular_aleph_one.cof_ord]; exact aleph0_lt_aleph_one)
      fun n => hβ (e n)
  obtain ⟨x, hx⟩ := hne _ hsup
  obtain ⟨n, rfl⟩ := he x
  have hbdd : BddAbove (Set.range (β ∘ e)) :=
    ⟨(aleph 1).ord, by rintro _ ⟨m, rfl⟩; exact (hβ (e m)).le⟩
  exact hxβ (e n) (hanti (le_ciSup hbdd n) hx)

/-- **Exact cardinality `ℵ₁`** from decreasing domains: countable complements at countable
indices, nonempty domains below `ω₁`, and eventual departure of every point.  No rank
function and no canonical representatives are chosen. -/
theorem mk_eq_aleph_one_of_domains {X : Type 1} (D : Ordinal.{0} → Set X) (hanti : Antitone D)
    (hcompl : ∀ β, β < (aleph 1).ord → (D β)ᶜ.Countable)
    (hne : ∀ β, β < (aleph 1).ord → (D β).Nonempty)
    (hleave : ∀ x, ∃ β, β < (aleph 1).ord ∧ x ∉ D β) : #X = aleph 1 := by
  rw [Cardinal.ord_aleph] at hcompl hne hleave
  exact InfinitaryLogic.mk_eq_aleph_one_of_domains D hanti hcompl hne hleave

end VaughtConjecture.CountableLoss
