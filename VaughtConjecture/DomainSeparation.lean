/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.CountableLoss

/-! # Separation, point tails, persistent cores, and cardinality with a countable core

Generic set-level results about a family of domains `D i` (any index type `I`) and a family of
observations `holds s : Q → Prop` that are eventually homogeneous on the domains.  The first
four are the reviewer's scratch-compiled generic core (2026-09-28, ported with their proofs
unchanged); the last is the cardinality theorem that tolerates a countable persistent core.

* `point_tail_of_isolation`: isolating observations plus homogeneity give **point tails**: for
  every `q` some domain either misses `q` or is `{q}`.
* `no_persistent_of_point_tails`, `exists_failure_of_point_tails`: point tails and cofinal
  successor losses leave no point in every domain (no continuity, countability, or initial
  condition is used).
* `persistent_subsingleton_of_separation`: pairwise separation alone bounds the persistent core
  by one point; it does not empty it.
* `mk_eq_aleph_one_of_countable_core`: decreasing domains indexed by countable ordinals with
  countable complements at countable indices, a countable persistent core, and cofinally many
  nonempty successor losses exhaust a space of cardinality exactly `ℵ₁`.  Eventual departure of
  every point is **not** assumed; the core may be a singleton.

Nothing here mentions ordinals except the last theorem, and nothing is construction-specific. -/

@[expose] public section

namespace VaughtConjecture.DomainSeparation

open Cardinal Set

universe u v w

section Generic

variable {I : Type u} {Q : Type v} {S : Type w}

/-- Isolation plus homogeneous observations gives the pointwise interface actually consumed by
the extinction argument. -/
theorem point_tail_of_isolation
    (D : I → Q → Prop) (holds : S → Q → Prop)
    (isolates : ∀ q : Q, ∃ s : S, ∀ r : Q, holds s r ↔ r = q)
    (homogeneous : ∀ s : S, ∃ i : I,
      ∀ p : Q, D i p → ∀ q : Q, D i q → (holds s p ↔ holds s q)) :
    ∀ q : Q, ∃ i : I, D i q → ∀ r : Q, D i r → r = q := by
  intro q
  obtain ⟨s, hs⟩ := isolates q
  obtain ⟨i, hi⟩ := homogeneous s
  refine ⟨i, ?_⟩
  intro hq r hr
  exact (hs r).mp ((hi q hq r hr).mp ((hs q).mpr rfl))

/-- Cofinal successor losses exclude any point belonging to every domain.  No continuity,
countability, or initial-domain equation is assumed. -/
theorem no_persistent_of_point_tails
    (below : I → I → Prop) (step : I → I) (D : I → Q → Prop)
    (antitone : ∀ i j : I, below i j → ∀ q : Q, D j q → D i q)
    (point_tails : ∀ q : Q, ∃ i : I, D i q → ∀ r : Q, D i r → r = q)
    (cofinal_losses : ∀ i : I, ∃ j : I, below i j ∧
      ∃ r : Q, D j r ∧ ¬ D (step j) r) :
    ∀ q : Q, ¬ (∀ i : I, D i q) := by
  intro q persistent
  obtain ⟨i, hi⟩ := point_tails q
  obtain ⟨j, hij, r, hr, hgone⟩ := cofinal_losses i
  have hrq : r = q := hi (persistent i) r (antitone i j hij r hr)
  apply hgone
  rw [hrq]
  exact persistent (step j)

/-- Classical existence-of-a-failure form; still no stopping rank is defined. -/
theorem exists_failure_of_point_tails
    (below : I → I → Prop) (step : I → I) (D : I → Q → Prop)
    (antitone : ∀ i j : I, below i j → ∀ q : Q, D j q → D i q)
    (point_tails : ∀ q : Q, ∃ i : I, D i q → ∀ r : Q, D i r → r = q)
    (cofinal_losses : ∀ i : I, ∃ j : I, below i j ∧
      ∃ r : Q, D j r ∧ ¬ D (step j) r) :
    ∀ q : Q, ∃ i : I, ¬ D i q := by
  classical
  intro q
  by_contra h
  apply no_persistent_of_point_tails below step D antitone point_tails cofinal_losses q
  intro i
  by_contra hi
  exact h ⟨i, hi⟩

/-- Pairwise separation alone bounds the persistent core by one point.  It does not imply that
this core is empty. -/
theorem persistent_subsingleton_of_separation
    (D : I → Q → Prop) (holds : S → Q → Prop)
    (separates : ∀ p q : Q, p ≠ q → ∃ s : S, ¬ (holds s p ↔ holds s q))
    (homogeneous : ∀ s : S, ∃ i : I,
      ∀ p : Q, D i p → ∀ q : Q, D i q → (holds s p ↔ holds s q))
    (p q : Q) (hp : ∀ i : I, D i p) (hq : ∀ i : I, D i q) : p = q := by
  classical
  by_contra hne
  obtain ⟨s, hs⟩ := separates p q hne
  obtain ⟨i, hi⟩ := homogeneous s
  exact hs (hi p (hp i) q (hq i))

end Generic

/-! ## Cardinality with a countable persistent core -/

/-- A set of countable ordinals that is cofinal in `ω₁` has cardinality `ℵ₁`. -/
theorem aleph_one_le_mk_of_cofinal (T : Set Ordinal.{0}) (hT : ∀ ξ ∈ T, ξ < (aleph 1).ord)
    (hcof : ∀ η, η < (aleph 1).ord → ∃ ξ ∈ T, η ≤ ξ) : aleph 1 ≤ #T := by
  by_contra h
  have hc : #T ≤ ℵ₀ := Cardinal.lt_aleph_one_iff.mp (not_le.mp h)
  have hcount : Countable T := Cardinal.mk_le_aleph0_iff.mp hc
  obtain ⟨ξ₀, hξ₀, -⟩ := hcof 0 (Cardinal.isSuccLimit_ord (aleph0_le_aleph 1)).pos
  have : Nonempty T := ⟨⟨ξ₀, hξ₀⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat T
  have hsup : iSup (fun n => (e n).1) < (aleph 1).ord :=
    Ordinal.iSup_lt_of_lt_cof
      (by rw [Cardinal.mk_nat, Cardinal.isRegular_aleph_one.cof_ord]; exact aleph0_lt_aleph_one)
      fun n => hT _ (e n).2
  have hlim := Cardinal.isSuccLimit_ord (aleph0_le_aleph 1)
  obtain ⟨ξ, hξT, hle⟩ := hcof _ (hlim.succ_lt hsup)
  obtain ⟨n, hn⟩ := he ⟨ξ, hξT⟩
  have hbdd : BddAbove (Set.range fun n => (e n).1) :=
    ⟨(aleph 1).ord, by rintro _ ⟨m, rfl⟩; exact (hT _ (e m).2).le⟩
  have : (e n).1 ≤ iSup fun n => (e n).1 := le_ciSup hbdd n
  rw [hn] at this
  exact absurd (hle.trans this) (not_le.mpr (Order.lt_succ _))

/-- **Exact cardinality with a countable persistent core.**  Decreasing domains, countable
complements at countable indices, a countable persistent core, and cofinally many nonempty
successor losses below `ω₁` give `#X = ℵ₁`.  No point is required to leave. -/
theorem mk_eq_aleph_one_of_countable_core {X : Type 1} (D : Ordinal.{0} → Set X)
    (hanti : Antitone D)
    (hcompl : ∀ β, β < (aleph 1).ord → (D β)ᶜ.Countable)
    (hcore : (⋂ β < (aleph 1).ord, D β).Countable)
    (hloss : ∀ η, η < (aleph 1).ord → ∃ ξ, η ≤ ξ ∧ ξ < (aleph 1).ord ∧
      (D ξ \ D (ξ + 1)).Nonempty) :
    #X = aleph 1 := by
  apply le_antisymm
  · -- every point is in the core or leaves some countable-index domain
    have hcov : (Set.univ : Set X) = (⋂ β < (aleph 1).ord, D β) ∪
        ⋃ β ∈ Set.Iio (aleph 1).ord, (D β)ᶜ := by
      ext x
      simp only [Set.mem_univ, true_iff, Set.mem_union, Set.mem_iInter, Set.mem_iUnion,
        Set.mem_compl_iff, Set.mem_Iio]
      by_cases h : ∀ β < (aleph 1).ord, x ∈ D β
      · exact Or.inl h
      · push Not at h
        obtain ⟨β, hβ, hx⟩ := h
        exact Or.inr ⟨β, hβ, hx⟩
    have hcount : (Set.univ : Set X).Countable ∨ True := Or.inr trivial
    calc #X = #(Set.univ : Set X) := Cardinal.mk_univ.symm
      _ ≤ #((⋂ β < (aleph 1).ord, D β) ∪ ⋃ β ∈ Set.Iio (aleph 1).ord, (D β)ᶜ : Set X) := by
          rw [hcov]
      _ ≤ #(⋂ β < (aleph 1).ord, D β : Set X) +
          #(⋃ β ∈ Set.Iio (aleph 1).ord, (D β)ᶜ : Set X) := Cardinal.mk_union_le _ _
      _ ≤ aleph 1 + aleph 1 := by
          gcongr
          · exact (Cardinal.le_aleph0_iff_set_countable.mpr hcore).trans aleph0_lt_aleph_one.le
          · calc #(⋃ β ∈ Set.Iio (aleph 1).ord, (D β)ᶜ : Set X)
                ≤ #(Set.Iio (aleph 1).ord) * ⨆ β : Set.Iio (aleph 1).ord, #((D β.1)ᶜ : Set X) :=
                  Cardinal.mk_biUnion_le _ _
              _ ≤ aleph 1 * aleph 1 := by
                  rw [CountableLoss.mk_Iio_ord_aleph_one]
                  gcongr
                  exact ciSup_le' fun β =>
                    (Cardinal.le_aleph0_iff_set_countable.mpr (hcompl β.1 β.2)).trans
                      aleph0_lt_aleph_one.le
              _ = aleph 1 := by simp only [Cardinal.aleph_mul_aleph, max_self]
      _ = aleph 1 := by simp only [Cardinal.aleph_add_aleph, max_self]
  · -- one point from each nonempty loss; losses are pairwise disjoint by antitonicity
    classical
    let T : Set Ordinal.{0} := {ξ | ξ < (aleph 1).ord ∧ (D ξ \ D (ξ + 1)).Nonempty}
    have hT : ∀ ξ ∈ T, ξ < (aleph 1).ord := fun _ h => h.1
    have hcof : ∀ η, η < (aleph 1).ord → ∃ ξ ∈ T, η ≤ ξ := fun η hη => by
      obtain ⟨ξ, hηξ, hξ, hne⟩ := hloss η hη
      exact ⟨ξ, ⟨hξ, hne⟩, hηξ⟩
    let pick : T → X := fun ξ => ξ.2.2.some
    have hpick : ∀ ξ : T, pick ξ ∈ D ξ.1 \ D (ξ.1 + 1) := fun ξ => ξ.2.2.some_mem
    have hinj : Function.Injective pick := by
      intro ξ ζ hξζ
      by_contra hne
      rcases lt_or_gt_of_ne (Subtype.coe_ne_coe.mpr hne) with hlt | hlt
      · have h1 : ξ.1 + 1 ≤ ζ.1 := Order.add_one_le_iff.mpr hlt
        exact (hpick ξ).2 (hξζ ▸ hanti h1 (hpick ζ).1)
      · have h1 : ζ.1 + 1 ≤ ξ.1 := Order.add_one_le_iff.mpr hlt
        exact (hpick ζ).2 (hξζ.symm ▸ hanti h1 (hpick ξ).1)
    exact (aleph_one_le_mk_of_cofinal T hT hcof).trans (Cardinal.mk_le_of_injective hinj)

end VaughtConjecture.DomainSeparation
