/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.DomainSeparation

/-! # A filtration certificate for counting and homogeneous observations

The construction supplies decreasing domains, countable successor losses, limit continuity,
cofinally nonempty losses, and homogeneous observations separating points. Standard countable
loss induction and separation then give cardinality `ℵ₁` and a countable truth side for each
observation. No stopping rank, eventual departure, or descriptive-set dichotomy is assumed.

The class presentation is in `Type 1`, matching the existing cardinality theorem. Observations
may live in any universe. The logic/DST application, including actual-satisfaction readback,
is separate in `Spectrum.FiltrationCertificate`.
-/

@[expose] public section

namespace VaughtConjecture

open Cardinal Set
universe u

/-- Explicit receipts for the generic filtration argument. Homogeneity only needs some
countable threshold per observation; applications may supply its quantifier rank. -/
structure FiltrationCertificate (Q : Type 1) (O : Type u) (truth : O → Q → Prop) where
  domain : Ordinal.{0} → Set Q
  zero : domain 0 = Set.univ
  antitone : Antitone domain
  loss_countable : ∀ ξ, ξ < (aleph 1).ord → (domain ξ \ domain (ξ + 1)).Countable
  limit : ∀ l, Order.IsSuccLimit l → l < (aleph 1).ord → (⋂ ξ < l, domain ξ) ⊆ domain l
  cofinal_losses : ∀ η, η < (aleph 1).ord → ∃ ξ, η ≤ ξ ∧ ξ < (aleph 1).ord ∧
    (domain ξ \ domain (ξ + 1)).Nonempty
  separates : ∀ p q, p ≠ q → ∃ s, ¬ (truth s p ↔ truth s q)
  homogeneous : ∀ s, ∃ ξ, ξ < (aleph 1).ord ∧
    ∀ p ∈ domain ξ, ∀ q ∈ domain ξ, (truth s p ↔ truth s q)

namespace FiltrationCertificate

variable {Q : Type 1} {O : Type u} {truth : O → Q → Prop}
variable (c : FiltrationCertificate Q O truth)

/-- Countable losses accumulate to countable complements below `ω₁`. -/
theorem compl_countable {β : Ordinal.{0}} (hβ : β < (aleph 1).ord) :
    (c.domain β)ᶜ.Countable :=
  CountableLoss.compl_countable_of_loss c.domain c.zero c.loss_countable c.limit β hβ

/-- Separation bounds the persistent core by one point, without proving it empty. -/
theorem persistent_core_countable : (⋂ ξ < (aleph 1).ord, c.domain ξ).Countable := by
  apply Set.Subsingleton.countable
  intro p hp q hq
  exact DomainSeparation.persistent_subsingleton_of_separation
    (fun i : {ξ : Ordinal.{0} // ξ < (aleph 1).ord} => (· ∈ c.domain i.1))
    truth c.separates (fun s => by
      obtain ⟨ξ, hξ, h⟩ := c.homogeneous s
      exact ⟨⟨ξ, hξ⟩, h⟩)
    p q (fun i => Set.mem_iInter₂.mp hp i.1 i.2)
    (fun i => Set.mem_iInter₂.mp hq i.1 i.2)

include c in
/-- Counting uses only the countable persistent core, not eventual departure. -/
theorem cardinality : #Q = aleph 1 :=
  DomainSeparation.mk_eq_aleph_one_of_countable_core c.domain c.antitone
    (fun _ h => c.compl_countable h) c.persistent_core_countable c.cofinal_losses

include c in
/-- Sentence-minimality when observations are sentences: one truth side is countable. -/
theorem countable_truth_side (s : O) :
    ({q | truth s q} : Set Q).Countable ∨ ({q | ¬ truth s q} : Set Q).Countable := by
  obtain ⟨ξ, hξ, hh⟩ := c.homogeneous s
  have hc := c.compl_countable hξ
  by_cases h : ∃ q ∈ c.domain ξ, truth s q
  · obtain ⟨q, hq, ht⟩ := h
    exact Or.inr (hc.mono fun p hp hpd => hp ((hh p hpd q hq).mpr ht))
  · exact Or.inl (hc.mono fun q hq hqd => h ⟨q, hqd, hq⟩)

end FiltrationCertificate
end VaughtConjecture
