/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionDomainBF

/-! # Homogeneous expansion domains at the sentence's own rank

Sentence agreement is read from the domain's projected back-and-forth comparison,
with no extra `ω`-factor in the budget. The old one-block interface is unchanged.
These statements use expansion existence directly, not stopping ranks, and
terminal countability is needed only to count the exceptional classes.
-/

@[expose] public section

namespace VaughtConjecture.Knight.ExpansionDomain

open TypeTower FirstOrder Language KnightRealization StoppingRankFiltration

/-- Membership in the expansion domain at `η` suffices for agreement on all
sentences of quantifier rank at most `η`. -/
theorem realizes_iff_of_mem_domain_uniform (φ : knightLang.Sentenceω)
    {η : Ordinal.{0}} (hφ : φ.qrank ≤ η) {q s : Classes}
    (hq : q ∈ domain η) (hs : s ∈ domain η) : realizes φ q ↔ realizes φ s := by
  revert hq hs
  refine Quotient.inductionOn₂ q s fun R S hq hs => ?_
  have key := @BFEquiv_implies_agreeQR knightLang ℕ inferInstance ℕ ℕ
    (structureOf R.1) (structureOf S.1) η 0 Fin.elim0 Fin.elim0
    (bfEquiv_of_mem_domain hq hs)
    (φ.relabelFree (Empty.elim : Empty → Fin 0))
    (by rw [BoundedFormulaInf.qrank_relabelFree]; exact hφ)
  have he : (Fin.elim0 : Fin 0 → ℕ) ∘ (Empty.elim : Empty → Fin 0) = Empty.elim :=
    funext fun e => e.elim
  simp only [FormulaInf.Realize, BoundedFormulaInf.realize_relabelFree, he] at key
  exact key

/-- Every sentence has a countable truth side; its own rank is the comparison
threshold. No eventual-departure hypothesis is needed. -/
theorem sentence_split_countable_uniform (hct : CountableTerminalFibres)
    (φ : knightLang.Sentenceω) :
    ({q : Classes | realizes φ q} : Set Classes).Countable ∨
      ({q : Classes | ¬ realizes φ q} : Set Classes).Countable := by
  have hc := compl_countable hct (qrank_lt_ord_aleph_one φ)
  by_cases h : ∃ q ∈ domain φ.qrank, realizes φ q
  · obtain ⟨q₀, hq₀, hr⟩ := h
    exact Or.inr (Set.Countable.mono (fun s hs hsd =>
      hs ((realizes_iff_of_mem_domain_uniform φ le_rfl hsd hq₀).mpr hr)) hc)
  · exact Or.inl (Set.Countable.mono (fun q hq hqd => h ⟨q, hqd, hq⟩) hc)

end VaughtConjecture.Knight.ExpansionDomain
