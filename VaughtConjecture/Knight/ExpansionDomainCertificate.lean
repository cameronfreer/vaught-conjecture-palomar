/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionDomainUniform
public import VaughtConjecture.Knight.ClassScottDefinitions
public import VaughtConjecture.FiltrationCertificate

/-! # Construction receipts for the generic filtration certificate

The domains are expansion domains. Terminal classification supplies countable losses; local
terminal models supply cofinal nonempty losses (both left explicit here). Limit expansion
supplies continuity, uniform finite-cover comparison supplies agreement at the sentence's own
rank, and ordinary Scott isolation supplies separation. No older one-block producer is added.
-/

@[expose] public section

namespace VaughtConjecture.Knight.ExpansionDomain

open FirstOrder Language Cardinal StoppingRankFiltration

/-- The construction-specific certificate, with both counting producers explicit. -/
def filtrationCertificate (hct : CountableTerminalFibres)
    (hloss : ∀ η, η < (aleph 1).ord → ∃ ξ, η ≤ ξ ∧ ξ < (aleph 1).ord ∧
      (domain ξ \ domain (ξ + 1)).Nonempty) :
    FiltrationCertificate Classes knightLang.Sentenceω realizes where
  domain := domain
  zero := domain_zero
  antitone := domain_antitone
  loss_countable := fun _ h => loss_countable hct h
  limit := fun _ hl h => iInter_subset_domain hl h
  cofinal_losses := hloss
  separates := fun p q hpq => by
    obtain ⟨φ, hφ⟩ := exists_isolating_sentence p
    exact ⟨φ, fun h => hpq (((hφ q).mp (h.mp ((hφ p).mpr rfl))).symm)⟩
  homogeneous := fun φ =>
    ⟨φ.qrank, qrank_lt_ord_aleph_one φ,
      fun _ hp _ hq => realizes_iff_of_mem_domain_uniform φ le_rfl hp hq⟩

end VaughtConjecture.Knight.ExpansionDomain
