/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionDomainLoss
public import VaughtConjecture.Knight.TopFreeCapHenkin

/-! # Nonempty losses and the lower spectrum bound without global termination

The top-free capped scheduler constructs a terminal model at every countable
block. Unique expansion puts its base class in that block's successor loss.
These losses are disjoint, so choosing one class in each injects the countable
ordinals into the counted classes. No classification or global termination is
used to produce these witnesses or obtain the lower cardinal bound.
-/

@[expose] public section

namespace VaughtConjecture.Knight.ExpansionDomain

open TypeTower KnightRealization Cardinal StoppingRankFiltration

/-- Every countable block has a nonempty successor loss, supplied by a locally
constructed top-free terminal model. This includes block zero. -/
theorem loss_nonempty {ξ : Ordinal.{0}} (hξ : ξ < (aleph 1).ord) :
    (domain ξ \ domain (ξ + 1)).Nonempty := by
  obtain ⟨W, hW, hterm⟩ := TopFreeCapHenkin.exists_terminal_model
    (β := blockStage ξ) (M := ℕ)
    (Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_ord.mp (blockLevel_lt_ord_aleph_one hξ)))
  exact ⟨_, terminalModel_mem_loss ⟨W, hW,
    hterm _ (blockStage_strictMono (Order.lt_add_one_iff.mpr le_rfl))⟩⟩

/-- In particular successor losses are cofinally nonempty below `ω₁`. -/
theorem cofinal_losses (η : Ordinal.{0}) (hη : η < (aleph 1).ord) :
    ∃ ξ, η ≤ ξ ∧ ξ < (aleph 1).ord ∧ (domain ξ \ domain (ξ + 1)).Nonempty :=
  ⟨η, le_rfl, hη, loss_nonempty hη⟩

/-- The lower bound comes from disjoint successor losses, not from a stopping
rank or a theorem asserting that every class eventually departs. -/
theorem aleph_one_le_classes : aleph 1 ≤ #Classes := by
  classical
  choose q hq using fun ξ : Set.Iio (aleph 1).ord => loss_nonempty ξ.2
  have hinj : Function.Injective q := by
    intro ξ η heq
    apply Subtype.ext
    apply le_antisymm
    · by_contra hle
      exact (hq η).2 (domain_antitone (Order.add_one_le_of_lt (lt_of_not_ge hle))
        (heq ▸ (hq ξ).1))
    · by_contra hle
      exact (hq ξ).2 (domain_antitone (Order.add_one_le_of_lt (lt_of_not_ge hle))
        (heq.symm ▸ (hq η).1))
  simpa only [CountableLoss.mk_Iio_ord_aleph_one] using Cardinal.mk_le_of_injective hinj

end VaughtConjecture.Knight.ExpansionDomain
