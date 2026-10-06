/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Spectrum.BFBoundednessThinness
public import VaughtConjecture.Knight.ExpansionDomainBF

/-! # Direct boundedness thinness from expansion-domain comparison

Countable terminal fibres and uniform comparison give countable empty-tuple BF
quotients. Analytic BF separation then excludes a perfect antichain directly.
Neither sentence splits, sentence recovery, global termination, nor nonempty
losses are needed. The receiving producer imports are inherited; this module
claims proof-dependency separation, not a wholly descriptive-free import cone.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ExpansionDomain

open FirstOrder Language Cardinal StoppingRankFiltration

/-- Direct thinness from countable BF quotients, with terminal counting explicit.
No lower bound, nonempty domain, or Borel presentation of the model set is needed. -/
theorem isThinOnNatModels_of_bfBoundedness (hct : CountableTerminalFibres) :
    knightSentence.IsThinOnNatModels := by
  apply Spectrum.isThinOn_of_countable_bfObservations (ModelsOf knightSentence)
    (fun η => Quotient.mk (bfEquivSetoid knightSentence η))
  · intro η hη
    have : Countable (Quotient (bfEquivSetoid knightSentence η)) :=
      mk_le_aleph0_iff.mp (mk_bfEquivSetoid_quotient_le_aleph0 hct (by rwa [ord_aleph]))
    exact Set.to_countable _
  · intro η _ c d h
    exact Quotient.exact h

end VaughtConjecture.Knight.ExpansionDomain
