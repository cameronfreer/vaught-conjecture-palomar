/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.BFScattered

/-! # Thinness from countably many back-and-forth observations

Uniform analytic separation bounds the BF levels needed to distinguish a Cantor
antichain. A countable observation range at that level would then contain an
injection of Cantor space. No sentence recovery, invariant separation, or
measurability of the ambient class or its observation maps is needed.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Spectrum

open FirstOrder Language MeasureTheory Set

universe u v w
variable {L : Language.{u, v}} [L.IsRelational]

/-- Countable observations give countable BF quotients; observations need not descend to
the quotient. Choose one representative per BF class and use observation equality only
in the direction that implies BF equivalence. -/
theorem bfScattered_of_countable_bfObservations (C : Set (StructureSpace L))
    {Q : Ordinal.{0} → Type w} (obs : ∀ η, C → Q η)
    (hc : ∀ η < Ordinal.omega 1, (range (obs η)).Countable)
    (hobs : ∀ η < Ordinal.omega 1, ∀ c d : C,
    obs η c = obs η d → CodeBFEquiv η c.1 d.1) : BFScattered C :=
  FirstOrder.Language.bfScattered_of_countable_bfObservations C obs hc hobs

/-- Countably many observations determining empty-tuple BF equivalence at each
countable level rule out a Cantor antichain. The observations need not be measurable. -/
theorem no_cantorAntichain_of_countable_bfObservations (C : Set (StructureSpace L))
    {Q : Ordinal.{0} → Type w} (obs : ∀ η, C → Q η)
    (hc : ∀ η < Ordinal.omega 1, (range (obs η)).Countable)
    (hobs : ∀ η < Ordinal.omega 1, ∀ c d : C,
      obs η c = obs η d → CodeBFEquiv η c.1 d.1) :
    ¬ HasCantorAntichainOn (structureIsoSetoid L) C :=
  FirstOrder.Language.not_hasCantorAntichainOn_of_countable_bfObservations C obs hc hobs

/-- Thinness follows from countable BF-determining observations. Countability of
the signature is used only to obtain a Cantor antichain from a perfect one. -/
theorem isThinOn_of_countable_bfObservations [Countable (Σ n, L.Relations n)]
    (C : Set (StructureSpace L)) {Q : Ordinal.{0} → Type w} (obs : ∀ η, C → Q η)
    (hc : ∀ η < Ordinal.omega 1, (range (obs η)).Countable)
    (hobs : ∀ η < Ordinal.omega 1, ∀ c d : C,
      obs η c = obs η d → CodeBFEquiv η c.1 d.1) :
    IsThinOn (structureIsoSetoid L) C :=
  FirstOrder.Language.isThinOn_of_countable_bfObservations C obs hc hobs

end VaughtConjecture.Spectrum
