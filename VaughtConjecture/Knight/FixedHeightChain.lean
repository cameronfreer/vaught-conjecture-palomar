/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FinitePartialState
public import VaughtConjecture.TypeTower.ChainUnion

/-! # Fixed-height chain unions without a request census

Compatibility adapters to the generic union of consistent realizations. No request
alphabet or model-existence theorem is needed. -/

@[expose] public section

namespace VaughtConjecture.Knight
open TypeTower Value ExtOrd
universe w
namespace FixedHeight
open KnightRealization
variable {M : Type w} {β : LimitStage}

section ChainLimit

variable {A : ℕ → KnightRealization β M}

open Classical in
/-- **The ω-union of a chain**: a tuple takes the value it takes at any stage that evaluates
it (well-defined along an `Extends`-chain, `chainLimit_eval_some_iff`). -/
noncomputable def chainLimit (A : ℕ → KnightRealization β M) : KnightRealization β M :=
  Realization.chainUnion A

/-- A value of the union is a value of some stage (no chain hypothesis needed). -/
theorem chainLimit_eval_some_exists {n : ℕ} {t : Fin n ↪ M} {Q : S β.1 n}
    (hQ : (chainLimit A).eval t = some Q) : ∃ k, (A k).eval t = some Q :=
  Realization.chainUnion_eval_some_exists hQ

/-- Extension is transitive along the chain. -/
theorem extends_of_le (hchain : ∀ k, Extends (A k) (A (k + 1))) {j k : ℕ} (hjk : j ≤ k) :
    Extends (A j) (A k) :=
  Realization.extends_of_le hchain hjk

/-- Every stage extends into the union. -/
theorem extends_chainLimit (hchain : ∀ k, Extends (A k) (A (k + 1))) (k : ℕ) :
    Extends (A k) (chainLimit A) :=
  Realization.extends_chainUnion hchain k

/-- The union's value at a tuple is exactly the eventual stage value. -/
theorem chainLimit_eval_some_iff (hchain : ∀ k, Extends (A k) (A (k + 1))) {n : ℕ}
    {t : Fin n ↪ M} {Q : S β.1 n} :
    (chainLimit A).eval t = some Q ↔ ∃ k, (A k).eval t = some Q :=
  ⟨chainLimit_eval_some_exists, fun ⟨k, hk⟩ => extends_chainLimit hchain k t Q hk⟩

/-- **The union of consistent states is consistent**: labels never change along `Extends`,
so a face equation holding at a finite stage holds at every later stage; in particular a
face forced UNDEFINED at a finite stage can never become defined later — the union stays
exactly consistent, with no interpolation. -/
theorem chainLimit_consistent (hchain : ∀ k, Extends (A k) (A (k + 1)))
    (hcons : ∀ k, (A k).IsExactParentConsistent) :
    (chainLimit A).IsExactParentConsistent :=
  Realization.chainUnion_consistent hchain hcons

end ChainLimit

end FixedHeight
end VaughtConjecture.Knight
