/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Closure

/-!
# Closure from an intersection-closed cofinal family of finite sets

Adapted from the newsimple14 canonical-hulls draft.
No infinite intersection or countability is used.
The predicate is deliberately unbundled: both plan faces and actual supports
use the same least-element lemma.
-/

@[expose] public section

namespace VaughtConjecture.FiniteSupportClosure

variable {M : Type*} [DecidableEq M]

/-- A nonempty collection of finite supersets, closed under binary intersection,
has a least member.  Only existence above this particular `S` is required. -/
theorem exists_least (P : Finset M → Prop)
    (hinter : ∀ A B, P A → P B → P (A ∩ B)) (S : Finset M)
    (hcover : ∃ A, P A ∧ S ⊆ A) :
    ∃ A, P A ∧ S ⊆ A ∧ ∀ B, P B → S ⊆ B → A ⊆ B := by
  classical
  have hex : ∃ n : ℕ, ∃ A : Finset M, P A ∧ S ⊆ A ∧ A.card = n := by
    obtain ⟨A, hA, hSA⟩ := hcover
    exact ⟨A.card, A, hA, hSA, rfl⟩
  obtain ⟨A, hA, hSA, hcard⟩ := Nat.find_spec hex
  refine ⟨A, hA, hSA, ?_⟩
  intro B hB hSB
  have hSAB : S ⊆ A ∩ B := fun x hx =>
    Finset.mem_inter.mpr ⟨hSA hx, hSB hx⟩
  have hle : A.card ≤ (A ∩ B).card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨A ∩ B, hinter A B hA hB, hSAB, rfl⟩
  have heq : A ∩ B = A :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left hle
  rw [← heq]
  exact Finset.inter_subset_right

noncomputable def hull (P : Finset M → Prop)
    (hinter : ∀ A B, P A → P B → P (A ∩ B))
    (hcover : ∀ S, ∃ A, P A ∧ S ⊆ A) (S : Finset M) : Finset M :=
  Classical.choose (exists_least P hinter S (hcover S))

theorem hull_spec (P : Finset M → Prop)
    (hinter : ∀ A B, P A → P B → P (A ∩ B))
    (hcover : ∀ S, ∃ A, P A ∧ S ⊆ A) (S : Finset M) :
    P (hull P hinter hcover S) ∧ S ⊆ hull P hinter hcover S ∧
      ∀ B, P B → S ⊆ B → hull P hinter hcover S ⊆ B :=
  Classical.choose_spec (exists_least P hinter S (hcover S))

/-- The usual closure operator. `IsClosed` is definitionally the original
predicate, rather than a second presentation of closedness. -/
noncomputable def ofCofinalInterClosed (P : Finset M → Prop)
    (hinter : ∀ A B, P A → P B → P (A ∩ B))
    (hcover : ∀ S, ∃ A, P A ∧ S ⊆ A) : ClosureOperator (Finset M) :=
  ClosureOperator.ofPred (hull P hinter hcover) P
    (fun S => (hull_spec P hinter hcover S).2.1)
    (fun S => (hull_spec P hinter hcover S).1)
    (fun S B hSB hB => (hull_spec P hinter hcover S).2.2 B hB hSB)

@[simp] theorem ofCofinalInterClosed_isClosed (P : Finset M → Prop)
    (hinter : ∀ A B, P A → P B → P (A ∩ B))
    (hcover : ∀ S, ∃ A, P A ∧ S ⊆ A) (S : Finset M) :
    (ofCofinalInterClosed P hinter hcover).IsClosed S ↔ P S := Iff.rfl

end VaughtConjecture.FiniteSupportClosure
