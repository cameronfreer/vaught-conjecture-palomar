/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HighLayerBountiful
public import VaughtConjecture.Knight.CanonicalGradeCutSections

/-! # A recursive full-layer inventory over one unchanged proper boundary

Stage n contains the complete old boundary and every controller inventory
at grades 1 through n. Old higher-grade proper owners are never discarded.
This module constructs geometry, not consistent source rows or bountifulness.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.RecursiveSourceCarrier
open Transform Value ExtOrd
open scoped BigOperators
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q : ℕ → Type*) [∀ j, Fintype (Q j)]

def scheme : (n : ℕ) → n ≤ A.card → CellScheme A
  | 0, _ => D
  | n + 1, hn => SourceLayerCarrier.scheme (scheme n (Nat.le_of_succ_le hn))
      (Q (n + 1)) (n + 1) (Nat.succ_pos n) hn

def step (n : ℕ) (hn : n + 1 ≤ A.card) :
    Cell (scheme D Q n (Nat.le_of_succ_le hn)) ↪o Cell (scheme D Q (n + 1) hn) :=
  OrderEmbedding.ofStrictMono
    (fun d => SourceLayerCarrier.toCell (scheme D Q n (Nat.le_of_succ_le hn))
      (Q (n + 1)) (n + 1) (Nat.succ_pos n) hn (.inl d))
    (SourceLayerCarrier.old_order _ _ _ _ _)

theorem step_cell (n : ℕ) (hn : n + 1 ≤ A.card)
    (d : Cell (scheme D Q n (Nat.le_of_succ_le hn))) :
    (scheme D Q (n + 1) hn).cell (step D Q n hn d) =
      (scheme D Q n (Nat.le_of_succ_le hn)).cell d :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)

def embed (m : ℕ) (hm : m ≤ A.card) : (t : ℕ) → (h : m + t ≤ A.card) →
    Cell (scheme D Q m hm) ↪o Cell (scheme D Q (m + t) h)
  | 0, _ => OrderEmbedding.ofStrictMono id strictMono_id
  | t + 1, h => (embed m hm t (by omega)).trans (step D Q (m + t) h)

theorem embed_cell (m : ℕ) (hm : m ≤ A.card) (t : ℕ) (h : m + t ≤ A.card)
    (d : Cell (scheme D Q m hm)) :
    (scheme D Q (m + t) h).cell (embed D Q m hm t h d) = (scheme D Q m hm).cell d := by
  induction t with
  | zero => rfl
  | succ t ih => exact (step_cell D Q (m + t) h _).trans (ih (by omega))

def boundary : (n : ℕ) → (hn : n ≤ A.card) → Cell D ↪o Cell (scheme D Q n hn)
  | 0, _ => OrderEmbedding.ofStrictMono id strictMono_id
  | n + 1, hn => (boundary n (Nat.le_of_succ_le hn)).trans (step D Q n hn)

theorem boundary_cell (n : ℕ) (hn : n ≤ A.card) (d : Cell D) :
    (scheme D Q n hn).cell (boundary D Q n hn d) = D.cell d := by
  induction n with
  | zero => rfl
  | succ n ih => exact (step_cell D Q n hn _).trans (ih (Nat.le_of_succ_le hn))

abbrev controller (n : ℕ) (hn : n + 1 ≤ A.card) (q : Q (n + 1)) :=
  SourceLayerCarrier.controller (scheme D Q n (Nat.le_of_succ_le hn))
    (Q (n + 1)) (n + 1) (Nat.succ_pos n) hn q

theorem controller_cell (n : ℕ) (hn : n + 1 ≤ A.card) (q : Q (n + 1)) :
    (scheme D Q (n + 1) hn).cell (controller D Q n hn q).1 = (A, n + 1) :=
  (controller D Q n hn q).2

/-- A controller remains a distinct actual occurrence at every later stage. -/
def retained (n t : ℕ) (h : n + 1 + t ≤ A.card) (q : Q (n + 1)) :
    Cell (scheme D Q (n + 1 + t) h) :=
  embed D Q (n + 1) (by omega) t h (controller D Q n (by omega) q).1

theorem retained_cell (n t : ℕ) (h : n + 1 + t ≤ A.card) (q : Q (n + 1)) :
    (scheme D Q (n + 1 + t) h).cell (retained D Q n t h q) = (A, n + 1) :=
  (embed_cell D Q (n + 1) (by omega) t h _).trans (controller_cell D Q n (by omega) q)

theorem classify (n : ℕ) (hn : n ≤ A.card) (d : Cell (scheme D Q n hn)) :
    (∃ c : Cell D, boundary D Q n hn c = d) ∨
      ∃ j, 0 < j ∧ j ≤ n ∧ (scheme D Q n hn).cell d = (A, j) := by
  induction n with
  | zero => exact Or.inl ⟨d, rfl⟩
  | succ n ih =>
    obtain ⟨x, rfl⟩ := (SourceLayerCarrier.enumeration
      (scheme D Q n (Nat.le_of_succ_le hn)) (Q (n + 1)) (n + 1) (Nat.succ_pos n) hn).surjective d
    cases x with
    | inl d =>
      rcases ih (Nat.le_of_succ_le hn) d with ⟨c, hc⟩ | ⟨j, hj, hjn, hd⟩
      · exact Or.inl ⟨c, congrArg (step D Q n hn) hc⟩
      · exact Or.inr ⟨j, hj, hjn.trans (Nat.le_succ n), (step_cell D Q n hn d).trans hd⟩
    | inr q => exact Or.inr ⟨n + 1, Nat.succ_pos n, le_rfl, controller_cell D Q n hn q⟩

theorem full_grade (hp : ∀ d : Cell D, D.scope d ≠ A)
    (n : ℕ) (hn : n ≤ A.card) (d : Cell (scheme D Q n hn))
    (hd : (scheme D Q n hn).scope d = A) : (scheme D Q n hn).grade d ≤ n := by
  rcases classify D Q n hn d with ⟨c, rfl⟩ | ⟨j, _, hj, he⟩
  · exact (hp c ((congrArg Prod.fst (boundary_cell D Q n hn c)).symm.trans hd)).elim
  · change ((scheme D Q n hn).cell d).2 ≤ n
    rw [he]
    exact hj

/-- Proper old owners may be higher than the next layer. Separation comes
from their scope, not an incorrect whole-predecessor grade bound. -/
theorem separated (hp : ∀ d : Cell D, D.scope d ≠ A)
    (n : ℕ) (hn : n ≤ A.card) (d : Cell (scheme D Q n hn)) :
    ¬ GradedLe (A, n + 1) ((scheme D Q n hn).cell d) := by
  intro h
  have hs : (scheme D Q n hn).scope d = A := Finset.Subset.antisymm
    ((scheme D Q n hn).isPlan.subset_of_mem ((scheme D Q n hn).scope_mem_plan d)) h.1
  exact (Nat.not_succ_le_self n) (h.2.trans (full_grade D Q hp n hn d hs))

def properEquiv (n : ℕ) (hn : n ≤ A.card) (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) :
    D.below J ≃ (scheme D Q n hn).below J :=
  Equiv.ofBijective (fun d => ⟨boundary D Q n hn d.1, by
    rw [boundary_cell]; exact d.2⟩) ⟨by
      intro a b he
      exact Subtype.ext ((boundary D Q n hn).injective (congrArg Subtype.val he)), by
      intro d
      rcases classify D Q n hn d.1 with ⟨c, hc⟩ | ⟨j, _, _, hj⟩
      · refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
        simpa only [← hc, boundary_cell] using d.2
      · exact (hJ (by simpa only [hj] using d.2.1)).elim⟩

def belowEquiv (m : ℕ) (hm : m ≤ A.card) : (t : ℕ) → (h : m + t ≤ A.card) →
    (J : Finset ι × ℕ) → J.2 ≤ m →
    (scheme D Q m hm).below J ≃ (scheme D Q (m + t) h).below J
  | 0, _, _, _ => Equiv.refl _
  | t + 1, h, J, hJ => (belowEquiv m hm t (by omega) J hJ).trans
      (HighLayerBountiful.equiv (scheme D Q (m + t) (by omega))
        (Q (m + t + 1)) (m + t + 1) (Nat.succ_pos _) h J (fun he => by
          have := he.2
          omega))

theorem belowEquiv_val (m : ℕ) (hm : m ≤ A.card) (t : ℕ) (h : m + t ≤ A.card)
    (J : Finset ι × ℕ) (hJ : J.2 ≤ m) (d : (scheme D Q m hm).below J) :
    (belowEquiv D Q m hm t h J hJ d).1 = embed D Q m hm t h d.1 := by
  induction t with
  | zero => rfl
  | succ t ih => exact congrArg (step D Q (m + t) h) (ih (by omega))

theorem card_eq (n : ℕ) (hn : n ≤ A.card) :
    (scheme D Q n hn).card = D.card + ∑ i ∈ Finset.range n, Fintype.card (Q (i + 1)) := by
  induction n with
  | zero => simp [scheme]
  | succ n ih =>
    change (scheme D Q n _).card + Fintype.card (Q (n + 1)) = _
    rw [ih, Finset.sum_range_succ, Nat.add_assoc]

end
end VaughtConjecture.Knight.RecursiveSourceCarrier
