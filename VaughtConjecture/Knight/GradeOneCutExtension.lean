/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneBottomCuts

/-! # Appending a source above the inherited inventory

Inherited cuts extend with the new occurrence nonbottom. If the new owner's
old block triples copy a source-maximal donor, their bottom implications add
no restriction on those cuts. The new all-bottom cut is also permitted.

The block table is an explicit hypothesis, not a constructed row or scheme.
This proves bottom-pattern preservation only: source witnesses, geometry,
availability, prescribed labels, and successor closure are not supplied.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting.BottomCut

variable {Y S : Type*} [LinearOrder S]

/-- The new occurrence is none; every old occurrence is retained by some. -/
def adjoin (E : Y → S) (κ : S) : Option Y → S
  | none => κ
  | some d => E d

/-- Extend flags without killing the new occurrence. -/
def extend (z : Y → Bool) : Option Y → Bool
  | none => false
  | some d => z d

theorem flag_adjoin_old (E : Y → S) (κ : S) (hκ : ∀ d, E d < κ) (a : Option Y) :
    flag (adjoin E κ) (a.map some) = extend (flag E a) := by
  funext d
  cases a with
  | none => cases d <;> rfl
  | some a =>
    cases d with
    | none => simp [flag, adjoin, extend, not_le_of_gt (hκ a)]
    | some d => rfl

theorem flag_adjoin_top (E : Y → S) (κ : S) (hκ : ∀ d, E d ≤ κ) :
    flag (adjoin E κ) (some none) = fun _ => true := by
  funext d
  cases d <;> simp [flag, adjoin, hκ]

/-- Nested block implications, written directly on the bottom flags. -/
def Closed (B : Y → Y → Y → Prop) (z : Y → Bool) : Prop :=
  ∀ c d e, B c d e → (z d = true ∨ z c = true) → (z e = true ∨ z c = true)

instance [Fintype Y] (B : Y → Y → Y → Prop) [∀ c d e, Decidable (B c d e)]
    (z : Y → Bool) : Decidable (Closed B z) :=
  inferInstanceAs (Decidable (∀ c d e, B c d e →
    (z d = true ∨ z c = true) → (z e = true ∨ z c = true)))

/-- Retain all old triples, copy a donor's old triples to the new owner,
and give the fresh occurrence its own block. No cross-block triple is added. -/
def donorBlocks (B : Y → Y → Y → Prop) (t : Y) :
    Option Y → Option Y → Option Y → Prop
  | some c, some d, some e => B c d e
  | none, some d, some e => B t d e
  | none, none, none => True
  | _, _, _ => False

instance (B : Y → Y → Y → Prop) [∀ c d e, Decidable (B c d e)]
    (t : Y) (c d e : Option Y) : Decidable (donorBlocks B t c d e) := by
  cases c <;> cases d <;> cases e <;> unfold donorBlocks <;> infer_instance

/-- If killing the donor kills all old occurrences, copying its blocks
introduces no additional bottom restriction when the new owner is nonbottom. -/
theorem closed_extend_iff (B : Y → Y → Y → Prop) (t : Y) (z : Y → Bool)
    (ht : z t = true → ∀ d, z d = true) :
    Closed (donorBlocks B t) (extend z) ↔ Closed B z := by
  constructor
  · intro h c d e hb hz
    exact h (some c) (some d) (some e) hb hz
  · intro h c d e hb hz
    cases c with
    | some c =>
      cases d <;> cases e <;> simp only [donorBlocks] at hb
      exact h _ _ _ hb hz
    | none =>
      cases d with
      | none => simp [extend] at hz
      | some d =>
        cases e with
        | none => exact False.elim hb
        | some e =>
          have hd : z d = true := by simpa [extend] using hz
          have he : z e = true := by
            rcases h t d e hb (Or.inl hd) with he | ht'
            · exact he
            · exact ht ht' e
          exact Or.inl he

/-- At a source-maximal donor, every inherited cut satisfies the needed
condition. The new source and copied blocks therefore preserve all old cuts. -/
theorem closed_adjoin_cut_iff (E : Y → S) (κ : S) (hκ : ∀ d, E d < κ)
    (B : Y → Y → Y → Prop) (t : Y) (ht : ∀ d, E d ≤ E t) (a : Option Y) :
    Closed (donorBlocks B t) (flag (adjoin E κ) (a.map some)) ↔
      Closed B (flag E a) := by
  rw [flag_adjoin_old E κ hκ]
  apply closed_extend_iff
  intro hz d
  cases a with
  | none => contradiction
  | some a =>
    simp only [flag, decide_eq_true_eq] at hz ⊢
    exact (ht d).trans hz

theorem closed_all_bottom (B : Y → Y → Y → Prop) : Closed B (fun _ => true) := by
  intro c d e _ _
  exact Or.inl rfl

theorem closed_adjoin_top (E : Y → S) (κ : S) (hκ : ∀ d, E d ≤ κ)
    (B : Y → Y → Y → Prop) (t : Y) :
    Closed (donorBlocks B t) (flag (adjoin E κ) (some none)) := by
  rw [flag_adjoin_top E κ hκ]
  exact closed_all_bottom _

/-- The Boolean predicate is exactly the executable check's nested blocks. -/
theorem blocks_seed_iff {C : Type*} (T : Executable.Data Y C) (z : Y → Bool) :
    T.Blocks (Executable.Data.seed z) ↔ Closed (fun c d e => (c, d, e) ∈ T.blocks) z := by
  simp only [Executable.Data.Blocks, Closed]
  have hs (d : Y) : Executable.Data.seed z d = 0 ↔ z d = true := by
    cases hz : z d <;> simp [Executable.Data.seed, hz]
  simp only [hs, Prod.forall]

end VaughtConjecture.Knight.FullRowLifting.BottomCut
