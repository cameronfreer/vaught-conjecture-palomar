/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingLadderUpperRows

/-! # Installed mixed receiving rows

The semantics is built from the old private rows, the fixed long ladder
rows, and the constructed weighted upper rows. The request has a positive
singleton row and the apex is mute. All rows are orderly and, under the
scalar coding hypotheses, coded. Every old row and its domain remain literal.

This is not a `SemScheme`: original-owner incidences and the complete
consistency and bountifulness proofs are still required.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ReceivingLadderSemantics

open Transform Value ExtOrd ReceivingLadderCarrier
noncomputable section

variable {L : ℕ} {X Q U : Type*} [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)
  (field : Cell C → X) (request high : X) (profile : Q → X → ℕ)
  (fields : U → X → ExtOrd) (anchor : U → Q) (G : Finset ExtOrd) (H : ExtOrd)

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC

/-- Totalization only; the default never occurs below an inherited owner. -/
def oldRead (sem : Semantics C) (a : Cell C) (d : Cell D) : ExtOrd := by
  classical
  exact match view C hC d with
  | .inl e => if he : GradedLe (C.cell e) (C.cell a) then sem.E a ⟨e, he⟩ else ⊥
  | .inr _ => ⊥

def row (sem : Semantics C) (c d : Cell D) : ExtOrd :=
  match view C hC c with
  | .inl a => oldRead C hC sem a d
  | .inr .request => SupportLadderRows.source 1 1
  | .inr (.ladder _ v) => ladderRow C hC field request profile v d
  | .inr (.upper _ a node) =>
      ReceivingLadderUpperRows.row C hC field request high profile fields anchor G H a node d
  | .inr .apex => ⊥

local notation "row₀" => row (L := L) C hC field request high profile fields anchor G H

theorem row_old (sem : Semantics C) (a : Cell C) (e : C.below (C.cell a)) :
    row₀ sem (old C hC a) (old C hC e.1) = sem.E a e := by
  simp only [row, view_old, oldRead, dite_eq_left e.2]
  rfl

theorem row_old_all (sem : Semantics C) (a : Cell C)
    (d : (D).below ((D).cell (old C hC a))) :
    row₀ sem (old C hC a) d.1 = inheritedRow C hC sem a d := by
  obtain ⟨e, rfl⟩ := below_old C hC a d
  rw [inheritedRow_old]
  exact row_old C hC field request high profile fields anchor G H sem a e

theorem row_orderly (sem : Semantics C)
    (hbot : ⊥ ∈ G) (hG : ∀ h ∈ G, SelfVis 2 h) (hH : SelfVis 2 H)
    (hfields : ∀ a x, SelfVis 1 (fields a x))
    (hold : ∀ a c, SelfVis (C.grade c) (fields a (field c)))
    (hhigh : ∀ a, SelfVis 2 (fields a high)) (c : Cell D) :
    IsOrderly (fun d : (D).below ((D).cell c) => (D).grade d.1)
      (fun d => row₀ sem c d.1) := by
  rcases ReceivingLadderCarrier.cell_cases C hC c with ⟨a, rfl⟩ | ⟨z, rfl⟩
  · intro d
    dsimp only
    rw [row_old_all C hC field request high profile fields anchor G H sem a d]
    exact inheritedRow_orderly C hC sem a d
  · cases z with
    | request =>
        intro d
        have hg : (D).grade d.1 = 1 := by
          have hle : (D).grade d.1 ≤ 1 := by
            simpa only [CellScheme.grade, added_index, newIndex] using d.2.2
          exact le_antisymm hle ((D).grade_pos d.1)
        simp only [row, view_added]
        rw [hg]
        exact (SupportLadderRows.source_visible 1 1).symm
    | ladder b v =>
        simpa only [row, view_added] using ladderRow_orderly C hC field request profile b v
    | upper b a node =>
        simpa only [row, view_added] using
          ReceivingLadderUpperRows.row_orderly C hC field request high profile fields anchor G H
            hbot hG hH hfields hold hhigh b a node
    | apex =>
        intro d
        simp only [row, view_added, extVisibilityReplace_bot]

/-- Actual installed orderly rows. No lawfulness or completion field is hidden here. -/
def semantics (sem : Semantics C)
    (hbot : ⊥ ∈ G) (hG : ∀ h ∈ G, SelfVis 2 h) (hH : SelfVis 2 H)
    (hfields : ∀ a x, SelfVis 1 (fields a x))
    (hold : ∀ a c, SelfVis (C.grade c) (fields a (field c)))
    (hhigh : ∀ a, SelfVis 2 (fields a high)) : Semantics D where
  E c d := row₀ sem c d.1
  orderly := row_orderly C hC field request high profile fields anchor G H sem
    hbot hG hH hfields hold hhigh

variable (sem : Semantics C)
  (hbot : ⊥ ∈ G) (hG : ∀ h ∈ G, SelfVis 2 h) (hH : SelfVis 2 H)
  (hfields : ∀ a x, SelfVis 1 (fields a x))
  (hold : ∀ a c, SelfVis (C.grade c) (fields a (field c)))
  (hhigh : ∀ a, SelfVis 2 (fields a high))

local notation "E₀" => semantics (L := L) C hC field request high profile fields anchor G H sem
  hbot hG hH hfields hold hhigh

theorem inherited (a : Cell C) (d : (D).below ((D).cell (old C hC a))) :
    (E₀).E (old C hC a) d = inheritedRow C hC sem a d :=
  row_old_all C hC field request high profile fields anchor G H sem a d

theorem hasLadderRows : HasLadderRows C hC field request profile E₀ := by
  intro b v d
  simp only [semantics, row, view_added]

theorem hasUpperRows : ReceivingLadderUpperRows.HasUpperRows
    C hC field request high profile fields anchor G H E₀ := by
  intro b a node d
  simp only [semantics, row, view_added]

theorem coded (hsem : sem.IsCoded) (hGc : ∀ h ∈ G, IsCodedLabel 2 h)
    (hHc : IsCodedLabel 2 H) (hfc : ∀ a x, IsCodedLabel 2 (fields a x)) : (E₀).IsCoded := by
  intro c d
  rcases ReceivingLadderCarrier.cell_cases C hC c with ⟨a, rfl⟩ | ⟨z, rfl⟩
  · rw [inherited]
    exact inheritedRow_coded C hC sem hsem a d
  · cases z with
    | request =>
        simpa only [semantics, row, view_added, CellScheme.grade, added_index, newIndex] using
          SupportLadderRows.source_coded 1 1
    | ladder b v =>
        simpa only [semantics, row, view_added, ladder_grade] using
          ladderRow_coded C hC field request profile v d.1
    | upper b a node =>
        simpa only [semantics, row, view_added, upper_grade] using
          ReceivingLadderUpperRows.row_coded C hC field request high profile fields anchor G H
            hbot hGc hHc hfc a node d.1
    | apex => exact Or.inl (by simp only [semantics, row, view_added])

/-- Lawful scalar private restrictions supply the original-owner incidences
of each weighted upper row. Original semantic rows may be long. This uses
the actual old locality; no composition of faithful transformations is used. -/
theorem private_incidence
    (hprivate : ∀ a, RespectsSemantics sem (fun c => fields a (field c)))
    (a : U) (node : Bool) (c : Cell C) :
    TransformsTo (fun d : (D).below ((D).cell (old C hC c)) => (D).grade d.1)
      ((E₀).E (old C hC c))
      (fun d => min
        (ReceivingLadderUpperRows.row (L := L) C hC field request high profile fields anchor G H
          a node d.1)
        (ReceivingLadderUpperRows.row (L := L) C hC field request high profile fields anchor G H
          a node (old C hC c))) := by
  have hmax (d : C.below (C.cell c)) : C.grade d.1 ≤ 2 := by
    exact (C.grade_le_card_scope d.1).trans
      (by simpa only [Fintype.card_fin] using Finset.card_le_univ (s := C.scope d.1))
  have ht := (((hprivate a).locality c).cap hmax
    (ReceivingLadderUpperRows.weight_visible high fields H hhigh hH a node)).reindex
      (oldArg (L := L) (X := X) (Q := Q) (U := U) C hC c)
  have hg : (fun d : (D).below ((D).cell (old C hC c)) =>
      C.grade (oldArg C hC c d).1) = (fun d => (D).grade d.1) :=
    funext (oldArg_grade C hC c)
  have hi : sem.E c ∘ oldArg (L := L) (X := X) (Q := Q) (U := U) C hC c =
      (E₀).E (old C hC c) := by
    funext d
    exact (inherited C hC field request high profile fields anchor G H sem
      hbot hG hH hfields hold hhigh c d).symm
  have ho : (fun d : (D).below ((D).cell (old C hC c)) =>
      min (min (fields a (field (oldArg C hC c d).1)) (fields a (field c)))
        (ReceivingLadderUpperRows.weight high fields H a node)) =
      (fun d => min
        (ReceivingLadderUpperRows.row (L := L) C hC field request high profile fields anchor G H
          a node d.1)
        (ReceivingLadderUpperRows.row (L := L) C hC field request high profile fields anchor G H
          a node (old C hC c))) := by
    funext d
    obtain ⟨e, rfl⟩ := below_old C hC c d
    rw [oldArg_oldBelow (L := L) (X := X) (Q := Q) (U := U) C hC c e]
    simp only [oldBelow, ReceivingLadderUpperRows.row,
      ReceivingLadderSources.source_old]
    grind
  convert ht using 1
  · exact hg.symm
  · exact hi.symm
  · exact ho.symm

end
end VaughtConjecture.Knight.ReceivingLadderSemantics
