/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SupportLadderRows
public import VaughtConjecture.Knight.RoundedMeetCarrier

/-! # The mixed-scope carrier for the fixed ladder receiver

Keep a two-point private scheme on `{0,1}` and add the request point `2`.
The mixed scopes are `{0,2}` and `{0,1,2}`. This is the new13--new15 geometry
with the private points ordered first. Every rung, shadow, upper leaf and
numerical node has its own occurrence at each mixed scope. The highest row
will be mute. This file constructs geometry, not bountifulness.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ReceivingLadderCarrier

open AmalgamationPlan

def privatePlan : Finset (Finset (Fin 2)) := {∅, {0}, {1}, Finset.univ}

def plan : Finset (Finset (Fin 3)) :=
  {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, Finset.univ}

theorem privatePlan_isPlan : Plan.IsPlan Finset.univ privatePlan := by
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  refine Plan.IsPlan.step (a := 0) (b := 1) (Q := {∅, {1}}) (R := {∅, {0}})
    (by decide) (by decide) (by decide) ?_ ?_ (by decide) (by decide) (by decide)
  · rw [show ({0, 1} : Finset (Fin 2)).erase 0 = {1} by decide]
    exact Plan.IsPlan.singleton 1
  · rw [show ({0, 1} : Finset (Fin 2)).erase 1 = {0} by decide]
    exact Plan.IsPlan.singleton 0

theorem isPlan : Plan.IsPlan Finset.univ plan := by
  have he : plan = RoundedMeetCarrier.plan (1 : Fin 2) privatePlan := by decide
  rw [he]
  exact RoundedMeetCarrier.isPlan privatePlan_isPlan 1 (by decide)

def scope : Bool → Finset (Fin 3)
  | false => {0, 2}
  | true => Finset.univ

@[simp] theorem fresh_scope (b : Bool) : (2 : Fin 3) ∈ scope b := by cases b <;> decide

/-- No auxiliary is identified with its parent or with its other-scope copy. -/
inductive Added (L : ℕ) (X Q U : Type*)
  | request
  | ladder (full : Bool) (v : SupportLadderRows.Point L X Q)
  | upper (full : Bool) (a : U) (node : Bool)
  | apex
  deriving Fintype

variable {L : ℕ} {X Q U : Type*}

def newIndex : Added L X Q U → Finset (Fin 3) × ℕ
  | .request => ({2}, 1)
  | .ladder b _ => (scope b, 1)
  | .upper b _ _ => (scope b, 2)
  | .apex => (Finset.univ, 3)

theorem newIndex_mem (x : Added L X Q U) : newIndex x ∈ Plan.gradedPlan plan := by
  cases x with
  | request => dsimp only [newIndex]; decide
  | ladder b _ => cases b <;> dsimp only [newIndex] <;> decide
  | upper b _ _ => cases b <;> dsimp only [newIndex] <;> decide
  | apex => dsimp only [newIndex]; decide

theorem newIndex_fresh (x : Added L X Q U) : (2 : Fin 3) ∈ (newIndex x).1 := by
  cases x with
  | request => dsimp only [newIndex]; decide
  | ladder b _ => exact fresh_scope b
  | upper b _ _ => exact fresh_scope b
  | apex => exact Finset.mem_univ _

variable [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)

include hC in
theorem old_face_iff (B : Finset (Fin 2)) :
    B.image Fin.castSuccEmb ∈ plan ↔ B ∈ C.plan := by
  rw [hC]
  exact (by decide : ∀ B : Finset (Fin 2),
    B.image Fin.castSuccEmb ∈ plan ↔ B ∈ privatePlan) B

noncomputable def scheme : CellScheme (ι := Fin 3) Finset.univ :=
  CellScheme.extendOneWith C plan isPlan (old_face_iff C hC)
    (newIndex (L := L) (X := X) (Q := Q) (U := U)) newIndex_mem

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC

def old (c : Cell C) : Cell D := Fin.castAdd (Fintype.card (Added L X Q U)) c

noncomputable def added (x : Added L X Q U) : Cell D :=
  Fin.natAdd C.card ((Fintype.equivFin (Added L X Q U)) x)

@[simp] theorem old_index (c : Cell C) :
    (D).cell (old (L := L) (X := X) (Q := Q) (U := U) C hC c) =
      ((C.scope c).image Fin.castSuccEmb, C.grade c) :=
  CellScheme.extendOneWith_cell_castAdd c

@[simp] theorem added_index (x : Added L X Q U) :
    (D).cell (added C hC x) = newIndex x := by
  unfold added scheme
  rw [CellScheme.extendOneWith_cell_natAdd, Equiv.symm_apply_apply]

theorem old_injective : Function.Injective (old (L := L) (X := X) (Q := Q) (U := U) C hC) := by
  intro a b h
  have he := congrArg Fin.val h
  exact Fin.ext he

theorem added_injective : Function.Injective (added (L := L) (X := X) (Q := Q) (U := U) C hC) := by
  intro a b h
  apply (Fintype.equivFin (Added L X Q U)).injective
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg Fin.val h)

theorem old_ne_added (c : Cell C) (x : Added L X Q U) : old C hC c ≠ added C hC x := by
  apply Fin.ne_of_val_ne
  simp only [old, added, Fin.val_castAdd, Fin.val_natAdd]
  have hc := c.isLt
  omega

theorem cell_cases (d : Cell D) :
    (∃ c, d = old C hC c) ∨ ∃ x, d = added C hC x := by
  induction d using Fin.addCases with
  | left c => exact Or.inl ⟨c, rfl⟩
  | right j =>
    exact Or.inr ⟨(Fintype.equivFin (Added L X Q U)).symm j,
      congrArg (Fin.natAdd C.card) ((Fintype.equivFin (Added L X Q U)).apply_symm_apply j).symm⟩

/-- Decode the occurrence tag without identifying either mixed-scope copy. -/
noncomputable def view : Cell D → Cell C ⊕ Added L X Q U :=
  Fin.addCases Sum.inl (fun j => Sum.inr ((Fintype.equivFin (Added L X Q U)).symm j))

@[simp] theorem view_old (c : Cell C) :
    view (L := L) (X := X) (Q := Q) (U := U) C hC (old C hC c) = Sum.inl c := by
  simp only [view, old, Fin.addCases_left]

@[simp] theorem view_added (x : Added L X Q U) :
    view C hC (added C hC x) = Sum.inr x := by
  simp only [view, added, Fin.addCases_right, Equiv.symm_apply_apply]

theorem old_visible : Finset.univ.image Fin.castSuccEmb ∈ (D).plan :=
  CellScheme.extendOneWith_visible

/-- The old ordered cell scheme is a literal face, not merely isomorphic. -/
theorem restrict_old : (D).restrictFace Fin.castSuccEmb (old_visible C hC) = C :=
  CellScheme.restrictFace_extendOneWith newIndex_fresh

def oldBelow (c : Cell C) (d : C.below (C.cell c)) :
    (D).below ((D).cell (old C hC c)) :=
  ⟨old C hC d.1, by
    rw [old_index, old_index]
    exact ⟨Finset.image_subset_image d.2.1, d.2.2⟩⟩

/-- Every argument below an inherited owner is inherited; none of the
new rung, shadow or upper occurrences enters an old row's domain. -/
theorem below_old (c : Cell C) (d : (D).below ((D).cell (old C hC c))) :
    ∃ a : C.below (C.cell c), oldBelow C hC c a = d := by
  rcases cell_cases C hC d.1 with ⟨a, ha⟩ | ⟨x, hx⟩
  · have hd := d.2
    rw [ha, old_index, old_index] at hd
    exact ⟨⟨a, (Finset.image_subset_image_iff Fin.castSuccEmb.injective).mp hd.1, hd.2⟩,
      Subtype.ext ha.symm⟩
  · have hd := d.2.1
    rw [hx, added_index, old_index] at hd
    obtain ⟨a, _, he⟩ := Finset.mem_image.mp (hd (newIndex_fresh x))
    have hh := congrArg Fin.val he
    have ha := a.isLt
    change a.val = 2 at hh
    omega

noncomputable def oldArg (c : Cell C) (d : (D).below ((D).cell (old C hC c))) :
    C.below (C.cell c) := Classical.choose (below_old C hC c d)

theorem oldArg_spec (c : Cell C) (d : (D).below ((D).cell (old C hC c))) :
    oldBelow C hC c (oldArg C hC c d) = d :=
  Classical.choose_spec (below_old C hC c d)

@[simp] theorem oldArg_oldBelow (c : Cell C) (d : C.below (C.cell c)) :
    oldArg (L := L) (X := X) (Q := Q) (U := U) C hC c (oldBelow C hC c d) = d := by
  apply Subtype.ext
  apply old_injective (L := L) (X := X) (Q := Q) (U := U) C hC
  exact congrArg Subtype.val (oldArg_spec C hC c (oldBelow C hC c d))

theorem oldArg_grade (c : Cell C) (d : (D).below ((D).cell (old C hC c))) :
    C.grade (oldArg C hC c d).1 = (D).grade d.1 := by
  have he := congrArg Subtype.val (oldArg_spec C hC c d)
  have hg := congrArg (fun z : Cell D => ((D).cell z).2) he
  simpa only [oldBelow, old_index, CellScheme.grade] using hg

/-- A same-scope copy contains the entire rung/shadow table. -/
noncomputable def ladderBelow (b : Bool) (c v : SupportLadderRows.Point L X Q) :
    (D).below ((D).cell (added C hC (.ladder b c))) :=
  ⟨added C hC (.ladder b v), by rw [added_index, added_index]; exact GradedLe.refl _⟩

@[simp] theorem ladder_grade (b : Bool) (v : SupportLadderRows.Point L X Q) :
    (D).grade (added C hC (.ladder b v)) = 1 :=
  congrArg Prod.snd (added_index C hC (.ladder b v))

theorem below_ladder_grade (b : Bool) (v : SupportLadderRows.Point L X Q)
    (d : (D).below ((D).cell (added C hC (.ladder b v)))) : (D).grade d.1 = 1 := by
  have hd := d.2.2
  change (D).grade d.1 ≤ (D).grade (added C hC (.ladder b v)) at hd
  rw [ladder_grade] at hd
  exact le_antisymm hd ((D).grade_pos d.1)

/-- Every possible grade-one availability witness at a mixed index is an
actual rung or shadow of that scope's table. -/
theorem at_ladder_index (b : Bool) (d : Cell D) (hd : (D).cell d = (scope b, 1)) :
    ∃ v : SupportLadderRows.Point L X Q, d = added C hC (.ladder b v) := by
  rcases cell_cases C hC d with ⟨a, rfl⟩ | ⟨x, rfl⟩
  · have he := congrArg Prod.fst hd
    rw [old_index] at he
    change (C.scope a).image Fin.castSuccEmb = scope b at he
    have hm : (2 : Fin 3) ∈ (C.scope a).image Fin.castSuccEmb :=
      he.symm ▸ fresh_scope b
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    have hv := congrArg Fin.val hi
    have hil := i.isLt
    change i.val = 2 at hv
    omega
  · rw [added_index] at hd
    cases x with
    | request =>
        have he := congrArg Prod.fst hd
        change ({2} : Finset (Fin 3)) = scope b at he
        have hz : (0 : Fin 3) ∈ scope b := by cases b <;> decide
        have hm : (0 : Fin 3) ∈ ({2} : Finset (Fin 3)) := he.symm ▸ hz
        exact (by decide : (0 : Fin 3) ∉ ({2} : Finset (Fin 3))) hm |>.elim
    | ladder b' v =>
        have he : b' = b := (by decide : ∀ x y : Bool, scope x = scope y → x = y)
          b' b (congrArg Prod.fst hd)
        subst b'
        exact ⟨v, rfl⟩
    | upper _ _ _ => exact (by decide : (2 : ℕ) ≠ 1) (congrArg Prod.snd hd) |>.elim
    | apex => exact (by decide : (3 : ℕ) ≠ 1) (congrArg Prod.snd hd) |>.elim

/-- Every required new graded index has an actual occurrence. Old
completeness is used only for the literal old face. -/
theorem complete [Nonempty Q] [Nonempty U] (hL : 0 < L) (hc : C.IsComplete) :
    (D).IsComplete := by
  apply CellScheme.IsComplete.extendOneWith hc
  rintro ⟨B, j⟩ hBJ hfresh
  obtain ⟨hB, hj, hcard⟩ := Plan.mem_gradedPlan.mp hBJ
  have hscope : B = {2} ∨ B = scope false ∨ B = Finset.univ :=
    (by decide : ∀ B : Finset (Fin 3), B ∈ plan → (2 : Fin 3) ∈ B →
      B = {2} ∨ B = scope false ∨ B = Finset.univ) B hB hfresh
  let a := Classical.choice ‹Nonempty Q›
  let u := Classical.choice ‹Nonempty U›
  rcases hscope with rfl | rfl | rfl
  · have hj' : j = 1 := by simpa using le_antisymm hcard hj
    exact ⟨.request, by rw [hj']; rfl⟩
  · have hj' : j = 1 ∨ j = 2 := by
      have he : (scope false).card = 2 := by decide
      rw [he] at hcard
      omega
    rcases hj' with rfl | rfl
    · exact ⟨.ladder false (SupportLadderRows.leaf hL a), rfl⟩
    · exact ⟨.upper false u false, rfl⟩
  · have hj' : j = 1 ∨ j = 2 ∨ j = 3 := by
      simp only [Finset.card_univ, Fintype.card_fin] at hcard
      omega
    rcases hj' with rfl | rfl | rfl
    · exact ⟨.ladder true (SupportLadderRows.leaf hL a), rfl⟩
    · exact ⟨.upper true u false, rfl⟩
    · exact ⟨.apex, rfl⟩

end VaughtConjecture.Knight.ReceivingLadderCarrier
