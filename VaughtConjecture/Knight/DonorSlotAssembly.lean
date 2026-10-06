/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SlotControllerFamily
public import VaughtConjecture.Knight.DonorFreshSlots

/-! # A jointly consistent slot layer retaining actual old occurrences

All slot controllers are supplied simultaneously, with literal old readings
and one fresh column. Every old occurrence remains a distinct occurrence even
when sources coincide. The common old profile respects the unchanged old rows.
Every lawful old input and independent fresh value has a joint whole-layer
section. Arbitrary row-layer ambients have an actual dominating controller.

This does not add intermediate mixed scopes or prove a bountiful cell scheme.
Full-index availability is proved; proper-index availability and original-cap
lifting are separate obligations.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.DonorSlotAssembly

open Transform Value ExtOrd FreshSourceSlots

variable {X : Type*} [Fintype X]

abbrev Occ (X : Type*) [Fintype X] := Option X ⊕ Fin (Fintype.card X + 1)

def old (d : X) : Occ X := .inl (some d)
def fresh : Occ X := .inl none
def controller (j : Fin (Fintype.card X + 1)) : Occ X := .inr j

open Classical in
/-- This map is only a proof device. The carrier remains `Occ X`, not its image. -/
noncomputable def position (E : X → ExtOrd) : Occ X → SlotControllerFamily.Point (Fintype.card X)
  | .inl none => SlotControllerFamily.fresh
  | .inl (some d) => if E d = ⊥ then SlotControllerFamily.bottomPoint
      else SlotControllerFamily.old ⟨rank E d, rank_lt_card E d⟩
  | .inr j => SlotControllerFamily.controller j

noncomputable def row (E : X → ExtOrd) (q : Fin (Fintype.card X + 1))
    (d : Occ X) : ExtOrd := SlotControllerFamily.row q (position E d)

theorem old_reading (E : X → ExtOrd) (q : Fin (Fintype.card X + 1)) (d : X) :
    row E q (old d) = oldSource E d := by
  classical
  by_cases hd : E d = ⊥
  · simp [row, old, position, hd, SlotControllerFamily.row, SlotControllerFamily.bottomPoint,
      SlotControllerFamily.index, SlotControllerFamily.value, oldSource, oldBlock, source]
  · simp [row, old, position, hd, SlotControllerFamily.row, SlotControllerFamily.old,
      SlotControllerFamily.index, SlotControllerFamily.value, oldSource, oldBlock, source]

theorem fresh_reading (E : X → ExtOrd) (q : Fin (Fintype.card X + 1)) :
    row E q fresh = SeparatedGradeOne.band (2 * q.val + 1) := by
  simp [row, fresh, position, SlotControllerFamily.row, SlotControllerFamily.fresh,
    SlotControllerFamily.index, SlotControllerFamily.value]

theorem diagonal (E : X → ExtOrd) (q : Fin (Fintype.card X + 1)) :
    row E q (controller q) = SeparatedGradeOne.band (ownerBlock X) := by
  simp [row, controller, position, SlotControllerFamily.row, SlotControllerFamily.value,
    SlotControllerFamily.height, ownerBlock]

theorem base_reading (E : X → ExtOrd) (q : Fin (Fintype.card X + 1)) (d : Option X) :
    row E q (.inl d) = FreshSourceSlots.row E q.val d := by
  cases d with
  | none => exact fresh_reading E q
  | some d => exact old_reading E q d

def Joint (E : X → ExtOrd) (p : Occ X → ExtOrd) : Prop :=
  (∀ d, SelfVis 1 (p d)) ∧
  (∀ c, TransformsTo (fun _ : Occ X => 1) (row E c)
    (fun d => min (p d) (p (controller c)))) ∧
  ∀ d, ∃ c, p d ≤ p (controller c)

theorem pull_joint (E : X → ExtOrd) {p : SlotControllerFamily.Point (Fintype.card X) → ExtOrd}
    (hp : SlotControllerFamily.Joint p) : Joint E (fun d => p (position E d)) := by
  refine ⟨fun d => hp.1 _, ?_, ?_⟩
  · intro c
    exact (hp.2.2.1 c).reindex (position E)
  · intro d
    exact hp.2.2.2 (position E d)

theorem rows_joint (E : X → ExtOrd) (q : Fin (Fintype.card X + 1)) : Joint E (row E q) :=
  pull_joint E (SlotControllerFamily.rows_joint q)

theorem row_coded (E : X → ExtOrd) (q : Fin (Fintype.card X + 1)) (d : Occ X) :
    IsCodedLabel 1 (row E q d) := SlotControllerFamily.value_coded _

/-- Source order, visibility and bottom flags suffice for joint respect in
this particular family. This is proved from its explicit cross-readings. -/
theorem ordered_joint (E : X → ExtOrd) (q : Fin (Fintype.card X + 1)) (p : Occ X → ExtOrd)
    (hv : ∀ d, SelfVis 1 (p d)) (hb : ∀ d, row E q d = ⊥ → p d = ⊥)
    (hm : ∀ d e, row E q d ≤ row E q e → p d ≤ p e) : Joint E p := by
  have ht : TransformsTo (fun _ : Occ X => 1) (row E q) p := by
    apply SlotControllerFamily.transforms_of_table
    · exact hv
    · intro d hd
      apply hb d
      change SlotControllerFamily.value (SlotControllerFamily.index q (position E d)) = ⊥
      rw [hd]
      rfl
    · intro d e h
      exact hm d e (SlotControllerFamily.value_mono h)
  obtain ⟨f, hf, hfbot, hfvis, he⟩ := SlotControllerFamily.table_of_transform ht
  have hj := pull_joint E
    (SlotControllerFamily.label_joint q f hf hfbot (fun _ => hfvis _))
  have hfun : (fun d => SlotControllerFamily.label q f (position E d)) = p := funext he
  rwa [hfun] at hj

/-- Arbitrary ordered old inputs and independent fresh readings have a
simultaneous section across all controllers, with a prescribed serving diagonal. -/
theorem exists_section {E p : X → ExtOrd} {v U : ExtOrd}
    (hp : ∀ d, SelfVis 1 (p d)) (hv : SelfVis 1 v) (hU : SelfVis 1 U)
    (horder : ∀ d e, E d ≤ E e → p d ≤ p e) (hbot : ∀ d, E d = ⊥ → p d = ⊥)
    (hpU : ∀ d, p d ≤ U) (hvU : v ≤ U) :
    ∃ r : Occ X → ExtOrd, Joint E r ∧ (∀ d, r (old d) = p d) ∧ r fresh = v ∧
      ∃ j, r (controller j) = U := by
  obtain ⟨j, hj⟩ := exists_slot_with_owner hp hv hU horder hbot hpU hvU
  let inc : Option (Option X) → Occ X := FreeDiagonal.append Sum.inl (controller j)
  have hread : ∀ d, row E j (inc d) =
      FreeDiagonal.append (FreshSourceSlots.row E j.val)
        (SeparatedGradeOne.band (ownerBlock X)) d := by
    rintro (_ | d)
    · exact diagonal E j
    · exact base_reading E j d
  have ht : TransformsTo (fun _ : Option (Option X) => 1)
      (fun d => SlotControllerFamily.value
        (SlotControllerFamily.index j (position E (inc d))))
      (FreeDiagonal.append (FreeDiagonal.append p v) U) := by
    change TransformsTo _ (fun d => row E j (inc d)) _
    simpa only [hread] using hj
  obtain ⟨f, hm, hb, hf, hliteral⟩ := SlotControllerFamily.table_of_transform ht
  let r : Occ X → ExtOrd := fun d => SlotControllerFamily.label j f (position E d)
  refine ⟨r, pull_joint E (SlotControllerFamily.label_joint j f hm hb (fun _ => hf _)),
    fun d => hliteral (some (some d)), hliteral (some none), j, hliteral none⟩

theorem Joint.exists_dominator {E : X → ExtOrd} {p : Occ X → ExtOrd} (hp : Joint E p) :
    ∃ q, ∀ d, p d ≤ p (controller q) := by
  obtain ⟨q, hq⟩ := Finite.exists_max (fun q : Fin (Fintype.card X + 1) => p (controller q))
  refine ⟨q, ?_⟩
  intro d
  obtain ⟨j, hj⟩ := hp.2.2 d
  exact hj.trans (hq j)

/-- Every row-layer ambient, not only a selected section, has a whole-table
ordered representation at an actual dominating controller. -/
theorem Joint.exists_shape {E : X → ExtOrd} {p : Occ X → ExtOrd} (hp : Joint E p) :
    ∃ q f, Monotone f ∧ f 0 = ⊥ ∧ (∀ i, SelfVis 1 (f i)) ∧
      ∀ d, p d = f (SlotControllerFamily.index q (position E d)) := by
  obtain ⟨q, hq⟩ := hp.exists_dominator
  have hl := hp.2.1 q
  have he : (fun d => min (p d) (p (controller q))) = p :=
    funext (fun d => min_eq_left (hq d))
  rw [he] at hl
  obtain ⟨f, hm, hb, hv, hf⟩ := SlotControllerFamily.table_of_transform hl
  exact ⟨q, f, hm, hb, hv, fun d => (hf d).symm⟩

section ActualDonor

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {o : Cell D} [Fintype (D.below (D.cell o))]

theorem old_restriction_respects (hc : sem.IsConsistent) (ho : D.grade o = 1)
    (j : Fin (Fintype.card (D.below (D.cell o)) + 1)) :
    RespectsSemanticsBelow sem (D.cell o) (fun d => row (sem.E o) j (old d)) := by
  simpa only [old_reading] using DonorFreshSlots.donor_profile_respects hc ho

/-- Simultaneous whole-layer sections retain every actual old occurrence and
the independent fresh value; no new-controller locality is an input. -/
theorem lawful_section {p : D.below (D.cell o) → ExtOrd} {v U : ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell o) p) (hu : DonorSourceRefinement.UniqueAt o)
    (ho : D.grade o = 1) (hv : SelfVis 1 v) (hU : SelfVis 1 U)
    (hpU : p (DonorSourceRefinement.owner o) ≤ U) (hvU : v ≤ U) :
    ∃ r : Occ (D.below (D.cell o)) → ExtOrd, Joint (sem.E o) r ∧
      (∀ d, r (old d) = p d) ∧ r fresh = v ∧ ∃ j, r (controller j) = U := by
  apply exists_section
  · intro d
    simpa only [DonorFreshSlots.grade_one ho d] using (hp.orderly d).symm
  · exact hv
  · exact hU
  · exact DonorFreshSlots.lawful_order hp hu ho
  · exact DonorFreshSlots.lawful_bottom hp hu ho
  · intro d
    exact (DonorSourceRefinement.label_le_owner hp hu d
      ((DonorFreshSlots.grade_one ho d).trans ho.symm)).trans hpU
  · exact hvU

end ActualDonor

end VaughtConjecture.Knight.DonorSlotAssembly
