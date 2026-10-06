/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FreshSourceSlots
public import VaughtConjecture.Knight.DonorSourceRefinement
public import VaughtConjecture.Knight.GradeOneInputEncoding

/-! # Independent fresh readings over an actual grade-one donor

The even-block profile is lawful for the unchanged old semantics. This uses
bounded-map source-block repair, not composition of faithful transformations.
At a unique grade-one donor, every lawful old input follows the donor's source
order and bottom flags. The finite slot family therefore covers that entire
input and any independent visible fresh value, literally.

The family is fixed before the input is given. It is not yet a family of cells
in a consistent enlarged scheme: sibling incidences and ambient-active coverage
remain to be constructed. No reference forcing or bountiful extension is claimed.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.DonorFreshSlots

open Transform Value ExtOrd FreshSourceSlots DonorSourceRefinement FullRowLifting

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {o : Cell D} [Fintype (D.below (D.cell o))]

omit [Fintype (D.below (D.cell o))] in
theorem grade_one (ho : D.grade o = 1) (d : D.below (D.cell o)) : D.grade d.1 = 1 := by
  have hl : D.grade d.1 ≤ D.grade o := d.2.2
  have hp := D.grade_pos d.1
  omega

/-- Recoding any lawful grade-one profile into separated even blocks preserves
respect of the old rows, including all incoming witnesses and availability. -/
theorem oldSource_respects {p : D.below (D.cell o) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell o) p) (ho : D.grade o = 1) :
    RespectsSemanticsBelow sem (D.cell o) (oldSource p) := by
  have hv : ∀ d, SelfVis 1 (p d) := by
    intro d
    simpa only [grade_one ho d] using (hp.orderly d).symm
  have hr := map_respects_of_bounded_reflecting
    (orderInterpolate_bounded hv (fun d => source_visible (oldBlock p d)))
    (orderInterpolate_bottom_iff (fun d h => (oldSource_bot_iff p d).mp h))
    (fun d => (grade_one ho d).le) hp
  have he : ∀ d, orderInterpolate p (oldSource p) (p d) = oldSource p d :=
    orderInterpolate_read (fun d e h => (oldSource_le_iff p d e).mpr h)
      (fun d h => (oldSource_bot_iff p d).mpr h)
  change RespectsSemanticsBelow sem (D.cell o)
    (fun d => orderInterpolate p (oldSource p) (p d)) at hr
  simpa only [he] using hr

theorem donor_profile_respects (hc : sem.IsConsistent) (ho : D.grade o = 1) :
    RespectsSemanticsBelow sem (D.cell o) (oldSource (sem.E o)) :=
  oldSource_respects (hc o) ho

theorem donor_profile_coded (d : D.below (D.cell o)) :
    IsCodedLabel 1 (oldSource (sem.E o) d) := source_coded _

omit [Fintype (D.below (D.cell o))] in
/-- No displayed ties or order are imposed: the source order is the old donor's. -/
theorem lawful_order {p : D.below (D.cell o) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell o) p) (hu : UniqueAt o)
    (ho : D.grade o = 1) (d e : D.below (D.cell o))
    (h : sem.E o d ≤ sem.E o e) : p d ≤ p e := by
  obtain ⟨τ, hτ, _, hr⟩ := exact_witness hp
  have hd : D.grade d.1 = D.grade o := (grade_one ho d).trans ho.symm
  have he : D.grade e.1 = D.grade o := (grade_one ho e).trans ho.symm
  have hh := hτ.mono h
  rwa [hr d, hr e, min_eq_left (label_le_owner hp hu d hd),
    min_eq_left (label_le_owner hp hu e he)] at hh

omit [Fintype (D.below (D.cell o))] in
theorem lawful_bottom {p : D.below (D.cell o) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell o) p) (hu : UniqueAt o)
    (ho : D.grade o = 1) (d : D.below (D.cell o)) (hd : sem.E o d = ⊥) : p d = ⊥ := by
  obtain ⟨τ, hτ, _, hr⟩ := exact_witness hp
  have hg : D.grade d.1 = D.grade o := (grade_one ho d).trans ho.symm
  have hh := hr d
  rw [hd, hτ.bot, min_eq_left (label_le_owner hp hu d hg)] at hh
  exact hh.symm

/-- A family of at most one more than the old occurrence count serves every
lawful old input and every independent fresh grade-one value. The sources are
chosen from the old row alone, not from the input or its displayed order. -/
theorem covers {p : D.below (D.cell o) → ExtOrd} {v : ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell o) p) (hu : UniqueAt o)
    (ho : D.grade o = 1) (hv : SelfVis 1 v) :
    ∃ j : Fin (Fintype.card (D.below (D.cell o)) + 1),
      TransformsTo (fun _ : Option (D.below (D.cell o)) => 1)
        (row (sem.E o) j.val) (FreeDiagonal.append p v) := by
  apply exists_slot
  · intro d
    simpa only [grade_one ho d] using (hp.orderly d).symm
  · exact hv
  · exact lawful_order hp hu ho
  · exact lawful_bottom hp hu ho

/-- The old owner's bound suffices for a freely prescribed dominating owner
of the appended row; the independent fresh label is bounded separately. -/
theorem covers_with_owner {p : D.below (D.cell o) → ExtOrd} {v U : ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell o) p) (hu : UniqueAt o)
    (ho : D.grade o = 1) (hv : SelfVis 1 v) (hU : SelfVis 1 U)
    (hpU : p (owner o) ≤ U) (hvU : v ≤ U) :
    ∃ j : Fin (Fintype.card (D.below (D.cell o)) + 1),
      TransformsTo (fun _ : Option (Option (D.below (D.cell o))) => 1)
        (FreeDiagonal.append (row (sem.E o) j.val)
          (SeparatedGradeOne.band (ownerBlock (D.below (D.cell o)))))
        (FreeDiagonal.append (FreeDiagonal.append p v) U) := by
  apply exists_slot_with_owner
  · intro d
    simpa only [grade_one ho d] using (hp.orderly d).symm
  · exact hv
  · exact hU
  · exact lawful_order hp hu ho
  · exact lawful_bottom hp hu ho
  · intro d
    exact (label_le_owner hp hu d ((grade_one ho d).trans ho.symm)).trans hpU
  · exact hvU

theorem old_reading (j : ℕ) (d : D.below (D.cell o)) :
    row (sem.E o) j (some d) = oldSource (sem.E o) d := rfl

theorem fresh_distinct (j : ℕ) (d : D.below (D.cell o)) :
    row (sem.E o) j none ≠ row (sem.E o) j (some d) := fresh_ne_old _ _ _

theorem template_coded (j : ℕ) (d : Option (D.below (D.cell o))) :
    IsCodedLabel 1 (row (sem.E o) j d) := source_coded _

end VaughtConjecture.Knight.DonorFreshSlots
