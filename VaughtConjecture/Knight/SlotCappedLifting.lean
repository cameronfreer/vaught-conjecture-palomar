/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SlotActiveCoverage
public import VaughtConjecture.Knight.GradeOneSectionLifting

/-! # Original-cap lifting across the whole slot row layer

A fitting ambient-active slot orders the ambient's capped trace. The proved
least-order completion extends the prescribed old/fresh labels and retains
every auxiliary controller's cap. Joint lawfulness follows from the explicit
cross-readings. Bottom and top caps are included; the cap is never raised.

The protected old/fresh inventory is a boundary, not asserted to be a lower
domain of an assembled scheme. Proper mixed scopes and their rows remain absent.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.SlotCappedLifting

open Transform Value ExtOrd DonorSlotAssembly SlotActiveCoverage FullRowLifting

variable {X : Type*} [Fintype X]

private theorem transform_order {Y : Type*} {s t : Y → ExtOrd}
    (h : TransformsTo (fun _ : Y => 1) s t) (d e : Y) (hde : s d ≤ s e) : t d ≤ t e := by
  obtain ⟨g, σ, _, _, _, hm, _, hr⟩ := h
  rw [hr d, hr e]
  exact min_le_min_right _ (hm hde)

private theorem transform_bottom {Y : Type*} {s t : Y → ExtOrd}
    (h : TransformsTo (fun _ : Y => 1) s t) (d : Y) (hd : s d = ⊥) : t d = ⊥ := by
  obtain ⟨g, σ, _, _, hb, _, _, hr⟩ := h
  rw [hr d, hd, hb, min_bot_left]

/-- All old and fresh outputs remain literal and every ambient auxiliary cap
is preserved, from an arbitrary jointly lawful ambient of the row layer. -/
theorem lift {E p : X → ExtOrd} {v γ : ExtOrd} {a : Occ X → ExtOrd}
    (ha : Joint E a) (hp : ∀ d, SelfVis 1 (p d)) (hv : SelfVis 1 v) (hγ : SelfVis 1 γ)
    (horder : ∀ d e, E d ≤ E e → p d ≤ p e) (hbot : ∀ d, E d = ⊥ → p d = ⊥)
    (hag : ∀ d : Option X, min (a (.inl d)) γ = min (FreeDiagonal.append p v d) γ) :
    ∃ r : Occ X → ExtOrd, Joint E r ∧ (∀ d, min (r d) γ = min (a d) γ) ∧
      ∀ d : Option X, r (.inl d) = FreeDiagonal.append p v d := by
  classical
  by_cases hreach : ∃ d : Option X, γ ≤ FreeDiagonal.append p v d
  swap
  · refine ⟨a, ha, fun _ => rfl, ?_⟩
    intro d
    have hd : FreeDiagonal.append p v d < γ := lt_of_not_ge (fun h => hreach ⟨d, h⟩)
    exact ((cap_eq_iff_profile _ _ _).mp (hag d)).1 hd
  obtain ⟨j, hact, hface⟩ := active_whole_face_coverage ha hp hv horder hbot hag hreach
  let q : Occ X → ExtOrd := fun d => min (a d) γ
  have htrace : TransformsTo (fun _ : Occ X => 1) (row E j) q := by
    have ht := (ha.2.1 j).cap (fun _ => le_rfl) hγ
    have he : ∀ d, min (min (a d) (a (controller j))) γ = min (a d) γ := by
      intro d
      rw [min_assoc, min_eq_right hact]
    simpa only [he] using ht
  have hpvis : ∀ d : Option X, SelfVis 1 (FreeDiagonal.append p v d) := by
    rintro (_ | d)
    · exact hv
    · exact hp d
  have hqvis : ∀ d, SelfVis 1 (q d) := fun d => selfVis_min (ha.1 d) hγ
  have hcheck : Propagation.Check (row E j) Sum.inl (FreeDiagonal.append p v) q γ :=
    Propagation.check_of_compatible_order (transform_order hface) (transform_order htrace)
      (transform_bottom hface) (transform_bottom htrace)
      (fun d => by simpa only [q, min_assoc, min_self] using hag d)
  let r := Propagation.close (row E j) Sum.inl (FreeDiagonal.append p v) q γ
  have hrvis : ∀ d, SelfVis 1 (r d) :=
    Propagation.close_visible (row E j) Sum.inl hpvis hqvis hγ
  refine ⟨r, ordered_joint E j r hrvis hcheck.2.2
    (fun _ _ h => Propagation.close_order _ _ _ _ _ h), ?_, ?_⟩
  · intro d
    have hh : min (r d) γ = min (q d) γ := by
      apply (cap_eq_iff_profile _ _ _).mpr
      constructor
      · intro hd
        apply le_antisymm (hcheck.1 d hd)
        have hl := Propagation.cap_le_close (row E j) Sum.inl (FreeDiagonal.append p v) q γ d
        rwa [min_eq_left hd.le] at hl
      · intro hd
        have hl := Propagation.cap_le_close (row E j) Sum.inl (FreeDiagonal.append p v) q γ d
        rwa [min_eq_right hd] at hl
    simpa only [q, min_assoc, min_self] using hh
  · intro d
    exact le_antisymm (hcheck.2.1 d)
      (Propagation.prescribed_le_close (row E j) Sum.inl (FreeDiagonal.append p v) q γ d)

section ActualDonor

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {o : Cell D} [Fintype (D.below (D.cell o))]

/-- The source-order and bottom conditions come from actual old lawfulness
at a unique grade-one donor, not from a restriction on the prescribed labels. -/
theorem lawful_lift {p : D.below (D.cell o) → ExtOrd} {v γ : ExtOrd}
    {a : Occ (D.below (D.cell o)) → ExtOrd}
    (ha : Joint (sem.E o) a) (hp : RespectsSemanticsBelow sem (D.cell o) p)
    (hu : DonorSourceRefinement.UniqueAt o) (ho : D.grade o = 1)
    (hv : SelfVis 1 v) (hγ : SelfVis 1 γ)
    (hag : ∀ d : Option (D.below (D.cell o)),
      min (a (.inl d)) γ = min (FreeDiagonal.append p v d) γ) :
    ∃ r : Occ (D.below (D.cell o)) → ExtOrd, Joint (sem.E o) r ∧
      (∀ d, min (r d) γ = min (a d) γ) ∧
      ∀ d : Option (D.below (D.cell o)), r (.inl d) = FreeDiagonal.append p v d := by
  apply lift ha
  · intro d
    simpa only [DonorFreshSlots.grade_one ho d] using (hp.orderly d).symm
  · exact hv
  · exact hγ
  · exact DonorFreshSlots.lawful_order hp hu ho
  · exact DonorFreshSlots.lawful_bottom hp hu ho
  · exact hag

end ActualDonor

end VaughtConjecture.Knight.SlotCappedLifting
