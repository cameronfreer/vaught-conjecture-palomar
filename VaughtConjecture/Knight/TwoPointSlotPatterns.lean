/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ThreePointSlotProfiles

/-! # The two exact order cones of the slot domain

This exposes the complete lawful-label criterion used to refine a three-point
boundary below and above a source cut. All four grade-one occurrences remain
in the criterion; neither competing controller is suppressed.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.TwoPointSlotPatterns

open Transform Value ExtOrd SlotControllerFamily

def Pattern {α : Type*} [LE α] (p : Fin 5 → α) : Prop :=
  (p 1 = p 3 ∧ p 1 ≤ p 0 ∧ p 0 ≤ p 2) ∨
  (p 0 = p 2 ∧ p 0 ≤ p 1 ∧ p 1 ≤ p 3)

def sourceIndex (c : Fin 2) : Fin 5 → ℕ :=
  if c = 0 then ![2, 1, 6, 1, 0] else ![2, 3, 2, 6, 0]

private theorem index_table (c : Fin 2) (d : TwoPointSlots.Inventory) :
    index c (DonorSlotAssembly.position TwoPointSlots.source d) =
      sourceIndex c (TwoPointSlots.embed d) := by
  fin_cases c <;> fin_cases d <;>
    simp [DonorSlotAssembly.position, TwoPointSlots.source, TwoPointSlots.embed,
      FreshSourceSlots.rank, SeparatedGradeOne.band, sourceIndex, index,
      SlotControllerFamily.old, SlotControllerFamily.fresh, SlotControllerFamily.controller,
      cross, height]

theorem source_respects (c : Fin 2) :
    RespectsSemantics TwoPointSlots.rows (fun d => value (sourceIndex c d)) := by
  have hh := TwoPointSlots.extend_respects (DonorSlotAssembly.rows_joint TwoPointSlots.source c)
  have he : TwoPointSlots.extend (DonorSlotAssembly.row TwoPointSlots.source c) =
      fun d => value (sourceIndex c d) := by
    funext d
    by_cases hd : d = 4
    · subst d
      fin_cases c <;> rfl
    · change (if d = 4 then ⊥ else value
        (index c (DonorSlotAssembly.position TwoPointSlots.source (TwoPointSlots.project d)))) = _
      rw [ite_eq_right hd, index_table, TwoPointSlots.embed_project d hd]
  rwa [he] at hh

theorem pattern_of_respects {p : Fin 5 → ExtOrd}
    (hp : RespectsSemantics TwoPointSlots.rows p) : Pattern p := by
  have hj := TwoPointSlots.joint_of_respects (by decide : 1 ≤ 2)
    (hp.toBelow (Finset.univ, 2))
  obtain ⟨c, f, hf, _, _, he⟩ := hj.exists_shape
  have he' (d : Fin 5) (hd : d ≠ 4) : p d = f (sourceIndex c d) := by
    have hh := he (TwoPointSlots.project d)
    change p (TwoPointSlots.embed (TwoPointSlots.project d)) = _ at hh
    simpa only [TwoPointSlots.embed_project d hd] using
      hh.trans (congrArg f (index_table c (TwoPointSlots.project d)))
  have h0 := he' 0 (by decide)
  have h1 := he' 1 (by decide)
  have h2 := he' 2 (by decide)
  have h3 := he' 3 (by decide)
  fin_cases c
  · left
    exact ⟨h1.trans h3.symm, h1.trans_le ((hf (by decide : 1 ≤ 2)).trans_eq h0.symm),
      h0.trans_le ((hf (by decide : 2 ≤ 6)).trans_eq h2.symm)⟩
  · right
    exact ⟨h0.trans h2.symm, h0.trans_le ((hf (by decide : 2 ≤ 3)).trans_eq h1.symm),
      h1.trans_le ((hf (by decide : 3 ≤ 6)).trans_eq h3.symm)⟩

theorem respects_of_pattern {p : Fin 5 → ExtOrd} (hv : ∀ d, SelfVis 1 (p d))
    (hb : p 4 = ⊥) (hp : Pattern p) : RespectsSemantics TwoPointSlots.rows p := by
  rcases hp with ⟨htie, hlo, hhi⟩ | ⟨htie, hlo, hhi⟩
  · apply ThreePointSlotProfiles.respects_of_order (source_respects 0) hv
    · intro d hd
      fin_cases d <;> simp_all [sourceIndex, value, SeparatedGradeOne.band]
    · intro d e hde
      have h02 := hlo.trans hhi
      have hh := (value_le_iff _ _).mp hde
      fin_cases d <;> fin_cases e <;>
        simp_all [sourceIndex]
  · apply ThreePointSlotProfiles.respects_of_order (source_respects 1) hv
    · intro d hd
      fin_cases d <;> simp_all [sourceIndex, value, SeparatedGradeOne.band]
    · intro d e hde
      have h03 := hlo.trans hhi
      have hh := (value_le_iff _ _).mp hde
      fin_cases d <;> fin_cases e <;>
        simp_all [sourceIndex]

theorem respects_iff (p : Fin 5 → ExtOrd) :
    RespectsSemantics TwoPointSlots.rows p ↔
      (∀ d, SelfVis 1 (p d)) ∧ p 4 = ⊥ ∧ Pattern p := by
  refine ⟨fun hp => ⟨?_, ?_, pattern_of_respects hp⟩, fun h => respects_of_pattern h.1 h.2.1 h.2.2⟩
  · intro d
    exact selfVis_mono (hp.orderly d).symm (by
      have hh : ∀ d : Fin 5, 1 ≤ TwoPointSlots.scheme.grade d := by decide
      exact hh d)
  · exact TwoPointSlots.mute_label (hp.toBelow (Finset.univ, 2)) (by
      unfold GradedLe
      decide)

end VaughtConjecture.Knight.TwoPointSlotPatterns
