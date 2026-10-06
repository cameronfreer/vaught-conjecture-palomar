/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SeparatedGradeOneCoding
public import VaughtConjecture.Knight.MixedGradeInterpolation
public import VaughtConjecture.Knight.FreeDiagonal

/-! # A finite family of source slots for an independent grade-one reading

Old source values are ranked once, before any output labels are supplied.
Their nonbottom codes occupy even blocks; odd blocks provide fresh slots.
Every source-ordered old target and every visible fresh target fit one slot.
An explicit finite maximum of step witnesses decodes all targets literally.
Bottom, top, and ties are allowed. There is no composition of transformations.

These are row templates, not jointly consistent controllers. Simultaneous
family incidences, availability, and reference readback remain separate.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.FreshSourceSlots

open Transform Value ExtOrd SeparatedGradeOne

local notation "band" => SeparatedGradeOne.band

theorem band_lt {m n : ℕ} (h : m < n) : band m < band n :=
  ofOrd_lt_ofOrd.mpr ((code_add_lt_mul (Nat.cast_lt.mpr h) 1).trans_le le_self_add)

theorem band_le_iff (m n : ℕ) : band m ≤ band n ↔ m ≤ n := by
  constructor
  · intro h
    by_contra hn
    exact (not_le_of_gt (band_lt (not_le.mp hn))) h
  · exact band_mono

noncomputable def source : Option ℕ → ExtOrd
  | none => ⊥
  | some n => band n

theorem source_visible (n : Option ℕ) : SelfVis 1 (source n) := by
  cases n with
  | none => exact selfVis_bot _
  | some n => exact band_visible n

theorem source_coded (n : Option ℕ) : IsCodedLabel 1 (source n) := by
  cases n with
  | none => exact Or.inl rfl
  | some n => exact band_coded n 1

theorem step_band (m n : ℕ) (v : ExtOrd) :
    stepShifter m ⊥ v (band n) = if m ≤ n then v else ⊥ := by
  classical
  by_cases h : m ≤ n
  · rw [ite_eq_left h]
    apply stepShifter_of_ge
    exact ofOrd_le_ofOrd.mpr ((mul_le_mul_right (Nat.cast_le.mpr h) _).trans le_self_add)
  · rw [ite_eq_right h]
    apply stepShifter_of_lt (ofOrd_ne_bot _)
    exact ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (not_le.mp h)) 1)

section Decoder

variable {X : Type*} [Fintype X]

noncomputable def decoder (r : X → Option ℕ) (t : X → ExtOrd) (x : ExtOrd) : ExtOrd :=
  Finset.univ.sup fun d => match r d with
    | none => ⊥
    | some n => stepShifter n ⊥ (t d) x

theorem decoder_witness (r : X → Option ℕ) (t : X → ExtOrd)
    (hv : ∀ d, SelfVis 1 (t d)) : Witness (gTop 1) (decoder r t) := by
  apply Witness.finset_sup (MixedGradeInterpolation.zero_witness 1)
  intro d _
  cases h : r d with
  | none => simpa only [h] using MixedGradeInterpolation.zero_witness 1
  | some n =>
    simpa only [h] using Witness.stepLimit 1 n bot_le (selfVis_bot 1) (hv d)

theorem decoder_read (r : X → Option ℕ) (t : X → ExtOrd)
    (horder : ∀ d e, source (r d) ≤ source (r e) → t d ≤ t e)
    (hbot : ∀ d, r d = none → t d = ⊥) (d : X) : decoder r t (source (r d)) = t d := by
  classical
  cases hd : r d with
  | none =>
    simp only [source, decoder, hbot d hd]
    apply le_antisymm _ bot_le
    apply Finset.sup_le
    intro e _
    cases r e <;> simp only [stepShifter_bot, le_refl]
  | some n =>
    change decoder r t (band n) = t d
    apply le_antisymm
    · apply Finset.sup_le
      intro e _
      cases he : r e with
      | none => exact bot_le
      | some m =>
        change stepShifter m ⊥ (t e) (band n) ≤ t d
        rw [step_band]
        split_ifs with h
        · exact horder e d (by rw [he, hd]; exact band_mono h)
        · exact bot_le
    · have h := Finset.le_sup (s := Finset.univ)
        (f := fun e => match r e with
          | none => (⊥ : ExtOrd)
          | some m => stepShifter m ⊥ (t e) (band n)) (Finset.mem_univ d)
      simpa only [hd, step_band, le_refl, ↓reduceIte, decoder] using h

end Decoder

section Slots

variable {X : Type*} [Fintype X]

open Classical in
/-- Rank counts occurrences, not a quotient. Equal old values still get equal ranks. -/
noncomputable def rank (E : X → ExtOrd) (d : X) : ℕ :=
  (Finset.univ.filter fun e => E e < E d).card

theorem rank_mono {E : X → ExtOrd} {d e : X} (h : E d ≤ E e) : rank E d ≤ rank E e := by
  classical
  apply Finset.card_le_card
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.trans_le h⟩

theorem rank_strict {E : X → ExtOrd} {d e : X} (h : E d < E e) : rank E d < rank E e := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.trans h⟩
  · intro heq
    have hd : d ∈ Finset.univ.filter (fun a => E a < E e) := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h
    rw [← heq] at hd
    exact (lt_irrefl (E d)) (Finset.mem_filter.mp hd).2

theorem rank_le_iff (E : X → ExtOrd) (d e : X) : rank E d ≤ rank E e ↔ E d ≤ E e := by
  constructor
  · intro h
    by_contra hn
    exact (not_le_of_gt (rank_strict (not_le.mp hn))) h
  · exact rank_mono

theorem rank_lt_card (E : X → ExtOrd) (d : X) : rank E d < Fintype.card X := by
  classical
  change (Finset.univ.filter fun e => E e < E d).card < Finset.univ.card
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have hd : d ∈ Finset.univ.filter (fun e => E e < E d) := heq.symm ▸ Finset.mem_univ d
  exact (lt_irrefl (E d)) (Finset.mem_filter.mp hd).2

open Classical in
noncomputable def oldBlock (E : X → ExtOrd) (d : X) : Option ℕ :=
  if E d = ⊥ then none else some (2 * rank E d + 2)

noncomputable def oldSource (E : X → ExtOrd) (d : X) : ExtOrd := source (oldBlock E d)

theorem oldSource_bot_iff (E : X → ExtOrd) (d : X) : oldSource E d = ⊥ ↔ E d = ⊥ := by
  classical
  by_cases h : E d = ⊥ <;> simp [oldSource, oldBlock, source, h, SeparatedGradeOne.band]

theorem oldSource_le_iff (E : X → ExtOrd) (d e : X) :
    oldSource E d ≤ oldSource E e ↔ E d ≤ E e := by
  classical
  by_cases hd : E d = ⊥
  · simp [oldSource, oldBlock, source, hd]
  by_cases he : E e = ⊥
  · simp [oldSource, oldBlock, source, hd, he, SeparatedGradeOne.band]
  simp only [oldSource, oldBlock, ite_eq_right hd, ite_eq_right he, source, band_le_iff]
  rw [← rank_le_iff E d e]
  omega

noncomputable def blocks (E : X → ExtOrd) (j : ℕ) : Option X → Option ℕ
  | none => some (2 * j + 1)
  | some d => oldBlock E d

noncomputable def row (E : X → ExtOrd) (j : ℕ) (d : Option X) : ExtOrd := source (blocks E j d)

theorem fresh_ne_old (E : X → ExtOrd) (j : ℕ) (d : X) : row E j none ≠ row E j (some d) := by
  classical
  by_cases hd : E d = ⊥
  · simp [row, blocks, oldBlock, source, hd, SeparatedGradeOne.band]
  · intro h
    have hf : band (2 * j + 1) = band (2 * rank E d + 2) := by
      simpa only [row, blocks, oldBlock, ite_eq_right hd, source] using h
    have h1 := (band_le_iff _ _).mp hf.le
    have h2 := (band_le_iff _ _).mp hf.ge
    omega

open Classical in
/-- The slot is computed from a finite lower cut in the output order. -/
noncomputable def chooseSlot (E q : X → ExtOrd) (v : ExtOrd) : ℕ :=
  Finset.univ.sup fun d => if E d ≠ ⊥ ∧ q d < v then rank E d + 1 else 0

theorem chooseSlot_le (E q : X → ExtOrd) (v : ExtOrd) : chooseSlot E q v ≤ Fintype.card X := by
  classical
  apply Finset.sup_le
  intro d _
  split_ifs
  · exact Nat.succ_le_of_lt (rank_lt_card E d)
  · exact Nat.zero_le _

theorem before_slot {E q : X → ExtOrd} {v : ExtOrd}
    (horder : ∀ d e, E d ≤ E e → q d ≤ q e) {d : X}
    (hd : rank E d < chooseSlot E q v) : q d ≤ v := by
  classical
  obtain ⟨e, _, he⟩ := Finset.lt_sup_iff.mp hd
  split_ifs at he with h
  · have hr : rank E d ≤ rank E e := by omega
    exact (horder d e ((rank_le_iff E d e).mp hr)).trans h.2.le
  · omega

theorem after_slot {E q : X → ExtOrd} {v : ExtOrd} {d : X}
    (hn : E d ≠ ⊥) (hd : chooseSlot E q v ≤ rank E d) : v ≤ q d := by
  classical
  by_contra h
  have ht := Finset.le_sup (s := Finset.univ)
    (f := fun e => if E e ≠ ⊥ ∧ q e < v then rank E e + 1 else 0) (Finset.mem_univ d)
  rw [ite_eq_left ⟨hn, not_le.mp h⟩] at ht
  change rank E d + 1 ≤ chooseSlot E q v at ht
  omega

/-- The computed slot fits the full old table and the independent fresh target. -/
theorem chosen_order {E q : X → ExtOrd} (v : ExtOrd)
    (horder : ∀ d e, E d ≤ E e → q d ≤ q e) (hbot : ∀ d, E d = ⊥ → q d = ⊥) :
    ∀ d e : Option X, row E (chooseSlot E q v) d ≤ row E (chooseSlot E q v) e →
      FreeDiagonal.append q v d ≤ FreeDiagonal.append q v e := by
  classical
  intro d e h
  cases d with
  | none =>
    cases e with
    | none => exact le_rfl
    | some e =>
      by_cases he : E e = ⊥
      · have hh : band (2 * chooseSlot E q v + 1) ≤ ⊥ := by
          simpa only [row, blocks, oldBlock, ite_eq_left he, source] using h
        exact False.elim ((not_ofOrd_le_bot _) hh)
      · have hh : 2 * chooseSlot E q v + 1 ≤ 2 * rank E e + 2 := by
          apply (band_le_iff _ _).mp
          simpa only [row, blocks, oldBlock, ite_eq_right he, source] using h
        change v ≤ q e
        exact after_slot he (by omega)
  | some d =>
    cases e with
    | none =>
      by_cases hd : E d = ⊥
      · change q d ≤ v
        rw [hbot d hd]
        exact bot_le
      · have hh : 2 * rank E d + 2 ≤ 2 * chooseSlot E q v + 1 := by
          apply (band_le_iff _ _).mp
          simpa only [row, blocks, oldBlock, ite_eq_right hd, source] using h
        change q d ≤ v
        exact before_slot horder (by omega)
    | some e => exact horder d e ((oldSource_le_iff E d e).mp h)

/-- A finite, prechosen family covers every ordered old input with any fresh
visible value. Slot choice changes no old source and no output label. -/
theorem exists_slot {E q : X → ExtOrd} {v : ExtOrd}
    (hq : ∀ d, SelfVis 1 (q d)) (hv : SelfVis 1 v)
    (horder : ∀ d e, E d ≤ E e → q d ≤ q e) (hbot : ∀ d, E d = ⊥ → q d = ⊥) :
    ∃ j : Fin (Fintype.card X + 1),
      TransformsTo (fun _ : Option X => 1) (row E j.val) (FreeDiagonal.append q v) := by
  classical
  let j := chooseSlot E q v
  have hbottom : ∀ d : Option X, blocks E j d = none → FreeDiagonal.append q v d = ⊥ := by
    rintro (_ | d) h
    · cases h
    · have hd : E d = ⊥ := by
        by_contra hd
        simp only [blocks, oldBlock, ite_eq_right hd, Option.some_ne_none] at h
      exact hbot d hd
  have hvisible : ∀ d : Option X, SelfVis 1 (FreeDiagonal.append q v d) := by
    rintro (_ | d)
    · exact hv
    · exact hq d
  refine ⟨⟨j, Nat.lt_succ_of_le (chooseSlot_le E q v)⟩, ?_⟩
  apply (decoder_witness (blocks E j) (FreeDiagonal.append q v) hvisible).transformsTo
  intro d
  rw [gTop_of_le le_rfl, min_top_right]
  exact (decoder_read (blocks E j) (FreeDiagonal.append q v)
    (chosen_order v horder hbot) hbottom d).symm

/-- A source-only diagonal strictly above every source in every allowed slot. -/
noncomputable def ownerBlock (X : Type*) [Fintype X] : ℕ := 2 * Fintype.card X + 4

theorem row_lt_owner (E : X → ExtOrd) (j : Fin (Fintype.card X + 1)) (d : Option X) :
    row E j.val d < band (ownerBlock X) := by
  classical
  cases d with
  | none =>
    apply band_lt
    have hj := j.isLt
    unfold ownerBlock
    omega
  | some d =>
    by_cases hd : E d = ⊥
    · simp only [row, blocks, oldBlock, ite_eq_left hd, source]
      exact bot_lt_ofOrd _
    · simp only [row, blocks, oldBlock, ite_eq_right hd, source]
      apply band_lt
      have hr := rank_lt_card E d
      unfold ownerBlock
      omega

/-- The same chosen slot also admits an independent dominating owner label.
This appends a row occurrence, not a controller in an enlarged scheme. -/
theorem exists_slot_with_owner {E q : X → ExtOrd} {v U : ExtOrd}
    (hq : ∀ d, SelfVis 1 (q d)) (hv : SelfVis 1 v) (hU : SelfVis 1 U)
    (horder : ∀ d e, E d ≤ E e → q d ≤ q e) (hbot : ∀ d, E d = ⊥ → q d = ⊥)
    (hqU : ∀ d, q d ≤ U) (hvU : v ≤ U) :
    ∃ j : Fin (Fintype.card X + 1),
      TransformsTo (fun _ : Option (Option X) => 1)
        (FreeDiagonal.append (row E j.val) (band (ownerBlock X)))
        (FreeDiagonal.append (FreeDiagonal.append q v) U) := by
  classical
  let j : Fin (Fintype.card X + 1) :=
    ⟨chooseSlot E q v, Nat.lt_succ_of_le (chooseSlot_le E q v)⟩
  let r := FreeDiagonal.append (blocks E j.val) (some (ownerBlock X))
  let t := FreeDiagonal.append (FreeDiagonal.append q v) U
  have hr : ∀ d, source (r d) =
      FreeDiagonal.append (row E j.val) (band (ownerBlock X)) d := by
    rintro (_ | d) <;> rfl
  have ht : ∀ d, SelfVis 1 (t d) := by
    rintro (_ | (_ | d))
    · exact hU
    · exact hv
    · exact hq d
  have hb : ∀ d, r d = none → t d = ⊥ := by
    rintro (_ | (_ | d)) h
    · cases h
    · cases h
    · change oldBlock E d = none at h
      by_cases hd : E d = ⊥
      · exact hbot d hd
      · simp only [oldBlock, ite_eq_right hd, Option.some_ne_none] at h
  have ho : ∀ d e, source (r d) ≤ source (r e) → t d ≤ t e := by
    intro d e h
    rw [hr d, hr e] at h
    cases d with
    | none =>
      cases e with
      | none => exact le_rfl
      | some e => exact False.elim ((not_le_of_gt (row_lt_owner E j e)) h)
    | some d =>
      cases e with
      | none =>
        cases d with
        | none => exact hvU
        | some d => exact hqU d
      | some e => exact chosen_order v horder hbot d e h
  refine ⟨j, (decoder_witness r t ht).transformsTo ?_⟩
  intro d
  rw [gTop_of_le le_rfl, min_top_right, ← hr d]
  exact (decoder_read r t ho hb d).symm

end Slots

end VaughtConjecture.Knight.FreshSourceSlots
