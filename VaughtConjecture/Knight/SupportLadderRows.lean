/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LongGuardRows
public import VaughtConjecture.Knight.FiniteProfileControllers

/-! # Physical support ladders

The rung of height `t ≥ 2` puts ranks `t - 1` and `t` in the same
source block, at offsets one and two. Every rung is an actual row owner;
unused field ranks are not omitted. These are the ladder rows of
`newapproach4` / `newapproach5`, with their original odd-block encoding.

This module concerns the complete row table. Installation on mixed supports
and grade-two numerical receiving remain separate obligations.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.SupportLadderRows

open Transform Value ExtOrd FiniteProfileControllers

/-- The exact source code used by a rung, including its long diagonal. -/
noncomputable def source (t i : ℕ) : ExtOrd :=
  if t ≤ 1 then SlotControllerFamily.value (2 * min i t - 1)
  else LongGuardRows.source (2 * t - 3) (2 * min i t - 1)

theorem source_visible (t i : ℕ) : SelfVis 1 (source t i) := by
  unfold source
  split_ifs
  · exact SlotControllerFamily.value_visible _
  · exact LongGuardRows.source_visible _ _

theorem source_coded (t i : ℕ) : IsCodedLabel 1 (source t i) := by
  unfold source
  split_ifs
  · exact SlotControllerFamily.value_coded _
  · exact LongGuardRows.source_coded _ _

theorem source_le_iff (t i j : ℕ) :
    source t i ≤ source t j ↔ min i t ≤ min j t := by
  unfold source
  split_ifs with ht
  · rw [SlotControllerFamily.value_le_iff]
    omega
  · rw [LongGuardRows.source_le_iff]
    omega

theorem source_mono (t : ℕ) : Monotone (source t) :=
  fun _ _ h => (source_le_iff _ _ _).mpr (min_le_min_right _ h)

@[simp] theorem source_zero (t : ℕ) : source t 0 = ⊥ := by
  simp [source, SlotControllerFamily.value]

theorem source_bot_iff (t i : ℕ) : source t i = ⊥ ↔ min i t = 0 := by
  have h := source_le_iff t i 0
  simpa only [source_zero, le_bot_iff, Nat.zero_min, Nat.le_zero] using h

theorem source_floor_bot_iff (t i : ℕ) :
    blockFloor (source t i) = ⊥ ↔ source t i = ⊥ := by
  unfold source LongGuardRows.source SlotControllerFamily.value
  split_ifs <;>
    simp [LongGuardRows.endpoint,
      blockFloor_ofOrd, SeparatedGradeOne.band]

/-- Adjacent actual rungs share the decisive short/long source block. -/
theorem predecessor_block {t : ℕ} (ht : 2 ≤ t) :
    blockFloor (source t (t - 1)) = blockFloor (source t t) := by
  have h1 : ¬t ≤ 1 := by omega
  have h2 : 2 * min (t - 1) t - 1 = 2 * t - 3 := by omega
  have h3 : ¬2 * min t t - 1 ≤ 2 * t - 3 := by omega
  have h4 : 2 * t - 3 ≠ 0 := by omega
  simp only [source, ite_eq_right h1, h2, LongGuardRows.source,
    le_refl, ite_true, ite_eq_right h3, SlotControllerFamily.value,
    ite_eq_right h4, SeparatedGradeOne.band_floor,
    LongGuardRows.endpoint, blockFloor_ofOrd, limitPart_code]

/-- Positive visible tables have faithful locality at every rung. The
source-block test includes the long diagonal, not just bounded commutation. -/
theorem transforms_positive {Y : Type*} [Finite Y] (a : Y → ℕ) (t : ℕ)
    (f : ℕ → ExtOrd) (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, SelfVis 1 (f i)) (hp : ∀ i, 0 < i → i ≤ t → f i ≠ ⊥) :
    TransformsTo (fun _ : Y => 1) (fun d => source t (a d))
      (fun d => f (min (a d) t)) := by
  apply LongGuardRows.transforms_of_visible_table
    (fun _ => source_visible _ _) (fun _ => hv _)
  · intro d e hde
    exact hf ((source_le_iff _ _ _).mp hde)
  · intro d hd
    rw [(source_bot_iff _ _).mp hd, h0]
  · intro d e hde hd
    have hz : min (a d) t = 0 := by
      by_contra hn
      exact hp _ (Nat.pos_of_ne_zero hn) (min_le_right _ _) hd
    have hs : source t (a d) = ⊥ := (source_bot_iff _ _).mpr hz
    rw [hs, blockFloor_bot] at hde
    have he := (source_floor_bot_iff _ _).mp hde.symm
    rw [(source_bot_iff _ _).mp he, h0]

theorem source_min (t i : ℕ) : source t (min i t) = source t i := by
  simp only [source, min_assoc, min_self]

/-- The short entries agree literally with the exported odd-block codes. -/
theorem source_short {t i : ℕ} (hi : i ≤ t) (hs : i < t ∨ t ≤ 1) :
    source t i = SlotControllerFamily.value (2 * i - 1) := by
  unfold source
  rw [min_eq_left hi]
  split_ifs with ht
  · rfl
  · unfold LongGuardRows.source
    rw [ite_eq_left (by omega : 2 * i - 1 ≤ 2 * t - 3)]

/-- The diagonal at height at least two is the preceding odd block's long
endpoint, not a short code in the next block. -/
theorem source_diagonal {t : ℕ} (ht : 2 ≤ t) :
    source t t = LongGuardRows.endpoint (2 * t - 3) := by
  simp only [source, ite_eq_right (by omega : ¬t ≤ 1), min_self,
    LongGuardRows.source, ite_eq_right (by omega : ¬2 * t - 1 ≤ 2 * t - 3)]

variable {X Q : Type*} {H : ℕ} {profile : Q → X → ℕ}

/-- Every rank has a separate rung, even when no original field uses it.
Shadows are separate occurrences, including rank-zero shadows. -/
abbrev Point (H : ℕ) (X Q : Type*) := Q × (Fin H ⊕ X)

def parent (v : Point H X Q) : Q := v.1

def ceiling (profile : Q → X → ℕ) (v : Point H X Q) : ℕ :=
  match v.2 with
  | .inl i => i.val + 1
  | .inr d => profile v.1 d

def rung (a : Q) (i : Fin H) : Point H X Q := (a, .inl i)
def shadow (a : Q) (d : X) : Point H X Q := (a, .inr d)
def leaf (hH : 0 < H) (a : Q) : Point H X Q := rung a ⟨H - 1, by omega⟩

noncomputable def index (profile : Q → X → ℕ) (a : Q) (v : Point H X Q) : ℕ :=
  min (cut H (profile a) (profile (parent v))) (ceiling profile v)

noncomputable def row (profile : Q → X → ℕ) (c v : Point H X Q) : ExtOrd :=
  source (ceiling profile c) (index profile (parent c) v)

noncomputable def image (profile : Q → X → ℕ) (a : Q) (f : ℕ → ExtOrd)
    (v : Point H X Q) : ExtOrd := f (index profile a v)

def Lawful (profile : Q → X → ℕ) (q : Point H X Q → ExtOrd) : Prop :=
  (∀ v, SelfVis 1 (q v)) ∧ ∀ c,
    TransformsTo (fun _ : Point H X Q => 1) (row profile c) (fun v => min (q v) (q c))

theorem ceiling_le (hbound : ∀ a d, profile a d ≤ H) (v : Point H X Q) :
    ceiling profile v ≤ H := by
  rcases v with ⟨a, i | d⟩
  · exact i.isLt
  · exact hbound a d

theorem index_le (a : Q) (v : Point H X Q) : index profile a v ≤ H :=
  (min_le_left _ _).trans (cut_le _ _ _)

@[simp] theorem index_rung (a : Q) (i : Fin H) :
    index profile a (rung a i) = i.val + 1 := by
  simp only [index, rung, parent, ceiling, cut_refl,
    min_eq_right (show i.val + 1 ≤ H from i.isLt)]

@[simp] theorem ceiling_leaf (hH : 0 < H) (a : Q) :
    ceiling profile (leaf (X := X) hH a) = H := by
  change H - 1 + 1 = H
  omega

@[simp] theorem index_leaf (hH : 0 < H) (a b : Q) :
    index profile a (leaf (X := X) hH b) = cut H (profile a) (profile b) := by
  rw [index, ceiling_leaf]
  exact min_eq_left (cut_le _ _ _)

theorem index_diagonal (hbound : ∀ a d, profile a d ≤ H) (c : Point H X Q) :
    index profile (parent c) c = ceiling profile c := by
  rw [index, cut_refl, min_eq_right (ceiling_le hbound c)]

/-- Whole-coordinate agreement includes every unused rung and every shadow. -/
theorem index_agreement (a b : Q) (v : Point H X Q) :
    min (index profile a v) (cut H (profile a) (profile b)) =
      min (index profile b v) (cut H (profile a) (profile b)) := by
  unfold index
  calc
    _ = min (min (cut H (profile a) (profile (parent v)))
        (cut H (profile a) (profile b))) (ceiling profile v) := by ac_rfl
    _ = min (min (cut H (profile b) (profile (parent v)))
        (cut H (profile a) (profile b))) (ceiling profile v) := by rw [cross_agreement]
    _ = _ := by ac_rfl

theorem image_cap_eq (a : Q) {f : ℕ → ExtOrd} (hf : Monotone f)
    (c v : Point H X Q) :
    min (image profile a f v) (image profile a f c) =
      f (min (index profile (parent c) v) (index profile a c)) := by
  rw [image, image, ← hf.map_min]
  change f (min (index profile a v) (min _ _)) = _
  rw [← min_assoc, index_agreement, min_assoc]
  rfl

theorem row_coded (c v : Point H X Q) : IsCodedLabel 1 (row profile c v) :=
  source_coded _ _

theorem row_visible (c v : Point H X Q) : SelfVis 1 (row profile c v) :=
  source_visible _ _

variable [Finite X] [Finite Q]

/-- A positive ordered scalar table receives every physical rung at its own
cap, including all long diagonals and all unused ranks. -/
theorem image_lawful (a : Q) (f : ℕ → ExtOrd) (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, SelfVis 1 (f i)) (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥) :
    Lawful (H := H) profile (image profile a f) := by
  refine ⟨fun _ => hv _, ?_⟩
  intro c
  have he := funext (image_cap_eq (profile := profile) a hf c)
  rw [he]
  let e := index profile a c
  have het : e ≤ ceiling profile c := min_le_right _ _
  by_cases hz : e = 0
  · have hzero : (fun v : Point H X Q => f (min (index profile (parent c) v) e)) =
        fun _ => ⊥ := by simp [hz, h0]
    change TransformsTo _ _ (fun v => f (min (index profile (parent c) v) e))
    rw [hzero]
    exact TransformsTo.to_bot _
  · have ht := transforms_positive (index (H := H) profile (parent c)) (ceiling profile c)
        (fun i => f (min i e))
        (fun _ _ h => hf (min_le_min_right _ h)) (by simpa using h0)
        (fun _ => hv _) (fun i hi _ => hp _ (by omega) ((min_le_right _ _).trans (index_le a c)))
    change TransformsTo _ (fun v => source (ceiling profile c) (index profile (parent c) v))
      (fun v => f (min (index profile (parent c) v) e))
    simpa only [min_assoc, min_eq_right het] using ht

/-- Every row of the table is lawful on the entire table. No future
availability or locality is assumed. -/
theorem rows_lawful (c : Point H X Q) : Lawful profile (row profile c) := by
  by_cases ht : ceiling profile c = 0
  · have he : row profile c = fun _ => ⊥ := by
      funext v
      exact (source_bot_iff _ _).mpr (by simp [ht])
    rw [he]
    exact ⟨fun _ => selfVis_bot _, fun _ => by
      simp only [min_self]
      exact TransformsTo.to_bot _⟩
  · exact image_lawful (parent c) (source (ceiling profile c)) (source_mono _)
      (source_zero _) (source_visible _) (fun i hi _ hz => by
        have h := (source_bot_iff _ _).mp hz
        omega)

omit [Finite X] [Finite Q] in
theorem row_parent (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H)
    (c : Point H X Q) :
    row profile c (leaf hH (parent c)) = row profile c c := by
  rw [row, row, index_leaf, cut_refl, index_diagonal hbound]
  have h := source_min (ceiling profile c) H
  rw [min_eq_right (ceiling_le hbound c)] at h
  exact h.symm

omit [Finite X] [Finite Q] in
/-- Locality at the auxiliary itself bounds it by its actual parent leaf. -/
theorem Lawful.le_parent {q : Point H X Q → ExtOrd} (hq : Lawful profile q)
    (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H) (c : Point H X Q) :
    q c ≤ q (leaf hH (parent c)) := by
  obtain ⟨g, σ, _, _, _, _, _, hr⟩ := hq.2 c
  apply min_eq_right_iff.mp
  calc
    min (q (leaf hH (parent c))) (q c) =
        min (σ (row profile c (leaf hH (parent c)))) (g 1) := hr _
    _ = min (σ (row profile c c)) (g 1) := by rw [row_parent hbound hH]
    _ = q c := by simpa only [min_self] using (hr c).symm

omit [Finite X] [Finite Q] in
/-- An actual long rung forbids a zero predecessor and a positive diagonal.
No field need occupy either rank. -/
theorem Lawful.predecessor_bot {q : Point H X Q → ExtOrd} (hq : Lawful profile q)
    (a : Q) {i : ℕ} (hi : 0 < i) (hiH : i < H)
    (hz : q (rung a ⟨i - 1, by omega⟩) = ⊥) : q (rung a ⟨i, hiH⟩) = ⊥ := by
  let c : Point H X Q := rung a ⟨i, hiH⟩
  let d : Point H X Q := rung a ⟨i - 1, by omega⟩
  have hb : blockFloor (row profile c d) = blockFloor (row profile c c) := by
    change blockFloor (source (i + 1) (index profile a d)) =
      blockFloor (source (i + 1) (index profile a c))
    dsimp only [d, c]
    rw [index_rung, index_rung]
    have hi' : i - 1 + 1 = i := by omega
    rw [hi']
    simpa only [Nat.add_sub_cancel] using predecessor_block (t := i + 1) (by omega)
  have hd : min (q d) (q c) = ⊥ := by rw [show q d = ⊥ from hz, min_bot_left]
  have hh := LongGuardRows.bottom_of_same_block (hq.2 c) hb hd
  simpa only [min_self] using hh

omit [Finite X] in
/-- Extract a scalar chart from an actual maximal leaf of an arbitrary lawful
section. The leaf's faithful witness is used directly, including its long row. -/
theorem Lawful.exists_shape [Nonempty Q] {q : Point H X Q → ExtOrd}
    (hq : Lawful profile q) (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H) :
    ∃ a f, Monotone f ∧ f 0 = ⊥ ∧ (∀ i, SelfVis 1 (f i)) ∧
      ∀ v, q v = image profile a f v := by
  obtain ⟨a, ha⟩ := Finite.exists_max (fun a : Q => q (leaf hH a))
  have hdom (v : Point H X Q) : q v ≤ q (leaf hH a) :=
    (hq.le_parent hbound hH v).trans (ha (parent v))
  obtain ⟨g, σ, _, hg, h0, hm, h5, hr⟩ := hq.2 (leaf hH a)
  let f : ℕ → ExtOrd := fun i => min (σ (source H i)) (g 1)
  refine ⟨a, f, fun _ _ h => min_le_min_right _ (hm (source_mono H h)), ?_, ?_, ?_⟩
  · simp only [f, source_zero, h0, min_bot_left]
  · intro i
    change SelfVis 1 (min (σ (source H i)) (g 1))
    by_cases hi : σ (source H i) ≤ g 1
    · rw [min_eq_left hi]
      have he := h5 (source H i) 1 hi 1 le_rfl
      rw [source_visible H i] at he
      exact he.symm
    · rw [min_eq_right (not_le.mp hi).le]
      exact (hg 1).symm
  · intro v
    have h := hr v
    dsimp only at h
    rw [min_eq_left (hdom v)] at h
    rw [row, ceiling_leaf] at h
    exact h

/-- The full ladder excludes partial support erasure: every lawful section
is zero, or its serving chart is positive at every actual rung. -/
theorem lawful_iff_shape [Nonempty Q]
    (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H) (q : Point H X Q → ExtOrd) :
    Lawful profile q ↔ (∀ v, q v = ⊥) ∨
      ∃ a f, Monotone f ∧ f 0 = ⊥ ∧ (∀ i, SelfVis 1 (f i)) ∧
        (∀ i, 0 < i → i ≤ H → f i ≠ ⊥) ∧ ∀ v, q v = image profile a f v := by
  constructor
  · intro hq
    by_cases hzero : ∀ v, q v = ⊥
    · exact Or.inl hzero
    obtain ⟨a, f, hf, h0, hv, he⟩ := hq.exists_shape hbound hH
    have htop : f H ≠ ⊥ := by
      intro hz
      apply hzero
      intro v
      rw [he v]
      exact le_bot_iff.mp ((hf (index_le a v)).trans_eq hz)
    have hstep (i : ℕ) (hi : 0 < i) (hiH : i < H) (hz : f i = ⊥) : f (i + 1) = ⊥ := by
      have hz' : q (rung a ⟨i - 1, by omega⟩) = ⊥ := by
        rw [he, image, index_rung]
        simpa only [Nat.sub_add_cancel hi] using hz
      have hh := hq.predecessor_bot a hi hiH hz'
      simpa only [he, image, index_rung] using hh
    have hp (i : ℕ) (hi : 0 < i) (hiH : i ≤ H) : f i ≠ ⊥ := by
      intro hz
      have hall : ∀ j, i ≤ j → j ≤ H → f j = ⊥ := by
        intro j hij hjH
        induction j, hij using Nat.le_induction with
        | base => exact hz
        | succ j hij ih => exact hstep j (by omega) (by omega) (ih (by omega))
      exact htop (hall H hiH le_rfl)
    exact Or.inr ⟨a, f, hf, h0, hv, hp, he⟩
  · rintro (hz | ⟨a, f, hf, h0, hv, hp, he⟩)
    · have he : q = fun _ => ⊥ := funext hz
      rw [he]
      exact ⟨fun _ => selfVis_bot _, fun _ => by
        simp only [min_self]
        exact TransformsTo.to_bot _⟩
    · rw [funext he]
      exact image_lawful a f hf h0 hv hp

/-- Shadows remain distinct actual cells; the readout is their finite maximum. -/
noncomputable def readout (q : Point H X Q → ExtOrd) (d : X) : ExtOrd :=
  let _ := Fintype.ofFinite Q
  Finset.univ.sup (fun a : Q => q (shadow a d))

omit [Finite X] in
theorem readout_image (hbound : ∀ a d, profile a d ≤ H) (a : Q)
    {f : ℕ → ExtOrd} (hf : Monotone f) (d : X) :
    readout (image (H := H) profile a f) d = f (profile a d) := by
  classical
  let _ := Fintype.ofFinite Q
  apply le_antisymm
  · apply Finset.sup_le
    intro b _
    apply hf
    change min (cut H (profile a) (profile b)) (profile b d) ≤ profile a d
    have h := agree_cut H (profile a) (profile b) d
    omega
  · have h := Finset.le_sup (f := fun b : Q => image (H := H) profile a f (shadow b d))
        (Finset.mem_univ a)
    change f (profile a d) ≤
      Finset.univ.sup (fun b : Q => image (H := H) profile a f (shadow b d))
    simpa only [image, index, shadow, parent, ceiling, cut_refl,
      min_eq_right (hbound a d)] using h

omit [Finite X] in
/-- The numerical shadow identity holds in every physical owner's row,
including the long rungs, not only the full leaf. -/
theorem row_readout (hbound : ∀ a d, profile a d ≤ H)
    (c : Point H X Q) (d : X) :
    readout (row profile c) d = source (ceiling profile c) (profile (parent c) d) :=
  readout_image hbound (parent c) (source_mono _) d

omit [Finite X] [Finite Q] in
/-- Prefix repair preserves each real rung and shadow cap. Below the rank cut
only capped equality is required: a boundary half-orbit already above `γ`
need not keep its old uncapped reading. This theorem does not construct the
replacement profile or the scalar tables. -/
theorem cap_agreement (a b : Q) {k : ℕ}
    (hk : k ≤ cut H (profile a) (profile b)) (f g : ℕ → ExtOrd)
    (hf : Monotone f) (hg : Monotone g) {γ : ExtOrd}
    (hγf : γ ≤ f k) (hγg : γ ≤ g k)
    (hfg : ∀ i, i < k → min (f i) γ = min (g i) γ) (v : Point H X Q) :
    min (image profile a f v) γ = min (image profile b g v) γ := by
  have he := congrArg (fun z => min z k) (index_agreement (profile := profile) a b v)
  simp only [min_assoc, min_eq_right hk] at he
  change min (f (index profile a v)) γ = min (g (index profile b v)) γ
  by_cases ha : index profile a v < k
  · have hb : index profile b v = index profile a v := by omega
    rw [hb]
    exact hfg _ ha
  · have ha' : k ≤ index profile a v := by omega
    have hb' : k ≤ index profile b v := by omega
    rw [min_eq_right (hγf.trans (hf ha')), min_eq_right (hγg.trans (hg hb'))]

omit [Finite X] [Finite Q] in
/-- Capped numerical sections may be restored above their owner's height
without changing any smaller original cap, coordinate by coordinate. -/
theorem cap_agreement_of_restore {q r : Point H X Q → ExtOrd} {h γ : ExtOrd}
    (hγ : γ ≤ h) (hr : ∀ v, min (r v) h = min (q v) h) (v : Point H X Q) :
    min (r v) γ = min (q v) γ := by
  have he := congrArg (fun x => min x γ) (hr v)
  simpa only [min_assoc, min_eq_right hγ] using he

omit [Finite X] [Finite Q] in
/-- Two full rung vectors determine the capped readings of the entire
physical table. This justifies the finite prefix comparison used upstairs;
comparison on the named fields alone is not an input or a conclusion. -/
theorem cap_agreement_of_two_ladders (a b : Q) (f g : ℕ → ExtOrd)
    (hf : Monotone f) (hg : Monotone g) {γ : ExtOrd}
    (hab : ∀ i, i ≤ H → min (f i) γ =
      min (g (min i (cut H (profile a) (profile b)))) γ)
    (hba : ∀ i, i ≤ H → min (g i) γ =
      min (f (min i (cut H (profile a) (profile b)))) γ)
    (v : Point H X Q) :
    min (image profile a f v) γ = min (image profile b g v) γ := by
  have he := index_agreement (profile := profile) a b v
  change min (f (index profile a v)) γ = min (g (index profile b v)) γ
  apply le_antisymm
  · rw [hab _ (index_le a v), he]
    exact min_le_min_right _ (hg (min_le_left _ _))
  · rw [hba _ (index_le b v), ← he]
    exact min_le_min_right _ (hf (min_le_left _ _))

/-- Positivity at any actual shadow activates every rung of that shadow's
parent, even ranks unused by every named field. -/
theorem Lawful.rung_ne_bot_of_shadow [Nonempty Q] {q : Point H X Q → ExtOrd}
    (hq : Lawful profile q) (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H)
    (a : Q) (d : X) (hd : q (shadow a d) ≠ ⊥) (i : Fin H) :
    q (rung a i) ≠ ⊥ := by
  rcases (lawful_iff_shape hbound hH q).mp hq with hz | ⟨b, f, _, h0, _, hp, he⟩
  · exact (hd (hz _)).elim
  have hk : 0 < cut H (profile b) (profile a) := by
    by_contra hn
    have hz : cut H (profile b) (profile a) = 0 := by omega
    apply hd
    rw [he, image, index]
    change f (min (cut H (profile b) (profile a)) (profile a d)) = ⊥
    rw [hz, Nat.zero_min, h0]
  rw [he, image]
  apply hp
  · change 0 < min (cut H (profile b) (profile a)) (i.val + 1)
    omega
  · exact index_le _ _

end VaughtConjecture.Knight.SupportLadderRows
