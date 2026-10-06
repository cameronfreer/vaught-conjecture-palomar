/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneInputEncoding
public import VaughtConjecture.Knight.NormalizedProfileFamily
public import VaughtConjecture.Knight.SourcePrefixRows

/-! # Explicit selected grade-one sections

The decoder is a finite right-filled table, not a chosen transformation.
It returns the first represented value above a source index, or the supplied
ceiling. Consequently its whole range has literal boundary/ceiling support.
All ordinals, bottom and literal top are permitted as boundary values.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GradeOneSelectedSections

open Transform Value ExtOrd SlotControllerFamily
open NormalizedProfileFamily (code_le code_zero code_order)

local notation "rankCode" => NormalizedProfileFamily.code

variable {X : Type*} [Fintype X]

open Classical in
noncomputable def decode (p : X → ExtOrd) (C : ExtOrd) (i : ℕ) : ExtOrd :=
  if i = 0 then ⊥ else min C ((Finset.univ.filter (fun d => i ≤ rankCode p d)).inf p)

@[simp] theorem decode_zero (p : X → ExtOrd) (C : ExtOrd) : decode p C 0 = ⊥ := by
  simp only [decode, ↓reduceIte]

theorem decode_bound (p : X → ExtOrd) (C : ExtOrd) (i : ℕ) : decode p C i ≤ C := by
  classical
  unfold decode
  split_ifs
  · exact bot_le
  · exact min_le_left _ _

theorem decode_le (p : X → ExtOrd) (C : ExtOrd) {i : ℕ} {d : X}
    (hd : i ≤ rankCode p d) : decode p C i ≤ p d := by
  classical
  unfold decode
  split_ifs
  · exact bot_le
  · exact (min_le_right _ _).trans (Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩))

theorem le_decode {p : X → ExtOrd} {C h : ExtOrd} {i : ℕ}
    (hi : i ≠ 0) (hC : h ≤ C) (hp : ∀ d, i ≤ rankCode p d → h ≤ p d) :
    h ≤ decode p C i := by
  classical
  simp only [decode, hi, ↓reduceIte]
  exact le_min hC (Finset.le_inf fun d hd => hp d (Finset.mem_filter.mp hd).2)

theorem decode_mono (p : X → ExtOrd) (C : ExtOrd) : Monotone (decode p C) := by
  classical
  intro i j hij
  by_cases hi : i = 0
  · subst i
    exact bot_le
  have hj : j ≠ 0 := by omega
  apply le_decode hj (decode_bound p C i)
  intro d hd
  exact decode_le p C (hij.trans hd)

theorem decode_read {p : X → ExtOrd} {C : ExtOrd} (hC : ∀ d, p d ≤ C) (d : X) :
    decode p C (rankCode p d) = p d := by
  by_cases hd : rankCode p d = 0
  · rw [hd, decode_zero, (code_zero p d).mp hd]
  apply le_antisymm (decode_le p C le_rfl)
  exact le_decode hd (hC d) (fun e he => (code_order p d e).mp he)

theorem decode_support (p : X → ExtOrd) (C : ExtOrd) (i : ℕ) :
    decode p C i = ⊥ ∨ decode p C i = C ∨ ∃ d, decode p C i = p d := by
  classical
  by_cases hi : i = 0
  · subst i
    exact Or.inl (decode_zero p C)
  right
  let S := Finset.univ.filter (fun d => i ≤ rankCode p d)
  by_cases hs : S.Nonempty
  · obtain ⟨d, _, hd⟩ := Finset.inf_mem_of_nonempty (f := p) hs
    change p d = S.inf p at hd
    simp only [decode, hi, ↓reduceIte]
    change min C (S.inf p) = C ∨ ∃ d, min C (S.inf p) = p d
    rw [← hd]
    rcases le_total C (p d) with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr ⟨d, min_eq_right h⟩
  · have hs' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    left
    simp only [decode, hi, ↓reduceIte]
    change min C (S.inf p) = C
    rw [hs', Finset.inf_empty, min_top_right]

theorem decode_visible {p : X → ExtOrd} {C : ExtOrd}
    (hp : ∀ d, SelfVis 1 (p d)) (hC : SelfVis 1 C) (i : ℕ) :
    SelfVis 1 (decode p C i) := by
  rcases decode_support p C i with h | h | ⟨d, h⟩
  · rw [h]; exact selfVis_bot _
  · rw [h]; exact hC
  · rw [h]; exact hp d

theorem decode_ceiling (p : X → ExtOrd) (C : ExtOrd) :
    decode p C (Fintype.card X + 1) = C := by
  apply le_antisymm (decode_bound _ _ _)
  apply le_decode (by omega) le_rfl
  intro d hd
  have := code_le p d
  omega

omit [Fintype X] in
theorem eq_of_agree_lt {p q : X → ExtOrd} {h : ExtOrd}
    (hpq : SourcePrefixRows.Agree p q h) {d : X} (hd : p d < h) : p d = q d := by
  have he := hpq d
  by_cases hq : q d < h
  · simpa only [min_eq_left hd.le, min_eq_left hq.le] using he
  · rw [min_eq_left hd.le, min_eq_right (le_of_not_gt hq)] at he
    exact False.elim ((ne_of_lt hd) he)

theorem code_eq_of_agree_lt {p q : X → ExtOrd} {h : ExtOrd}
    (hpq : SourcePrefixRows.Agree p q h) {d : X} (hd : p d < h) :
    rankCode p d = rankCode q d := by
  classical
  have he := eq_of_agree_lt hpq hd
  have hr : FreshSourceSlots.rank p d = FreshSourceSlots.rank q d := by
    unfold FreshSourceSlots.rank
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    calc
      p e < p d ↔ min (p e) h < p d := by simp [min_lt_iff, not_lt_of_ge hd.le]
      _ ↔ min (q e) h < p d := by rw [hpq e]
      _ ↔ q e < p d := by simp [min_lt_iff, not_lt_of_ge hd.le]
      _ ↔ q e < q d := by rw [he]
  simp only [NormalizedProfileFamily.code, he, hr]

theorem decode_cap_le {p q : X → ExtOrd} {C h : ExtOrd}
    (hpq : SourcePrefixRows.Agree p q h) (i : ℕ) :
    min (decode p C i) h ≤ decode q C i := by
  by_cases hi : i = 0
  · subst i; simp
  apply le_decode hi ((min_le_left _ _).trans (decode_bound _ _ _))
  intro d hd
  by_cases hq : q d < h
  · have hqp : SourcePrefixRows.Agree q p h := fun e => (hpq e).symm
    have he := eq_of_agree_lt hqp hq
    have hc := code_eq_of_agree_lt hqp hq
    rw [hc] at hd
    exact (min_le_left _ _).trans ((decode_le p C hd).trans_eq he.symm)
  · exact (min_le_right _ _).trans (le_of_not_gt hq)

/-- Right-filled scalar readings are natural at every cap; no visible-cut
restriction is needed for this grade-one comparison. -/
theorem decode_caps {p q : X → ExtOrd} {C h : ExtOrd}
    (hpq : SourcePrefixRows.Agree p q h) (i : ℕ) :
    min (decode p C i) h = min (decode q C i) h := by
  apply le_antisymm
  · exact le_min (decode_cap_le hpq i) (min_le_right _ _)
  · exact le_min (decode_cap_le (fun d => (hpq d).symm) i) (min_le_right _ _)

open Classical in
noncomputable def splitCut (p : X → ExtOrd) (h : ExtOrd) : ℕ :=
  (Finset.univ.filter (fun d => p d < h)).sup (rankCode p) + 1

theorem splitCut_pos (p : X → ExtOrd) (h : ExtOrd) : 0 < splitCut p h := Nat.succ_pos _

theorem splitCut_bound (p : X → ExtOrd) (h : ExtOrd) :
    splitCut p h ≤ Fintype.card X + 1 := by
  classical
  exact Nat.add_le_add_right (Finset.sup_le fun d _ => code_le p d) 1

theorem code_lt_splitCut {p : X → ExtOrd} {h : ExtOrd} {d : X} (hd : p d < h) :
    rankCode p d < splitCut p h := by
  classical
  exact Nat.lt_succ_of_le (Finset.le_sup (f := rankCode p)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩))

theorem splitCut_le_code {p q : X → ExtOrd} {h : ExtOrd}
    (hpq : SourcePrefixRows.Agree p q h) (hh : ⊥ < h) {d : X} (hd : h ≤ q d) :
    splitCut p h ≤ rankCode q d := by
  classical
  have hdpos : 0 < rankCode q d := by
    have hn : q d ≠ ⊥ := ne_bot_of_gt (hh.trans_le hd)
    exact Nat.pos_of_ne_zero (fun he => hn ((code_zero q d).mp he))
  have hs : (Finset.univ.filter (fun e => p e < h)).sup (rankCode p) ≤ rankCode q d - 1 := by
    apply Finset.sup_le
    intro e he
    have hel := (Finset.mem_filter.mp he).2
    have heq := eq_of_agree_lt hpq hel
    have hc := code_eq_of_agree_lt hpq hel
    have hlt : rankCode q e < rankCode q d := by
      rw [lt_iff_not_ge, code_order]
      exact not_le_of_gt (heq ▸ hel.trans_le hd)
    omega
  change _ + 1 ≤ rankCode q d
  omega

theorem encoded_agree_splitCut {p q : X → ExtOrd} {h : ExtOrd}
    (hpq : SourcePrefixRows.Agree p q h) (hh : ⊥ < h) :
    FiniteProfileControllers.Agree (rankCode p) (rankCode q) (splitCut p h) := by
  intro d
  by_cases hd : p d < h
  · rw [code_eq_of_agree_lt hpq hd]
  · have hpd := splitCut_le_code (fun _ => rfl) hh (le_of_not_gt hd)
    have hqd : h ≤ q d := by
      have he := hpq d
      rw [min_eq_right (le_of_not_gt hd)] at he
      exact he.trans_le (min_le_left _ _)
    rw [min_eq_right hpd, min_eq_right (splitCut_le_code hpq hh hqd)]

theorem cut_reaches {p q : X → ExtOrd} {C h : ExtOrd}
    (hpq : SourcePrefixRows.Agree p q h) (hh : ⊥ < h) (hC : h ≤ C) :
    h ≤ decode p C (FiniteProfileControllers.cut
      (Fintype.card X + 1) (rankCode p) (rankCode q)) ∧
    h ≤ decode q C (FiniteProfileControllers.cut
      (Fintype.card X + 1) (rankCode p) (rankCode q)) := by
  let e := FiniteProfileControllers.cut (Fintype.card X + 1) (rankCode p) (rankCode q)
  have he : splitCut p h ≤ e := FiniteProfileControllers.le_cut
    (splitCut_bound p h) (encoded_agree_splitCut hpq hh)
  have hen : e ≠ 0 := by have := splitCut_pos p h; omega
  constructor
  · apply le_decode hen hC
    intro d hd
    by_contra hn
    have := code_lt_splitCut (lt_of_not_ge hn)
    omega
  · apply le_decode hen hC
    intro d hd
    by_contra hn
    have hq := lt_of_not_ge hn
    have hqp : SourcePrefixRows.Agree q p h := fun d => (hpq d).symm
    have hpd : p d < h := (eq_of_agree_lt hqp hq) ▸ hq
    have heq := code_eq_of_agree_lt hpq hpd
    have := code_lt_splitCut hpd
    omega

variable {Q : Type*}

/-- The selected whole section, on distinct boundary and controller occurrences. -/
noncomputable def selected (profiles : Q → X → ℕ) (p : X → ExtOrd) (C : ExtOrd) :
    X ⊕ Q → ExtOrd
  | .inl d => p d
  | .inr q => decode p C
      (FiniteProfileControllers.cut (Fintype.card X + 1) (rankCode p) (profiles q))

theorem selected_read (profiles : Q → X → ℕ) (p : X → ExtOrd) (C : ExtOrd) (d : X) :
    selected profiles p C (.inl d) = p d := rfl

theorem selected_bound (profiles : Q → X → ℕ) {p : X → ExtOrd} {C : ExtOrd}
    (hp : ∀ d, p d ≤ C) (d : X ⊕ Q) : selected profiles p C d ≤ C := by
  cases d with
  | inl d => exact hp d
  | inr q => exact decode_bound _ _ _

theorem selected_support (profiles : Q → X → ℕ) (p : X → ExtOrd) (C : ExtOrd) (d : X ⊕ Q) :
    selected profiles p C d = ⊥ ∨ selected profiles p C d = C ∨
      ∃ x, selected profiles p C d = p x := by
  cases d with
  | inl d => exact Or.inr (Or.inr ⟨d, rfl⟩)
  | inr q => exact decode_support _ _ _

/-- No chosen whole completion enters this cap-naturality theorem. Both
sections are the explicit finite decoder construction above. -/
theorem selected_agreement (profiles : Q → X → ℕ) {p q : X → ExtOrd} {C h : ExtOrd}
    (hpq : SourcePrefixRows.Agree p q h) (hC : h ≤ C) :
    SourcePrefixRows.Agree (selected profiles p C) (selected profiles q C) h := by
  intro d
  cases d with
  | inl d => exact hpq d
  | inr c =>
    change min (decode p C _) h = min (decode q C _) h
    by_cases hh : h = ⊥
    · subst h; simp
    have hpos := bot_lt_iff_ne_bot.mpr hh
    let H := Fintype.card X + 1
    let e := FiniteProfileControllers.cut H (rankCode p) (rankCode q)
    let i := FiniteProfileControllers.cut H (rankCode p) (profiles c)
    let j := FiniteProfileControllers.cut H (rankCode q) (profiles c)
    have hij : min i e = min j e :=
      FiniteProfileControllers.cross_agreement H (rankCode p) (rankCode q) (profiles c)
    have hreach := cut_reaches hpq hpos hC
    change min (decode p C i) h = min (decode q C j) h
    by_cases hi : i < e
    · have hj : j = i := by omega
      rw [hj]
      exact decode_caps hpq i
    · have hie : e ≤ i := Nat.le_of_not_gt hi
      have hje : e ≤ j := by omega
      rw [min_eq_right (hreach.1.trans (decode_mono p C hie)),
        min_eq_right (hreach.2.trans (decode_mono q C hje))]

theorem selected_joint [Finite Q] {profiles : Q → X → ℕ}
    (hprofiles : ∀ q d, profiles q d ≤ Fintype.card X + 1)
    {p : X → ExtOrd} {C : ExtOrd} (hp : ∀ d, SelfVis 1 (p d))
    (hC : SelfVis 1 C) (hbound : ∀ d, p d ≤ C)
    (q : Q) (heq : profiles q = rankCode p) :
    FiniteProfileControllers.Joint (Fintype.card X + 1) profiles (selected profiles p C) := by
  have h := FiniteProfileControllers.label_joint hprofiles q (decode p C)
    (decode_mono p C) (decode_zero p C) (decode_visible hp hC)
  have he : (fun d => decode p C
      (FiniteProfileControllers.index (Fintype.card X + 1) profiles q d)) =
      selected profiles p C := by
    funext d
    cases d with
    | inl d => simpa only [FiniteProfileControllers.index, selected, heq] using decode_read hbound d
    | inr c => simp only [FiniteProfileControllers.index, selected, heq]
  rwa [he] at h

end VaughtConjecture.Knight.GradeOneSelectedSections
