/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedCore

/-! # Sharp coding and locality of the capped cores on the enlarged domain

Checks on the provenance-preserving capped cores (`Knight/CappedCore.lean`): the retained
grade-two witness row is sharply coded at its own grade (`retained_witness_row_coded`), the
capped grade-three rows are sharply coded at grade three (`capped_old_row_mem`,
`expandedRow_coded`), the domain enlarged by the capped cells themselves carries the same-level
locality (`expanded_same3`, on `ExpandedLow3`), repeated capping preserves the whole expanded row
(`expandedRow_recap`), a represented meet cell exists with the literal capped-row identity
(`represented_meet_rows`), and the bounded-alphabet core families are finite (`finite_core3`,
`finite_cappedCore3`).  Contributed as a review scout (2026-09-05) and graduated unchanged.
It does not construct a `SemScheme`; that is `Knight/FiniteAssembly.lean`.
Construction-private (not root-exported). -/
@[expose] public section

namespace VaughtConjecture.Knight.CappedCore3
open Transform Value ExtOrd
variable {P : Type*} [Fintype P] [DecidableEq P] {gradeP : P → ℕ} {T : ℕ}
variable (st : Setting gradeP T)

omit [Fintype P] [DecidableEq P] in
/-- Bounded alphabets really give finite core families; proof fields add no choices. -/
theorem finite_core3 [Finite P] : Finite (Core3 (gradeP := gradeP) (T := T)) := by
  let key (a : Core3 (gradeP := gradeP) (T := T)) :
      (P → ↥(codedAlphabet 3 T)) × ↥(codedAlphabet 3 T) :=
    (fun c => ⟨a.F c, by
      by_cases hc : gradeP c ≤ 3
      · exact a.F_mem c hc
      · rw [a.F_bot c (by omega)]
        exact bot_mem_codedAlphabet 3 T⟩, ⟨a.γ, a.γ_mem⟩)
  apply Finite.of_injective key
  intro a b hab
  have hF : a.F = b.F := by
    funext c
    exact congrArg (fun p => (p.1 c).val) hab
  have hγ : a.γ = b.γ := congrArg (fun p => p.2.val) hab
  cases a
  cases b
  dsimp only at hF hγ
  cases hF
  cases hγ
  rfl

omit [Fintype P] [DecidableEq P] in
/-- Provenance-retaining caps do not introduce an infinite history space. -/
theorem finite_cappedCore3 [Finite P] : Finite (CappedCore3 gradeP T) := by
  have : Finite (Core3 (gradeP := gradeP) (T := T)) := finite_core3
  let key (a : CappedCore3 gradeP T) :
      Core3 (gradeP := gradeP) (T := T) × ↥(codedAlphabet 3 T) :=
    (a.base, ⟨a.η, a.η_mem⟩)
  apply Finite.of_injective key
  intro a b hab
  have hbase : a.base = b.base := congrArg Prod.fst hab
  have hη : a.η = b.η := congrArg (fun p => p.2.val) hab
  cases a
  cases b
  dsimp only at hbase hη
  cases hbase
  cases hη
  rfl

theorem core2_row_mem (s : Core2 (gradeP := gradeP) (T := T)) (d : Low2 gradeP T) :
    s.row st d ∈ codedAlphabet 2 T := by
  rcases d with c | H | t
  · exact s.F_mem c.1 c.2
  · exact s.rho_mem st H
  · exact meet₂_mem_V st s t

/-- Retaining the original lower witness preserves its OWN owner's sharp code bound.
Its key set need not equal the truncated upper row's primitive range. -/
theorem retained_witness_row_coded (a : CappedCore3 gradeP T) (d : Low2 gradeP T) :
    IsCodedLabel 2 ((a.base.wit2 st).row st d) :=
  (codedAlphabet_isAlph 2 T).coded _ (core2_row_mem st (a.base.wit2 st) d)

theorem capped_old_row_mem (a : CappedCore3 gradeP T) (d : Low3 gradeP T) :
    a.row st d ∈ codedAlphabet 3 T := by
  rcases d with c | H | s | t
  · exact (codedAlphabet_isAlph 3 T).min_mem _ (a.base.F_mem c.1 c.2) _ a.η_mem
  · exact (codedAlphabet_isAlph 3 T).min_mem _ (a.base.rho1_mem st H) _ a.η_mem
  · exact (codedAlphabet_isAlph 3 T).min_mem _ (a.base.rho2_mem st s) _ a.η_mem
  · exact (codedAlphabet_isAlph 3 T).min_mem _ (meet₃_mem_V st a.base t) _ a.η_mem

abbrev ExpandedLow3 :=
  {c : P // gradeP c ≤ 3} ⊕ Row1 gradeP T ⊕
    Core2 (gradeP := gradeP) (T := T) ⊕ CappedCore3 gradeP T

def project : ExpandedLow3 (gradeP := gradeP) (T := T) → Low3 gradeP T
  | .inl c => .inl c
  | .inr (.inl H) => .inr (.inl H)
  | .inr (.inr (.inl s)) => .inr (.inr (.inl s))
  | .inr (.inr (.inr a)) => .inr (.inr (.inr a.base))

noncomputable def entryCap : ExpandedLow3 (gradeP := gradeP) (T := T) → ExtOrd
  | .inl _ => ⊤
  | .inr (.inl _) => ⊤
  | .inr (.inr (.inl _)) => ⊤
  | .inr (.inr (.inr a)) => a.η

noncomputable def expandedRow (a : CappedCore3 gradeP T)
    (d : ExpandedLow3 (gradeP := gradeP) (T := T)) : ExtOrd :=
  min (a.row st (project d)) (entryCap d)

/-- The genuinely new entries are precisely the capped meets. -/
theorem expandedRow_at_capped (a b : CappedCore3 gradeP T) :
    expandedRow st a (.inr (.inr (.inr b))) = a.meetC st b := by
  change min (min (meet₃ st a.base b.base) a.η) b.η = _
  exact min_assoc _ _ _

theorem expandedRow_coded (a : CappedCore3 gradeP T)
    (d : ExpandedLow3 (gradeP := gradeP) (T := T)) :
    IsCodedLabel 3 (expandedRow st a d) := by
  apply (codedAlphabet_isAlph 3 T).coded
  rcases d with c | H | s | b
  · simpa only [expandedRow, entryCap, project, min_eq_left le_top] using
      capped_old_row_mem st a (.inl c)
  · simpa only [expandedRow, entryCap, project, min_eq_left le_top] using
      capped_old_row_mem st a (.inr (.inl H))
  · simpa only [expandedRow, entryCap, project, min_eq_left le_top] using
      capped_old_row_mem st a (.inr (.inr (.inl s)))
  · exact (codedAlphabet_isAlph 3 T).min_mem _
      (capped_old_row_mem st a (project (.inr (.inr (.inr b))))) _ b.η_mem

theorem expandedRow_agree (a b : CappedCore3 gradeP T)
    (d : ExpandedLow3 (gradeP := gradeP) (T := T)) :
    min (expandedRow st b d) (b.meetC st a) =
      min (expandedRow st a d) (b.meetC st a) := by
  have h := rowC_agree st a b (project d)
  calc min (expandedRow st b d) (b.meetC st a)
      = min (min (b.row st (project d)) (b.meetC st a)) (entryCap d) := by
        unfold expandedRow; ac_rfl
    _ = min (min (a.row st (project d)) (b.meetC st a)) (entryCap d) :=
      congrArg (fun v => min v (entryCap d)) h
    _ = min (expandedRow st a d) (b.meetC st a) := by
        unfold expandedRow; ac_rfl

/-- Repeated capping preserves the complete expanded row, including new/new entries. -/
theorem expandedRow_recap (a : CappedCore3 gradeP T) (η : ExtOrd)
    (hη : η ∈ codedAlphabet 3 T) (hv : SelfVis 3 η)
    (d : ExpandedLow3 (gradeP := gradeP) (T := T)) :
    expandedRow st (a.recap η hη hv) d = min (expandedRow st a d) η := by
  have hrow : (a.recap η hη hv).row st (project d) = min (a.row st (project d)) η := by
    rcases d with c | H | s | b <;>
      simp only [project, row, F, rho1, rho2, recap] <;> exact (min_assoc _ _ _).symm
  unfold expandedRow
  rw [hrow]
  ac_rfl

/-- A represented meet cell with the literal capped-row identity on the expanded domain. -/
theorem represented_meet_rows (a b : CappedCore3 gradeP T) :
    ∃ m : CappedCore3 gradeP T, m.η = a.meetC st b ∧
      ∀ d : ExpandedLow3 (gradeP := gradeP) (T := T),
        expandedRow st m d = min (expandedRow st a d) (a.meetC st b) ∧
        expandedRow st m d = min (expandedRow st b d) (a.meetC st b) := by
  have hm : a.meetC st b ∈ codedAlphabet 3 T :=
    (codedAlphabet_isAlph 3 T).min_mem _ (meet₃_mem_V st a.base b.base) _
      ((codedAlphabet_isAlph 3 T).min_mem _ a.η_mem _ b.η_mem)
  let m := a.recap (a.meetC st b) hm (a.meetC_selfVis st b)
  refine ⟨m, min_eq_right (a.meetC_le_left st b), fun d => ?_⟩
  have he := expandedRow_recap st a (a.meetC st b) hm (a.meetC_selfVis st b) d
  exact ⟨he, he.trans (expandedRow_agree st b a d)⟩

/-- Same-level locality now includes ALL of the newly capped cells as arguments. -/
theorem expanded_same3 (a b : CappedCore3 gradeP T) :
    TransformsTo (fun d => Low3.grade (project d)) (expandedRow st a)
      (fun d => min (expandedRow st b d) (b.meetC st a)) := by
  refine ⟨fun k => if k ≤ 3 then b.meetC st a else ⊥, id, ?_, ?_, rfl,
    fun _ _ h => h, fun _ _ _ _ _ => rfl, ?_⟩
  · intro n m hnm
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · omega
    · exact bot_le
    · exact le_rfl
  · intro n
    dsimp only
    split_ifs with h
    · exact (selfVis_mono (b.meetC_selfVis st a) h).symm
    · rfl
  · intro d
    dsimp only
    rw [ite_eq_left (Low3.grade_le_three (project d))]
    exact expandedRow_agree st a b d


end VaughtConjecture.Knight.CappedCore3
