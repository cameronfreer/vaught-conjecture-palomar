/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledGradeTwoRetune

/-! # The grade-two endpoint: one sufficiency lemma, the three rules cashed out

**The sufficiency lemma** (`respects_of_shape₂`): a labelling of the full grade-two lower set
`(univ, 2)` in the **value shape** `Shape₂` — the four parameters `(vP, x₀', x₁', H')` at the six
named cells (`x₀'` at the old occurrence, `x₁'` at the copy and the grade-one controller,
`min x₀' H'` at the old level-two witness, `H'` at its copy and the grade-two controller), the
proper value `vP` at the proper grade-one cells, `⊥` at the proper grade-two cells — respects the
frozen rows `rows₃` whenever the parameters are **legal** (`Legal₂`: `vP` grade-one self-visible
and below `x₀'`; `x₀' ≤ x₁'` grade-one self-visible and bottom-coupled; `H' ≤ x₁'` and
`min x₀' H'` grade-two self-visible).  Orderliness is the visibility fields; locality uses the
limit-step witnesses at the three grade-one rows (with `Witness.raise` at `ω·2+2` at the grade-one
controller), the strip witness `Witness.strip` at the two level-two witnesses, and the strip raised
at `ω·2+3` at the grade-two controller — where the bottom case is exactly the coupling
`min x₀' H' = ⊥ → H' = ⊥` (`Legal₂.min_bot`); availability is the case analysis of `two_cases`,
with the new scope facts `not_isProper_of_A_sub`/`not_isProper_of_B_sub` (no proper cell's scope
contains a face) closing the proper grade-two controller cases.  The lemma is proved once and
serves all three retuning rules.

**The endpoint** (`properToFull₃_two`): the grade-two scope-changing case of the coupled
semantics' bountifulness — a respecting labelling of a proper pair `(C, 2)` and one of `(univ, 2)`
agreeing below a grade-two self-visible `γ` on the pair have a common respecting labelling of
`(univ, 2)`, literal on the pair and agreeing with the second below `γ`.  The inputs' constraints
are read off the actual cells (the grade-one triple through the restriction to `(univ, 1)`, the
high label through `CoupledGradeTwoConstraints`); the protected face — old, copy, or neither —
selects the rule (`rule_two_old`, `rule_two_copy`, `rule_two_v`), whose `Retuned` output is legal
(`Retuned.legal`) and whose literal-preservation clauses put `retune₂` in the value shape; capped
agreement is the rule's agreement fields.  `properToFull₃_of_le_two` is the obligation
`ProperToFull₃Low` for every target grade `j ≤ 2`, by the same-grade case at `(univ, i)` followed
by `bountiful_full_scope` up to `(univ, j)`.

Not done: grade three (`ProperToFull₃Low` at `j = 3`), whose duplicate graded indices break the
uniqueness argument used here.  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## Scope facts about proper cells -/

section Scopes

/-- No proper cell's scope contains the old face `{0, 1, 2}`. -/
theorem not_isProper_of_A_sub {d : Cell D₂} (hd : ¬ mute₂ d)
    (h : ({0, 1, 2} : Finset (Fin 4)) ⊆ D₂.scope d) : ¬ IsProper d := by
  rintro ⟨c, hc⟩
  have h1 : (Finset.univ : Finset (Fin 3)) ⊆ C₂.scope (ret₂ d) := by
    rw [scope_ret₂ d hd]; exact univ_sub_fold_A.trans (Finset.image_subset_image h)
  rw [Family.scope_eq, hc] at h1
  exact Prop3.scope_ne_univ c (Finset.univ_subset_iff.mp h1)

/-- No proper cell's scope contains the copy face `{1, 2, 3}`. -/
theorem not_isProper_of_B_sub {d : Cell D₂} (hd : ¬ mute₂ d)
    (h : ({1, 2, 3} : Finset (Fin 4)) ⊆ D₂.scope d) : ¬ IsProper d := by
  rintro ⟨c, hc⟩
  have h1 : (Finset.univ : Finset (Fin 3)) ⊆ C₂.scope (ret₂ d) := by
    rw [scope_ret₂ d hd]; exact univ_sub_fold_B.trans (Finset.image_subset_image h)
  rw [Family.scope_eq, hc] at h1
  exact Prop3.scope_ne_univ c (Finset.univ_subset_iff.mp h1)

theorem scope_H₀old' : D₂.scope H₀old = {0, 1, 2} := by
  change (D₂.cell H₀old).1 = _; unfold H₀old; rw [cell_castAdd_X]; decide

/-- A cell of graded index `({c}, 1)` is proper. -/
theorem isProper_of_cell_singleton (x : Cell D₂) (c : Fin 4) (hx : D₂.cell x = ({c}, 1)) :
    IsProper x := by
  have hnm : ¬ mute₂ x := fun hm => by
    change D₂.cell x = _ at hm; rw [hx] at hm
    have := congrArg Prod.snd hm; change (1 : ℕ) = 4 at this; omega
  have hg : D₂.grade x ≤ 1 := by change (D₂.cell x).2 ≤ 1; rw [hx]
  have hcard : (D₂.scope x).card = 1 := by change (D₂.cell x).1.card = 1; rw [hx]; simp
  rcases one_cases hnm hg with rfl | rfl | rfl | hp
  · exfalso; rw [scope_H₀old'] at hcard; exact absurd hcard (by decide)
  · exfalso; rw [scope_H₀new] at hcard; exact absurd hcard (by decide)
  · exfalso
    change (D₂.cell U_H).1.card = 1 at hcard
    rw [cell_U_H, Finset.card_univ, Fintype.card_fin] at hcard; omega
  · exact hp

theorem selfVis_of_respects {BJ : Finset (Fin 4) × ℕ} {r : D₂.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow rows₃ BJ r) (d : D₂.below BJ) :
    SelfVis (D₂.grade d.1) (r d) := (hr.orderly d).symm

end Scopes

/-! ## The sufficiency lemma -/

section Sufficiency

/-- **Legal grade-two parameters**: the proper value grade-one self-visible and below the old
label; the grade-one labels ordered, bottom-coupled and grade-one self-visible; the high label
grade-two self-visible and below the copy label; the old high label grade-two self-visible. -/
structure Legal₂ (vP x₀' x₁' H' : ExtOrd) : Prop where
  visP : SelfVis 1 vP
  vle : vP ≤ x₀'
  le01 : x₀' ≤ x₁'
  coup : x₀' = ⊥ → x₁' = ⊥
  vis0 : SelfVis 1 x₀'
  vis1 : SelfVis 1 x₁'
  visH : SelfVis 2 H'
  Hle : H' ≤ x₁'
  vismin : SelfVis 2 (min x₀' H')

theorem Retuned.legal {vP x₀q x₁q Hq γ x₀' x₁' H' : ExtOrd}
    (R : Retuned vP x₀q x₁q Hq γ x₀' x₁' H') (hvP : SelfVis 1 vP) : Legal₂ vP x₀' x₁' H' :=
  ⟨hvP, R.vle, R.le01, R.coup, R.vis0, R.vis1, R.visH, R.Hle, R.vismin⟩

theorem Legal₂.min_bot {vP x₀' x₁' H' : ExtOrd} (L : Legal₂ vP x₀' x₁' H')
    (h : min x₀' H' = ⊥) : H' = ⊥ := by
  rcases min_eq_bot.mp h with h0 | h0
  · exact le_bot_iff.mp (L.Hle.trans (L.coup h0).le)
  · exact h0

/-- **The value shape** of a grade-two labelling: the parameters at the six named cells, the
proper value at the proper grade-one cells, `⊥` at the proper grade-two cells. -/
structure Shape₂ (r : D₂.below (Finset.univ, 2) → ExtOrd) (vP x₀' x₁' H' : ExtOrd) : Prop where
  at_H₀old : r ⟨H₀old, memH₀old₂⟩ = x₀'
  at_H₀new : r ⟨H₀new, memH₀new₂⟩ = x₁'
  at_U_H : r ⟨U_H, memU_H₂⟩ = x₁'
  at_s₀old : r ⟨s₀old, mems₀old₂⟩ = min x₀' H'
  at_s₀new : r ⟨s₀new, mems₀new₂⟩ = H'
  at_U_S : r ⟨U_S, memU₂⟩ = H'
  at_proper : ∀ d : D₂.below (Finset.univ, 2), IsProper d.1 →
    r d = if D₂.grade d.1 = 2 then ⊥ else vP

theorem ω2_two_lt_three : ofOrd (ω2 2) < ofOrd (ω2 3) :=
  ofOrd_lt_ofOrd.mpr (ω2_lt_ω2 (by decide))

/-- **Sufficiency**: legal parameters in the value shape give a respecting labelling of the
full grade-two lower set. -/
theorem respects_of_shape₂ {r : D₂.below (Finset.univ, 2) → ExtOrd} {vP x₀' x₁' H' : ExtOrd}
    (L : Legal₂ vP x₀' x₁' H') (S : Shape₂ r vP x₀' x₁' H') :
    RespectsSemanticsBelow rows₃ (Finset.univ, 2) r := by
  have hnm : ∀ d : D₂.below (Finset.univ, 2), ¬ mute₂ d.1 := not_mute_of_two
  have hv_low : ∀ d : D₂.below (Finset.univ, 2), IsProper d.1 → D₂.grade d.1 ≤ 1 → r d = vP :=
    fun d hd hg => by rw [S.at_proper d hd, ite_eq_right (by omega)]
  have hv_two : ∀ d : D₂.below (Finset.univ, 2), IsProper d.1 → D₂.grade d.1 = 2 → r d = ⊥ :=
    fun d hd hg => by rw [S.at_proper d hd, ite_eq_left hg]
  have hvle1 : vP ≤ x₁' := L.vle.trans L.le01
  have hmS : SelfVis 1 (min vP H') := selfVis_min' L.visP (L.visH.mono (by omega))
  have hmY : SelfVis 1 (min vP (min x₀' H')) := selfVis_min' L.visP (L.vismin.mono (by omega))
  -- every grade-one label is at most the grade-one controller's
  have hle₁ : ∀ d : D₂.below (Finset.univ, 2), D₂.grade d.1 = 1 → r d ≤ x₁' := by
    intro d hg
    rcases two_cases (hnm d) d.2.2 with h | h | h | h | h | h | ⟨h, -⟩ | ⟨-, h⟩
    · rw [show d = ⟨H₀old, memH₀old₂⟩ from Subtype.ext h, S.at_H₀old]; exact L.le01
    · rw [show d = ⟨H₀new, memH₀new₂⟩ from Subtype.ext h, S.at_H₀new]
    · rw [show d = ⟨U_H, memU_H₂⟩ from Subtype.ext h, S.at_U_H]
    · rw [h, grade_s₀old] at hg; omega
    · rw [h, grade_s₀new] at hg; omega
    · rw [h, grade_U_S] at hg; omega
    · rw [hv_low d h hg.le]; exact hvle1
    · omega
  -- every grade-two label is at most the grade-two controller's
  have hle₂ : ∀ d : D₂.below (Finset.univ, 2), D₂.grade d.1 = 2 → r d ≤ H' := by
    intro d hg
    rcases two_cases (hnm d) d.2.2 with h | h | h | h | h | h | ⟨-, h⟩ | ⟨h, -⟩
    · rw [h, grade_H₀old] at hg; omega
    · rw [h, grade_H₀new] at hg; omega
    · rw [h, grade_U_H] at hg; omega
    · rw [show d = ⟨s₀old, mems₀old₂⟩ from Subtype.ext h, S.at_s₀old]; exact min_le_right _ _
    · rw [show d = ⟨s₀new, mems₀new₂⟩ from Subtype.ext h, S.at_s₀new]
    · rw [show d = ⟨U_S, memU₂⟩ from Subtype.ext h, S.at_U_S]
    · omega
    · rw [hv_two d h hg]; exact bot_le
  refine ⟨?_, ?_, ?_⟩
  · -- orderly
    intro d
    change r d = extVisibilityReplace (r d) (D₂.grade d.1) (D₂.grade d.1)
    rcases two_cases (hnm d) d.2.2 with h | h | h | h | h | h | ⟨h, hg⟩ | ⟨h, hg⟩
    · have hg : D₂.grade d.1 = 1 := by rw [h, grade_H₀old]
      rw [hg, show d = ⟨H₀old, memH₀old₂⟩ from Subtype.ext h, S.at_H₀old]; exact L.vis0.symm
    · have hg : D₂.grade d.1 = 1 := by rw [h, grade_H₀new]
      rw [hg, show d = ⟨H₀new, memH₀new₂⟩ from Subtype.ext h, S.at_H₀new]; exact L.vis1.symm
    · have hg : D₂.grade d.1 = 1 := by rw [h, grade_U_H]
      rw [hg, show d = ⟨U_H, memU_H₂⟩ from Subtype.ext h, S.at_U_H]; exact L.vis1.symm
    · have hg : D₂.grade d.1 = 2 := by rw [h, grade_s₀old]
      rw [hg, show d = ⟨s₀old, mems₀old₂⟩ from Subtype.ext h, S.at_s₀old]; exact L.vismin.symm
    · have hg : D₂.grade d.1 = 2 := by rw [h, grade_s₀new]
      rw [hg, show d = ⟨s₀new, mems₀new₂⟩ from Subtype.ext h, S.at_s₀new]; exact L.visH.symm
    · have hg : D₂.grade d.1 = 2 := by rw [h, grade_U_S]
      rw [hg, show d = ⟨U_S, memU₂⟩ from Subtype.ext h, S.at_U_S]; exact L.visH.symm
    · rw [hv_low d h hg.le, hg]; exact L.visP.symm
    · rw [hv_two d h hg, hg]; exact (selfVis_bot 2).symm
  · -- locality
    intro Sig
    obtain ⟨x, hx⟩ := Sig
    rcases two_cases (hnm ⟨x, hx⟩) hx.2 with rfl | rfl | rfl | rfl | rfl | rfl | ⟨hP, hg⟩ | ⟨hP, hg⟩
    · -- the old occurrence: the limit step
      refine (Witness.stepLimit 1 2 L.vle L.visP L.vis0).transformsTo fun d => ?_
      rw [gTop_of_le (K := 1) (k := D₂.grade d.1) (d.2.2.trans grade_H₀old.le), min_eq_left le_top]
      change min (r (CellScheme.below.incl ⟨H₀old, hx⟩ d)) (r ⟨H₀old, memH₀old₂⟩) = _
      rw [S.at_H₀old]
      rcases below_H₀old_cases d with hd | hd
      · rw [show CellScheme.below.incl ⟨H₀old, hx⟩ d = ⟨H₀old, memH₀old₂⟩ from Subtype.ext hd,
          S.at_H₀old, min_self, rows₃_E_H₀old_self d hd, stepShifter_of_ge (ω2_ge 1)]
      · rw [hv_low (CellScheme.below.incl ⟨H₀old, hx⟩ d) hd (d.2.2.trans grade_H₀old.le),
          min_eq_left L.vle,
          rows₃_E_one_proper grade_H₀old d hd, stepShifter_of_lt (a := v₀) v₀_ne_bot v₀_lt_ω2']
    · -- the copy: the limit step
      refine (Witness.stepLimit 1 2 hvle1 L.visP L.vis1).transformsTo fun d => ?_
      rw [gTop_of_le (K := 1) (k := D₂.grade d.1) (d.2.2.trans grade_H₀new.le), min_eq_left le_top]
      change min (r (CellScheme.below.incl ⟨H₀new, hx⟩ d)) (r ⟨H₀new, memH₀new₂⟩) = _
      rw [S.at_H₀new]
      rcases below_H₀new_cases' d with hd | hd
      · rw [show CellScheme.below.incl ⟨H₀new, hx⟩ d = ⟨H₀new, memH₀new₂⟩ from Subtype.ext hd,
          S.at_H₀new, min_self, rows₃_E_H₀new_self d hd, stepShifter_of_ge (ω2_ge 1)]
      · rw [hv_low (CellScheme.below.incl ⟨H₀new, hx⟩ d) hd (d.2.2.trans grade_H₀new.le),
          min_eq_left hvle1,
          rows₃_E_one_proper grade_H₀new d hd, stepShifter_of_lt (a := v₀) v₀_ne_bot v₀_lt_ω2']
    · -- the grade-one controller: the limit step raised at the separating value
      refine ((Witness.stepLimit 1 2 L.vle L.visP L.vis0).raise 1 (fun _ hk => gTop_bot hk)
        (ξ := ω2 2) (by rw [fp_ω2]; omega) L.vis1).transformsTo fun d => ?_
      rw [gTop_of_le (K := 1) (k := D₂.grade d.1) (below_U_H_mem d).2, min_eq_left le_top]
      change min (r (CellScheme.below.incl ⟨U_H, hx⟩ d)) (r ⟨U_H, memU_H₂⟩) = _
      rw [S.at_U_H]
      rcases one_cases (not_mute_below_U_H d) (below_U_H_mem d).2 with hd | hd | hd | hd
      · rw [show CellScheme.below.incl ⟨U_H, hx⟩ d = ⟨H₀old, memH₀old₂⟩ from Subtype.ext hd,
          S.at_H₀old, min_eq_left L.le01, rows₃_E_U_H_H₀old d hd,
          raiseShifter_of_lt (ofOrd_lt_ofOrd.mpr (ω2_lt_ω2 (a := 1) (b := 2) (by decide))),
          stepShifter_of_ge (ω2_ge 1)]
      · rw [show CellScheme.below.incl ⟨U_H, hx⟩ d = ⟨H₀new, memH₀new₂⟩ from Subtype.ext hd,
          S.at_H₀new, min_self, rows₃_E_U_H_new d (Or.inl hd)]
        by_cases hb : x₀' = ⊥
        · rw [raiseShifter_of_bot (σ := stepShifter 2 vP x₀') (ξ := ω2 2) (c := x₁')
            (a := ofOrd (ω2 2)) (by rw [stepShifter_of_ge (ω2_ge 2)]; exact hb)]
          exact L.coup hb
        · rw [raiseShifter_of_ge (σ := stepShifter 2 vP x₀') (c := x₁') le_rfl
            (by rw [stepShifter_of_ge (ω2_ge 2)]; exact hb),
            stepShifter_of_ge (ω2_ge 2), max_eq_right L.le01]
      · rw [show CellScheme.below.incl ⟨U_H, hx⟩ d = ⟨U_H, memU_H₂⟩ from Subtype.ext hd,
          S.at_U_H, min_self, rows₃_E_U_H_new d (Or.inr hd)]
        by_cases hb : x₀' = ⊥
        · rw [raiseShifter_of_bot (σ := stepShifter 2 vP x₀') (ξ := ω2 2) (c := x₁')
            (a := ofOrd (ω2 2)) (by rw [stepShifter_of_ge (ω2_ge 2)]; exact hb)]
          exact L.coup hb
        · rw [raiseShifter_of_ge (σ := stepShifter 2 vP x₀') (c := x₁') le_rfl
            (by rw [stepShifter_of_ge (ω2_ge 2)]; exact hb),
            stepShifter_of_ge (ω2_ge 2), max_eq_right L.le01]
      · rw [hv_low (CellScheme.below.incl ⟨U_H, hx⟩ d) hd (below_U_H_mem d).2, min_eq_left hvle1,
          rows₃_E_one_proper grade_U_H d hd,
          raiseShifter_of_lt (v₀_lt_ω2 2), stepShifter_of_lt (a := v₀) v₀_ne_bot v₀_lt_ω2']
    · -- the old level-two witness: the strip
      refine (Witness.strip hmY L.vismin (min_le_right _ _)).transformsTo fun d => ?_
      rw [gTop_of_le (K := 2) (k := D₂.grade d.1) (d.2.2.trans grade_s₀old.le), min_eq_left le_top]
      change min (r (CellScheme.below.incl ⟨s₀old, hx⟩ d)) (r ⟨s₀old, mems₀old₂⟩) = _
      rw [S.at_s₀old, rows₃_E_s₀old d]
      rcases below_s₀old_cases d with hd | hd | hd
      · rw [show CellScheme.below.incl ⟨s₀old, hx⟩ d = ⟨H₀old, memH₀old₂⟩ from Subtype.ext hd,
          S.at_H₀old, min_eq_right (min_le_left _ _), hd, ret₂_H₀old, Equiv.symm_apply_apply,
          rowX_s₀_H, s₀c_γ_num, strip_ω2]
      · rw [show CellScheme.below.incl ⟨s₀old, hx⟩ d = ⟨s₀old, mems₀old₂⟩ from Subtype.ext hd,
          S.at_s₀old, min_self, hd, ret₂_s₀old, Equiv.symm_apply_apply, rowX_s₀_s, s₀c_γ_num,
          strip_ω2]
      · rw [rowX_s₀_of_proper (hmute_below₂ _ d.1 not_mute_s₀old d.2) hd]
        have h2 : D₂.grade d.1 ≤ 2 := d.2.2.trans grade_s₀old.le
        by_cases hg : D₂.grade d.1 ≤ 1
        · rw [ite_eq_left hg, hv_low (CellScheme.below.incl ⟨s₀old, hx⟩ d) hd hg, strip_v₀ hmY]
        · rw [ite_eq_right hg, hv_two (CellScheme.below.incl ⟨s₀old, hx⟩ d) hd
            (show D₂.grade d.1 = 2 by omega), strip_bot, min_eq_left bot_le]
    · -- the copy of the level-two witness: the strip
      refine (Witness.strip hmS L.visH (min_le_right _ _)).transformsTo fun d => ?_
      rw [gTop_of_le (K := 2) (k := D₂.grade d.1) (d.2.2.trans grade_s₀new.le), min_eq_left le_top]
      change min (r (CellScheme.below.incl ⟨s₀new, hx⟩ d)) (r ⟨s₀new, mems₀new₂⟩) = _
      rw [S.at_s₀new, rows₃_E_s₀new d]
      rcases below_s₀new_cases₂ d with hd | hd | hd
      · rw [show CellScheme.below.incl ⟨s₀new, hx⟩ d = ⟨H₀new, memH₀new₂⟩ from Subtype.ext hd,
          S.at_H₀new, min_eq_right L.Hle, hd, ret₂_H₀new, Equiv.symm_apply_apply,
          rowX_s₀_H, s₀c_γ_num, strip_ω2]
      · rw [show CellScheme.below.incl ⟨s₀new, hx⟩ d = ⟨s₀new, mems₀new₂⟩ from Subtype.ext hd,
          S.at_s₀new, min_self, hd, ret₂_s₀new, Equiv.symm_apply_apply, rowX_s₀_s, s₀c_γ_num,
          strip_ω2]
      · rw [rowX_s₀_of_proper (hmute_below₂ _ d.1 not_mute_s₀new d.2) hd]
        have h2 : D₂.grade d.1 ≤ 2 := d.2.2.trans grade_s₀new.le
        by_cases hg : D₂.grade d.1 ≤ 1
        · rw [ite_eq_left hg, hv_low (CellScheme.below.incl ⟨s₀new, hx⟩ d) hd hg, strip_v₀ hmS]
        · rw [ite_eq_right hg, hv_two (CellScheme.below.incl ⟨s₀new, hx⟩ d) hd
            (show D₂.grade d.1 = 2 by omega), strip_bot, min_eq_left bot_le]
    · -- the grade-two controller: the strip raised at the separating value
      have hmc : min vP H' ≤ min x₀' H' := min_le_min L.vle le_rfl
      refine ((Witness.strip hmS L.vismin hmc).raise 2 (fun _ hk => gTop_bot hk)
        (ξ := ω2 3) (by rw [fp_ω2]; omega) L.visH).transformsTo fun d => ?_
      rw [gTop_of_le (K := 2) (k := D₂.grade d.1) (below_U_S_mem d).2, min_eq_left le_top]
      change min (r (CellScheme.below.incl ⟨U_S, hx⟩ d)) (r ⟨U_S, memU₂⟩) = _
      rw [S.at_U_S, rows₃_E, E₃_U_S]
      have hraise_sep : raiseShifter (stripShifter (min vP H') (min x₀' H')) (ω2 3) H'
          (ofOrd (ω2 3)) = H' := by
        by_cases hb : min x₀' H' = ⊥
        · rw [raiseShifter_of_bot (by rw [strip_ω2]; exact hb)]; exact (L.min_bot hb).symm
        · rw [raiseShifter_of_ge le_rfl (by rw [strip_ω2]; exact hb), strip_ω2,
            max_eq_right (min_le_right _ _)]
      rcases two_cases (not_mute_below_U_S d) (below_U_S_mem d).2 with
        hd | hd | hd | hd | hd | hd | ⟨hd, hg⟩ | ⟨hd, hg⟩
      · rw [show CellScheme.below.incl ⟨U_S, hx⟩ d = ⟨H₀old, memH₀old₂⟩ from Subtype.ext hd,
          S.at_H₀old, hd, vS_H₀old, s₀c_γ_num, raiseShifter_of_lt ω2_two_lt_three, strip_ω2]
      · rw [show CellScheme.below.incl ⟨U_S, hx⟩ d = ⟨H₀new, memH₀new₂⟩ from Subtype.ext hd,
          S.at_H₀new, min_eq_right L.Hle, hd, vS_H₀new, γ₁_num, hraise_sep]
      · rw [show CellScheme.below.incl ⟨U_S, hx⟩ d = ⟨U_H, memU_H₂⟩ from Subtype.ext hd,
          S.at_U_H, min_eq_right L.Hle, hd, vS_U_H, γ₁_num, hraise_sep]
      · rw [show CellScheme.below.incl ⟨U_S, hx⟩ d = ⟨s₀old, mems₀old₂⟩ from Subtype.ext hd,
          S.at_s₀old, min_eq_left (min_le_right _ _), hd, vS_s₀old, s₀c_γ_num,
          raiseShifter_of_lt ω2_two_lt_three, strip_ω2]
      · rw [show CellScheme.below.incl ⟨U_S, hx⟩ d = ⟨s₀new, mems₀new₂⟩ from Subtype.ext hd,
          S.at_s₀new, min_self, hd, vS_s₀new, γ₁_num, hraise_sep]
      · rw [show CellScheme.below.incl ⟨U_S, hx⟩ d = ⟨U_S, memU₂⟩ from Subtype.ext hd,
          S.at_U_S, min_self, hd, vS_of_new ⟨Or.inr ret₂_U_S, fullCell_ne_old s₀X rfl⟩, γ₁_num,
          hraise_sep]
      · rw [hv_low (CellScheme.below.incl ⟨U_S, hx⟩ d) hd hg.le,
          vS_of_proper' (not_mute_below_U_S d) hd, ite_eq_left hg.le,
          raiseShifter_of_lt (v₀_lt_ω2 3), strip_v₀ hmS]
      · rw [hv_two (CellScheme.below.incl ⟨U_S, hx⟩ d) hd hg,
          vS_of_proper' (not_mute_below_U_S d) hd, ite_eq_right (by omega),
          raiseShifter_of_lt (bot_lt_ofOrd _), strip_bot, min_eq_left bot_le]
    · -- a proper grade-one cell: the constant row
      have hnx : ¬ mute₂ x := hnm ⟨x, hx⟩
      have hbelow : ∀ d : D₂.below (D₂.cell x), IsProper d.1 := fun d =>
        isProper_of_below hnx (hmute_below₂ x d.1 hnx d.2) d.2 (d.2.2.trans hg.le) hP
      refine transformsTo_congr rfl rfl ?_ (transformsTo_const_of_ne_bot (w := vP)
        (fun d => d.2.2.trans hg.le) (p := rows₃.E x)
        (fun d => by rw [rows₃_E_one_proper hg d (hbelow d)]; exact ofOrd_ne_bot _) L.visP)
      funext d
      rw [hv_low (CellScheme.below.incl ⟨x, hx⟩ d) (hbelow d) (d.2.2.trans hg.le),
        hv_low ⟨x, hx⟩ hP hg.le, min_self]
    · -- a proper grade-two cell: the bottom row
      refine (witness_id 2).transformsTo fun d => ?_
      change min (r (CellScheme.below.incl ⟨x, hx⟩ d)) (r ⟨x, hx⟩) =
        min (id (rows₃.E x d)) (gTop 2 (D₂.grade d.1))
      rw [hv_two ⟨x, hx⟩ hP hg, rows₃_E_proper_two hP hg d, min_eq_right bot_le]
      exact (min_eq_left bot_le).symm
  · -- availability
    intro Sig Xi₀ hs hg
    refine ⟨Xi₀, rfl, ?_⟩
    rcases two_cases (hnm Xi₀) Xi₀.2.2 with h | h | h | h | h | h | ⟨h, hgX⟩ | ⟨h, hgX⟩
    · rw [show Xi₀ = ⟨H₀old, memH₀old₂⟩ from Subtype.ext h, S.at_H₀old]
      rw [h] at hs; rw [h, grade_H₀old] at hg
      rcases two_cases (hnm Sig) Sig.2.2 with h' | h' | h' | h' | h' | h' | ⟨h', -⟩ | ⟨-, h'⟩
      · rw [show Sig = ⟨H₀old, memH₀old₂⟩ from Subtype.ext h', S.at_H₀old]
      · exact absurd (hs (h' ▸ three_mem_scope_H₀new)) three_not_mem_scope_H₀old'
      · exact absurd (hs (h' ▸ three_mem_scope_U_H)) three_not_mem_scope_H₀old'
      · rw [h', grade_s₀old] at hg; omega
      · rw [h', grade_s₀new] at hg; omega
      · rw [h', grade_U_S] at hg; omega
      · rw [hv_low Sig h' hg.le]; exact L.vle
      · omega
    · rw [show Xi₀ = ⟨H₀new, memH₀new₂⟩ from Subtype.ext h, S.at_H₀new]
      rw [h] at hs; rw [h, grade_H₀new] at hg
      rcases two_cases (hnm Sig) Sig.2.2 with h' | h' | h' | h' | h' | h' | ⟨h', -⟩ | ⟨-, h'⟩
      · exact absurd (hs (h' ▸ zero_mem_scope_H₀old)) zero_not_mem_scope_H₀new
      · rw [show Sig = ⟨H₀new, memH₀new₂⟩ from Subtype.ext h', S.at_H₀new]
      · exact absurd (hs (h' ▸ zero_mem_scope_U_H)) zero_not_mem_scope_H₀new
      · rw [h', grade_s₀old] at hg; omega
      · rw [h', grade_s₀new] at hg; omega
      · rw [h', grade_U_S] at hg; omega
      · rw [hv_low Sig h' hg.le]; exact hvle1
      · omega
    · rw [show Xi₀ = ⟨U_H, memU_H₂⟩ from Subtype.ext h, S.at_U_H]
      rw [h, grade_U_H] at hg
      exact hle₁ Sig hg
    · rw [show Xi₀ = ⟨s₀old, mems₀old₂⟩ from Subtype.ext h, S.at_s₀old]
      rw [h] at hs; rw [h, grade_s₀old] at hg
      rcases two_cases (hnm Sig) Sig.2.2 with h' | h' | h' | h' | h' | h' | ⟨-, h'⟩ | ⟨h', -⟩
      · rw [h', grade_H₀old] at hg; omega
      · rw [h', grade_H₀new] at hg; omega
      · rw [h', grade_U_H] at hg; omega
      · rw [show Sig = ⟨s₀old, mems₀old₂⟩ from Subtype.ext h', S.at_s₀old]
      · exact absurd (hs (h' ▸ three_mem_scope_s₀new)) three_not_mem_scope_s₀old
      · exact absurd (hs (h' ▸ three_mem_scope_U_S)) three_not_mem_scope_s₀old
      · omega
      · rw [hv_two Sig h' hg]; exact bot_le
    · rw [show Xi₀ = ⟨s₀new, mems₀new₂⟩ from Subtype.ext h, S.at_s₀new]
      rw [h] at hs; rw [h, grade_s₀new] at hg
      rcases two_cases (hnm Sig) Sig.2.2 with h' | h' | h' | h' | h' | h' | ⟨-, h'⟩ | ⟨h', -⟩
      · rw [h', grade_H₀old] at hg; omega
      · rw [h', grade_H₀new] at hg; omega
      · rw [h', grade_U_H] at hg; omega
      · exact absurd (hs (h' ▸ zero_mem_scope_s₀old)) zero_not_mem_scope_s₀new
      · rw [show Sig = ⟨s₀new, mems₀new₂⟩ from Subtype.ext h', S.at_s₀new]
      · exact absurd (hs (h' ▸ zero_mem_scope_U_S)) zero_not_mem_scope_s₀new
      · omega
      · rw [hv_two Sig h' hg]; exact bot_le
    · rw [show Xi₀ = ⟨U_S, memU₂⟩ from Subtype.ext h, S.at_U_S]
      rw [h, grade_U_S] at hg
      exact hle₂ Sig hg
    · -- a proper grade-one cell dominates only proper cells
      rw [hgX] at hg
      have hS : IsProper Sig.1 :=
        isProper_of_below (hnm Xi₀) (hnm Sig)
          ⟨hs, by change D₂.grade Sig.1 ≤ D₂.grade Xi₀.1; rw [hg, hgX]⟩ hg.le h
      rw [hv_low Sig hS hg.le, hv_low Xi₀ h hgX.le]
    · -- a proper grade-two cell dominates only proper cells
      rw [hgX] at hg
      rw [hv_two Xi₀ h hgX]
      rcases two_cases (hnm Sig) Sig.2.2 with h' | h' | h' | h' | h' | h' | ⟨-, h'⟩ | ⟨h', -⟩
      · rw [h', grade_H₀old] at hg; omega
      · rw [h', grade_H₀new] at hg; omega
      · rw [h', grade_U_H] at hg; omega
      · exfalso
        rw [h', scope_s₀old] at hs
        exact not_isProper_of_A_sub (hnm Xi₀) hs h
      · exfalso
        rw [h', scope_s₀new] at hs
        exact not_isProper_of_B_sub (hnm Xi₀) hs h
      · exfalso
        have : ({0, 1, 2} : Finset (Fin 4)) ⊆ D₂.scope Xi₀.1 := fun i _ => hs (by
          rw [h']; change i ∈ (D₂.cell U_S).1; rw [cell_U_S]; exact Finset.mem_univ _)
        exact not_isProper_of_A_sub (hnm Xi₀) this h
      · omega
      · rw [hv_two Sig h' hg]

end Sufficiency

/-! ## The grade-two endpoint -/

section Endpoint

theorem h₁₂C (C : Finset (Fin 4)) : GradedLe (C, 1) (C, 2) :=
  ⟨Finset.Subset.refl _, by change (1 : ℕ) ≤ 2; decide⟩

/-- **The grade-two scope-changing case**: a respecting labelling of a proper pair `(C, 2)` and a
respecting labelling of `(univ, 2)` agreeing below a grade-two self-visible `γ` on the pair have
a common respecting labelling of `(univ, 2)` — literal on the pair, agreeing with the second
below `γ`. -/
theorem properToFull₃_two (C : Finset (Fin 4)) (hCI : (C, 2) ∈ Plan.gradedPlan plan₄)
    (hC : C ≠ Finset.univ) (h : GradedLe (C, 2) (Finset.univ, 2))
    (p : D₂.below (C, 2) → ExtOrd) (q : D₂.below (Finset.univ, 2) → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow rows₃ (C, 2) p)
    (hq : RespectsSemanticsBelow rows₃ (Finset.univ, 2) q)
    (hγ : extVisibilityReplace γ 2 2 = γ)
    (hagree : ∀ d : D₂.below (C, 2), min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D₂.below (Finset.univ, 2) → ExtOrd, RespectsSemanticsBelow rows₃ (Finset.univ, 2) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D₂.below (C, 2), q' (CellScheme.below.mono h d) = p d) := by
  classical
  have hγ' : SelfVis 2 γ := hγ
  -- the singleton cells: one inside `C`, and the cell `{1}`
  obtain ⟨hCp, -, hcard⟩ := Plan.mem_gradedPlan.mp hCI
  dsimp only at hCp hcard
  obtain ⟨c, hc⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  have hsing : ∀ c : Fin 4, (({c} : Finset (Fin 4)), 1) ∈ Plan.gradedPlan plan₄ := fun c =>
    Plan.mem_gradedPlan.mpr ⟨singleton_mem_plan₄ c, Nat.one_pos, by simp⟩
  have hC1 : (C, 1) ∈ Plan.gradedPlan plan₄ :=
    Plan.mem_gradedPlan.mpr ⟨hCp, Nat.one_pos, by change (1 : ℕ) ≤ C.card; omega⟩
  obtain ⟨sc, hsc⟩ := D₂_complete _ (hsing c)
  obtain ⟨s1, hs1⟩ := D₂_complete _ (hsing 1)
  obtain ⟨T, hT⟩ := D₂_complete _ hC1
  have hscC : GradedLe (D₂.cell sc) (C, 2) := by
    rw [hsc]; exact ⟨Finset.singleton_subset_iff.mpr hc, by change (1 : ℕ) ≤ 2; decide⟩
  have hscC₁ : GradedLe (D₂.cell sc) (C, 1) := by
    rw [hsc]; exact ⟨Finset.singleton_subset_iff.mpr hc, le_rfl⟩
  have hscU : GradedLe (D₂.cell sc) (Finset.univ, 2) := by
    rw [hsc]; exact ⟨Finset.subset_univ _, by change (1 : ℕ) ≤ 2; decide⟩
  have hscU₁ : GradedLe (D₂.cell sc) (Finset.univ, 1) := by
    rw [hsc]; exact ⟨Finset.subset_univ _, le_rfl⟩
  have hs1U : GradedLe (D₂.cell s1) (Finset.univ, 2) := by
    rw [hs1]; exact ⟨Finset.subset_univ _, by change (1 : ℕ) ≤ 2; decide⟩
  have hscP : IsProper sc := isProper_of_cell_singleton sc c hsc
  have hs1P : IsProper s1 := isProper_of_cell_singleton s1 1 hs1
  -- the restrictions to grade one
  have hq₁ := hq.mono h₁₂
  have hp₁ := hp.mono (h₁₂C C)
  -- the constants
  set vP := p ⟨sc, hscC⟩ with hvP
  set vq := q ⟨sc, hscU⟩ with hvq
  set x₀q := q ⟨H₀old, memH₀old₂⟩ with hx₀q
  set x₁q := q ⟨U_H, memU_H₂⟩ with hx₁q
  set Hq := q ⟨U_S, memU₂⟩ with hHq
  -- proper grade-one constancy
  have hpc : ∀ d : D₂.below (C, 2), IsProper d.1 → D₂.grade d.1 ≤ 1 → p d = vP := by
    intro d hd hg
    have := const_of_respects rfl hp₁ ⟨T, by rw [hT]; exact GradedLe.refl _⟩ hT
      ⟨d.1, ⟨d.2.1, hg⟩⟩ ⟨sc, hscC₁⟩ hd hscP
    rwa [show CellScheme.below.mono (h₁₂C C) ⟨d.1, ⟨d.2.1, hg⟩⟩ = d from Subtype.ext rfl,
      show CellScheme.below.mono (h₁₂C C) ⟨sc, hscC₁⟩ = ⟨sc, hscC⟩ from Subtype.ext rfl] at this
  have hqc : ∀ d : D₂.below (Finset.univ, 2), IsProper d.1 → D₂.grade d.1 ≤ 1 → q d = vq := by
    intro d hd hg
    have := const_of_respects rfl hq₁ ⟨U_H, memU₁⟩ cell_U_H ⟨d.1, ⟨d.2.1, hg⟩⟩ ⟨sc, hscU₁⟩ hd hscP
    rwa [show CellScheme.below.mono h₁₂ ⟨d.1, ⟨d.2.1, hg⟩⟩ = d from Subtype.ext rfl,
      show CellScheme.below.mono h₁₂ ⟨sc, hscU₁⟩ = ⟨sc, hscU⟩ from Subtype.ext rfl] at this
  -- the grade-one facts, through the restriction
  have hq1 : q ⟨H₀new, memH₀new₂⟩ = x₁q := by
    have := H₀new_eq_U_H_of_respects hq₁
    rwa [show CellScheme.below.mono h₁₂ ⟨H₀new, memB le_rfl⟩ = ⟨H₀new, memH₀new₂⟩ from
      Subtype.ext rfl, show CellScheme.below.mono h₁₂ ⟨U_H, memU₁⟩ = ⟨U_H, memU_H₂⟩ from
      Subtype.ext rfl] at this
  have hq01 : x₀q ≤ x₁q := by
    have := le_U_H_of_respects hq₁ ⟨H₀old, memA le_rfl⟩
    rwa [show CellScheme.below.mono h₁₂ ⟨H₀old, memA le_rfl⟩ = ⟨H₀old, memH₀old₂⟩ from
      Subtype.ext rfl, show CellScheme.below.mono h₁₂ ⟨U_H, memU₁⟩ = ⟨U_H, memU_H₂⟩ from
      Subtype.ext rfl] at this
  have hcoup : x₀q = ⊥ → x₁q = ⊥ := by
    have := U_H_eq_bot_of_H₀old hq₁
    rwa [show CellScheme.below.mono h₁₂ ⟨H₀old, memA le_rfl⟩ = ⟨H₀old, memH₀old₂⟩ from
      Subtype.ext rfl, show CellScheme.below.mono h₁₂ ⟨U_H, memU₁⟩ = ⟨U_H, memU_H₂⟩ from
      Subtype.ext rfl] at this
  have hvq0 : vq ≤ x₀q := by
    rw [← hqc ⟨s1, hs1U⟩ hs1P (by change (D₂.cell s1).2 ≤ 1; rw [hs1])]
    obtain ⟨Xi, hXi, hle⟩ := hq.availability ⟨s1, hs1U⟩ ⟨H₀old, memH₀old₂⟩ (by
        change (D₂.cell s1).1 ⊆ D₂.scope H₀old; rw [hs1, scope_H₀old']; decide)
      (by change (D₂.cell s1).2 = D₂.grade H₀old; rw [hs1, grade_H₀old])
    have : Xi = ⟨H₀old, memH₀old₂⟩ :=
      Subtype.ext (cell_inj_low hXi (by
        change (D₂.cell Xi.1).2 ≤ 2; rw [hXi]
        exact (show D₂.grade H₀old ≤ 2 by rw [grade_H₀old]; decide)))
    rw [this] at hle; exact hle
  have hagree_sc : min vq γ = min vP γ := by
    have := hagree ⟨sc, hscC⟩
    rwa [show CellScheme.below.mono h ⟨sc, hscC⟩ = ⟨sc, hscU⟩ from Subtype.ext rfl] at this
  -- the grade-two facts
  have hHle : Hq ≤ x₁q := U_S_le_U_H_of_respects hq
  have hy : q ⟨s₀old, mems₀old₂⟩ = min x₀q Hq := s₀old_eq_min_of_respects hq
  have hs₀new : q ⟨s₀new, mems₀new₂⟩ = Hq := s₀new_eq_U_S_of_respects hq
  have hHbot : min x₀q Hq = ⊥ → Hq = ⊥ := fun h0 => U_S_eq_bot_of_s₀old hq (hy.trans h0)
  -- self-visibility of the constants
  have hvP_vis : SelfVis 1 vP := by
    have := selfVis_of_respects hp ⟨sc, hscC⟩
    change SelfVis (D₂.grade sc) vP at this
    rwa [show D₂.grade sc = 1 by change (D₂.cell sc).2 = 1; rw [hsc]] at this
  have hx₀q_vis : SelfVis 1 x₀q := by
    have := selfVis_of_respects hq ⟨H₀old, memH₀old₂⟩
    change SelfVis (D₂.grade H₀old) x₀q at this
    rwa [grade_H₀old] at this
  have hx₁q_vis : SelfVis 1 x₁q := by
    have := selfVis_of_respects hq ⟨U_H, memU_H₂⟩
    change SelfVis (D₂.grade U_H) x₁q at this
    rwa [grade_U_H] at this
  have hH_vis : SelfVis 2 Hq := by
    have := selfVis_of_respects hq ⟨U_S, memU₂⟩
    change SelfVis (D₂.grade U_S) Hq at this
    rwa [grade_U_S] at this
  have hmin_vis : SelfVis 2 (min x₀q Hq) := by
    have := selfVis_of_respects hq ⟨s₀old, mems₀old₂⟩
    change SelfVis (D₂.grade s₀old) (q ⟨s₀old, mems₀old₂⟩) at this
    rwa [grade_s₀old, hy] at this
  -- membership of the faces in the pair
  have hAB : ¬ (GradedLe (D₂.cell H₀old) (C, 2) ∧ GradedLe (D₂.cell H₀new) (C, 2)) := by
    rintro ⟨hA, hB⟩
    apply hC
    apply Finset.eq_univ_of_forall
    intro i
    have h0 : ({0, 1, 2} : Finset (Fin 4)) ⊆ C := by
      have := hA.1; change D₂.scope H₀old ⊆ C at this; rwa [scope_H₀old'] at this
    have h3 : ({1, 2, 3} : Finset (Fin 4)) ⊆ C := by
      have := hB.1; change D₂.scope H₀new ⊆ C at this; rwa [scope_H₀new] at this
    fin_cases i
    · exact h0 (by decide)
    · exact h0 (by decide)
    · exact h0 (by decide)
    · exact h3 (by decide)
  have hUC : ¬ GradedLe (D₂.cell U_H) (C, 2) := fun hU => hC (Finset.univ_subset_iff.mp (by
    have := hU.1; rw [cell_U_H] at this; exact this))
  have hUSC : ¬ GradedLe (D₂.cell U_S) (C, 2) := fun hU => hC (Finset.univ_subset_iff.mp (by
    have := hU.1; rw [cell_U_S] at this; exact this))
  have hAs : GradedLe (D₂.cell H₀old) (C, 2) → GradedLe (D₂.cell s₀old) (C, 2) := fun hA =>
    ⟨by change D₂.scope s₀old ⊆ C; rw [scope_s₀old]; have := hA.1
        change D₂.scope H₀old ⊆ C at this; rwa [scope_H₀old'] at this,
     by change D₂.grade s₀old ≤ 2; rw [grade_s₀old]⟩
  have hsA : GradedLe (D₂.cell s₀old) (C, 2) → GradedLe (D₂.cell H₀old) (C, 2) := fun hs =>
    ⟨by change D₂.scope H₀old ⊆ C; rw [scope_H₀old']; have := hs.1
        change D₂.scope s₀old ⊆ C at this; rwa [scope_s₀old] at this,
     by change D₂.grade H₀old ≤ 2; rw [grade_H₀old]; decide⟩
  have hBs : GradedLe (D₂.cell H₀new) (C, 2) → GradedLe (D₂.cell s₀new) (C, 2) := fun hB =>
    ⟨by change D₂.scope s₀new ⊆ C; rw [scope_s₀new]; have := hB.1
        change D₂.scope H₀new ⊆ C at this; rwa [scope_H₀new] at this,
     by change D₂.grade s₀new ≤ 2; rw [grade_s₀new]⟩
  have hsB : GradedLe (D₂.cell s₀new) (C, 2) → GradedLe (D₂.cell H₀new) (C, 2) := fun hs =>
    ⟨by change D₂.scope H₀new ⊆ C; rw [scope_H₀new]; have := hs.1
        change D₂.scope s₀new ⊆ C at this; rwa [scope_s₀new] at this,
     by change D₂.grade H₀new ≤ 2; rw [grade_H₀new]; decide⟩
  -- the proper value is below a protected face's grade-one label
  have hpA : ∀ hA : GradedLe (D₂.cell H₀old) (C, 2), vP ≤ p ⟨H₀old, hA⟩ := by
    intro hA
    have hs1C : GradedLe (D₂.cell s1) (C, 2) := by
      rw [hs1]; refine ⟨Finset.singleton_subset_iff.mpr (hA.1 ?_), by change (1 : ℕ) ≤ 2; decide⟩
      change (1 : Fin 4) ∈ D₂.scope H₀old; rw [scope_H₀old']; decide
    rw [← hpc ⟨s1, hs1C⟩ hs1P (by change (D₂.cell s1).2 ≤ 1; rw [hs1])]
    obtain ⟨Xi, hXi, hle⟩ := hp.availability ⟨s1, hs1C⟩ ⟨H₀old, hA⟩ (by
        change (D₂.cell s1).1 ⊆ D₂.scope H₀old; rw [hs1, scope_H₀old']; decide)
      (by change (D₂.cell s1).2 = D₂.grade H₀old; rw [hs1, grade_H₀old])
    have : Xi = ⟨H₀old, hA⟩ :=
      Subtype.ext (cell_inj_low hXi (by
        change (D₂.cell Xi.1).2 ≤ 2; rw [hXi]
        exact (show D₂.grade H₀old ≤ 2 by rw [grade_H₀old]; decide)))
    rw [this] at hle; exact hle
  have hpB : ∀ hB : GradedLe (D₂.cell H₀new) (C, 2), vP ≤ p ⟨H₀new, hB⟩ := by
    intro hB
    have hs1C : GradedLe (D₂.cell s1) (C, 2) := by
      rw [hs1]; refine ⟨Finset.singleton_subset_iff.mpr (hB.1 ?_), by change (1 : ℕ) ≤ 2; decide⟩
      change (1 : Fin 4) ∈ D₂.scope H₀new; rw [scope_H₀new]; decide
    rw [← hpc ⟨s1, hs1C⟩ hs1P (by change (D₂.cell s1).2 ≤ 1; rw [hs1])]
    obtain ⟨Xi, hXi, hle⟩ := hp.availability ⟨s1, hs1C⟩ ⟨H₀new, hB⟩ (by
        change (D₂.cell s1).1 ⊆ D₂.scope H₀new; rw [hs1, scope_H₀new]; decide)
      (by change (D₂.cell s1).2 = D₂.grade H₀new; rw [hs1, grade_H₀new])
    have : Xi = ⟨H₀new, hB⟩ :=
      Subtype.ext (cell_inj_low hXi (by
        change (D₂.cell Xi.1).2 ≤ 2; rw [hXi]
        exact (show D₂.grade H₀new ≤ 2 by rw [grade_H₀new]; decide)))
    rw [this] at hle; exact hle
  -- the agreements at the faces
  have hagA : ∀ hA : GradedLe (D₂.cell H₀old) (C, 2), min x₀q γ = min (p ⟨H₀old, hA⟩) γ :=
    fun hA => hagree ⟨H₀old, hA⟩
  have hagB : ∀ hB : GradedLe (D₂.cell H₀new) (C, 2), min x₁q γ = min (p ⟨H₀new, hB⟩) γ :=
    fun hB => by rw [← hq1]; exact hagree ⟨H₀new, hB⟩
  have hagAs : ∀ hs : GradedLe (D₂.cell s₀old) (C, 2),
      min (min x₀q Hq) γ = min (p ⟨s₀old, hs⟩) γ := fun hs => by rw [← hy]; exact hagree ⟨s₀old, hs⟩
  have hagBs : ∀ hs : GradedLe (D₂.cell s₀new) (C, 2), min Hq γ = min (p ⟨s₀new, hs⟩) γ :=
    fun hs => by rw [← hs₀new]; exact hagree ⟨s₀new, hs⟩
  -- **the rules**
  obtain ⟨x₀', x₁', H', R, hxA, hxB, hxAs, hxBs⟩ :
      ∃ x₀' x₁' H' : ExtOrd, Retuned vP x₀q x₁q Hq γ x₀' x₁' H' ∧
        (∀ hA : GradedLe (D₂.cell H₀old) (C, 2), x₀' = p ⟨H₀old, hA⟩) ∧
        (∀ hB : GradedLe (D₂.cell H₀new) (C, 2), x₁' = p ⟨H₀new, hB⟩) ∧
        (∀ hs : GradedLe (D₂.cell s₀old) (C, 2), min x₀' H' = p ⟨s₀old, hs⟩) ∧
        (∀ hs : GradedLe (D₂.cell s₀new) (C, 2), H' = p ⟨s₀new, hs⟩) := by
    by_cases hA : GradedLe (D₂.cell H₀old) (C, 2)
    · -- the old face is protected
      have hB : ¬ GradedLe (D₂.cell H₀new) (C, 2) := fun hB => hAB ⟨hA, hB⟩
      have hxp_vis : SelfVis 1 (p ⟨H₀old, hA⟩) := by
        have := selfVis_of_respects hp ⟨H₀old, hA⟩
        change SelfVis (D₂.grade H₀old) _ at this
        rwa [grade_H₀old] at this
      have hhp_vis : SelfVis 2 (p ⟨s₀old, hAs hA⟩) := by
        have := selfVis_of_respects hp ⟨s₀old, hAs hA⟩
        change SelfVis (D₂.grade s₀old) _ at this
        rwa [grade_s₀old] at this
      obtain ⟨x₀', x₁', H', R, hx, hH⟩ := rule_two_old hx₁q_vis hH_vis hq01 hcoup hHle hHbot
        hxp_vis hhp_vis (hpA hA) (s₀old_le_H₀old_of_respects hp (hAs hA) hA) (hagA hA)
        (hagAs (hAs hA))
      exact ⟨x₀', x₁', H', R, fun _ => hx, fun hB' => absurd hB' hB, fun _ => hH,
        fun hs => absurd (hsB hs) hB⟩
    · by_cases hB : GradedLe (D₂.cell H₀new) (C, 2)
      · -- the copy face is protected
        have hxp_vis : SelfVis 1 (p ⟨H₀new, hB⟩) := by
          have := selfVis_of_respects hp ⟨H₀new, hB⟩
          change SelfVis (D₂.grade H₀new) _ at this
          rwa [grade_H₀new] at this
        have hhp_vis : SelfVis 2 (p ⟨s₀new, hBs hB⟩) := by
          have := selfVis_of_respects hp ⟨s₀new, hBs hB⟩
          change SelfVis (D₂.grade s₀new) _ at this
          rwa [grade_s₀new] at this
        obtain ⟨x₀', x₁', H', R, hx, hH⟩ := rule_two_copy hvP_vis hx₀q_vis hvq0 hq01 hcoup
          hmin_vis hγ' hagree_sc hxp_vis hhp_vis (hpB hB)
          (s₀new_le_H₀new_of_respects hp (hBs hB) hB) (hagB hB) (hagBs (hBs hB))
        exact ⟨x₀', x₁', H', R, fun hA' => absurd hA' hA, fun _ => hx,
          fun hs => absurd (hsA hs) hA, fun _ => hH⟩
      · -- only the proper value is protected
        obtain ⟨x₀', x₁', H', R⟩ := rule_two_v hvP_vis hx₀q_vis hx₁q_vis hH_vis hvq0 hq01 hcoup
          hHle hmin_vis hγ' hagree_sc
        exact ⟨x₀', x₁', H', R, fun hA' => absurd hA' hA, fun hB' => absurd hB' hB,
          fun hs => absurd (hsA hs) hA, fun hs => absurd (hsB hs) hB⟩
  -- **the retuned labelling**
  set q' := retune₂ C p x₀' x₁' H' vP with hq'def
  have S : Shape₂ q' vP x₀' x₁' H' := by
    refine ⟨?_, ?_, retune₂_U_H hUC, ?_, ?_, retune₂_U_S hUSC, ?_⟩
    · by_cases hA : GradedLe (D₂.cell H₀old) (C, 2)
      · rw [hq'def, retune₂_in ⟨H₀old, memH₀old₂⟩ hA, hxA hA]
      · exact retune₂_H₀old hA
    · by_cases hB : GradedLe (D₂.cell H₀new) (C, 2)
      · rw [hq'def, retune₂_in ⟨H₀new, memH₀new₂⟩ hB, hxB hB]
      · exact retune₂_H₀new hB
    · by_cases hs : GradedLe (D₂.cell s₀old) (C, 2)
      · rw [hq'def, retune₂_in ⟨s₀old, mems₀old₂⟩ hs, hxAs hs]
      · exact retune₂_s₀old hs
    · by_cases hs : GradedLe (D₂.cell s₀new) (C, 2)
      · rw [hq'def, retune₂_in ⟨s₀new, mems₀new₂⟩ hs, hxBs hs]
      · exact retune₂_s₀new hs
    · intro d hd
      by_cases hdC : GradedLe (D₂.cell d.1) (C, 2)
      · rw [hq'def, retune₂_in d hdC]
        by_cases hg : D₂.grade d.1 = 2
        · rw [ite_eq_left hg]; exact proper_two_eq_bot' hp ⟨d.1, hdC⟩ hd hg
        · rw [ite_eq_right hg]
          exact hpc ⟨d.1, hdC⟩ hd (show D₂.grade d.1 ≤ 1 by
            have := d.2.2; change D₂.grade d.1 ≤ 2 at this; omega)
      · exact retune₂_proper d hd hdC
  have L : Legal₂ vP x₀' x₁' H' := R.legal hvP_vis
  refine ⟨q', respects_of_shape₂ L S, ?_, ?_⟩
  · -- capped agreement
    intro d
    by_cases hdC : GradedLe (D₂.cell d.1) (C, 2)
    · rw [hq'def, retune₂_in d hdC]
      have := hagree ⟨d.1, hdC⟩
      rw [show CellScheme.below.mono h ⟨d.1, hdC⟩ = d from Subtype.ext rfl] at this
      exact this.symm
    · rcases two_cases (not_mute_of_two d) d.2.2 with h' | h' | h' | h' | h' | h' | ⟨h', hg⟩ |
        ⟨h', hg⟩
      · rw [show d = ⟨H₀old, memH₀old₂⟩ from Subtype.ext h', S.at_H₀old]; exact R.ag0
      · rw [show d = ⟨H₀new, memH₀new₂⟩ from Subtype.ext h', S.at_H₀new, hq1]; exact R.ag1
      · rw [show d = ⟨U_H, memU_H₂⟩ from Subtype.ext h', S.at_U_H]; exact R.ag1
      · rw [show d = ⟨s₀old, mems₀old₂⟩ from Subtype.ext h', S.at_s₀old, hy]; exact R.agmin
      · rw [show d = ⟨s₀new, mems₀new₂⟩ from Subtype.ext h', S.at_s₀new, hs₀new]; exact R.agH
      · rw [show d = ⟨U_S, memU₂⟩ from Subtype.ext h', S.at_U_S]; exact R.agH
      · rw [S.at_proper d h', ite_eq_right (by omega), hqc d h' hg.le]; exact hagree_sc.symm
      · rw [S.at_proper d h', ite_eq_left hg, proper_two_eq_bot hq d h' hg]
  · -- literal preservation
    intro d
    exact retune₂_in _ d.2

/-- **The scope-changing obligation at grades one and two.** -/
theorem properToFull₃_of_le_two (CI : Finset (Fin 4) × ℕ) (j : ℕ) (hj : j ≤ 2)
    (hCI : CI ∈ Plan.gradedPlan plan₄) (hC : CI.1 ≠ Finset.univ)
    (hU : (Finset.univ, j) ∈ Plan.gradedPlan plan₄) (h : GradedLe CI (Finset.univ, j))
    (p : D₂.below CI → ExtOrd) (q : D₂.below (Finset.univ, j) → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow rows₃ CI p) (hq : RespectsSemanticsBelow rows₃ (Finset.univ, j) q)
    (hγ : extVisibilityReplace γ j j = γ)
    (hagree : ∀ d : D₂.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D₂.below (Finset.univ, j) → ExtOrd, RespectsSemanticsBelow rows₃ (Finset.univ, j) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D₂.below CI, q' (CellScheme.below.mono h d) = p d) := by
  obtain ⟨C, i⟩ := CI
  obtain ⟨hCp, hi0, -⟩ := Plan.mem_gradedPlan.mp hCI
  dsimp only at hCp hi0
  have hij : i ≤ j := h.2
  have hUp : (Finset.univ : Finset (Fin 4)) ∈ plan₄ := (Plan.mem_gradedPlan.mp hU).1
  have hi : GradedLe ((Finset.univ : Finset (Fin 4)), i) (Finset.univ, j) :=
    ⟨Finset.Subset.refl _, hij⟩
  have hCi : GradedLe (C, i) (Finset.univ, i) := ⟨Finset.subset_univ _, le_rfl⟩
  have hγi : extVisibilityReplace γ i i = γ := (show SelfVis j γ from hγ).mono hij
  have hagree' : ∀ d : D₂.below (C, i),
      min (q (CellScheme.below.mono hi (CellScheme.below.mono hCi d))) γ = min (p d) γ :=
    fun d => hagree d
  -- the same-grade case at `(univ, i)`, then full-scope bountifulness up to `(univ, j)`
  have key : ∃ qᵢ : D₂.below (Finset.univ, i) → ExtOrd,
      RespectsSemanticsBelow rows₃ (Finset.univ, i) qᵢ ∧
      (∀ d, min (qᵢ d) γ = min (q (CellScheme.below.mono hi d)) γ) ∧
      (∀ d : D₂.below (C, i), qᵢ (CellScheme.below.mono hCi d) = p d) := by
    rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
    · exact properToFull₃_one C hCI hC hCi p _ γ hp (hq.mono hi) hγi hagree'
    · exact properToFull₃_two C hCI hC hCi p _ γ hp (hq.mono hi) hγi hagree'
  obtain ⟨qᵢ, hqᵢ, hqᵢγ, hqᵢext⟩ := key
  obtain ⟨q', hq', hq'γ, hq'ext⟩ :=
    bountiful_full_scope rows₃ hi qᵢ q γ hqᵢ hq hγ (fun d => (hqᵢγ d).symm)
  refine ⟨q', hq', hq'γ, fun d => ?_⟩
  have e : CellScheme.below.mono h d =
      CellScheme.below.mono hi (CellScheme.below.mono hCi d) := rfl
  rw [e, hq'ext, hqᵢext]

end Endpoint

end VaughtConjecture.Knight
