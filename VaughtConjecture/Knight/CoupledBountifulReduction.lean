/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TwoContextCoupled

/-! # Bountifulness of the coupled semantics, reduced by scope

The three modified rows of `rows₃` are frozen.  **The reduction** (`rows₃_isBountiful_of`):
bountifulness (Def. 2.5.14) of `rows₃` follows from the **scope-changing obligation at grades
at most three** (`ProperToFull₃Low`: a proper pair below `(univ, j)`, `j ≤ 3`).  The cases with a
proper target pair are the fixed glue's (`bountiful₂_A`, `bountiful₂_B`): every row in a proper
lower set is unchanged (`respects₃_iff_of_proper`).  The full-scope pairs are the general
full-scope extension (`bountiful_full_scope`), and grade four reduces to grade three exactly as
for the fixed glue.  Under the obligation the coupled domain is a `SemScheme`
(`semSchemeCoupled`).

**The smallest remaining case, grade one** (`(C, 1)` below `(univ, 1)`, `C` proper): the
constraints a respecting labelling `q` of `(univ, 1)` must satisfy, extracted from actual
respecting inputs — the separation deliberately breaks the old glue's controller-probe
equalities and creates new ones:
* every label is at most the controller's (`le_U_H_of_respects`; the controller `U_H` is the
  unique cell of graded index `(univ, 1)`, `eq_U_H_of_cell`);
* **the new probe equality** `q H₀new = q U_H` (`H₀new_eq_U_H_of_respects`): the copy and the
  diagonal read the same separating source `ω·2+2` at the controller — in the fixed glue the
  three occurrences were identified, now the copy is tied to the controller instead;
* **the clause-5 coupling at the bottom label** (`U_H_eq_bot_of_H₀old`): the old occurrence's
  source `ω·2+1` and the separating source `ω·2+2` sit in one `ω`-block one step apart, so a
  shifter sending the first to `⊥` sends the second to `⊥`: `q H₀old = ⊥ → q U_H = ⊥`.  A
  retuning rule choosing the controller's label freely above a bottom old label is refuted by
  this constraint alone.

**A witness for the retuning** (`Witness.stepLimit`): the two-valued shifter `c₀` below a
*limit* cutoff `ω·n`, `c₁` from it on, is a witness unconditionally in the values (the bottom
fibre allowed), because visibility replacement never crosses a limit (`evr_lt_limit`,
`evr_ge_limit`) — the modification `Witness.raise`/`Witness.lower` cannot express (their cutoff
needs finite part above the threshold).  It is the witness at the level-one witness rows (sources
`ω+1` at the proper cells, `ω·2+1` at the diagonal), where the free labels at the proper cells
and at the old occurrence are chosen independently.

Not done: the obligation `ProperToFull₃Low` itself (the retuning at grades one to three).
Construction-private (not root-exported). -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

section Reduction

/-- Rows at cells of proper scope are unchanged. -/
theorem rows₃_E_of_proper_scope {Sig : Cell D₂} (h : D₂.scope Sig ≠ Finset.univ) :
    rows₃.E Sig = rows₂.E Sig := by
  funext d
  refine E₃_of_ne ?_ ?_ ?_ d
  · rintro rfl; exact h (congrArg Prod.fst cell_U_H)
  · rintro rfl; exact h (congrArg Prod.fst cell_U_S)
  · rintro rfl; exact h (congrArg Prod.fst cell_ub₁)

theorem scope_ne_univ_of_below {BJ : Finset (Fin 4) × ℕ} (hB : BJ.1 ≠ Finset.univ)
    (d : D₂.below BJ) : D₂.scope d.1 ≠ Finset.univ := fun h =>
  hB (Finset.univ_subset_iff.mp (h ▸ d.2.1))

/-- **Respect below a proper pair is the same for the two semantics.** -/
theorem respects₃_iff_of_proper {BJ : Finset (Fin 4) × ℕ} (hB : BJ.1 ≠ Finset.univ)
    (r : D₂.below BJ → ExtOrd) :
    RespectsSemanticsBelow rows₃ BJ r ↔ RespectsSemanticsBelow rows₂ BJ r :=
  ⟨fun h => h.congr_sem fun Sig => (rows₃_E_of_proper_scope (scope_ne_univ_of_below hB Sig)).symm,
   fun h => h.congr_sem fun Sig => rows₃_E_of_proper_scope (scope_ne_univ_of_below hB Sig)⟩

/-- **The scope-changing obligation** for the coupled semantics, at grades at most three. -/
def ProperToFull₃Low : Prop :=
  ∀ (CI : Finset (Fin 4) × ℕ) (j : ℕ), j ≤ 3 → CI ∈ Plan.gradedPlan plan₄ →
    CI.1 ≠ Finset.univ → (Finset.univ, j) ∈ Plan.gradedPlan plan₄ →
    (h : GradedLe CI (Finset.univ, j)) →
    ∀ (p : D₂.below CI → ExtOrd) (q : D₂.below (Finset.univ, j) → ExtOrd) (γ : ExtOrd),
      RespectsSemanticsBelow rows₃ CI p → RespectsSemanticsBelow rows₃ (Finset.univ, j) q →
      extVisibilityReplace γ j j = γ →
      (∀ d : D₂.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) →
      ∃ q' : D₂.below (Finset.univ, j) → ExtOrd, RespectsSemanticsBelow rows₃ (Finset.univ, j) q' ∧
        (∀ d, min (q' d) γ = min (q d) γ) ∧
        (∀ d : D₂.below CI, q' (CellScheme.below.mono h d) = p d)

/-- **Bountifulness of the coupled semantics, reduced to the scope-changing obligation.** -/
theorem rows₃_isBountiful_of (H : ProperToFull₃Low) : rows₃.IsBountiful := by
  intro CI BJ hCI hBJ h hne p q γ hp hq hγ hagree
  by_cases hB : BJ.1 = Finset.univ
  · by_cases hC : CI.1 = Finset.univ
    · obtain ⟨B, j⟩ := BJ
      obtain ⟨C, i⟩ := CI
      dsimp only at hB hC
      subst hB hC
      exact bountiful_full_scope rows₃ h p q γ hp hq hγ hagree
    · obtain ⟨B, j⟩ := BJ
      dsimp only at hB
      subst hB
      by_cases hj3 : j ≤ 3
      · exact H CI j hj3 hCI hC hBJ h p q γ hp hq hγ hagree
      · have hj4 : j = 4 := by
          obtain ⟨-, -, hjc⟩ := Plan.mem_gradedPlan.mp hBJ
          change j ≤ (Finset.univ : Finset (Fin 4)).card at hjc
          rw [Finset.card_univ, Fintype.card_fin] at hjc
          omega
        subst hj4
        have h₃ : GradedLe ((Finset.univ : Finset (Fin 4)), 3) (Finset.univ, 4) :=
          ⟨Finset.Subset.refl _, by omega⟩
        have hC3 : GradedLe CI (Finset.univ, 3) := by
          refine ⟨Finset.subset_univ _, ?_⟩
          obtain ⟨-, -, hiC⟩ := Plan.mem_gradedPlan.mp hCI
          have h4 : CI.1.card ≤ 4 := (Finset.card_le_univ _).trans (by simp)
          have hne4 : CI.1.card ≠ 4 := fun e =>
            hC (Finset.eq_univ_of_card _ (by rw [Fintype.card_fin]; exact e))
          exact hiC.trans (by omega)
        have hu3 : ((Finset.univ : Finset (Fin 4)), 3) ∈ Plan.gradedPlan plan₄ :=
          Plan.mem_gradedPlan.mpr ⟨by decide, by decide, by decide⟩
        obtain ⟨q₃, hq₃, hq₃γ, hq₃ext⟩ := H CI 3 le_rfl hCI hC hu3 hC3
          p (fun d => q (CellScheme.below.mono h₃ d)) γ hp (hq.mono h₃)
          ((show SelfVis 4 γ from hγ).mono (by omega)) (fun d => hagree d)
        obtain ⟨q', hq', hq'γ, hq'ext⟩ := bountiful_full_scope rows₃ h₃ q₃ q γ hq₃ hq hγ
          (fun d => (hq₃γ d).symm)
        refine ⟨q', hq', hq'γ, fun d => ?_⟩
        have e : CellScheme.below.mono h d =
            CellScheme.below.mono h₃ (CellScheme.below.mono hC3 d) := rfl
        rw [e, hq'ext, hq₃ext]
  · have hC : CI.1 ≠ Finset.univ := fun e => hB (Finset.univ_subset_iff.mp (e ▸ h.1))
    rw [respects₃_iff_of_proper hC] at hp
    rw [respects₃_iff_of_proper hB] at hq
    have hBp : BJ.1 ∈ plan₄ := (Plan.mem_gradedPlan.mp hBJ).1
    rcases proper_side BJ.1 hBp hB with h3 | h0
    · obtain ⟨q', hq', hq'γ, hq'ext⟩ := bountiful₂_A CI BJ hCI hBJ h h3 p q γ hp hq hγ hagree
      exact ⟨q', (respects₃_iff_of_proper hB q').mpr hq', hq'γ, hq'ext⟩
    · obtain ⟨q', hq', hq'γ, hq'ext⟩ := bountiful₂_B CI BJ hCI hBJ h h0 p q γ hp hq hγ hagree
      exact ⟨q', (respects₃_iff_of_proper hB q').mpr hq', hq'γ, hq'ext⟩

/-- **The coupled domain**, conditional on the scope-changing obligation. -/
noncomputable def semSchemeCoupled (H : ProperToFull₃Low) : SemScheme 4 where
  scheme := D₂
  rows := rows₃
  rows_coded := rows₃_coded
  consistent := rows₃_consistent
  bountiful := rows₃_isBountiful_of H
  complete := D₂_complete

end Reduction


/-! ## The smallest scope-changing case: grade one -/

section GradeOne

theorem memU₁ : GradedLe (D₂.cell U_H) (Finset.univ, 1) := by rw [cell_U_H]; exact GradedLe.refl _

/-- The unique cell of graded index `(univ, 1)` is the grade-one controller. -/
theorem eq_U_H_of_cell {d : Cell D₂} (h : D₂.cell d = (Finset.univ, 1)) : d = U_H := by
  have hnm : ¬ mute₂ d := by
    intro hm; change D₂.cell d = _ at hm; rw [h] at hm
    exact absurd (congrArg Prod.snd hm) (by decide)
  rcases cell_cases d hnm with ⟨i, rfl⟩ | hB | rfl | rfl | rfl | rfl | rfl
  · exfalso
    exact three_not_mem_scope_castAdd i (by
      change (3 : Fin 4) ∈ (D₂.cell _).1; rw [h]; exact Finset.mem_univ _)
  · exfalso
    have : (0 : Fin 4) ∈ D₂.scope d := by
      change (0 : Fin 4) ∈ (D₂.cell d).1; rw [h]; exact Finset.mem_univ _
    exact absurd (hB.1 this) (by decide)
  · rfl
  · exfalso; rw [cell_U_S] at h; exact absurd (congrArg Prod.snd h) (by decide)
  · exfalso; rw [cell_A₁c] at h; exact absurd (congrArg Prod.snd h) (by decide)
  · exfalso; rw [cell_A₂c] at h; exact absurd (congrArg Prod.snd h) (by decide)
  · exfalso; rw [cell_ub₁] at h; exact absurd (congrArg Prod.snd h) (by decide)

theorem evr_δ_two : extVisibilityReplace (ofOrd (ω2 1)) 2 2 = ofOrd (ω2 2) := by
  rw [extVisibilityReplace_ofOrd]
  unfold visibilityReplace
  rw [ite_eq_left (by rw [fp_ω2]; omega)]
  unfold ordinalReplace
  rw [limitPart_mul_add]

variable {q : D₂.below (Finset.univ, 1) → ExtOrd}
  (hq : RespectsSemanticsBelow rows₃ (Finset.univ, 1) q)
include hq

/-- **Availability at grade one**: every label is at most the controller's. -/
theorem le_U_H_of_respects (d : D₂.below (Finset.univ, 1)) : q d ≤ q ⟨U_H, memU₁⟩ := by
  obtain ⟨Xi, hXi, hle⟩ := hq.availability d ⟨U_H, memU₁⟩ (by
      change D₂.scope d.1 ⊆ (D₂.cell U_H).1; rw [cell_U_H]; exact Finset.subset_univ _)
    (by
      change (D₂.cell d.1).2 = (D₂.cell U_H).2
      rw [cell_U_H]; exact le_antisymm d.2.2 (D₂.grade_pos _))
  rw [cell_U_H] at hXi
  have : Xi = ⟨U_H, memU₁⟩ := Subtype.ext (eq_U_H_of_cell hXi)
  rw [this] at hle; exact hle

/-- **The new controller-probe equality**: the copy and the controller read the same separating
source at the controller, so they are labelled equally. -/
theorem H₀new_eq_U_H_of_respects : q ⟨H₀new, memB le_rfl⟩ = q ⟨U_H, memU₁⟩ := by
  refine le_antisymm (le_U_H_of_respects hq _) ?_
  have h := hq.probe_eq_of_row_eq ⟨U_H, memU₁⟩ ⟨H₀new, memB_U⟩ ⟨U_H, refl_U⟩ (by
      exact (E₃_U_H ⟨H₀new, memB_U⟩).trans
        ((vU_of_new ⟨ret₂_H₀new, H₀old_ne_H₀new.symm⟩).trans
          ((vU_of_new ⟨ret₂_U_H, H₀old_ne_U_H.symm⟩).symm.trans (E₃_U_H ⟨U_H, refl_U⟩).symm)))
    (by rw [grade_H₀new, grade_U_H])
  have e1 : CellScheme.below.incl ⟨U_H, memU₁⟩ ⟨H₀new, memB_U⟩ = ⟨H₀new, memB le_rfl⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨U_H, memU₁⟩ ⟨U_H, refl_U⟩ = ⟨U_H, memU₁⟩ := Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.symm ▸ min_le_left _ _

/-- **The clause-5 coupling at the bottom label**: the old occurrence's source `ω·2+1` and the
separating source `ω·2+2` sit in one block one step apart, so a shifter sending the first to `⊥`
sends the second to `⊥` — the controller's label is `⊥` whenever the old occurrence's is. -/
theorem U_H_eq_bot_of_H₀old (h : q ⟨H₀old, memA le_rfl⟩ = ⊥) : q ⟨U_H, memU₁⟩ = ⊥ := by
  obtain ⟨g, σ, hw, heq⟩ := TransformsTo.witness (hq.locality ⟨U_H, memU₁⟩)
  have h0 : min (q ⟨H₀old, memA le_rfl⟩) (q ⟨U_H, memU₁⟩) =
      min (σ (rows₃.E U_H ⟨H₀old, memA_U⟩)) (g (D₂.grade H₀old)) := heq ⟨H₀old, memA_U⟩
  have h2 : min (q ⟨U_H, memU₁⟩) (q ⟨U_H, memU₁⟩) =
      min (σ (rows₃.E U_H ⟨U_H, refl_U⟩)) (g (D₂.grade U_H)) := heq ⟨U_H, refl_U⟩
  have e0 : rows₃.E U_H ⟨H₀old, memA_U⟩ = ofOrd (ω2 1) :=
    (E₃_U_H _).trans (vU_H₀old.trans H₀c_δ_num)
  have e2 : rows₃.E U_H ⟨U_H, refl_U⟩ = ofOrd (ω2 2) :=
    (E₃_U_H _).trans ((vU_of_new ⟨ret₂_U_H, H₀old_ne_U_H.symm⟩).trans wSep_num)
  rw [h, e0, grade_H₀old, min_eq_left bot_le] at h0
  rw [min_self, e2, grade_U_H] at h2
  rcases min_eq_bot.mp h0.symm with hσ | hg
  · have h5 := hw.clause5 (ofOrd (ω2 1)) 2 (by rw [hσ]; exact bot_le) 2 le_rfl
    rw [hσ, extVisibilityReplace_bot, evr_δ_two] at h5
    rw [h2, h5]; exact min_eq_left bot_le
  · rw [h2, hg]; exact min_eq_right bot_le

end GradeOne

/-! ## A step witness at a limit cutoff -/

section StepLimit

open Classical in
/-- The two-valued shifter: `c₀` below the limit cutoff `ω·n`, `c₁` from it on. -/
noncomputable def stepShifter (n : ℕ) (c₀ c₁ : ExtOrd) : ExtOrd → ExtOrd :=
  fun a => if a = ⊥ then ⊥ else if a < ofOrd (Ordinal.omega0 * (n : Ordinal)) then c₀ else c₁

theorem stepShifter_bot (n : ℕ) (c₀ c₁ : ExtOrd) : stepShifter n c₀ c₁ ⊥ = ⊥ := by
  classical
  unfold stepShifter; rw [ite_eq_left rfl]
theorem stepShifter_of_lt {n : ℕ} {c₀ c₁ a : ExtOrd} (ha : a ≠ ⊥)
    (h : a < ofOrd (Ordinal.omega0 * (n : Ordinal))) : stepShifter n c₀ c₁ a = c₀ := by
  classical
  unfold stepShifter; rw [ite_eq_right ha, ite_eq_left h]
theorem stepShifter_of_ge {n : ℕ} {c₀ c₁ a : ExtOrd}
    (h : ofOrd (Ordinal.omega0 * (n : Ordinal)) ≤ a) : stepShifter n c₀ c₁ a = c₁ := by
  classical
  unfold stepShifter
  rw [ite_eq_right (fun hb => not_ofOrd_le_bot _ (hb ▸ h)), ite_eq_right (not_lt.mpr h)]

theorem limitPart_omega_mul (n : ℕ) : limitPart (Ordinal.omega0 * (n : Ordinal)) =
    Ordinal.omega0 * (n : Ordinal) := by
  have := limitPart_mul_add n 0
  rw [Nat.cast_zero, add_zero] at this; exact this

/-- Visibility replacement never crosses a limit cutoff, in either direction. -/
theorem evr_lt_limit {n : ℕ} {a : ExtOrd} (h : a < ofOrd (Ordinal.omega0 * (n : Ordinal)))
    (k i : ℕ) :
    extVisibilityReplace a k i < ofOrd (Ordinal.omega0 * (n : Ordinal)) := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · rw [extVisibilityReplace_bot]; exact bot_lt_ofOrd _
  · exact absurd h (not_lt.mpr le_top)
  · rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
    have hα := ofOrd_lt_ofOrd.mp h
    have hl : limitPart (visibilityReplace α k i) < limitPart (Ordinal.omega0 * (n : Ordinal)) := by
      rw [limitPart_visibilityReplace, limitPart_omega_mul]
      exact lt_of_le_of_lt (limitPart_le α) hα
    exact lt_of_lt_of_le (lt_limitPart_of_limitPart_lt hl) (limitPart_le _)
theorem evr_ge_limit {n : ℕ} {a : ExtOrd} (h : ofOrd (Ordinal.omega0 * (n : Ordinal)) ≤ a)
    (k i : ℕ) :
    ofOrd (Ordinal.omega0 * (n : Ordinal)) ≤ extVisibilityReplace a k i := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · exact absurd h (not_ofOrd_le_bot _)
  · rw [extVisibilityReplace_top]; exact le_top
  · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
    have hα := ofOrd_le_ofOrd.mp h
    calc Ordinal.omega0 * (n : Ordinal) = limitPart (Ordinal.omega0 * (n : Ordinal)) :=
          (limitPart_omega_mul n).symm
      _ ≤ limitPart α := limitPart_mono hα
      _ = limitPart (visibilityReplace α k i) := (limitPart_visibilityReplace α k i).symm
      _ ≤ visibilityReplace α k i := limitPart_le _

/-- **The step witness at a limit cutoff**: unconditional in the values (the bottom fibre is
allowed), because visibility replacement never crosses a limit. -/
theorem Witness.stepLimit (K n : ℕ) {c₀ c₁ : ExtOrd} (h : c₀ ≤ c₁) (hc₀ : SelfVis K c₀)
    (hc₁ : SelfVis K c₁) : Witness (gTop K) (stepShifter n c₀ c₁) where
  anti := (witness_id K).anti
  vis := (witness_id K).vis
  bot := stepShifter_bot n c₀ c₁
  mono := by
    intro a b hab
    by_cases ha : a = ⊥
    · rw [ha, stepShifter_bot]; exact bot_le
    have hb : b ≠ ⊥ := fun hb => ha (le_bot_iff.mp (hb ▸ hab))
    by_cases hal : a < ofOrd (Ordinal.omega0 * (n : Ordinal))
    · rw [stepShifter_of_lt ha hal]
      by_cases hbl : b < ofOrd (Ordinal.omega0 * (n : Ordinal))
      · rw [stepShifter_of_lt hb hbl]
      · rw [stepShifter_of_ge (not_lt.mp hbl)]; exact h
    · have hbl : ¬ b < ofOrd (Ordinal.omega0 * (n : Ordinal)) :=
        fun hbl => hal (lt_of_le_of_lt hab hbl)
      rw [stepShifter_of_ge (not_lt.mp hal), stepShifter_of_ge (not_lt.mp hbl)]
  clause5 := by
    intro α k hk i hi
    by_cases hα : α = ⊥
    · rw [hα, stepShifter_bot, extVisibilityReplace_bot, stepShifter_bot]
    have hα' : extVisibilityReplace α k i ≠ ⊥ := extVisibilityReplace_ne_bot hα k i
    by_cases hkK : k ≤ K
    · by_cases hal : α < ofOrd (Ordinal.omega0 * (n : Ordinal))
      · rw [stepShifter_of_lt hα hal, stepShifter_of_lt hα' (evr_lt_limit hal k i),
          evr_eq_self_of_selfVis (hc₀.mono hkK)]
      · rw [stepShifter_of_ge (not_lt.mp hal), stepShifter_of_ge (evr_ge_limit (not_lt.mp hal) k i),
          evr_eq_self_of_selfVis (hc₁.mono hkK)]
    · rw [gTop_of_gt (by omega)] at hk
      have hσ := le_bot_iff.mp hk
      by_cases hal : α < ofOrd (Ordinal.omega0 * (n : Ordinal))
      · rw [stepShifter_of_lt hα hal] at hσ
        rw [stepShifter_of_lt hα hal, stepShifter_of_lt hα' (evr_lt_limit hal k i), hσ,
          extVisibilityReplace_bot]
      · rw [stepShifter_of_ge (not_lt.mp hal)] at hσ
        rw [stepShifter_of_ge (not_lt.mp hal), stepShifter_of_ge (evr_ge_limit (not_lt.mp hal) k i),
          hσ, extVisibilityReplace_bot]

end StepLimit


end VaughtConjecture.Knight
