/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledGradeOne

/-! # Grade two of the coupled semantics' bountifulness: the parameter reduction on the cells

For a labelling `q` respecting the frozen rows `rows₃` on `(univ, 2)`, write `x₀ = q H₀old`,
`Y = q U_S` (the grade-two controller, the unique cell of graded index `(univ, 2)`,
`eq_U_S_of_cell`).  On the actual cells:
* `q s₀new = Y` (`s₀new_eq_U_S_of_respects`): the copy of `s₀` and the controller read the same
  separating source `ω·2+3` at the controller;
* `Y ≤ q U_H` (`U_S_le_U_H_of_respects`): the antitone suppressor at the separating source, read
  at grades one and two;
* **`q s₀old = min x₀ Y`** (`s₀old_eq_min_of_respects`): the controller reads the same source
  `ω·2+2` at the two old witnesses; the antitone suppressor bounds the grade-two probe by the
  grade-one probe, and the controller's own value (at most its grade-two suppressor) gives the
  reverse bound;
* every grade-two proper cell is labelled `⊥` (`proper_two_eq_bot`): its row is `⊥` everywhere;
* `q s₀old = ⊥ → Y = ⊥` (`U_S_eq_bot_of_s₀old`): the sources `ω·2+2` and `ω·2+3` sit one step
  apart in one block (clause 5 at threshold three).
Together with the grade-one triple `(v, x₀, x₁)` on the restriction to `(univ, 1)`, a respecting
labelling of `(univ, 2)` is the triple plus **one high label** `Y ≤ x₁`, with the level-two
witnesses reading `min x₀ Y` and `Y`, the grade-two proper cells `⊥`, and the visibility
constraints (`Y` and `min x₀ Y` self-visible at two) and the bottom coupling.

Not done: the grade-two retuning (`ProperToFull₃Low` at `j = 2`).  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

section GradeTwo

theorem memU₂ : GradedLe (D₂.cell U_S) (Finset.univ, 2) := by rw [cell_U_S]; exact GradedLe.refl _
theorem memH₀old₂ : GradedLe (D₂.cell H₀old) (Finset.univ, 2) := memA (by decide)
theorem memH₀new₂ : GradedLe (D₂.cell H₀new) (Finset.univ, 2) := memB (by decide)
theorem memU_H₂ : GradedLe (D₂.cell U_H) (Finset.univ, 2) := by
  rw [cell_U_H]; exact ⟨Finset.subset_univ _, by decide⟩
theorem mems₀old₂ : GradedLe (D₂.cell s₀old) (Finset.univ, 2) :=
  ⟨Finset.subset_univ _, by change D₂.grade s₀old ≤ 2; rw [grade_s₀old]⟩
theorem mems₀new₂ : GradedLe (D₂.cell s₀new) (Finset.univ, 2) :=
  ⟨Finset.subset_univ _, by change D₂.grade s₀new ≤ 2; rw [grade_s₀new]⟩
theorem H₀old_below_U_S' : GradedLe (D₂.cell H₀old) (D₂.cell U_S) := H₀old_below_U_S
theorem s₀old_below_U_S : GradedLe (D₂.cell s₀old) (D₂.cell U_S) := by
  rw [cell_U_S]; exact mems₀old₂
theorem s₀new_below_U_S : GradedLe (D₂.cell s₀new) (D₂.cell U_S) := by
  rw [cell_U_S]; exact mems₀new₂
theorem U_H_below_U_S : GradedLe (D₂.cell U_H) (D₂.cell U_S) := by
  rw [cell_U_S]; exact memU_H₂
theorem refl_U_S : GradedLe (D₂.cell U_S) (D₂.cell U_S) := GradedLe.refl _

/-- The unique cell of graded index `(univ, 2)` is the grade-two controller. -/
theorem eq_U_S_of_cell {d : Cell D₂} (h : D₂.cell d = (Finset.univ, 2)) : d = U_S :=
  cell_inj_low (h.trans cell_U_S.symm) (by change (D₂.cell d).2 ≤ 2; rw [h])

/-- The row of the grade-two controller at the six cells. -/
theorem rows₃_U_S_H₀old : rows₃.E U_S ⟨H₀old, H₀old_below_U_S⟩ = ofOrd (ω2 2) :=
  (E₃_U_S _).trans (by change vS H₀old = _; rw [vS_H₀old, s₀c_γ_num])
theorem rows₃_U_S_s₀old : rows₃.E U_S ⟨s₀old, s₀old_below_U_S⟩ = ofOrd (ω2 2) :=
  (E₃_U_S _).trans (by change vS s₀old = _; rw [vS_s₀old, s₀c_γ_num])
theorem rows₃_U_S_s₀new : rows₃.E U_S ⟨s₀new, s₀new_below_U_S⟩ = ofOrd (ω2 3) :=
  (E₃_U_S _).trans (by change vS s₀new = _; rw [vS_s₀new]; rfl)
theorem rows₃_U_S_U_H : rows₃.E U_S ⟨U_H, U_H_below_U_S⟩ = ofOrd (ω2 3) :=
  (E₃_U_S _).trans (by change vS U_H = _; rw [vS_U_H]; rfl)
theorem rows₃_U_S_self : rows₃.E U_S ⟨U_S, refl_U_S⟩ = ofOrd (ω2 3) :=
  (E₃_U_S _).trans (by
    change vS U_S = _; rw [vS_of_new ⟨Or.inr ret₂_U_S, fullCell_ne_old s₀X rfl⟩]; rfl)

theorem evr_ρ_three : extVisibilityReplace (ofOrd (ω2 2)) 3 3 = ofOrd (ω2 3) := by
  rw [extVisibilityReplace_ofOrd]
  unfold visibilityReplace
  rw [ite_eq_left (by rw [fp_ω2]; omega)]
  unfold ordinalReplace
  rw [limitPart_mul_add]

variable {q : D₂.below (Finset.univ, 2) → ExtOrd}
  (hq : RespectsSemanticsBelow rows₃ (Finset.univ, 2) q)
include hq

/-- **Availability at grade two**: every grade-two label is at most the controller's. -/
theorem le_U_S_of_respects (d : D₂.below (Finset.univ, 2)) (hd : D₂.grade d.1 = 2) :
    q d ≤ q ⟨U_S, memU₂⟩ := by
  obtain ⟨Xi, hXi, hle⟩ := hq.availability d ⟨U_S, memU₂⟩ (by
      change D₂.scope d.1 ⊆ (D₂.cell U_S).1; rw [cell_U_S]; exact Finset.subset_univ _)
    (by change D₂.grade d.1 = (D₂.cell U_S).2; rw [cell_U_S, hd])
  rw [cell_U_S] at hXi
  have : Xi = ⟨U_S, memU₂⟩ := Subtype.ext (eq_U_S_of_cell hXi)
  rw [this] at hle; exact hle

/-- **The copy of `s₀` is labelled like the controller.** -/
theorem s₀new_eq_U_S_of_respects : q ⟨s₀new, mems₀new₂⟩ = q ⟨U_S, memU₂⟩ := by
  refine le_antisymm (le_U_S_of_respects hq _ grade_s₀new) ?_
  have h := hq.probe_eq_of_row_eq ⟨U_S, memU₂⟩ ⟨s₀new, s₀new_below_U_S⟩ ⟨U_S, refl_U_S⟩
    (rows₃_U_S_s₀new.trans rows₃_U_S_self.symm) (by rw [grade_s₀new, grade_U_S])
  have e1 : CellScheme.below.incl ⟨U_S, memU₂⟩ ⟨s₀new, s₀new_below_U_S⟩ = ⟨s₀new, mems₀new₂⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨U_S, memU₂⟩ ⟨U_S, refl_U_S⟩ = ⟨U_S, memU₂⟩ := Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.symm ▸ min_le_left _ _

/-- **The grade-two controller is dominated by the grade-one controller** (antitone probe at
the separating source). -/
theorem U_S_le_U_H_of_respects : q ⟨U_S, memU₂⟩ ≤ q ⟨U_H, memU_H₂⟩ := by
  have h := hq.probe_ge_of_row_eq ⟨U_S, memU₂⟩ ⟨U_H, U_H_below_U_S⟩ ⟨U_S, refl_U_S⟩
    (rows₃_U_S_U_H.trans rows₃_U_S_self.symm) (by rw [grade_U_H, grade_U_S]; decide)
  have e1 : CellScheme.below.incl ⟨U_S, memU₂⟩ ⟨U_H, U_H_below_U_S⟩ = ⟨U_H, memU_H₂⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨U_S, memU₂⟩ ⟨U_S, refl_U_S⟩ = ⟨U_S, memU₂⟩ := Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.trans (min_le_left _ _)

/-- **The old level-two witness reads the minimum**: `q s₀old = min (q H₀old) (q U_S)` — the
controller reads the same source `ω·2+2` at the two old witnesses; the antitone suppressor gives
one inequality, the controller's own value (at most its grade-two suppressor) the other. -/
theorem s₀old_eq_min_of_respects :
    q ⟨s₀old, mems₀old₂⟩ = min (q ⟨H₀old, memH₀old₂⟩) (q ⟨U_S, memU₂⟩) := by
  obtain ⟨g, σ, hw, heq⟩ := TransformsTo.witness (hq.locality ⟨U_S, memU₂⟩)
  have h0 : min (q ⟨H₀old, memH₀old₂⟩) (q ⟨U_S, memU₂⟩) =
      min (σ (rows₃.E U_S ⟨H₀old, H₀old_below_U_S⟩)) (g (D₂.grade H₀old)) :=
    heq ⟨H₀old, H₀old_below_U_S⟩
  have hs : min (q ⟨s₀old, mems₀old₂⟩) (q ⟨U_S, memU₂⟩) =
      min (σ (rows₃.E U_S ⟨s₀old, s₀old_below_U_S⟩)) (g (D₂.grade s₀old)) :=
    heq ⟨s₀old, s₀old_below_U_S⟩
  have hU : min (q ⟨U_S, memU₂⟩) (q ⟨U_S, memU₂⟩) =
      min (σ (rows₃.E U_S ⟨U_S, refl_U_S⟩)) (g (D₂.grade U_S)) := heq ⟨U_S, refl_U_S⟩
  rw [rows₃_U_S_H₀old, grade_H₀old] at h0
  rw [rows₃_U_S_s₀old, grade_s₀old,
    min_eq_left (le_U_S_of_respects hq ⟨s₀old, mems₀old₂⟩ grade_s₀old)] at hs
  rw [min_self, rows₃_U_S_self, grade_U_S] at hU
  have hY2 : q ⟨U_S, memU₂⟩ ≤ g 2 := hU.le.trans (min_le_right _ _)
  have hg21 : g 2 ≤ g 1 := hw.anti 1 2 (by decide)
  rcases le_total (σ (ofOrd (ω2 2))) (g 2) with hle | hle
  · rw [hs, h0, min_eq_left hle, min_eq_left (hle.trans hg21)]
  · have hy : q ⟨s₀old, mems₀old₂⟩ = g 2 := by rw [hs, min_eq_right hle]
    have hYeq : q ⟨U_S, memU₂⟩ = g 2 :=
      le_antisymm hY2 (hy ▸ le_U_S_of_respects hq ⟨s₀old, mems₀old₂⟩ grade_s₀old)
    rw [hy]
    apply le_antisymm
    · rw [h0]; exact le_min hle hg21
    · exact (min_le_right _ _).trans hYeq.le

/-- **Grade-two proper cells are labelled `⊥`**: their rows are `⊥` at every cell. -/
theorem proper_two_eq_bot (d : D₂.below (Finset.univ, 2)) (hd : IsProper d.1)
    (hg : D₂.grade d.1 = 2) : q d = ⊥ := by
  obtain ⟨c, hc⟩ := hd
  have hnm : ¬ mute₂ d.1 := not_mute₂_of_low (by decide) d
  obtain ⟨g, σ, hw, heq⟩ := TransformsTo.witness (hq.locality d)
  have h := heq ⟨d.1, GradedLe.refl _⟩
  have e : CellScheme.below.incl d ⟨d.1, GradedLe.refl _⟩ = d := Subtype.ext rfl
  rw [e, min_self] at h
  have hrow : rows₃.E d.1 ⟨d.1, GradedLe.refl _⟩ = ⊥ := by
    refine (E₃_of_proper hc _).trans ((rows₂_E_eq_pull hnm _).trans ?_)
    rw [hc]
    change pull (Sum.inl c) d.1 = ⊥
    rw [pull_of_not_mute _ hnm, hc]
    change (if c.gradeP ≤ 1 then family₂.v else ⊥) = ⊥
    rw [ite_eq_right (by rw [gradeP_le_of_proper hnm hc, hg]; decide)]
  rw [hrow, hw.bot] at h
  rw [h]; exact min_eq_left bot_le

/-- **The clause-5 coupling at grade two**: the old level-two witness's source `ω·2+2` and the
controller's separating source `ω·2+3` sit one step apart, so `q s₀old = ⊥ → q U_S = ⊥`. -/
theorem U_S_eq_bot_of_s₀old (h : q ⟨s₀old, mems₀old₂⟩ = ⊥) : q ⟨U_S, memU₂⟩ = ⊥ := by
  obtain ⟨g, σ, hw, heq⟩ := TransformsTo.witness (hq.locality ⟨U_S, memU₂⟩)
  have hs : min (q ⟨s₀old, mems₀old₂⟩) (q ⟨U_S, memU₂⟩) =
      min (σ (rows₃.E U_S ⟨s₀old, s₀old_below_U_S⟩)) (g (D₂.grade s₀old)) :=
    heq ⟨s₀old, s₀old_below_U_S⟩
  have hU : min (q ⟨U_S, memU₂⟩) (q ⟨U_S, memU₂⟩) =
      min (σ (rows₃.E U_S ⟨U_S, refl_U_S⟩)) (g (D₂.grade U_S)) := heq ⟨U_S, refl_U_S⟩
  rw [h, rows₃_U_S_s₀old, grade_s₀old, min_eq_left bot_le] at hs
  rw [min_self, rows₃_U_S_self, grade_U_S] at hU
  rcases min_eq_bot.mp hs.symm with hσ | hg
  · have h5 := hw.clause5 (ofOrd (ω2 2)) 3 (by rw [hσ]; exact bot_le) 3 le_rfl
    rw [hσ, extVisibilityReplace_bot, evr_ρ_three] at h5
    rw [hU, h5]; exact min_eq_left bot_le
  · rw [hU, hg]; exact min_eq_right bot_le

end GradeTwo


end VaughtConjecture.Knight
