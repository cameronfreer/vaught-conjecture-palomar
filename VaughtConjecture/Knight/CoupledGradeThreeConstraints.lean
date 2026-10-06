/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledGradeTwoEndpoint

/-! # Grade three of the coupled semantics' bountifulness: the constraints on the cells

The grade-three cells of `D₂` are the two old caps `a₁old`, `a₂old` (both of graded index
`({0,1,2}, 3)`), the copy `b₁new` (index `({1,2,3}, 3)`), and the three fresh full cells `A₁c`,
`A₂c`, `ub₁` (all of index `(univ, 3)`) — `three_cases`, `eq_three_of_cell`.  Availability at
grade three therefore says only that a grade-three label is below *one* of the three controllers'
(`le_controller_of_respects`); graded-index equality identifies nothing.  What identifies the
labels is the actual controllers' rows, which are frozen: `a₁`'s row reads `ω+3` at every
non-proper cell, `a₂`'s reads `ω+4` except `ω+3` at the `a₁` cells, and `b₁`'s (the labelling
`qL`) reads `ω·2+3` at the separated cells, `ω+4` at the old occurrences and the `a₂` cells,
`ω+3` at the `a₁` cells.

For a labelling `q` respecting `rows₃` on `(univ, 3)`, write `z₁ = q A₁c`, `z₂ = q A₂c`,
`w = q ub₁`.  On the actual cells:
* the controllers are ordered, `z₁ ≤ z₂ ≤ w` (`A₁c_le_A₂c_of_respects`, `A₂c_le_ub₁_of_respects`),
  hence every grade-three label is at most `w` (`le_ub₁_of_respects`);
* **the duplicates collapse onto the controllers**: `q b₁new = w` (`b₁new_eq_ub₁_of_respects`),
  `q a₂old = z₂` (`a₂old_eq_A₂c_of_respects`: `b₁`'s row reads `ω+4` at both, so their probes
  against `w` agree, and `z₂ ≤ q a₂old ≤ w`), `q a₁old = z₁` (`a₁old_eq_A₁c_of_respects`: `a₂`'s
  row reads `ω+3` at both, and `q a₁old ≤ q a₂old = z₂`);
* `w ≤ q U_S` (`ub₁_le_U_S_of_respects`: the antitone suppressor at `ω·2+3`);
* **`z₂ = min (q H₀old) w`** (`A₂c_eq_min_of_respects`: `b₁`'s row reads `ω+4` at the old
  occurrence and at `a₂`'s controller, and the grade-one probe is at most the grade-three
  suppressor because `w` is);
* `z₁ = ⊥ → z₂ = ⊥` (`A₂c_eq_bot_of_A₁c`: the sources `ω+3`, `ω+4` one step apart in one block,
  clause 5 at threshold four).
So a respecting labelling of `(univ, 3)` is a respecting labelling of `(univ, 2)` plus **two
labels** `z₁ ≤ w`, with `w ≤ q U_S`, `z₂ = min (q H₀old) w`, `z₁ ≤ z₂`, self-visibility at
three, and the bottom coupling; the six grade-three cells carry `z₁, z₂, w, z₁, z₂, w`.

Not done: the grade-three retuning (`ProperToFull₃Low` at `j = 3`).  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## The cells of grade three -/

section Cells

theorem cell_a₁old : D₂.cell a₁old = (({0, 1, 2} : Finset (Fin 4)), 3) := by
  unfold a₁old; rw [cell_castAdd_X]
  exact Prod.ext (by decide) rfl
theorem grade_a₁old : D₂.grade a₁old = 3 := by change (D₂.cell a₁old).2 = 3; rw [cell_a₁old]
theorem grade_A₁c : D₂.grade A₁c = 3 := by change (D₂.cell A₁c).2 = 3; rw [cell_A₁c]
theorem grade_A₂c : D₂.grade A₂c = 3 := by change (D₂.cell A₂c).2 = 3; rw [cell_A₂c]
theorem not_mute_a₁old : ¬ mute₂ a₁old := not_mute₂_castAdd _
theorem not_mute_b₁new : ¬ mute₂ b₁new := not_mute_copyB _

/-- **The cells of grade three**: the two old caps, the copy of `b₁`, and the three fresh full
cells. -/
theorem three_cases {d : Cell D₂} (hd : ¬ mute₂ d) (hg : D₂.grade d = 3) :
    d = a₁old ∨ d = a₂old ∨ d = b₁new ∨ d = A₁c ∨ d = A₂c ∨ d = ub₁ := by
  rcases cell_cases d hd with ⟨i, rfl⟩ | hB | rfl | rfl | rfl | rfl | rfl
  · -- the A face
    rw [D₂_grade_castAdd, Family.grade_eq] at hg
    rcases hx : family₀.e.symm i with c | H | s | a
    · exfalso; rw [hx] at hg; change c.gradeP = 3 at hg; have := c.gradeP_le_two; omega
    · exfalso; rw [hx] at hg; change (1 : ℕ) = 3 at hg; omega
    · exfalso; rw [hx] at hg; change (2 : ℕ) = 3 at hg; omega
    · have h : a.1 ∈ ({a₁, a₂} : Finset (CappedCore3 Prop3.gradeP T₀)) := a.2
      rcases Finset.mem_insert.mp h with h | h
      · left
        have h1 : family₀.e.symm i = a₁X₀ := by
          rw [hx]
          exact congrArg (fun z : ↥family₀.S₃ => (.inr (.inr (.inr z)) : family₀.X))
            (Subtype.ext h)
        unfold a₁old; rw [← h1, Equiv.apply_symm_apply]
      · right; left
        have h1 : family₀.e.symm i = a₂X₀ := by
          rw [hx]
          exact congrArg (fun z : ↥family₀.S₃ => (.inr (.inr (.inr z)) : family₀.X))
            (Subtype.ext (Finset.mem_singleton.mp h))
        unfold a₂old; rw [← h1, Equiv.apply_symm_apply]
  · -- the B face
    right; right
    have h2 : C₁.grade (retB d) = D₂.grade d :=
      congrArg Prod.snd (cell_retB zero_not_mem_B ⟨d, hB⟩)
    rw [Family.grade_eq, hg] at h2
    rcases img_cases (family₁.e.symm (retB d)) with ⟨c, hc⟩ | h1 | h1 | h1
    · exfalso; rw [hc] at h2; change c.gradeP = 3 at h2; have := c.gradeP_le_two; omega
    · exfalso; rw [h1] at h2; change (1 : ℕ) = 3 at h2; omega
    · exfalso; rw [h1] at h2; change (2 : ℕ) = 3 at h2; omega
    · left
      rw [eq_copyB_of_B hB]; unfold b₁new; rw [← h1, Equiv.apply_symm_apply]
  · exfalso; rw [grade_U_H] at hg; omega
  · exfalso; rw [grade_U_S] at hg; omega
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- **The three controllers**: the cells of graded index `(univ, 3)`. -/
theorem eq_three_of_cell {d : Cell D₂} (h : D₂.cell d = (Finset.univ, 3)) :
    d = A₁c ∨ d = A₂c ∨ d = ub₁ := by
  have hnm : ¬ mute₂ d := fun hm => by
    change D₂.cell d = _ at hm; rw [h] at hm
    have := congrArg Prod.snd hm; change (3 : ℕ) = 4 at this; omega
  have hg : D₂.grade d = 3 := by change (D₂.cell d).2 = 3; rw [h]
  have h3 : (3 : Fin 4) ∈ D₂.scope d := by change (3 : Fin 4) ∈ (D₂.cell d).1; rw [h]; simp
  have h0 : (0 : Fin 4) ∈ D₂.scope d := by change (0 : Fin 4) ∈ (D₂.cell d).1; rw [h]; simp
  rcases three_cases hnm hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd h3 (three_not_mem_scope_castAdd _)
  · exact absurd h3 (three_not_mem_scope_castAdd _)
  · exact absurd h0 (zero_not_mem_scope_copyB _)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-! ### Memberships -/

theorem memA₁c₃ : GradedLe (D₂.cell A₁c) (Finset.univ, 3) := by
  rw [cell_A₁c]; exact GradedLe.refl _
theorem memA₂c₃ : GradedLe (D₂.cell A₂c) (Finset.univ, 3) := by
  rw [cell_A₂c]; exact GradedLe.refl _
theorem memub₁₃ : GradedLe (D₂.cell ub₁) (Finset.univ, 3) := by
  rw [cell_ub₁]; exact GradedLe.refl _
theorem mema₁old₃ : GradedLe (D₂.cell a₁old) (Finset.univ, 3) := memA' _
theorem mema₂old₃ : GradedLe (D₂.cell a₂old) (Finset.univ, 3) := memA' _
theorem memb₁new₃ : GradedLe (D₂.cell b₁new) (Finset.univ, 3) := memB' _
theorem memH₀old₃ : GradedLe (D₂.cell H₀old) (Finset.univ, 3) := memA (by decide)
theorem memU_S₃ : GradedLe (D₂.cell U_S) (Finset.univ, 3) := by
  rw [cell_U_S]; exact ⟨Finset.subset_univ _, by decide⟩

theorem H₀old_below_A₁c : GradedLe (D₂.cell H₀old) (D₂.cell A₁c) := by
  rw [cell_A₁c]; exact memH₀old₃
theorem a₁old_below_A₁c : GradedLe (D₂.cell a₁old) (D₂.cell A₁c) := by
  rw [cell_A₁c]; exact mema₁old₃
theorem A₂c_below_A₁c : GradedLe (D₂.cell A₂c) (D₂.cell A₁c) := by
  rw [cell_A₁c]; exact memA₂c₃
theorem refl_A₁c : GradedLe (D₂.cell A₁c) (D₂.cell A₁c) := GradedLe.refl _
theorem a₁old_below_A₂c : GradedLe (D₂.cell a₁old) (D₂.cell A₂c) := by
  rw [cell_A₂c]; exact mema₁old₃
theorem a₂old_below_A₂c : GradedLe (D₂.cell a₂old) (D₂.cell A₂c) := by
  rw [cell_A₂c]; exact mema₂old₃
theorem A₁c_below_A₂c : GradedLe (D₂.cell A₁c) (D₂.cell A₂c) := by
  rw [cell_A₂c]; exact memA₁c₃
theorem ub₁_below_A₂c : GradedLe (D₂.cell ub₁) (D₂.cell A₂c) := by
  rw [cell_A₂c]; exact memub₁₃
theorem refl_A₂c : GradedLe (D₂.cell A₂c) (D₂.cell A₂c) := GradedLe.refl _
theorem H₀old_below_ub₁ : GradedLe (D₂.cell H₀old) (D₂.cell ub₁) := by
  rw [cell_ub₁]; exact memH₀old₃
theorem U_S_below_ub₁ : GradedLe (D₂.cell U_S) (D₂.cell ub₁) := by
  rw [cell_ub₁]; exact memU_S₃
theorem b₁new_below_ub₁ : GradedLe (D₂.cell b₁new) (D₂.cell ub₁) := by
  rw [cell_ub₁]; exact memb₁new₃
theorem A₂c_below_ub₁ : GradedLe (D₂.cell A₂c) (D₂.cell ub₁) := by
  rw [cell_ub₁]; exact memA₂c₃
theorem refl_ub₁ : GradedLe (D₂.cell ub₁) (D₂.cell ub₁) := GradedLe.refl _
theorem a₂old_below_a₁old : GradedLe (D₂.cell a₂old) (D₂.cell a₁old) := by
  rw [cell_a₂old, cell_a₁old]; exact GradedLe.refl _
theorem refl_a₁old : GradedLe (D₂.cell a₁old) (D₂.cell a₁old) := GradedLe.refl _

/-! ### The rows at the grade-three cells -/

theorem pull_eq_rowX (x : family₂.X) {d : Cell D₂} (hd : ¬ mute₂ d) {y : family₂.X}
    (h : ret₂ d = family₂.e y) : pull x d = family₂.rowX x y := by
  rw [pull_of_not_mute _ hd, h, Equiv.symm_apply_apply]

theorem rows₃_A₁c_H₀old : rows₃.E A₁c ⟨H₀old, H₀old_below_A₁c⟩ = η₁ :=
  (E₃_A₁c _).trans ((pull_eq_rowX _ not_mute_H₀old ret₂_H₀old).trans rowX_a₁_H)
theorem rows₃_A₁c_a₁old : rows₃.E A₁c ⟨a₁old, a₁old_below_A₁c⟩ = η₁ :=
  (E₃_A₁c _).trans ((pull_eq_rowX _ not_mute_a₁old ret₂_a₁old).trans rowX_a₁_a₁)
theorem rows₃_A₁c_A₂c : rows₃.E A₁c ⟨A₂c, A₂c_below_A₁c⟩ = η₁ :=
  (E₃_A₁c _).trans ((pull_eq_rowX _ not_mute_A₂c ret₂_A₂c).trans rowX_a₁_a₂)
theorem rows₃_A₁c_self : rows₃.E A₁c ⟨A₁c, refl_A₁c⟩ = η₁ :=
  (E₃_A₁c _).trans ((pull_eq_rowX _ not_mute_A₁c ret₂_A₁c).trans rowX_a₁_a₁)

theorem rows₃_A₂c_a₁old : rows₃.E A₂c ⟨a₁old, a₁old_below_A₂c⟩ = η₁ :=
  (E₃_A₂c _).trans ((pull_eq_rowX _ not_mute_a₁old ret₂_a₁old).trans rowX_a₂_a₁)
theorem rows₃_A₂c_A₁c : rows₃.E A₂c ⟨A₁c, A₁c_below_A₂c⟩ = η₁ :=
  (E₃_A₂c _).trans ((pull_eq_rowX _ not_mute_A₁c ret₂_A₁c).trans rowX_a₂_a₁)
theorem rows₃_A₂c_a₂old : rows₃.E A₂c ⟨a₂old, a₂old_below_A₂c⟩ = γ₀ :=
  (E₃_A₂c _).trans ((pull_eq_rowX _ not_mute_a₂old ret₂_a₂old).trans rowX_a₂_a₂)
theorem rows₃_A₂c_ub₁ : rows₃.E A₂c ⟨ub₁, ub₁_below_A₂c⟩ = γ₀ :=
  (E₃_A₂c _).trans ((pull_eq_rowX _ not_mute_ub₁ ret₂_ub₁).trans rowX_a₂_b₁)
theorem rows₃_A₂c_self : rows₃.E A₂c ⟨A₂c, refl_A₂c⟩ = γ₀ :=
  (E₃_A₂c _).trans ((pull_eq_rowX _ not_mute_A₂c ret₂_A₂c).trans rowX_a₂_a₂)

theorem qL_a₂old : qL a₂old = γ₀ :=
  (qL_castAdd _).trans ((pull_eq_rowX _ not_mute_a₂old ret₂_a₂old).trans rowX_a₂_a₂)
theorem qL_b₁new : qL b₁new = γ₁ :=
  (qL_of_B (copyB_mem _)).trans ((labelQ_eq_pull _).trans
    ((pull_eq_rowX _ not_mute_b₁new ret₂_b₁new).trans rowX_b₁_b₁))

theorem rows₃_ub₁_H₀old : rows₃.E ub₁ ⟨H₀old, H₀old_below_ub₁⟩ = γ₀ :=
  (rows₃_E _ _).trans ((E₃_ub₁ _).trans qL_H₀old)
theorem rows₃_ub₁_U_S : rows₃.E ub₁ ⟨U_S, U_S_below_ub₁⟩ = γ₁ :=
  (rows₃_E _ _).trans ((E₃_ub₁ _).trans qL_U_S)
theorem rows₃_ub₁_a₂old : rows₃.E ub₁ ⟨a₂old, a₂old_below_ub₁⟩ = γ₀ :=
  (rows₃_E _ _).trans ((E₃_ub₁ _).trans qL_a₂old)
theorem rows₃_ub₁_b₁new : rows₃.E ub₁ ⟨b₁new, b₁new_below_ub₁⟩ = γ₁ :=
  (rows₃_E _ _).trans ((E₃_ub₁ _).trans qL_b₁new)
theorem rows₃_ub₁_A₂c : rows₃.E ub₁ ⟨A₂c, A₂c_below_ub₁⟩ = γ₀ :=
  (rows₃_E _ _).trans ((E₃_ub₁ _).trans qL_A₂c)
theorem rows₃_ub₁_self : rows₃.E ub₁ ⟨ub₁, refl_ub₁⟩ = γ₁ :=
  (rows₃_E _ _).trans ((E₃_ub₁ _).trans qL_ub₁)

theorem rows₃_a₁old_eq (d : D₂.below (D₂.cell a₁old)) : rows₃.E a₁old d = pull a₁X d.1 := by
  have hA : AFace a₁old := aFace_castAdd _
  rw [E₃_of_A hA, rows₂_E_eq_pull not_mute_a₁old, ret₂_a₁old, Equiv.symm_apply_apply]
theorem rows₃_a₁old_a₂old : rows₃.E a₁old ⟨a₂old, a₂old_below_a₁old⟩ = η₁ :=
  (rows₃_a₁old_eq _).trans ((pull_eq_rowX _ not_mute_a₂old ret₂_a₂old).trans rowX_a₁_a₂)
theorem rows₃_a₁old_self : rows₃.E a₁old ⟨a₁old, refl_a₁old⟩ = η₁ :=
  (rows₃_a₁old_eq _).trans ((pull_eq_rowX _ not_mute_a₁old ret₂_a₁old).trans rowX_a₁_a₁)

/-- The clause-5 step from `ω+3` to `ω+4` at threshold four. -/
theorem evr_η₁_four : extVisibilityReplace η₁ 4 4 = γ₀ := by
  rw [η₁_num, γ₀_num', extVisibilityReplace_ofOrd]
  unfold visibilityReplace
  rw [ite_eq_left (by rw [fp_ω1j]; omega)]
  unfold ordinalReplace
  rw [limitPart_mul_add]

end Cells

/-! ## The constraints on a respecting labelling of `(univ, 3)` -/

section Constraints

variable {q : D₂.below (Finset.univ, 3) → ExtOrd}
  (hq : RespectsSemanticsBelow rows₃ (Finset.univ, 3) q)
include hq

/-- **Availability at grade three**: every grade-three label is at most one of the three
controllers' labels — availability alone does not say which. -/
theorem le_controller_of_respects (d : D₂.below (Finset.univ, 3)) (hd : D₂.grade d.1 = 3) :
    q d ≤ q ⟨A₁c, memA₁c₃⟩ ∨ q d ≤ q ⟨A₂c, memA₂c₃⟩ ∨ q d ≤ q ⟨ub₁, memub₁₃⟩ := by
  obtain ⟨Xi, hXi, hle⟩ := hq.availability d ⟨ub₁, memub₁₃⟩ (by
      change D₂.scope d.1 ⊆ (D₂.cell ub₁).1; rw [cell_ub₁]; exact Finset.subset_univ _)
    (by change D₂.grade d.1 = (D₂.cell ub₁).2; rw [cell_ub₁, hd])
  rw [cell_ub₁] at hXi
  rcases eq_three_of_cell hXi with h | h | h
  · left; rw [show Xi = ⟨A₁c, memA₁c₃⟩ from Subtype.ext h] at hle; exact hle
  · right; left; rw [show Xi = ⟨A₂c, memA₂c₃⟩ from Subtype.ext h] at hle; exact hle
  · right; right; rw [show Xi = ⟨ub₁, memub₁₃⟩ from Subtype.ext h] at hle; exact hle

/-- **`a₁`'s controller is below `a₂`'s**: `a₁`'s row reads `ω+3` at both. -/
theorem A₁c_le_A₂c_of_respects : q ⟨A₁c, memA₁c₃⟩ ≤ q ⟨A₂c, memA₂c₃⟩ := by
  have h := hq.probe_eq_of_row_eq ⟨A₁c, memA₁c₃⟩ ⟨A₂c, A₂c_below_A₁c⟩ ⟨A₁c, refl_A₁c⟩
    (rows₃_A₁c_A₂c.trans rows₃_A₁c_self.symm) (by rw [grade_A₂c, grade_A₁c])
  have e1 : CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₂c, A₂c_below_A₁c⟩ = ⟨A₂c, memA₂c₃⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₁c, refl_A₁c⟩ = ⟨A₁c, memA₁c₃⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.symm.le.trans (min_le_left _ _)

/-- **`a₁`'s controller is below the old cap `a₁`.** -/
theorem A₁c_le_a₁old_of_respects : q ⟨A₁c, memA₁c₃⟩ ≤ q ⟨a₁old, mema₁old₃⟩ := by
  have h := hq.probe_eq_of_row_eq ⟨A₁c, memA₁c₃⟩ ⟨a₁old, a₁old_below_A₁c⟩ ⟨A₁c, refl_A₁c⟩
    (rows₃_A₁c_a₁old.trans rows₃_A₁c_self.symm) (by rw [grade_a₁old, grade_A₁c])
  have e1 : CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨a₁old, a₁old_below_A₁c⟩ =
      ⟨a₁old, mema₁old₃⟩ := Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₁c, refl_A₁c⟩ = ⟨A₁c, memA₁c₃⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.symm.le.trans (min_le_left _ _)

/-- **`a₂`'s controller is below `b₁`'s**: `a₂`'s row reads `ω+4` at both. -/
theorem A₂c_le_ub₁_of_respects : q ⟨A₂c, memA₂c₃⟩ ≤ q ⟨ub₁, memub₁₃⟩ := by
  have h := hq.probe_eq_of_row_eq ⟨A₂c, memA₂c₃⟩ ⟨ub₁, ub₁_below_A₂c⟩ ⟨A₂c, refl_A₂c⟩
    (rows₃_A₂c_ub₁.trans rows₃_A₂c_self.symm) (by rw [grade_ub₁, grade_A₂c])
  have e1 : CellScheme.below.incl ⟨A₂c, memA₂c₃⟩ ⟨ub₁, ub₁_below_A₂c⟩ = ⟨ub₁, memub₁₃⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨A₂c, memA₂c₃⟩ ⟨A₂c, refl_A₂c⟩ = ⟨A₂c, memA₂c₃⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.symm.le.trans (min_le_left _ _)

/-- **`a₂`'s controller is below the old cap `a₂`.** -/
theorem A₂c_le_a₂old_of_respects : q ⟨A₂c, memA₂c₃⟩ ≤ q ⟨a₂old, mema₂old₃⟩ := by
  have h := hq.probe_eq_of_row_eq ⟨A₂c, memA₂c₃⟩ ⟨a₂old, a₂old_below_A₂c⟩ ⟨A₂c, refl_A₂c⟩
    (rows₃_A₂c_a₂old.trans rows₃_A₂c_self.symm) (by rw [grade_a₂old, grade_A₂c])
  have e1 : CellScheme.below.incl ⟨A₂c, memA₂c₃⟩ ⟨a₂old, a₂old_below_A₂c⟩ =
      ⟨a₂old, mema₂old₃⟩ := Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨A₂c, memA₂c₃⟩ ⟨A₂c, refl_A₂c⟩ = ⟨A₂c, memA₂c₃⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.symm.le.trans (min_le_left _ _)

/-- **Every grade-three label is at most `b₁`'s controller's** (availability, with the
controllers ordered). -/
theorem le_ub₁_of_respects (d : D₂.below (Finset.univ, 3)) (hd : D₂.grade d.1 = 3) :
    q d ≤ q ⟨ub₁, memub₁₃⟩ := by
  rcases le_controller_of_respects hq d hd with h | h | h
  · exact h.trans ((A₁c_le_A₂c_of_respects hq).trans (A₂c_le_ub₁_of_respects hq))
  · exact h.trans (A₂c_le_ub₁_of_respects hq)
  · exact h

/-- **`b₁`'s controller is below the copy of `b₁`**: `b₁`'s row reads `ω·2+3` at both. -/
theorem ub₁_le_b₁new_of_respects : q ⟨ub₁, memub₁₃⟩ ≤ q ⟨b₁new, memb₁new₃⟩ := by
  have h := hq.probe_eq_of_row_eq ⟨ub₁, memub₁₃⟩ ⟨b₁new, b₁new_below_ub₁⟩ ⟨ub₁, refl_ub₁⟩
    (rows₃_ub₁_b₁new.trans rows₃_ub₁_self.symm) (by rw [grade_b₁new, grade_ub₁])
  have e1 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨b₁new, b₁new_below_ub₁⟩ =
      ⟨b₁new, memb₁new₃⟩ := Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨ub₁, refl_ub₁⟩ = ⟨ub₁, memub₁₃⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.symm.le.trans (min_le_left _ _)

/-- **The copy of `b₁` is labelled like its controller.** -/
theorem b₁new_eq_ub₁_of_respects : q ⟨b₁new, memb₁new₃⟩ = q ⟨ub₁, memub₁₃⟩ :=
  le_antisymm (le_ub₁_of_respects hq _ grade_b₁new) (ub₁_le_b₁new_of_respects hq)

/-- **The old cap `a₂` is labelled like its controller**: `b₁`'s row reads `ω+4` at both, so
their probes against `b₁`'s controller agree; the controller is below the cap and the cap below
`b₁`'s controller. -/
theorem a₂old_eq_A₂c_of_respects : q ⟨a₂old, mema₂old₃⟩ = q ⟨A₂c, memA₂c₃⟩ := by
  have h := hq.probe_eq_of_row_eq ⟨ub₁, memub₁₃⟩ ⟨a₂old, a₂old_below_ub₁⟩ ⟨A₂c, A₂c_below_ub₁⟩
    (rows₃_ub₁_a₂old.trans rows₃_ub₁_A₂c.symm) (by rw [grade_a₂old, grade_A₂c])
  have e1 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨a₂old, a₂old_below_ub₁⟩ =
      ⟨a₂old, mema₂old₃⟩ := Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨A₂c, A₂c_below_ub₁⟩ = ⟨A₂c, memA₂c₃⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_eq_left (le_ub₁_of_respects hq ⟨a₂old, mema₂old₃⟩ grade_a₂old),
    min_eq_left (A₂c_le_ub₁_of_respects hq)] at h
  exact h

/-- **The old cap `a₁` is below the old cap `a₂`**: `a₁`'s row reads `ω+3` at both. -/
theorem a₁old_le_a₂old_of_respects : q ⟨a₁old, mema₁old₃⟩ ≤ q ⟨a₂old, mema₂old₃⟩ := by
  have h := hq.probe_eq_of_row_eq ⟨a₁old, mema₁old₃⟩ ⟨a₂old, a₂old_below_a₁old⟩
    ⟨a₁old, refl_a₁old⟩ (rows₃_a₁old_a₂old.trans rows₃_a₁old_self.symm)
    (by rw [grade_a₂old, grade_a₁old])
  have e1 : CellScheme.below.incl ⟨a₁old, mema₁old₃⟩ ⟨a₂old, a₂old_below_a₁old⟩ =
      ⟨a₂old, mema₂old₃⟩ := Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨a₁old, mema₁old₃⟩ ⟨a₁old, refl_a₁old⟩ =
      ⟨a₁old, mema₁old₃⟩ := Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.symm.le.trans (min_le_left _ _)

/-- **The old cap `a₁` is labelled like its controller**: `a₂`'s row reads `ω+3` at both, so
their probes against `a₂`'s controller agree; the old cap `a₁` is below the old cap `a₂`, which
is `a₂`'s controller's label. -/
theorem a₁old_eq_A₁c_of_respects : q ⟨a₁old, mema₁old₃⟩ = q ⟨A₁c, memA₁c₃⟩ := by
  have h := hq.probe_eq_of_row_eq ⟨A₂c, memA₂c₃⟩ ⟨a₁old, a₁old_below_A₂c⟩ ⟨A₁c, A₁c_below_A₂c⟩
    (rows₃_A₂c_a₁old.trans rows₃_A₂c_A₁c.symm) (by rw [grade_a₁old, grade_A₁c])
  have e1 : CellScheme.below.incl ⟨A₂c, memA₂c₃⟩ ⟨a₁old, a₁old_below_A₂c⟩ =
      ⟨a₁old, mema₁old₃⟩ := Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨A₂c, memA₂c₃⟩ ⟨A₁c, A₁c_below_A₂c⟩ = ⟨A₁c, memA₁c₃⟩ :=
    Subtype.ext rfl
  have hle : q ⟨a₁old, mema₁old₃⟩ ≤ q ⟨A₂c, memA₂c₃⟩ :=
    (a₁old_le_a₂old_of_respects hq).trans (a₂old_eq_A₂c_of_respects hq).le
  rw [e1, e2, min_eq_left hle, min_eq_left (A₁c_le_A₂c_of_respects hq)] at h
  exact h

/-- **`b₁`'s controller is below the grade-two controller** (antitone suppressor at the
separating source `ω·2+3`, read at grades two and three). -/
theorem ub₁_le_U_S_of_respects : q ⟨ub₁, memub₁₃⟩ ≤ q ⟨U_S, memU_S₃⟩ := by
  have h := hq.probe_ge_of_row_eq ⟨ub₁, memub₁₃⟩ ⟨U_S, U_S_below_ub₁⟩ ⟨ub₁, refl_ub₁⟩
    (rows₃_ub₁_U_S.trans rows₃_ub₁_self.symm) (by rw [grade_U_S, grade_ub₁]; decide)
  have e1 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨U_S, U_S_below_ub₁⟩ = ⟨U_S, memU_S₃⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨ub₁, refl_ub₁⟩ = ⟨ub₁, memub₁₃⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.trans (min_le_left _ _)

/-- **`a₂`'s controller reads the minimum**: `q A₂c = min (q H₀old) (q ub₁)` — `b₁`'s row reads
the same source `ω+4` at the old occurrence and at `a₂`'s controller; the grade-one probe is at
most the grade-three suppressor because `b₁`'s controller's own value is. -/
theorem A₂c_eq_min_of_respects :
    q ⟨A₂c, memA₂c₃⟩ = min (q ⟨H₀old, memH₀old₃⟩) (q ⟨ub₁, memub₁₃⟩) := by
  obtain ⟨g, σ, hw, heq⟩ := TransformsTo.witness (hq.locality ⟨ub₁, memub₁₃⟩)
  have h0 : min (q ⟨H₀old, memH₀old₃⟩) (q ⟨ub₁, memub₁₃⟩) =
      min (σ (rows₃.E ub₁ ⟨H₀old, H₀old_below_ub₁⟩)) (g (D₂.grade H₀old)) :=
    heq ⟨H₀old, H₀old_below_ub₁⟩
  have hA : min (q ⟨A₂c, memA₂c₃⟩) (q ⟨ub₁, memub₁₃⟩) =
      min (σ (rows₃.E ub₁ ⟨A₂c, A₂c_below_ub₁⟩)) (g (D₂.grade A₂c)) :=
    heq ⟨A₂c, A₂c_below_ub₁⟩
  have hU : min (q ⟨ub₁, memub₁₃⟩) (q ⟨ub₁, memub₁₃⟩) =
      min (σ (rows₃.E ub₁ ⟨ub₁, refl_ub₁⟩)) (g (D₂.grade ub₁)) := heq ⟨ub₁, refl_ub₁⟩
  rw [rows₃_ub₁_H₀old, grade_H₀old] at h0
  rw [rows₃_ub₁_A₂c, grade_A₂c, min_eq_left (A₂c_le_ub₁_of_respects hq)] at hA
  rw [min_self, rows₃_ub₁_self, grade_ub₁] at hU
  have hw3 : q ⟨ub₁, memub₁₃⟩ ≤ g 3 := hU.le.trans (min_le_right _ _)
  have hg31 : g 3 ≤ g 1 := hw.anti 1 3 (by decide)
  have h1 : min (q ⟨H₀old, memH₀old₃⟩) (q ⟨ub₁, memub₁₃⟩) ≤ g 3 :=
    (min_le_right _ _).trans hw3
  calc q ⟨A₂c, memA₂c₃⟩ = min (σ γ₀) (g 3) := hA
    _ = min (min (σ γ₀) (g 1)) (g 3) := by rw [min_assoc, min_eq_right hg31]
    _ = min (min (q ⟨H₀old, memH₀old₃⟩) (q ⟨ub₁, memub₁₃⟩)) (g 3) := by rw [h0]
    _ = min (q ⟨H₀old, memH₀old₃⟩) (q ⟨ub₁, memub₁₃⟩) := min_eq_left h1

/-- **The clause-5 coupling at grade three**: the sources `ω+3` (at `a₁`) and `ω+4` (at `a₂`)
sit one step apart in one block, so `q A₁c = ⊥ → q A₂c = ⊥` (clause 5 at threshold four in
`a₂`'s controller's witness). -/
theorem A₂c_eq_bot_of_A₁c (h : q ⟨A₁c, memA₁c₃⟩ = ⊥) : q ⟨A₂c, memA₂c₃⟩ = ⊥ := by
  obtain ⟨g, σ, hw, heq⟩ := TransformsTo.witness (hq.locality ⟨A₂c, memA₂c₃⟩)
  have h1 : min (q ⟨A₁c, memA₁c₃⟩) (q ⟨A₂c, memA₂c₃⟩) =
      min (σ (rows₃.E A₂c ⟨A₁c, A₁c_below_A₂c⟩)) (g (D₂.grade A₁c)) :=
    heq ⟨A₁c, A₁c_below_A₂c⟩
  have hA : min (q ⟨A₂c, memA₂c₃⟩) (q ⟨A₂c, memA₂c₃⟩) =
      min (σ (rows₃.E A₂c ⟨A₂c, refl_A₂c⟩)) (g (D₂.grade A₂c)) := heq ⟨A₂c, refl_A₂c⟩
  rw [h, rows₃_A₂c_A₁c, grade_A₁c, min_eq_left bot_le] at h1
  rw [min_self, rows₃_A₂c_self, grade_A₂c] at hA
  rcases min_eq_bot.mp h1.symm with hσ | hg
  · have h5 := hw.clause5 η₁ 4 (by rw [hσ]; exact bot_le) 4 le_rfl
    rw [hσ, extVisibilityReplace_bot, evr_η₁_four] at h5
    rw [hA, h5]; exact min_eq_left bot_le
  · rw [hA, hg]; exact min_eq_right bot_le

/-- The grade-three labels are self-visible at three. -/
theorem selfVis_ub₁_of_respects : SelfVis 3 (q ⟨ub₁, memub₁₃⟩) := by
  have := selfVis_of_respects hq ⟨ub₁, memub₁₃⟩
  change SelfVis (D₂.grade ub₁) _ at this
  rwa [grade_ub₁] at this
theorem selfVis_A₁c_of_respects : SelfVis 3 (q ⟨A₁c, memA₁c₃⟩) := by
  have := selfVis_of_respects hq ⟨A₁c, memA₁c₃⟩
  change SelfVis (D₂.grade A₁c) _ at this
  rwa [grade_A₁c] at this

end Constraints

end VaughtConjecture.Knight
