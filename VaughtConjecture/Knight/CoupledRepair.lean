/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledNotBountiful

/-! # The single-row repair of the coupled semantics

The frozen `rows₃` is not bountiful (`CoupledNotBountiful`): a bottom proper label forces `b₁`'s
controller to `⊥` through the chain `z₁ ≤ R₃ v`, `z₁ = ⊥ → z₂ = ⊥`, `z₂ = min x₀ w`, where the last
link comes from `b₁`'s controller reading **one** source `ω+4` at the old occurrence and at `a₂`'s
controller.  **The repair** (after the reviewer's research handoff `SOURCE-REPAIR-HANDOFF.md`,
draft #319) changes that one row and nothing else: `qM` reads `ω·2+3` at the two old witnesses
`H₀old`, `s₀old` and `ω·2+4` at the six separated cells (the copies of `H₀`, `s₀`, `b₁` and the
three controllers), and `qL` elsewhere — eight changed entries, no new ordinal block, both new
finite parts fixed by every replacement at thresholds at most three.  `rowsR` is `rows₃` with that
row (`E_R`).  The old witnesses no longer share a source with `a₂`'s controller.

**Acceptance 1 — faces literal, other rows unchanged**: `rowsR_E_of_A`, `rowsR_E_of_B`,
`rowsR_E_of_ne`, `rowsR_E_of_proper_scope`.

**Acceptance 2 — coding and consistency, both directions at the changed cell**: `rowsR_coded`
(finite parts `3`, `4` at grade three); `rowsR_consistent`.  Rows whose cell does not lie above
`b₁`'s controller are consistent as before (`consistentR_of_not_above`, by agreement of the
semantics below them).  Above it lie exactly `a₁`'s and `a₂`'s controllers (the same graded
index) and the mute cell (`ub₁_below_cases`); the **reverse incidences** — those two rows
respecting the repaired row — are the clamp at `ω·2+4` with constant `ω+3`, resp. `ω+4`
(`A₁c_locality_ub₁R`, `A₂c_locality_ub₁R`, through `min_qM_η₁`/`min_qM_γ₀`: the repaired row reads
`a₁`'s, resp. `a₂`'s, row below those caps).  The **forward incidences** — the repaired row as a
labelling of `(univ, 3)` respecting every row (`qM_respects`) — use one new witness shape,
`Witness.idConst` (the identity below a limit cutoff, a self-visible constant above; its bottom
fibre is `{⊥}`, so clause 5 above the grade reduces to the bottom-input case, where both sides
are bottom), raised by `Witness.raise` at `ω·2+2`
(grade-one controller) and `ω·2+3` (grade-two controller).

**Acceptance 3 — both displays**: the prescribed labelling `qL` respects `rowsR`
(`qL_respectsR`; at the changed row by the clamp at `ω·2+4` with constants `ω+4`, `ω·2+3`,
`qL_locality_ub₁R`), and `qL_realizes` is unchanged; the bottom face of the no-go extends
(`bottomFace_extendsR`): `bottomFull` is `3` where the repaired row is in the block at `ω·2` and
`⊥` elsewhere — its grade-two part by the sufficiency lemma `respects_of_shape₂` with parameters
`(⊥, 3, 3, 3)`, its grade-three localities by the all-bottom transformation at the `a₁`/`a₂` cells,
the face's own locality at the copy of `b₁`, and the limit step at `ω·2` at the changed row.

**Transfers**: below grade three the repaired semantics is the frozen one
(`respectsR_iff_low`), so the grade-one and grade-two endpoints transfer
(`properToFullR_of_le_two`), and bountifulness reduces to the scope-changing obligation
`ProperToFullRLow` (`rowsR_isBountiful_of`).

**Acceptance 4 — the grade-three constraints, re-extracted** (for `q` respecting `rowsR` on
`(univ, 3)`).  Surviving, with the same proofs (rows other than the changed one, or its unchanged
entries): `z₁ ≤ z₂ ≤ w`, every grade-three label `≤ w`, the collapses `q b₁new = w`,
`q a₂old = z₂`, `q a₁old = z₁`, `w ≤ q U_S`, the bottom coupling `z₁ = ⊥ → z₂ = ⊥`, the
moving-orbit bound `z₁ ≤ R₃ v` and its sharp form.  **Dead**: `z₂ = min x₀ w`
(`not_A₂c_eq_minR`: the bottom display has `z₂ = ⊥` under `min x₀ w = 3`).  **Newly induced**:
`z₂ ≤ x₀` (`A₂c_le_H₀old_of_respectsR`, `a₂`'s row), hence `z₂ ≤ min x₀ w`
(`A₂c_le_min_of_respectsR`); and the explicit bottom fibre of the changed row at threshold four,
`min x₀ w = ⊥ → w = ⊥` (`ub₁_eq_bot_of_min_botR`: `ω·2+3 ↦ ω·2+4`).

A tested repair candidate with its acceptance tests compiled; **not** a proof of bountifulness.
Not done: the grade-three face obligations of `ProperToFullRLow`.  The no-go for the frozen
`rows₃` stands unchanged.  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## The repaired row -/

section Row

/-- **The repaired row of `b₁`'s controller**: `ω·2+3` at the old witnesses, `ω·2+4` at the six
separated cells (the copies of `H₀`, `s₀`, `b₁` and the three controllers), `qL` elsewhere. -/
noncomputable def qM (d : Cell D₂) : ExtOrd :=
  if d = H₀old ∨ d = s₀old then ofOrd (ω2 3)
  else if ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X ∨ ret₂ d = family₂.e b₁X then
    ofOrd (ω2 4)
  else qL d

theorem qM_of_old {d : Cell D₂} (h : d = H₀old ∨ d = s₀old) : qM d = ofOrd (ω2 3) := by
  unfold qM; rw [ite_eq_left h]
theorem qM_of_sep {d : Cell D₂} (h1 : ¬ (d = H₀old ∨ d = s₀old))
    (h2 : ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X ∨ ret₂ d = family₂.e b₁X) :
    qM d = ofOrd (ω2 4) := by
  unfold qM; rw [ite_eq_right h1, ite_eq_left h2]
theorem qM_of_other {d : Cell D₂} (h1 : ¬ (d = H₀old ∨ d = s₀old))
    (h2 : ¬ (ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X ∨ ret₂ d = family₂.e b₁X)) :
    qM d = qL d := by
  unfold qM; rw [ite_eq_right h1, ite_eq_right h2]

theorem qM_H₀old : qM H₀old = ofOrd (ω2 3) := qM_of_old (Or.inl rfl)
theorem qM_s₀old : qM s₀old = ofOrd (ω2 3) := qM_of_old (Or.inr rfl)
theorem qM_H₀new : qM H₀new = ofOrd (ω2 4) :=
  qM_of_sep (by rintro (h | h); exacts [H₀old_ne_H₀new h.symm, s₀old_ne_H₀new h.symm])
    (Or.inl ret₂_H₀new)
theorem qM_U_H : qM U_H = ofOrd (ω2 4) :=
  qM_of_sep (by rintro (h | h); exacts [H₀old_ne_U_H h.symm, s₀old_ne_U_H h.symm])
    (Or.inl ret₂_U_H)
theorem qM_s₀new : qM s₀new = ofOrd (ω2 4) :=
  qM_of_sep (by rintro (h | h); exacts [s₀new_ne_H₀old h, s₀new_ne_s₀old h])
    (Or.inr (Or.inl ret₂_s₀new))
theorem qM_U_S : qM U_S = ofOrd (ω2 4) :=
  qM_of_sep (by rintro (h | h); exacts [U_S_ne_H₀old h, U_S_ne_s₀old h])
    (Or.inr (Or.inl ret₂_U_S))
theorem b₁new_ne_old : ¬ (b₁new = H₀old ∨ b₁new = s₀old) := by
  rintro (h | h)
  · exact zero_not_mem_scope_copyB _ (h ▸ zero_mem_scope_H₀old)
  · exact zero_not_mem_scope_copyB _ (h ▸ zero_mem_scope_s₀old)
theorem ub₁_ne_old : ¬ (ub₁ = H₀old ∨ ub₁ = s₀old) := fullCell_ne_old b₁X rfl
theorem qM_b₁new : qM b₁new = ofOrd (ω2 4) := qM_of_sep b₁new_ne_old (Or.inr (Or.inr ret₂_b₁new))
theorem qM_ub₁ : qM ub₁ = ofOrd (ω2 4) := qM_of_sep ub₁_ne_old (Or.inr (Or.inr ret₂_ub₁))

theorem qM_of_ret_a₁ {d : Cell D₂} (h : ret₂ d = family₂.e a₁X) : qM d = qL d := by
  apply qM_of_other
  · rintro (e | e)
    · rw [e, ret₂_H₀old] at h; cases family₂.e.injective h
    · rw [e, ret₂_s₀old] at h; cases family₂.e.injective h
  · rw [h]
    rintro (e | e | e)
    · cases family₂.e.injective e
    · cases family₂.e.injective e
    · exact a₁_ne_b₁ (congrArg Subtype.val (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
        (family₂.e.injective e)))))
theorem qM_of_ret_a₂ {d : Cell D₂} (h : ret₂ d = family₂.e a₂X) : qM d = qL d := by
  apply qM_of_other
  · rintro (e | e)
    · rw [e, ret₂_H₀old] at h; cases family₂.e.injective h
    · rw [e, ret₂_s₀old] at h; cases family₂.e.injective h
  · rw [h]
    rintro (e | e | e)
    · cases family₂.e.injective e
    · cases family₂.e.injective e
    · exact a₂_ne_b₁ (congrArg Subtype.val (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
        (family₂.e.injective e)))))
theorem qM_of_proper {d : Cell D₂} (hd : ¬ mute₂ d) {c : Prop3}
    (hc : family₂.e.symm (ret₂ d) = .inl c) : qM d = t₀.F c := by
  rw [← qL_of_proper hd hc]
  apply qM_of_other
  · rintro (e | e)
    · rw [e, ret₂_H₀old, Equiv.symm_apply_apply] at hc; cases hc
    · rw [e, ret₂_s₀old, Equiv.symm_apply_apply] at hc; cases hc
  · rintro (e | e | e)
    · exact ret_ne_of_inl' hc rfl e
    · exact ret_ne_of_inl' hc rfl e
    · exact ret_ne_of_inl' hc rfl e

theorem qM_a₁old : qM a₁old = η₁ := (qM_of_ret_a₁ ret₂_a₁old).trans
  ((qL_castAdd _).trans ((pull_eq_rowX _ not_mute_a₁old ret₂_a₁old).trans rowX_a₂_a₁))
theorem qM_A₁c : qM A₁c = η₁ := (qM_of_ret_a₁ ret₂_A₁c).trans qL_A₁c
theorem qM_a₂old : qM a₂old = γ₀ := (qM_of_ret_a₂ ret₂_a₂old).trans qL_a₂old
theorem qM_A₂c : qM A₂c = γ₀ := (qM_of_ret_a₂ ret₂_A₂c).trans qL_A₂c

theorem ω2_three_lt_four : ofOrd (ω2 3) < ofOrd (ω2 4) :=
  ofOrd_lt_ofOrd.mpr (ω2_lt_ω2 (by decide))
theorem ω2_one_lt_two' : ofOrd (ω2 1) < ofOrd (ω2 2) :=
  ofOrd_lt_ofOrd.mpr (ω2_lt_ω2 (by decide))
theorem ω2_lt_ω2_four (j : ℕ) (h : j < 4) : ofOrd (ω2 j) < ofOrd (ω2 4) :=
  ofOrd_lt_ofOrd.mpr (ω2_lt_ω2 h)
theorem η₁_lt_ω2 (j : ℕ) : η₁ < ofOrd (ω2 j) := by
  rw [η₁_num]; exact ofOrd_lt_ofOrd.mpr (ω1j_lt_ω2 _ _)
theorem γ₀_lt_ω2 (j : ℕ) : γ₀ < ofOrd (ω2 j) := by
  rw [γ₀_num']; exact ofOrd_lt_ofOrd.mpr (ω1j_lt_ω2 _ _)
theorem selfVis_ω2 (K j : ℕ) (h : K ≤ j) : SelfVis K (ofOrd (ω2 j)) := by
  rw [selfVis_ofOrd_iff, fp_ω2]; exact h

/-- The repaired row is self-visible at every grade at most three. -/
theorem qM_selfVis (d : D₂.below (D₂.cell ub₁)) : SelfVis (D₂.grade d.1) (qM d.1) := by
  have hg := grade_le_below_ub₁ d
  by_cases h1 : d.1 = H₀old ∨ d.1 = s₀old
  · rw [qM_of_old h1]; exact selfVis_ω2 _ _ hg
  by_cases h2 : ret₂ d.1 = family₂.e H₀X ∨ ret₂ d.1 = family₂.e s₀X ∨ ret₂ d.1 = family₂.e b₁X
  · rw [qM_of_sep h1 h2]; exact selfVis_ω2 _ _ (by omega)
  · rw [qM_of_other h1 h2]; exact qL_selfVis d

/-- **The repaired semantics' rows**: `rows₃` except at `b₁`'s controller. -/
noncomputable def E_R (Sig : Cell D₂) (d : D₂.below (D₂.cell Sig)) : ExtOrd :=
  if Sig = ub₁ then qM d.1 else E₃ Sig d

theorem E_R_ub₁ (d : D₂.below (D₂.cell ub₁)) : E_R ub₁ d = qM d.1 := by
  unfold E_R; rw [ite_eq_left rfl]
theorem E_R_of_ne {Sig : Cell D₂} (h : Sig ≠ ub₁) (d : D₂.below (D₂.cell Sig)) :
    E_R Sig d = rows₃.E Sig d := by
  unfold E_R; rw [ite_eq_right h]; rfl

/-- **The repaired semantics.** -/
noncomputable def rowsR : Semantics D₂ where
  E := E_R
  orderly Sig d := by
    change E_R Sig d = extVisibilityReplace (E_R Sig d) (D₂.grade d.1) (D₂.grade d.1)
    by_cases h : Sig = ub₁
    · subst h; rw [E_R_ub₁]; exact (qM_selfVis d).symm
    · rw [E_R_of_ne h]; exact rows₃.orderly Sig d

theorem rowsR_E (Sig : Cell D₂) (d : D₂.below (D₂.cell Sig)) : rowsR.E Sig d = E_R Sig d := rfl
theorem rowsR_E_ub₁ (d : D₂.below (D₂.cell ub₁)) : rowsR.E ub₁ d = qM d.1 := E_R_ub₁ d
theorem rowsR_E_of_ne {Sig : Cell D₂} (h : Sig ≠ ub₁) : rowsR.E Sig = rows₃.E Sig :=
  funext (E_R_of_ne h)

/-! ### Acceptance 1: both faces literal, every other row unchanged -/

theorem rowsR_E_of_A {Sig : Cell D₂} (h : AFace Sig) (d : D₂.below (D₂.cell Sig)) :
    rowsR.E Sig d = rows₂.E Sig d := by
  rw [rowsR_E_of_ne (aFace_ne_fullCell h b₁X rfl)]; exact E₃_of_A h d
theorem rowsR_E_of_B {Sig : Cell D₂} (h : BFace Sig) (d : D₂.below (D₂.cell Sig)) :
    rowsR.E Sig d = rows₂.E Sig d := by
  rw [rowsR_E_of_ne (B_face_ne_fullCell h b₁X rfl)]; exact E₃_of_B h d
theorem rowsR_E_of_proper_scope {Sig : Cell D₂} (h : D₂.scope Sig ≠ Finset.univ) :
    rowsR.E Sig = rows₂.E Sig := by
  rw [rowsR_E_of_ne (fun e => h (by rw [e]; exact congrArg Prod.fst cell_ub₁))]
  exact rows₃_E_of_proper_scope h

/-! ### Acceptance 2a: coded -/

theorem rowsR_coded : rowsR.IsCoded := by
  intro Sig d
  by_cases h : Sig = ub₁
  · subst h
    rw [rowsR_E_ub₁, grade_ub₁]
    by_cases h1 : d.1 = H₀old ∨ d.1 = s₀old
    · rw [qM_of_old h1]; exact Or.inr ⟨2, 3, by omega, rfl⟩
    by_cases h2 : ret₂ d.1 = family₂.e H₀X ∨ ret₂ d.1 = family₂.e s₀X ∨
        ret₂ d.1 = family₂.e b₁X
    · rw [qM_of_sep h1 h2]; exact Or.inr ⟨2, 4, by omega, rfl⟩
    · rw [qM_of_other h1 h2]
      have := rows₃_coded ub₁ d
      rwa [rows₃_E, E₃_ub₁, grade_ub₁] at this
  · rw [rowsR_E_of_ne h]; exact rows₃_coded Sig d

end Row

/-! ## Acceptance 2b: consistency, both directions at `b₁`'s controller -/

section Consistency

/-- The cells with `b₁`'s controller below them: the three controllers and the mute cell. -/
theorem ub₁_below_cases {Sig : Cell D₂} (h : GradedLe (D₂.cell ub₁) (D₂.cell Sig)) :
    Sig = A₁c ∨ Sig = A₂c ∨ Sig = ub₁ ∨ mute₂ Sig := by
  rw [cell_ub₁] at h
  have hs : D₂.scope Sig = Finset.univ := Finset.univ_subset_iff.mp h.1
  have hg3 : 3 ≤ D₂.grade Sig := h.2
  have hg4 : D₂.grade Sig ≤ 4 := by
    have := D₂.grade_le_card_scope Sig
    rwa [hs, Finset.card_univ, Fintype.card_fin] at this
  by_cases hg : D₂.grade Sig = 3
  · have : D₂.cell Sig = (Finset.univ, 3) := Prod.ext hs hg
    rcases eq_three_of_cell this with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
  · right; right; right
    change D₂.cell Sig = (Finset.univ, 4)
    exact Prod.ext hs (show D₂.grade Sig = 4 by omega)

/-- A row whose cell does not lie above `b₁`'s controller is consistent as before. -/
theorem consistentR_of_not_above {Sig : Cell D₂} (h : ¬ GradedLe (D₂.cell ub₁) (D₂.cell Sig)) :
    RespectsSemanticsBelow rowsR (D₂.cell Sig) (rowsR.E Sig) := by
  have hne : Sig ≠ ub₁ := fun e => h (e ▸ GradedLe.refl _)
  rw [rowsR_E_of_ne hne]
  exact (rows₃_consistent Sig).congr_sem fun Sig' => rowsR_E_of_ne fun e => h (e ▸ Sig'.2)

theorem rowsR_E_mute {Sig : Cell D₂} (h : mute₂ Sig) (d : D₂.below (D₂.cell Sig)) :
    rowsR.E Sig d = ⊥ := by
  rw [rowsR_E_of_ne (fun e => not_mute_ub₁ (e ▸ h))]; exact rows₃_E_mute h d

theorem consistentR_mute {Sig : Cell D₂} (h : mute₂ Sig) :
    RespectsSemanticsBelow rowsR (D₂.cell Sig) (rowsR.E Sig) where
  orderly := rowsR.orderly Sig
  locality Sig' := by
    refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
    funext d; rw [rowsR_E_mute h, rowsR_E_mute h, min_self]
  availability Sig' Xi₀ _ _ := ⟨Xi₀, rfl, by rw [rowsR_E_mute h, rowsR_E_mute h]⟩

/-- The value of the repaired row against a cap `c` between `ω+4` and `ω·2+4`: the clamp at
`ω·2+4` with constants `c`, `c`. -/
theorem clamp_qM {c : ExtOrd} (hc' : c < ofOrd (ω2 4)) (d : Cell D₂) :
    clampShifter c (ω2 4) c (qM d) = min (qM d) c := by
  by_cases h1 : d = H₀old ∨ d = s₀old
  · rw [qM_of_old h1, clampShifter_of_lt ω2_three_lt_four]
  by_cases h2 : ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X ∨ ret₂ d = family₂.e b₁X
  · rw [qM_of_sep h1 h2, clampShifter_of_ge le_rfl, min_eq_right hc'.le]
  · rw [qM_of_other h1 h2, clampShifter_of_lt ((qL_le_γ₁ d).trans_lt
      (by rw [γ₁_num]; exact ω2_lt_ω2_four 3 (by decide)))]

end Consistency

/-! ## A witness shape: the identity below a limit cutoff, a constant above -/

section IdConst

open Classical in
/-- The identity below `ω·n`, the constant `c` from `ω·n` on. -/
noncomputable def idConstShifter (n : ℕ) (c : ExtOrd) : ExtOrd → ExtOrd :=
  fun a => if a < ofOrd (Ordinal.omega0 * (n : Ordinal)) then a else c

theorem idConst_of_lt {n : ℕ} {c a : ExtOrd} (h : a < ofOrd (Ordinal.omega0 * (n : Ordinal))) :
    idConstShifter n c a = a := by
  classical
  unfold idConstShifter; rw [ite_eq_left h]
theorem idConst_of_ge {n : ℕ} {c a : ExtOrd} (h : ofOrd (Ordinal.omega0 * (n : Ordinal)) ≤ a) :
    idConstShifter n c a = c := by
  classical
  unfold idConstShifter; rw [ite_eq_right (not_lt.mpr h)]

/-- **The identity-then-constant witness**: `c` self-visible at `K` and at least the cutoff. -/
theorem Witness.idConst (K n : ℕ) {c : ExtOrd} (hc : SelfVis K c)
    (hnc : ofOrd (Ordinal.omega0 * (n : Ordinal)) ≤ c) : Witness (gTop K) (idConstShifter n c) where
  anti := (witness_id K).anti
  vis := (witness_id K).vis
  bot := idConst_of_lt (bot_lt_ofOrd _)
  mono := by
    intro a b hab
    by_cases hal : a < ofOrd (Ordinal.omega0 * (n : Ordinal))
    · rw [idConst_of_lt hal]
      by_cases hbl : b < ofOrd (Ordinal.omega0 * (n : Ordinal))
      · rw [idConst_of_lt hbl]; exact hab
      · rw [idConst_of_ge (not_lt.mp hbl)]; exact hal.le.trans hnc
    · have hbl : ¬ b < ofOrd (Ordinal.omega0 * (n : Ordinal)) :=
        fun hbl => hal (lt_of_le_of_lt hab hbl)
      rw [idConst_of_ge (not_lt.mp hal), idConst_of_ge (not_lt.mp hbl)]
  clause5 := by
    intro α k hk i hi
    by_cases hkK : k ≤ K
    · by_cases hal : α < ofOrd (Ordinal.omega0 * (n : Ordinal))
      · rw [idConst_of_lt hal, idConst_of_lt (evr_lt_limit hal k i)]
      · rw [idConst_of_ge (not_lt.mp hal), idConst_of_ge (evr_ge_limit (not_lt.mp hal) k i),
          evr_eq_self_of_selfVis (hc.mono hkK)]
    · rw [gTop_of_gt (by omega)] at hk
      have hσ := le_bot_iff.mp hk
      by_cases hal : α < ofOrd (Ordinal.omega0 * (n : Ordinal))
      · rw [idConst_of_lt hal] at hσ
        rw [hσ, extVisibilityReplace_bot, idConst_of_lt (bot_lt_ofOrd _), extVisibilityReplace_bot]
      · rw [idConst_of_ge (not_lt.mp hal)] at hσ
        exact absurd hσ (ne_bot_of_le_ne_bot (ofOrd_ne_bot _) hnc)

theorem ω2_zero' : Ordinal.omega0 * ((2 : ℕ) : Ordinal) = ω2 0 := ω2_zero.symm
theorem ofOrd_ω2_le (j : ℕ) : ofOrd (Ordinal.omega0 * ((2 : ℕ) : Ordinal)) ≤ ofOrd (ω2 j) :=
  ω2_ge j
theorem idConst_ω2 {c : ExtOrd} (j : ℕ) : idConstShifter 2 c (ofOrd (ω2 j)) = c :=
  idConst_of_ge (ω2_ge j)
theorem idConst_v₀ {c : ExtOrd} : idConstShifter 2 c v₀ = v₀ := idConst_of_lt v₀_lt_ω2'
theorem idConst_bot' {c : ExtOrd} : idConstShifter 2 c ⊥ = ⊥ := idConst_of_lt (bot_lt_ofOrd _)
theorem idConst_lt_ω2 {c a : ExtOrd} (h : a < ofOrd (Ordinal.omega0 * ((2 : ℕ) : Ordinal))) :
    idConstShifter 2 c a = a := idConst_of_lt h

end IdConst

/-! ## The values of the repaired row against the caps -/

section MinQM

theorem qM_le_ω2_four (d : Cell D₂) : qM d ≤ ofOrd (ω2 4) := by
  by_cases h1 : d = H₀old ∨ d = s₀old
  · rw [qM_of_old h1]; exact ω2_three_lt_four.le
  by_cases h2 : ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X ∨ ret₂ d = family₂.e b₁X
  · rw [qM_of_sep h1 h2]
  · rw [qM_of_other h1 h2]
    exact (qL_le_γ₁ d).trans (by rw [γ₁_num]; exact ω2_three_lt_four.le)

theorem pull_of_sep {x : family₂.X} {d : Cell D₂} (hd : ¬ mute₂ d)
    (h : ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X ∨ ret₂ d = family₂.e b₁X)
    {v : ExtOrd} (hH : family₂.rowX x H₀X = v) (hs : family₂.rowX x s₀X = v)
    (hb : family₂.rowX x b₁X = v) : pull x d = v := by
  rcases h with h | h | h
  · rw [pull_eq_rowX _ hd h, hH]
  · rw [pull_eq_rowX _ hd h, hs]
  · rw [pull_eq_rowX _ hd h, hb]

/-- `min (qM d) η₁ = pull a₁X d`: the repaired row reads `a₁`'s row below `ω+3`. -/
theorem min_qM_η₁ {d : Cell D₂} (hd : ¬ mute₂ d) : min (qM d) η₁ = pull a₁X d := by
  by_cases h1 : d = H₀old ∨ d = s₀old
  · rw [qM_of_old h1, min_eq_right (η₁_lt_ω2 3).le]
    rcases h1 with rfl | rfl
    · exact (pull_eq_rowX _ hd ret₂_H₀old).trans rowX_a₁_H |>.symm
    · exact (pull_eq_rowX _ hd ret₂_s₀old).trans rowX_a₁_s |>.symm
  by_cases h2 : ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X ∨ ret₂ d = family₂.e b₁X
  · rw [qM_of_sep h1 h2, min_eq_right (η₁_lt_ω2 4).le,
      pull_of_sep hd h2 rowX_a₁_H rowX_a₁_s rowX_a₁_b₁]
  · rw [qM_of_other h1 h2]; exact min_qL_η₁ hd

/-- `min (qM d) γ₀ = pull a₂X d`: the repaired row reads `a₂`'s row below `ω+4`. -/
theorem min_qM_γ₀ {d : Cell D₂} (hd : ¬ mute₂ d) : min (qM d) γ₀ = pull a₂X d := by
  by_cases h1 : d = H₀old ∨ d = s₀old
  · rw [qM_of_old h1, min_eq_right (γ₀_lt_ω2 3).le]
    rcases h1 with rfl | rfl
    · exact (pull_eq_rowX _ hd ret₂_H₀old).trans rowX_a₂_H |>.symm
    · exact (pull_eq_rowX _ hd ret₂_s₀old).trans rowX_a₂_s |>.symm
  by_cases h2 : ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X ∨ ret₂ d = family₂.e b₁X
  · rw [qM_of_sep h1 h2, min_eq_right (γ₀_lt_ω2 4).le,
      pull_of_sep hd h2 rowX_a₂_H rowX_a₂_s rowX_a₂_b₁]
  · rw [qM_of_other h1 h2]; exact min_qL_γ₀ hd

theorem pull_a₁_le (d : Cell D₂) : pull a₁X d ≤ η₁ := by
  by_cases hd : mute₂ d
  · unfold pull; rw [ite_eq_left hd]; exact bot_le
  · rw [← min_qM_η₁ hd]; exact min_le_right _ _
theorem pull_a₂_le (d : Cell D₂) : pull a₂X d ≤ γ₀ := by
  by_cases hd : mute₂ d
  · unfold pull; rw [ite_eq_left hd]; exact bot_le
  · rw [← min_qM_γ₀ hd]; exact min_le_right _ _

end MinQM

/-! ## Acceptance 2b, continued: the two reverse incidences and the changed row itself -/

section ConsistencyR

/-- **`a₁`'s controller's row respects the repaired row** (the reverse incidence): the clamp at
`ω+3` reads the repaired row as `a₁`'s. -/
theorem A₁c_locality_ub₁R (hy : GradedLe (D₂.cell ub₁) (D₂.cell A₁c)) :
    TransformsTo (fun d : D₂.below (D₂.cell ub₁) => D₂.grade d.1) (rowsR.E ub₁)
      (fun d => min (rowsR.E A₁c (CellScheme.below.incl ⟨ub₁, hy⟩ d)) (rowsR.E A₁c ⟨ub₁, hy⟩)) := by
  refine (Witness.clamp 3 (ξ := ω2 4) (by rw [fp_ω2]; omega) (c := η₁) (c' := η₁) η₁_vis η₁_vis
    le_rfl (ofOrd_ne_bot _) (ofOrd_ne_bot _)).transformsTo fun d => ?_
  rw [gTop_of_le (K := 3) (k := D₂.grade d.1) (grade_le_below_ub₁ d), min_eq_left le_top,
    rowsR_E_ub₁, clamp_qM (c := η₁) (η₁_lt_ω2 4) d.1, min_qM_η₁ (not_mute_below_ub₁ d)]
  rw [rowsR_E_of_ne A₁c_ne_ub₁, E₃_A₁c (CellScheme.below.incl ⟨ub₁, hy⟩ d), E₃_A₁c ⟨ub₁, hy⟩]
  change min (pull a₁X d.1) (pull a₁X ub₁) = pull a₁X d.1
  rw [pull_eq_rowX _ not_mute_ub₁ ret₂_ub₁, rowX_a₁_b₁]
  exact min_eq_left (pull_a₁_le _)

theorem A₂c_locality_ub₁R (hy : GradedLe (D₂.cell ub₁) (D₂.cell A₂c)) :
    TransformsTo (fun d : D₂.below (D₂.cell ub₁) => D₂.grade d.1) (rowsR.E ub₁)
      (fun d => min (rowsR.E A₂c (CellScheme.below.incl ⟨ub₁, hy⟩ d)) (rowsR.E A₂c ⟨ub₁, hy⟩)) := by
  refine (Witness.clamp 3 (ξ := ω2 4) (by rw [fp_ω2]; omega) (c := γ₀) (c' := γ₀) γ₀_vis γ₀_vis
    le_rfl (ofOrd_ne_bot _) (ofOrd_ne_bot _)).transformsTo fun d => ?_
  rw [gTop_of_le (K := 3) (k := D₂.grade d.1) (grade_le_below_ub₁ d), min_eq_left le_top,
    rowsR_E_ub₁, clamp_qM (c := γ₀) (γ₀_lt_ω2 4) d.1, min_qM_γ₀ (not_mute_below_ub₁ d)]
  rw [rowsR_E_of_ne A₂c_ne_ub₁, E₃_A₂c (CellScheme.below.incl ⟨ub₁, hy⟩ d), E₃_A₂c ⟨ub₁, hy⟩]
  change min (pull a₂X d.1) (pull a₂X ub₁) = pull a₂X d.1
  rw [pull_eq_rowX _ not_mute_ub₁ ret₂_ub₁, rowX_a₂_b₁]
  exact min_eq_left (pull_a₂_le _)

theorem consistentR_A₁c : RespectsSemanticsBelow rowsR (D₂.cell A₁c) (rowsR.E A₁c) where
  orderly := rowsR.orderly A₁c
  locality Sig' := by
    by_cases h : Sig'.1 = ub₁
    · have e : Sig' = ⟨ub₁, by rw [← h]; exact Sig'.2⟩ := Subtype.ext h
      rw [e]; exact A₁c_locality_ub₁R _
    · have key := consistent_A₁c.locality Sig'
      rw [rowsR_E_of_ne A₁c_ne_ub₁, rowsR_E_of_ne h]
      exact key
  availability := by
    rw [rowsR_E_of_ne A₁c_ne_ub₁]; exact consistent_A₁c.availability

theorem consistentR_A₂c : RespectsSemanticsBelow rowsR (D₂.cell A₂c) (rowsR.E A₂c) where
  orderly := rowsR.orderly A₂c
  locality Sig' := by
    by_cases h : Sig'.1 = ub₁
    · have e : Sig' = ⟨ub₁, by rw [← h]; exact Sig'.2⟩ := Subtype.ext h
      rw [e]; exact A₂c_locality_ub₁R _
    · have key := consistent_A₂c.locality Sig'
      rw [rowsR_E_of_ne A₂c_ne_ub₁, rowsR_E_of_ne h]
      exact key
  availability := by
    rw [rowsR_E_of_ne A₂c_ne_ub₁]; exact consistent_A₂c.availability

end ConsistencyR

/-! ## Acceptance 2b, concluded: the repaired row respects every row below it -/

section RespectR

theorem qM_proper_one {d : Cell D₂} (hd : ¬ mute₂ d) (hp : IsProper d) (hg : D₂.grade d ≤ 1) :
    qM d = v₀ := by
  obtain ⟨c, hc⟩ := hp
  rw [qM_of_proper hd hc, t₀_F_v₀ (by rw [gradeP_le_of_proper hd hc]; exact hg)]
theorem qM_proper_two {d : Cell D₂} (hd : ¬ mute₂ d) (hp : IsProper d) (hg : D₂.grade d = 2) :
    qM d = ⊥ := by
  obtain ⟨c, hc⟩ := hp
  rw [qM_of_proper hd hc, t₀_F_bot (by rw [gradeP_le_of_proper hd hc]; exact hg)]
theorem qM_proper_le {d : Cell D₂} (hd : ¬ mute₂ d) (hp : IsProper d) : qM d ≤ v₀ := by
  obtain ⟨c, hc⟩ := hp
  rw [qM_of_proper hd hc]
  rcases t₀_F_cases c with h | h
  · rw [h]
  · rw [h]; exact bot_le

theorem a₁old_ne_ub₁ : a₁old ≠ ub₁ := fun h => castAdd_ne_fullCell _ b₁X rfl (h.trans ub₁_eq)
theorem H₀old_ne_ub₁ : H₀old ≠ ub₁ := fun h => castAdd_ne_fullCell _ b₁X rfl (h.trans ub₁_eq)
theorem s₀old_ne_ub₁ : s₀old ≠ ub₁ := fun h => castAdd_ne_fullCell _ b₁X rfl (h.trans ub₁_eq)
theorem H₀new_ne_ub₁ : H₀new ≠ ub₁ := fun h =>
  B_face_ne_fullCell (copyB_mem _) b₁X rfl (h.trans ub₁_eq)
theorem s₀new_ne_ub₁ : s₀new ≠ ub₁ := fun h =>
  B_face_ne_fullCell (copyB_mem _) b₁X rfl (h.trans ub₁_eq)
theorem b₁new_ne_ub₁ : b₁new ≠ ub₁ := fun h =>
  B_face_ne_fullCell (copyB_mem _) b₁X rfl (h.trans ub₁_eq)

theorem below_b₁new_mem (d : D₂.below (D₂.cell b₁new)) :
    GradedLe (D₂.cell d.1) (({1, 2, 3} : Finset (Fin 4)), 3) := d.2.trans (copyB_mem _)

/-- Below the copy of `b₁`: the three copies or a proper cell. -/
theorem below_b₁new_cases (d : D₂.below (D₂.cell b₁new)) :
    d.1 = b₁new ∨ d.1 = H₀new ∨ d.1 = s₀new ∨ IsProper d.1 := by
  have hr := ret₂_eq_emb₁_retB zero_not_mem_B ⟨d.1, below_b₁new_mem d⟩
  rcases img_cases (family₁.e.symm (retB d.1)) with ⟨c, hc⟩ | hc | hc | hc
  · right; right; right
    refine ⟨c, ?_⟩
    rw [hr]
    change family₂.e.symm (family₂.e (embX₁ (family₁.e.symm (retB d.1)))) = _
    rw [Equiv.symm_apply_apply, hc]; rfl
  · right; left
    have h1 : retB d.1 = family₁.e H₀X₁ := by rw [← hc, Equiv.apply_symm_apply]
    have := retB_inj zero_not_mem_B ⟨d.1, below_b₁new_mem d⟩ ⟨H₀new, copyB_mem _⟩
      (h1.trans (retB_copyB _).symm)
    exact congrArg Subtype.val this
  · right; right; left
    have h1 : retB d.1 = family₁.e s₀X₁ := by rw [← hc, Equiv.apply_symm_apply]
    have := retB_inj zero_not_mem_B ⟨d.1, below_b₁new_mem d⟩ ⟨s₀new, copyB_mem _⟩
      (h1.trans (retB_copyB _).symm)
    exact congrArg Subtype.val this
  · left
    have h1 : retB d.1 = family₁.e b₁X₁ := by rw [← hc, Equiv.apply_symm_apply]
    have := retB_inj zero_not_mem_B ⟨d.1, below_b₁new_mem d⟩ ⟨b₁new, copyB_mem _⟩
      (h1.trans (retB_copyB _).symm)
    exact congrArg Subtype.val this

theorem scope_b₁new : D₂.scope b₁new = {1, 2, 3} := by
  apply fold_univ_of_B _ (D₂.scope_mem_plan _) (zero_not_mem_scope_copyB _)
  have h := cell_copyB (family₁.e b₁X₁)
  rw [Family.cell_e] at h
  exact (congrArg Prod.fst h).symm
theorem three_mem_scope_b₁new : (3 : Fin 4) ∈ D₂.scope b₁new := by rw [scope_b₁new]; decide
theorem three_mem_scope_A₁c : (3 : Fin 4) ∈ D₂.scope A₁c := by
  change (3 : Fin 4) ∈ (D₂.cell A₁c).1; rw [cell_A₁c]; exact Finset.mem_univ _
theorem three_mem_scope_A₂c : (3 : Fin 4) ∈ D₂.scope A₂c := by
  change (3 : Fin 4) ∈ (D₂.cell A₂c).1; rw [cell_A₂c]; exact Finset.mem_univ _
theorem three_mem_scope_ub₁ : (3 : Fin 4) ∈ D₂.scope ub₁ := by
  change (3 : Fin 4) ∈ (D₂.cell ub₁).1; rw [cell_ub₁]; exact Finset.mem_univ _

theorem rowsR_E_b₁new (d : D₂.below (D₂.cell b₁new)) :
    rowsR.E b₁new d = family₂.rowX b₁X (family₂.e.symm (ret₂ d.1)) := by
  have hB : BFace b₁new := copyB_mem _
  rw [rowsR_E_of_B hB d, rows₂_E_eq_pull not_mute_b₁new, ret₂_b₁new,
    Equiv.symm_apply_apply, pull_of_not_mute _ (hmute_below₂ _ d.1 not_mute_b₁new d.2)]

theorem v₀_le_ω2 (j : ℕ) : v₀ ≤ ofOrd (ω2 j) := (v₀_lt_ω2 j).le

theorem witness_idConst₃ : Witness (gTop 1) (idConstShifter 2 (ofOrd (ω2 3))) :=
  Witness.idConst 1 2 (selfVis_ω2 1 3 (by decide)) (ω2_ge 3)
theorem witness_idConst₃' : Witness (gTop 2) (idConstShifter 2 (ofOrd (ω2 3))) :=
  Witness.idConst 2 2 (selfVis_ω2 2 3 (by decide)) (ω2_ge 3)
theorem witness_idConst₄ (K : ℕ) (hK : K ≤ 3) :
    Witness (gTop K) (idConstShifter 2 (ofOrd (ω2 4))) :=
  Witness.idConst K 2 (selfVis_ω2 K 4 (by omega)) (ω2_ge 4)
theorem idConst₃_ne_bot (j : ℕ) : idConstShifter 2 (ofOrd (ω2 3)) (ofOrd (ω2 j)) ≠ ⊥ := by
  rw [idConst_ω2]; exact ofOrd_ne_bot _

/-- **The repaired row respects every row below `b₁`'s controller** (the forward incidences). -/
theorem qM_respects : RespectsSemanticsBelow rowsR (Finset.univ, 3) (fun d => qM d.1) where
  orderly d := (qM_selfVis ⟨d.1, by rw [cell_ub₁]; exact d.2⟩).symm
  locality := by
    intro Sig
    obtain ⟨x, hx⟩ := Sig
    have hnm : ¬ mute₂ x := not_mute₂_of_low le_rfl ⟨x, hx⟩
    by_cases hg3 : D₂.grade x = 3
    · rcases three_cases hnm hg3 with rfl | rfl | rfl | rfl | rfl | rfl
      · -- the old cap `a₁`: the target is the source
        refine transformsTo_congr rfl rfl ?_ (TransformsTo.refl _)
        funext d
        change rowsR.E a₁old d = min (qM d.1) (qM a₁old)
        rw [rowsR_E_of_ne a₁old_ne_ub₁, rows₃_a₁old_eq, qM_a₁old,
          min_qM_η₁ (hmute_below₂ _ d.1 not_mute_a₁old d.2)]
      · -- the old cap `a₂`
        refine transformsTo_congr rfl rfl ?_ (TransformsTo.refl _)
        funext d
        change rowsR.E a₂old d = min (qM d.1) (qM a₂old)
        have hA : AFace a₂old := aFace_castAdd _
        rw [rowsR_E_of_A hA d, rows₂_a₂old_eq, qM_a₂old,
          min_qM_γ₀ (hmute_below₂ _ d.1 not_mute_a₂old d.2)]
      · -- the copy of `b₁`: raised to `ω·2+4`
        refine (witness_idConst₄ 3 le_rfl).transformsTo fun d => ?_
        rw [gTop_of_le (K := 3) (k := D₂.grade d.1) (d.2.2.trans grade_b₁new.le),
          min_eq_left le_top]
        change min (qM d.1) (qM b₁new) = _
        rw [qM_b₁new, rowsR_E_b₁new]
        rcases below_b₁new_cases d with hd | hd | hd | hd
        · rw [hd, ret₂_b₁new, Equiv.symm_apply_apply, rowX_b₁_b₁, γ₁_num, idConst_ω2, qM_b₁new,
            min_self]
        · rw [hd, ret₂_H₀new, Equiv.symm_apply_apply, rowX_b₁_H, γ₁_num, idConst_ω2, qM_H₀new,
            min_self]
        · rw [hd, ret₂_s₀new, Equiv.symm_apply_apply, rowX_b₁_s, γ₁_num, idConst_ω2, qM_s₀new,
            min_self]
        · have hnd : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_b₁new d.2
          obtain ⟨c, hc⟩ := hd
          rw [hc, rowX_b₁_inl, qM_of_proper hnd hc]
          rcases t₀_F_cases c with h | h
          · rw [h, idConst_v₀, min_eq_left (v₀_le_ω2 4)]
          · rw [h, idConst_bot', min_eq_left bot_le]
      · -- `a₁`'s controller: the target is the source
        refine transformsTo_congr rfl rfl ?_ (TransformsTo.refl _)
        funext d
        change rowsR.E A₁c d = min (qM d.1) (qM A₁c)
        rw [rowsR_E_of_ne A₁c_ne_ub₁, E₃_A₁c d, qM_A₁c,
          min_qM_η₁ (hmute_below₂ _ d.1 not_mute_A₁c d.2)]
      · -- `a₂`'s controller
        refine transformsTo_congr rfl rfl ?_ (TransformsTo.refl _)
        funext d
        change rowsR.E A₂c d = min (qM d.1) (qM A₂c)
        rw [rowsR_E_of_ne A₂c_ne_ub₁, E₃_A₂c d, qM_A₂c,
          min_qM_γ₀ (hmute_below₂ _ d.1 not_mute_A₂c d.2)]
      · -- `b₁`'s controller: its own row
        refine transformsTo_congr rfl rfl ?_ (TransformsTo.refl _)
        funext d
        change rowsR.E ub₁ d = min (qM d.1) (qM ub₁)
        rw [rowsR_E_ub₁, qM_ub₁, min_eq_left (qM_le_ω2_four _)]
    · have hg2 : D₂.grade x ≤ 2 := by have := hx.2; change D₂.grade x ≤ 3 at this; omega
      rcases two_cases hnm hg2 with rfl | rfl | rfl | rfl | rfl | rfl | ⟨hP, hg⟩ | ⟨hP, hg⟩
      · -- the old occurrence: `ω·2+1 ↦ ω·2+3`
        refine witness_idConst₃.transformsTo fun d => ?_
        rw [gTop_of_le (K := 1) (k := D₂.grade d.1) (d.2.2.trans grade_H₀old.le),
          min_eq_left le_top]
        change min (qM d.1) (qM H₀old) = _
        rw [qM_H₀old, rowsR_E_of_ne H₀old_ne_ub₁]
        rcases below_H₀old_cases d with hd | hd
        · rw [rows₃_E_H₀old_self d hd, idConst_ω2, hd, qM_H₀old, min_self]
        · have hnd : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_H₀old d.2
          rw [rows₃_E_one_proper grade_H₀old d hd, idConst_v₀,
            qM_proper_one hnd hd (d.2.2.trans grade_H₀old.le), min_eq_left (v₀_le_ω2 3)]
      · -- the copy of `H₀`: `ω·2+1 ↦ ω·2+4`
        refine (witness_idConst₄ 1 (by decide)).transformsTo fun d => ?_
        rw [gTop_of_le (K := 1) (k := D₂.grade d.1) (d.2.2.trans grade_H₀new.le),
          min_eq_left le_top]
        change min (qM d.1) (qM H₀new) = _
        rw [qM_H₀new, rowsR_E_of_ne H₀new_ne_ub₁]
        rcases below_H₀new_cases' d with hd | hd
        · rw [rows₃_E_H₀new_self d hd, idConst_ω2, hd, qM_H₀new, min_self]
        · have hnd : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_H₀new d.2
          rw [rows₃_E_one_proper grade_H₀new d hd, idConst_v₀,
            qM_proper_one hnd hd (d.2.2.trans grade_H₀new.le), min_eq_left (v₀_le_ω2 4)]
      · -- the grade-one controller: `ω·2+1 ↦ ω·2+3`, `ω·2+2 ↦ ω·2+4`
        refine (witness_idConst₃.raise 1 (fun _ hk => gTop_bot hk) (ξ := ω2 2)
          (by rw [fp_ω2]; omega) (selfVis_ω2 1 4 (by decide))).transformsTo fun d => ?_
        rw [gTop_of_le (K := 1) (k := D₂.grade d.1) (below_U_H_mem d).2, min_eq_left le_top]
        change min (qM d.1) (qM U_H) = _
        rw [qM_U_H, rowsR_E_of_ne ub₁_ne_U_H.symm]
        rcases one_cases (not_mute_below_U_H d) (below_U_H_mem d).2 with hd | hd | hd | hd
        · rw [rows₃_E_U_H_H₀old d hd, raiseShifter_of_lt ω2_one_lt_two', idConst_ω2, hd, qM_H₀old,
            min_eq_left ω2_three_lt_four.le]
        · rw [rows₃_E_U_H_new d (Or.inl hd), raiseShifter_of_ge le_rfl (idConst₃_ne_bot 2),
            idConst_ω2, max_eq_right ω2_three_lt_four.le, hd, qM_H₀new, min_self]
        · rw [rows₃_E_U_H_new d (Or.inr hd), raiseShifter_of_ge le_rfl (idConst₃_ne_bot 2),
            idConst_ω2, max_eq_right ω2_three_lt_four.le, hd, qM_U_H, min_self]
        · rw [rows₃_E_one_proper grade_U_H d hd, raiseShifter_of_lt (v₀_lt_ω2 2), idConst_v₀,
            qM_proper_one (not_mute_below_U_H d) hd (below_U_H_mem d).2, min_eq_left (v₀_le_ω2 4)]
      · -- the old level-two witness: `ω·2+2 ↦ ω·2+3`
        refine witness_idConst₃'.transformsTo fun d => ?_
        rw [gTop_of_le (K := 2) (k := D₂.grade d.1) (d.2.2.trans grade_s₀old.le),
          min_eq_left le_top]
        change min (qM d.1) (qM s₀old) = _
        rw [qM_s₀old, rowsR_E_of_ne s₀old_ne_ub₁, rows₃_E_s₀old d]
        have hnd : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_s₀old d.2
        rcases below_s₀old_cases d with hd | hd | hd
        · rw [hd, ret₂_H₀old, Equiv.symm_apply_apply, rowX_s₀_H, s₀c_γ_num, idConst_ω2, qM_H₀old,
            min_self]
        · rw [hd, ret₂_s₀old, Equiv.symm_apply_apply, rowX_s₀_s, s₀c_γ_num, idConst_ω2, qM_s₀old,
            min_self]
        · rw [rowX_s₀_of_proper hnd hd]
          by_cases hg1 : D₂.grade d.1 ≤ 1
          · rw [ite_eq_left hg1, idConst_v₀, qM_proper_one hnd hd hg1, min_eq_left (v₀_le_ω2 3)]
          · have h2 : D₂.grade d.1 ≤ 2 := d.2.2.trans grade_s₀old.le
            rw [ite_eq_right hg1, idConst_bot', qM_proper_two hnd hd (by omega), min_eq_left bot_le]
      · -- the copy of the level-two witness: `ω·2+2 ↦ ω·2+4`
        refine (witness_idConst₄ 2 (by decide)).transformsTo fun d => ?_
        rw [gTop_of_le (K := 2) (k := D₂.grade d.1) (d.2.2.trans grade_s₀new.le),
          min_eq_left le_top]
        change min (qM d.1) (qM s₀new) = _
        rw [qM_s₀new, rowsR_E_of_ne s₀new_ne_ub₁, rows₃_E_s₀new d]
        have hnd : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_s₀new d.2
        rcases below_s₀new_cases₂ d with hd | hd | hd
        · rw [hd, ret₂_H₀new, Equiv.symm_apply_apply, rowX_s₀_H, s₀c_γ_num, idConst_ω2, qM_H₀new,
            min_self]
        · rw [hd, ret₂_s₀new, Equiv.symm_apply_apply, rowX_s₀_s, s₀c_γ_num, idConst_ω2, qM_s₀new,
            min_self]
        · rw [rowX_s₀_of_proper hnd hd]
          by_cases hg1 : D₂.grade d.1 ≤ 1
          · rw [ite_eq_left hg1, idConst_v₀, qM_proper_one hnd hd hg1, min_eq_left (v₀_le_ω2 4)]
          · have h2 : D₂.grade d.1 ≤ 2 := d.2.2.trans grade_s₀new.le
            rw [ite_eq_right hg1, idConst_bot', qM_proper_two hnd hd (by omega), min_eq_left bot_le]
      · -- the grade-two controller: `ω·2+2 ↦ ω·2+3`, `ω·2+3 ↦ ω·2+4`
        refine (witness_idConst₃'.raise 2 (fun _ hk => gTop_bot hk) (ξ := ω2 3)
          (by rw [fp_ω2]; omega) (selfVis_ω2 2 4 (by decide))).transformsTo fun d => ?_
        rw [gTop_of_le (K := 2) (k := D₂.grade d.1) (below_U_S_mem d).2, min_eq_left le_top]
        change min (qM d.1) (qM U_S) = _
        rw [qM_U_S, rowsR_E_of_ne ub₁_ne_U_S.symm, rows₃_E, E₃_U_S]
        have hnd := not_mute_below_U_S d
        rcases two_cases hnd (below_U_S_mem d).2 with hd | hd | hd | hd | hd | hd | ⟨hd, hg⟩ |
          ⟨hd, hg⟩
        · rw [hd, vS_H₀old, s₀c_γ_num, raiseShifter_of_lt ω2_two_lt_three, idConst_ω2, qM_H₀old,
            min_eq_left ω2_three_lt_four.le]
        · rw [hd, vS_H₀new, γ₁_num, raiseShifter_of_ge le_rfl (idConst₃_ne_bot 3), idConst_ω2,
            max_eq_right ω2_three_lt_four.le, qM_H₀new, min_self]
        · rw [hd, vS_U_H, γ₁_num, raiseShifter_of_ge le_rfl (idConst₃_ne_bot 3), idConst_ω2,
            max_eq_right ω2_three_lt_four.le, qM_U_H, min_self]
        · rw [hd, vS_s₀old, s₀c_γ_num, raiseShifter_of_lt ω2_two_lt_three, idConst_ω2, qM_s₀old,
            min_eq_left ω2_three_lt_four.le]
        · rw [hd, vS_s₀new, γ₁_num, raiseShifter_of_ge le_rfl (idConst₃_ne_bot 3), idConst_ω2,
            max_eq_right ω2_three_lt_four.le, qM_s₀new, min_self]
        · rw [hd, vS_of_new ⟨Or.inr ret₂_U_S, fullCell_ne_old s₀X rfl⟩, γ₁_num,
            raiseShifter_of_ge le_rfl (idConst₃_ne_bot 3), idConst_ω2,
            max_eq_right ω2_three_lt_four.le, qM_U_S, min_self]
        · rw [vS_of_proper' hnd hd, ite_eq_left hg.le, raiseShifter_of_lt (v₀_lt_ω2 3), idConst_v₀,
            qM_proper_one hnd hd hg.le, min_eq_left (v₀_le_ω2 4)]
        · rw [vS_of_proper' hnd hd, ite_eq_right (by omega), raiseShifter_of_lt (bot_lt_ofOrd _),
            idConst_bot', qM_proper_two hnd hd hg, min_eq_left bot_le]
      · -- a proper grade-one cell: the constant row
        refine transformsTo_congr rfl rfl ?_ (TransformsTo.refl _)
        funext d
        have hnd : ¬ mute₂ d.1 := hmute_below₂ x d.1 hnm d.2
        have hdP : IsProper d.1 := isProper_of_below hnm hnd d.2 (d.2.2.trans hg.le) hP
        change rowsR.E x d = min (qM d.1) (qM x)
        rw [rowsR_E_of_ne (fun e => not_isProper_of_ret rfl ret₂_ub₁ (e ▸ hP)),
          rows₃_E_one_proper hg d hdP, qM_proper_one hnd hdP (d.2.2.trans hg.le),
          qM_proper_one hnm hP hg.le, min_self]
      · -- a proper grade-two cell: the bottom row
        refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
        funext d
        change ⊥ = min (qM d.1) (qM x)
        rw [qM_proper_two hnm hP hg, min_eq_right bot_le]
  availability := by
    intro Sig Xi₀ hs hg
    have hnmX : ¬ mute₂ Xi₀.1 := not_mute₂_of_low le_rfl Xi₀
    have hnmS : ¬ mute₂ Sig.1 := not_mute₂_of_low le_rfl Sig
    by_cases hg3 : D₂.grade Xi₀.1 = 3
    · rcases three_cases hnmX hg3 with h | h | h | h | h | h
      · -- the old cap `a₁`: dominate by the old cap `a₂`, same graded index
        refine ⟨⟨a₂old, mema₂old₃⟩, by rw [h, cell_a₂old, cell_a₁old], ?_⟩
        change qM Sig.1 ≤ qM a₂old
        rw [qM_a₂old]
        rw [h] at hs hg
        rcases three_cases hnmS (hg.trans grade_a₁old) with h' | h' | h' | h' | h' | h'
        · rw [h', qM_a₁old]; exact η₁_le_γ₀
        · rw [h', qM_a₂old]
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_b₁new)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_A₁c)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_A₂c)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_ub₁)
      · refine ⟨Xi₀, rfl, ?_⟩
        rw [h, qM_a₂old]
        rw [h] at hs hg
        rcases three_cases hnmS (hg.trans grade_a₂old) with h' | h' | h' | h' | h' | h'
        · rw [h', qM_a₁old]; exact η₁_le_γ₀
        · rw [h', qM_a₂old]
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_b₁new)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_A₁c)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_A₂c)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_ub₁)
      · refine ⟨Xi₀, rfl, ?_⟩; rw [h, qM_b₁new]
        exact qM_le_ω2_four _
      · refine ⟨⟨ub₁, memub₁₃⟩, by rw [h, cell_ub₁, cell_A₁c], ?_⟩
        change qM Sig.1 ≤ qM ub₁; rw [qM_ub₁]; exact qM_le_ω2_four _
      · refine ⟨⟨ub₁, memub₁₃⟩, by rw [h, cell_ub₁, cell_A₂c], ?_⟩
        change qM Sig.1 ≤ qM ub₁; rw [qM_ub₁]; exact qM_le_ω2_four _
      · refine ⟨Xi₀, rfl, ?_⟩; rw [h, qM_ub₁]
        exact qM_le_ω2_four _
    · have hg2 : D₂.grade Xi₀.1 ≤ 2 := by
        have := Xi₀.2.2; change D₂.grade Xi₀.1 ≤ 3 at this; omega
      refine ⟨Xi₀, rfl, ?_⟩
      rcases two_cases hnmX hg2 with h | h | h | h | h | h | ⟨h, hgX⟩ | ⟨h, hgX⟩
      · -- the old occurrence: only itself and proper cells lie below
        rw [h, qM_H₀old]
        rw [h] at hs hg
        rw [grade_H₀old] at hg
        rcases two_cases hnmS (by omega) with h' | h' | h' | h' | h' | h' | ⟨h', -⟩ | ⟨-, h'⟩
        · rw [h', qM_H₀old]
        · exact absurd (hs (h' ▸ three_mem_scope_H₀new)) three_not_mem_scope_H₀old'
        · exact absurd (hs (h' ▸ three_mem_scope_U_H)) three_not_mem_scope_H₀old'
        · rw [h', grade_s₀old] at hg; omega
        · rw [h', grade_s₀new] at hg; omega
        · rw [h', grade_U_S] at hg; omega
        · exact (qM_proper_le hnmS h').trans (v₀_le_ω2 3)
        · omega
      · rw [h, qM_H₀new]; exact qM_le_ω2_four _
      · rw [h, qM_U_H]; exact qM_le_ω2_four _
      · rw [h, qM_s₀old]
        rw [h] at hs hg
        rw [grade_s₀old] at hg
        rcases two_cases hnmS (by omega) with h' | h' | h' | h' | h' | h' | ⟨-, h'⟩ | ⟨h', -⟩
        · rw [h', grade_H₀old] at hg; omega
        · rw [h', grade_H₀new] at hg; omega
        · rw [h', grade_U_H] at hg; omega
        · rw [h', qM_s₀old]
        · exact absurd (hs (h' ▸ three_mem_scope_s₀new)) three_not_mem_scope_s₀old
        · exact absurd (hs (h' ▸ three_mem_scope_U_S)) three_not_mem_scope_s₀old
        · omega
        · exact (qM_proper_le hnmS h').trans (v₀_le_ω2 3)
      · rw [h, qM_s₀new]; exact qM_le_ω2_four _
      · rw [h, qM_U_S]; exact qM_le_ω2_four _
      · -- a proper grade-one cell dominates only proper cells
        rw [qM_proper_one hnmX h hgX.le]
        have hS : IsProper Sig.1 :=
          isProper_of_below hnmX hnmS ⟨hs, by change D₂.grade Sig.1 ≤ D₂.grade Xi₀.1; rw [hg]⟩
            (by rw [hg, hgX]) h
        exact qM_proper_le hnmS hS
      · -- a proper grade-two cell dominates only proper grade-two cells
        rw [qM_proper_two hnmX h hgX]
        rw [hgX] at hg
        rcases two_cases hnmS (by omega) with h' | h' | h' | h' | h' | h' | ⟨-, h'⟩ | ⟨h', -⟩
        · rw [h', grade_H₀old] at hg; omega
        · rw [h', grade_H₀new] at hg; omega
        · rw [h', grade_U_H] at hg; omega
        · exfalso; rw [h', scope_s₀old] at hs; exact not_isProper_of_A_sub hnmX hs h
        · exfalso; rw [h', scope_s₀new] at hs; exact not_isProper_of_B_sub hnmX hs h
        · exfalso
          have : ({0, 1, 2} : Finset (Fin 4)) ⊆ D₂.scope Xi₀.1 := fun i _ => hs (by
            rw [h']; change i ∈ (D₂.cell U_S).1; rw [cell_U_S]; exact Finset.mem_univ _)
          exact not_isProper_of_A_sub hnmX this h
        · omega
        · rw [qM_proper_two hnmS h' hg]

/-- **Consistency at `b₁`'s controller.** -/
theorem consistentR_ub₁ : RespectsSemanticsBelow rowsR (D₂.cell ub₁) (rowsR.E ub₁) := by
  rw [show rowsR.E ub₁ = fun d => qM d.1 from funext rowsR_E_ub₁]
  exact respects_of_cell_eq cell_ub₁.symm qM_respects

/-- **The repaired semantics is consistent.** -/
theorem rowsR_consistent : rowsR.IsConsistent := by
  intro Sig
  by_cases h : GradedLe (D₂.cell ub₁) (D₂.cell Sig)
  · rcases ub₁_below_cases h with rfl | rfl | rfl | hm
    · exact consistentR_A₁c
    · exact consistentR_A₂c
    · exact consistentR_ub₁
    · exact consistentR_mute hm
  · exact consistentR_of_not_above h

end RespectR

/-! ## Acceptance 3: the two displays -/

section Displays

theorem eq_ret_of_symm {d : Cell D₂} {x : family₂.X} (h : family₂.e.symm (ret₂ d) = x) :
    ret₂ d = family₂.e x := by rw [← h, Equiv.apply_symm_apply]

theorem qL_le_γ₀_of_other {d : Cell D₂} (hd : ¬ mute₂ d)
    (h2 : ¬ (ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X ∨ ret₂ d = family₂.e b₁X)) :
    qL d ≤ γ₀ := by
  rcases hw : family₂.e.symm (ret₂ d) with c | H | s | a
  · rw [qL_of_proper hd hw]; exact (t₀_F_le_η₁ c).trans η₁_le_γ₀
  · exact absurd (Or.inl (eq_ret_of_symm (hw.trans (eq_H₀X H)))) h2
  · exact absurd (Or.inr (Or.inl (eq_ret_of_symm (hw.trans (eq_s₀X s))))) h2
  · have hne : ¬ (d = H₀old ∨ d = s₀old) := by
      rintro (e | e)
      · exact h2 (Or.inl (by rw [e]; exact ret₂_H₀old))
      · exact h2 (Or.inr (Or.inl (by rw [e]; exact ret₂_s₀old)))
    rw [qL_of_ne hne, labelQ_eq_pull, pull_of_not_mute _ hd, hw]
    rcases a_cases a with ha | ha | ha
    · rw [ha, rowX_b₁_a₁]; exact η₁_le_γ₀
    · rw [ha, rowX_b₁_a₂]
    · exact absurd (Or.inr (Or.inr (eq_ret_of_symm (hw.trans ha)))) h2

/-- **The prescribed labelling's locality at the repaired row**: the clamp at `ω·2+4` with
constants `ω+4`, `ω·2+3` lowers the old witnesses' new source to `ω+4` and the separated cells'
to `ω·2+3`. -/
theorem qL_locality_ub₁R (hx : GradedLe (D₂.cell ub₁) (Finset.univ, 3)) :
    TransformsTo (fun d : D₂.below (D₂.cell ub₁) => D₂.grade d.1) (rowsR.E ub₁)
      (fun d => min (qL (CellScheme.below.incl ⟨ub₁, hx⟩ d).1) (qL ub₁)) := by
  refine (Witness.clamp 3 (ξ := ω2 4) (by rw [fp_ω2]; omega) (c := γ₀) (c' := γ₁) γ₀_vis γ₁_vis
    γ₀_le_γ₁ (ofOrd_ne_bot _) (ofOrd_ne_bot _)).transformsTo fun d => ?_
  rw [gTop_of_le (K := 3) (k := D₂.grade d.1) (grade_le_below_ub₁ d), min_eq_left le_top,
    rowsR_E_ub₁]
  change min (qL d.1) (qL ub₁) = _
  rw [qL_ub₁, min_eq_left (qL_le_γ₁ _)]
  have hnd := not_mute_below_ub₁ d
  by_cases h1 : d.1 = H₀old ∨ d.1 = s₀old
  · rw [qM_of_old h1, clampShifter_of_lt ω2_three_lt_four, min_eq_right (γ₀_lt_ω2 3).le,
      qL_of_eq h1]
  by_cases h2 : ret₂ d.1 = family₂.e H₀X ∨ ret₂ d.1 = family₂.e s₀X ∨ ret₂ d.1 = family₂.e b₁X
  · rw [qM_of_sep h1 h2, clampShifter_of_ge le_rfl]
    rcases h2 with h | h | h
    · exact qL_of_ret_H₀ hnd h (fun e => h1 (Or.inl e))
    · exact qL_of_ret_s₀ hnd h (fun e => h1 (Or.inr e))
    · rw [qL_of_ne h1, labelQ_eq_pull, pull_eq_rowX _ hnd h, rowX_b₁_b₁]
  · rw [qM_of_other h1 h2,
      clampShifter_of_lt ((qL_le_γ₁ _).trans_lt (by rw [γ₁_num]; exact ω2_three_lt_four)),
      min_eq_left (qL_le_γ₀_of_other hnd h2)]

/-- **Display one: the prescribed labelling respects the repaired semantics.** -/
theorem qL_respectsR : RespectsSemanticsBelow rowsR (Finset.univ, 3) (fun d => qL d.1) where
  orderly := qL_respects.orderly
  locality Sig := by
    by_cases h : Sig.1 = ub₁
    · have e : Sig = ⟨ub₁, by rw [← h]; exact Sig.2⟩ := Subtype.ext h
      rw [e]; exact qL_locality_ub₁R _
    · rw [rowsR_E_of_ne h]; exact qL_respects.locality Sig
  availability := qL_respects.availability

/-! ### Display two: the bottom face extends -/

/-- **The extension of the bottom face**: `3` where the repaired row is in the block at `ω·2`
(the old witnesses and the six separated cells), `⊥` elsewhere. -/
noncomputable def bottomFull (d : D₂.below (Finset.univ, 3)) : ExtOrd :=
  stepShifter 2 ⊥ (ofOrd 3) (qM d.1)

theorem three_vis (K : ℕ) (hK : K ≤ 3) : SelfVis K (ofOrd 3) := by
  rw [selfVis_ofOrd_iff, show (3 : Ordinal) = ((3 : ℕ) : Ordinal) from rfl,
    Value.finitePart_natCast]
  exact hK

theorem stepShifter_le_three (a : ExtOrd) : stepShifter 2 ⊥ (ofOrd 3) a ≤ ofOrd 3 := by
  by_cases ha : a = ⊥
  · rw [ha, stepShifter_bot]; exact bot_le
  by_cases hal : a < ofOrd (Ordinal.omega0 * ((2 : ℕ) : Ordinal))
  · rw [stepShifter_of_lt ha hal]; exact bot_le
  · rw [stepShifter_of_ge (not_lt.mp hal)]
theorem stepShifter_cases (a : ExtOrd) :
    stepShifter 2 ⊥ (ofOrd 3) a = ⊥ ∨ stepShifter 2 ⊥ (ofOrd 3) a = ofOrd 3 := by
  by_cases ha : a = ⊥
  · left; rw [ha, stepShifter_bot]
  by_cases hal : a < ofOrd (Ordinal.omega0 * ((2 : ℕ) : Ordinal))
  · left; rw [stepShifter_of_lt ha hal]
  · right; rw [stepShifter_of_ge (not_lt.mp hal)]
theorem stepShifter_of_le_γ₀ {a : ExtOrd} (h : a ≤ γ₀) : stepShifter 2 ⊥ (ofOrd 3) a = ⊥ := by
  by_cases ha : a = ⊥
  · rw [ha, stepShifter_bot]
  · exact stepShifter_of_lt ha (h.trans_lt (by rw [ω2_zero']; exact γ₀_lt_ω2 0))

theorem bottomFull_le_three (d : D₂.below (Finset.univ, 3)) : bottomFull d ≤ ofOrd 3 :=
  stepShifter_le_three _
theorem bottomFull_of_low {d : D₂.below (Finset.univ, 3)} (h : qM d.1 ≤ γ₀) :
    bottomFull d = ⊥ := stepShifter_of_le_γ₀ h
theorem bottomFull_of_high {d : D₂.below (Finset.univ, 3)}
    (h : ofOrd (Ordinal.omega0 * ((2 : ℕ) : Ordinal)) ≤ qM d.1) : bottomFull d = ofOrd 3 :=
  stepShifter_of_ge h

theorem h₂₃ : GradedLe ((Finset.univ : Finset (Fin 4)), 2) (Finset.univ, 3) :=
  ⟨Finset.Subset.refl _, by decide⟩

theorem bottomFull_legal : Legal₂ ⊥ (ofOrd 3) (ofOrd 3) (ofOrd 3) :=
  ⟨selfVis_bot 1, bot_le, le_rfl, fun h => absurd h (ofOrd_ne_bot _), three_vis 1 (by decide),
    three_vis 1 (by decide), three_vis 2 (by decide), le_rfl,
    by rw [min_self]; exact three_vis 2 (by decide)⟩

theorem bottomFull_shape :
    Shape₂ (fun d => bottomFull (CellScheme.below.mono h₂₃ d)) ⊥ (ofOrd 3) (ofOrd 3) (ofOrd 3) where
  at_H₀old := bottomFull_of_high (d := CellScheme.below.mono h₂₃ ⟨H₀old, memH₀old₂⟩)
    (by change _ ≤ qM H₀old; rw [qM_H₀old]; exact ω2_ge 3)
  at_H₀new := bottomFull_of_high (d := CellScheme.below.mono h₂₃ ⟨H₀new, memH₀new₂⟩)
    (by change _ ≤ qM H₀new; rw [qM_H₀new]; exact ω2_ge 4)
  at_U_H := bottomFull_of_high (d := CellScheme.below.mono h₂₃ ⟨U_H, memU_H₂⟩)
    (by change _ ≤ qM U_H; rw [qM_U_H]; exact ω2_ge 4)
  at_s₀old := by
    rw [min_self]
    exact bottomFull_of_high (d := CellScheme.below.mono h₂₃ ⟨s₀old, mems₀old₂⟩)
      (by change _ ≤ qM s₀old; rw [qM_s₀old]; exact ω2_ge 3)
  at_s₀new := bottomFull_of_high (d := CellScheme.below.mono h₂₃ ⟨s₀new, mems₀new₂⟩)
    (by change _ ≤ qM s₀new; rw [qM_s₀new]; exact ω2_ge 4)
  at_U_S := bottomFull_of_high (d := CellScheme.below.mono h₂₃ ⟨U_S, memU₂⟩)
    (by change _ ≤ qM U_S; rw [qM_U_S]; exact ω2_ge 4)
  at_proper d hd := by
    have h0 : bottomFull (CellScheme.below.mono h₂₃ d) = ⊥ :=
      bottomFull_of_low ((qM_proper_le (not_mute_of_two d) hd).trans v₀_le_γ₀)
    rw [h0]; split_ifs <;> rfl

theorem bottomFull_respects₂ : RespectsSemanticsBelow rows₃ (Finset.univ, 2)
    (fun d => bottomFull (CellScheme.below.mono h₂₃ d)) :=
  respects_of_shape₂ bottomFull_legal bottomFull_shape

/-- **The extension restricts to the bottom face.** -/
theorem bottomFull_eq_bottomFace (d : D₂.below (({1, 2, 3} : Finset (Fin 4)), 3)) :
    bottomFull ⟨d.1, d.2.trans ⟨Finset.subset_univ _, le_rfl⟩⟩ = bottomFace d := by
  have hr := ret₂_eq_emb₁_retB zero_not_mem_B d
  have hnd : ¬ mute₂ d.1 :=
    not_mute₂_of_low (by decide) ⟨d.1, d.2.trans ⟨Finset.subset_univ _, le_rfl⟩⟩
  change stepShifter 2 ⊥ (ofOrd 3) (qM d.1) = bottomFaceX (family₁.e.symm (retB d.1))
  rcases img_cases (family₁.e.symm (retB d.1)) with ⟨c, hc⟩ | hc | hc | hc
  · have hp : family₂.e.symm (ret₂ d.1) = .inl c := by
      rw [hr]
      change family₂.e.symm (family₂.e (embX₁ (family₁.e.symm (retB d.1)))) = _
      rw [Equiv.symm_apply_apply, hc]; rfl
    rw [hc, stepShifter_of_le_γ₀ ((qM_proper_le hnd ⟨c, hp⟩).trans v₀_le_γ₀)]; rfl
  · have h1 : retB d.1 = family₁.e H₀X₁ := by rw [← hc, Equiv.apply_symm_apply]
    have := retB_inj zero_not_mem_B d ⟨H₀new, copyB_mem _⟩ (h1.trans (retB_copyB _).symm)
    rw [hc, congrArg Subtype.val this, qM_H₀new, stepShifter_of_ge (ω2_ge 4)]; rfl
  · have h1 : retB d.1 = family₁.e s₀X₁ := by rw [← hc, Equiv.apply_symm_apply]
    have := retB_inj zero_not_mem_B d ⟨s₀new, copyB_mem _⟩ (h1.trans (retB_copyB _).symm)
    rw [hc, congrArg Subtype.val this, qM_s₀new, stepShifter_of_ge (ω2_ge 4)]; rfl
  · have h1 : retB d.1 = family₁.e b₁X₁ := by rw [← hc, Equiv.apply_symm_apply]
    have := retB_inj zero_not_mem_B d ⟨b₁new, copyB_mem _⟩ (h1.trans (retB_copyB _).symm)
    rw [hc, congrArg Subtype.val this, qM_b₁new, stepShifter_of_ge (ω2_ge 4)]; rfl

theorem bottomFull_A₁c (h : GradedLe (D₂.cell A₁c) (Finset.univ, 3)) : bottomFull ⟨A₁c, h⟩ = ⊥ :=
  bottomFull_of_low (by change qM A₁c ≤ γ₀; rw [qM_A₁c]; exact η₁_le_γ₀)
theorem bottomFull_A₂c (h : GradedLe (D₂.cell A₂c) (Finset.univ, 3)) : bottomFull ⟨A₂c, h⟩ = ⊥ :=
  bottomFull_of_low (by change qM A₂c ≤ γ₀; rw [qM_A₂c])
theorem bottomFull_a₁old (h : GradedLe (D₂.cell a₁old) (Finset.univ, 3)) :
    bottomFull ⟨a₁old, h⟩ = ⊥ :=
  bottomFull_of_low (by change qM a₁old ≤ γ₀; rw [qM_a₁old]; exact η₁_le_γ₀)
theorem bottomFull_a₂old (h : GradedLe (D₂.cell a₂old) (Finset.univ, 3)) :
    bottomFull ⟨a₂old, h⟩ = ⊥ :=
  bottomFull_of_low (by change qM a₂old ≤ γ₀; rw [qM_a₂old])
theorem bottomFull_b₁new (h : GradedLe (D₂.cell b₁new) (Finset.univ, 3)) :
    bottomFull ⟨b₁new, h⟩ = ofOrd 3 :=
  bottomFull_of_high (by change _ ≤ qM b₁new; rw [qM_b₁new]; exact ω2_ge 4)
theorem bottomFull_ub₁ (h : GradedLe (D₂.cell ub₁) (Finset.univ, 3)) :
    bottomFull ⟨ub₁, h⟩ = ofOrd 3 :=
  bottomFull_of_high (by change _ ≤ qM ub₁; rw [qM_ub₁]; exact ω2_ge 4)

/-- **Display two: the bottom face's extension respects the repaired semantics.** -/
theorem bottomFull_respects : RespectsSemanticsBelow rowsR (Finset.univ, 3) bottomFull where
  orderly d := by
    change bottomFull d = extVisibilityReplace (bottomFull d) (D₂.grade d.1) (D₂.grade d.1)
    rcases stepShifter_cases (qM d.1) with h | h
    · rw [show bottomFull d = ⊥ from h]; exact (selfVis_bot _).symm
    · rw [show bottomFull d = ofOrd 3 from h]
      exact (three_vis _ (by have := d.2.2; change D₂.grade d.1 ≤ 3 at this; exact this)).symm
  locality := by
    intro Sig
    obtain ⟨x, hx⟩ := Sig
    have hnm : ¬ mute₂ x := not_mute₂_of_low le_rfl ⟨x, hx⟩
    by_cases hg3 : D₂.grade x = 3
    · rcases three_cases hnm hg3 with rfl | rfl | rfl | rfl | rfl | rfl
      · refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
        funext d
        rw [bottomFull_a₁old hx, min_eq_right bot_le]
      · refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
        funext d
        rw [bottomFull_a₂old hx, min_eq_right bot_le]
      · -- the copy of `b₁`: the face's own locality
        refine transformsTo_congr rfl (rowsR_E_of_ne b₁new_ne_ub₁).symm ?_
          (bottomFace_respects.locality ⟨b₁new, copyB_mem _⟩)
        funext d
        rw [← bottomFull_eq_bottomFace (CellScheme.below.incl ⟨b₁new, copyB_mem _⟩ d),
          ← bottomFull_eq_bottomFace ⟨b₁new, copyB_mem _⟩]
        rfl
      · refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
        funext d
        rw [bottomFull_A₁c hx, min_eq_right bot_le]
      · refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
        funext d
        rw [bottomFull_A₂c hx, min_eq_right bot_le]
      · -- `b₁`'s controller: the limit step at `ω·2`, by definition of the extension
        refine (Witness.stepLimit 3 2 bot_le (selfVis_bot 3) (three_vis 3 le_rfl)).transformsTo
          fun d => ?_
        rw [gTop_of_le (K := 3) (k := D₂.grade d.1) (grade_le_below_ub₁ d), min_eq_left le_top,
          rowsR_E_ub₁]
        change min (stepShifter 2 ⊥ (ofOrd 3) (qM d.1)) (stepShifter 2 ⊥ (ofOrd 3) (qM ub₁)) = _
        rw [qM_ub₁, stepShifter_of_ge (ω2_ge 4)]
        exact min_eq_left (stepShifter_le_three _)
    · -- grade at most two: the grade-two sufficiency lemma
      have hg2 : D₂.grade x ≤ 2 := by have := hx.2; change D₂.grade x ≤ 3 at this; omega
      have hne : x ≠ ub₁ := fun e => hg3 (by rw [e]; exact grade_ub₁)
      have hx₂ : GradedLe (D₂.cell x) (Finset.univ, 2) := ⟨Finset.subset_univ _, hg2⟩
      refine transformsTo_congr rfl (rowsR_E_of_ne hne).symm ?_
        (bottomFull_respects₂.locality ⟨x, hx₂⟩)
      funext d
      rw [show CellScheme.below.mono h₂₃ (CellScheme.below.incl ⟨x, hx₂⟩ d) =
          CellScheme.below.incl ⟨x, hx⟩ d from Subtype.ext rfl,
        show CellScheme.below.mono h₂₃ ⟨x, hx₂⟩ = ⟨x, hx⟩ from Subtype.ext rfl]
  availability := by
    intro Sig Xi₀ hs hg
    have hnmX : ¬ mute₂ Xi₀.1 := not_mute₂_of_low le_rfl Xi₀
    have hnmS : ¬ mute₂ Sig.1 := not_mute₂_of_low le_rfl Sig
    by_cases hg3 : D₂.grade Xi₀.1 = 3
    · rcases three_cases hnmX hg3 with h | h | h | h | h | h
      · refine ⟨Xi₀, rfl, ?_⟩
        rw [show Xi₀ = ⟨a₁old, mema₁old₃⟩ from Subtype.ext h, bottomFull_a₁old _]
        rw [h] at hs hg
        rcases three_cases hnmS (hg.trans grade_a₁old) with h' | h' | h' | h' | h' | h'
        · rw [show Sig = ⟨a₁old, mema₁old₃⟩ from Subtype.ext h', bottomFull_a₁old _]
        · rw [show Sig = ⟨a₂old, mema₂old₃⟩ from Subtype.ext h', bottomFull_a₂old _]
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_b₁new)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_A₁c)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_A₂c)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_ub₁)
      · refine ⟨Xi₀, rfl, ?_⟩
        rw [show Xi₀ = ⟨a₂old, mema₂old₃⟩ from Subtype.ext h, bottomFull_a₂old _]
        rw [h] at hs hg
        rcases three_cases hnmS (hg.trans grade_a₂old) with h' | h' | h' | h' | h' | h'
        · rw [show Sig = ⟨a₁old, mema₁old₃⟩ from Subtype.ext h', bottomFull_a₁old _]
        · rw [show Sig = ⟨a₂old, mema₂old₃⟩ from Subtype.ext h', bottomFull_a₂old _]
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_b₁new)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_A₁c)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_A₂c)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_ub₁)
      · refine ⟨Xi₀, rfl, ?_⟩
        rw [show Xi₀ = ⟨b₁new, memb₁new₃⟩ from Subtype.ext h, bottomFull_b₁new _]
        exact bottomFull_le_three _
      · refine ⟨⟨ub₁, memub₁₃⟩, by rw [h, cell_ub₁, cell_A₁c], ?_⟩
        rw [bottomFull_ub₁ _]; exact bottomFull_le_three _
      · refine ⟨⟨ub₁, memub₁₃⟩, by rw [h, cell_ub₁, cell_A₂c], ?_⟩
        rw [bottomFull_ub₁ _]; exact bottomFull_le_three _
      · refine ⟨Xi₀, rfl, ?_⟩
        rw [show Xi₀ = ⟨ub₁, memub₁₃⟩ from Subtype.ext h, bottomFull_ub₁ _]
        exact bottomFull_le_three _
    · have hg2 : D₂.grade Xi₀.1 ≤ 2 := by
        have := Xi₀.2.2; change D₂.grade Xi₀.1 ≤ 3 at this; omega
      have hS2 : D₂.grade Sig.1 ≤ 2 := hg ▸ hg2
      obtain ⟨Xi, hc, hle⟩ := bottomFull_respects₂.availability
        ⟨Sig.1, ⟨Finset.subset_univ _, hS2⟩⟩ ⟨Xi₀.1, ⟨Finset.subset_univ _, hg2⟩⟩ hs hg
      refine ⟨CellScheme.below.mono h₂₃ Xi, hc, ?_⟩
      rw [show CellScheme.below.mono h₂₃ ⟨Sig.1, ⟨Finset.subset_univ _, hS2⟩⟩ = Sig from
        Subtype.ext rfl] at hle
      exact hle

/-- **The bottom face extends to a labelling respecting the repaired semantics** — the input of
the no-go against the frozen rows. -/
theorem bottomFace_extendsR : ∃ q : D₂.below (Finset.univ, 3) → ExtOrd,
    RespectsSemanticsBelow rowsR (Finset.univ, 3) q ∧
    ∀ d : D₂.below (({1, 2, 3} : Finset (Fin 4)), 3),
      q ⟨d.1, d.2.trans ⟨Finset.subset_univ _, le_rfl⟩⟩ = bottomFace d :=
  ⟨bottomFull, bottomFull_respects, bottomFull_eq_bottomFace⟩

end Displays

/-! ## The transfers: grades one and two are frozen -/

section Transfer

theorem respectsR_iff_of_proper {BJ : Finset (Fin 4) × ℕ} (hB : BJ.1 ≠ Finset.univ)
    (r : D₂.below BJ → ExtOrd) :
    RespectsSemanticsBelow rowsR BJ r ↔ RespectsSemanticsBelow rows₂ BJ r :=
  ⟨fun h => h.congr_sem fun Sig => (rowsR_E_of_proper_scope (scope_ne_univ_of_below hB Sig)).symm,
   fun h => h.congr_sem fun Sig => rowsR_E_of_proper_scope (scope_ne_univ_of_below hB Sig)⟩

theorem ne_ub₁_of_low {j : ℕ} (hj : j ≤ 2) (Sig : D₂.below (Finset.univ, j)) : Sig.1 ≠ ub₁ :=
  fun e => by
    have := Sig.2.2
    rw [e] at this
    change D₂.grade ub₁ ≤ j at this
    rw [grade_ub₁] at this
    omega

/-- **Below grade three the repaired semantics is the frozen one.** -/
theorem respectsR_iff_low {j : ℕ} (hj : j ≤ 2) (r : D₂.below (Finset.univ, j) → ExtOrd) :
    RespectsSemanticsBelow rowsR (Finset.univ, j) r ↔
      RespectsSemanticsBelow rows₃ (Finset.univ, j) r :=
  ⟨fun h => h.congr_sem fun Sig => (rowsR_E_of_ne (ne_ub₁_of_low hj Sig)).symm,
   fun h => h.congr_sem fun Sig => rowsR_E_of_ne (ne_ub₁_of_low hj Sig)⟩

/-- **The scope-changing obligation** for the repaired semantics, at grades at most three. -/
def ProperToFullRLow : Prop :=
  ∀ (CI : Finset (Fin 4) × ℕ) (j : ℕ), j ≤ 3 → CI ∈ Plan.gradedPlan plan₄ →
    CI.1 ≠ Finset.univ → (Finset.univ, j) ∈ Plan.gradedPlan plan₄ →
    (h : GradedLe CI (Finset.univ, j)) →
    ∀ (p : D₂.below CI → ExtOrd) (q : D₂.below (Finset.univ, j) → ExtOrd) (γ : ExtOrd),
      RespectsSemanticsBelow rowsR CI p → RespectsSemanticsBelow rowsR (Finset.univ, j) q →
      extVisibilityReplace γ j j = γ →
      (∀ d : D₂.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) →
      ∃ q' : D₂.below (Finset.univ, j) → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, j) q' ∧
        (∀ d, min (q' d) γ = min (q d) γ) ∧
        (∀ d : D₂.below CI, q' (CellScheme.below.mono h d) = p d)

/-- **Bountifulness of the repaired semantics, reduced to the scope-changing obligation.** -/
theorem rowsR_isBountiful_of (H : ProperToFullRLow) : rowsR.IsBountiful := by
  intro CI BJ hCI hBJ h hne p q γ hp hq hγ hagree
  by_cases hB : BJ.1 = Finset.univ
  · by_cases hC : CI.1 = Finset.univ
    · obtain ⟨B, j⟩ := BJ
      obtain ⟨C, i⟩ := CI
      dsimp only at hB hC
      subst hB hC
      exact bountiful_full_scope rowsR h p q γ hp hq hγ hagree
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
        obtain ⟨q', hq', hq'γ, hq'ext⟩ := bountiful_full_scope rowsR h₃ q₃ q γ hq₃ hq hγ
          (fun d => (hq₃γ d).symm)
        refine ⟨q', hq', hq'γ, fun d => ?_⟩
        have e : CellScheme.below.mono h d =
            CellScheme.below.mono h₃ (CellScheme.below.mono hC3 d) := rfl
        rw [e, hq'ext, hq₃ext]
  · have hC : CI.1 ≠ Finset.univ := fun e => hB (Finset.univ_subset_iff.mp (e ▸ h.1))
    rw [respectsR_iff_of_proper hC] at hp
    rw [respectsR_iff_of_proper hB] at hq
    have hBp : BJ.1 ∈ plan₄ := (Plan.mem_gradedPlan.mp hBJ).1
    rcases proper_side BJ.1 hBp hB with h3 | h0
    · obtain ⟨q', hq', hq'γ, hq'ext⟩ := bountiful₂_A CI BJ hCI hBJ h h3 p q γ hp hq hγ hagree
      exact ⟨q', (respectsR_iff_of_proper hB q').mpr hq', hq'γ, hq'ext⟩
    · obtain ⟨q', hq', hq'γ, hq'ext⟩ := bountiful₂_B CI BJ hCI hBJ h h0 p q γ hp hq hγ hagree
      exact ⟨q', (respectsR_iff_of_proper hB q').mpr hq', hq'γ, hq'ext⟩

/-- **The grade-one and grade-two endpoints transfer**: the obligation at every target grade
`j ≤ 2` holds for the repaired semantics. -/
theorem properToFullR_of_le_two (CI : Finset (Fin 4) × ℕ) (j : ℕ) (hj : j ≤ 2)
    (hCI : CI ∈ Plan.gradedPlan plan₄) (hC : CI.1 ≠ Finset.univ)
    (hU : (Finset.univ, j) ∈ Plan.gradedPlan plan₄) (h : GradedLe CI (Finset.univ, j))
    (p : D₂.below CI → ExtOrd) (q : D₂.below (Finset.univ, j) → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow rowsR CI p) (hq : RespectsSemanticsBelow rowsR (Finset.univ, j) q)
    (hγ : extVisibilityReplace γ j j = γ)
    (hagree : ∀ d : D₂.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D₂.below (Finset.univ, j) → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, j) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D₂.below CI, q' (CellScheme.below.mono h d) = p d) := by
  have hp₃ : RespectsSemanticsBelow rows₃ CI p :=
    (respects₃_iff_of_proper hC p).mpr ((respectsR_iff_of_proper hC p).mp hp)
  have hq₃ : RespectsSemanticsBelow rows₃ (Finset.univ, j) q := (respectsR_iff_low hj q).mp hq
  obtain ⟨q', hq', h1, h2⟩ := properToFull₃_of_le_two CI j hj hCI hC hU h p q γ hp₃ hq₃ hγ hagree
  exact ⟨q', (respectsR_iff_low hj q').mpr hq', h1, h2⟩

/-- The B-face input of the no-go respects the repaired semantics on the B face. -/
theorem bottomFace_respectsR :
    RespectsSemanticsBelow rowsR (({1, 2, 3} : Finset (Fin 4)), 3) bottomFace :=
  (respectsR_iff_of_proper (by decide) bottomFace).mpr
    ((respects₃_iff_of_proper (by decide) bottomFace).mp bottomFace_respects)

end Transfer

/-! ## Acceptance 4: the grade-three constraints, re-extracted -/

section ConstraintsR

theorem a₁old_below_ub₁ : GradedLe (D₂.cell a₁old) (D₂.cell ub₁) := by
  rw [cell_ub₁]; exact mema₁old₃
theorem A₁c_below_ub₁ : GradedLe (D₂.cell A₁c) (D₂.cell ub₁) := by
  rw [cell_ub₁]; exact memA₁c₃

theorem rowsR_ub₁_H₀old : rowsR.E ub₁ ⟨H₀old, H₀old_below_ub₁⟩ = ofOrd (ω2 3) :=
  (rowsR_E_ub₁ _).trans qM_H₀old
theorem rowsR_ub₁_U_S : rowsR.E ub₁ ⟨U_S, U_S_below_ub₁⟩ = ofOrd (ω2 4) :=
  (rowsR_E_ub₁ _).trans qM_U_S
theorem rowsR_ub₁_a₂old : rowsR.E ub₁ ⟨a₂old, a₂old_below_ub₁⟩ = γ₀ :=
  (rowsR_E_ub₁ _).trans qM_a₂old
theorem rowsR_ub₁_A₂c : rowsR.E ub₁ ⟨A₂c, A₂c_below_ub₁⟩ = γ₀ := (rowsR_E_ub₁ _).trans qM_A₂c
theorem rowsR_ub₁_b₁new : rowsR.E ub₁ ⟨b₁new, b₁new_below_ub₁⟩ = ofOrd (ω2 4) :=
  (rowsR_E_ub₁ _).trans qM_b₁new
theorem rowsR_ub₁_self : rowsR.E ub₁ ⟨ub₁, refl_ub₁⟩ = ofOrd (ω2 4) :=
  (rowsR_E_ub₁ _).trans qM_ub₁
theorem rowsR_ub₁_a₁old : rowsR.E ub₁ ⟨a₁old, a₁old_below_ub₁⟩ = η₁ :=
  (rowsR_E_ub₁ _).trans qM_a₁old
theorem rowsR_ub₁_A₁c : rowsR.E ub₁ ⟨A₁c, A₁c_below_ub₁⟩ = η₁ := (rowsR_E_ub₁ _).trans qM_A₁c
theorem rowsR_E_A₁c (d : D₂.below (D₂.cell A₁c)) : rowsR.E A₁c d = rows₃.E A₁c d :=
  congrFun (rowsR_E_of_ne A₁c_ne_ub₁) d
theorem rowsR_E_A₂c (d : D₂.below (D₂.cell A₂c)) : rowsR.E A₂c d = rows₃.E A₂c d :=
  congrFun (rowsR_E_of_ne A₂c_ne_ub₁) d
theorem rowsR_E_a₁old (d : D₂.below (D₂.cell a₁old)) : rowsR.E a₁old d = rows₃.E a₁old d :=
  congrFun (rowsR_E_of_ne a₁old_ne_ub₁) d

theorem evr_ω2_three_four : extVisibilityReplace (ofOrd (ω2 3)) 4 4 = ofOrd (ω2 4) := by
  rw [extVisibilityReplace_ofOrd]
  unfold visibilityReplace
  rw [ite_eq_left (by rw [fp_ω2]; omega)]
  unfold ordinalReplace
  rw [limitPart_mul_add]

variable {q : D₂.below (Finset.univ, 3) → ExtOrd}
  (hq : RespectsSemanticsBelow rowsR (Finset.univ, 3) q)
include hq

/-! ### Surviving constraints (rows other than `b₁`'s controller's, or unchanged entries) -/

theorem le_controller_of_respectsR (d : D₂.below (Finset.univ, 3)) (hd : D₂.grade d.1 = 3) :
    q d ≤ q ⟨A₁c, memA₁c₃⟩ ∨ q d ≤ q ⟨A₂c, memA₂c₃⟩ ∨ q d ≤ q ⟨ub₁, memub₁₃⟩ := by
  obtain ⟨Xi, hXi, hle⟩ := hq.availability d ⟨ub₁, memub₁₃⟩ (by
      change D₂.scope d.1 ⊆ (D₂.cell ub₁).1; rw [cell_ub₁]; exact Finset.subset_univ _)
    (by change D₂.grade d.1 = (D₂.cell ub₁).2; rw [cell_ub₁, hd])
  rw [cell_ub₁] at hXi
  rcases eq_three_of_cell hXi with h | h | h
  · left; rw [show Xi = ⟨A₁c, memA₁c₃⟩ from Subtype.ext h] at hle; exact hle
  · right; left; rw [show Xi = ⟨A₂c, memA₂c₃⟩ from Subtype.ext h] at hle; exact hle
  · right; right; rw [show Xi = ⟨ub₁, memub₁₃⟩ from Subtype.ext h] at hle; exact hle

theorem A₁c_le_A₂c_of_respectsR : q ⟨A₁c, memA₁c₃⟩ ≤ q ⟨A₂c, memA₂c₃⟩ := by
  have h := hq.probe_eq_of_row_eq ⟨A₁c, memA₁c₃⟩ ⟨A₂c, A₂c_below_A₁c⟩ ⟨A₁c, refl_A₁c⟩
    ((rowsR_E_A₁c ⟨A₂c, A₂c_below_A₁c⟩).trans (rows₃_A₁c_A₂c.trans
      (rows₃_A₁c_self.symm.trans (rowsR_E_A₁c ⟨A₁c, refl_A₁c⟩).symm)))
    (by rw [grade_A₂c, grade_A₁c])
  have e1 : CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₂c, A₂c_below_A₁c⟩ = ⟨A₂c, memA₂c₃⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₁c, refl_A₁c⟩ = ⟨A₁c, memA₁c₃⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.symm.le.trans (min_le_left _ _)

theorem A₂c_le_ub₁_of_respectsR : q ⟨A₂c, memA₂c₃⟩ ≤ q ⟨ub₁, memub₁₃⟩ := by
  have h := hq.probe_eq_of_row_eq ⟨A₂c, memA₂c₃⟩ ⟨ub₁, ub₁_below_A₂c⟩ ⟨A₂c, refl_A₂c⟩
    ((rowsR_E_A₂c ⟨ub₁, ub₁_below_A₂c⟩).trans (rows₃_A₂c_ub₁.trans
      (rows₃_A₂c_self.symm.trans (rowsR_E_A₂c ⟨A₂c, refl_A₂c⟩).symm)))
    (by rw [grade_ub₁, grade_A₂c])
  have e1 : CellScheme.below.incl ⟨A₂c, memA₂c₃⟩ ⟨ub₁, ub₁_below_A₂c⟩ = ⟨ub₁, memub₁₃⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨A₂c, memA₂c₃⟩ ⟨A₂c, refl_A₂c⟩ = ⟨A₂c, memA₂c₃⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.symm.le.trans (min_le_left _ _)

theorem le_ub₁_of_respectsR (d : D₂.below (Finset.univ, 3)) (hd : D₂.grade d.1 = 3) :
    q d ≤ q ⟨ub₁, memub₁₃⟩ := by
  rcases le_controller_of_respectsR hq d hd with h | h | h
  · exact h.trans ((A₁c_le_A₂c_of_respectsR hq).trans (A₂c_le_ub₁_of_respectsR hq))
  · exact h.trans (A₂c_le_ub₁_of_respectsR hq)
  · exact h

/-- The copy of `b₁` is labelled like its controller (unchanged entries `ω·2+4`). -/
theorem b₁new_eq_ub₁_of_respectsR : q ⟨b₁new, memb₁new₃⟩ = q ⟨ub₁, memub₁₃⟩ := by
  refine le_antisymm (le_ub₁_of_respectsR hq _ grade_b₁new) ?_
  have h := hq.probe_eq_of_row_eq ⟨ub₁, memub₁₃⟩ ⟨b₁new, b₁new_below_ub₁⟩ ⟨ub₁, refl_ub₁⟩
    (rowsR_ub₁_b₁new.trans rowsR_ub₁_self.symm) (by rw [grade_b₁new, grade_ub₁])
  have e1 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨b₁new, b₁new_below_ub₁⟩ =
      ⟨b₁new, memb₁new₃⟩ := Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨ub₁, refl_ub₁⟩ = ⟨ub₁, memub₁₃⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.symm.le.trans (min_le_left _ _)

/-- The old cap `a₂` is labelled like its controller (unchanged entries `ω+4`). -/
theorem a₂old_eq_A₂c_of_respectsR : q ⟨a₂old, mema₂old₃⟩ = q ⟨A₂c, memA₂c₃⟩ := by
  have h := hq.probe_eq_of_row_eq ⟨ub₁, memub₁₃⟩ ⟨a₂old, a₂old_below_ub₁⟩ ⟨A₂c, A₂c_below_ub₁⟩
    (rowsR_ub₁_a₂old.trans rowsR_ub₁_A₂c.symm) (by rw [grade_a₂old, grade_A₂c])
  have e1 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨a₂old, a₂old_below_ub₁⟩ =
      ⟨a₂old, mema₂old₃⟩ := Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨A₂c, A₂c_below_ub₁⟩ = ⟨A₂c, memA₂c₃⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_eq_left (le_ub₁_of_respectsR hq ⟨a₂old, mema₂old₃⟩ grade_a₂old),
    min_eq_left (A₂c_le_ub₁_of_respectsR hq)] at h
  exact h

theorem a₁old_le_a₂old_of_respectsR : q ⟨a₁old, mema₁old₃⟩ ≤ q ⟨a₂old, mema₂old₃⟩ := by
  have h := hq.probe_eq_of_row_eq ⟨a₁old, mema₁old₃⟩ ⟨a₂old, a₂old_below_a₁old⟩
    ⟨a₁old, refl_a₁old⟩
    ((rowsR_E_a₁old ⟨a₂old, a₂old_below_a₁old⟩).trans (rows₃_a₁old_a₂old.trans
      (rows₃_a₁old_self.symm.trans (rowsR_E_a₁old ⟨a₁old, refl_a₁old⟩).symm)))
    (by rw [grade_a₂old, grade_a₁old])
  have e1 : CellScheme.below.incl ⟨a₁old, mema₁old₃⟩ ⟨a₂old, a₂old_below_a₁old⟩ =
      ⟨a₂old, mema₂old₃⟩ := Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨a₁old, mema₁old₃⟩ ⟨a₁old, refl_a₁old⟩ =
      ⟨a₁old, mema₁old₃⟩ := Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.symm.le.trans (min_le_left _ _)

/-- The old cap `a₁` is labelled like its controller (`a₂`'s row, unchanged). -/
theorem a₁old_eq_A₁c_of_respectsR : q ⟨a₁old, mema₁old₃⟩ = q ⟨A₁c, memA₁c₃⟩ := by
  have h := hq.probe_eq_of_row_eq ⟨A₂c, memA₂c₃⟩ ⟨a₁old, a₁old_below_A₂c⟩ ⟨A₁c, A₁c_below_A₂c⟩
    ((rowsR_E_A₂c ⟨a₁old, a₁old_below_A₂c⟩).trans (rows₃_A₂c_a₁old.trans
      (rows₃_A₂c_A₁c.symm.trans (rowsR_E_A₂c ⟨A₁c, A₁c_below_A₂c⟩).symm)))
    (by rw [grade_a₁old, grade_A₁c])
  have e1 : CellScheme.below.incl ⟨A₂c, memA₂c₃⟩ ⟨a₁old, a₁old_below_A₂c⟩ =
      ⟨a₁old, mema₁old₃⟩ := Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨A₂c, memA₂c₃⟩ ⟨A₁c, A₁c_below_A₂c⟩ = ⟨A₁c, memA₁c₃⟩ :=
    Subtype.ext rfl
  have hle : q ⟨a₁old, mema₁old₃⟩ ≤ q ⟨A₂c, memA₂c₃⟩ :=
    (a₁old_le_a₂old_of_respectsR hq).trans (a₂old_eq_A₂c_of_respectsR hq).le
  rw [e1, e2, min_eq_left hle, min_eq_left (A₁c_le_A₂c_of_respectsR hq)] at h
  exact h

/-- `b₁`'s controller is below the grade-two controller (unchanged entries `ω·2+4`). -/
theorem ub₁_le_U_S_of_respectsR : q ⟨ub₁, memub₁₃⟩ ≤ q ⟨U_S, memU_S₃⟩ := by
  have h := hq.probe_ge_of_row_eq ⟨ub₁, memub₁₃⟩ ⟨U_S, U_S_below_ub₁⟩ ⟨ub₁, refl_ub₁⟩
    (rowsR_ub₁_U_S.trans rowsR_ub₁_self.symm) (by rw [grade_U_S, grade_ub₁]; decide)
  have e1 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨U_S, U_S_below_ub₁⟩ = ⟨U_S, memU_S₃⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨ub₁, refl_ub₁⟩ = ⟨ub₁, memub₁₃⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.trans (min_le_left _ _)

/-- The clause-5 coupling `z₁ = ⊥ → z₂ = ⊥` (`a₂`'s controller's row, unchanged). -/
theorem A₂c_eq_bot_of_A₁cR (h : q ⟨A₁c, memA₁c₃⟩ = ⊥) : q ⟨A₂c, memA₂c₃⟩ = ⊥ := by
  obtain ⟨g, σ, hw, heq⟩ := TransformsTo.witness (hq.locality ⟨A₂c, memA₂c₃⟩)
  have h1 : min (q ⟨A₁c, memA₁c₃⟩) (q ⟨A₂c, memA₂c₃⟩) =
      min (σ (rowsR.E A₂c ⟨A₁c, A₁c_below_A₂c⟩)) (g (D₂.grade A₁c)) :=
    heq ⟨A₁c, A₁c_below_A₂c⟩
  have hA : min (q ⟨A₂c, memA₂c₃⟩) (q ⟨A₂c, memA₂c₃⟩) =
      min (σ (rowsR.E A₂c ⟨A₂c, refl_A₂c⟩)) (g (D₂.grade A₂c)) := heq ⟨A₂c, refl_A₂c⟩
  rw [h, rowsR_E_A₂c ⟨A₁c, A₁c_below_A₂c⟩, rows₃_A₂c_A₁c, grade_A₁c, min_eq_left bot_le] at h1
  rw [min_self, rowsR_E_A₂c ⟨A₂c, refl_A₂c⟩, rows₃_A₂c_self, grade_A₂c] at hA
  rcases min_eq_bot.mp h1.symm with hσ | hg
  · have h5 := hw.clause5 η₁ 4 (by rw [hσ]; exact bot_le) 4 le_rfl
    rw [hσ, extVisibilityReplace_bot, evr_η₁_four] at h5
    rw [hA, h5]; exact min_eq_left bot_le
  · rw [hA, hg]; exact min_eq_right bot_le

/-- The moving-orbit bound `z₁ ≤ R₃ v` (`a₁`'s controller's row, unchanged). -/
theorem A₁c_le_R₃_of_respectsR (d : D₂.below (Finset.univ, 3)) (hp : IsProper d.1)
    (hg : D₂.grade d.1 = 1) :
    q ⟨A₁c, memA₁c₃⟩ ≤ extVisibilityReplace (q d) 3 3 := by
  have h := orbit_bounds_probe (fun e : D₂.below (D₂.cell A₁c) => D₂.grade e.1) (rowsR.E A₁c)
    (fun e => q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ e)) (c := ⟨A₁c, refl_A₁c⟩)
    (d := ⟨d.1, proper_below_A₁c d⟩)
    (by change D₂.grade d.1 ≤ D₂.grade A₁c; rw [hg, grade_A₁c]; decide)
    (hq.locality ⟨A₁c, memA₁c₃⟩) (e := ⟨A₁c, refl_A₁c⟩) (by
      change rowsR.E A₁c ⟨A₁c, refl_A₁c⟩ =
        extVisibilityReplace (rowsR.E A₁c ⟨d.1, proper_below_A₁c d⟩) (D₂.grade A₁c) (D₂.grade A₁c)
      rw [rowsR_E_A₁c ⟨A₁c, refl_A₁c⟩, rowsR_E_A₁c ⟨d.1, proper_below_A₁c d⟩, rows₃_A₁c_self,
        rows₃_A₁c_proper ⟨d.1, proper_below_A₁c d⟩ hp hg, grade_A₁c, v₀_orbit_three])
  have e1 : CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₁c, refl_A₁c⟩ = ⟨A₁c, memA₁c₃⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨d.1, proper_below_A₁c d⟩ = d :=
    Subtype.ext rfl
  change min (q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₁c, refl_A₁c⟩))
    (q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₁c, refl_A₁c⟩)) ≤
    extVisibilityReplace (q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨d.1, proper_below_A₁c d⟩))
      (D₂.grade A₁c) (D₂.grade A₁c) at h
  rwa [e1, e2, min_self, grade_A₁c] at h

theorem proper_fix_of_lt_A₁cR (d : D₂.below (Finset.univ, 3)) (hp : IsProper d.1)
    (hg : D₂.grade d.1 = 1) (hlt : q d < q ⟨A₁c, memA₁c₃⟩) :
    extVisibilityReplace (q d) 3 1 = q d := by
  have e1 : CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₁c, refl_A₁c⟩ = ⟨A₁c, memA₁c₃⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨d.1, proper_below_A₁c d⟩ = d :=
    Subtype.ext rfl
  have h := orbit_fixes_label (fun e : D₂.below (D₂.cell A₁c) => D₂.grade e.1) (rowsR.E A₁c)
    (fun e => q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ e)) (c := ⟨A₁c, refl_A₁c⟩)
    (d := ⟨d.1, proper_below_A₁c d⟩)
    (by change D₂.grade d.1 ≤ D₂.grade A₁c; rw [hg, grade_A₁c]; decide)
    (hq.locality ⟨A₁c, memA₁c₃⟩) (by
      change q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨d.1, proper_below_A₁c d⟩) <
        q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₁c, refl_A₁c⟩)
      rw [e1, e2]; exact hlt)
    (i := 1) (by change 1 ≤ D₂.grade A₁c; rw [grade_A₁c]; decide) (by
      change extVisibilityReplace (rowsR.E A₁c ⟨d.1, proper_below_A₁c d⟩) (D₂.grade A₁c) 1 =
        rowsR.E A₁c ⟨d.1, proper_below_A₁c d⟩
      rw [rowsR_E_A₁c ⟨d.1, proper_below_A₁c d⟩, rows₃_A₁c_proper ⟨d.1, proper_below_A₁c d⟩ hp hg,
        grade_A₁c, v₀_orbit_three_one])
  change extVisibilityReplace (q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨d.1, proper_below_A₁c d⟩))
    (D₂.grade A₁c) 1 = q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨d.1, proper_below_A₁c d⟩) at h
  rwa [e2, grade_A₁c] at h

theorem selfVis_A₁c_of_respectsR : SelfVis 3 (q ⟨A₁c, memA₁c₃⟩) := by
  have := (hq.orderly ⟨A₁c, memA₁c₃⟩).symm
  change SelfVis (D₂.grade A₁c) _ at this
  rwa [grade_A₁c] at this

/-- The sharp orbit law `v < z₁ → z₁ = R₃ v` survives. -/
theorem A₁c_eq_R₃_of_ltR (d : D₂.below (Finset.univ, 3)) (hp : IsProper d.1)
    (hg : D₂.grade d.1 = 1) (hlt : q d < q ⟨A₁c, memA₁c₃⟩) :
    q ⟨A₁c, memA₁c₃⟩ = extVisibilityReplace (q d) 3 3 :=
  eq_R₃_of_orbit hlt (selfVis_A₁c_of_respectsR hq) (A₁c_le_R₃_of_respectsR hq d hp hg)
    (proper_fix_of_lt_A₁cR hq d hp hg hlt)

/-! ### Newly induced constraints -/

/-- **`a₂`'s controller is below the old occurrence** (`a₂`'s row reads `ω+4` at both). -/
theorem A₂c_le_H₀old_of_respectsR : q ⟨A₂c, memA₂c₃⟩ ≤ q ⟨H₀old, memH₀old₃⟩ := by
  have hb : GradedLe (D₂.cell H₀old) (D₂.cell A₂c) := by rw [cell_A₂c]; exact memH₀old₃
  have h := hq.probe_ge_of_row_eq ⟨A₂c, memA₂c₃⟩ ⟨H₀old, hb⟩ ⟨A₂c, refl_A₂c⟩
    ((rowsR_E_A₂c ⟨H₀old, hb⟩).trans
      (((E₃_A₂c _).trans ((pull_eq_rowX _ not_mute_H₀old ret₂_H₀old).trans rowX_a₂_H)).trans
        (rows₃_A₂c_self.symm.trans (rowsR_E_A₂c ⟨A₂c, refl_A₂c⟩).symm)))
    (by rw [grade_H₀old, grade_A₂c]; decide)
  have e1 : CellScheme.below.incl ⟨A₂c, memA₂c₃⟩ ⟨H₀old, hb⟩ = ⟨H₀old, memH₀old₃⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨A₂c, memA₂c₃⟩ ⟨A₂c, refl_A₂c⟩ = ⟨A₂c, memA₂c₃⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.trans (min_le_left _ _)

/-- **The replacement of the dead identity**: `z₂ ≤ min x₀ w`, an inequality only. -/
theorem A₂c_le_min_of_respectsR :
    q ⟨A₂c, memA₂c₃⟩ ≤ min (q ⟨H₀old, memH₀old₃⟩) (q ⟨ub₁, memub₁₃⟩) :=
  le_min (A₂c_le_H₀old_of_respectsR hq) (A₂c_le_ub₁_of_respectsR hq)

/-- **The bottom fibre of the repaired row at threshold four** (explicit, as the sources
`ω·2+3` at the old witnesses and `ω·2+4` at the separated cells sit one step apart in one
block): `min x₀ w = ⊥ → w = ⊥`. -/
theorem ub₁_eq_bot_of_min_botR (h : min (q ⟨H₀old, memH₀old₃⟩) (q ⟨ub₁, memub₁₃⟩) = ⊥) :
    q ⟨ub₁, memub₁₃⟩ = ⊥ := by
  obtain ⟨g, σ, hw, heq⟩ := TransformsTo.witness (hq.locality ⟨ub₁, memub₁₃⟩)
  have h0 : min (q ⟨H₀old, memH₀old₃⟩) (q ⟨ub₁, memub₁₃⟩) =
      min (σ (rowsR.E ub₁ ⟨H₀old, H₀old_below_ub₁⟩)) (g (D₂.grade H₀old)) :=
    heq ⟨H₀old, H₀old_below_ub₁⟩
  have hU : min (q ⟨ub₁, memub₁₃⟩) (q ⟨ub₁, memub₁₃⟩) =
      min (σ (rowsR.E ub₁ ⟨ub₁, refl_ub₁⟩)) (g (D₂.grade ub₁)) := heq ⟨ub₁, refl_ub₁⟩
  rw [h, rowsR_ub₁_H₀old, grade_H₀old] at h0
  rw [min_self, rowsR_ub₁_self, grade_ub₁] at hU
  rcases min_eq_bot.mp h0.symm with hσ | hg
  · have h5 := hw.clause5 (ofOrd (ω2 3)) 4 (by rw [hσ]; exact bot_le) 4 le_rfl
    rw [hσ, extVisibilityReplace_bot, evr_ω2_three_four] at h5
    rw [hU, h5]; exact min_eq_left bot_le
  · have hg3 : g 3 = ⊥ := le_bot_iff.mp ((hw.anti 1 3 (by decide)).trans hg.le)
    rw [hU, hg3]; exact min_eq_right bot_le

end ConstraintsR

/-- **The dead identity is really dead**: the bottom face's extension has `z₂ = ⊥` under
`min x₀ w = 3`. -/
theorem not_A₂c_eq_minR : ∃ q : D₂.below (Finset.univ, 3) → ExtOrd,
    RespectsSemanticsBelow rowsR (Finset.univ, 3) q ∧
    q ⟨A₂c, memA₂c₃⟩ ≠ min (q ⟨H₀old, memH₀old₃⟩) (q ⟨ub₁, memub₁₃⟩) := by
  refine ⟨bottomFull, bottomFull_respects, ?_⟩
  rw [bottomFull_A₂c, bottomFull_ub₁,
    bottomFull_of_high (d := ⟨H₀old, memH₀old₃⟩)
      (by change _ ≤ qM H₀old; rw [qM_H₀old]; exact ω2_ge 3), min_self]
  exact (ofOrd_ne_bot _).symm

end VaughtConjecture.Knight
