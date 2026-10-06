/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledBountifulReduction

/-! # The grade-one scope-changing case of the coupled semantics' bountifulness

**The complete grade-one retuning** (`properToFull₃_one`): the scope-changing obligation
`ProperToFull₃Low` at `j = 1` against the frozen rows `rows₃` — a labelling `p` respecting the
rows on a proper pair `(C, 1)` and a labelling `q` respecting them on `(univ, 1)`, agreeing below
`γ` on the pair, have a common respecting labelling of `(univ, 1)` extending `p` **literally** and
agreeing with `q` **below `γ`**.

**The parameter reduction, on the actual cells.**  A respecting labelling of `(univ, 1)` is a
triple: one value `v` on the seven proper cells (`const_of_respects`: locality at the top cell
reads `ω+1` at every proper cell, availability and cell uniqueness bound every proper label by
the top's — cells of grade at most two are determined by their graded index, `cell_inj_low`),
`x₀` at the old occurrence `H₀old`, and `x₁` at both the copy `H₀new` and the controller `U_H`
(`H₀new_eq_U_H_of_respects`), with `v ≤ x₀ ≤ x₁` and the bottom coupling `x₀ = ⊥ → x₁ = ⊥`
(`U_H_eq_bot_of_H₀old`).  A proper pair protects `v` alone, or `(v, x₀)` (the old face
`{0,1,2}`), or `(v, x₁)` (the copy face `{1,2,3}`) — never both witnesses.

**The explicit face-sensitive rule** (`retune₁` with the free labels chosen in
`properToFull₃_one`): keep `p` on the pair and its proper value `vP` on every proper cell; with
the whole `q = (vq, x₀q, x₁q)`:
* old face protected: `x₀' = p H₀old`, `x₁' = max x₁q x₀'`;
* copy face protected: `x₁' = p H₀new`, `x₀' = min (max x₀q vP) x₁'`;
* only `v` protected: `x₀' = max x₀q vP`, `x₁' = max x₁q x₀'`;
* `γ = ⊥` (agreement vacuous): both free labels equal the protected witness label, else `vP`.
The bottom coupling holds because agreement below a nonbottom `γ` transports `x₀q = ⊥` (hence
`x₁q = ⊥`) to the chosen labels.  Capped agreement is the distributivity of `min` over `max`
together with `vq ≤ x₀q ≤ x₁q`.

**The witnesses**: the constant witness at proper cells (`transformsTo_const_of_ne_bot`), the
limit step `Witness.stepLimit` at `2ω` from `v` to `x₀` at the old occurrence (and to `x₁` at the
copy), and at the controller the limit step followed by `Witness.raise` at `2ω+2` to `x₁`, with the
bottom case separated (a bottom `x₀'` blocks the raise and the coupling makes `x₁' = ⊥`).  The
limit-cutoff witness is used only at limit cutoffs; the finite-offset cutoff `2ω+2` is handled by
`Witness.raise` as before.

Reviewed against the SMT handoff `research/smt/COUPLED-GRADE-ONE.md` (the same triple model and
face-sensitive choices, checked externally on the scalar model); the Lean bridges that handoff
lists as remaining — that every actual respecting labelling has the triple form, and the
identification of the named cells with the scheme's cells — are the theorems above.

Not done: grades two and three of `ProperToFull₃Low`.  Construction-private (not root-exported). -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## Cell uniqueness at grades at most two -/

section Unique

theorem Prop3.eq_of_cell {c c' : Prop3} (h : (c.scope, c.gradeP) = (c'.scope, c'.gradeP)) :
    c = c' := by
  revert h; cases c <;> cases c' <;> decide

/-- Input A's cells of grade at most two are determined by their graded index. -/
theorem family₀_cellX_inj {x y : family₀.X} (h : family₀.cellX x = family₀.cellX y)
    (hg : (family₀.cellX x).2 ≤ 2) : x = y := by
  rcases x with c | H | s | a <;> rcases y with c' | H' | s' | a'
  · exact congrArg Sum.inl (Prop3.eq_of_cell h)
  · exact absurd (congrArg Prod.fst h) (Prop3.scope_ne_univ c)
  · exact absurd (congrArg Prod.fst h) (Prop3.scope_ne_univ c)
  · exact absurd (congrArg Prod.fst h) (Prop3.scope_ne_univ c)
  · exact absurd (congrArg Prod.fst h).symm (Prop3.scope_ne_univ c')
  · rw [eq_H₀X₀ H, eq_H₀X₀ H']
  · have := congrArg Prod.snd h; change (1 : ℕ) = 2 at this; omega
  · have := congrArg Prod.snd h; change (1 : ℕ) = 3 at this; omega
  · exact absurd (congrArg Prod.fst h).symm (Prop3.scope_ne_univ c')
  · have := congrArg Prod.snd h; change (2 : ℕ) = 1 at this; omega
  · rw [eq_s₀X₀ s, eq_s₀X₀ s']
  · have := congrArg Prod.snd h; change (2 : ℕ) = 3 at this; omega
  · change (3 : ℕ) ≤ 2 at hg; omega
  · change (3 : ℕ) ≤ 2 at hg; omega
  · change (3 : ℕ) ≤ 2 at hg; omega
  · change (3 : ℕ) ≤ 2 at hg; omega

/-- Input B's cells of grade at most two are determined by their graded index. -/
theorem family₁_cellX_inj {x y : family₁.X} (h : family₁.cellX x = family₁.cellX y)
    (hg : (family₁.cellX x).2 ≤ 2) : x = y := by
  rcases img_cases x with ⟨c, rfl⟩ | rfl | rfl | rfl <;>
    rcases img_cases y with ⟨c', rfl⟩ | rfl | rfl | rfl
  · exact congrArg Sum.inl (Prop3.eq_of_cell h)
  · exact absurd (congrArg Prod.fst h) (Prop3.scope_ne_univ c)
  · exact absurd (congrArg Prod.fst h) (Prop3.scope_ne_univ c)
  · exact absurd (congrArg Prod.fst h) (Prop3.scope_ne_univ c)
  · exact absurd (congrArg Prod.fst h).symm (Prop3.scope_ne_univ c')
  · rfl
  · exact absurd (congrArg Prod.snd h) (by decide)
  · exact absurd (congrArg Prod.snd h) (by decide)
  · exact absurd (congrArg Prod.fst h).symm (Prop3.scope_ne_univ c')
  · exact absurd (congrArg Prod.snd h) (by decide)
  · rfl
  · exact absurd (congrArg Prod.snd h) (by decide)
  · exact absurd hg (by decide)
  · exact absurd hg (by decide)
  · exact absurd hg (by decide)
  · exact absurd hg (by decide)

theorem castAdd_inj_cell {i i' : Cell C₀}
    (h : D₂.cell (Fin.castAdd (Fintype.card New₂) i) = D₂.cell (Fin.castAdd (Fintype.card New₂) i'))
    (hg : D₂.grade (Fin.castAdd (Fintype.card New₂) i) ≤ 2) :
    Fin.castAdd (Fintype.card New₂) i = Fin.castAdd (Fintype.card New₂) i' := by
  rw [D₂_cell_castAdd, D₂_cell_castAdd] at h
  unfold pushGraded at h
  have hf := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  dsimp only at hf hs
  have h1 : C₀.cell i = C₀.cell i' :=
    Prod.ext (Finset.image_injective Fin.castSuccEmb.injective hf) hs
  rw [Family.cell_eq, Family.cell_eq] at h1
  have hg' : (family₀.cellX (family₀.e.symm i)).2 ≤ 2 := by
    rw [← Family.grade_eq, ← D₂_grade_castAdd]; exact hg
  have := family₀_cellX_inj h1 hg'
  rw [← Equiv.apply_symm_apply family₀.e i, this, Equiv.apply_symm_apply]

/-- A B-face cell whose scope misses the fresh point is an A-face cell. -/
theorem eq_castAdd_of_B_of_three {d : Cell D₂} (hd : ¬ mute₂ d) (h3 : (3 : Fin 4) ∉ D₂.scope d)
    (hB : GradedLe (D₂.cell d) (({1, 2, 3} : Finset (Fin 4)), 3)) :
    ∃ i, d = Fin.castAdd (Fintype.card New₂) i := by
  induction d using Fin.addCases with
  | left i => exact ⟨i, rfl⟩
  | right j =>
    exfalso
    rcases hy : (Fintype.equivFin New₂).symm j with p | f | u
    · apply h3
      change (3 : Fin 4) ∈ (D₂.cell _).1
      rw [D₂_cell_natAdd, hy]
      exact last_mem_newFacesB _ p.1.1.2
    · have : (0 : Fin 4) ∈ D₂.scope (Fin.natAdd C₀.card j) := by
        change (0 : Fin 4) ∈ (D₂.cell _).1
        rw [D₂_cell_natAdd, hy]; exact Finset.mem_univ _
      exact absurd (hB.1 this) (by decide)
    · exact hd (mute₂_natAdd_unit hy)

/-- **Cells of grade at most two are determined by their graded index.** -/
theorem cell_inj_low {d d' : Cell D₂} (h : D₂.cell d = D₂.cell d') (hg : D₂.grade d ≤ 2) :
    d = d' := by
  have hg' : D₂.grade d' ≤ 2 := by change (D₂.cell d').2 ≤ 2; rw [← h]; exact hg
  have hnm : ¬ mute₂ d := fun hm => by
    change D₂.cell d = _ at hm; have := congrArg Prod.snd hm; change D₂.grade d = 4 at this; omega
  have hnm' : ¬ mute₂ d' := fun hm => by
    change D₂.cell d' = _ at hm; have := congrArg Prod.snd hm; change D₂.grade d' = 4 at this; omega
  -- reduce both to the A face, the B face, or the two low full cells
  have key : ∀ x : Cell D₂, ¬ mute₂ x → D₂.grade x ≤ 2 →
      (∃ i, x = Fin.castAdd (Fintype.card New₂) i) ∨
      ((3 : Fin 4) ∈ D₂.scope x ∧ GradedLe (D₂.cell x) (({1, 2, 3} : Finset (Fin 4)), 3)) ∨
      x = U_H ∨ x = U_S := by
    intro x hx hgx
    rcases cell_cases x hx with ⟨i, rfl⟩ | hB | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨i, rfl⟩
    · by_cases h3 : (3 : Fin 4) ∈ D₂.scope x
      · exact Or.inr (Or.inl ⟨h3, hB⟩)
      · exact Or.inl (eq_castAdd_of_B_of_three hx h3 hB)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exfalso; change (D₂.cell A₁c).2 ≤ 2 at hgx; rw [cell_A₁c] at hgx; exact absurd hgx (by decide)
    · exfalso; change (D₂.cell A₂c).2 ≤ 2 at hgx; rw [cell_A₂c] at hgx; exact absurd hgx (by decide)
    · exfalso; change (D₂.cell ub₁).2 ≤ 2 at hgx; rw [cell_ub₁] at hgx; exact absurd hgx (by decide)
  have hsc : D₂.scope d = D₂.scope d' := congrArg Prod.fst h
  rcases key d hnm hg with ⟨i, rfl⟩ | ⟨h3, hB⟩ | rfl | rfl <;>
    rcases key d' hnm' hg' with ⟨i', rfl⟩ | ⟨h3', hB'⟩ | rfl | rfl
  · exact castAdd_inj_cell h hg
  · exact absurd (hsc ▸ h3') (three_not_mem_scope_castAdd i)
  · exfalso; apply three_not_mem_scope_castAdd i; rw [hsc]
    change (3 : Fin 4) ∈ (D₂.cell U_H).1; rw [cell_U_H]; exact Finset.mem_univ _
  · exfalso; apply three_not_mem_scope_castAdd i; rw [hsc]
    change (3 : Fin 4) ∈ (D₂.cell U_S).1; rw [cell_U_S]; exact Finset.mem_univ _
  · exact absurd (hsc.symm ▸ h3) (three_not_mem_scope_castAdd i')
  · -- both on the B face: retract to input B
    rw [eq_copyB_of_B hB, eq_copyB_of_B hB']
    congr 1
    have h1 := cell_retB zero_not_mem_B ⟨d, hB⟩
    have h2 := cell_retB zero_not_mem_B ⟨d', hB'⟩
    have h12 : C₁.cell (retB d) = C₁.cell (retB d') := by
      rw [h1, h2, hsc, show D₂.grade d = D₂.grade d' from congrArg Prod.snd h]
    rw [Family.cell_eq, Family.cell_eq] at h12
    have hg1 : (family₁.cellX (family₁.e.symm (retB d))).2 ≤ 2 := by
      rw [← Family.grade_eq, show C₁.grade (retB d) = D₂.grade d from congrArg Prod.snd h1]
      exact hg
    have := family₁_cellX_inj h12 hg1
    rw [← Equiv.apply_symm_apply family₁.e (retB d), this, Equiv.apply_symm_apply]
  · exfalso
    have : (0 : Fin 4) ∈ D₂.scope d := by
      rw [hsc]; change (0 : Fin 4) ∈ (D₂.cell U_H).1; rw [cell_U_H]; exact Finset.mem_univ _
    exact absurd (hB.1 this) (by decide)
  · exfalso
    have : (0 : Fin 4) ∈ D₂.scope d := by
      rw [hsc]; change (0 : Fin 4) ∈ (D₂.cell U_S).1; rw [cell_U_S]; exact Finset.mem_univ _
    exact absurd (hB.1 this) (by decide)
  · exfalso; apply three_not_mem_scope_castAdd i'; rw [← hsc]
    change (3 : Fin 4) ∈ (D₂.cell U_H).1; rw [cell_U_H]; exact Finset.mem_univ _
  · exfalso
    have : (0 : Fin 4) ∈ D₂.scope d' := by
      rw [← hsc]; change (0 : Fin 4) ∈ (D₂.cell U_H).1; rw [cell_U_H]; exact Finset.mem_univ _
    exact absurd (hB'.1 this) (by decide)
  · rfl
  · exfalso; rw [cell_U_H, cell_U_S] at h; exact absurd (congrArg Prod.snd h) (by decide)
  · exfalso; apply three_not_mem_scope_castAdd i'; rw [← hsc]
    change (3 : Fin 4) ∈ (D₂.cell U_S).1; rw [cell_U_S]; exact Finset.mem_univ _
  · exfalso
    have : (0 : Fin 4) ∈ D₂.scope d' := by
      rw [← hsc]; change (0 : Fin 4) ∈ (D₂.cell U_S).1; rw [cell_U_S]; exact Finset.mem_univ _
    exact absurd (hB'.1 this) (by decide)
  · exfalso; rw [cell_U_H, cell_U_S] at h; exact absurd (congrArg Prod.snd h) (by decide)
  · rfl

end Unique


/-! ## Rows and labellings at grade one -/

section One

/-- A cell retracting to a proper cell of the three-cell family. -/
def IsProper (d : Cell D₂) : Prop := ∃ c : Prop3, family₂.e.symm (ret₂ d) = .inl c

theorem one_cases {d : Cell D₂} (hd : ¬ mute₂ d) (hg : D₂.grade d ≤ 1) :
    d = H₀old ∨ d = H₀new ∨ d = U_H ∨ IsProper d := by
  rcases vU_cases d hd hg with h | h | ⟨c, -, hc⟩
  · exact Or.inl h
  · rcases ret_H₀_cases hd h.1 with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
  · exact Or.inr (Or.inr (Or.inr ⟨c, hc⟩))

theorem gradeP_le_of_proper {d : Cell D₂} (hd : ¬ mute₂ d) {c : Prop3}
    (hc : family₂.e.symm (ret₂ d) = .inl c) : c.gradeP = D₂.grade d := by
  rw [grade_ret_eq hd, hc]; rfl

theorem not_isProper_of_ret {d : Cell D₂} {x : family₂.X} (hx : (family₂.cellX x).1 = Finset.univ)
    (h : ret₂ d = family₂.e x) : ¬ IsProper d := fun ⟨_, hc⟩ => ret_ne_of_inl' hc hx h

theorem isProper_of_below {Sig d : Cell D₂} (hSig : ¬ mute₂ Sig) (hd : ¬ mute₂ d)
    (hle : GradedLe (D₂.cell d) (D₂.cell Sig)) (hg : D₂.grade d ≤ 1) (hp : IsProper Sig) :
    IsProper d := by
  obtain ⟨c, hc⟩ := hp
  rcases one_cases hd hg with rfl | rfl | rfl | h
  · exact absurd ret₂_H₀old (ret_ne_full_of_below hSig hd hle hc rfl)
  · exact absurd ret₂_H₀new (ret_ne_full_of_below hSig hd hle hc rfl)
  · exact absurd ret₂_U_H (ret_ne_full_of_below hSig hd hle hc rfl)
  · exact h

/-- **The rows at grade one read `ω+1` at every proper cell.** -/
theorem rows₃_E_one_proper {T : Cell D₂} (hT : D₂.grade T = 1) (d : D₂.below (D₂.cell T))
    (hd : IsProper d.1) : rows₃.E T d = v₀ := by
  obtain ⟨c, hc⟩ := hd
  have hnmT : ¬ mute₂ T := fun hm => by
    change D₂.cell T = _ at hm; have := congrArg Prod.snd hm; change D₂.grade T = 4 at this; omega
  have hnmd : ¬ mute₂ d.1 := hmute_below₂ T d.1 hnmT d.2
  have hc1 : c.gradeP ≤ 1 := by rw [gradeP_le_of_proper hnmd hc]; exact d.2.2.trans hT.le
  have hA : AFace H₀old := aFace_castAdd _
  rcases one_cases hnmT hT.le with rfl | rfl | rfl | ⟨c', hc'⟩
  · rw [E₃_of_A hA, rows₂_E_eq_pull not_mute_H₀old, ret₂_H₀old,
      Equiv.symm_apply_apply, pull_of_not_mute _ hnmd, hc, family₂.rowX_H_inl _ c hc1]
    exact H₀c_G_v₀ hc1
  · rw [E₃_of_B bFace_H₀new, rows₂_E_eq_pull not_mute_H₀new, ret₂_H₀new,
      Equiv.symm_apply_apply, pull_of_not_mute _ hnmd, hc, family₂.rowX_H_inl _ c hc1]
    exact H₀c_G_v₀ hc1
  · rw [rows₃_E, E₃_U_H]; exact vU_of_proper hnmd hc1 hc
  · rw [E₃_of_proper hc', rows₂_E_eq_pull hnmT, hc', pull_of_not_mute _ hnmd, hc]
    change (if c'.gradeP ≤ 1 then family₂.v else ⊥) = v₀
    rw [ite_eq_left (by rw [gradeP_le_of_proper hnmT hc']; exact hT.le)]; rfl

theorem rows₃_E_H₀old_self (d : D₂.below (D₂.cell H₀old)) (hd : d.1 = H₀old) :
    rows₃.E H₀old d = ofOrd (ω2 1) := by
  have hA : AFace H₀old := aFace_castAdd _
  rw [E₃_of_A hA, rows₂_E_eq_pull not_mute_H₀old, ret₂_H₀old, Equiv.symm_apply_apply,
    hd, pull_of_ret not_mute_H₀old ret₂_H₀old, rowX_H₀X_H₀X, H₀c_δ_num]
theorem rows₃_E_H₀new_self (d : D₂.below (D₂.cell H₀new)) (hd : d.1 = H₀new) :
    rows₃.E H₀new d = ofOrd (ω2 1) := by
  rw [E₃_of_B bFace_H₀new, rows₂_E_eq_pull not_mute_H₀new, ret₂_H₀new, Equiv.symm_apply_apply,
    hd, pull_of_ret not_mute_H₀new ret₂_H₀new, rowX_H₀X_H₀X, H₀c_δ_num]
theorem rows₃_E_U_H_H₀old (d : D₂.below (D₂.cell U_H)) (hd : d.1 = H₀old) :
    rows₃.E U_H d = ofOrd (ω2 1) := by
  rw [rows₃_E, E₃_U_H, hd, vU_H₀old, H₀c_δ_num]
theorem rows₃_E_U_H_new (d : D₂.below (D₂.cell U_H)) (hd : d.1 = H₀new ∨ d.1 = U_H) :
    rows₃.E U_H d = ofOrd (ω2 2) := by
  rw [rows₃_E, E₃_U_H, vU_eq_row₃, row₃_of_eq d hd, wSep_num]

/-- Below the old occurrence: itself or a proper cell. -/
theorem below_H₀old_cases (d : D₂.below (D₂.cell H₀old)) : d.1 = H₀old ∨ IsProper d.1 := by
  have hd : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_H₀old d.2
  rcases one_cases hd (d.2.2.trans grade_H₀old.le) with h | h | h | h
  · exact Or.inl h
  · exfalso
    have h3 : (3 : Fin 4) ∈ D₂.scope d.1 := by rw [h, scope_H₀new]; decide
    exact three_not_mem_scope_castAdd (family₀.e H₀X₀) (d.2.1 h3)
  · exfalso
    apply three_not_mem_scope_castAdd (family₀.e H₀X₀) (d.2.1 _)
    rw [h, cell_U_H]; exact Finset.mem_univ _
  · exact Or.inr h
theorem below_H₀new_cases' (d : D₂.below (D₂.cell H₀new)) : d.1 = H₀new ∨ IsProper d.1 := by
  rcases below_H₀new_cases d with h | ⟨c, -, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨c, hc⟩

theorem memU₁' : GradedLe (D₂.cell U_H) (Finset.univ, 1) := memU₁

/-- **Proper-cell constancy**: a labelling respecting the rows on a lower set of grade one with a
top cell is constant on the proper cells (locality at the top cell reads `ω+1` everywhere;
availability and cell uniqueness bound every proper label by the top's). -/
theorem const_of_respects {BJ : Finset (Fin 4) × ℕ} (hBJ : BJ.2 = 1) {r : D₂.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow rows₃ BJ r) (T : D₂.below BJ) (hT : D₂.cell T.1 = BJ)
    (d sc : D₂.below BJ) (hd : IsProper d.1) (hsc : IsProper sc.1) : r d = r sc := by
  have hgT : D₂.grade T.1 = 1 := by change (D₂.cell T.1).2 = 1; rw [hT, hBJ]
  have hdT : GradedLe (D₂.cell d.1) (D₂.cell T.1) := by rw [hT]; exact d.2
  have hscT : GradedLe (D₂.cell sc.1) (D₂.cell T.1) := by rw [hT]; exact sc.2
  have hprobe := hr.probe_eq_of_row_eq T ⟨d.1, hdT⟩ ⟨sc.1, hscT⟩
    ((rows₃_E_one_proper hgT ⟨d.1, hdT⟩ hd).trans (rows₃_E_one_proper hgT ⟨sc.1, hscT⟩ hsc).symm)
    (by
      change (D₂.cell d.1).2 = (D₂.cell sc.1).2
      have h1 : D₂.grade d.1 = 1 := le_antisymm (d.2.2.trans hBJ.le) (D₂.grade_pos _)
      have h2 : D₂.grade sc.1 = 1 := le_antisymm (sc.2.2.trans hBJ.le) (D₂.grade_pos _)
      exact h1.trans h2.symm)
  have e1 : CellScheme.below.incl T ⟨d.1, hdT⟩ = d := Subtype.ext rfl
  have e2 : CellScheme.below.incl T ⟨sc.1, hscT⟩ = sc := Subtype.ext rfl
  rw [e1, e2] at hprobe
  -- every proper label is at most the top's
  have hle : ∀ x : D₂.below BJ, r x ≤ r T := by
    intro x
    obtain ⟨Xi, hXi, hle⟩ := hr.availability x T (by
        change (D₂.cell x.1).1 ⊆ (D₂.cell T.1).1; rw [hT]; exact x.2.1) (by
      change (D₂.cell x.1).2 = (D₂.cell T.1).2
      rw [hT]; exact le_antisymm x.2.2 (hBJ ▸ D₂.grade_pos _))
    have : Xi = T := Subtype.ext (cell_inj_low hXi (by
      change (D₂.cell Xi.1).2 ≤ 2; rw [hXi, hT, hBJ]; decide))
    rw [this] at hle; exact hle
  rw [min_eq_left (hle d), min_eq_left (hle sc)] at hprobe
  exact hprobe

end One


/-! ## Self-visibility of minima and maxima -/

theorem selfVis_max {K : ℕ} {a b : ExtOrd} (ha : SelfVis K a) (hb : SelfVis K b) :
    SelfVis K (max a b) := by
  change extVisibilityReplace (max a b) K K = max a b
  rw [extVisibilityReplace_max a b le_rfl]
  change extVisibilityReplace a K K = a at ha
  change extVisibilityReplace b K K = b at hb
  rw [ha, hb]
theorem selfVis_min' {K : ℕ} {a b : ExtOrd} (ha : SelfVis K a) (hb : SelfVis K b) :
    SelfVis K (min a b) := by
  change extVisibilityReplace (min a b) K K = min a b
  have hm : Monotone (fun z : ExtOrd => extVisibilityReplace z K K) :=
    fun x y h => evr_mono h le_rfl
  rw [hm.map_min]
  change extVisibilityReplace a K K = a at ha
  change extVisibilityReplace b K K = b at hb
  rw [ha, hb]

/-! ## The grade-one retuning -/

section Retune

theorem singleton_mem_plan₄ : ∀ c : Fin 4, ({c} : Finset (Fin 4)) ∈ plan₄ := by decide

theorem v₀_ne_bot : v₀ ≠ ⊥ := ofOrd_ne_bot _
theorem ω2_zero : ω2 0 = Ordinal.omega0 * ((2 : ℕ) : Ordinal) := by
  unfold ω2; rw [Nat.cast_zero, add_zero]
theorem v₀_lt_ω2' : v₀ < ofOrd (Ordinal.omega0 * ((2 : ℕ) : Ordinal)) := by
  rw [v₀_num, ← ω2_zero]
  exact ofOrd_lt_ofOrd.mpr (ω1j_lt_ω2 1 0)
theorem ω2_ge (j : ℕ) : ofOrd (Ordinal.omega0 * ((2 : ℕ) : Ordinal)) ≤ ofOrd (ω2 j) :=
  ofOrd_le_ofOrd.mpr le_self_add

open Classical in
/-- **The retuned labelling**: the pair's labelling literally, the free labels at the old
occurrence, at the copy and the controller, and the pair's proper value elsewhere. -/
noncomputable def retune₁ (C : Finset (Fin 4)) (p : D₂.below (C, 1) → ExtOrd) (x₀' x₁' vP : ExtOrd)
    (d : D₂.below (Finset.univ, 1)) : ExtOrd :=
  if hd : GradedLe (D₂.cell d.1) (C, 1) then p ⟨d.1, hd⟩
  else if d.1 = H₀old then x₀' else if d.1 = H₀new ∨ d.1 = U_H then x₁' else vP

theorem retune₁_in {C : Finset (Fin 4)} {p : D₂.below (C, 1) → ExtOrd} {x₀' x₁' vP : ExtOrd}
    (d : D₂.below (Finset.univ, 1)) (hd : GradedLe (D₂.cell d.1) (C, 1)) :
    retune₁ C p x₀' x₁' vP d = p ⟨d.1, hd⟩ := by
  classical
  unfold retune₁; rw [dite_of_pos hd]
theorem retune₁_H₀old {C : Finset (Fin 4)} {p : D₂.below (C, 1) → ExtOrd} {x₀' x₁' vP : ExtOrd}
    (hA : ¬ GradedLe (D₂.cell H₀old) (C, 1)) :
    retune₁ C p x₀' x₁' vP ⟨H₀old, memA le_rfl⟩ = x₀' := by
  classical
  unfold retune₁; rw [dite_of_neg hA, ite_eq_left rfl]
theorem retune₁_H₀new {C : Finset (Fin 4)} {p : D₂.below (C, 1) → ExtOrd} {x₀' x₁' vP : ExtOrd}
    (hB : ¬ GradedLe (D₂.cell H₀new) (C, 1)) :
    retune₁ C p x₀' x₁' vP ⟨H₀new, memB le_rfl⟩ = x₁' := by
  classical
  unfold retune₁; rw [dite_of_neg hB, ite_eq_right H₀old_ne_H₀new.symm, ite_eq_left (Or.inl rfl)]
theorem retune₁_U_H {C : Finset (Fin 4)} {p : D₂.below (C, 1) → ExtOrd} {x₀' x₁' vP : ExtOrd}
    (hU : ¬ GradedLe (D₂.cell U_H) (C, 1)) :
    retune₁ C p x₀' x₁' vP ⟨U_H, memU₁⟩ = x₁' := by
  classical
  unfold retune₁; rw [dite_of_neg hU, ite_eq_right H₀old_ne_U_H.symm, ite_eq_left (Or.inr rfl)]
theorem retune₁_proper {C : Finset (Fin 4)} {p : D₂.below (C, 1) → ExtOrd} {x₀' x₁' vP : ExtOrd}
    (d : D₂.below (Finset.univ, 1)) (hd : IsProper d.1) (hdC : ¬ GradedLe (D₂.cell d.1) (C, 1)) :
    retune₁ C p x₀' x₁' vP d = vP := by
  classical
  have h1 : ¬ d.1 = H₀old := fun e => not_isProper_of_ret rfl ret₂_H₀old (e ▸ hd)
  have h2 : ¬ (d.1 = H₀new ∨ d.1 = U_H) := by
    rintro (e | e)
    · exact not_isProper_of_ret rfl ret₂_H₀new (e ▸ hd)
    · exact not_isProper_of_ret rfl ret₂_U_H (e ▸ hd)
  unfold retune₁
  rw [dite_of_neg hdC, ite_eq_right h1, ite_eq_right h2]

/-- **The grade-one scope-changing case**: a respecting labelling of a proper pair `(C, 1)` and a
respecting labelling of `(univ, 1)` agreeing below `γ` on the pair have a common respecting
labelling of `(univ, 1)` — literal on the pair, agreeing with the second below `γ`. -/
theorem properToFull₃_one (C : Finset (Fin 4)) (hCI : (C, 1) ∈ Plan.gradedPlan plan₄)
    (hC : C ≠ Finset.univ) (h : GradedLe (C, 1) (Finset.univ, 1))
    (p : D₂.below (C, 1) → ExtOrd) (q : D₂.below (Finset.univ, 1) → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow rows₃ (C, 1) p)
    (hq : RespectsSemanticsBelow rows₃ (Finset.univ, 1) q)
    (_hγ : extVisibilityReplace γ 1 1 = γ)
    (hagree : ∀ d : D₂.below (C, 1), min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D₂.below (Finset.univ, 1) → ExtOrd, RespectsSemanticsBelow rows₃ (Finset.univ, 1) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D₂.below (C, 1), q' (CellScheme.below.mono h d) = p d) := by
  classical
  -- the singleton cells: one inside `C`, and the cell `{1}`
  obtain ⟨c, hc⟩ : C.Nonempty := Finset.card_pos.mp (by
    obtain ⟨-, -, h1⟩ := Plan.mem_gradedPlan.mp hCI; exact h1)
  have hsing : ∀ c : Fin 4, (({c} : Finset (Fin 4)), 1) ∈ Plan.gradedPlan plan₄ := fun c =>
    Plan.mem_gradedPlan.mpr ⟨singleton_mem_plan₄ c, Nat.one_pos, by simp⟩
  obtain ⟨sc, hsc⟩ := D₂_complete _ (hsing c)
  obtain ⟨s1, hs1⟩ := D₂_complete _ (hsing 1)
  obtain ⟨T, hT⟩ := D₂_complete _ hCI
  have hscC : GradedLe (D₂.cell sc) (C, 1) := by
    rw [hsc]; exact ⟨Finset.singleton_subset_iff.mpr hc, le_rfl⟩
  have hscU : GradedLe (D₂.cell sc) (Finset.univ, 1) := by
    rw [hsc]; exact ⟨Finset.subset_univ _, le_rfl⟩
  have hs1U : GradedLe (D₂.cell s1) (Finset.univ, 1) := by
    rw [hs1]; exact ⟨Finset.subset_univ _, le_rfl⟩
  -- singleton cells are proper
  have hproper_sing : ∀ (x : Cell D₂) (c : Fin 4), D₂.cell x = ({c}, 1) → IsProper x := by
    intro x c hx
    have hnm : ¬ mute₂ x := fun hm => by
      change D₂.cell x = _ at hm; rw [hx] at hm
      have := congrArg Prod.snd hm; change (1 : ℕ) = 4 at this; omega
    have hg : D₂.grade x ≤ 1 := by change (D₂.cell x).2 ≤ 1; rw [hx]
    have hcard : (D₂.scope x).card = 1 := by change (D₂.cell x).1.card = 1; rw [hx]; simp
    rcases one_cases hnm hg with rfl | rfl | rfl | hp
    · exfalso
      have : (D₂.scope H₀old).card = 3 := by
        change (D₂.cell H₀old).1.card = 3; unfold H₀old; rw [cell_castAdd_X]; decide
      omega
    · exfalso; rw [scope_H₀new] at hcard; exact absurd hcard (by decide)
    · exfalso
      change (D₂.cell U_H).1.card = 1 at hcard
      rw [cell_U_H, Finset.card_univ, Fintype.card_fin] at hcard; omega
    · exact hp
  have hscP : IsProper sc := hproper_sing sc c hsc
  have hs1P : IsProper s1 := hproper_sing s1 1 hs1
  -- the constants
  set vP := p ⟨sc, hscC⟩ with hvP
  set vq := q ⟨sc, hscU⟩ with hvq
  set x₀q := q ⟨H₀old, memA le_rfl⟩ with hx₀q
  set x₁q := q ⟨U_H, memU₁⟩ with hx₁q
  have hpc : ∀ d : D₂.below (C, 1), IsProper d.1 → p d = vP := fun d hd =>
    const_of_respects rfl hp ⟨T, by rw [hT]; exact GradedLe.refl _⟩ hT d ⟨sc, hscC⟩ hd hscP
  have hqc : ∀ d : D₂.below (Finset.univ, 1), IsProper d.1 → q d = vq := fun d hd =>
    const_of_respects rfl hq ⟨U_H, memU₁⟩ cell_U_H d ⟨sc, hscU⟩ hd hscP
  have hq1 : q ⟨H₀new, memB le_rfl⟩ = x₁q := H₀new_eq_U_H_of_respects hq
  have hq01 : x₀q ≤ x₁q := le_U_H_of_respects hq _
  have hcoup : x₀q = ⊥ → x₁q = ⊥ := U_H_eq_bot_of_H₀old hq
  have hvq0 : vq ≤ x₀q := by
    rw [← hqc ⟨s1, hs1U⟩ hs1P]
    obtain ⟨Xi, hXi, hle⟩ := hq.availability ⟨s1, hs1U⟩ ⟨H₀old, memA le_rfl⟩ (by
        change (D₂.cell s1).1 ⊆ D₂.scope H₀old; rw [hs1]
        exact Finset.singleton_subset_iff.mpr (by
          change (1 : Fin 4) ∈ (D₂.cell H₀old).1; unfold H₀old; rw [cell_castAdd_X]; decide))
      (by change (D₂.cell s1).2 = D₂.grade H₀old; rw [hs1, grade_H₀old])
    have : Xi = ⟨H₀old, memA le_rfl⟩ :=
      Subtype.ext (cell_inj_low hXi (by
        change (D₂.cell Xi.1).2 ≤ 2; rw [hXi]
        exact (show D₂.grade H₀old ≤ 2 by rw [grade_H₀old]; decide)))
    rw [this] at hle; exact hle
  have hvq1 : vq ≤ x₁q := hvq0.trans hq01
  have hagree_sc : min vq γ = min vP γ := by
    have := hagree ⟨sc, hscC⟩
    rwa [hqc (CellScheme.below.mono h ⟨sc, hscC⟩) hscP] at this
  -- self-visibility of the constants
  have hvP_vis : SelfVis 1 vP := by
    have := (hp.orderly ⟨sc, hscC⟩).symm
    change extVisibilityReplace vP (D₂.grade sc) (D₂.grade sc) = vP at this
    rwa [show D₂.grade sc = 1 by change (D₂.cell sc).2 = 1; rw [hsc]] at this
  have hx₀q_vis : SelfVis 1 x₀q := by
    have := (hq.orderly ⟨H₀old, memA le_rfl⟩).symm
    change extVisibilityReplace x₀q (D₂.grade H₀old) (D₂.grade H₀old) = x₀q at this
    rwa [grade_H₀old] at this
  have hx₁q_vis : SelfVis 1 x₁q := by
    have := (hq.orderly ⟨U_H, memU₁⟩).symm
    change extVisibilityReplace x₁q (D₂.grade U_H) (D₂.grade U_H) = x₁q at this
    rwa [grade_U_H] at this
  -- membership of the two witness occurrences in the pair
  have hAB : ¬ (GradedLe (D₂.cell H₀old) (C, 1) ∧ GradedLe (D₂.cell H₀new) (C, 1)) := by
    rintro ⟨hA, hB⟩
    apply hC
    apply Finset.eq_univ_of_forall
    intro i
    have h0 : ({0, 1, 2} : Finset (Fin 4)) ⊆ C := by
      have := hA.1; change D₂.scope H₀old ⊆ C at this
      refine (le_of_eq ?_).trans this
      change _ = (D₂.cell H₀old).1; unfold H₀old; rw [cell_castAdd_X]; decide
    have h3 : ({1, 2, 3} : Finset (Fin 4)) ⊆ C := by
      have := hB.1; change D₂.scope H₀new ⊆ C at this; rw [scope_H₀new] at this; exact this
    fin_cases i
    · exact h0 (by decide)
    · exact h0 (by decide)
    · exact h0 (by decide)
    · exact h3 (by decide)
  have hUC : ¬ GradedLe (D₂.cell U_H) (C, 1) := fun hU => hC (Finset.univ_subset_iff.mp (by
    have := hU.1; rw [cell_U_H] at this; exact this))
  -- the free labels
  have hpA : ∀ hA : GradedLe (D₂.cell H₀old) (C, 1), vP ≤ p ⟨H₀old, hA⟩ := by
    intro hA
    have hs1C : GradedLe (D₂.cell s1) (C, 1) := by
      rw [hs1]; refine ⟨Finset.singleton_subset_iff.mpr (hA.1 ?_), le_rfl⟩
      unfold H₀old; rw [cell_castAdd_X]; decide
    rw [← hpc ⟨s1, hs1C⟩ hs1P]
    obtain ⟨Xi, hXi, hle⟩ := hp.availability ⟨s1, hs1C⟩ ⟨H₀old, hA⟩ (by
        change (D₂.cell s1).1 ⊆ D₂.scope H₀old; rw [hs1]
        exact Finset.singleton_subset_iff.mpr (by
          change (1 : Fin 4) ∈ (D₂.cell H₀old).1; unfold H₀old; rw [cell_castAdd_X]; decide))
      (by change (D₂.cell s1).2 = D₂.grade H₀old; rw [hs1, grade_H₀old])
    have : Xi = ⟨H₀old, hA⟩ :=
      Subtype.ext (cell_inj_low hXi (by
        change (D₂.cell Xi.1).2 ≤ 2; rw [hXi]
        exact (show D₂.grade H₀old ≤ 2 by rw [grade_H₀old]; decide)))
    rw [this] at hle; exact hle
  have hpB : ∀ hB : GradedLe (D₂.cell H₀new) (C, 1), vP ≤ p ⟨H₀new, hB⟩ := by
    intro hB
    have hs1C : GradedLe (D₂.cell s1) (C, 1) := by
      rw [hs1]; refine ⟨Finset.singleton_subset_iff.mpr (hB.1 ?_), le_rfl⟩
      change (1 : Fin 4) ∈ D₂.scope H₀new; rw [scope_H₀new]; decide
    rw [← hpc ⟨s1, hs1C⟩ hs1P]
    obtain ⟨Xi, hXi, hle⟩ := hp.availability ⟨s1, hs1C⟩ ⟨H₀new, hB⟩ (by
        change (D₂.cell s1).1 ⊆ D₂.scope H₀new; rw [hs1, scope_H₀new]; decide)
      (by change (D₂.cell s1).2 = D₂.grade H₀new; rw [hs1, grade_H₀new])
    have : Xi = ⟨H₀new, hB⟩ :=
      Subtype.ext (cell_inj_low hXi (by
        change (D₂.cell Xi.1).2 ≤ 2; rw [hXi]
        exact (show D₂.grade H₀new ≤ 2 by rw [grade_H₀new]; decide)))
    rw [this] at hle; exact hle
  have hagA : ∀ hA : GradedLe (D₂.cell H₀old) (C, 1), min x₀q γ = min (p ⟨H₀old, hA⟩) γ :=
    fun hA => hagree ⟨H₀old, hA⟩
  have hagB : ∀ hB : GradedLe (D₂.cell H₀new) (C, 1), min x₁q γ = min (p ⟨H₀new, hB⟩) γ :=
    fun hB => by rw [← hq1]; exact hagree ⟨H₀new, hB⟩
  -- **the explicit rule for the free labels**
  obtain ⟨x₀', x₁', hvx0, hx01, hcoup', hx0v, hx1v, hag0, hag1, hxA, hxB⟩ :
      ∃ x₀' x₁' : ExtOrd, vP ≤ x₀' ∧ x₀' ≤ x₁' ∧ (x₀' = ⊥ → x₁' = ⊥) ∧ SelfVis 1 x₀' ∧
        SelfVis 1 x₁' ∧ min x₀' γ = min x₀q γ ∧ min x₁' γ = min x₁q γ ∧
        (∀ hA : GradedLe (D₂.cell H₀old) (C, 1), x₀' = p ⟨H₀old, hA⟩) ∧
        (∀ hB : GradedLe (D₂.cell H₀new) (C, 1), x₁' = p ⟨H₀new, hB⟩) := by
    have hle_min : min x₀q γ ≤ min x₁q γ := min_le_min hq01 le_rfl
    have hvq_min : min vq γ ≤ min x₀q γ := min_le_min hvq0 le_rfl
    by_cases hA : GradedLe (D₂.cell H₀old) (C, 1)
    · -- the old occurrence is inside the pair
      have hB : ¬ GradedLe (D₂.cell H₀new) (C, 1) := fun hB => hAB ⟨hA, hB⟩
      have ha_vis : SelfVis 1 (p ⟨H₀old, hA⟩) := by
        have := (hp.orderly ⟨H₀old, hA⟩).symm
        change extVisibilityReplace _ (D₂.grade H₀old) (D₂.grade H₀old) = _ at this
        rwa [grade_H₀old] at this
      by_cases hγ : γ = ⊥
      · refine ⟨p ⟨H₀old, hA⟩, p ⟨H₀old, hA⟩, hpA hA, le_rfl, fun h => h, ha_vis, ha_vis, ?_, ?_,
          fun _ => rfl, fun hB' => absurd hB' hB⟩
        · rw [hγ, min_eq_right bot_le, min_eq_right bot_le]
        · rw [hγ, min_eq_right bot_le, min_eq_right bot_le]
      · refine ⟨p ⟨H₀old, hA⟩, max x₁q (p ⟨H₀old, hA⟩), hpA hA, le_max_right _ _, ?_, ha_vis,
          selfVis_max hx₁q_vis ha_vis, (hagA hA).symm, ?_, fun _ => rfl, fun hB' => absurd hB' hB⟩
        · intro h0
          have h1 : min x₀q γ = ⊥ := by rw [hagA hA, h0, min_eq_left bot_le]
          rcases min_eq_bot.mp h1 with h2 | h2
          · rw [hcoup h2, h0, max_self]
          · exact absurd h2 hγ
        · rw [min_max_distrib_right, ← hagA hA, max_eq_left hle_min]
    · by_cases hB : GradedLe (D₂.cell H₀new) (C, 1)
      · -- the copy is inside the pair
        have hb_vis : SelfVis 1 (p ⟨H₀new, hB⟩) := by
          have := (hp.orderly ⟨H₀new, hB⟩).symm
          change extVisibilityReplace _ (D₂.grade H₀new) (D₂.grade H₀new) = _ at this
          rwa [grade_H₀new] at this
        by_cases hγ : γ = ⊥
        · refine ⟨p ⟨H₀new, hB⟩, p ⟨H₀new, hB⟩, hpB hB, le_rfl, fun h => h, hb_vis, hb_vis, ?_, ?_,
            fun hA' => absurd hA' hA, fun _ => rfl⟩
          · rw [hγ, min_eq_right bot_le, min_eq_right bot_le]
          · rw [hγ, min_eq_right bot_le, min_eq_right bot_le]
        · refine ⟨min (max x₀q vP) (p ⟨H₀new, hB⟩), p ⟨H₀new, hB⟩,
            le_min (le_max_right _ _) (hpB hB), min_le_right _ _, ?_,
            selfVis_min' (selfVis_max hx₀q_vis hvP_vis) hb_vis, hb_vis, ?_, (hagB hB).symm,
            fun hA' => absurd hA' hA, fun _ => rfl⟩
          · intro h0
            rcases min_eq_bot.mp h0 with h2 | h2
            · have h3 : x₀q = ⊥ := le_bot_iff.mp (h2 ▸ le_max_left x₀q vP)
              have h4 : min (p ⟨H₀new, hB⟩) γ = ⊥ := by rw [← hagB hB, hcoup h3, min_eq_left bot_le]
              rcases min_eq_bot.mp h4 with h5 | h5
              · exact h5
              · exact absurd h5 hγ
            · exact h2
          · rw [min_right_comm, min_max_distrib_right, ← hagree_sc, max_eq_left hvq_min]
            exact min_eq_left (hle_min.trans ((hagB hB).le.trans (min_le_left _ _)))
      · -- neither occurrence is inside the pair
        by_cases hγ : γ = ⊥
        · refine ⟨vP, vP, le_rfl, le_rfl, fun h => h, hvP_vis, hvP_vis, ?_, ?_,
            fun hA' => absurd hA' hA, fun hB' => absurd hB' hB⟩
          · rw [hγ, min_eq_right bot_le, min_eq_right bot_le]
          · rw [hγ, min_eq_right bot_le, min_eq_right bot_le]
        · refine ⟨max x₀q vP, max x₁q (max x₀q vP), le_max_right _ _, le_max_right _ _, ?_,
            selfVis_max hx₀q_vis hvP_vis, selfVis_max hx₁q_vis (selfVis_max hx₀q_vis hvP_vis),
            ?_, ?_, fun hA' => absurd hA' hA, fun hB' => absurd hB' hB⟩
          · intro h0
            have h3 : x₀q = ⊥ := le_bot_iff.mp (h0 ▸ le_max_left x₀q vP)
            rw [h0, hcoup h3, max_self]
          · rw [min_max_distrib_right, ← hagree_sc, max_eq_left hvq_min]
          · rw [min_max_distrib_right, min_max_distrib_right, ← hagree_sc, max_eq_left hvq_min,
              max_eq_left hle_min]
  have hvx1 : vP ≤ x₁' := hvx0.trans hx01
  -- **the retuned labelling**
  set q' := retune₁ C p x₀' x₁' vP with hq'def
  have hv_H₀old : q' ⟨H₀old, memA le_rfl⟩ = x₀' := by
    by_cases hA : GradedLe (D₂.cell H₀old) (C, 1)
    · rw [hq'def, retune₁_in ⟨H₀old, memA le_rfl⟩ hA, hxA hA]
    · exact retune₁_H₀old hA
  have hv_H₀new : q' ⟨H₀new, memB le_rfl⟩ = x₁' := by
    by_cases hB : GradedLe (D₂.cell H₀new) (C, 1)
    · rw [hq'def, retune₁_in ⟨H₀new, memB le_rfl⟩ hB, hxB hB]
    · exact retune₁_H₀new hB
  have hv_U_H : q' ⟨U_H, memU₁⟩ = x₁' := retune₁_U_H hUC
  have hv_proper : ∀ d : D₂.below (Finset.univ, 1), IsProper d.1 → q' d = vP := by
    intro d hd
    by_cases hdC : GradedLe (D₂.cell d.1) (C, 1)
    · rw [hq'def, retune₁_in d hdC]; exact hpc ⟨d.1, hdC⟩ hd
    · exact retune₁_proper d hd hdC
  have hnm : ∀ d : D₂.below (Finset.univ, 1), ¬ mute₂ d.1 := fun d =>
    not_mute₂_of_low (by decide) d
  have hg1 : ∀ d : D₂.below (Finset.univ, 1), D₂.grade d.1 = 1 := fun d =>
    le_antisymm d.2.2 (D₂.grade_pos _)
  -- every label is at most the controller's
  have hle_top : ∀ d : D₂.below (Finset.univ, 1), q' d ≤ x₁' := by
    intro d
    rcases one_cases (hnm d) d.2.2 with h | h | h | h
    · rw [show d = ⟨H₀old, memA le_rfl⟩ from Subtype.ext h, hv_H₀old]; exact hx01
    · rw [show d = ⟨H₀new, memB le_rfl⟩ from Subtype.ext h, hv_H₀new]
    · rw [show d = ⟨U_H, memU₁⟩ from Subtype.ext h, hv_U_H]
    · rw [hv_proper d h]; exact hvx1
  refine ⟨q', ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- orderly
    intro d
    change q' d = extVisibilityReplace (q' d) (D₂.grade d.1) (D₂.grade d.1)
    rw [hg1 d]
    rcases one_cases (hnm d) d.2.2 with h | h | h | h
    · rw [show d = ⟨H₀old, memA le_rfl⟩ from Subtype.ext h, hv_H₀old]; exact hx0v.symm
    · rw [show d = ⟨H₀new, memB le_rfl⟩ from Subtype.ext h, hv_H₀new]; exact hx1v.symm
    · rw [show d = ⟨U_H, memU₁⟩ from Subtype.ext h, hv_U_H]; exact hx1v.symm
    · rw [hv_proper d h]; exact hvP_vis.symm
  · -- locality
    intro Sig
    obtain ⟨x, hx⟩ := Sig
    rcases one_cases (hnm ⟨x, hx⟩) hx.2 with rfl | rfl | rfl | hxP
    · -- the old occurrence: the limit step
      refine (Witness.stepLimit 1 2 hvx0 hvP_vis hx0v).transformsTo fun d => ?_
      rw [gTop_of_le (K := 1) (k := D₂.grade d.1) (d.2.2.trans grade_H₀old.le), min_eq_left le_top]
      change min (q' (CellScheme.below.incl ⟨H₀old, hx⟩ d)) (q' ⟨H₀old, memA le_rfl⟩) = _
      rw [hv_H₀old]
      rcases below_H₀old_cases d with hd | hd
      · rw [show CellScheme.below.incl ⟨H₀old, hx⟩ d = ⟨H₀old, memA le_rfl⟩ from Subtype.ext hd,
          hv_H₀old, min_self, rows₃_E_H₀old_self d hd, stepShifter_of_ge (ω2_ge 1)]
      · rw [hv_proper _ hd, min_eq_left hvx0, rows₃_E_one_proper grade_H₀old d hd,
          stepShifter_of_lt (a := v₀) v₀_ne_bot v₀_lt_ω2']
    · -- the copy: the limit step
      refine (Witness.stepLimit 1 2 hvx1 hvP_vis hx1v).transformsTo fun d => ?_
      rw [gTop_of_le (K := 1) (k := D₂.grade d.1) (d.2.2.trans grade_H₀new.le), min_eq_left le_top]
      change min (q' (CellScheme.below.incl ⟨H₀new, hx⟩ d)) (q' ⟨H₀new, memB le_rfl⟩) = _
      rw [hv_H₀new]
      rcases below_H₀new_cases' d with hd | hd
      · rw [show CellScheme.below.incl ⟨H₀new, hx⟩ d = ⟨H₀new, memB le_rfl⟩ from Subtype.ext hd,
          hv_H₀new, min_self, rows₃_E_H₀new_self d hd, stepShifter_of_ge (ω2_ge 1)]
      · rw [hv_proper _ hd, min_eq_left hvx1, rows₃_E_one_proper grade_H₀new d hd,
          stepShifter_of_lt (a := v₀) v₀_ne_bot v₀_lt_ω2']
    · -- the controller: the limit step raised at the separating value
      refine ((Witness.stepLimit 1 2 hvx0 hvP_vis hx0v).raise 1 (fun _ hk => gTop_bot hk)
        (ξ := ω2 2) (by rw [fp_ω2]; omega) hx1v).transformsTo fun d => ?_
      rw [gTop_of_le (K := 1) (k := D₂.grade d.1) (below_U_H_mem d).2, min_eq_left le_top]
      change min (q' (CellScheme.below.incl ⟨U_H, hx⟩ d)) (q' ⟨U_H, memU₁⟩) = _
      rw [hv_U_H]
      rcases one_cases (not_mute_below_U_H d) (below_U_H_mem d).2 with hd | hd | hd | hd
      · rw [show CellScheme.below.incl ⟨U_H, hx⟩ d = ⟨H₀old, memA le_rfl⟩ from Subtype.ext hd,
          hv_H₀old, min_eq_left hx01, rows₃_E_U_H_H₀old d hd,
          raiseShifter_of_lt (ofOrd_lt_ofOrd.mpr (ω2_lt_ω2 (a := 1) (b := 2) (by decide))),
          stepShifter_of_ge (ω2_ge 1)]
      · rw [show CellScheme.below.incl ⟨U_H, hx⟩ d = ⟨H₀new, memB le_rfl⟩ from Subtype.ext hd,
          hv_H₀new, min_self, rows₃_E_U_H_new d (Or.inl hd)]
        by_cases hb : x₀' = ⊥
        · rw [raiseShifter_of_bot (σ := stepShifter 2 vP x₀') (ξ := ω2 2) (c := x₁')
            (a := ofOrd (ω2 2)) (by rw [stepShifter_of_ge (ω2_ge 2)]; exact hb)]
          exact hcoup' hb
        · rw [raiseShifter_of_ge (σ := stepShifter 2 vP x₀') (c := x₁') le_rfl
            (by rw [stepShifter_of_ge (ω2_ge 2)]; exact hb),
            stepShifter_of_ge (ω2_ge 2), max_eq_right hx01]
      · rw [show CellScheme.below.incl ⟨U_H, hx⟩ d = ⟨U_H, memU₁⟩ from Subtype.ext hd,
          hv_U_H, min_self, rows₃_E_U_H_new d (Or.inr hd)]
        by_cases hb : x₀' = ⊥
        · rw [raiseShifter_of_bot (σ := stepShifter 2 vP x₀') (ξ := ω2 2) (c := x₁')
            (a := ofOrd (ω2 2)) (by rw [stepShifter_of_ge (ω2_ge 2)]; exact hb)]
          exact hcoup' hb
        · rw [raiseShifter_of_ge (σ := stepShifter 2 vP x₀') (c := x₁') le_rfl
            (by rw [stepShifter_of_ge (ω2_ge 2)]; exact hb),
            stepShifter_of_ge (ω2_ge 2), max_eq_right hx01]
      · rw [hv_proper _ hd, min_eq_left hvx1, rows₃_E_one_proper grade_U_H d hd,
          raiseShifter_of_lt (v₀_lt_ω2 2), stepShifter_of_lt (a := v₀) v₀_ne_bot v₀_lt_ω2']
    · -- a proper cell: the constant row
      have hgx : D₂.grade x = 1 := hg1 ⟨x, hx⟩
      have hnx : ¬ mute₂ x := hnm ⟨x, hx⟩
      have hbelow : ∀ d : D₂.below (D₂.cell x), IsProper d.1 := fun d =>
        isProper_of_below hnx (hmute_below₂ x d.1 hnx d.2) d.2 (d.2.2.trans hgx.le) hxP
      refine transformsTo_congr rfl rfl ?_ (transformsTo_const_of_ne_bot (w := vP)
        (fun d => d.2.2.trans hgx.le) (p := rows₃.E x)
        (fun d => by rw [rows₃_E_one_proper hgx d (hbelow d)]; exact ofOrd_ne_bot _) hvP_vis)
      funext d
      rw [hv_proper _ (hbelow d), hv_proper _ hxP, min_self]
  · -- availability
    intro Sig Xi₀ hs hg
    rcases one_cases (hnm Xi₀) Xi₀.2.2 with h | h | h | h
    · refine ⟨Xi₀, rfl, ?_⟩
      rw [show Xi₀ = ⟨H₀old, memA le_rfl⟩ from Subtype.ext h, hv_H₀old]
      rw [h] at hs
      rcases one_cases (hnm Sig) Sig.2.2 with h' | h' | h' | h'
      · rw [show Sig = ⟨H₀old, memA le_rfl⟩ from Subtype.ext h', hv_H₀old]
      · exfalso
        exact three_not_mem_scope_castAdd (family₀.e H₀X₀) (hs (by rw [h', scope_H₀new]; decide))
      · exfalso
        refine three_not_mem_scope_castAdd (family₀.e H₀X₀) (hs ?_)
        rw [h']; change (3 : Fin 4) ∈ (D₂.cell U_H).1; rw [cell_U_H]; exact Finset.mem_univ _
      · rw [hv_proper Sig h']; exact hvx0
    · refine ⟨Xi₀, rfl, ?_⟩
      rw [show Xi₀ = ⟨H₀new, memB le_rfl⟩ from Subtype.ext h, hv_H₀new]
      rw [h, scope_H₀new] at hs
      rcases one_cases (hnm Sig) Sig.2.2 with h' | h' | h' | h'
      · exfalso
        refine absurd (hs ?_) (by decide : (0 : Fin 4) ∉ ({1, 2, 3} : Finset (Fin 4)))
        rw [h']; exact zero_mem_scope_castAdd H₀X₀ rfl
      · rw [show Sig = ⟨H₀new, memB le_rfl⟩ from Subtype.ext h', hv_H₀new]
      · exfalso
        refine absurd (hs ?_) (by decide : (0 : Fin 4) ∉ ({1, 2, 3} : Finset (Fin 4)))
        rw [h']; change (0 : Fin 4) ∈ (D₂.cell U_H).1; rw [cell_U_H]; exact Finset.mem_univ _
      · rw [hv_proper Sig h']; exact hvx1
    · refine ⟨Xi₀, rfl, ?_⟩
      rw [show Xi₀ = ⟨U_H, memU₁⟩ from Subtype.ext h, hv_U_H]
      exact hle_top Sig
    · refine ⟨Xi₀, rfl, ?_⟩
      have hS : IsProper Sig.1 :=
        isProper_of_below (hnm Xi₀) (hnm Sig)
          ⟨hs, by change D₂.grade Sig.1 ≤ D₂.grade Xi₀.1; rw [hg1 Sig, hg1 Xi₀]⟩ Sig.2.2 h
      rw [hv_proper Sig hS, hv_proper Xi₀ h]
  · -- capped agreement
    intro d
    by_cases hdC : GradedLe (D₂.cell d.1) (C, 1)
    · rw [hq'def, retune₁_in d hdC]
      have := hagree ⟨d.1, hdC⟩
      rw [show CellScheme.below.mono h ⟨d.1, hdC⟩ = d from Subtype.ext rfl] at this
      exact this.symm
    · rcases one_cases (hnm d) d.2.2 with h' | h' | h' | h'
      · rw [show d = ⟨H₀old, memA le_rfl⟩ from Subtype.ext h', hv_H₀old]; exact hag0
      · rw [show d = ⟨H₀new, memB le_rfl⟩ from Subtype.ext h', hv_H₀new, hq1]; exact hag1
      · rw [show d = ⟨U_H, memU₁⟩ from Subtype.ext h', hv_U_H]; exact hag1
      · rw [hv_proper d h', hqc d h']; exact hagree_sc.symm
  · -- literal preservation
    intro d
    exact retune₁_in _ d.2

end Retune


end VaughtConjecture.Knight
