/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledGradeThreeOrbit

/-! # The frozen coupled semantics is not bountiful

A no-go for the frozen rows `rows₃`, after the research scout `BottomFace.lean` (draft #319,
2026-09-06).  Nothing in the construction is changed: coding, consistency, availability and the
realization of the prescribed pair (`coupled_realization`) stand; the reduction
`rows₃_isBountiful_of` stands; what fails is its hypothesis `ProperToFull₃Low`, hence
`rows₃.IsBountiful` (`rows₃_not_bountiful`), so `semSchemeCoupled` has no instance.

**The legal input** (`bottomFaceB_respects`, `bottomFace_respects`): on input B's own family put
`⊥` at every proper cell and the ordinal `3` at the three full-scope cells `H₀`, `s₀`, `b₁`.  This
respects input B's semantics — locality at the full cells by the limit step at `ω·2`
(`Witness.stepLimit`: the proper sources are `⊥` or in the block at `ω`, the witness and cap
sources in the block at `ω·2`), the all-bottom transformation at the proper cells, availability
because every full label is `3` — and, transported to the actual B face `({1,2,3}, 3)` of the
coupled scheme, respects the frozen rows there (they are input B's).

**The obstruction** (`ub₁_eq_bot_of_proper_bot`), from the necessary constraints already
compiled: a bottom proper grade-one label `v` gives `z₁ ≤ R₃ v = ⊥` (the moving orbit
`A₁c_le_R₃_of_respects`), then `z₂ = ⊥` (`A₂c_eq_bot_of_A₁c`), then `min x₀ w = ⊥`
(`A₂c_eq_min_of_respects`); if `w ≠ ⊥` then `x₀ = ⊥`, so `x₁ = ⊥` (`U_H_eq_bot_of_H₀old`), and
`w ≤ q U_S ≤ x₁` (`ub₁_le_U_S_of_respects`, `U_S_le_U_H_of_respects`) forces `w = ⊥`.  But the
copy of `b₁` is labelled like `b₁`'s controller (`b₁new_eq_ub₁_of_respects`), and the face puts
`3` there (`bottomFace_no_extension`).  So the obligation fails at the pair `({1,2,3}, 3)`, cap
`⊥`, second labelling `qL` (`not_properToFull₃Low`).

**What the chain identifies.**  Every link is a construction-owned full row or an inherited
orbit: `ω+1 ↦ ω+3` in `a₁`'s controller's row (inherited from input A's cap `a₁`, and equally
present in the old cap's own row); `ω+3 ↦ ω+4` in `a₂`'s controller's row (inherited from `a₂`);
`b₁`'s controller reading the *same* source `ω+4` at the old occurrence `H₀old` and at `a₂`'s
controller (construction-owned: the lowered labelling `qL` is that row); the separating source
pair `ω·2+1 ↦ ω·2+2` in the grade-one controller's row (construction-owned); the antitone
suppressor chain `w ≤ q U_S ≤ q U_H`.  A repair must support this bottom face *and* the original
prescribed pair; moving one source to a new block need not suffice, since locality with the
inherited A rows can force the same interaction back.  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-- **A bottom proper label forces the high label to bottom**: `v = ⊥` gives `z₁ ≤ R₃ ⊥ = ⊥`,
then `z₂ = ⊥`, then `min x₀ w = ⊥`; if `w ≠ ⊥` then `x₀ = ⊥`, the grade-one coupling gives
`x₁ = ⊥`, and `w ≤ q U_S ≤ x₁` — so `w = ⊥` either way. -/
theorem ub₁_eq_bot_of_proper_bot
    {q : D₂.below (Finset.univ, 3) → ExtOrd}
    (hq : RespectsSemanticsBelow rows₃ (Finset.univ, 3) q)
    (d : D₂.below (Finset.univ, 3)) (hp : IsProper d.1)
    (hg : D₂.grade d.1 = 1) (hb : q d = ⊥) :
    q ⟨ub₁, memub₁₃⟩ = ⊥ := by
  have hA : q ⟨A₁c, memA₁c₃⟩ = ⊥ := by
    have h := A₁c_le_R₃_of_respects hq d hp hg
    rw [hb, extVisibilityReplace_bot] at h
    exact le_bot_iff.mp h
  have hA2 := A₂c_eq_bot_of_A₁c hq hA
  rw [A₂c_eq_min_of_respects hq] at hA2
  rcases min_eq_bot.mp hA2 with h0 | hw
  · have h1 := U_H_eq_bot_of_H₀old
      (hq.mono (show GradedLe (Finset.univ, 1) (Finset.univ, 3) from
        ⟨Finset.Subset.refl _, by decide⟩)) h0
    have h2 := U_S_le_U_H_of_respects
      (hq.mono (show GradedLe (Finset.univ, 2) (Finset.univ, 3) from
        ⟨Finset.Subset.refl _, by decide⟩))
    exact le_bot_iff.mp ((ub₁_le_U_S_of_respects hq).trans (h2.trans h1.le))
  · exact hw

/-- The bottom face on input B's family: `⊥` at every proper cell, the ordinal `3` at the three
full-scope cells. -/
noncomputable def bottomFaceX : family₁.X → ExtOrd
  | .inl _ => ⊥
  | .inr _ => ofOrd 3

/-- The bottom face as a labelling of input B's full lower set. -/
noncomputable def bottomFaceB (d : C₁.below (Finset.univ, 3)) : ExtOrd :=
  bottomFaceX (family₁.e.symm d.1)

theorem bottomFaceX_selfVis (x : family₁.X) : SelfVis (family₁.cellX x).2 (bottomFaceX x) := by
  rcases img_cases x with ⟨c, rfl⟩ | rfl | rfl | rfl
  · exact selfVis_bot _
  all_goals
    simp only [bottomFaceX, Family.cellX]
    rw [selfVis_ofOrd_iff, show (3 : Ordinal) = ((3 : ℕ) : Ordinal) from rfl,
      Value.finitePart_natCast]
  all_goals omega

/-- The limit step at `ω·2` sends every source of a full-scope row of input B to the bottom
face's value: proper sources are `⊥` or in the block at `ω`, witness and cap sources in the block
at `ω·2`. -/
theorem bottomFace_step (x y : family₁.X)
    (hx : (family₁.cellX x).1 = Finset.univ)
    (hxy : GradedLe (family₁.cellX y) (family₁.cellX x)) :
    stepShifter 2 ⊥ (ofOrd 3) (family₁.rowX x y) = bottomFaceX y := by
  rcases img_cases x with ⟨c, rfl⟩ | rfl | rfl | rfl
  · have hn : c.scope ≠ Finset.univ := by cases c <;> decide
    exact False.elim (hn hx)
  · rcases img_cases y with ⟨c, rfl⟩ | rfl | rfl | rfl
    · have hc : c.gradeP ≤ 1 := hxy.2
      rw [family₁.rowX_H_inl _ c hc, H₀c_G_v₀ hc, v₀_num]
      exact stepShifter_of_lt (ofOrd_ne_bot _)
        (ofOrd_lt_ofOrd.mpr (ω2_zero ▸ ω1j_lt_ω2 1 0))
    · rw [family₁.rowX_H_H, meet₁_self, H₀c_δ_num]
      exact stepShifter_of_ge (ofOrd_le_ofOrd.mpr (le_self_add))
    · have : (2 : ℕ) ≤ 1 := hxy.2; omega
    · have : (3 : ℕ) ≤ 1 := hxy.2; omega
  · rw [rowX₁_eq, embX₁_s₀]
    rcases img_cases y with ⟨c, rfl⟩ | rfl | rfl | rfl
    · rw [show embX₁ (.inl c) = .inl c from rfl, rowX_s₀_inl]
      by_cases hc : c.gradeP ≤ 1
      · rw [s₀c_F_v₀ hc, v₀_num]
        exact stepShifter_of_lt (ofOrd_ne_bot _)
          (ofOrd_lt_ofOrd.mpr (ω2_zero ▸ ω1j_lt_ω2 1 0))
      · rw [s₀c_F_bot (by have := c.gradeP_le_two; omega), stepShifter_bot]; rfl
    · rw [embX₁_H₀, rowX_s₀_H, s₀c_γ_num]
      exact stepShifter_of_ge (ofOrd_le_ofOrd.mpr (le_self_add))
    · rw [embX₁_s₀, rowX_s₀_s, s₀c_γ_num]
      exact stepShifter_of_ge (ofOrd_le_ofOrd.mpr (le_self_add))
    · have : (3 : ℕ) ≤ 2 := hxy.2; omega
  · rw [rowX₁_eq, embX₁_b₁]
    rcases img_cases y with ⟨c, rfl⟩ | rfl | rfl | rfl
    · rw [show embX₁ (.inl c) = .inl c from rfl, rowX_b₁_inl]
      by_cases hc : c.gradeP ≤ 1
      · rw [t₀_F_v₀ hc, v₀_num]
        exact stepShifter_of_lt (ofOrd_ne_bot _)
          (ofOrd_lt_ofOrd.mpr (ω2_zero ▸ ω1j_lt_ω2 1 0))
      · rw [t₀_F_bot (by have := c.gradeP_le_two; omega), stepShifter_bot]; rfl
    · rw [embX₁_H₀, rowX_b₁_H, γ₁_num]
      exact stepShifter_of_ge (ofOrd_le_ofOrd.mpr (le_self_add))
    · rw [embX₁_s₀, rowX_b₁_s, γ₁_num]
      exact stepShifter_of_ge (ofOrd_le_ofOrd.mpr (le_self_add))
    · rw [embX₁_b₁, rowX_b₁_b₁, γ₁_num]
      exact stepShifter_of_ge (ofOrd_le_ofOrd.mpr (le_self_add))

theorem bottomFaceX_of_full {x : family₁.X} (hx : (family₁.cellX x).1 = Finset.univ) :
    bottomFaceX x = ofOrd 3 := by
  rcases img_cases x with ⟨c, rfl⟩ | rfl | rfl | rfl
  · have hn : c.scope ≠ Finset.univ := by cases c <;> decide
    exact False.elim (hn hx)
  all_goals rfl

theorem bottomFaceX_le (x : family₁.X) : bottomFaceX x ≤ ofOrd 3 := by
  cases x <;> simp only [bottomFaceX, bot_le, le_refl]

/-- **The bottom face respects input B's semantics** (locality by `Witness.stepLimit` at the full
cells, the all-bottom transformation at the proper cells; availability since every full label is
`3`). -/
theorem bottomFaceB_respects :
    RespectsSemanticsBelow family₁.rows (Finset.univ, 3) bottomFaceB where
  orderly d := (bottomFaceX_selfVis (family₁.e.symm d.1)).symm
  locality Sig := by
    by_cases hf : C₁.scope Sig.1 = Finset.univ
    · have hv : bottomFaceB Sig = ofOrd 3 := bottomFaceX_of_full hf
      have vis3 : SelfVis 3 (ofOrd 3) := by
        rw [selfVis_ofOrd_iff, show (3 : Ordinal) = ((3 : ℕ) : Ordinal) from rfl,
          Value.finitePart_natCast]
      refine (Witness.stepLimit 3 2 bot_le (selfVis_bot _) vis3).transformsTo fun d => ?_
      have hg : C₁.grade d.1 ≤ 3 := (d.2.trans Sig.2).2
      rw [gTop_of_le hg, min_top_right, hv]
      change min (bottomFaceX (family₁.e.symm d.1)) (ofOrd 3) =
        stepShifter 2 ⊥ (ofOrd 3)
          (family₁.rowX (family₁.e.symm Sig.1) (family₁.e.symm d.1))
      rw [min_eq_left (bottomFaceX_le _)]
      exact (bottomFace_step _ _ hf d.2).symm
    · have hv : bottomFaceB Sig = ⊥ := by
        change bottomFaceX (family₁.e.symm Sig.1) = ⊥
        rcases img_cases (family₁.e.symm Sig.1) with ⟨c, he⟩ | he | he | he
        · rw [he]; rfl
        all_goals
          exfalso; apply hf
          change (family₁.cellX (family₁.e.symm Sig.1)).1 = Finset.univ
          rw [he]; rfl
      refine ⟨fun _ => ⊥, fun _ => ⊥, fun _ _ _ => le_rfl,
        fun n => (extVisibilityReplace_bot n n).symm, rfl,
        fun _ _ _ => le_rfl, fun _ k _ i _ => (extVisibilityReplace_bot k i).symm, ?_⟩
      intro d
      change min (bottomFaceB (CellScheme.below.incl Sig d)) (bottomFaceB Sig) = ⊥
      rw [hv, min_bot_right]
  availability Sig Xi₀ hs _ := by
    refine ⟨Xi₀, rfl, ?_⟩
    by_cases hf : C₁.scope Sig.1 = Finset.univ
    · have hfx : C₁.scope Xi₀.1 = Finset.univ := by
        change C₁.scope Sig.1 ⊆ C₁.scope Xi₀.1 at hs
        rw [hf] at hs
        exact Finset.univ_subset_iff.mp hs
      change bottomFaceX (family₁.e.symm Sig.1) ≤ bottomFaceX (family₁.e.symm Xi₀.1)
      exact (bottomFaceX_of_full (x := family₁.e.symm Sig.1) hf).le.trans
        (bottomFaceX_of_full (x := family₁.e.symm Xi₀.1) hfx).ge
    · change bottomFaceX (family₁.e.symm Sig.1) ≤ _
      rcases img_cases (family₁.e.symm Sig.1) with ⟨c, he⟩ | he | he | he
      · rw [he]; exact bot_le
      all_goals
        exfalso; apply hf
        change (family₁.cellX (family₁.e.symm Sig.1)).1 = Finset.univ
        rw [he]; rfl

/-- The bottom face transported to the actual B face `({1,2,3}, 3)` of the coupled scheme. -/
noncomputable def bottomFace (d : D₂.below ({1, 2, 3}, 3)) : ExtOrd :=
  bottomFaceX (family₁.e.symm (retB d.1))

/-- **The bottom face respects the frozen rows on the B face** (the rows there are input B's). -/
theorem bottomFace_respects : RespectsSemanticsBelow rows₃ ({1, 2, 3}, 3) bottomFace := by
  apply (respects₃_iff_of_proper (by decide) bottomFace).mpr
  apply (respects_iff_B B_face_mem zero_not_mem_B 3 bottomFace).mpr
  have h := RespectsSemanticsBelow.cast image_fold_B.symm bottomFaceB_respects
  convert h using 1
  funext d
  change bottomFaceX (family₁.e.symm (retB ((eB B_face_mem zero_not_mem_B 3).symm d).1)) =
    bottomFaceX (family₁.e.symm d.1)
  apply congrArg (fun i => bottomFaceX (family₁.e.symm i))
  exact congrArg Subtype.val ((eB B_face_mem zero_not_mem_B 3).apply_symm_apply d)

theorem bottomFace_copyB (x : family₁.X) :
    bottomFace ⟨copyB (family₁.e x), copyB_mem _⟩ = bottomFaceX x := by
  change bottomFaceX (family₁.e.symm (retB (copyB (family₁.e x)))) = bottomFaceX x
  rw [retB_copyB, Equiv.symm_apply_apply]

/-- **No respecting labelling of `(univ, 3)` extends the bottom face**: the face puts `⊥` at the
proper cell `{1}` and `3` at the copy of `b₁`, but the copy is labelled like `b₁`'s controller,
which a bottom proper label forces to `⊥`. -/
theorem bottomFace_no_extension
    {q : D₂.below (Finset.univ, 3) → ExtOrd}
    (hq : RespectsSemanticsBelow rows₃ (Finset.univ, 3) q)
    (he : ∀ d : D₂.below ({1, 2, 3}, 3),
      q ⟨d.1, d.2.trans ⟨Finset.subset_univ _, le_rfl⟩⟩ = bottomFace d) : False := by
  let d : D₂.below (Finset.univ, 3) :=
    ⟨copyB (family₁.e (.inl Prop3.s1)),
      (copyB_mem _).trans ⟨Finset.subset_univ _, le_rfl⟩⟩
  have hp : IsProper d.1 := by
    refine ⟨Prop3.s1, ?_⟩
    change family₂.e.symm (ret₂ (copyB (family₁.e (.inl Prop3.s1)))) = .inl Prop3.s1
    rw [ret₂_copyB_X, Equiv.symm_apply_apply]; rfl
  have hg : D₂.grade d.1 = 1 := grade_copyB_eq _
  have hb : q d = ⊥ := (he ⟨d.1, copyB_mem _⟩).trans (bottomFace_copyB _)
  have hw := ub₁_eq_bot_of_proper_bot hq d hp hg hb
  have hbp := (he ⟨b₁new, copyB_mem _⟩).trans (bottomFace_copyB b₁X₁)
  have hbw := b₁new_eq_ub₁_of_respects hq
  have : (ofOrd 3 : ExtOrd) = ⊥ := hbp.symm.trans (hbw.trans hw)
  exact ofOrd_ne_bot _ this

/-- **The scope-changing obligation fails at grade three** (cap `⊥`, the second labelling `qL`). -/
theorem not_properToFull₃Low : ¬ ProperToFull₃Low := by
  intro H
  obtain ⟨q', hq', _, he⟩ := H ({1, 2, 3}, 3) 3 le_rfl
    (AmalgamationPlan.Plan.mem_gradedPlan.mpr ⟨B_face_mem, by decide, by decide⟩)
    (by decide)
    (AmalgamationPlan.Plan.mem_gradedPlan.mpr ⟨by decide, by decide, by decide⟩)
    ⟨Finset.subset_univ _, le_rfl⟩ bottomFace (fun d => qL d.1) ⊥ bottomFace_respects qL_respects
    (extVisibilityReplace_bot 3 3) (fun _ => by simp only [min_bot_right])
  exact bottomFace_no_extension hq' he

/-- **The frozen coupled semantics is not bountiful.** -/
theorem rows₃_not_bountiful : ¬ rows₃.IsBountiful := by
  intro H
  apply not_properToFull₃Low
  intro CI j _ hCI hC hBJ h p q γ hp hq hγ ha
  exact H CI (Finset.univ, j) hCI hBJ h
    (fun he => hC (congrArg Prod.fst he)) p q γ hp hq hγ ha

end VaughtConjecture.Knight
