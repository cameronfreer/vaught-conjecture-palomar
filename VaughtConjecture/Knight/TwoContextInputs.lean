/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteAssemblyInstance

/-! # The two inputs of the two-context experiment, and the three-cell family

* **Input A** is `semScheme₀` (`family₀`: level-three cells `a₁ = (t₀, ω+3)`, `a₂ = (t₀, ω+4)`).
* **Input B** is `semScheme₁` (`family₁`: one level-three cell `b₁ = (t₁, ω·2+3)`, the same proper
  row `v₀ = ω+1` and the same lower levels `H₀c`, `s₀c`), unconditional by the general grade-one
  reduction `Family.properToFull_of_S₁`: every family whose level-one cells are all the shared
  witness `H₀c` is bountiful, by `family₀`'s argument.
* **The three-cell family** `family₂` (`S₃ = {a₁, a₂, b₁}`) holds both inputs' level-three cells
  over the shared lower levels; it is legal and bountiful (`semScheme₂`) and hosts the mixed
  controllers of the glued domain (`Knight/TwoContextGlue.lean`).

The two inputs differ above the shared lower levels (`family₁_distinct_from_family₀`).
Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

section General
variable {F : Family st₀}

/-- A cell of graded index `(univ, 1)` is a level-one cell. -/
theorem Family.exists_S₁_of_cellX {w : F.X} (h : F.cellX w = (Finset.univ, 1)) :
    ∃ H : ↥F.S₁, w = .inr (.inl H) := by
  rcases w with c | H | s | a
  · exact absurd (congrArg Prod.fst h) (Prop3.scope_ne_univ c)
  · exact ⟨H, rfl⟩
  · exact absurd (congrArg Prod.snd h) (by decide : (2 : ℕ) ≠ 1)
  · exact absurd (congrArg Prod.snd h) (by decide : (3 : ℕ) ≠ 1)


/-- **Step 4**: the constant labelling respects the semantics on the grade-one lower set. -/
theorem Family.respects_constLabel_one_of_S₁ (hS₁ : ∀ H ∈ F.S₁, H = H₀c) {u' : ExtOrd}
    (hu' : SelfVis 1 u') :
    RespectsSemanticsBelow F.rows (Finset.univ, 1)
      (F.constLabel (Finset.univ, 1) u') := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    have : SelfVis (F.cellX (F.e.symm d.1)).2
        (F.constLabel (Finset.univ, 1) u' d) := by
      change SelfVis _ (if (F.cellX (F.e.symm d.1)).2 ≤ 1 then u' else ⊥)
      split_ifs with hd
      · exact hu'.mono hd
      · exact selfVis_bot _
    exact this.symm
  · intro Sig
    have hSig1 : (F.cellX (F.e.symm Sig.1)).2 ≤ 1 := Sig.2.2
    have hgr : ∀ d : F.scheme.below (F.scheme.cell Sig.1),
        F.scheme.grade d.1 ≤ 1 := fun d => (d.2.2 : _ ≤ _).trans hSig1
    have htarget : (fun d : F.scheme.below (F.scheme.cell Sig.1) =>
        min (F.constLabel (Finset.univ, 1) u' (CellScheme.below.incl Sig d))
          (F.constLabel (Finset.univ, 1) u' Sig)) = fun _ => u' := by
      funext d
      change min (if (F.cellX (F.e.symm d.1)).2 ≤ 1 then u' else ⊥)
        (if (F.cellX (F.e.symm Sig.1)).2 ≤ 1 then u' else ⊥) = u'
      have hd1 : (F.cellX (F.e.symm d.1)).2 ≤ 1 := hgr d
      rw [ite_eq_left hd1, ite_eq_left hSig1, min_self]
    refine transformsTo_congr rfl rfl htarget.symm ?_
    rcases hx : F.e.symm Sig.1 with c | H | s | a
    · -- a proper cell: the constant source `v`
      have hc1 : c.gradeP ≤ 1 := by rw [hx] at hSig1; exact hSig1
      have hsrc : F.rows.E Sig.1 = fun _ => F.v := by
        funext d
        change F.rowX (F.e.symm Sig.1) _ = _
        rw [hx]
        change (if c.gradeP ≤ 1 then F.v else ⊥) = _
        rw [ite_eq_left hc1]
      exact transformsTo_congr rfl hsrc.symm rfl (transformsTo_const_const hgr F.v_ne hu')
    · -- the level-one cell: every source entry is nonbottom
      apply transformsTo_const_of_ne_bot hgr _ hu'
      intro d
      change F.rowX (F.e.symm Sig.1) (F.e.symm d.1) ≠ ⊥
      rw [hx]
      have hH : H.1 = H₀c := hS₁ _ H.2
      rcases hd : F.e.symm d.1 with c' | H' | s' | a'
      · have hc' : c'.gradeP ≤ 1 := by have := hgr d; rw [Family.grade_eq, hd] at this; exact this
        rw [Family.rowX_H_inl F H c' hc', hH]
        exact H₀c_G_ne_bot hc'
      · rw [Family.rowX_H_H, hH, hS₁ _ H'.2, meet₁_self]
        exact H₀c_δ_ne_bot
      · exfalso
        have := hgr d
        rw [Family.grade_eq, hd] at this
        exact absurd this (by decide : ¬ ((2 : ℕ) ≤ 1))
      · exfalso
        have := hgr d
        rw [Family.grade_eq, hd] at this
        exact absurd this (by decide : ¬ ((3 : ℕ) ≤ 1))
    · exfalso; rw [hx] at hSig1; exact absurd hSig1 (by decide : ¬ ((2 : ℕ) ≤ 1))
    · exfalso; rw [hx] at hSig1; exact absurd hSig1 (by decide : ¬ ((3 : ℕ) ≤ 1))
  · intro Sig Xi₀ _ hg
    refine ⟨Xi₀, rfl, le_of_eq ?_⟩
    change (if (F.cellX (F.e.symm Sig.1)).2 ≤ 1 then u' else ⊥) =
      if (F.cellX (F.e.symm Xi₀.1)).2 ≤ 1 then u' else ⊥
    have : (F.cellX (F.e.symm Sig.1)).2 = (F.cellX (F.e.symm Xi₀.1)).2 :=
      hg
    rw [this]

/-- **Steps 2–4**: the grade-one relabelling for `F`, in the form of the reviewer's
reduction. -/
theorem Family.gradeOne_relabel_of_S₁ (hS₁ : ∀ H ∈ F.S₁, H = H₀c) :
    ∀ (q : F.scheme.below (Finset.univ, 1) → ExtOrd),
      RespectsSemanticsBelow F.rows (Finset.univ, 1) q →
      ∀ (γ u' : ExtOrd), SelfVis 1 γ → SelfVis 1 u' →
        min u' γ = min (q (F.cellOf (BJ := (Finset.univ, 1)) (.inl .s0)
          ⟨Finset.subset_univ _, le_rfl⟩)) γ →
        ∃ q' : F.scheme.below (Finset.univ, 1) → ExtOrd,
          RespectsSemanticsBelow F.rows (Finset.univ, 1) q' ∧
          (∀ d, min (q' d) γ = min (q d) γ) ∧
          q' (F.cellOf (BJ := (Finset.univ, 1)) (.inl .s0)
            ⟨Finset.subset_univ _, le_rfl⟩) = u' := by
  intro q hq γ u' _ hu' hag
  set s0c := F.cellOf (BJ := (Finset.univ, 1)) (.inl .s0) ⟨Finset.subset_univ _, le_rfl⟩
    with hs0c
  by_cases hu : q s0c < γ
  · -- step 3: below the cap, the new value is the old one
    have heq : u' = q s0c := by
      rw [min_eq_left hu.le] at hag
      rcases lt_or_ge u' γ with h | h
      · rwa [min_eq_left h.le] at hag
      · rw [min_eq_right h] at hag
        exact absurd hag (ne_of_gt hu)
    exact ⟨q, hq, fun _ => rfl, heq.symm⟩
  · have hγu : γ ≤ q s0c := not_lt.mp hu
    have hγu' : γ ≤ u' := by
      rw [min_eq_right hγu] at hag
      by_contra h
      rw [min_eq_left (not_le.mp h).le] at hag
      exact (ne_of_lt (not_le.mp h)) hag
    -- step 2: every value of `q` is at least `γ`
    have hq_ge : ∀ d, γ ≤ q d := by
      intro d
      rcases hd : F.e.symm d.1 with c | H | s | a
      · have hc : c.gradeP = 1 := by
          have h1 : (F.cellX (F.e.symm d.1)).2 ≤ 1 := d.2.2
          rw [hd] at h1
          have h1' : c.gradeP ≤ 1 := h1
          have := c.gradeP_pos
          omega
        have hd_eq : d = F.cellOf (.inl c)
            ⟨Finset.subset_univ _, by change c.gradeP ≤ 1; omega⟩ := by
          apply Subtype.ext
          change d.1 = F.e (.inl c)
          rw [← hd, Equiv.apply_symm_apply]
        rw [hd_eq, F.respects_full_const hq le_rfl (c' := Prop3.s0) hc rfl]
        exact hγu
      · -- availability lifts `s0` to the (unique) level-one cell
        obtain ⟨Xi, hcell, hle⟩ := hq.availability s0c d
          (by
            change (F.cellX (F.e.symm (F.e (.inl .s0)))).1 ⊆
              (F.cellX (F.e.symm d.1)).1
            rw [Equiv.symm_apply_apply, hd]
            exact Finset.subset_univ _)
          (by
            change (F.cellX (F.e.symm (F.e (.inl .s0)))).2 =
              (F.cellX (F.e.symm d.1)).2
            rw [Equiv.symm_apply_apply, hd]
            rfl)
        have hXi : Xi = d := by
          have h1 : F.cellX (F.e.symm Xi.1) = (Finset.univ, 1) := by
            have := hcell
            rw [Family.cell_eq, Family.cell_eq, hd] at this
            exact this
          obtain ⟨H', hH'⟩ := F.exists_S₁_of_cellX h1
          apply Subtype.ext
          rw [← Equiv.apply_symm_apply F.e Xi.1, ← Equiv.apply_symm_apply F.e d.1,
            hH', hd, Subtype.ext ((hS₁ _ H'.2).trans (hS₁ _ H.2).symm)]
        rw [hXi] at hle
        exact hγu.trans hle
      · exfalso
        have h1 : (F.cellX (F.e.symm d.1)).2 ≤ 1 := d.2.2
        rw [hd] at h1
        exact absurd h1 (by decide : ¬ ((2 : ℕ) ≤ 1))
      · exfalso
        have h1 : (F.cellX (F.e.symm d.1)).2 ≤ 1 := d.2.2
        rw [hd] at h1
        exact absurd h1 (by decide : ¬ ((3 : ℕ) ≤ 1))
    -- step 4: the constant labelling `u'`
    refine ⟨F.constLabel (Finset.univ, 1) u', F.respects_constLabel_one_of_S₁ hS₁ hu', ?_, ?_⟩
    · intro d
      change min (if (F.cellX (F.e.symm d.1)).2 ≤ 1 then u' else ⊥) γ = min (q d) γ
      have hd1 : (F.cellX (F.e.symm d.1)).2 ≤ 1 := d.2.2
      rw [ite_eq_left hd1, min_eq_right hγu', min_eq_right (hq_ge d)]
    · change (if (F.cellX (F.e.symm (F.e (.inl .s0)))).2 ≤ 1 then u' else ⊥) = u'
      rw [Equiv.symm_apply_apply]
      exact ite_eq_left (by change Prop3.s0.gradeP ≤ 1; decide)


/-- **The grade-one reduction for any family whose level-one cells are the shared witness.** -/
theorem Family.properToFull_of_S₁ (hS₁ : ∀ H ∈ F.S₁, H = H₀c) : F.ProperToFull :=
  F.properToFull_of_relabel ((F.relabel_iff_gradeOne).mpr (F.gradeOne_relabel_of_S₁ hS₁))

end General

/-! ## The second input: cap `γ₁ = ω·2 + 3` -/

noncomputable def γ₁ : ExtOrd := ofOrd (Ordinal.omega0 * (2 : ℕ) + (3 : ℕ))

theorem γ₁_vis : SelfVis 3 γ₁ := by
  unfold γ₁; rw [selfVis_ofOrd_iff, finitePart_mul_add]
theorem γ₁_mem : γ₁ ∈ codedAlphabet 3 T₀ := mem_codedAlphabet_of (by decide) (by decide)
theorem v₀_le_γ₁ : v₀ ≤ γ₁ := by
  unfold v₀ γ₁; rw [ofOrd_le_ofOrd]
  exact add_le_add (mul_le_mul_right (Nat.cast_le.mpr (by decide : (1 : ℕ) ≤ 2)) _)
    (Nat.cast_le.mpr (by decide : (1 : ℕ) ≤ 3))
theorem γ₁_ne_γ₀ : γ₁ ≠ γ₀ := by
  unfold γ₁ γ₀
  intro h
  have h' := congrArg finitePart (ofOrd_inj.mp h)
  rw [finitePart_mul_add, finitePart_mul_add] at h'
  exact absurd h' (by decide)

/-- **The second base core**: the same proper row, cap `γ₁`. -/
noncomputable def t₁ : Core3 (gradeP := Prop3.gradeP) (T := T₀) where
  F c := if c.gradeP ≤ 1 then v₀ else ⊥
  γ := γ₁
  F_mem c _ := by
    split_ifs
    · exact v₀_mem
    · exact bot_mem_codedAlphabet 3 T₀
  F_bot c hc := absurd hc (by have := c.gradeP_le_two; omega)
  γ_mem := γ₁_mem
  γ_vis := γ₁_vis
  F_le c := by
    split_ifs
    · exact v₀_le_γ₁
    · exact bot_le
  F_orderly c _ := by
    split_ifs with h
    · exact v₀_vis.mono h
    · exact selfVis_bot _

theorem t₁_F : t₁.F = t₀.F := rfl

/-- The witnesses of `t₁` are those of `t₀`: they depend on the proper row only. -/
theorem t₁_wit1 : witness1 st₀.hT t₁.F (t₁.orderly st₀) = H₀c := rfl
theorem t₁_wit2 : t₁.wit2 st₀ = s₀c := rfl

noncomputable def b₁ : CappedCore3 Prop3.gradeP T₀ := ⟨t₁, γ₁, γ₁_mem, γ₁_vis, le_rfl⟩

/-- **The second family**: the lower levels of `family₀`, one level-three cell `b₁`. -/
noncomputable def family₁ : Family st₀ where
  v := v₀
  v_ne := ofOrd_ne_bot _
  v_vis := v₀_vis
  v_coded := Or.inr ⟨1, 1, by omega, rfl⟩
  S₁ := {H₀c, H₁c}
  S₂ := {s₀c}
  S₃ := {b₁}
  ne₁ := ⟨H₀c, Finset.mem_insert_self _ _⟩
  ne₂ := ⟨s₀c, Finset.mem_singleton_self _⟩
  ne₃ := ⟨b₁, Finset.mem_singleton_self _⟩
  const₁ := family₀.const₁
  const₂ := family₀.const₂
  bot₂ := family₀.bot₂
  const₃ a ha c c' hc hc' := by
    rw [Finset.mem_singleton.mp ha]; exact t₀_F_const hc hc'
  bot₃ a ha c hc := by
    rw [Finset.mem_singleton.mp ha]; exact t₀_F_bot hc
  wit₂ := family₀.wit₂
  wit₃₁ a ha := by
    rw [Finset.mem_singleton.mp ha]; exact Finset.mem_insert_self _ _
  wit₃₂ a ha := by
    rw [Finset.mem_singleton.mp ha]; exact Finset.mem_singleton_self _

theorem family₁_S₁ : ∀ H ∈ family₁.S₁, H = H₀c := fun _ h => mem_S₁_eq h

theorem family₁_properToFull : family₁.ProperToFull := family₁.properToFull_of_S₁ family₁_S₁

/-- **The second unconditional three-point input.** -/
noncomputable def semScheme₁ : SemScheme 3 := family₁.toSemScheme family₁_properToFull

theorem family₁_not_mute : family₁.rowX (.inl .s0) (.inl .s0) ≠ ⊥ := by
  change (if Prop3.s0.gradeP ≤ 1 then v₀ else ⊥) ≠ ⊥
  rw [ite_eq_left (by decide)]
  exact ofOrd_ne_bot _

/-- The two inputs differ above the shared lower levels: the level-three diagonals are the two
caps `γ₁ ≠ γ₀`. -/
theorem family₁_distinct_from_family₀ :
    family₁.rowX (.inr (.inr (.inr ⟨b₁, Finset.mem_singleton_self _⟩)))
        (.inr (.inr (.inr ⟨b₁, Finset.mem_singleton_self _⟩))) ≠
      family₀.rowX (.inr (.inr (.inr ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)))
        (.inr (.inr (.inr ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩))) := by
  rw [Family.rowX_a_a, Family.rowX_a_a]
  change min (meet₃ st₀ t₁ t₁) (min γ₁ γ₁) ≠ min (meet₃ st₀ t₀ t₀) (min γ₀ γ₀)
  rw [CappedCore3.meet₃_self', CappedCore3.meet₃_self', min_self, min_self]
  change min γ₁ γ₁ ≠ min γ₀ γ₀
  rw [min_self, min_self]
  exact γ₁_ne_γ₀


/-- **The three-cell family**: both inputs' level-three cells over the shared lower levels. -/
noncomputable def family₂ : Family st₀ where
  v := v₀
  v_ne := ofOrd_ne_bot _
  v_vis := v₀_vis
  v_coded := Or.inr ⟨1, 1, by omega, rfl⟩
  S₁ := {H₀c, H₁c}
  S₂ := {s₀c}
  S₃ := {a₁, a₂, b₁}
  ne₁ := ⟨H₀c, Finset.mem_insert_self _ _⟩
  ne₂ := ⟨s₀c, Finset.mem_singleton_self _⟩
  ne₃ := ⟨a₁, Finset.mem_insert_self _ _⟩
  const₁ := family₀.const₁
  const₂ := family₀.const₂
  bot₂ := family₀.bot₂
  const₃ a ha c c' hc hc' := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact t₀_F_const hc hc'
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact t₀_F_const hc hc'
    · rw [Finset.mem_singleton.mp ha]; exact t₀_F_const hc hc'
  bot₃ a ha c hc := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact t₀_F_bot hc
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact t₀_F_bot hc
    · rw [Finset.mem_singleton.mp ha]; exact t₀_F_bot hc
  wit₂ := family₀.wit₂
  wit₃₁ a ha := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_insert_self _ _
    · rw [Finset.mem_singleton.mp ha]; exact Finset.mem_insert_self _ _
  wit₃₂ a ha := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_singleton_self _
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_singleton_self _
    · rw [Finset.mem_singleton.mp ha]; exact Finset.mem_singleton_self _

theorem family₂_S₁ : ∀ H ∈ family₂.S₁, H = H₀c := fun _ h => mem_S₁_eq h
theorem family₂_properToFull : family₂.ProperToFull := family₂.properToFull_of_S₁ family₂_S₁

/-- **The three-cell domain**, unconditional: the mixed controllers' rows live here. -/
noncomputable def semScheme₂ : SemScheme 3 := family₂.toSemScheme family₂_properToFull



end VaughtConjecture.Knight
