/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FaceExtA

/-! # The B-face obligation of the two-context glue

**Result** (`faceExtB'`): the B-face obligation `FaceExtB'` holds.  Input B (`family₁`: `b₁`,
`H₀`, `s₀`, proper) sits inside the three-cell family; the free labels are at `a₁` and `a₂`.
Both are derived from **one mixed witness**: input B's own `b₁`-locality witness `(g, σ)`
(truncated above grade three), read at the sources `ω+3` and `ω+4` that `a₁`, `a₂` present to
`b₁`'s row (`MixedWitness`; the three level-three localities follow from it:
`MixedWitness.locality_b₁`, `locality_a₁`, `locality_a₂`, the latter two by capping).

**Agreement with `q` modulo `γ`** is the acceptance test, not automatic: the label at `a₁` is
settled by the **orbit equation** (`Witness.at_η₁`: under the guard, `σ (ω+3)` is the
`3`-replacement of `σ (ω+1)`), which forces the two witnesses' `ω+3`-values to agree modulo `γ`
from the agreement of their `ω+1`-values (`orbit_agree`); the label at `a₂` is free between
`σ (ω+3)` and input B's cap, and is set to meet `q a₂` modulo `γ` by raising or lowering `σ` on
the block-`ω` tail at `ω+4` (`Witness.raise`, `Witness.lower`).  When input B's cap agrees with
`q b₁` below `γ`, `q`'s own witness serves directly.  Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

section InputB

theorem le_top₁ (d : Cell C₁) : GradedLe (C₁.cell d) (Finset.univ, 3) :=
  ⟨Finset.subset_univ _, (C₁.grade_le_card_scope d).trans
    ((Finset.card_le_univ _).trans (by simp : Fintype.card (Fin 3) ≤ 3))⟩

noncomputable abbrev cell₁ (x : family₁.X) : C₁.below (Finset.univ, 3) := ⟨family₁.e x, le_top₁ _⟩

noncomputable abbrev b₁X₁ : family₁.X := .inr (.inr (.inr ⟨b₁, Finset.mem_singleton_self _⟩))
noncomputable abbrev H₀X₁ : family₁.X := .inr (.inl ⟨H₀c, Finset.mem_insert_self _ _⟩)
noncomputable abbrev s₀X₁ : family₁.X := .inr (.inr (.inl ⟨s₀c, Finset.mem_singleton_self _⟩))

theorem embX₁_b₁ : embX₁ b₁X₁ = b₁X := rfl
theorem embX₁_H₀ : embX₁ H₀X₁ = H₀X := rfl
theorem embX₁_s₀ : embX₁ s₀X₁ = s₀X := rfl

theorem embBelow₁_cell₁ (y : family₁.X) : embBelow₁ (cell₁ y) = cell₂ (embX₁ y) := by
  apply Subtype.ext
  change family₂.e (embX₁ (family₁.e.symm (family₁.e y))) = family₂.e (embX₁ y)
  rw [Equiv.symm_apply_apply]

theorem rowX₁_eq (x y : family₁.X) : family₁.rowX x y = family₂.rowX (embX₁ x) (embX₁ y) :=
  (rowX_embX₁ x y).symm

/-- Antitone probe in input B's family. -/
theorem probe_diag₁ {p : C₁.below (Finset.univ, 3) → ExtOrd}
    (hp : RespectsSemanticsBelow family₁.rows (Finset.univ, 3) p) (x y : family₁.X)
    (hs : (family₁.cellX y).1 ⊆ (family₁.cellX x).1)
    (hgr : (family₁.cellX y).2 ≤ (family₁.cellX x).2)
    (hrow : family₁.rowX x y = family₁.rowX x x) : p (cell₁ x) ≤ p (cell₁ y) := by
  have hle : GradedLe (family₁.scheme.cell (family₁.e y)) (family₁.scheme.cell (family₁.e x)) := by
    rw [Family.cell_e, Family.cell_e]; exact ⟨hs, hgr⟩
  have h := hp.ge_of_row_eq_diag (cell₁ x) ⟨family₁.e y, hle⟩ ?_ ?_
  · exact h
  · change family₁.rowX (family₁.e.symm (family₁.e x)) (family₁.e.symm (family₁.e y)) =
      family₁.rowX (family₁.e.symm (family₁.e x)) (family₁.e.symm (family₁.e x))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hrow]
  · change (family₁.scheme.cell (family₁.e y)).2 ≤ (family₁.scheme.cell (family₁.e x)).2
    rw [Family.cell_e, Family.cell_e]; exact hgr

/-- **The constraints on input B's labelling `p`**: `p b₁ ≤ p H₀, p s₀`. -/
theorem p_b₁_le_H {p : C₁.below (Finset.univ, 3) → ExtOrd}
    (hp : RespectsSemanticsBelow family₁.rows (Finset.univ, 3) p) :
    p (cell₁ b₁X₁) ≤ p (cell₁ H₀X₁) :=
  probe_diag₁ hp b₁X₁ H₀X₁ (Finset.Subset.refl _) (by change (1 : ℕ) ≤ 3; decide)
    (by rw [rowX₁_eq, rowX₁_eq, embX₁_b₁, embX₁_H₀, rowX_b₁_H, rowX_b₁_b₁])
theorem p_b₁_le_s {p : C₁.below (Finset.univ, 3) → ExtOrd}
    (hp : RespectsSemanticsBelow family₁.rows (Finset.univ, 3) p) :
    p (cell₁ b₁X₁) ≤ p (cell₁ s₀X₁) :=
  probe_diag₁ hp b₁X₁ s₀X₁ (Finset.Subset.refl _) (by change (2 : ℕ) ≤ 3; decide)
    (by rw [rowX₁_eq, rowX₁_eq, embX₁_b₁, embX₁_s₀, rowX_b₁_s, rowX_b₁_b₁])

theorem q_a₁_le_b₁ {q : C₂.below (Finset.univ, 3) → ExtOrd}
    (hq : RespectsSemanticsBelow family₂.rows (Finset.univ, 3) q) :
    q (cell₂ a₁X) ≤ q (cell₂ b₁X) :=
  probe_diag₂ hq a₁X b₁X (Finset.Subset.refl _) le_rfl (by rw [rowX_a₁_b₁, rowX_a₁_a₁])

/-! ### The cells of the three-cell family: images of input B, `a₁`, `a₂` -/

theorem a₁_ne_a₂ : a₁ ≠ a₂ := fun h => η₁_ne_γ₀ (congrArg CappedCore3.η h)

theorem cell₂_a₁_ne_a₂ : (cell₂ a₁X).1 ≠ (cell₂ a₂X).1 := by
  intro h
  have h' := family₂.e.injective h
  have : a₁ = a₂ := by
    have := congrArg (fun z : family₂.X => match z with
      | .inr (.inr (.inr b)) => b.1 | _ => a₁) h'
    exact this
  exact a₁_ne_a₂ this

theorem not_emb₁_a (i : Cell C₁) : emb₁ i ≠ (cell₂ a₁X).1 ∧ emb₁ i ≠ (cell₂ a₂X).1 := by
  have key : ∀ (a : CappedCore3 Prop3.gradeP T₀) (ha : a ∈ family₂.S₃), a ≠ b₁ →
      emb₁ i ≠ family₂.e (.inr (.inr (.inr ⟨a, ha⟩))) := by
    intro a ha hab h
    change family₂.e (embX₁ (family₁.e.symm i)) = family₂.e _ at h
    have h' := family₂.e.injective h
    rcases hw : family₁.e.symm i with c | H | s | b
    all_goals rw [hw] at h'
    · exact absurd h' (by simp [embX₁])
    · exact absurd h' (by simp [embX₁])
    · exact absurd h' (by simp [embX₁])
    · have hb : b.1 = a := by
        have := congrArg (fun z : family₂.X => match z with
          | .inr (.inr (.inr d)) => d.1 | _ => a) h'
        exact this
      have hb1 : b.1 = b₁ := Finset.mem_singleton.mp b.2
      exact hab (hb.symm.trans hb1)
  exact ⟨key a₁ (Finset.mem_insert_self _ _) a₁_ne_b₁,
    key a₂ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) a₂_ne_b₁⟩

theorem embBelow₁_injective : Function.Injective embBelow₁ := fun _ _ h =>
  Subtype.ext (emb₁_injective (congrArg Subtype.val h))

/-- Every cell of the three-cell family is an image of input B, or `a₁`, or `a₂`. -/
theorem cases₂' (d : C₂.below (Finset.univ, 3)) :
    (∃ c : C₁.below (Finset.univ, 3), embBelow₁ c = d) ∨ d = cell₂ a₁X ∨ d = cell₂ a₂X := by
  by_cases h3 : C₂.grade d.1 ≤ 2
  · obtain ⟨i, hi⟩ := exists_emb₁_of_grade_le_two d.1 h3
    exact Or.inl ⟨⟨i, le_top₁ i⟩, Subtype.ext hi⟩
  · rcases hw : family₂.e.symm d.1 with c | H | s | a
    · exfalso; apply h3
      change (family₂.cellX (family₂.e.symm d.1)).2 ≤ 2
      rw [hw]; exact c.gradeP_le_two
    · exfalso; apply h3
      change (family₂.cellX (family₂.e.symm d.1)).2 ≤ 2
      rw [hw]; change (1 : ℕ) ≤ 2; decide
    · exfalso; apply h3
      change (family₂.cellX (family₂.e.symm d.1)).2 ≤ 2
      rw [hw]; change (2 : ℕ) ≤ 2; decide
    · have ha : a.1 ∈ ({a₁, a₂, b₁} : Finset (CappedCore3 Prop3.gradeP T₀)) := a.2
      have hd : d.1 = family₂.e (.inr (.inr (.inr a))) := by
        rw [← hw, Equiv.apply_symm_apply]
      rcases Finset.mem_insert.mp ha with h | h
      · right; left
        apply Subtype.ext
        change d.1 = family₂.e a₁X
        rw [hd]
        have e : a = ⟨a₁, Finset.mem_insert_self _ _⟩ := Subtype.ext h
        rw [e]
      rcases Finset.mem_insert.mp h with h | h
      · right; right
        apply Subtype.ext
        change d.1 = family₂.e a₂X
        rw [hd]
        have e : a = ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩ := Subtype.ext h
        rw [e]
      · left
        refine ⟨cell₁ b₁X₁, Subtype.ext ?_⟩
        rw [embBelow₁_cell₁, embX₁_b₁]
        change family₂.e b₁X = d.1
        rw [hd]
        have e : a = ⟨b₁, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self _))⟩ := Subtype.ext (Finset.mem_singleton.mp h)
        rw [e]

open Classical in
/-- **The extension by two values**: input B's labelling on its cells, `x₁` at `a₁`, `x₂` at
`a₂`. -/
noncomputable def ext₁ (p : C₁.below (Finset.univ, 3) → ExtOrd) (x₁ x₂ : ExtOrd)
    (d : C₂.below (Finset.univ, 3)) : ExtOrd :=
  if h : ∃ c, embBelow₁ c = d then p (Classical.choose h) else if d = cell₂ a₁X then x₁ else x₂

theorem ext₁_emb (p : C₁.below (Finset.univ, 3) → ExtOrd) (x₁ x₂ : ExtOrd)
    (c : C₁.below (Finset.univ, 3)) : ext₁ p x₁ x₂ (embBelow₁ c) = p c := by
  classical
  unfold ext₁
  rw [dite_of_pos ⟨c, rfl⟩]
  congr 1
  exact embBelow₁_injective (Classical.choose_spec (⟨c, rfl⟩ : ∃ c', embBelow₁ c' = embBelow₁ c))

theorem ext₁_a₁ (p : C₁.below (Finset.univ, 3) → ExtOrd) (x₁ x₂ : ExtOrd) :
    ext₁ p x₁ x₂ (cell₂ a₁X) = x₁ := by
  classical
  unfold ext₁
  rw [dite_of_neg, ite_eq_left rfl]
  rintro ⟨c, hc⟩
  exact (not_emb₁_a c.1).1 (congrArg Subtype.val hc)

theorem ext₁_a₂ (p : C₁.below (Finset.univ, 3) → ExtOrd) (x₁ x₂ : ExtOrd) :
    ext₁ p x₁ x₂ (cell₂ a₂X) = x₂ := by
  classical
  unfold ext₁
  rw [dite_of_neg, ite_eq_right]
  · intro h; exact cell₂_a₁_ne_a₂ (congrArg Subtype.val h).symm
  · rintro ⟨c, hc⟩
    exact (not_emb₁_a c.1).2 (congrArg Subtype.val hc)

/-! ### The sources: the three level-three rows at every cell -/

theorem t₀_F_le_η₁ (c : Prop3) : t₀.F c ≤ η₁ := by
  change (if c.gradeP ≤ 1 then v₀ else ⊥) ≤ η₁
  split_ifs
  · exact v₀_le_η₁
  · exact bot_le

/-- The proper values of the level-three rows agree (each caps the shared proper row from above). -/
theorem rowX_a₁_inl (c : Prop3) : family₂.rowX a₁X (.inl c) = t₀.F c := by
  rw [Family.rowX_a_inl]; exact min_eq_left (t₀_F_le_η₁ c)
theorem rowX_a₂_inl (c : Prop3) : family₂.rowX a₂X (.inl c) = t₀.F c := by
  rw [Family.rowX_a_inl]; exact min_eq_left (t₀.F_le c)
theorem rowX_b₁_inl (c : Prop3) : family₂.rowX b₁X (.inl c) = t₀.F c := by
  rw [Family.rowX_a_inl]
  change min (t₀.F c) γ₁ = t₀.F c
  exact min_eq_left ((t₀.F_le c).trans γ₀_le_γ₁)

theorem t₀_F_cases (c : Prop3) : t₀.F c = v₀ ∨ t₀.F c = ⊥ := by
  change (if c.gradeP ≤ 1 then v₀ else ⊥) = v₀ ∨ (if c.gradeP ≤ 1 then v₀ else ⊥) = ⊥
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The cells of input B: proper, or one of `H₀`, `s₀`, `b₁`. -/
theorem img_cases (y : family₁.X) : (∃ c, y = .inl c) ∨ y = H₀X₁ ∨ y = s₀X₁ ∨ y = b₁X₁ := by
  rcases y with c | H | s | a
  · exact Or.inl ⟨c, rfl⟩
  · right; left
    have e : H = ⟨H₀c, Finset.mem_insert_self _ _⟩ := Subtype.ext (family₁_S₁ H.1 H.2)
    rw [e]
  · right; right; left
    have e : s = ⟨s₀c, Finset.mem_singleton_self _⟩ := Subtype.ext (Finset.mem_singleton.mp s.2)
    rw [e]
  · right; right; right
    have e : a = ⟨b₁, Finset.mem_singleton_self _⟩ := Subtype.ext (Finset.mem_singleton.mp a.2)
    rw [e]

/-- The sources are the two caps of input A and the shared proper row. -/
theorem η₁_eq : η₁ = ofOrd (Ordinal.omega0 * (1 : ℕ) + (3 : ℕ)) := rfl
theorem γ₁_eq : γ₁ = ofOrd (Ordinal.omega0 * (2 : ℕ) + (3 : ℕ)) := rfl
theorem v₀_eq : v₀ = ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ)) := rfl

end InputB

/-! ## Orbit facts: the shifter's values at `ω+3` and `ω+4` from its value at `ω+1` -/

section Orbit

theorem evr_v₀_three : extVisibilityReplace v₀ 3 3 = η₁ := by
  rw [v₀_eq, η₁_eq, extVisibilityReplace_ofOrd]
  congr 1
  unfold visibilityReplace
  rw [ite_eq_left (by rw [finitePart_mul_add]; decide)]
  unfold ordinalReplace
  rw [limitPart_mul_add]

theorem evr_v₀_four : extVisibilityReplace v₀ 4 4 = γ₀ := by
  rw [v₀_eq, γ₀_eq, extVisibilityReplace_ofOrd]
  congr 1
  unfold visibilityReplace
  rw [ite_eq_left (by rw [finitePart_mul_add]; decide)]
  unfold ordinalReplace
  rw [limitPart_mul_add]

/-- The `⊥`-fibre of a shifter is closed under visibility replacement. -/
theorem Witness.bot_orbit {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hw : Witness g σ) {a : ExtOrd}
    (h : σ a = ⊥) {k i : ℕ} (hi : i ≤ k) : σ (extVisibilityReplace a k i) = ⊥ := by
  rw [hw.clause5 a k (by rw [h]; exact bot_le) i hi, h, extVisibilityReplace_bot]

/-- **The orbit equation**: under the guard at threshold `3`, the value at `ω+3` is the
`3`-replacement of the value at `ω+1`. -/
theorem Witness.at_η₁ {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hw : Witness g σ)
    (hg : σ v₀ ≤ g 3) : σ η₁ = extVisibilityReplace (σ v₀) 3 3 := by
  rw [← evr_v₀_three]; exact hw.clause5 v₀ 3 hg 3 le_rfl

theorem Witness.at_γ₀_bot {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hw : Witness g σ)
    (h : σ v₀ = ⊥) : σ γ₀ = ⊥ := by
  rw [← evr_v₀_four]; exact hw.bot_orbit h le_rfl

theorem Witness.at_η₁_bot {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hw : Witness g σ)
    (h : σ v₀ = ⊥) : σ η₁ = ⊥ := by
  rw [← evr_v₀_three]; exact hw.bot_orbit h le_rfl

/-- **Agreement of the `ω+3`-values of two witnesses modulo `γ`**, from the agreement of their
`ω+1`-values modulo `γ` under caps at least `γ`. -/
theorem orbit_agree {g g' : ℕ → ExtOrd} {σ σ' : ExtOrd → ExtOrd} (hw : Witness g σ)
    (hw' : Witness g' σ') {γ : ExtOrd} (hg : γ ≤ g 3) (hg' : γ ≤ g' 3)
    (hagree : min (min (σ v₀) (g 1)) γ = min (min (σ' v₀) (g' 1)) γ) :
    min (σ η₁) γ = min (σ' η₁) γ := by
  have hg13 : g 3 ≤ g 1 := hw.anti 1 3 (by decide)
  have hg13' : g' 3 ≤ g' 1 := hw'.anti 1 3 (by decide)
  -- a value at least `γ` forces the other side's value at least `γ`
  have key : ∀ {g g' : ℕ → ExtOrd} {σ σ' : ExtOrd → ExtOrd}, Witness g σ → Witness g' σ' →
      γ ≤ g 3 → γ ≤ g' 3 →
      min (min (σ v₀) (g 1)) γ = min (min (σ' v₀) (g' 1)) γ →
      γ ≤ σ v₀ → γ ≤ σ' η₁ := by
    intro g g' σ σ' hw hw' hg hg' hagree hA
    have hg13 : g 3 ≤ g 1 := hw.anti 1 3 (by decide)
    have hg13' : g' 3 ≤ g' 1 := hw'.anti 1 3 (by decide)
    have h1 : min (min (σ v₀) (g 1)) γ = γ :=
      min_eq_right (le_min hA (hg.trans hg13))
    have hB : γ ≤ σ' v₀ := by
      by_contra hlt
      rw [not_le] at hlt
      have h2 : min (min (σ' v₀) (g' 1)) γ < γ :=
        lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) hlt
      rw [← hagree, h1] at h2
      exact lt_irrefl _ h2
    by_cases hguard : σ' v₀ ≤ g' 3
    · rw [hw'.at_η₁ hguard]
      exact hB.trans (le_extVisibilityReplace_self _ _)
    · rw [not_le] at hguard
      exact hB.trans (hw'.mono (show v₀ ≤ η₁ from v₀_le_η₁))
  by_cases hA : γ ≤ σ v₀
  · -- both sides are at least `γ`
    have h1 : γ ≤ σ η₁ := hA.trans (hw.mono v₀_le_η₁)
    have h2 : γ ≤ σ' η₁ := key hw hw' hg hg' hagree hA
    rw [min_eq_right h1, min_eq_right h2]
  · by_cases hB : γ ≤ σ' v₀
    · have h2 : γ ≤ σ' η₁ := hB.trans (hw'.mono v₀_le_η₁)
      have h1 : γ ≤ σ η₁ := key hw' hw hg' hg hagree.symm hB
      rw [min_eq_right h1, min_eq_right h2]
    · rw [not_le] at hA hB
      -- both `ω+1`-values are below `γ`, hence below the caps, and equal
      have hAg : σ v₀ ≤ g 3 := hA.le.trans hg
      have hBg : σ' v₀ ≤ g' 3 := hB.le.trans hg'
      rw [min_eq_left (hAg.trans hg13), min_eq_left (hBg.trans hg13'), min_eq_left hA.le,
        min_eq_left hB.le] at hagree
      rw [hw.at_η₁ hAg, hw'.at_η₁ hBg, hagree]

end Orbit


/-! ## The mixed witness and the extension's respect -/

section Mixed

theorem evr_η₁ : extVisibilityReplace η₁ 3 3 = η₁ := by
  rw [η₁_eq, extVisibilityReplace_ofOrd, visReplace_cutoff (by rw [finitePart_mul_add])]
theorem evr_γ₀ : extVisibilityReplace γ₀ 3 3 = γ₀ := by
  rw [γ₀_eq, extVisibilityReplace_ofOrd, visReplace_cutoff (by rw [finitePart_mul_add]; decide)]

/-- **One mixed witness for the two free labels**: a legal pair `(g, σ)`, `g` trivial above `3`,
reproducing input B's `b₁`-locality, whose values at the sources `ω+3` and `ω+4` are the labels. -/
structure MixedWitness (p : C₁.below (Finset.univ, 3) → ExtOrd) (g : ℕ → ExtOrd)
    (σ : ExtOrd → ExtOrd) (x₁ x₂ : ExtOrd) : Prop where
  wit : Witness g σ
  hgK : ∀ k, 3 < k → g k = ⊥
  heq : ∀ y : family₁.X, min (p (cell₁ y)) (p (cell₁ b₁X₁)) =
    min (σ (family₁.rowX b₁X₁ y)) (g (family₁.cellX y).2)
  hx₁ : min (σ η₁) (g 3) = x₁
  hx₂ : min (σ γ₀) (g 3) = x₂

variable {p : C₁.below (Finset.univ, 3) → ExtOrd} {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd}
  {x₁ x₂ : ExtOrd}

theorem MixedWitness.pb (mw : MixedWitness p g σ x₁ x₂) :
    p (cell₁ b₁X₁) = min (σ γ₁) (g 3) := by
  have h := mw.heq b₁X₁
  rw [min_self, rowX₁_eq, embX₁_b₁, rowX_b₁_b₁] at h
  exact h

theorem MixedWitness.x₁_le_x₂ (mw : MixedWitness p g σ x₁ x₂) : x₁ ≤ x₂ := by
  rw [← mw.hx₁, ← mw.hx₂]
  exact min_le_min_right _ (mw.wit.mono η₁_le_γ₀)

theorem MixedWitness.x₂_le_pb (mw : MixedWitness p g σ x₁ x₂) : x₂ ≤ p (cell₁ b₁X₁) := by
  rw [mw.pb, ← mw.hx₂]
  exact min_le_min_right _ (mw.wit.mono γ₀_le_γ₁)

theorem MixedWitness.x₁_le_pb (mw : MixedWitness p g σ x₁ x₂) : x₁ ≤ p (cell₁ b₁X₁) :=
  mw.x₁_le_x₂.trans mw.x₂_le_pb

theorem MixedWitness.g_le (mw : MixedWitness p g σ x₁ x₂) {k : ℕ} (hk : k ≤ 3) : g 3 ≤ g k := by
  rcases lt_or_eq_of_le hk with h | h
  · exact mw.wit.anti k 3 h
  · rw [h]

/-- A value `min (σ s) (g 3)` is `3`-visible when `s` is fixed by `3`-replacement. -/
theorem MixedWitness.vis_of (mw : MixedWitness p g σ x₁ x₂) {s : ExtOrd}
    (hs : extVisibilityReplace s 3 3 = s) :
    extVisibilityReplace (min (σ s) (g 3)) 3 3 = min (σ s) (g 3) := by
  rcases le_total (σ s) (g 3) with h | h
  · rw [min_eq_left h]
    have := mw.wit.clause5 s 3 h 3 le_rfl
    rw [hs] at this
    exact this.symm
  · rw [min_eq_right h]
    exact (mw.wit.vis 3).symm

theorem MixedWitness.x₁_vis (mw : MixedWitness p g σ x₁ x₂) :
    extVisibilityReplace x₁ 3 3 = x₁ := by rw [← mw.hx₁]; exact mw.vis_of evr_η₁
theorem MixedWitness.x₂_vis (mw : MixedWitness p g σ x₁ x₂) :
    extVisibilityReplace x₂ 3 3 = x₂ := by rw [← mw.hx₂]; exact mw.vis_of evr_γ₀

theorem grade_e₂ (x : family₂.X) : C₂.grade (family₂.e x) = (family₂.cellX x).2 := by
  change (C₂.cell (family₂.e x)).2 = _
  rw [Family.cell_e]

/-- The graded index of an image cell. -/
theorem grade_emb₁_cell₁ (y : family₁.X) :
    C₂.grade (family₂.e (embX₁ y)) = (family₁.cellX y).2 := by
  change (C₂.cell (family₂.e (embX₁ y))).2 = _
  rw [Family.cell_e, cellX_embX₁]

/-- An image cell of the three-cell family, written through input B's cells. -/
theorem image_of_emb {c : C₁.below (Finset.univ, 3)} {d : Cell C₂} (h : emb₁ c.1 = d) :
    ∃ y : family₁.X, c = cell₁ y ∧ d = family₂.e (embX₁ y) := by
  refine ⟨family₁.e.symm c.1, Subtype.ext (Equiv.apply_symm_apply _ _).symm, ?_⟩
  rw [← h]; rfl

theorem ext₁_at_b₁ (p : C₁.below (Finset.univ, 3) → ExtOrd) (x₁ x₂ : ExtOrd) :
    ext₁ p x₁ x₂ (cell₂ b₁X) = p (cell₁ b₁X₁) := by
  rw [← embX₁_b₁, ← embBelow₁_cell₁, ext₁_emb]

/-- A cell below a full-scope controller of the three-cell family, as an element of the top lower
set. -/
theorem below_top {Sig : C₂.below (Finset.univ, 3)} (d : C₂.below (C₂.cell Sig.1)) :
    (CellScheme.below.incl Sig d).1 = d.1 := rfl

theorem grade_le_three (d : Cell C₂) : C₂.grade d ≤ 3 :=
  (C₂.grade_le_card_scope _).trans ((Finset.card_le_univ _).trans (by simp))

/-- **Locality at `b₁`** from the mixed witness. -/
theorem MixedWitness.locality_b₁ (mw : MixedWitness p g σ x₁ x₂) :
    TransformsTo (fun d : C₂.below (C₂.cell (cell₂ b₁X).1) => C₂.grade d.1)
      (family₂.rows.E (cell₂ b₁X).1)
      (fun d => min (ext₁ p x₁ x₂ (CellScheme.below.incl (cell₂ b₁X) d))
        (ext₁ p x₁ x₂ (cell₂ b₁X))) := by
  refine mw.wit.transformsTo ?_
  intro d
  rw [ext₁_at_b₁]
  change min (ext₁ p x₁ x₂ (CellScheme.below.incl (cell₂ b₁X) d)) (p (cell₁ b₁X₁)) =
    min (σ (family₂.rowX (family₂.e.symm (family₂.e b₁X)) (family₂.e.symm d.1))) (g (C₂.grade d.1))
  rw [Equiv.symm_apply_apply]
  rcases cases₂' (CellScheme.below.incl (cell₂ b₁X) d) with ⟨c, hc⟩ | hc | hc
  · obtain ⟨y, rfl, hd⟩ := image_of_emb (congrArg Subtype.val hc)
    rw [← hc, ext₁_emb]
    change d.1 = _ at hd
    rw [hd, Equiv.symm_apply_apply, grade_emb₁_cell₁]
    have := mw.heq y
    rw [rowX₁_eq, embX₁_b₁] at this
    exact this
  · have hd : d.1 = family₂.e a₁X := congrArg Subtype.val hc
    rw [hc, ext₁_a₁, hd, Equiv.symm_apply_apply, rowX_b₁_a₁, grade_e₂]
    change min x₁ (p (cell₁ b₁X₁)) = min (σ η₁) (g 3)
    rw [min_eq_left mw.x₁_le_pb, mw.hx₁]
  · have hd : d.1 = family₂.e a₂X := congrArg Subtype.val hc
    rw [hc, ext₁_a₂, hd, Equiv.symm_apply_apply, rowX_b₁_a₂, grade_e₂]
    change min x₂ (p (cell₁ b₁X₁)) = min (σ γ₀) (g 3)
    rw [min_eq_left mw.x₂_le_pb, mw.hx₂]

/-- The proper-cell equation of the mixed witness, with an extra cap. -/
theorem MixedWitness.proper_cap (mw : MixedWitness p g σ x₁ x₂) (c : Prop3) {x : ExtOrd}
    (hx : x ≤ p (cell₁ b₁X₁)) :
    min (p (cell₁ (.inl c))) x = min (σ (t₀.F c)) (min (g (family₁.cellX (.inl c)).2) x) := by
  have h := mw.heq (.inl c)
  rw [rowX₁_eq, embX₁_b₁, show embX₁ (Sum.inl c) = Sum.inl c from rfl, rowX_b₁_inl] at h
  rw [← min_assoc, ← h, min_assoc, min_eq_right hx]

/-- **Locality at `a₁`** from the mixed witness capped at `x₁`. -/
theorem MixedWitness.locality_a₁ (mw : MixedWitness p g σ x₁ x₂)
    (hp : RespectsSemanticsBelow family₁.rows (Finset.univ, 3) p) :
    TransformsTo (fun d : C₂.below (C₂.cell (cell₂ a₁X).1) => C₂.grade d.1)
      (family₂.rows.E (cell₂ a₁X).1)
      (fun d => min (ext₁ p x₁ x₂ (CellScheme.below.incl (cell₂ a₁X) d))
        (ext₁ p x₁ x₂ (cell₂ a₁X))) := by
  refine (mw.wit.cap 3 mw.x₁_vis).transformsTo ?_
  intro d
  rw [ext₁_a₁, capG_of_le (grade_le_three _)]
  change min (ext₁ p x₁ x₂ (CellScheme.below.incl (cell₂ a₁X) d)) x₁ =
    min (σ (family₂.rowX (family₂.e.symm (family₂.e a₁X)) (family₂.e.symm d.1)))
      (min (g (C₂.grade d.1)) x₁)
  rw [Equiv.symm_apply_apply]
  have hcap : ∀ k, k ≤ 3 → min (σ η₁) (min (g k) x₁) = x₁ := by
    intro k hk
    rw [← min_assoc, min_eq_right]
    rw [← mw.hx₁]
    exact min_le_min_left _ (mw.g_le hk)
  rcases cases₂' (CellScheme.below.incl (cell₂ a₁X) d) with ⟨c, hc⟩ | hc | hc
  · obtain ⟨y, rfl, hd⟩ := image_of_emb (congrArg Subtype.val hc)
    rw [← hc, ext₁_emb]
    change d.1 = _ at hd
    rw [hd, Equiv.symm_apply_apply, grade_emb₁_cell₁]
    rcases img_cases y with ⟨c', rfl⟩ | rfl | rfl | rfl
    · rw [embX₁, rowX_a₁_inl]; exact mw.proper_cap c' mw.x₁_le_pb
    · rw [embX₁_H₀, rowX_a₁_H]
      change min (p (cell₁ H₀X₁)) x₁ = min (σ η₁) (min (g 1) x₁)
      rw [hcap 1 (by decide)]
      exact min_eq_right (mw.x₁_le_pb.trans (p_b₁_le_H hp))
    · rw [embX₁_s₀, rowX_a₁_s]
      change min (p (cell₁ s₀X₁)) x₁ = min (σ η₁) (min (g 2) x₁)
      rw [hcap 2 (by decide)]
      exact min_eq_right (mw.x₁_le_pb.trans (p_b₁_le_s hp))
    · rw [embX₁_b₁, rowX_a₁_b₁]
      change min (p (cell₁ b₁X₁)) x₁ = min (σ η₁) (min (g 3) x₁)
      rw [hcap 3 le_rfl]
      exact min_eq_right mw.x₁_le_pb
  · have hd : d.1 = family₂.e a₁X := congrArg Subtype.val hc
    rw [hc, ext₁_a₁, hd, Equiv.symm_apply_apply, rowX_a₁_a₁, grade_e₂]
    change min x₁ x₁ = min (σ η₁) (min (g 3) x₁)
    rw [hcap 3 le_rfl, min_self]
  · have hd : d.1 = family₂.e a₂X := congrArg Subtype.val hc
    rw [hc, ext₁_a₂, hd, Equiv.symm_apply_apply, rowX_a₁_a₂, grade_e₂]
    change min x₂ x₁ = min (σ η₁) (min (g 3) x₁)
    rw [hcap 3 le_rfl, min_eq_right mw.x₁_le_x₂]

/-- **Locality at `a₂`** from the mixed witness capped at `x₂`. -/
theorem MixedWitness.locality_a₂ (mw : MixedWitness p g σ x₁ x₂)
    (hp : RespectsSemanticsBelow family₁.rows (Finset.univ, 3) p) :
    TransformsTo (fun d : C₂.below (C₂.cell (cell₂ a₂X).1) => C₂.grade d.1)
      (family₂.rows.E (cell₂ a₂X).1)
      (fun d => min (ext₁ p x₁ x₂ (CellScheme.below.incl (cell₂ a₂X) d))
        (ext₁ p x₁ x₂ (cell₂ a₂X))) := by
  refine (mw.wit.cap 3 mw.x₂_vis).transformsTo ?_
  intro d
  rw [ext₁_a₂, capG_of_le (grade_le_three _)]
  change min (ext₁ p x₁ x₂ (CellScheme.below.incl (cell₂ a₂X) d)) x₂ =
    min (σ (family₂.rowX (family₂.e.symm (family₂.e a₂X)) (family₂.e.symm d.1)))
      (min (g (C₂.grade d.1)) x₂)
  rw [Equiv.symm_apply_apply]
  have hcap : ∀ k, k ≤ 3 → min (σ γ₀) (min (g k) x₂) = x₂ := by
    intro k hk
    rw [← min_assoc, min_eq_right]
    rw [← mw.hx₂]
    exact min_le_min_left _ (mw.g_le hk)
  rcases cases₂' (CellScheme.below.incl (cell₂ a₂X) d) with ⟨c, hc⟩ | hc | hc
  · obtain ⟨y, rfl, hd⟩ := image_of_emb (congrArg Subtype.val hc)
    rw [← hc, ext₁_emb]
    change d.1 = _ at hd
    rw [hd, Equiv.symm_apply_apply, grade_emb₁_cell₁]
    rcases img_cases y with ⟨c', rfl⟩ | rfl | rfl | rfl
    · rw [embX₁, rowX_a₂_inl]; exact mw.proper_cap c' mw.x₂_le_pb
    · rw [embX₁_H₀, rowX_a₂_H]
      change min (p (cell₁ H₀X₁)) x₂ = min (σ γ₀) (min (g 1) x₂)
      rw [hcap 1 (by decide)]
      exact min_eq_right (mw.x₂_le_pb.trans (p_b₁_le_H hp))
    · rw [embX₁_s₀, rowX_a₂_s]
      change min (p (cell₁ s₀X₁)) x₂ = min (σ γ₀) (min (g 2) x₂)
      rw [hcap 2 (by decide)]
      exact min_eq_right (mw.x₂_le_pb.trans (p_b₁_le_s hp))
    · rw [embX₁_b₁, rowX_a₂_b₁]
      change min (p (cell₁ b₁X₁)) x₂ = min (σ γ₀) (min (g 3) x₂)
      rw [hcap 3 le_rfl]
      exact min_eq_right mw.x₂_le_pb
  · have hd : d.1 = family₂.e a₁X := congrArg Subtype.val hc
    rw [hc, ext₁_a₁, hd, Equiv.symm_apply_apply, rowX_a₂_a₁, grade_e₂]
    change min x₁ x₂ = min (σ η₁) (min (g 3) x₂)
    rw [← min_assoc, mw.hx₁, min_eq_left mw.x₁_le_x₂]
  · have hd : d.1 = family₂.e a₂X := congrArg Subtype.val hc
    rw [hc, ext₁_a₂, hd, Equiv.symm_apply_apply, rowX_a₂_a₂, grade_e₂]
    change min x₂ x₂ = min (σ γ₀) (min (g 3) x₂)
    rw [hcap 3 le_rfl, min_self]

end Mixed


/-! ## Respect of the extension -/

section Respect

open Classical in
noncomputable def inv₁ (c : Cell C₂) : Cell C₁ :=
  if h : ∃ i, emb₁ i = c then Classical.choose h else family₁.e b₁X₁

theorem emb₁_inv₁ {c : Cell C₂} (h : ∃ i, emb₁ i = c) : emb₁ (inv₁ c) = c := by
  classical
  unfold inv₁
  rw [dite_of_pos h]
  exact Classical.choose_spec h

theorem inv₁_emb₁ (i : Cell C₁) : inv₁ (emb₁ i) = i := emb₁_injective (emb₁_inv₁ ⟨i, rfl⟩)

/-- The level-three cells of input B: only `b₁`. -/
theorem grade3_cases₁ (c : Cell C₁) (h : C₁.grade c = 3) : c = family₁.e b₁X₁ := by
  have hc : family₁.cellX (family₁.e.symm c) = (Finset.univ, 3) := by
    rw [← Family.cell_eq]
    refine Prod.ext ?_ h
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin]
    have h3 := C₁.grade_le_card_scope c
    rw [h] at h3
    exact le_antisymm ((Finset.card_le_univ _).trans (by simp)) h3
  rcases hw : family₁.e.symm c with p | H | s | a
  · exact absurd (congrArg Prod.fst (hw ▸ hc)) (Prop3.scope_ne_univ p)
  · exact absurd (show (1 : ℕ) = 3 from congrArg Prod.snd (hw ▸ hc)) (by decide)
  · exact absurd (show (2 : ℕ) = 3 from congrArg Prod.snd (hw ▸ hc)) (by decide)
  · have e : a = ⟨b₁, Finset.mem_singleton_self _⟩ := Subtype.ext (Finset.mem_singleton.mp a.2)
    rw [← Equiv.apply_symm_apply family₁.e c, hw, e]

/-- **Locality at a cell of input B of grade at most two**: everything below is an image. -/
theorem ext₁_locality_low {p : C₁.below (Finset.univ, 3) → ExtOrd}
    (hp : RespectsSemanticsBelow family₁.rows (Finset.univ, 3) p) (x₁ x₂ : ExtOrd)
    (c : C₁.below (Finset.univ, 3)) (hc : C₁.grade c.1 ≤ 2) :
    TransformsTo (fun d : C₂.below (C₂.cell (embBelow₁ c).1) => C₂.grade d.1)
      (family₂.rows.E (embBelow₁ c).1)
      (fun d => min (ext₁ p x₁ x₂ (CellScheme.below.incl (embBelow₁ c) d))
        (ext₁ p x₁ x₂ (embBelow₁ c))) := by
  classical
  have hgr : ∀ d : C₂.below (C₂.cell (embBelow₁ c).1), C₂.grade d.1 ≤ 2 := by
    intro d
    have h := d.2.2
    change C₂.grade d.1 ≤ C₂.grade (emb₁ c.1) at h
    have h' : C₂.grade (emb₁ c.1) = C₁.grade c.1 := by
      change (C₂.cell (emb₁ c.1)).2 = (C₁.cell c.1).2; rw [cell_emb₁]
    rw [h'] at h
    exact h.trans hc
  have himg : ∀ d : C₂.below (C₂.cell (embBelow₁ c).1), ∃ i, emb₁ i = d.1 :=
    fun d => exists_emb₁_of_grade_le_two d.1 (hgr d)
  have hmem : ∀ d : C₂.below (C₂.cell (embBelow₁ c).1),
      GradedLe (C₁.cell (inv₁ d.1)) (C₁.cell c.1) := by
    intro d
    have h := d.2
    change GradedLe (C₂.cell d.1) (C₂.cell (emb₁ c.1)) at h
    rw [← emb₁_inv₁ (himg d), cell_emb₁, cell_emb₁] at h
    exact h
  let ψ : C₂.below (C₂.cell (embBelow₁ c).1) → C₁.below (C₁.cell c.1) := fun d =>
    ⟨inv₁ d.1, hmem d⟩
  have key := (hp.locality c).reindex ψ
  refine transformsTo_congr ?_ ?_ ?_ key
  · funext d
    change C₁.grade (inv₁ d.1) = C₂.grade d.1
    change (C₁.cell (inv₁ d.1)).2 = (C₂.cell d.1).2
    rw [← cell_emb₁, emb₁_inv₁ (himg d)]
  · funext d
    obtain ⟨i, hi⟩ := himg d
    have hinv : inv₁ d.1 = i := by rw [← hi, inv₁_emb₁]
    change family₁.rowX (family₁.e.symm c.1) (family₁.e.symm (inv₁ d.1)) =
      family₂.rowX (family₂.e.symm (emb₁ c.1)) (family₂.e.symm d.1)
    rw [hinv, ← hi]
    change _ = family₂.rowX (family₂.e.symm (family₂.e _)) (family₂.e.symm (family₂.e _))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, rowX_embX₁]
  · funext d
    change min (p (CellScheme.below.incl c (ψ d))) (p c) =
      min (ext₁ p x₁ x₂ (CellScheme.below.incl (embBelow₁ c) d)) (ext₁ p x₁ x₂ (embBelow₁ c))
    rw [ext₁_emb]
    have e : CellScheme.below.incl (embBelow₁ c) d = embBelow₁ (CellScheme.below.incl c (ψ d)) := by
      apply Subtype.ext
      change d.1 = emb₁ (inv₁ d.1)
      rw [emb₁_inv₁ (himg d)]
    rw [e, ext₁_emb]

theorem grade_emb₁' (c : C₁.below (Finset.univ, 3)) : C₂.grade (embBelow₁ c).1 = C₁.grade c.1 := by
  change (C₂.cell (emb₁ c.1)).2 = (C₁.cell c.1).2
  rw [cell_emb₁]

theorem grade_a₁ : C₂.grade (cell₂ a₁X).1 = 3 := by
  change (C₂.cell (family₂.e a₁X)).2 = 3
  rw [Family.cell_e]; rfl
theorem grade_a₂ : C₂.grade (cell₂ a₂X).1 = 3 := by
  change (C₂.cell (family₂.e a₂X)).2 = 3
  rw [Family.cell_e]; rfl

/-- **The extension respects the three-cell family**, from a mixed witness. -/
theorem respects_ext₁ {p : C₁.below (Finset.univ, 3) → ExtOrd}
    (hp : RespectsSemanticsBelow family₁.rows (Finset.univ, 3) p) {g : ℕ → ExtOrd}
    {σ : ExtOrd → ExtOrd} {x₁ x₂ : ExtOrd} (mw : MixedWitness p g σ x₁ x₂) :
    RespectsSemanticsBelow family₂.rows (Finset.univ, 3) (ext₁ p x₁ x₂) where
  orderly d := by
    rcases cases₂' d with ⟨c, rfl⟩ | rfl | rfl
    · have := hp.orderly c
      dsimp only at this ⊢
      rw [ext₁_emb, grade_emb₁']
      exact this
    · dsimp only
      rw [ext₁_a₁, grade_a₁]
      exact mw.x₁_vis.symm
    · dsimp only
      rw [ext₁_a₂, grade_a₂]
      exact mw.x₂_vis.symm
  locality Sig := by
    rcases cases₂' Sig with ⟨c, rfl⟩ | rfl | rfl
    · by_cases hc : C₁.grade c.1 ≤ 2
      · exact ext₁_locality_low hp x₁ x₂ c hc
      · have h3 : C₁.grade c.1 = 3 := by
          have := (C₁.grade_le_card_scope c.1).trans
            ((Finset.card_le_univ _).trans (by simp : Fintype.card (Fin 3) ≤ 3))
          omega
        have hcb : c = cell₁ b₁X₁ := Subtype.ext (grade3_cases₁ c.1 h3)
        subst hcb
        have e : embBelow₁ (cell₁ b₁X₁) = cell₂ b₁X := by rw [embBelow₁_cell₁, embX₁_b₁]
        rw [e]
        exact mw.locality_b₁
    · exact mw.locality_a₁ hp
    · exact mw.locality_a₂ hp
  availability Sig Xi₀ hs hg := by
    by_cases hc : C₂.cell Sig.1 = C₂.cell Xi₀.1
    · exact ⟨Sig, hc, le_rfl⟩
    · have hne3 : C₂.grade Sig.1 ≠ 3 := by
        intro h3
        apply hc
        rw [cell_eq_univ_of_grade3₂ _ h3, cell_eq_univ_of_grade3₂ _ (hg ▸ h3)]
      rcases cases₂' Sig with ⟨c, rfl⟩ | rfl | rfl
      · rcases cases₂' Xi₀ with ⟨c', rfl⟩ | rfl | rfl
        · obtain ⟨Xi, hcell, hle⟩ := hp.availability c c'
            (by
              have := hs
              change (C₂.cell (emb₁ c.1)).1 ⊆ (C₂.cell (emb₁ c'.1)).1 at this
              rw [cell_emb₁, cell_emb₁] at this
              exact this)
            (by
              have := hg
              rw [grade_emb₁', grade_emb₁'] at this
              exact this)
          refine ⟨embBelow₁ Xi, ?_, ?_⟩
          · change C₂.cell (emb₁ Xi.1) = C₂.cell (emb₁ c'.1)
            rw [cell_emb₁, cell_emb₁]; exact hcell
          · rw [ext₁_emb, ext₁_emb]; exact hle
        · exact absurd (hg.trans grade_a₁) hne3
        · exact absurd (hg.trans grade_a₂) hne3
      · exact absurd grade_a₁ hne3
      · exact absurd grade_a₂ hne3

end Respect


/-! ## The main theorem -/

section Main

theorem v₀_lt_ξ : v₀ < ofOrd (Ordinal.omega0 * (1 : ℕ) + (4 : ℕ)) := by
  rw [v₀_eq, ofOrd_lt_ofOrd]
  exact add_lt_add_right (Nat.cast_lt.mpr (by decide : (1 : ℕ) < 4) :
    ((1 : ℕ) : Ordinal) < (4 : ℕ)) _
theorem η₁_lt_ξ : η₁ < ofOrd (Ordinal.omega0 * (1 : ℕ) + (4 : ℕ)) := by
  rw [η₁_eq, ofOrd_lt_ofOrd]
  exact add_lt_add_right (Nat.cast_lt.mpr (by decide : (3 : ℕ) < 4) :
    ((3 : ℕ) : Ordinal) < (4 : ℕ)) _
theorem ξ_le_γ₀ : ofOrd (Ordinal.omega0 * (1 : ℕ) + (4 : ℕ)) ≤ γ₀ := le_rfl
theorem ξ_le_γ₁ : ofOrd (Ordinal.omega0 * (1 : ℕ) + (4 : ℕ)) ≤ γ₁ := γ₀_le_γ₁
theorem fp_ξ : 3 < finitePart (Ordinal.omega0 * (1 : ℕ) + (4 : ℕ)) := by
  rw [finitePart_mul_add]; decide

theorem le_η₁_of_lt_ξ {a : ExtOrd} (h : a < ofOrd (Ordinal.omega0 * (1 : ℕ) + (4 : ℕ))) :
    a ≤ η₁ := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · exact bot_le
  · exact absurd h (not_lt.mpr le_top)
  · rw [η₁_eq, ofOrd_le_ofOrd]
    have this := ofOrd_lt_ofOrd.mp h
    have e : ((4 : ℕ) : Ordinal) = ((3 : ℕ) : Ordinal) + 1 := Nat.cast_succ 3
    rw [e, ← add_assoc] at this
    exact Order.lt_add_one_iff.mp this

theorem inTail_γ₀ : InTail (Ordinal.omega0 * (1 : ℕ) + (4 : ℕ)) γ₀ := ⟨_, rfl, le_rfl, rfl⟩

theorem not_inTail_γ₁ : ¬ InTail (Ordinal.omega0 * (1 : ℕ) + (4 : ℕ)) γ₁ := by
  rintro ⟨β, hβ, h1, h2⟩
  have hβ' : Ordinal.omega0 * (2 : ℕ) + (3 : ℕ) = β := ofOrd_inj.mp hβ
  subst hβ'
  rw [limitPart_mul_add, limitPart_mul_add] at h2
  have := blockIdx_mono h1
  rw [blockIdx_mul_add, blockIdx_mul_add] at this
  have h' : (1 : ℕ) ≤ 2 := Nat.cast_le.mp this
  -- the limit parts differ: `ω·2 ≠ ω·1`
  have hc := congrArg blockIdx h2
  have e1 : Ordinal.omega0 * (2 : ℕ) = Ordinal.omega0 * (2 : ℕ) + ((0 : ℕ) : Ordinal) := by
    rw [Nat.cast_zero, add_zero]
  have e2 : Ordinal.omega0 * (1 : ℕ) = Ordinal.omega0 * (1 : ℕ) + ((0 : ℕ) : Ordinal) := by
    rw [Nat.cast_zero, add_zero]
  rw [e1, e2, blockIdx_mul_add, blockIdx_mul_add] at hc
  exact absurd (Nat.cast_injective hc) (by decide)

/-- A value `min (σ s) (g 3)` of a witness is `3`-visible when `s` is fixed by `3`-replacement. -/
theorem Witness.vis_min {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hw : Witness g σ) {s : ExtOrd}
    (hs : extVisibilityReplace s 3 3 = s) :
    extVisibilityReplace (min (σ s) (g 3)) 3 3 = min (σ s) (g 3) := by
  rcases le_total (σ s) (g 3) with h | h
  · rw [min_eq_left h]
    have := hw.clause5 s 3 h 3 le_rfl
    rw [hs] at this
    exact this.symm
  · rw [min_eq_right h]
    exact (hw.vis 3).symm

theorem vis_max {a b : ExtOrd} (ha : extVisibilityReplace a 3 3 = a)
    (hb : extVisibilityReplace b 3 3 = b) : extVisibilityReplace (max a b) 3 3 = max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha

/-- The sources of input B's `b₁`-row: `⊥`, the proper constant, or `b₁`'s cap. -/
theorem rowX₁_b₁_cases (y : family₁.X) :
    family₁.rowX b₁X₁ y = ⊥ ∨ family₁.rowX b₁X₁ y = v₀ ∨ family₁.rowX b₁X₁ y = γ₁ := by
  rw [rowX₁_eq, embX₁_b₁]
  rcases img_cases y with ⟨c, rfl⟩ | rfl | rfl | rfl
  · rw [embX₁, rowX_b₁_inl]
    rcases t₀_F_cases c with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · rw [embX₁_H₀, rowX_b₁_H]; exact Or.inr (Or.inr rfl)
  · rw [embX₁_s₀, rowX_b₁_s]; exact Or.inr (Or.inr rfl)
  · rw [embX₁_b₁, rowX_b₁_b₁]; exact Or.inr (Or.inr rfl)

theorem t₀_F_s1 : t₀.F Prop3.s1 = v₀ := by
  change (if Prop3.s1.gradeP ≤ 1 then v₀ else ⊥) = v₀
  rw [ite_eq_left (by decide)]

/-- **`FaceExtB'` holds.** -/
theorem faceExtB' : FaceExtB' := by
  intro p q γ hp hq hγ hagree
  -- input B's `b₁`-locality witness, truncated above grade three
  obtain ⟨g₀, σ, hw₀, heq₀⟩ := TransformsTo.witness (hp.locality (cell₁ b₁X₁))
  set g : ℕ → ExtOrd := truncG 3 g₀ with hgdef
  have hw : Witness g σ := hw₀.truncate 3
  have hgK : ∀ k, 3 < k → g k = ⊥ := fun k hk => truncG_of_gt hk
  have heq : ∀ y : family₁.X, min (p (cell₁ y)) (p (cell₁ b₁X₁)) =
      min (σ (family₁.rowX b₁X₁ y)) (g (family₁.cellX y).2) := by
    intro y
    have hle : GradedLe (C₁.cell (family₁.e y)) (C₁.cell (cell₁ b₁X₁).1) := by
      have e : C₁.cell (cell₁ b₁X₁).1 = (Finset.univ, 3) := by
        change C₁.cell (family₁.e b₁X₁) = _
        rw [Family.cell_e family₁ b₁X₁]; rfl
      rw [e]; exact le_top₁ _
    have h := heq₀ ⟨family₁.e y, hle⟩
    dsimp only at h
    have e1 : CellScheme.below.incl (cell₁ b₁X₁) ⟨family₁.e y, hle⟩ = cell₁ y := Subtype.ext rfl
    rw [e1] at h
    change _ = min (σ (family₁.rowX (family₁.e.symm (family₁.e b₁X₁))
      (family₁.e.symm (family₁.e y)))) (g₀ (C₁.grade (family₁.e y))) at h
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h
    have hgr : C₁.grade (family₁.e y) = (family₁.cellX y).2 := by
      change (C₁.cell (family₁.e y)).2 = _; rw [Family.cell_e]
    have hle3 : (family₁.cellX y).2 ≤ 3 := by
      have := (le_top₁ (family₁.e y)).2
      change (C₁.cell (family₁.e y)).2 ≤ 3 at this
      rw [Family.cell_e] at this; exact this
    rw [h, hgr, hgdef, truncG_of_le hle3]
  -- `q`'s `b₁`-locality witness
  obtain ⟨gq₀, σq, hwq₀, heqq₀⟩ := TransformsTo.witness (hq.locality (cell₂ b₁X))
  set gq : ℕ → ExtOrd := truncG 3 gq₀ with hgqdef
  have hwq : Witness gq σq := hwq₀.truncate 3
  have hgqK : ∀ k, 3 < k → gq k = ⊥ := fun k hk => truncG_of_gt hk
  have heqq : ∀ x : family₂.X, min (q (cell₂ x)) (q (cell₂ b₁X)) =
      min (σq (family₂.rowX b₁X x)) (gq (family₂.cellX x).2) := by
    intro x
    have hle : GradedLe (C₂.cell (family₂.e x)) (C₂.cell (cell₂ b₁X).1) := by
      have e : C₂.cell (cell₂ b₁X).1 = (Finset.univ, 3) := by
        change C₂.cell (family₂.e b₁X) = _
        rw [Family.cell_e family₂ b₁X]; rfl
      rw [e]; exact le_top₂ _
    have h := heqq₀ ⟨family₂.e x, hle⟩
    dsimp only at h
    have e1 : CellScheme.below.incl (cell₂ b₁X) ⟨family₂.e x, hle⟩ = cell₂ x := Subtype.ext rfl
    rw [e1] at h
    change _ = min (σq (family₂.rowX (family₂.e.symm (family₂.e b₁X))
      (family₂.e.symm (family₂.e x)))) (gq₀ (C₂.grade (family₂.e x))) at h
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h
    have hle3 : (family₂.cellX x).2 ≤ 3 := by
      have := (le_top₂ (family₂.e x)).2
      change (C₂.cell (family₂.e x)).2 ≤ 3 at this
      rw [Family.cell_e] at this; exact this
    rw [h, grade_e₂, hgqdef, truncG_of_le hle3]
  -- names
  set pb := p (cell₁ b₁X₁) with hpbdef
  set qb := q (cell₂ b₁X) with hqbdef
  set q₁ := q (cell₂ a₁X) with hq₁def
  set q₂ := q (cell₂ a₂X) with hq₂def
  have hpb : pb = min (σ γ₁) (g 3) := by
    have h := heq b₁X₁
    rw [min_self, rowX₁_eq, embX₁_b₁, rowX_b₁_b₁] at h
    exact h
  have hpb_le : pb ≤ g 3 := by rw [hpb]; exact min_le_right _ _
  have hpb_le' : pb ≤ σ γ₁ := by rw [hpb]; exact min_le_left _ _
  have hqb : qb = min (σq γ₁) (gq 3) := by
    have h := heqq b₁X
    rw [min_self, rowX_b₁_b₁] at h
    exact h
  have hq1 : min q₁ qb = min (σq η₁) (gq 3) := by
    have h := heqq a₁X; rw [rowX_b₁_a₁] at h; exact h
  have hq2 : min q₂ qb = min (σq γ₀) (gq 3) := by
    have h := heqq a₂X; rw [rowX_b₁_a₂] at h; exact h
  have hq12 := q_a₁_le_a₂ hq
  have hq2b := q_a₂_le_b₁ hq
  have hq1b := q_a₁_le_b₁ hq
  have hagree' : ∀ y : family₁.X, min (q (cell₂ (embX₁ y))) γ = min (p (cell₁ y)) γ := by
    intro y
    have := hagree (cell₁ y)
    rw [embBelow₁_cell₁] at this
    exact this
  have hagree_b : min qb γ = min pb γ := by
    have := hagree' b₁X₁; rw [embX₁_b₁] at this; exact this
  have hagree_img : ∀ (x₁ x₂ : ExtOrd) (c : C₁.below (Finset.univ, 3)),
      min (ext₁ p x₁ x₂ (embBelow₁ c)) γ = min (q (embBelow₁ c)) γ := by
    intro x₁ x₂ c; rw [ext₁_emb]; exact (hagree c).symm
  have hq₁vis : extVisibilityReplace q₁ 3 3 = q₁ := by
    have := hq.orderly (cell₂ a₁X); dsimp only at this; rw [grade_a₁] at this; exact this.symm
  have hq₂vis : extVisibilityReplace q₂ 3 3 = q₂ := by
    have := hq.orderly (cell₂ a₂X); dsimp only at this; rw [grade_a₂] at this; exact this.symm
  by_cases hI : pb = qb ∧ qb ≤ γ
  · -- **Case I**: `q`'s own witness serves; the free labels are `q a₁`, `q a₂`
    obtain ⟨hpq, hqγ⟩ := hI
    have mw : MixedWitness p gq σq q₁ q₂ :=
      { wit := hwq
        hgK := hgqK
        heq := by
          intro y
          have h := heqq (embX₁ y)
          rw [cellX_embX₁] at h
          rw [rowX₁_eq, embX₁_b₁, ← h, ← hpbdef, hpq]
          have h2 := hagree' y
          calc min (p (cell₁ y)) qb = min (min (p (cell₁ y)) γ) qb := by
                rw [min_assoc, min_eq_right hqγ]
            _ = min (min (q (cell₂ (embX₁ y))) γ) qb := by rw [h2]
            _ = min (q (cell₂ (embX₁ y))) qb := by rw [min_assoc, min_eq_right hqγ]
        hx₁ := by rw [← hq1]; exact min_eq_left hq1b
        hx₂ := by rw [← hq2]; exact min_eq_left hq2b }
    refine ⟨ext₁ p q₁ q₂, respects_ext₁ hp mw, ?_, fun d => ext₁_emb p _ _ d⟩
    intro d
    rcases cases₂' d with ⟨c, rfl⟩ | rfl | rfl
    · exact hagree_img _ _ c
    · rw [ext₁_a₁]
    · rw [ext₁_a₂]
  · -- **Case II**: input B's witness, spliced at `ω+4`
    have hpbγ : γ ≤ pb := by
      by_contra hlt
      rw [not_le] at hlt
      rw [min_eq_left hlt.le] at hagree_b
      apply hI
      by_cases hqγ : qb ≤ γ
      · rw [min_eq_left hqγ] at hagree_b; exact ⟨hagree_b.symm, hqγ⟩
      · rw [not_le] at hqγ
        rw [min_eq_right hqγ.le] at hagree_b
        exact absurd hagree_b (ne_of_gt hlt)
    have hqbγ : γ ≤ qb := by
      by_contra hlt
      rw [not_le] at hlt
      rw [min_eq_left hlt.le, min_eq_right hpbγ] at hagree_b
      exact absurd hagree_b (ne_of_lt hlt)
    have hg3 : γ ≤ g 3 := hpbγ.trans hpb_le
    have hgq3 : γ ≤ gq 3 := hqbγ.trans (hqb ▸ min_le_right _ _)
    -- the `ω+1`-values agree modulo `γ`: the proper cell `s1`
    have hv₀ : min (min (σ v₀) (g 1)) γ = min (min (σq v₀) (gq 1)) γ := by
      have h1 := heq (.inl Prop3.s1)
      rw [rowX₁_eq, embX₁_b₁, show embX₁ (.inl Prop3.s1) = .inl Prop3.s1 from rfl, rowX_b₁_inl,
        t₀_F_s1] at h1
      change min (p (cell₁ (.inl Prop3.s1))) pb = min (σ v₀) (g 1) at h1
      have h2 := heqq (.inl Prop3.s1)
      rw [rowX_b₁_inl, t₀_F_s1] at h2
      change min (q (cell₂ (.inl Prop3.s1))) qb = min (σq v₀) (gq 1) at h2
      rw [← h1, ← h2, min_assoc, min_eq_right hpbγ, min_assoc, min_eq_right hqbγ]
      exact (hagree' (.inl Prop3.s1)).symm
    have horbit : min (σ η₁) γ = min (σq η₁) γ := orbit_agree hw hwq hg3 hgq3 hv₀
    -- the first free label, from input B's witness at `ω+3`
    set x₁ := min (σ η₁) (g 3) with hx₁def
    have hx₁γ : min x₁ γ = min q₁ γ := by
      have e1 : min x₁ γ = min (σ η₁) γ := by rw [hx₁def, min_assoc, min_eq_right hg3]
      have e2 : min q₁ γ = min (σq η₁) γ := by
        have h1b : q₁ ≤ qb := hq1b
        rw [← min_eq_left h1b, hq1, min_assoc, min_eq_right hgq3]
      rw [e1, e2, horbit]
    have hx₁vis : extVisibilityReplace x₁ 3 3 = x₁ := hw.vis_min evr_η₁
    set x₂p := min (σ γ₀) (g 3) with hx₂pdef
    have hx₂p_le_pb : x₂p ≤ pb := by
      rw [hpb]; exact min_le_min_right _ (hw.mono γ₀_le_γ₁)
    have hx₁_le_x₂p : x₁ ≤ x₂p := min_le_min_right _ (hw.mono η₁_le_γ₀)
    -- the second free label, reconciled with `q a₂` modulo `γ`
    set x₂ : ExtOrd := if γ ≤ q₂ then max x₂p γ else q₂ with hx₂def
    have hx₂γ : min x₂ γ = min q₂ γ := by
      rw [hx₂def]; split_ifs with h
      · rw [min_eq_right (le_max_right _ _), min_eq_right h]
      · rfl
    have hx₂_le_pb : x₂ ≤ pb := by
      rw [hx₂def]; split_ifs with h
      · exact max_le hx₂p_le_pb hpbγ
      · rw [not_le] at h; exact h.le.trans hpbγ
    have hx₂vis : extVisibilityReplace x₂ 3 3 = x₂ := by
      rw [hx₂def]; split_ifs with h
      · exact vis_max (hw.vis_min evr_γ₀) hγ
      · exact hq₂vis
    have hx₁_le_x₂ : x₁ ≤ x₂ := by
      rw [hx₂def]; split_ifs with h
      · exact hx₁_le_x₂p.trans (le_max_left _ _)
      · rw [not_le] at h
        have h1 : min q₁ γ = q₁ := min_eq_left (hq12.trans h.le)
        rw [h1] at hx₁γ
        by_contra hlt
        rw [not_le] at hlt
        rcases lt_or_ge x₁ γ with hx | hx
        · rw [min_eq_left hx.le] at hx₁γ
          rw [hx₁γ] at hlt
          exact absurd hlt (not_lt.mpr hq12)
        · rw [min_eq_right hx] at hx₁γ
          rw [hx₁γ] at h
          exact absurd h (not_lt.mpr hq12)
    -- the spliced witness
    have hσ' : ∃ σ' : ExtOrd → ExtOrd, Witness g σ' ∧ σ' ⊥ = ⊥ ∧ σ' v₀ = σ v₀ ∧ σ' η₁ = σ η₁ ∧
        σ' γ₁ = σ γ₁ ∧ min (σ' γ₀) (g 3) = x₂ := by
      by_cases hdir : x₂p ≤ x₂
      · -- raise
        refine ⟨raiseShifter σ (Ordinal.omega0 * (1 : ℕ) + (4 : ℕ)) x₂,
          hw.raise 3 hgK fp_ξ hx₂vis, (raiseShifter_of_lt (bot_lt_ofOrd _)).trans hw.bot,
          raiseShifter_of_lt v₀_lt_ξ, raiseShifter_of_lt η₁_lt_ξ, ?_, ?_⟩
        · by_cases hb : σ γ₁ = ⊥
          · rw [raiseShifter_of_bot hb, hb]
          · rw [raiseShifter_of_ge ξ_le_γ₁ hb]
            exact max_eq_left (hx₂_le_pb.trans hpb_le')
        · by_cases hb : σ γ₀ = ⊥
          · rw [raiseShifter_of_bot hb, min_eq_left bot_le]
            -- the `⊥`-fibre cannot be raised: the second label is `⊥` here
            have hx₂p0 : x₂p = ⊥ := by rw [hx₂pdef, hb, min_eq_left bot_le]
            have hσv : σ v₀ = ⊥ := le_bot_iff.mp (hb ▸ hw.mono v₀_le_γ₀)
            have hs1 : min (p (cell₁ (.inl Prop3.s1))) pb = ⊥ := by
              have h1 := heq (.inl Prop3.s1)
              rw [rowX₁_eq, embX₁_b₁, show embX₁ (.inl Prop3.s1) = .inl Prop3.s1 from rfl,
                rowX_b₁_inl, t₀_F_s1, hσv, min_eq_left bot_le] at h1
              exact h1
            by_cases hγ0 : γ = ⊥
            · rw [hx₂def, hγ0, ite_eq_left bot_le, hx₂p0, max_self]
            · have hγpos : ⊥ < γ := bot_lt_iff_ne_bot.mpr hγ0
              have hps1 : p (cell₁ (.inl Prop3.s1)) = ⊥ := by
                rcases min_eq_bot.mp hs1 with h | h
                · exact h
                · exact absurd (h ▸ hpbγ) (not_le.mpr hγpos)
              have hqs1 : q (cell₂ (.inl Prop3.s1)) = ⊥ := by
                have h := hagree' (.inl Prop3.s1)
                rw [hps1, min_eq_left bot_le] at h
                rcases min_eq_bot.mp h with h' | h'
                · exact h'
                · exact absurd h' hγ0
              -- `q a₂ = ⊥` from `q`'s `a₂`-locality
              obtain ⟨g₂, σ₂, hw₂, heq₂⟩ := TransformsTo.witness (hq.locality (cell₂ a₂X))
              have hle₂ : ∀ x : family₂.X,
                  GradedLe (C₂.cell (family₂.e x)) (C₂.cell (cell₂ a₂X).1) := by
                intro x
                have e : C₂.cell (cell₂ a₂X).1 = (Finset.univ, 3) := by
                  change C₂.cell (family₂.e a₂X) = _
                  rw [Family.cell_e family₂ a₂X]; rfl
                rw [e]; exact le_top₂ _
              have h₂s := heq₂ ⟨family₂.e (.inl Prop3.s1), hle₂ _⟩
              have h₂a := heq₂ ⟨family₂.e a₂X, hle₂ _⟩
              dsimp only at h₂s h₂a
              have e1 : CellScheme.below.incl (cell₂ a₂X) ⟨family₂.e (.inl Prop3.s1), hle₂ _⟩ =
                cell₂ (.inl Prop3.s1) := Subtype.ext rfl
              have e2 : CellScheme.below.incl (cell₂ a₂X) ⟨family₂.e a₂X, hle₂ _⟩ = cell₂ a₂X :=
                Subtype.ext rfl
              rw [e1] at h₂s
              rw [e2, min_self] at h₂a
              change _ = min (σ₂ (family₂.rowX (family₂.e.symm (family₂.e a₂X))
                (family₂.e.symm (family₂.e (.inl Prop3.s1))))) (g₂ (C₂.grade (family₂.e _))) at h₂s
              change _ = min (σ₂ (family₂.rowX (family₂.e.symm (family₂.e a₂X))
                (family₂.e.symm (family₂.e a₂X)))) (g₂ (C₂.grade (family₂.e _))) at h₂a
              rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, rowX_a₂_inl, t₀_F_s1, grade_e₂,
                hqs1, min_eq_left bot_le] at h₂s
              rw [Equiv.symm_apply_apply, rowX_a₂_a₂, grade_e₂] at h₂a
              change ⊥ = min (σ₂ v₀) (g₂ 1) at h₂s
              change q₂ = min (σ₂ γ₀) (g₂ 3) at h₂a
              have hq₂0 : q₂ = ⊥ := by
                rcases min_eq_bot.mp h₂s.symm with h' | h'
                · rw [h₂a, hw₂.at_γ₀_bot h', min_eq_left bot_le]
                · rw [h₂a]
                  exact le_bot_iff.mp ((min_le_right _ _).trans ((hw₂.anti 1 3 (by decide)).trans
                    (le_of_eq h')))
              rw [hx₂def, hq₂0, ite_eq_right (fun h => absurd (le_bot_iff.mp h) hγ0)]
          · rw [raiseShifter_of_ge ξ_le_γ₀ hb]
            rcases le_total (σ γ₀) x₂ with h | h
            · rw [max_eq_right h]
              exact min_eq_left (hx₂_le_pb.trans hpb_le)
            · rw [max_eq_left h, ← hx₂pdef]
              exact le_antisymm hdir (le_min h (hx₂_le_pb.trans hpb_le))
      · -- lower
        rw [not_le] at hdir
        have hq₂γ : ¬ γ ≤ q₂ := by
          intro h
          apply absurd hdir (not_lt.mpr _)
          rw [hx₂def, ite_eq_left h]; exact le_max_left _ _
        have hx₂q : x₂ = q₂ := by rw [hx₂def, ite_eq_right hq₂γ]
        have hση : σ η₁ ≤ q₂ := by
          have hle : σ η₁ ≤ g 3 := by
            by_contra hlt
            rw [not_le] at hlt
            have : x₁ = g 3 := by rw [hx₁def, min_eq_right hlt.le]
            have h2 : x₂p ≤ g 3 := min_le_right _ _
            exact absurd (lt_of_lt_of_le hdir (h2.trans (this ▸ hx₁_le_x₂))) (lt_irrefl _)
          have : x₁ = σ η₁ := by rw [hx₁def, min_eq_left hle]
          rw [← this, ← hx₂q]; exact hx₁_le_x₂
        refine ⟨lowerShifter σ (Ordinal.omega0 * (1 : ℕ) + (4 : ℕ)) q₂,
          hw.lower 3 hgK fp_ξ hq₂vis (fun a ha => (hw.mono (le_η₁_of_lt_ξ ha)).trans hση),
          (lowerShifter_of_not_mem (not_inTail_bot _)).trans hw.bot,
          lowerShifter_of_not_mem (not_inTail_of_lt v₀_lt_ξ),
          lowerShifter_of_not_mem (not_inTail_of_lt η₁_lt_ξ),
          lowerShifter_of_not_mem not_inTail_γ₁, ?_⟩
        have hd' : q₂ ≤ x₂p := by rw [← hx₂q]; exact hdir.le
        rw [lowerShifter_of_mem inTail_γ₀, hx₂q, min_right_comm, ← hx₂pdef]
        exact min_eq_right hd'
    obtain ⟨σ', hw', hσ'bot, hσ'v₀, hσ'η₁, hσ'γ₁, hσ'γ₀⟩ := hσ'
    have mw : MixedWitness p g σ' x₁ x₂ :=
      { wit := hw'
        hgK := hgK
        heq := by
          intro y
          rw [heq y]
          rcases rowX₁_b₁_cases y with h | h | h <;> rw [h]
          · rw [hσ'bot, hw.bot]
          · rw [hσ'v₀]
          · rw [hσ'γ₁]
        hx₁ := by rw [hσ'η₁]
        hx₂ := hσ'γ₀ }
    refine ⟨ext₁ p x₁ x₂, respects_ext₁ hp mw, ?_, fun d => ext₁_emb p _ _ d⟩
    intro d
    rcases cases₂' d with ⟨c, rfl⟩ | rfl | rfl
    · exact hagree_img _ _ c
    · rw [ext₁_a₁]; exact hx₁γ
    · rw [ext₁_a₂]; exact hx₂γ

end Main

end VaughtConjecture.Knight
