/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteAssembly

/-! # The concrete assembled domain: one unconditional three-level `SemScheme`

The regression instance of `Knight/FiniteAssembly.lean`: the family `family₀` at alphabet bound
`8` — proper constant `v₀ = ω+1`; base core `t₀` (`v₀` at grade one, `⊥` at grade two, cap
`γ₀ = ω+4`); capped cells `a₁ = (t₀, ω+3)`, `a₂ = (t₀, ω+4)`; the owned witnesses `t₀.wit2`,
`witness1 t₀`, `(t₀.wit2).wit`.  Eleven cells; not mute (`family₀_not_mute`); two distinct
level-three rows (`family₀_distinct_rows`).

**Bountifulness is discharged**, through the grade-one reduction:

1. the two level-one witnesses coincide (`Core3.wit2_wit`, `H₁c_eq`), so the grade-one lower set
   has one full-scope cell and five proper cells;
2. a respecting labelling of it is a proper value `u` and a full-scope value `w` with `u ≤ w`;
3. if `u < γ`, capped agreement forces `u' = u` and the labelling is kept;
4. otherwise `γ ≤ u ≤ w` and `γ ≤ u'`, and the constant labelling `u'` respects: every grade-one
   semantic entry is nonbottom (witness values are codes, the diagonal is the cap code), so the
   constant-nonbottom shifter carries each row to the constant target
   (`family₀_respects_constLabel_one`, `family₀_gradeOne_relabel`).

Hence `family₀_relabel`, `family₀_properToFull`, `family₀_bountiful`, and
`semScheme₀ : SemScheme 3` — coded, complete, consistent, bountiful — with no hypothesis.
Nothing is claimed for a general `Family`.  Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-- A nonbottom row on cells of grade `≤ 1` transforms to any constant row whose value is
self-visible at one (the constant-nonbottom shifter; the trivial witness if the value is `⊥`). -/
theorem transformsTo_const_of_ne_bot {D : Type*} {grade : D → ℕ} (hK : ∀ d, grade d ≤ 1)
    {p : D → ExtOrd} (hp : ∀ d, p d ≠ ⊥) {w : ExtOrd} (hw : SelfVis 1 w) :
    TransformsTo grade p (fun _ => w) := by
  by_cases hw0 : w = ⊥
  · subst hw0; exact TransformsTo.to_bot _
  have h := (isStepShifter_constNonbot (K := 1) hw0 hw).transformsTo hK p
  have e : (fun d => constNonbot w (p d)) = fun _ => w := by
    funext d; simp [constNonbot, hp d]
  rwa [e] at h

section Concrete

/-- The alphabet bound. -/
abbrev T₀ : ℕ := 8

theorem st₀ : Setting Prop3.gradeP T₀ := Prop3.setting le_rfl

/-! Classical equality on the fragment's cells, local to this module (the families are `Finset`
literals). -/

noncomputable abbrev decEqRow1 : DecidableEq (Row1 Prop3.gradeP T₀) := Classical.decEq _
noncomputable abbrev decEqCore2 : DecidableEq (Core2 (gradeP := Prop3.gradeP) (T := T₀)) :=
  Classical.decEq _
noncomputable abbrev decEqCappedCore3 : DecidableEq (CappedCore3 Prop3.gradeP T₀) :=
  Classical.decEq _
attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-- The proper constant `v₀ = ω + 1`, the level-three cap `γ₀ = ω + 4`, the intermediate cap
`η₁ = ω + 3`. -/
noncomputable def v₀ : ExtOrd := ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ))
noncomputable def γ₀ : ExtOrd := ofOrd (Ordinal.omega0 * (1 : ℕ) + (4 : ℕ))
noncomputable def η₁ : ExtOrd := ofOrd (Ordinal.omega0 * (1 : ℕ) + (3 : ℕ))

theorem v₀_vis : SelfVis 1 v₀ := by
  unfold v₀; rw [selfVis_ofOrd_iff, finitePart_mul_add]
theorem γ₀_vis : SelfVis 3 γ₀ := by
  unfold γ₀; rw [selfVis_ofOrd_iff, finitePart_mul_add]; omega
theorem η₁_vis : SelfVis 3 η₁ := by
  unfold η₁; rw [selfVis_ofOrd_iff, finitePart_mul_add]
theorem v₀_mem : v₀ ∈ codedAlphabet 3 T₀ := mem_codedAlphabet_of (by decide) (by decide)
theorem γ₀_mem : γ₀ ∈ codedAlphabet 3 T₀ := mem_codedAlphabet_of (by decide) (by decide)
theorem η₁_mem : η₁ ∈ codedAlphabet 3 T₀ := mem_codedAlphabet_of (by decide) (by decide)
theorem v₀_le_γ₀ : v₀ ≤ γ₀ := by
  unfold v₀ γ₀; rw [ofOrd_le_ofOrd]
  exact add_le_add_right
    (Nat.cast_le.mpr (by decide : (1 : ℕ) ≤ 4) : ((1 : ℕ) : Ordinal) ≤ (4 : ℕ)) _
theorem η₁_le_γ₀ : η₁ ≤ γ₀ := by
  unfold η₁ γ₀; rw [ofOrd_le_ofOrd]
  exact add_le_add_right
    (Nat.cast_le.mpr (by decide : (3 : ℕ) ≤ 4) : ((3 : ℕ) : Ordinal) ≤ (4 : ℕ)) _
theorem η₁_ne_γ₀ : η₁ ≠ γ₀ := by
  unfold η₁ γ₀
  intro h
  have h' := ofOrd_inj.mp h
  have h'' : ((3 : ℕ) : Ordinal) = (4 : ℕ) := add_left_cancel h'
  exact absurd (Nat.cast_injective h'') (by decide)

/-- **The base core**: `v₀` at the grade-one proper cells, `⊥` at the grade-two cells, cap `γ₀`. -/
noncomputable def t₀ : Core3 (gradeP := Prop3.gradeP) (T := T₀) where
  F c := if c.gradeP ≤ 1 then v₀ else ⊥
  γ := γ₀
  F_mem c _ := by
    split_ifs
    · exact v₀_mem
    · exact bot_mem_codedAlphabet 3 T₀
  F_bot c hc := absurd hc (by have := c.gradeP_le_two; omega)
  γ_mem := γ₀_mem
  γ_vis := γ₀_vis
  F_le c := by
    split_ifs
    · exact v₀_le_γ₀
    · exact bot_le
  F_orderly c _ := by
    split_ifs with h
    · exact v₀_vis.mono h
    · exact selfVis_bot _

theorem t₀_F_const {c c' : Prop3} (hc : c.gradeP ≤ 1) (hc' : c'.gradeP ≤ 1) : t₀.F c = t₀.F c' := by
  change (if c.gradeP ≤ 1 then v₀ else ⊥) = if c'.gradeP ≤ 1 then v₀ else ⊥
  rw [ite_eq_left hc, ite_eq_left hc']
theorem t₀_F_bot {c : Prop3} (hc : c.gradeP = 2) : t₀.F c = ⊥ := by
  change (if c.gradeP ≤ 1 then v₀ else ⊥) = ⊥
  rw [ite_eq_right (by omega)]

/-- The two capped cells over `t₀`: caps `η₁` and `γ₀`. -/
noncomputable def a₁ : CappedCore3 Prop3.gradeP T₀ := ⟨t₀, η₁, η₁_mem, η₁_vis, η₁_le_γ₀⟩
noncomputable def a₂ : CappedCore3 Prop3.gradeP T₀ := ⟨t₀, γ₀, γ₀_mem, γ₀_vis, le_rfl⟩
/-- The owned level-two witness of `t₀`. -/
noncomputable def s₀c : Core2 (gradeP := Prop3.gradeP) (T := T₀) := t₀.wit2 st₀
/-- The owned level-one witnesses of `t₀` and of `s₀c`. -/
noncomputable def H₀c : Row1 Prop3.gradeP T₀ := witness1 st₀.hT t₀.F (t₀.orderly st₀)
noncomputable def H₁c : Row1 Prop3.gradeP T₀ := s₀c.wit st₀

/-- A witness row of a row constant on the cells of grade `≤ l` is constant there. -/
theorem witnessRow_const {P : Type*} {gradeP : P → ℕ}
    {F : P → ExtOrd} {l : ℕ} {S : Finset Ordinal.{0}} {c c' : P} (hF : F c = F c')
    (hc : gradeP c ≤ l) (hc' : gradeP c' ≤ l) :
    witnessRow gradeP F l S c = witnessRow gradeP F l S c' := by
  unfold witnessRow
  rw [ite_eq_left hc, ite_eq_left hc', hF]

theorem s₀c_F_const {c c' : Prop3} (hc : c.gradeP ≤ 1) (hc' : c'.gradeP ≤ 1) :
    s₀c.F c = s₀c.F c' :=
  witnessRow_const (t₀_F_const hc hc') (by omega) (by omega)
theorem s₀c_F_bot {c : Prop3} (hc : c.gradeP = 2) : s₀c.F c = ⊥ :=
  witnessRow_bot Prop3.gradeP (by omega) (t₀_F_bot hc)
theorem H₀c_G_const {c c' : Prop3} (hc : c.gradeP ≤ 1) (hc' : c'.gradeP ≤ 1) :
    H₀c.G c = H₀c.G c' :=
  witnessRow_const (t₀_F_const hc hc') hc hc'
theorem H₁c_G_const {c c' : Prop3} (hc : c.gradeP ≤ 1) (hc' : c'.gradeP ≤ 1) :
    H₁c.G c = H₁c.G c' :=
  witnessRow_const (s₀c_F_const hc hc') hc hc'

/-- **The concrete family**: two capped level-three cells over one base, its level-two witness,
and the two level-one witnesses. -/
noncomputable def family₀ : Family st₀ where
  v := v₀
  v_ne := ofOrd_ne_bot _
  v_vis := v₀_vis
  v_coded := Or.inr ⟨1, 1, by omega, rfl⟩
  S₁ := {H₀c, H₁c}
  S₂ := {s₀c}
  S₃ := {a₁, a₂}
  ne₁ := ⟨H₀c, Finset.mem_insert_self _ _⟩
  ne₂ := ⟨s₀c, Finset.mem_singleton_self _⟩
  ne₃ := ⟨a₁, Finset.mem_insert_self _ _⟩
  const₁ H hH c c' hc hc' := by
    rcases Finset.mem_insert.mp hH with rfl | hH
    · exact H₀c_G_const hc hc'
    · rw [Finset.mem_singleton.mp hH]; exact H₁c_G_const hc hc'
  const₂ s hs c c' hc hc' := by
    rw [Finset.mem_singleton.mp hs]; exact s₀c_F_const hc hc'
  bot₂ s hs c hc := by
    rw [Finset.mem_singleton.mp hs]; exact s₀c_F_bot hc
  const₃ a ha c c' hc hc' := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact t₀_F_const hc hc'
    · rw [Finset.mem_singleton.mp ha]; exact t₀_F_const hc hc'
  bot₃ a ha c hc := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact t₀_F_bot hc
    · rw [Finset.mem_singleton.mp ha]; exact t₀_F_bot hc
  wit₂ s hs := by
    rw [Finset.mem_singleton.mp hs]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  wit₃₁ a ha := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_insert_self _ _
    · rw [Finset.mem_singleton.mp ha]; exact Finset.mem_insert_self _ _
  wit₃₂ a ha := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_singleton_self _
    · rw [Finset.mem_singleton.mp ha]; exact Finset.mem_singleton_self _

/-- **The concrete scheme is coded, complete and consistent.** -/
theorem family₀_coded : family₀.rows.IsCoded := family₀.rows_isCoded
theorem family₀_complete : family₀.scheme.IsComplete := family₀.scheme_isComplete
theorem family₀_consistent : family₀.rows.IsConsistent := family₀.rows_isConsistent

/-- **Nontriviality**: the proper part is not mute, and the two level-three cells have distinct
rows (their diagonal values are the two caps). -/
theorem family₀_not_mute : family₀.rowX (.inl .s0) (.inl .s0) ≠ ⊥ := by
  change (if Prop3.s0.gradeP ≤ 1 then v₀ else ⊥) ≠ ⊥
  rw [ite_eq_left (by decide)]
  exact ofOrd_ne_bot _

theorem family₀_distinct_rows :
    family₀.rowX (.inr (.inr (.inr ⟨a₁, Finset.mem_insert_self _ _⟩)))
        (.inr (.inr (.inr ⟨a₁, Finset.mem_insert_self _ _⟩))) ≠
      family₀.rowX (.inr (.inr (.inr ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)))
        (.inr (.inr (.inr ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩))) := by
  rw [Family.rowX_a_a, Family.rowX_a_a]
  change min (meet₃ st₀ t₀ t₀) (min η₁ η₁) ≠ min (meet₃ st₀ t₀ t₀) (min γ₀ γ₀)
  rw [CappedCore3.meet₃_self', min_self, min_self]
  change min γ₀ η₁ ≠ min γ₀ γ₀
  rw [min_self, min_eq_right η₁_le_γ₀]
  exact η₁_ne_γ₀



/-- **Step 1**: the two level-one witnesses coincide. -/
theorem H₁c_eq : H₁c = H₀c := Core3.wit2_wit st₀ t₀

theorem mem_S₁_eq {H : Row1 Prop3.gradeP T₀} (h : H ∈ family₀.S₁) : H = H₀c := by
  have h' : H ∈ ({H₀c, H₁c} : Finset (Row1 Prop3.gradeP T₀)) := h
  rcases Finset.mem_insert.mp h' with rfl | h''
  · rfl
  · rw [Finset.mem_singleton.mp h'']; exact H₁c_eq

/-- The full-scope grade-one cells of `family₀` are all the same cell. -/
theorem S₁cell_eq (H H' : ↥family₀.S₁) : H = H' :=
  Subtype.ext ((mem_S₁_eq H.2).trans (mem_S₁_eq H'.2).symm)

theorem t₀_F_eq {c : Prop3} (hc : c.gradeP ≤ 1) :
    t₀.F c = ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ)) := by
  change (if c.gradeP ≤ 1 then v₀ else ⊥) = _
  rw [ite_eq_left hc]; rfl

/-- The grade-one witness values are codes, hence nonbottom. -/
theorem H₀c_G_ne_bot {c : Prop3} (hc : c.gradeP ≤ 1) : H₀c.G c ≠ ⊥ := by
  change witnessRow Prop3.gradeP t₀.F 1 _ c ≠ ⊥
  rw [witnessRow_ofOrd Prop3.gradeP hc (t₀_F_eq hc)]
  exact ofOrd_ne_bot _

/-- The diagonal of the witness row is the cap code, nonbottom. -/
theorem H₀c_δ_ne_bot : H₀c.δ ≠ ⊥ := ofOrd_ne_bot _

/-- A cell of graded index `(univ, 1)` is a level-one cell. -/
theorem exists_S₁_of_cellX {w : family₀.X} (h : family₀.cellX w = (Finset.univ, 1)) :
    ∃ H : ↥family₀.S₁, w = .inr (.inl H) := by
  rcases w with c | H | s | a
  · exact absurd (congrArg Prod.fst h) (Prop3.scope_ne_univ c)
  · exact ⟨H, rfl⟩
  · exact absurd (congrArg Prod.snd h) (by decide : (2 : ℕ) ≠ 1)
  · exact absurd (congrArg Prod.snd h) (by decide : (3 : ℕ) ≠ 1)

/-- **Step 4**: the constant labelling respects the semantics on the grade-one lower set. -/
theorem family₀_respects_constLabel_one {u' : ExtOrd} (hu' : SelfVis 1 u') :
    RespectsSemanticsBelow family₀.rows (Finset.univ, 1)
      (family₀.constLabel (Finset.univ, 1) u') := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    have : SelfVis (family₀.cellX (family₀.e.symm d.1)).2
        (family₀.constLabel (Finset.univ, 1) u' d) := by
      change SelfVis _ (if (family₀.cellX (family₀.e.symm d.1)).2 ≤ 1 then u' else ⊥)
      split_ifs with hd
      · exact hu'.mono hd
      · exact selfVis_bot _
    exact this.symm
  · intro Sig
    have hSig1 : (family₀.cellX (family₀.e.symm Sig.1)).2 ≤ 1 := Sig.2.2
    have hgr : ∀ d : family₀.scheme.below (family₀.scheme.cell Sig.1),
        family₀.scheme.grade d.1 ≤ 1 := fun d => (d.2.2 : _ ≤ _).trans hSig1
    have htarget : (fun d : family₀.scheme.below (family₀.scheme.cell Sig.1) =>
        min (family₀.constLabel (Finset.univ, 1) u' (CellScheme.below.incl Sig d))
          (family₀.constLabel (Finset.univ, 1) u' Sig)) = fun _ => u' := by
      funext d
      change min (if (family₀.cellX (family₀.e.symm d.1)).2 ≤ 1 then u' else ⊥)
        (if (family₀.cellX (family₀.e.symm Sig.1)).2 ≤ 1 then u' else ⊥) = u'
      have hd1 : (family₀.cellX (family₀.e.symm d.1)).2 ≤ 1 := hgr d
      rw [ite_eq_left hd1, ite_eq_left hSig1, min_self]
    refine transformsTo_congr rfl rfl htarget.symm ?_
    rcases hx : family₀.e.symm Sig.1 with c | H | s | a
    · -- a proper cell: the constant source `v`
      have hc1 : c.gradeP ≤ 1 := by rw [hx] at hSig1; exact hSig1
      have hsrc : family₀.rows.E Sig.1 = fun _ => family₀.v := by
        funext d
        change family₀.rowX (family₀.e.symm Sig.1) _ = _
        rw [hx]
        change (if c.gradeP ≤ 1 then family₀.v else ⊥) = _
        rw [ite_eq_left hc1]
      exact transformsTo_congr rfl hsrc.symm rfl (transformsTo_const_const hgr family₀.v_ne hu')
    · -- the level-one cell: every source entry is nonbottom
      apply transformsTo_const_of_ne_bot hgr _ hu'
      intro d
      change family₀.rowX (family₀.e.symm Sig.1) (family₀.e.symm d.1) ≠ ⊥
      rw [hx]
      have hH : H.1 = H₀c := mem_S₁_eq H.2
      rcases hd : family₀.e.symm d.1 with c' | H' | s' | a'
      · have hc' : c'.gradeP ≤ 1 := by have := hgr d; rw [Family.grade_eq, hd] at this; exact this
        rw [Family.rowX_H_inl family₀ H c' hc', hH]
        exact H₀c_G_ne_bot hc'
      · rw [Family.rowX_H_H, hH, mem_S₁_eq H'.2, meet₁_self]
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
    change (if (family₀.cellX (family₀.e.symm Sig.1)).2 ≤ 1 then u' else ⊥) =
      if (family₀.cellX (family₀.e.symm Xi₀.1)).2 ≤ 1 then u' else ⊥
    have : (family₀.cellX (family₀.e.symm Sig.1)).2 = (family₀.cellX (family₀.e.symm Xi₀.1)).2 :=
      hg
    rw [this]

/-- **Steps 2–4**: the grade-one relabelling for `family₀`, in the form of the reviewer's
reduction. -/
theorem family₀_gradeOne_relabel :
    ∀ (q : family₀.scheme.below (Finset.univ, 1) → ExtOrd),
      RespectsSemanticsBelow family₀.rows (Finset.univ, 1) q →
      ∀ (γ u' : ExtOrd), SelfVis 1 γ → SelfVis 1 u' →
        min u' γ = min (q (family₀.cellOf (BJ := (Finset.univ, 1)) (.inl .s0)
          ⟨Finset.subset_univ _, le_rfl⟩)) γ →
        ∃ q' : family₀.scheme.below (Finset.univ, 1) → ExtOrd,
          RespectsSemanticsBelow family₀.rows (Finset.univ, 1) q' ∧
          (∀ d, min (q' d) γ = min (q d) γ) ∧
          q' (family₀.cellOf (BJ := (Finset.univ, 1)) (.inl .s0)
            ⟨Finset.subset_univ _, le_rfl⟩) = u' := by
  intro q hq γ u' _ hu' hag
  set s0c := family₀.cellOf (BJ := (Finset.univ, 1)) (.inl .s0) ⟨Finset.subset_univ _, le_rfl⟩
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
      rcases hd : family₀.e.symm d.1 with c | H | s | a
      · have hc : c.gradeP = 1 := by
          have h1 : (family₀.cellX (family₀.e.symm d.1)).2 ≤ 1 := d.2.2
          rw [hd] at h1
          have h1' : c.gradeP ≤ 1 := h1
          have := c.gradeP_pos
          omega
        have hd_eq : d = family₀.cellOf (.inl c)
            ⟨Finset.subset_univ _, by change c.gradeP ≤ 1; omega⟩ := by
          apply Subtype.ext
          change d.1 = family₀.e (.inl c)
          rw [← hd, Equiv.apply_symm_apply]
        rw [hd_eq, family₀.respects_full_const hq le_rfl (c' := Prop3.s0) hc rfl]
        exact hγu
      · -- availability lifts `s0` to the (unique) level-one cell
        obtain ⟨Xi, hcell, hle⟩ := hq.availability s0c d
          (by
            change (family₀.cellX (family₀.e.symm (family₀.e (.inl .s0)))).1 ⊆
              (family₀.cellX (family₀.e.symm d.1)).1
            rw [Equiv.symm_apply_apply, hd]
            exact Finset.subset_univ _)
          (by
            change (family₀.cellX (family₀.e.symm (family₀.e (.inl .s0)))).2 =
              (family₀.cellX (family₀.e.symm d.1)).2
            rw [Equiv.symm_apply_apply, hd]
            rfl)
        have hXi : Xi = d := by
          have h1 : family₀.cellX (family₀.e.symm Xi.1) = (Finset.univ, 1) := by
            have := hcell
            rw [Family.cell_eq, Family.cell_eq, hd] at this
            exact this
          obtain ⟨H', hH'⟩ := exists_S₁_of_cellX h1
          apply Subtype.ext
          rw [← Equiv.apply_symm_apply family₀.e Xi.1, ← Equiv.apply_symm_apply family₀.e d.1,
            hH', hd, S₁cell_eq H' H]
        rw [hXi] at hle
        exact hγu.trans hle
      · exfalso
        have h1 : (family₀.cellX (family₀.e.symm d.1)).2 ≤ 1 := d.2.2
        rw [hd] at h1
        exact absurd h1 (by decide : ¬ ((2 : ℕ) ≤ 1))
      · exfalso
        have h1 : (family₀.cellX (family₀.e.symm d.1)).2 ≤ 1 := d.2.2
        rw [hd] at h1
        exact absurd h1 (by decide : ¬ ((3 : ℕ) ≤ 1))
    -- step 4: the constant labelling `u'`
    refine ⟨family₀.constLabel (Finset.univ, 1) u', family₀_respects_constLabel_one hu', ?_, ?_⟩
    · intro d
      change min (if (family₀.cellX (family₀.e.symm d.1)).2 ≤ 1 then u' else ⊥) γ = min (q d) γ
      have hd1 : (family₀.cellX (family₀.e.symm d.1)).2 ≤ 1 := d.2.2
      rw [ite_eq_left hd1, min_eq_right hγu', min_eq_right (hq_ge d)]
    · change (if (family₀.cellX (family₀.e.symm (family₀.e (.inl .s0)))).2 ≤ 1 then u' else ⊥) = u'
      rw [Equiv.symm_apply_apply]
      exact ite_eq_left (by decide)

/-- **Step 5**: through the compiled reduction and the scout's own reductions. -/
theorem family₀_relabel : family₀.Relabel :=
  (family₀.relabel_iff_gradeOne).mpr family₀_gradeOne_relabel

theorem family₀_properToFull : family₀.ProperToFull :=
  family₀.properToFull_of_relabel family₀_relabel

theorem family₀_bountiful : family₀.rows.IsBountiful :=
  family₀.isBountiful_of_properToFull family₀_properToFull

/-- **The concrete domain with its associated semantics, unconditionally**: coded, complete,
consistent and bountiful — one non-mute, sharply coded three-level domain. -/
noncomputable def semScheme₀ : SemScheme 3 := family₀.toSemScheme family₀_properToFull

theorem semScheme₀_scheme : semScheme₀.scheme = family₀.scheme := rfl
theorem semScheme₀_rows : semScheme₀.rows = family₀.rows := rfl

end Concrete

end VaughtConjecture.Knight
