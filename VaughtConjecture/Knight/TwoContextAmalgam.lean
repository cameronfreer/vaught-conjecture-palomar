/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FaceExtB

/-! # The labelled amalgam of the two contexts

**The unconditional glued domain** `glueDomain : SemScheme 4` (`semSchemeGlue'` with both face
obligations proved).

**Which pairs of input labellings are simultaneously realizable.**  Rigidity (`rigidity₂`)
forces every respecting labelling of the glued domain to agree at input A's level-one witness
`H₀` and at input B's copy of it.  Input A's specified labelling `p₀` (the row of its cap `ω+4`)
reads `ω+4` there, while input B's specified labelling `p₁` (the row of its cap `ω·2+3`) reads
`ω·2+3` there: the pair `(p₀, p₁)` is **not** simultaneously realizable (`not_realizable_p₀_p₁`).

**The amalgam.**  `Q : S stage₃ 4` labels the glued domain by input B's row pulled back along the
retraction.  Its initial face is literally the labelled type `pA` of `semScheme₀` (the coface
equation `isCoface_pA_Q`), whose labels are input B's row read at input A's cells — input A with
its witnesses raised to input B's cap (`ω·2+3` at `H₀`, `s₀`; `ω+4` at `a₂`; `ω+3` at `a₁`).  Its
fresh face carries input B's specified labelling `p₁` literally, cell by cell, through the copy
embedding `copyB` (`label_copyB`, `rows_copyB`, `cell_copyB`); `typeMap` along the fresh face is
defined (`typeMap_embB`), but its value is the restriction with the induced enumeration, which is
not input B's own enumeration (the copy embedding is not monotone in the cell indices).

Not claimed: any logical extension-spectrum distinction, or realization inside fixed models.
Construction-private (not root-exported). -/


@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

section Amalgam

/-- **The glued domain, unconditional.** -/
noncomputable def glueDomain : SemScheme 4 := semSchemeGlue' faceExtA' faceExtB'

theorem glueDomain_scheme : glueDomain.scheme = D₂ := rfl
theorem glueDomain_rows : glueDomain.rows = rows₂ := rfl

/-- The stage `ω·3`, above input B's cap. -/
noncomputable abbrev stage₃ : Ordinal.{0} := Ordinal.omega0 * (2 : ℕ) + Ordinal.omega0

theorem γ₁_lt_stage₃ : γ₁ < ofOrd stage₃ := by
  rw [γ₁_eq, ofOrd_lt_ofOrd]
  exact add_lt_add_right (Ordinal.natCast_lt_omega0 3) _

/-- Input B's row is bounded by its cap. -/
theorem rowX_b₁_le (x : family₂.X) : family₂.rowX b₁X x ≤ γ₁ := by
  rcases x with c | H | s | a
  · rw [rowX_b₁_inl]; exact (t₀.F_le c).trans γ₀_le_γ₁
  · rw [eq_H₀X, rowX_b₁_H]
  · rw [eq_s₀X, rowX_b₁_s]
  · have ha : a.1 ∈ ({a₁, a₂, b₁} : Finset (CappedCore3 Prop3.gradeP T₀)) := a.2
    rcases Finset.mem_insert.mp ha with h | h
    · have e : a = ⟨a₁, Finset.mem_insert_self _ _⟩ := Subtype.ext h
      rw [e]
      change family₂.rowX b₁X a₁X ≤ γ₁
      rw [rowX_b₁_a₁]; exact η₁_le_γ₀.trans γ₀_le_γ₁
    rcases Finset.mem_insert.mp h with h | h
    · have e : a = ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩ := Subtype.ext h
      rw [e]
      change family₂.rowX b₁X a₂X ≤ γ₁
      rw [rowX_b₁_a₂]; exact γ₀_le_γ₁
    · have e : a = ⟨b₁, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))⟩ := Subtype.ext (Finset.mem_singleton.mp h)
      rw [e]
      change family₂.rowX b₁X b₁X ≤ γ₁
      rw [rowX_b₁_b₁]

/-! ### Input B's specified labelling: the row of its cap -/

noncomputable def top₁ : Cell C₁ := family₁.e b₁X₁

theorem cell_top₁ : C₁.cell top₁ = (Finset.univ, 3) := Family.cell_e _ _

theorem hall₁ (d : Cell C₁) : GradedLe (C₁.cell d) (C₁.cell top₁) := by
  rw [cell_top₁]; exact le_top₁ d

/-- **Input B labelled by the row of its cap `b₁`.** -/
noncomputable def p₁ : S stage₃ 3 where
  scheme := semScheme₁
  label d := family₁.rows.E top₁ ⟨d, hall₁ d⟩
  label_bound d := by
    left
    change family₁.rowX (family₁.e.symm (family₁.e b₁X₁)) (family₁.e.symm d) < _
    rw [Equiv.symm_apply_apply, rowX₁_eq, embX₁_b₁]
    exact lt_of_le_of_lt (rowX_b₁_le _) γ₁_lt_stage₃
  respects := (family₁.rows_isConsistent top₁).toRespects hall₁

theorem p₁_label (x : family₁.X) : p₁.label (family₁.e x) = family₂.rowX b₁X (embX₁ x) := by
  change family₁.rowX (family₁.e.symm (family₁.e b₁X₁)) (family₁.e.symm (family₁.e x)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, rowX₁_eq, embX₁_b₁]

/-! ### The amalgam's labelling: input B's row pulled back -/

theorem cell_e₂_b₁ : C₂.cell (family₂.e b₁X) = (Finset.univ, 3) := Family.cell_e _ _

theorem grade_le_three_of_not_mute {d : Cell D₂} (hd : ¬ mute₂ d) : D₂.grade d ≤ 3 := by
  by_contra h4
  rw [not_le] at h4
  have h := D₂.grade_le_card_scope d
  have hc : (D₂.scope d).card ≤ 4 := (Finset.card_le_univ _).trans (by simp)
  apply hd
  refine Prod.ext ?_ ?_
  · apply Finset.eq_univ_of_card; rw [Fintype.card_fin]; change (D₂.scope d).card = 4; omega
  · change D₂.grade d = 4; omega

theorem hret₂ {d : Cell D₂} (hd : ¬ mute₂ d) :
    GradedLe (C₂.cell (ret₂ d)) (C₂.cell (family₂.e b₁X)) := by
  rw [cell_e₂_b₁]
  refine ⟨Finset.subset_univ _, ?_⟩
  change C₂.grade (ret₂ d) ≤ 3
  rw [← grade_ret₂ d hd]
  exact grade_le_three_of_not_mute hd

/-- **The labelling of the glued domain**: input B's row at the retraction, `⊥` at the mute cell. -/
noncomputable def labelQ (d : Cell D₂) : ExtOrd :=
  if hd : mute₂ d then ⊥ else family₂.rows.E (family₂.e b₁X) ⟨ret₂ d, hret₂ hd⟩

theorem labelQ_of_not_mute {d : Cell D₂} (hd : ¬ mute₂ d) :
    labelQ d = family₂.rows.E (family₂.e b₁X) ⟨ret₂ d, hret₂ hd⟩ := by
  unfold labelQ; rw [dite_of_neg hd]

theorem labelQ_of_mute {d : Cell D₂} (hd : mute₂ d) : labelQ d = ⊥ := by
  unfold labelQ; rw [dite_of_pos hd]

theorem labelQ_eq_rowX {d : Cell D₂} (hd : ¬ mute₂ d) :
    labelQ d = family₂.rowX b₁X (family₂.e.symm (ret₂ d)) := by
  rw [labelQ_of_not_mute hd]
  change family₂.rowX (family₂.e.symm (family₂.e b₁X)) _ = _
  rw [Equiv.symm_apply_apply]

theorem labelQ_lt_stage (d : Cell D₂) : labelQ d < ofOrd stage₃ := by
  by_cases hd : mute₂ d
  · rw [labelQ_of_mute hd]; exact bot_lt_ofOrd _
  · rw [labelQ_eq_rowX hd]; exact lt_of_le_of_lt (rowX_b₁_le _) γ₁_lt_stage₃

/-- The fresh copy of `b₁` at full scope: its row is the labelling. -/
noncomputable def ub₁ : Cell D₂ :=
  Fin.natAdd C₀.card ((Fintype.equivFin New₂) (.inr (.inl ⟨family₂.e b₁X, by
    change (C₂.cell (family₂.e b₁X)).1 = _; rw [cell_e₂_b₁]⟩)))

theorem cell_ub₁ : D₂.cell ub₁ = (Finset.univ, 3) := by
  unfold ub₁
  rw [D₂_cell_natAdd, Equiv.symm_apply_apply]
  change (Finset.univ, (C₂.cell (family₂.e b₁X)).2) = _
  rw [cell_e₂_b₁]

theorem ret₂_ub₁ : ret₂ ub₁ = family₂.e b₁X := by
  unfold ub₁; rw [ret₂_natAdd, Equiv.symm_apply_apply]; rfl

theorem not_mute_ub₁ : ¬ mute₂ ub₁ := by
  intro h
  change D₂.cell ub₁ = _ at h
  rw [cell_ub₁] at h
  exact absurd (congrArg Prod.snd h) (by decide)

theorem below_ub₁ {d : Cell D₂} (hd : ¬ mute₂ d) : GradedLe (D₂.cell d) (D₂.cell ub₁) := by
  rw [cell_ub₁]
  refine ⟨Finset.subset_univ _, ?_⟩
  change D₂.grade d ≤ 3
  rw [grade_ret₂ d hd]
  exact (hret₂ hd).2.trans (by rw [cell_e₂_b₁])

theorem rows₂_ub₁ (d : D₂.below (D₂.cell ub₁)) : rows₂.E ub₁ d = labelQ d.1 := by
  have hd : ¬ mute₂ d.1 := hmute_below₂ ub₁ d.1 not_mute_ub₁ d.2
  rw [rows₂_E_of_not_mute not_mute_ub₁, labelQ_of_not_mute hd]
  exact family₂.rows.E_congr' ret₂_ub₁ rfl

/-- **The labelled amalgam.** -/
noncomputable def Q : S stage₃ 4 where
  scheme := glueDomain
  label := labelQ
  label_bound d := Or.inl (labelQ_lt_stage d)
  respects := by
    have hu := rows₂_isConsistent ub₁
    refine ⟨?_, ?_, ?_⟩
    · intro d
      by_cases hd : mute₂ d
      · rw [labelQ_of_mute hd]; exact (extVisibilityReplace_bot _ _).symm
      · have := hu.orderly ⟨d, below_ub₁ hd⟩
        dsimp only at this
        erw [rows₂_ub₁] at this
        exact this
    · intro Sig
      by_cases hSig : mute₂ Sig
      · refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
        funext d
        rw [labelQ_of_mute hSig, min_eq_right bot_le]
      · have key := hu.locality ⟨Sig, below_ub₁ hSig⟩
        refine transformsTo_congr rfl rfl ?_ key
        funext d
        erw [rows₂_ub₁, rows₂_ub₁]
        rfl
    · intro Sig Xi₀ hs hg
      by_cases hSig : mute₂ Sig
      · have hXi : mute₂ Xi₀ := by
          change D₂.cell Xi₀ = _
          change D₂.cell Sig = _ at hSig
          have hs' : Finset.univ ⊆ D₂.scope Xi₀ := by
            have := hs; change (D₂.cell Sig).1 ⊆ _ at this; rw [hSig] at this; exact this
          have hg' : D₂.grade Xi₀ = 4 := by
            have := hg; change (D₂.cell Sig).2 = _ at this; rw [hSig] at this; exact this.symm
          exact Prod.ext (Finset.univ_subset_iff.mp hs') hg'
        refine ⟨Xi₀, rfl, ?_⟩
        rw [labelQ_of_mute hSig]; exact bot_le
      · have hXi : ¬ mute₂ Xi₀ := by
          intro hXi
          apply hSig
          change D₂.cell Xi₀ = _ at hXi
          change D₂.cell Sig = _
          have hg' : D₂.grade Sig = 4 := by
            have := hg; change _ = (D₂.cell Xi₀).2 at this; rw [hXi] at this; exact this
          have hs' : D₂.scope Sig = Finset.univ := by
            apply Finset.eq_univ_of_card
            have := D₂.grade_le_card_scope Sig
            have h4' : (D₂.scope Sig).card ≤ 4 := (Finset.card_le_univ _).trans (by simp)
            rw [Fintype.card_fin]; omega
          exact Prod.ext hs' hg'
        obtain ⟨Xi, hcell, hle⟩ := hu.availability ⟨Sig, below_ub₁ hSig⟩ ⟨Xi₀, below_ub₁ hXi⟩ hs hg
        refine ⟨Xi.1, hcell, ?_⟩
        erw [rows₂_ub₁, rows₂_ub₁] at hle; exact hle

theorem Q_label (d : Cell D₂) : Q.label d = labelQ d := rfl

/-! ### The initial face: input A with its witnesses raised to input B's cap -/

/-- Input A's cells, labelled by input B's row. -/
noncomputable def labelA (i : Cell C₀) : ExtOrd := family₂.rowX b₁X (embX₀ (family₀.e.symm i))

theorem labelQ_castAdd (i : Cell C₀) : labelQ (Fin.castAdd (Fintype.card New₂) i) = labelA i := by
  rw [labelQ_eq_rowX (not_mute₂_castAdd i), ret₂_castAdd]
  change family₂.rowX b₁X (family₂.e.symm (family₂.e _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The restricted domain of the amalgam along the initial face is input A's domain. -/
theorem glueDomain_restrict : glueDomain.restrictFace Fin.castSuccEmb vis₂ = semScheme₀ := by
  refine SemScheme.ext_of_components (congrArg CellScheme.plan hE₂) (congrArg CellScheme.card hE₂)
    (fun i => CellScheme.cell_cast_of_eq hE₂ i) (fun Sig d => ?_)
  exact rows₂_restrict Sig d _

/-- Transport of respect along an equality of domains. -/
theorem RespectsSemantics.castSem {n : ℕ} {X Y : SemScheme n} (h : X = Y)
    {r : Cell X.scheme → ExtOrd} (hr : RespectsSemantics X.rows r) :
    RespectsSemantics Y.rows (fun i => r (SemScheme.castCell h.symm i)) := by
  subst h
  exact hr

theorem castCell_eq (i : Cell C₀) :
    SemScheme.castCell glueDomain_restrict.symm i = Fin.cast hcard₂.symm i := Fin.ext rfl

/-- **The initial-face labelled type**: `semScheme₀` labelled by input B's row. -/
noncomputable def pA : S stage₃ 3 where
  scheme := semScheme₀
  label := labelA
  label_bound i := Or.inl (lt_of_le_of_lt (rowX_b₁_le _) γ₁_lt_stage₃)
  respects := by
    have h' := RespectsSemantics.castSem glueDomain_restrict
      (Q.restrictFace Fin.castSuccEmb vis₂).respects
    have e : ∀ i, (Q.restrictFace Fin.castSuccEmb vis₂).label
        (SemScheme.castCell glueDomain_restrict.symm i) = labelA i := by
      intro i
      change labelQ (toCell D₂ Fin.castSuccEmb vis₂ (Fin.cast hcard₂.symm i)) = labelA i
      erw [toCell_cast₂, labelQ_castAdd]
    have e' : labelA = fun i => (StageType.restrictFace Q Fin.castSuccEmb vis₂).label
        (SemScheme.castCell glueDomain_restrict.symm i) := funext (fun i => (e i).symm)
    rw [e']
    exact h'

theorem pA_label_H₀ : pA.label (family₀.e H₀X₀) = γ₁ := by
  change family₂.rowX b₁X (embX₀ (family₀.e.symm (family₀.e H₀X₀))) = γ₁
  rw [Equiv.symm_apply_apply, embX₀_H₀, rowX_b₁_H]
theorem pA_label_a₂ : pA.label (family₀.e a₂X₀) = γ₀ := by
  change family₂.rowX b₁X (embX₀ (family₀.e.symm (family₀.e a₂X₀))) = γ₀
  rw [Equiv.symm_apply_apply, embX₀_a₂, rowX_b₁_a₂]
theorem pA_label_a₁ : pA.label (family₀.e a₁X₀) = η₁ := by
  change family₂.rowX b₁X (embX₀ (family₀.e.symm (family₀.e a₁X₀))) = η₁
  rw [Equiv.symm_apply_apply, embX₀_a₁, rowX_b₁_a₁]

/-- **The literal coface equation for the initial face.** -/
theorem isCoface_pA_Q : IsCoface pA Q := by
  change typeMap Fin.castSuccEmb Q = some pA
  rw [typeMap_eq_some _ _ vis₂]
  congr 1
  refine StageType.ext_of_components (congrArg CellScheme.plan hE₂) (congrArg CellScheme.card hE₂)
    (fun i => CellScheme.cell_cast_of_eq hE₂ i) (fun i => ?_) (fun Sig d => ?_)
  · change labelQ (toCell D₂ Fin.castSuccEmb vis₂ (Fin.cast hcard₂.symm i)) = labelA i
    erw [toCell_cast₂, labelQ_castAdd]
  · exact rows₂_restrict Sig d _

/-! ### The fresh face: input B's specified labelling, cell by cell -/

theorem le_fold_B (c : Cell C₁) :
    GradedLe (C₁.cell c) (({1, 2, 3} : Finset (Fin 4)).image fold, 3) := by
  rw [image_fold_one_two_three]; exact le_top₁ c

/-- **The copy embedding** of input B's cells into the fresh face. -/
noncomputable def copyB (c : Cell C₁) : Cell D₂ :=
  (Classical.choose (retB_surj B_face_mem zero_not_mem_B ⟨c, le_fold_B c⟩)).1

theorem copyB_mem (c : Cell C₁) : GradedLe (D₂.cell (copyB c)) ({1, 2, 3}, 3) :=
  (Classical.choose (retB_surj B_face_mem zero_not_mem_B ⟨c, le_fold_B c⟩)).2

theorem retB_copyB (c : Cell C₁) : retB (copyB c) = c :=
  Classical.choose_spec (retB_surj B_face_mem zero_not_mem_B ⟨c, le_fold_B c⟩)

theorem ret₂_copyB (c : Cell C₁) : ret₂ (copyB c) = emb₁ c := by
  have := ret₂_eq_emb₁_retB zero_not_mem_B ⟨copyB c, copyB_mem c⟩
  rw [retB_copyB] at this
  exact this

theorem not_mute_copyB (c : Cell C₁) : ¬ mute₂ (copyB c) :=
  not_mute₂_of_B zero_not_mem_B ⟨copyB c, copyB_mem c⟩

/-- The copy's graded index folds to the cell's. -/
theorem cell_copyB (c : Cell C₁) :
    C₁.cell c = ((D₂.scope (copyB c)).image fold, D₂.grade (copyB c)) := by
  have h := cell_retB zero_not_mem_B ⟨copyB c, copyB_mem c⟩
  rw [retB_copyB] at h
  exact h

/-- **Literal labels on the fresh face.** -/
theorem label_copyB (c : Cell C₁) : Q.label (copyB c) = p₁.label c := by
  rw [Q_label, labelQ_eq_rowX (not_mute_copyB c), ret₂_copyB]
  change family₂.rowX b₁X (family₂.e.symm (family₂.e _)) = family₁.rows.E top₁ ⟨c, hall₁ c⟩
  rw [Equiv.symm_apply_apply]
  change _ = family₁.rowX (family₁.e.symm (family₁.e b₁X₁)) (family₁.e.symm c)
  rw [Equiv.symm_apply_apply, rowX₁_eq, embX₁_b₁]

/-- **Literal rows on the fresh face.** -/
theorem rows_copyB (Sig : Cell C₁) (d : C₁.below (C₁.cell Sig))
    (hd : GradedLe (D₂.cell (copyB d.1)) (D₂.cell (copyB Sig))) :
    rows₂.E (copyB Sig) ⟨copyB d.1, hd⟩ = family₁.rows.E Sig d :=
  rows₂_E_emb₁ (not_mute_copyB Sig) ⟨copyB d.1, hd⟩ Sig d.1 (ret₂_copyB Sig) (ret₂_copyB d.1) d.2

/-- The embedding of the fresh face. -/
def embB : Fin 3 ↪ Fin 4 :=
  ⟨fun i => if i = 0 then 3 else Fin.castSucc i, by decide⟩

theorem embB_image : Finset.univ.image embB = ({1, 2, 3} : Finset (Fin 4)) := by decide

theorem embB_mem : Finset.univ.image embB ∈ D₂.plan := by
  rw [embB_image]; exact B_face_mem

/-- `typeMap` along the fresh face is defined; its value is the restriction with the induced
enumeration. -/
theorem typeMap_embB : typeMap embB Q = some (Q.restrictFace embB embB_mem) :=
  typeMap_eq_some _ _ embB_mem

/-! ### The specified pair `(p₀, p₁)` is not simultaneously realizable -/

theorem p₀_label_H₀ : p₀.label (family₀.e H₀X₀) = γ₀ := by
  change family₀.rows.E top ⟨family₀.e H₀X₀, _⟩ = γ₀
  change family₀.rowX (family₀.e.symm (family₀.e _)) (family₀.e.symm (family₀.e H₀X₀)) = γ₀
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, rowX₀_eq, embX₀_H₀]
  exact rowX_a₂_H

theorem p₁_label_H₀ : p₁.label (family₁.e H₀X₁) = γ₁ := by
  rw [p₁_label, embX₁_H₀, rowX_b₁_H]

theorem ret₂_castAdd_H₀ : ret₂ (Fin.castAdd (Fintype.card New₂) (family₀.e H₀X₀)) =
    ret₂ (copyB (family₁.e H₀X₁)) := by
  rw [ret₂_castAdd, ret₂_copyB]
  change family₂.e (embX₀ (family₀.e.symm (family₀.e H₀X₀))) =
    family₂.e (embX₁ (family₁.e.symm (family₁.e H₀X₁)))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]; rfl

theorem memA_H₀ : GradedLe (D₂.cell (Fin.castAdd (Fintype.card New₂) (family₀.e H₀X₀)))
    (Finset.univ, 3) := by
  rw [D₂_cell_castAdd, Family.cell_e]; exact ⟨Finset.subset_univ _, by decide⟩
theorem memB_H₀ : GradedLe (D₂.cell (copyB (family₁.e H₀X₁))) (Finset.univ, 3) :=
  (copyB_mem _).trans ⟨Finset.subset_univ _, le_rfl⟩

/-- **Input A's specified row and input B's specified row cannot be realized together**: every
respecting labelling of the glued domain agrees at `H₀` and at its copy (rigidity), where they
read `ω+4` and `ω·2+3`. -/
theorem not_realizable_p₀_p₁ :
    ¬ ∃ q : D₂.below (Finset.univ, 3) → ExtOrd, RespectsSemanticsBelow rows₂ (Finset.univ, 3) q ∧
      q ⟨Fin.castAdd (Fintype.card New₂) (family₀.e H₀X₀), memA_H₀⟩ =
        p₀.label (family₀.e H₀X₀) ∧
      q ⟨copyB (family₁.e H₀X₁), memB_H₀⟩ = p₁.label (family₁.e H₀X₁) := by
  rintro ⟨q, hq, h₀, h₁⟩
  have := rigidity₂ le_rfl hq ⟨Fin.castAdd (Fintype.card New₂) (family₀.e H₀X₀), memA_H₀⟩
    ⟨copyB (family₁.e H₀X₁), memB_H₀⟩ ret₂_castAdd_H₀
  rw [h₀, h₁, p₀_label_H₀, p₁_label_H₀] at this
  exact γ₁_ne_γ₀ this.symm

end Amalgam

end VaughtConjecture.Knight
