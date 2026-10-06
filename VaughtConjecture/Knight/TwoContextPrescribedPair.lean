/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TwoContextAmalgam
public import VaughtConjecture.Knight.StageReindex

/-! # The original prescribed pair: common stage, shared-face compatibility, and the source
equations of the forced identification

**The fresh face, settled** (`reindex_p₁_Q`): input B's specified labelled type `p₁` is a
reindexing of the amalgam's fresh face `Q.restrictFace embB` through the copy embedding — the
literal face equation up to the enumeration of the cells (`typeMap_embB` gives only the
restriction with the induced enumeration; the copy embedding is not monotone in the indices).

**The original pair at a common stage**: `p₀'` is input A's specified labelling `p₀` (the row
of its cap `ω+4`) at the stage `ω·3` of `p₁`.  **Exact shared-face compatibility**
(`reindex_shared`): the restrictions of `p₀'` and of `p₁` to the shared pair `{1, 2}` are
reindexings of each other — graded indices, labels and rows agree cell by cell.  So the two
specified labellings are compatible on the shared face; the obstruction to realizing both is
not on the shared face.

**The source equations of the forced identification** (`mixed_source_eq`): every non-mute
controller of the fixed glue reads the same value at input A's level-one witness `H₀old` (on the
A face) and at its copy `H₀new` (on the fresh face), because both retract to the same cell of the
three-cell family; the controller-probe lemma turns this into `forced_identification` for every
respecting labelling, while the specified labels there differ (`specified_labels_differ`:
`ω+4` versus `ω·2+3`).  Separating the two occurrences requires mixed-controller rows reading
*different* sources there — `Knight/TwoContextSeparation.lean`.

Not claimed: any logical extension-spectrum distinction, or realization inside fixed models.
Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## The fresh face, settled: input B's labelled type is a reindexing of the restriction -/

section FreshFace

theorem D₂_plan : D₂.plan = plan₄ := rfl
theorem C₁_plan : C₁.plan = Prop3.plan := rfl

theorem pullCell_embB : ∀ S ∈ plan₄, S ⊆ ({1, 2, 3} : Finset (Fin 4)) →
    (Finset.univ.filter fun i => embB i ∈ S) = S.image fold := by decide

theorem restrict_plan_embB : (D₂.restrictFace embB embB_mem).plan = Prop3.plan := by
  change ((Finset.univ : Finset (Fin 3)).powerset.filter fun C => C.image embB ∈ plan₄) =
    Prop3.plan
  decide

theorem visible_embB_iff (d : Cell D₂) :
    D₂.scope d ⊆ Finset.univ.image embB ↔ D₂.scope d ⊆ ({1, 2, 3} : Finset (Fin 4)) := by
  rw [embB_image]

/-- A cell visible on the fresh face lies below `({1,2,3}, 3)`. -/
theorem mem_face_of_visible {d : Cell D₂} (h : D₂.scope d ⊆ Finset.univ.image embB) :
    GradedLe (D₂.cell d) ({1, 2, 3}, 3) := by
  rw [visible_embB_iff] at h
  refine ⟨h, ?_⟩
  change D₂.grade d ≤ 3
  apply grade_le_three_of_not_mute
  intro hm
  change D₂.cell d = _ at hm
  have := congrArg Prod.fst hm
  change D₂.scope d = Finset.univ at this
  rw [this] at h
  exact absurd (h (Finset.mem_univ 0)) (by decide)

/-- **The copy embedding is a bijection** onto the cells visible on the fresh face. -/
noncomputable def copyEquiv :
    Cell C₁ ≃ {d : Cell D₂ // D₂.scope d ⊆ Finset.univ.image embB} :=
  Equiv.ofBijective (fun c => ⟨copyB c, (visible_embB_iff _).mpr (copyB_mem c).1⟩)
    ⟨fun c c' h => by
      have := congrArg (fun z => retB z.1) h
      simp only [retB_copyB] at this
      exact this,
     fun d => by
      refine ⟨retB d.1, Subtype.ext ?_⟩
      change copyB (retB d.1) = d.1
      have h := retB_inj zero_not_mem_B ⟨copyB (retB d.1), copyB_mem _⟩
        ⟨d.1, mem_face_of_visible d.2⟩
        (by change retB (copyB (retB d.1)) = retB d.1; rw [retB_copyB])
      exact congrArg Subtype.val h⟩

theorem copyEquiv_val (c : Cell C₁) : (copyEquiv c).1 = copyB c := rfl

/-- **The fresh face, settled**: `p₁` is a reindexing of the amalgam's restriction along the fresh
face — indices, labels and rows agree cell by cell through the copy embedding. -/
theorem reindex_p₁_Q : StageType.Reindex p₁ (Q.restrictFace embB embB_mem) := by
  refine reindex_restrictFace Q embB embB_mem p₁ copyEquiv restrict_plan_embB ?_ ?_ ?_
  · intro c
    change (Finset.univ.filter fun i => embB i ∈ D₂.scope (copyB c), D₂.grade (copyB c)) =
      C₁.cell c
    rw [pullCell_embB _ (D₂.scope_mem_plan _) (copyB_mem c).1]
    exact (cell_copyB c).symm
  · intro c
    change Q.label (copyB c) = p₁.label c
    exact label_copyB c
  · intro Sig d d' hd'
    have hd'' : d'.1 = copyB d.1 := hd'
    change rows₂.E (copyB Sig) d' = family₁.rows.E Sig d
    exact rows₂_E_emb₁ (not_mute_copyB Sig) d' Sig d.1 (ret₂_copyB Sig)
      (by rw [hd'']; exact ret₂_copyB d.1) d.2

end FreshFace

/-! ## The original pair at a common stage, and exact shared-face compatibility -/

section Shared

/-- Input A's specified row is bounded by its cap `ω+4`. -/
theorem rowX_a₂_le (y : family₂.X) : family₂.rowX a₂X y ≤ γ₀ := by
  rcases y with c | H | s | a
  · rw [rowX_a₂_inl]; exact t₀.F_le c
  · rw [eq_H₀X, rowX_a₂_H]
  · rw [eq_s₀X, rowX_a₂_s]
  · have ha : a.1 ∈ ({a₁, a₂, b₁} : Finset (CappedCore3 Prop3.gradeP T₀)) := a.2
    rcases Finset.mem_insert.mp ha with h | h
    · have e : a = ⟨a₁, Finset.mem_insert_self _ _⟩ := Subtype.ext h
      rw [e]; change family₂.rowX a₂X a₁X ≤ γ₀; rw [rowX_a₂_a₁]; exact η₁_le_γ₀
    rcases Finset.mem_insert.mp h with h | h
    · have e : a = ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩ := Subtype.ext h
      rw [e]; change family₂.rowX a₂X a₂X ≤ γ₀; rw [rowX_a₂_a₂]
    · have e : a = ⟨b₁, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))⟩ := Subtype.ext (Finset.mem_singleton.mp h)
      rw [e]; change family₂.rowX a₂X b₁X ≤ γ₀; rw [rowX_a₂_b₁]

theorem p₀_label_eq (x : family₀.X) : p₀.label (family₀.e x) = family₂.rowX a₂X (embX₀ x) := by
  change family₀.rows.E top ⟨family₀.e x, _⟩ = _
  change family₀.rowX (family₀.e.symm (family₀.e _)) (family₀.e.symm (family₀.e x)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, rowX₀_eq]
  change family₂.rowX (embX₀ a₂X₀) (embX₀ x) = _
  rw [embX₀_a₂]

/-- **Input A's specified labelling at the common stage `ω·3`.** -/
noncomputable def p₀' : S stage₃ 3 where
  scheme := semScheme₀
  label := p₀.label
  label_bound d := by
    left
    rw [← Equiv.apply_symm_apply family₀.e d, p₀_label_eq]
    exact lt_of_le_of_lt (rowX_a₂_le _) (lt_of_le_of_lt γ₀_le_γ₁ γ₁_lt_stage₃)
  respects := p₀.respects

theorem p₀'_label (d : Cell C₀) : p₀'.label d = p₀.label d := rfl

/-- The shared pair `{1, 2}`, as a face of either input. -/
def fAB : Fin 2 ↪ Fin 3 := ⟨Fin.succ, Fin.succ_injective _⟩

theorem fAB_image : Finset.univ.image fAB = ({1, 2} : Finset (Fin 3)) := by decide
theorem fAB_mem₀ : Finset.univ.image fAB ∈ C₀.plan := by rw [fAB_image]; decide
theorem fAB_mem₁ : Finset.univ.image fAB ∈ C₁.plan := by rw [fAB_image]; decide

theorem exists_inl_of_scope₁ (i : Cell C₁) (h : C₁.scope i ≠ Finset.univ) :
    ∃ c, family₁.e.symm i = .inl c := by
  have hs : C₁.scope i = (family₁.cellX (family₁.e.symm i)).1 :=
    congrArg Prod.fst (Family.cell_eq family₁ i)
  rcases hw : family₁.e.symm i with c | H | s | a
  · exact ⟨c, rfl⟩
  all_goals exact absurd (by rw [hs, hw]; rfl) h

theorem scope_ne_univ_of_visible₁ {d : Cell C₁} (h : C₁.scope d ⊆ Finset.univ.image fAB) :
    C₁.scope d ≠ Finset.univ := by
  intro hu; rw [hu, fAB_image] at h; exact absurd (h (Finset.mem_univ 0)) (by decide)
theorem scope_ne_univ_of_visible₀ {d : Cell C₀} (h : C₀.scope d ⊆ Finset.univ.image fAB) :
    C₀.scope d ≠ Finset.univ := by
  intro hu; rw [hu, fAB_image] at h; exact absurd (h (Finset.mem_univ 0)) (by decide)

/-- The proper cells of input B, as cells of input A (junk on full cells). -/
noncomputable def embX₁₀ : family₁.X → family₀.X
  | .inl c => .inl c
  | .inr _ => .inr (.inr (.inr ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩))

/-- The visible cells of the two inputs on the shared pair correspond through their proper cells. -/
noncomputable def sharedEquiv :
    {d : Cell C₁ // C₁.scope d ⊆ Finset.univ.image fAB} ≃
      {d : Cell C₀ // C₀.scope d ⊆ Finset.univ.image fAB} where
  toFun d := ⟨family₀.e (embX₁₀ (family₁.e.symm d.1)), by
    obtain ⟨c, hc⟩ := exists_inl_of_scope₁ d.1 (scope_ne_univ_of_visible₁ d.2)
    rw [hc]
    change (C₀.cell (family₀.e (Sum.inl c))).1 ⊆ _
    rw [Family.cell_e]
    have := d.2
    change (C₁.cell d.1).1 ⊆ _ at this
    rw [Family.cell_eq, hc] at this
    exact this⟩
  invFun d := ⟨family₁.e (embX₀₁ (family₀.e.symm d.1)), by
    obtain ⟨c, hc⟩ := exists_inl_of_scope d.1 (scope_ne_univ_of_visible₀ d.2)
    rw [hc]
    change (C₁.cell (family₁.e (Sum.inl c))).1 ⊆ _
    rw [Family.cell_e]
    have := d.2
    change (C₀.cell d.1).1 ⊆ _ at this
    rw [Family.cell_eq, hc] at this
    exact this⟩
  left_inv d := by
    apply Subtype.ext
    obtain ⟨c, hc⟩ := exists_inl_of_scope₁ d.1 (scope_ne_univ_of_visible₁ d.2)
    change family₁.e (embX₀₁ (family₀.e.symm (family₀.e (embX₁₀ (family₁.e.symm d.1))))) = d.1
    rw [Equiv.symm_apply_apply, hc]
    change family₁.e (Sum.inl c) = d.1
    rw [← hc, Equiv.apply_symm_apply]
  right_inv d := by
    apply Subtype.ext
    obtain ⟨c, hc⟩ := exists_inl_of_scope d.1 (scope_ne_univ_of_visible₀ d.2)
    change family₀.e (embX₁₀ (family₁.e.symm (family₁.e (embX₀₁ (family₀.e.symm d.1))))) = d.1
    rw [Equiv.symm_apply_apply, hc]
    change family₀.e (Sum.inl c) = d.1
    rw [← hc, Equiv.apply_symm_apply]

theorem sharedEquiv_val (d : {d : Cell C₁ // C₁.scope d ⊆ Finset.univ.image fAB}) :
    (sharedEquiv d).1 = family₀.e (embX₁₀ (family₁.e.symm d.1)) := rfl

theorem restrict_plan_fAB : (C₀.restrictFace fAB fAB_mem₀).plan =
    (semScheme₁.restrictFace fAB fAB_mem₁).scheme.plan := rfl

/-- **Exact shared-face compatibility of the original pair**: the restriction of `p₁` to the
shared pair is a reindexing of the restriction of `p₀'` (indices, labels and rows agree cell by
cell, through the proper cells). -/
theorem reindex_shared :
    StageType.Reindex (p₁.restrictFace fAB fAB_mem₁) (p₀'.restrictFace fAB fAB_mem₀) := by
  refine reindex_restrictFace p₀' fAB fAB_mem₀ (p₁.restrictFace fAB fAB_mem₁)
    ((restrictEquiv C₁ fAB fAB_mem₁).trans sharedEquiv) rfl ?_ ?_ ?_
  · intro i
    change C₀.pullCell fAB (family₀.e (embX₁₀ (family₁.e.symm (toCell C₁ fAB fAB_mem₁ i)))) =
      C₁.pullCell fAB (toCell C₁ fAB fAB_mem₁ i)
    obtain ⟨c, hc⟩ := exists_inl_of_scope₁ _ (scope_ne_univ_of_visible₁
      (CellScheme.restrictFace.scope_toCell_subset C₁ fAB fAB_mem₁ i))
    rw [hc]
    have h1 : C₀.cell (family₀.e (embX₁₀ (Sum.inl c))) = (c.scope, c.gradeP) := Family.cell_e _ _
    have h2 : C₁.cell (toCell C₁ fAB fAB_mem₁ i) = (c.scope, c.gradeP) := by
      rw [Family.cell_eq, hc]; rfl
    change (Finset.univ.filter fun j => fAB j ∈ (C₀.cell _).1, (C₀.cell _).2) =
      (Finset.univ.filter fun j => fAB j ∈ (C₁.cell _).1, (C₁.cell _).2)
    rw [h1, h2]
  · intro i
    change p₀.label (family₀.e (embX₁₀ (family₁.e.symm (toCell C₁ fAB fAB_mem₁ i)))) =
      p₁.label (toCell C₁ fAB fAB_mem₁ i)
    obtain ⟨c, hc⟩ := exists_inl_of_scope₁ _ (scope_ne_univ_of_visible₁
      (CellScheme.restrictFace.scope_toCell_subset C₁ fAB fAB_mem₁ i))
    rw [hc, ← Equiv.apply_symm_apply family₁.e (toCell C₁ fAB fAB_mem₁ i), hc, p₁_label,
      p₀_label_eq]
    change family₂.rowX a₂X (Sum.inl c) = family₂.rowX b₁X (Sum.inl c)
    rw [rowX_a₂_inl, rowX_b₁_inl]
  · intro Sig d d' _
    change family₀.rows.E (family₀.e (embX₁₀ (family₁.e.symm (toCell C₁ fAB fAB_mem₁ Sig)))) d' =
      family₁.rows.E (toCell C₁ fAB fAB_mem₁ Sig) (belowMap C₁ fAB fAB_mem₁ Sig d)
    obtain ⟨c, hc⟩ := exists_inl_of_scope₁ _ (scope_ne_univ_of_visible₁
      (CellScheme.restrictFace.scope_toCell_subset C₁ fAB fAB_mem₁ Sig))
    change family₀.rowX (family₀.e.symm (family₀.e (embX₁₀ (family₁.e.symm
      (toCell C₁ fAB fAB_mem₁ Sig))))) (family₀.e.symm d'.1) =
      family₁.rowX (family₁.e.symm (toCell C₁ fAB fAB_mem₁ Sig))
        (family₁.e.symm (belowMap C₁ fAB fAB_mem₁ Sig d).1)
    rw [Equiv.symm_apply_apply, hc]
    rfl

end Shared

/-! ## The source equations forcing the witness-copy identification in the fixed glue -/

section Forced

/-- The two occurrences of input A's level-one witness: the old cell, and its copy on the fresh
face. -/
noncomputable def H₀old : Cell D₂ := Fin.castAdd (Fintype.card New₂) (family₀.e H₀X₀)
noncomputable def H₀new : Cell D₂ := copyB (family₁.e H₀X₁)

theorem ret₂_H₀old_new : ret₂ H₀old = ret₂ H₀new := ret₂_castAdd_H₀

/-- **The mixed-controller source equations**: every non-mute controller reads the same value at
the two occurrences, because both retract to the same cell of the three-cell family. -/
theorem mixed_source_eq (c : Cell D₂) (hc : ¬ mute₂ c)
    (hA : GradedLe (D₂.cell H₀old) (D₂.cell c)) (hB : GradedLe (D₂.cell H₀new) (D₂.cell c)) :
    rows₂.E c ⟨H₀old, hA⟩ = rows₂.E c ⟨H₀new, hB⟩ := by
  exact (rows₂_E_of_not_mute hc _).trans
    ((family₂.rows.E_congr' rfl ret₂_H₀old_new).trans (rows₂_E_of_not_mute hc _).symm)

/-- **The forced identification** (rigidity, from the source equations): every respecting
labelling of a full-scope lower set of grade at most three labels the two occurrences equally. -/
theorem forced_identification {j : ℕ} (hj : j ≤ 3) {q : D₂.below (Finset.univ, j) → ExtOrd}
    (hq : RespectsSemanticsBelow rows₂ (Finset.univ, j) q)
    (hA : GradedLe (D₂.cell H₀old) (Finset.univ, j))
    (hB : GradedLe (D₂.cell H₀new) (Finset.univ, j)) :
    q ⟨H₀old, hA⟩ = q ⟨H₀new, hB⟩ :=
  rigidity₂ hj hq _ _ ret₂_H₀old_new

/-- The specified labels at the two occurrences differ: `ω+4` and `ω·2+3`. -/
theorem specified_labels_differ : p₀'.label (family₀.e H₀X₀) ≠ p₁.label (family₁.e H₀X₁) := by
  rw [p₀'_label, p₀_label_H₀, p₁_label_H₀]; exact γ₁_ne_γ₀.symm

end Forced

end VaughtConjecture.Knight
