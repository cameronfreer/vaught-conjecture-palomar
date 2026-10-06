/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TwoContextInputs
public import VaughtConjecture.Knight.PartialSections
public import VaughtConjecture.Knight.FourPointDuplication

/-! # The glued four-point domain of the two contexts (claim 2: a legal common extension)

Two independently legal three-point inputs glued along the shared pair `{1, 2}`: input A
(`semScheme₀`) on the points `0, 1, 2`, input B (`semScheme₁`) on the points `1, 2, 3` (fold
`3 ↦ 0`).

* **Claim 1 (matching shared faces)** is `shared_face_agree`: the two top rows agree at every
  proper cell, in particular on the shared pair.  It is kept separate from claim 2.
* **The glued scheme `D₂`** (`Knight/ExtendOneWith` over `C₀`): old cells = input A literally;
  copies of input B's cells along `{3}, {1,3}, {1,2,3}`; one fresh copy at `(univ, k)` of every
  full cell of the three-cell family `family₂` (the mixed controllers); a mute cell at `(univ, 4)`.
  Rows: `family₂`'s rows pulled back along `ret₂ : Cell D₂ → Cell C₂`.
* **Legality.**  `D₂_complete`, `rows₂_isCoded`, **`rows₂_isConsistent`** (partial sections:
  a grade-three cell inside a face already has the face's index).  Bountifulness inside input A's
  face (`bountiful₂_A`) and input B's face (`bountiful₂_B`) transports from the inputs; full-scope
  pairs are `bountiful_full_scope`; every scope-changing pair off the two grade-three faces goes
  through rigidity (`rigidity₂`), descent along a section, `semScheme₂`'s bountifulness, and
  pullback with partial sections (`ext_of_bij`, `scopeChange_of_ext`).  The two grade-three faces
  are the obligations `FaceExtA'`, `FaceExtB'` — in three-point terms: a respecting labelling of
  one input's top lower set and a respecting labelling of the three-cell family agreeing with it
  below `γ` have a common respecting extension.  Given these, `semSchemeGlue' : SemScheme 4`; both
  are proved in `Knight/FaceExtA.lean` and `Knight/FaceExtB.lean`.
* **Literal preservation of input A**: `extendsDomainGlue`; input B's face lower sets are input
  B's with input B's rows through the bijection `eB`.
* **Freshness** (`fresh_not_duplicate`): the fresh face's level-three cell reads `ω·2+3` at itself,
  no level-three cell of input A's face does — a row/diagonal distinction only, not a distinction
  of logical extension types.

Not claimed: claim 3 (logical extension-spectrum control).  Construction-private (not
root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## Part B4: the glued four-point scheme

Points `0, 1, 2` carry input A (`family₀`, literally the old cells), points `1, 2, 3` carry input B
(`family₁`, as copies along the fold `3 ↦ 0`), the shared pair `{1, 2}` is literally shared, and the
full-scope indices carry one fresh copy of every full cell of the three-cell family `family₂`
(the mixed controllers), plus one mute cell at `(univ, 4)`.  The rows are `family₂`'s rows pulled
back along the retraction `ret₂ : Cell D₂ → Cell C₂`. -/

section Glue

noncomputable abbrev C₁ : CellScheme (ι := Fin 3) Finset.univ := family₁.scheme
noncomputable abbrev C₂ : CellScheme (ι := Fin 3) Finset.univ := family₂.scheme

theorem S₃₀_sub {a : CappedCore3 Prop3.gradeP T₀} (h : a ∈ family₀.S₃) : a ∈ family₂.S₃ := by
  have h' : a ∈ ({a₁, a₂} : Finset (CappedCore3 Prop3.gradeP T₀)) := h
  rcases Finset.mem_insert.mp h' with rfl | h''
  · exact Finset.mem_insert_self _ _
  · rw [Finset.mem_singleton.mp h'']
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem S₃₁_sub {a : CappedCore3 Prop3.gradeP T₀} (h : a ∈ family₁.S₃) : a ∈ family₂.S₃ := by
  have h' : a ∈ ({b₁} : Finset (CappedCore3 Prop3.gradeP T₀)) := h
  rw [Finset.mem_singleton.mp h']
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- The inclusions of the inputs' cells into the three-cell family. -/
def embX₀ : family₀.X → family₂.X
  | .inl c => .inl c
  | .inr (.inl H) => .inr (.inl ⟨H.1, H.2⟩)
  | .inr (.inr (.inl s)) => .inr (.inr (.inl ⟨s.1, s.2⟩))
  | .inr (.inr (.inr a)) => .inr (.inr (.inr ⟨a.1, S₃₀_sub a.2⟩))

def embX₁ : family₁.X → family₂.X
  | .inl c => .inl c
  | .inr (.inl H) => .inr (.inl ⟨H.1, H.2⟩)
  | .inr (.inr (.inl s)) => .inr (.inr (.inl ⟨s.1, s.2⟩))
  | .inr (.inr (.inr a)) => .inr (.inr (.inr ⟨a.1, S₃₁_sub a.2⟩))

theorem cellX_embX₀ (w : family₀.X) : family₂.cellX (embX₀ w) = family₀.cellX w := by
  rcases w with c | H | s | a <;> rfl
theorem cellX_embX₁ (w : family₁.X) : family₂.cellX (embX₁ w) = family₁.cellX w := by
  rcases w with c | H | s | a <;> rfl

theorem embX₀_injective : Function.Injective embX₀ := by
  rintro (c | ⟨H, hH⟩ | ⟨s, hs⟩ | ⟨a, ha⟩) (c' | ⟨H', hH'⟩ | ⟨s', hs'⟩ | ⟨a', ha'⟩) h
  all_goals simp only [embX₀, Sum.inl.injEq, Sum.inr.injEq, Subtype.mk.injEq, reduceCtorEq] at h
  all_goals first | (subst h; rfl) | (cases h; rfl)

theorem embX₁_injective : Function.Injective embX₁ := by
  rintro (c | ⟨H, hH⟩ | ⟨s, hs⟩ | ⟨a, ha⟩) (c' | ⟨H', hH'⟩ | ⟨s', hs'⟩ | ⟨a', ha'⟩) h
  all_goals simp only [embX₁, Sum.inl.injEq, Sum.inr.injEq, Subtype.mk.injEq, reduceCtorEq] at h
  all_goals first | (subst h; rfl) | (cases h; rfl)

/-- The chosen level-one and level-two representatives are the shared witnesses. -/
theorem H₀_eq₀ : family₀.H₀ = H₀c := mem_S₁_eq family₀.ne₁.choose_spec
theorem H₀_eq₁ : family₁.H₀ = H₀c := family₁_S₁ _ family₁.ne₁.choose_spec
theorem H₀_eq₂ : family₂.H₀ = H₀c := family₂_S₁ _ family₂.ne₁.choose_spec
theorem s₀_eq₀ : family₀.s₀ = s₀c := Finset.mem_singleton.mp family₀.ne₂.choose_spec
theorem s₀_eq₁ : family₁.s₀ = s₀c := Finset.mem_singleton.mp family₁.ne₂.choose_spec
theorem s₀_eq₂ : family₂.s₀ = s₀c := Finset.mem_singleton.mp family₂.ne₂.choose_spec

theorem toLow1_embX₀ (y : family₀.X) : family₂.toLow1 (embX₀ y) = family₀.toLow1 y := by
  rcases y with c | H | s | a
  · simp only [embX₀, Family.toLow1]
    split_ifs
    · rfl
    · rw [H₀_eq₂, H₀_eq₀]
  · rfl
  · simp only [embX₀, Family.toLow1]; rw [H₀_eq₂, H₀_eq₀]
  · simp only [embX₀, Family.toLow1]; rw [H₀_eq₂, H₀_eq₀]

theorem toLow1_embX₁ (y : family₁.X) : family₂.toLow1 (embX₁ y) = family₁.toLow1 y := by
  rcases y with c | H | s | a
  · simp only [embX₁, Family.toLow1]
    split_ifs
    · rfl
    · rw [H₀_eq₂, H₀_eq₁]
  · rfl
  · simp only [embX₁, Family.toLow1]; rw [H₀_eq₂, H₀_eq₁]
  · simp only [embX₁, Family.toLow1]; rw [H₀_eq₂, H₀_eq₁]

theorem toLow2_embX₀ (y : family₀.X) : family₂.toLow2 (embX₀ y) = family₀.toLow2 y := by
  rcases y with c | H | s | a
  · rfl
  · rfl
  · rfl
  · simp only [embX₀, Family.toLow2]; rw [s₀_eq₂, s₀_eq₀]

theorem toLow2_embX₁ (y : family₁.X) : family₂.toLow2 (embX₁ y) = family₁.toLow2 y := by
  rcases y with c | H | s | a
  · rfl
  · rfl
  · rfl
  · simp only [embX₁, Family.toLow2]; rw [s₀_eq₂, s₀_eq₁]

theorem toLow3_embX₀ (y : family₀.X) : family₂.toLow3 (embX₀ y) = family₀.toLow3 y := by
  rcases y with c | H | s | a <;> rfl
theorem toLow3_embX₁ (y : family₁.X) : family₂.toLow3 (embX₁ y) = family₁.toLow3 y := by
  rcases y with c | H | s | a <;> rfl

/-- **The rows of the three-cell family restrict to the inputs' rows.** -/
theorem rowX_embX₀ (x y : family₀.X) : family₂.rowX (embX₀ x) (embX₀ y) = family₀.rowX x y := by
  rcases x with c | H | s | a
  · rfl
  · change H.1.row (family₂.toLow1 (embX₀ y)) = H.1.row (family₀.toLow1 y)
    rw [toLow1_embX₀]
  · change s.1.row st₀ (family₂.toLow2 (embX₀ y)) = s.1.row st₀ (family₀.toLow2 y)
    rw [toLow2_embX₀]
  · change CappedCore3.expandedRow st₀ a.1 (family₂.toLow3 (embX₀ y)) =
      CappedCore3.expandedRow st₀ a.1 (family₀.toLow3 y)
    rw [toLow3_embX₀]

theorem rowX_embX₁ (x y : family₁.X) : family₂.rowX (embX₁ x) (embX₁ y) = family₁.rowX x y := by
  rcases x with c | H | s | a
  · rfl
  · change H.1.row (family₂.toLow1 (embX₁ y)) = H.1.row (family₁.toLow1 y)
    rw [toLow1_embX₁]
  · change s.1.row st₀ (family₂.toLow2 (embX₁ y)) = s.1.row st₀ (family₁.toLow2 y)
    rw [toLow2_embX₁]
  · change CappedCore3.expandedRow st₀ a.1 (family₂.toLow3 (embX₁ y)) =
      CappedCore3.expandedRow st₀ a.1 (family₁.toLow3 y)
    rw [toLow3_embX₁]

/-- The inclusions on cells. -/
noncomputable def emb₀ (i : Cell C₀) : Cell C₂ := family₂.e (embX₀ (family₀.e.symm i))
noncomputable def emb₁ (i : Cell C₁) : Cell C₂ := family₂.e (embX₁ (family₁.e.symm i))

theorem cell_emb₀ (i : Cell C₀) : C₂.cell (emb₀ i) = C₀.cell i := by
  change C₂.cell (family₂.e _) = _
  rw [Family.cell_e, cellX_embX₀, ← Family.cell_eq]
theorem cell_emb₁ (i : Cell C₁) : C₂.cell (emb₁ i) = C₁.cell i := by
  change C₂.cell (family₂.e _) = _
  rw [Family.cell_e, cellX_embX₁, ← Family.cell_eq]

theorem emb₀_injective : Function.Injective emb₀ := fun _ _ h =>
  family₀.e.symm.injective (embX₀_injective (family₂.e.injective h))
theorem emb₁_injective : Function.Injective emb₁ := fun _ _ h =>
  family₁.e.symm.injective (embX₁_injective (family₂.e.injective h))

/-- A cell of the three-cell family of grade `≤ 2`, or of proper scope, is in either input. -/
theorem exists_emb₀_of_cell (Xi' : Cell C₂) (i : Cell C₀)
    (h : C₂.cell Xi' = C₀.cell i) (hk : C₀.grade i ≤ 2 ∨ C₀.scope i ≠ Finset.univ) :
    ∃ i' : Cell C₀, emb₀ i' = Xi' ∧ C₀.cell i' = C₀.cell i := by
  rw [Family.cell_eq] at h
  rcases hw : family₂.e.symm Xi' with c | H | s | a
  · refine ⟨family₀.e (.inl c), ?_, ?_⟩
    · change family₂.e (embX₀ (family₀.e.symm (family₀.e (Sum.inl c)))) = _
      rw [Equiv.symm_apply_apply]
      change family₂.e (Sum.inl c) = _
      rw [← hw, Equiv.apply_symm_apply]
    · rw [Family.cell_e, ← h, hw]; rfl
  · refine ⟨family₀.e (.inr (.inl ⟨H.1, H.2⟩)), ?_, ?_⟩
    · change family₂.e (embX₀ (family₀.e.symm (family₀.e (Sum.inr (Sum.inl ⟨H.1, H.2⟩))))) = _
      rw [Equiv.symm_apply_apply]
      change family₂.e (Sum.inr (Sum.inl H)) = _
      rw [← hw, Equiv.apply_symm_apply]
    · rw [Family.cell_e, ← h, hw]; rfl
  · refine ⟨family₀.e (.inr (.inr (.inl ⟨s.1, s.2⟩))), ?_, ?_⟩
    · change family₂.e (embX₀ (family₀.e.symm
        (family₀.e (Sum.inr (Sum.inr (Sum.inl ⟨s.1, s.2⟩)))))) = _
      rw [Equiv.symm_apply_apply]
      change family₂.e (Sum.inr (Sum.inr (Sum.inl s))) = _
      rw [← hw, Equiv.apply_symm_apply]
    · rw [Family.cell_e, ← h, hw]; rfl
  · exfalso
    rw [hw] at h
    have hS : Finset.univ = C₀.scope i := congrArg Prod.fst h
    have hk3 : (3 : ℕ) = C₀.grade i := congrArg Prod.snd h
    rcases hk with hk | hk
    · omega
    · exact hk hS.symm

theorem exists_emb₁_of_cell (Xi' : Cell C₂) (i : Cell C₁)
    (h : C₂.cell Xi' = C₁.cell i) (hk : C₁.grade i ≤ 2 ∨ C₁.scope i ≠ Finset.univ) :
    ∃ i' : Cell C₁, emb₁ i' = Xi' ∧ C₁.cell i' = C₁.cell i := by
  rw [Family.cell_eq] at h
  rcases hw : family₂.e.symm Xi' with c | H | s | a
  · refine ⟨family₁.e (.inl c), ?_, ?_⟩
    · change family₂.e (embX₁ (family₁.e.symm (family₁.e (Sum.inl c)))) = _
      rw [Equiv.symm_apply_apply]
      change family₂.e (Sum.inl c) = _
      rw [← hw, Equiv.apply_symm_apply]
    · rw [Family.cell_e, ← h, hw]; rfl
  · refine ⟨family₁.e (.inr (.inl ⟨H.1, H.2⟩)), ?_, ?_⟩
    · change family₂.e (embX₁ (family₁.e.symm (family₁.e (Sum.inr (Sum.inl ⟨H.1, H.2⟩))))) = _
      rw [Equiv.symm_apply_apply]
      change family₂.e (Sum.inr (Sum.inl H)) = _
      rw [← hw, Equiv.apply_symm_apply]
    · rw [Family.cell_e, ← h, hw]; rfl
  · refine ⟨family₁.e (.inr (.inr (.inl ⟨s.1, s.2⟩))), ?_, ?_⟩
    · change family₂.e (embX₁ (family₁.e.symm
        (family₁.e (Sum.inr (Sum.inr (Sum.inl ⟨s.1, s.2⟩)))))) = _
      rw [Equiv.symm_apply_apply]
      change family₂.e (Sum.inr (Sum.inr (Sum.inl s))) = _
      rw [← hw, Equiv.apply_symm_apply]
    · rw [Family.cell_e, ← h, hw]; rfl
  · exfalso
    rw [hw] at h
    have hS : Finset.univ = C₁.scope i := congrArg Prod.fst h
    have hk3 : (3 : ℕ) = C₁.grade i := congrArg Prod.snd h
    rcases hk with hk | hk
    · omega
    · exact hk hS.symm

/-! ### The scheme -/

/-- The faces of the fresh point other than the domain. -/
def newFacesB : Finset (Finset (Fin 4)) := {{3}, {1, 3}, {1, 2, 3}}

theorem newFacesB_subset : ∀ B ∈ newFacesB, B ∈ plan₄ := by decide
theorem last_mem_newFacesB : ∀ B ∈ newFacesB, (3 : Fin 4) ∈ B := by decide
theorem newFacesB_ne_univ : ∀ B ∈ newFacesB, B ≠ Finset.univ := by decide
theorem mem_newFacesB_of_last : ∀ B ∈ plan₄, (3 : Fin 4) ∈ B → B ≠ Finset.univ →
    B ∈ newFacesB := by decide
theorem fold_newFacesB_mem : ∀ B ∈ newFacesB, B.image fold ∈ Prop3.plan := by decide
theorem card_fold_newFacesB : ∀ B ∈ newFacesB, (B.image fold).card = B.card := by decide

/-- **Copies of input B's cells** along the fresh faces. -/
abbrev CopyB : Type := {p : ↥newFacesB × Cell C₁ // C₁.scope p.2 = (p.1.1).image fold}
/-- **The fresh full cells**: one copy of every full cell of the three-cell family. -/
abbrev Fresh : Type := {c : Cell C₂ // C₂.scope c = Finset.univ}
abbrev New₂ : Type := CopyB ⊕ Fresh ⊕ Unit

noncomputable def newCell₂ : New₂ → Finset (Fin 4) × ℕ
  | .inl p => (p.1.1.1, C₁.grade p.1.2)
  | .inr (.inl f) => (Finset.univ, C₂.grade f.1)
  | .inr (.inr _) => (Finset.univ, 4)

theorem newCell₂_mem (x : New₂) : newCell₂ x ∈ Plan.gradedPlan plan₄ := by
  rcases x with p | f | _
  · refine Plan.mem_gradedPlan.mpr ⟨newFacesB_subset _ p.1.1.2, C₁.grade_pos _, ?_⟩
    change C₁.grade p.1.2 ≤ (p.1.1.1).card
    calc C₁.grade p.1.2 ≤ (C₁.scope p.1.2).card := C₁.grade_le_card_scope _
      _ = ((p.1.1.1).image fold).card := by rw [p.2]
      _ ≤ (p.1.1.1).card := Finset.card_image_le
  · refine Plan.mem_gradedPlan.mpr ⟨isPlan₄.domain_mem, C₂.grade_pos _, ?_⟩
    change C₂.grade f.1 ≤ (Finset.univ : Finset (Fin 4)).card
    calc C₂.grade f.1 ≤ (C₂.scope f.1).card := C₂.grade_le_card_scope _
      _ = 3 := by rw [f.2]; rfl
      _ ≤ _ := by decide
  · change (Finset.univ, 4) ∈ _
    exact Plan.mem_gradedPlan.mpr ⟨by decide, by decide, by decide⟩

theorem newCell₂_last (x : New₂) : Fin.last 3 ∈ (newCell₂ x).1 := by
  rcases x with p | f | _
  · exact last_mem_newFacesB _ p.1.1.2
  · exact Finset.mem_univ _
  · exact Finset.mem_univ _

/-- **The glued four-point scheme.** -/
noncomputable abbrev D₂ : CellScheme (ι := Fin 4) Finset.univ :=
  CellScheme.extendOneWith C₀ plan₄ isPlan₄ hface₄ newCell₂ newCell₂_mem

theorem D₂_complete : D₂.IsComplete := by
  refine CellScheme.IsComplete.extendOneWith family₀.scheme_isComplete ?_
  rintro ⟨B, j⟩ hBJ hlast
  obtain ⟨hB, hj0, hjB⟩ := Plan.mem_gradedPlan.mp hBJ
  dsimp only at hB hj0 hjB hlast
  by_cases hBu : B = Finset.univ
  · subst hBu
    by_cases hj4 : j = 4
    · exact ⟨.inr (.inr ()), by rw [hj4]; rfl⟩
    · have hj3 : j ≤ 3 := by
        rw [Finset.card_univ, Fintype.card_fin] at hjB; omega
      obtain ⟨x, hx⟩ := family₂.scheme_isComplete (Finset.univ, j)
        (Plan.mem_gradedPlan.mpr ⟨C₂.isPlan.domain_mem, hj0, by
          change j ≤ (Finset.univ : Finset (Fin 3)).card
          rw [Finset.card_univ, Fintype.card_fin]; exact hj3⟩)
      refine ⟨.inr (.inl ⟨x, congrArg Prod.fst hx⟩), ?_⟩
      change (Finset.univ, C₂.grade x) = (Finset.univ, j)
      rw [show C₂.grade x = j from congrArg Prod.snd hx]
  · have hBn : B ∈ newFacesB := mem_newFacesB_of_last B hB hlast hBu
    obtain ⟨x, hx⟩ := family₁.scheme_isComplete (B.image fold, j)
      (Plan.mem_gradedPlan.mpr ⟨fold_newFacesB_mem B hBn, hj0, by
        rw [card_fold_newFacesB B hBn]; exact hjB⟩)
    refine ⟨.inl ⟨(⟨B, hBn⟩, x), congrArg Prod.fst hx⟩, ?_⟩
    change (B, C₁.grade x) = (B, j)
    rw [show C₁.grade x = j from congrArg Prod.snd hx]

/-- The retraction on new cells; the mute cell goes anywhere. -/
noncomputable def retNew₂ : New₂ → Cell C₂
  | .inl p => emb₁ p.1.2
  | .inr (.inl f) => f.1
  | .inr (.inr _) => emb₀ a₂cell

/-- **The retraction** into the three-cell family. -/
noncomputable def ret₂ : Cell D₂ → Cell C₂ :=
  Fin.addCases emb₀ (fun j => retNew₂ ((Fintype.equivFin New₂).symm j))

theorem ret₂_castAdd (i : Cell C₀) : ret₂ (Fin.castAdd (Fintype.card New₂) i) = emb₀ i := by
  unfold ret₂; exact Fin.addCases_left i
theorem ret₂_natAdd (j : Fin (Fintype.card New₂)) :
    ret₂ (Fin.natAdd C₀.card j) = retNew₂ ((Fintype.equivFin New₂).symm j) := by
  unfold ret₂; exact Fin.addCases_right j

noncomputable def mute₂ (d : Cell D₂) : Prop := D₂.cell d = (Finset.univ, 4)
noncomputable instance : DecidablePred mute₂ := fun d => inferInstanceAs (Decidable (D₂.cell d = _))

theorem D₂_cell_castAdd (i : Cell C₀) :
    D₂.cell (Fin.castAdd (Fintype.card New₂) i) = pushGraded Fin.castSuccEmb (C₀.cell i) :=
  CellScheme.extendOneWith_cell_castAdd i
theorem D₂_cell_natAdd (j : Fin (Fintype.card New₂)) :
    D₂.cell (Fin.natAdd C₀.card j) = newCell₂ ((Fintype.equivFin New₂).symm j) :=
  CellScheme.extendOneWith_cell_natAdd j
theorem D₂_scope_castAdd (i : Cell C₀) :
    D₂.scope (Fin.castAdd (Fintype.card New₂) i) = (C₀.scope i).image Fin.castSuccEmb :=
  CellScheme.extendOneWith_scope_castAdd i
theorem D₂_grade_castAdd (i : Cell C₀) :
    D₂.grade (Fin.castAdd (Fintype.card New₂) i) = C₀.grade i :=
  CellScheme.extendOneWith_grade_castAdd i

theorem not_mute₂_natAdd_of_ne {j : Fin (Fintype.card New₂)} {x : New₂}
    (hy : (Fintype.equivFin New₂).symm j = x) (hx : ∀ u, x ≠ .inr (.inr u)) :
    ¬ mute₂ (Fin.natAdd C₀.card j) := by
  intro h
  change D₂.cell (Fin.natAdd _ j) = _ at h
  rw [D₂_cell_natAdd, hy] at h
  rcases x with p | f | u
  · exact absurd (congrArg Prod.fst h) (newFacesB_ne_univ _ p.1.1.2)
  · have := congrArg Prod.snd h
    change C₂.grade f.1 = 4 at this
    have h3 := C₂.grade_le_card_scope f.1
    rw [f.2] at h3
    change C₂.grade f.1 ≤ (Finset.univ : Finset (Fin 3)).card at h3
    rw [Finset.card_univ, Fintype.card_fin] at h3
    omega
  · exact hx u rfl

theorem mute₂_natAdd_unit {j : Fin (Fintype.card New₂)} {u : Unit}
    (hy : (Fintype.equivFin New₂).symm j = .inr (.inr u)) : mute₂ (Fin.natAdd C₀.card j) := by
  change D₂.cell (Fin.natAdd _ j) = _
  rw [D₂_cell_natAdd, hy]; rfl

/-- The scope of the retraction of a non-mute cell is the fold of its scope. -/
theorem scope_ret₂ (x : Cell D₂) (hx : ¬ mute₂ x) :
    C₂.scope (ret₂ x) = (D₂.scope x).image fold := by
  induction x using Fin.addCases with
  | left i =>
    rw [ret₂_castAdd]
    change (C₂.cell (emb₀ i)).1 = ((D₂.cell (Fin.castAdd _ i)).1).image fold
    rw [cell_emb₀, D₂_cell_castAdd]
    exact (image_fold_image_castSucc _).symm
  | right j =>
    rw [ret₂_natAdd]
    change (C₂.cell (retNew₂ _)).1 = ((D₂.cell (Fin.natAdd _ j)).1).image fold
    rw [D₂_cell_natAdd]
    rcases hy : (Fintype.equivFin New₂).symm j with p | f | u
    · change (C₂.cell (emb₁ p.1.2)).1 = _
      rw [cell_emb₁]; exact p.2
    · change C₂.scope f.1 = (Finset.univ : Finset (Fin 4)).image fold
      rw [f.2, image_fold_univ]
    · exact absurd (mute₂_natAdd_unit hy) hx

theorem grade_ret₂ (x : Cell D₂) (hx : ¬ mute₂ x) : D₂.grade x = C₂.grade (ret₂ x) := by
  induction x using Fin.addCases with
  | left i =>
    rw [ret₂_castAdd]
    change _ = (C₂.cell (emb₀ i)).2
    rw [cell_emb₀]
    exact CellScheme.extendOneWith_grade_castAdd i
  | right j =>
    rw [ret₂_natAdd]
    change (D₂.cell (Fin.natAdd _ j)).2 = _
    rw [D₂_cell_natAdd]
    rcases hy : (Fintype.equivFin New₂).symm j with p | f | u
    · change C₁.grade p.1.2 = (C₂.cell (emb₁ p.1.2)).2
      rw [cell_emb₁]; rfl
    · rfl
    · exact absurd (mute₂_natAdd_unit hy) hx

theorem hscope₂ (x y : Cell D₂) (hx : ¬ mute₂ x) (hy : ¬ mute₂ y) (h : D₂.scope x ⊆ D₂.scope y) :
    C₂.scope (ret₂ x) ⊆ C₂.scope (ret₂ y) := by
  rw [scope_ret₂ x hx, scope_ret₂ y hy]
  exact Finset.image_subset_image h

theorem hmute_below₂ (x d : Cell D₂) (hx : ¬ mute₂ x) (h : GradedLe (D₂.cell d) (D₂.cell x)) :
    ¬ mute₂ d := by
  intro hd
  apply hx
  change D₂.cell d = (Finset.univ, 4) at hd
  have hs : Finset.univ ⊆ D₂.scope x := by
    have := h.1; rw [hd] at this; exact this
  have hg : 4 ≤ D₂.grade x := by
    have := h.2; rw [hd] at this; exact this
  have hcard : D₂.grade x ≤ 4 := by
    have := D₂.grade_le_card_scope x
    have h4 : (D₂.scope x).card ≤ 4 := (Finset.card_le_univ _).trans (by simp)
    omega
  change D₂.cell x = (Finset.univ, 4)
  exact Prod.ext (Finset.univ_subset_iff.mp hs) (by change D₂.grade x = 4; omega)

/-- A cell of grade three whose scope lies in a three-element face has that face as scope. -/
theorem scope_eq_of_grade_three {x : Cell D₂} {B : Finset (Fin 4)} (hB : B.card = 3)
    (hs : D₂.scope x ⊆ B) (hg : D₂.grade x = 3) : D₂.scope x = B := by
  apply Finset.eq_of_subset_of_card_le hs
  rw [hB, ← hg]
  exact D₂.grade_le_card_scope x

/-- **Partial sections**: availability witnesses at a distinct larger index lift — at a full index
every cell of the three-cell family has a fresh copy; at a face only the input's own cells are
needed, since a cell of grade three inside a face already has the face's index. -/
theorem hsect₂ : PartialSections ret₂ mute₂ := by
  intro Sig Xi₀ Xi' hSig hXi₀ hs hg hne hcell
  induction Xi₀ using Fin.addCases with
  | left i =>
    rw [ret₂_castAdd, cell_emb₀] at hcell
    have hk : C₀.grade i ≤ 2 ∨ C₀.scope i ≠ Finset.univ := by
      by_contra hcon
      rw [not_or, not_le, not_ne_iff] at hcon
      apply hne
      have hg3 : D₂.grade Sig = 3 := by
        rw [hg, D₂_grade_castAdd]
        have h3 := C₀.grade_le_card_scope i
        rw [hcon.2] at h3
        change C₀.grade i ≤ (Finset.univ : Finset (Fin 3)).card at h3
        rw [Finset.card_univ, Fintype.card_fin] at h3
        omega
      have hsc : D₂.scope (Fin.castAdd _ i) = Finset.univ.image Fin.castSuccEmb := by
        rw [D₂_scope_castAdd, hcon.2]
      have hs' : D₂.scope Sig ⊆ Finset.univ.image Fin.castSuccEmb := by rw [← hsc]; exact hs
      have hSs : D₂.scope Sig = Finset.univ.image Fin.castSuccEmb :=
        scope_eq_of_grade_three (by decide) hs' hg3
      exact Prod.ext (hSs.trans hsc.symm) hg
    obtain ⟨i', hi', hci'⟩ := exists_emb₀_of_cell Xi' i hcell hk
    refine ⟨Fin.castAdd _ i', ?_, by rw [ret₂_castAdd, hi']⟩
    rw [D₂_cell_castAdd, D₂_cell_castAdd, hci']
  | right j =>
    rw [ret₂_natAdd] at hcell
    rcases hy : (Fintype.equivFin New₂).symm j with p | f | u
    · rw [hy] at hcell
      change C₂.cell Xi' = C₂.cell (emb₁ p.1.2) at hcell
      rw [cell_emb₁] at hcell
      have hk : C₁.grade p.1.2 ≤ 2 ∨ C₁.scope p.1.2 ≠ Finset.univ := by
        by_contra hcon
        rw [not_or, not_le, not_ne_iff] at hcon
        apply hne
        have hcellXi₀ : D₂.cell (Fin.natAdd C₀.card j) = (p.1.1.1, 3) := by
          rw [D₂_cell_natAdd, hy]
          change (p.1.1.1, C₁.grade p.1.2) = _
          have h3 := C₁.grade_le_card_scope p.1.2
          rw [hcon.2] at h3
          change C₁.grade p.1.2 ≤ (Finset.univ : Finset (Fin 3)).card at h3
          rw [Finset.card_univ, Fintype.card_fin] at h3
          rw [show C₁.grade p.1.2 = 3 by omega]
        have hcardB : (p.1.1.1).card = 3 := by
          rw [← card_fold_newFacesB _ p.1.1.2, ← p.2, hcon.2]; rfl
        have hg3 : D₂.grade Sig = 3 := by
          rw [hg]; exact congrArg Prod.snd hcellXi₀
        have hs' : D₂.scope Sig ⊆ p.1.1.1 := by
          have := hs; rw [show D₂.scope (Fin.natAdd C₀.card j) = p.1.1.1 from
            congrArg Prod.fst hcellXi₀] at this; exact this
        rw [hcellXi₀]
        exact Prod.ext (scope_eq_of_grade_three hcardB hs' hg3) hg3
      obtain ⟨i', hi', hci'⟩ := exists_emb₁_of_cell Xi' p.1.2 hcell hk
      have hs' : C₁.scope i' = (p.1.1.1).image fold := by
        rw [← p.2]; exact congrArg Prod.fst hci'
      refine ⟨Fin.natAdd C₀.card ((Fintype.equivFin New₂) (.inl ⟨(p.1.1, i'), hs'⟩)), ?_, ?_⟩
      · rw [D₂_cell_natAdd, D₂_cell_natAdd, Equiv.symm_apply_apply, hy]
        change (p.1.1.1, C₁.grade i') = (p.1.1.1, C₁.grade p.1.2)
        rw [show C₁.grade i' = C₁.grade p.1.2 from congrArg Prod.snd hci']
      · rw [ret₂_natAdd, Equiv.symm_apply_apply]; exact hi'
    · rw [hy] at hcell
      change C₂.cell Xi' = C₂.cell f.1 at hcell
      have hsu : C₂.scope Xi' = Finset.univ := (congrArg Prod.fst hcell).trans f.2
      refine ⟨Fin.natAdd C₀.card ((Fintype.equivFin New₂) (.inr (.inl ⟨Xi', hsu⟩))), ?_, ?_⟩
      · rw [D₂_cell_natAdd, D₂_cell_natAdd, Equiv.symm_apply_apply, hy]
        change (Finset.univ, C₂.grade Xi') = (Finset.univ, C₂.grade f.1)
        rw [show C₂.grade Xi' = C₂.grade f.1 from congrArg Prod.snd hcell]
      · rw [ret₂_natAdd, Equiv.symm_apply_apply]; rfl
    · exact absurd (mute₂_natAdd_unit hy) hXi₀

/-- **The rows of the glued scheme**: the three-cell family's rows pulled back. -/
noncomputable def rows₂ : Semantics D₂ :=
  family₂.rows.pullback ret₂ mute₂ grade_ret₂ hscope₂ hmute_below₂

theorem rows₂_E_of_not_mute {x : Cell D₂} (hx : ¬ mute₂ x) (d : D₂.below (D₂.cell x)) :
    rows₂.E x d =
      family₂.rows.E (ret₂ x) (retBelow ret₂ mute₂ grade_ret₂ hscope₂ hmute_below₂ hx d) :=
  Semantics.pullback_E_of_not_mute hx d

theorem rows₂_isCoded : rows₂.IsCoded := Semantics.pullback_isCoded family₂.rows_isCoded

/-- **The mixed controllers are consistent.** -/
theorem rows₂_isConsistent : rows₂.IsConsistent :=
  Semantics.pullback_isConsistent' family₂.rows_isConsistent hsect₂

end Glue

/-! ## Part B6: bountifulness inside the two faces, by transport from the inputs -/

section Faces

/-- The retraction onto input A (junk off the old cells). -/
noncomputable def retA : Cell D₂ → Cell C₀ := Fin.addCases (fun i => i) (fun _ => a₂cell)

theorem retA_castAdd (i : Cell C₀) : retA (Fin.castAdd (Fintype.card New₂) i) = i := by
  unfold retA; exact Fin.addCases_left i

theorem not_mute₂_castAdd (i : Cell C₀) : ¬ mute₂ (Fin.castAdd (Fintype.card New₂) i) := by
  intro h
  change D₂.cell _ = _ at h
  rw [D₂_cell_castAdd] at h
  have h3 : (3 : Fin 4) ∈ (C₀.scope i).image Fin.castSuccEmb := by
    rw [show (C₀.scope i).image Fin.castSuccEmb = Finset.univ from congrArg Prod.fst h]
    exact Finset.mem_univ _
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp h3
  exact (Fin.castSucc_lt_last x).ne hx

/-- Cells below an old face are old cells. -/
theorem old_of_A {B : Finset (Fin 4)} (hB : B ⊆ Finset.univ.image Fin.castSuccEmb) {j : ℕ}
    (a : D₂.below (B, j)) : ∃ i, Fin.castAdd (Fintype.card New₂) i = a.1 :=
  (CellScheme.extendOneWith_scope_subset_iff newCell₂_last a.1).mp (a.2.1.trans hB)

theorem sub_castSucc_of_not_last : ∀ B ∈ plan₄, (3 : Fin 4) ∉ B →
    B ⊆ Finset.univ.image Fin.castSuccEmb := by decide
theorem fold_inj_old : ∀ B ∈ plan₄, ∀ B' ∈ plan₄, (3 : Fin 4) ∉ B → (3 : Fin 4) ∉ B' →
    B.image fold = B'.image fold → B = B' := by decide
theorem old_ne_univ : ∀ B ∈ plan₄, (3 : Fin 4) ∉ B → B ≠ Finset.univ := by decide

/-- **Rows on old cells are input A's rows.** -/
theorem rows₂_E_castAdd (i : Cell C₀) (d : D₂.below (D₂.cell (Fin.castAdd (Fintype.card New₂) i)))
    (i' : Cell C₀) (hi' : Fin.castAdd (Fintype.card New₂) i' = d.1)
    (hd : GradedLe (C₀.cell i') (C₀.cell i)) :
    rows₂.E (Fin.castAdd (Fintype.card New₂) i) d = family₀.rows.E i ⟨i', hd⟩ := by
  rw [rows₂_E_of_not_mute (not_mute₂_castAdd i)]
  change family₂.rowX (family₂.e.symm (ret₂ (Fin.castAdd _ i))) (family₂.e.symm (ret₂ d.1)) =
    family₀.rowX (family₀.e.symm i) (family₀.e.symm i')
  rw [← hi', ret₂_castAdd, ret₂_castAdd]
  change family₂.rowX (family₂.e.symm (family₂.e _)) (family₂.e.symm (family₂.e _)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, rowX_embX₀]

theorem retA_mem_below {B : Finset (Fin 4)} (hB : B ⊆ Finset.univ.image Fin.castSuccEmb) {j : ℕ}
    (a : D₂.below (B, j)) : GradedLe (C₀.cell (retA a.1)) (B.image fold, j) := by
  obtain ⟨i, hi⟩ := old_of_A hB a
  have ha := a.2
  rw [← hi, D₂_cell_castAdd] at ha
  rw [← hi, retA_castAdd]
  refine ⟨?_, ha.2⟩
  change C₀.scope i ⊆ _
  rw [← image_fold_image_castSucc (C₀.scope i)]
  exact Finset.image_subset_image ha.1

/-- **The old-face bijection** onto input A's lower sets. -/
noncomputable def eA {B : Finset (Fin 4)} (hBp : B ∈ plan₄) (h3 : (3 : Fin 4) ∉ B) (j : ℕ) :
    D₂.below (B, j) ≃ C₀.below (B.image fold, j) :=
  Equiv.ofBijective (fun a => ⟨retA a.1, retA_mem_below (sub_castSucc_of_not_last B hBp h3) a⟩)
    ⟨by
      intro a b hab
      have hB := sub_castSucc_of_not_last B hBp h3
      obtain ⟨i, hi⟩ := old_of_A hB a
      obtain ⟨i', hi'⟩ := old_of_A hB b
      have : retA a.1 = retA b.1 := congrArg Subtype.val hab
      rw [← hi, ← hi', retA_castAdd, retA_castAdd] at this
      apply Subtype.ext
      rw [← hi, ← hi', this],
     by
      intro y
      refine ⟨⟨Fin.castAdd (Fintype.card New₂) y.1, ?_⟩, ?_⟩
      · rw [D₂_cell_castAdd]
        refine ⟨?_, y.2.2⟩
        change (C₀.scope y.1).image Fin.castSuccEmb ⊆ B
        exact castSucc_sub_old B hBp h3 _ y.2.1
      · apply Subtype.ext
        change retA (Fin.castAdd _ y.1) = y.1
        exact retA_castAdd y.1⟩

theorem eA_val {B : Finset (Fin 4)} (hBp : B ∈ plan₄) (h3 : (3 : Fin 4) ∉ B) (j : ℕ)
    (a : D₂.below (B, j)) : (eA hBp h3 j a).1 = retA a.1 := rfl

theorem eA_grade {B : Finset (Fin 4)} (hBp : B ∈ plan₄) (h3 : (3 : Fin 4) ∉ B) (j : ℕ)
    (a : D₂.below (B, j)) : D₂.grade a.1 = C₀.grade (eA hBp h3 j a).1 := by
  obtain ⟨i, hi⟩ := old_of_A (sub_castSucc_of_not_last B hBp h3) a
  rw [eA_val, ← hi, retA_castAdd, D₂_grade_castAdd]

theorem eA_scope {B : Finset (Fin 4)} (hBp : B ∈ plan₄) (h3 : (3 : Fin 4) ∉ B) (j : ℕ)
    (a b : D₂.below (B, j)) :
    D₂.scope a.1 ⊆ D₂.scope b.1 ↔ C₀.scope (eA hBp h3 j a).1 ⊆ C₀.scope (eA hBp h3 j b).1 := by
  obtain ⟨i, hi⟩ := old_of_A (sub_castSucc_of_not_last B hBp h3) a
  obtain ⟨i', hi'⟩ := old_of_A (sub_castSucc_of_not_last B hBp h3) b
  rw [eA_val, eA_val, ← hi, ← hi', retA_castAdd, retA_castAdd, D₂_scope_castAdd, D₂_scope_castAdd]
  exact Finset.image_subset_image_iff Fin.castSuccEmb.injective

theorem eA_rows {B : Finset (Fin 4)} (hBp : B ∈ plan₄) (h3 : (3 : Fin 4) ∉ B) (j : ℕ)
    (Sig : D₂.below (B, j)) (d : D₂.below (D₂.cell Sig.1))
    (hd : GradedLe (C₀.cell (eA hBp h3 j ⟨d.1, d.2.trans Sig.2⟩).1)
      (C₀.cell (eA hBp h3 j Sig).1)) :
    rows₂.E Sig.1 d = family₀.rows.E (eA hBp h3 j Sig).1
      ⟨(eA hBp h3 j ⟨d.1, d.2.trans Sig.2⟩).1, hd⟩ := by
  obtain ⟨i, hi⟩ := old_of_A (sub_castSucc_of_not_last B hBp h3) Sig
  obtain ⟨i', hi'⟩ := old_of_A (sub_castSucc_of_not_last B hBp h3) ⟨d.1, d.2.trans Sig.2⟩
  have e1 : (eA hBp h3 j Sig).1 = i := by
    change retA Sig.1 = i; rw [← hi, retA_castAdd]
  have e2 : (eA hBp h3 j ⟨d.1, d.2.trans Sig.2⟩).1 = i' := by
    change retA d.1 = i'; rw [← hi', retA_castAdd]
  have hd' : GradedLe (C₀.cell i') (C₀.cell i) := by rw [← e1, ← e2]; exact hd
  have hSig : Sig.1 = Fin.castAdd (Fintype.card New₂) i := hi.symm
  have key := rows₂_E_castAdd i ⟨d.1, by rw [← hSig]; exact d.2⟩ i' hi' hd'
  refine (rows₂.E_congr' hSig rfl).trans (key.trans ?_)
  exact family₀.rows.E_congr' e1.symm e2.symm

theorem respects_iff_A {B : Finset (Fin 4)} (hBp : B ∈ plan₄) (h3 : (3 : Fin 4) ∉ B) (j : ℕ)
    (q : D₂.below (B, j) → ExtOrd) :
    RespectsSemanticsBelow rows₂ (B, j) q ↔
      RespectsSemanticsBelow family₀.rows (B.image fold, j) (q ∘ (eA hBp h3 j).symm) :=
  respects_iff_of_equiv (eA hBp h3 j) (eA_grade hBp h3 j) (eA_scope hBp h3 j) (eA_rows hBp h3 j) q

/-- **Bountifulness inside the old face**: transported from input A. -/
theorem bountiful₂_A (CI BJ : Finset (Fin 4) × ℕ) (hCI : CI ∈ Plan.gradedPlan plan₄)
    (hBJ : BJ ∈ Plan.gradedPlan plan₄) (h : GradedLe CI BJ) (h3 : (3 : Fin 4) ∉ BJ.1)
    (p : D₂.below CI → ExtOrd) (q : D₂.below BJ → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow rows₂ CI p) (hq : RespectsSemanticsBelow rows₂ BJ q)
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ)
    (hagree : ∀ d : D₂.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D₂.below BJ → ExtOrd, RespectsSemanticsBelow rows₂ BJ q' ∧
      (∀ d : D₂.below BJ, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D₂.below CI, q' (CellScheme.below.mono h d) = p d) := by
  obtain ⟨C, i⟩ := CI
  obtain ⟨B, j⟩ := BJ
  dsimp only at h3 hγ
  have hBp : B ∈ plan₄ := (Plan.mem_gradedPlan.mp hBJ).1
  have hCp : C ∈ plan₄ := (Plan.mem_gradedPlan.mp hCI).1
  have hC3 : (3 : Fin 4) ∉ C := fun hx => h3 (h.1 hx)
  by_cases hne : (C, i) = (B, j)
  · obtain ⟨hCB, hij⟩ := Prod.mk.inj hne
    subst hCB; subst hij
    refine ⟨p, hp, fun d => ?_, fun d => ?_⟩
    · have := hagree d
      rw [show CellScheme.below.mono h d = d from Subtype.ext rfl] at this
      exact this.symm
    · rw [show CellScheme.below.mono h d = d from Subtype.ext rfl]
  have hfoldC : (C.image fold, i) ∈ Plan.gradedPlan Prop3.plan := by
    obtain ⟨-, hi0, hiC⟩ := Plan.mem_gradedPlan.mp hCI
    exact Plan.mem_gradedPlan.mpr ⟨fold_mem_plan C hCp (old_ne_univ C hCp hC3), hi0, by
      change i ≤ (C.image fold).card; rw [card_fold_proper C hCp (old_ne_univ C hCp hC3)]
      exact hiC⟩
  have hfoldB : (B.image fold, j) ∈ Plan.gradedPlan Prop3.plan := by
    obtain ⟨-, hj0, hjB⟩ := Plan.mem_gradedPlan.mp hBJ
    exact Plan.mem_gradedPlan.mpr ⟨fold_mem_plan B hBp (old_ne_univ B hBp h3), hj0, by
      change j ≤ (B.image fold).card; rw [card_fold_proper B hBp (old_ne_univ B hBp h3)]
      exact hjB⟩
  have h' : GradedLe (C.image fold, i) (B.image fold, j) := ⟨Finset.image_subset_image h.1, h.2⟩
  have hne' : (C.image fold, i) ≠ (B.image fold, j) := by
    intro he
    apply hne
    have hc := fold_inj_old C hCp B hBp hC3 h3 (congrArg Prod.fst he)
    rw [hc, show i = j from congrArg Prod.snd he]
  exact bountiful_of_equiv h h' (eA hBp h3 j) (eA hCp hC3 i) (fun d => Subtype.ext rfl)
    (respects_iff_A hBp h3 j) (respects_iff_A hCp hC3 i)
    (semScheme₀.bountiful _ _ hfoldC hfoldB h' hne') rfl p q γ hp hq hγ hagree

end Faces


theorem Prop3.scope_mem : ∀ c : Prop3, c.scope ∈ Prop3.plan := by decide

section FacesB

/-- The identification of input A's proper cells with input B's (junk on full cells). -/
noncomputable def embX₀₁ : family₀.X → family₁.X
  | .inl c => .inl c
  | .inr (.inl H) => .inr (.inl ⟨H.1, H.2⟩)
  | .inr (.inr (.inl s)) => .inr (.inr (.inl ⟨s.1, s.2⟩))
  | .inr (.inr (.inr _)) => .inr (.inr (.inr ⟨b₁, Finset.mem_singleton_self _⟩))

noncomputable def toC₁ (i : Cell C₀) : Cell C₁ := family₁.e (embX₀₁ (family₀.e.symm i))

noncomputable def retNewB : New₂ → Cell C₁
  | .inl p => p.1.2
  | .inr _ => family₁.e (.inl .s0)

/-- **The retraction onto input B**: shared proper cells to themselves, copies to their
originals. -/
noncomputable def retB : Cell D₂ → Cell C₁ :=
  Fin.addCases toC₁ (fun j => retNewB ((Fintype.equivFin New₂).symm j))

theorem retB_castAdd (i : Cell C₀) : retB (Fin.castAdd (Fintype.card New₂) i) = toC₁ i := by
  unfold retB; exact Fin.addCases_left i
theorem retB_natAdd (j : Fin (Fintype.card New₂)) :
    retB (Fin.natAdd C₀.card j) = retNewB ((Fintype.equivFin New₂).symm j) := by
  unfold retB; exact Fin.addCases_right j

theorem exists_inl_of_scope (i : Cell C₀) (h : C₀.scope i ≠ Finset.univ) :
    ∃ c, family₀.e.symm i = .inl c := by
  have hs : C₀.scope i = (family₀.cellX (family₀.e.symm i)).1 :=
    congrArg Prod.fst (Family.cell_eq family₀ i)
  rcases hw : family₀.e.symm i with c | H | s | a
  · exact ⟨c, rfl⟩
  all_goals exact absurd (by rw [hs, hw]; rfl) h

theorem emb₁_toC₁ (i : Cell C₀) (h : C₀.scope i ≠ Finset.univ) : emb₁ (toC₁ i) = emb₀ i := by
  obtain ⟨c, hc⟩ := exists_inl_of_scope i h
  change family₂.e (embX₁ (family₁.e.symm (family₁.e (embX₀₁ (family₀.e.symm i))))) =
    family₂.e (embX₀ (family₀.e.symm i))
  rw [Equiv.symm_apply_apply, hc]; rfl

/-- The B-side faces: the faces avoiding the point `0`. -/
theorem B_ne_univ : ∀ B ∈ plan₄, (0 : Fin 4) ∉ B → B ≠ Finset.univ := by decide
theorem fold_inj_B : ∀ B ∈ plan₄, ∀ B' ∈ plan₄, (0 : Fin 4) ∉ B → (0 : Fin 4) ∉ B' →
    B.image fold = B'.image fold → B = B' := by decide
theorem fold_univ_of_B : ∀ B ∈ plan₄, (0 : Fin 4) ∉ B → B.image fold = Finset.univ →
    B = {1, 2, 3} := by decide
theorem three_mem_of_zero_mem_fold : ∀ B ∈ plan₄, (0 : Fin 4) ∉ B →
    (0 : Fin 3) ∈ B.image fold → (3 : Fin 4) ∈ B := by decide
theorem castSucc_sub_B : ∀ B ∈ plan₄, (0 : Fin 4) ∉ B →
    ∀ S : Finset (Fin 3), S ⊆ B.image fold → (0 : Fin 3) ∉ S → S.image Fin.castSuccEmb ⊆ B := by
  decide
theorem unfold_spec_B : ∀ B ∈ plan₄, (0 : Fin 4) ∉ B →
    ∀ S ∈ Prop3.plan, S ⊆ B.image fold → (0 : Fin 3) ∈ S →
      unfold S ∈ newFacesB ∧ unfold S ⊆ B ∧ (unfold S).image fold = S := by decide
theorem one_two_three_mem_newFacesB : ({1, 2, 3} : Finset (Fin 4)) ∈ newFacesB := by decide
theorem image_fold_one_two_three : ({1, 2, 3} : Finset (Fin 4)).image fold = Finset.univ := by
  decide
theorem zero_not_mem_of_castSucc_sub {S : Finset (Fin 3)} {B : Finset (Fin 4)}
    (hB0 : (0 : Fin 4) ∉ B) (h : S.image Fin.castSuccEmb ⊆ B) : (0 : Fin 3) ∉ S := fun h0 =>
  hB0 (h (Finset.mem_image_of_mem _ h0))

/-- On the B side the retraction into the three-cell family factors through input B. -/
theorem ret₂_eq_emb₁_retB {B : Finset (Fin 4)} (hB0 : (0 : Fin 4) ∉ B) {j : ℕ}
    (a : D₂.below (B, j)) : ret₂ a.1 = emb₁ (retB a.1) := by
  obtain ⟨x, hx⟩ := a
  induction x using Fin.addCases with
  | left i =>
    rw [ret₂_castAdd, retB_castAdd, emb₁_toC₁]
    intro hu
    have hs : D₂.scope (Fin.castAdd _ i) ⊆ B := hx.1
    rw [D₂_scope_castAdd, hu] at hs
    exact hB0 (hs (Finset.mem_image_of_mem _ (Finset.mem_univ (0 : Fin 3))))
  | right j' =>
    rw [ret₂_natAdd, retB_natAdd]
    rcases hy : (Fintype.equivFin New₂).symm j' with p | f | u
    · rfl
    · exfalso
      have hs : D₂.scope (Fin.natAdd _ j') ⊆ B := hx.1
      rw [show D₂.scope (Fin.natAdd C₀.card j') = Finset.univ from by
        change (D₂.cell _).1 = _; rw [D₂_cell_natAdd, hy]; rfl] at hs
      exact hB0 (hs (Finset.mem_univ _))
    · exfalso
      have hs : D₂.scope (Fin.natAdd _ j') ⊆ B := hx.1
      rw [show D₂.scope (Fin.natAdd C₀.card j') = Finset.univ from by
        change (D₂.cell _).1 = _; rw [D₂_cell_natAdd, hy]; rfl] at hs
      exact hB0 (hs (Finset.mem_univ _))

theorem not_mute₂_of_B {B : Finset (Fin 4)} (hB0 : (0 : Fin 4) ∉ B) {j : ℕ}
    (a : D₂.below (B, j)) : ¬ mute₂ a.1 := by
  intro h
  change D₂.cell a.1 = (Finset.univ, 4) at h
  have := a.2.1
  rw [h] at this
  exact hB0 (this (Finset.mem_univ _))

theorem cell_retB {B : Finset (Fin 4)} (hB0 : (0 : Fin 4) ∉ B) {j : ℕ} (a : D₂.below (B, j)) :
    C₁.cell (retB a.1) = ((D₂.scope a.1).image fold, D₂.grade a.1) := by
  rw [← cell_emb₁, ← ret₂_eq_emb₁_retB hB0 a]
  exact Prod.ext (scope_ret₂ a.1 (not_mute₂_of_B hB0 a))
    (grade_ret₂ a.1 (not_mute₂_of_B hB0 a)).symm

theorem retB_mem_below {B : Finset (Fin 4)} (hB0 : (0 : Fin 4) ∉ B) {j : ℕ}
    (a : D₂.below (B, j)) : GradedLe (C₁.cell (retB a.1)) (B.image fold, j) := by
  rw [cell_retB hB0 a]
  exact ⟨Finset.image_subset_image a.2.1, a.2.2⟩

/-- **Rows on B-side cells are input B's rows.** -/
theorem rows₂_E_emb₁ {x : Cell D₂} (hx : ¬ mute₂ x) (d : D₂.below (D₂.cell x)) (a b : Cell C₁)
    (ha : ret₂ x = emb₁ a) (hb : ret₂ d.1 = emb₁ b) (hab : GradedLe (C₁.cell b) (C₁.cell a)) :
    rows₂.E x d = family₁.rows.E a ⟨b, hab⟩ := by
  rw [rows₂_E_of_not_mute hx]
  change family₂.rowX (family₂.e.symm (ret₂ x)) (family₂.e.symm (ret₂ d.1)) =
    family₁.rowX (family₁.e.symm a) (family₁.e.symm b)
  rw [ha, hb]
  change family₂.rowX (family₂.e.symm (family₂.e _)) (family₂.e.symm (family₂.e _)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, rowX_embX₁]

/-- The retraction is injective on B-side lower sets. -/
theorem retB_inj {B : Finset (Fin 4)} (hB0 : (0 : Fin 4) ∉ B) {j : ℕ}
    (a b : D₂.below (B, j)) (h : retB a.1 = retB b.1) : a = b := by
  have h2 : ret₂ a.1 = ret₂ b.1 := by
    rw [ret₂_eq_emb₁_retB hB0 a, ret₂_eq_emb₁_retB hB0 b, h]
  apply Subtype.ext
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  change ret₂ a = ret₂ b at h2
  change a = b
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left i' =>
      rw [ret₂_castAdd, ret₂_castAdd] at h2
      rw [emb₀_injective h2]
    | right j' =>
      exfalso
      rw [ret₂_castAdd, ret₂_natAdd] at h2
      rcases hy : (Fintype.equivFin New₂).symm j' with p | f | u
      · rw [hy] at h2
        change emb₀ i = emb₁ p.1.2 at h2
        have hc : C₂.cell (emb₀ i) = C₂.cell (emb₁ p.1.2) := by rw [h2]
        rw [cell_emb₀, cell_emb₁] at hc
        have h0 : (0 : Fin 3) ∈ C₀.scope i := by
          change (0 : Fin 3) ∈ (C₀.cell i).1
          rw [hc]
          change (0 : Fin 3) ∈ C₁.scope p.1.2
          rw [p.2]
          exact Finset.mem_image_of_mem fold (last_mem_newFacesB _ p.1.1.2)
        have hsub : D₂.scope (Fin.castAdd _ i) ⊆ B := ha.1
        rw [D₂_scope_castAdd] at hsub
        exact hB0 (hsub (Finset.mem_image_of_mem _ h0))
      · have hs : D₂.scope (Fin.natAdd _ j') ⊆ B := hb.1
        rw [show D₂.scope (Fin.natAdd C₀.card j') = Finset.univ from by
          change (D₂.cell _).1 = _; rw [D₂_cell_natAdd, hy]; rfl] at hs
        exact hB0 (hs (Finset.mem_univ _))
      · exact absurd (mute₂_natAdd_unit hy) (not_mute₂_of_B hB0 ⟨_, hb⟩)
  | right j' =>
    induction b using Fin.addCases with
    | left i' =>
      exfalso
      rw [ret₂_natAdd, ret₂_castAdd] at h2
      rcases hy : (Fintype.equivFin New₂).symm j' with p | f | u
      · rw [hy] at h2
        change emb₁ p.1.2 = emb₀ i' at h2
        have hc : C₂.cell (emb₀ i') = C₂.cell (emb₁ p.1.2) := by rw [h2]
        rw [cell_emb₀, cell_emb₁] at hc
        have h0 : (0 : Fin 3) ∈ C₀.scope i' := by
          change (0 : Fin 3) ∈ (C₀.cell i').1
          rw [hc]
          change (0 : Fin 3) ∈ C₁.scope p.1.2
          rw [p.2]
          exact Finset.mem_image_of_mem fold (last_mem_newFacesB _ p.1.1.2)
        have hsub : D₂.scope (Fin.castAdd _ i') ⊆ B := hb.1
        rw [D₂_scope_castAdd] at hsub
        exact hB0 (hsub (Finset.mem_image_of_mem _ h0))
      · have hs : D₂.scope (Fin.natAdd _ j') ⊆ B := ha.1
        rw [show D₂.scope (Fin.natAdd C₀.card j') = Finset.univ from by
          change (D₂.cell _).1 = _; rw [D₂_cell_natAdd, hy]; rfl] at hs
        exact hB0 (hs (Finset.mem_univ _))
      · exact absurd (mute₂_natAdd_unit hy) (not_mute₂_of_B hB0 ⟨_, ha⟩)
    | right j'' =>
      rw [ret₂_natAdd, ret₂_natAdd] at h2
      rcases hy : (Fintype.equivFin New₂).symm j' with p | f | u
      · rcases hy' : (Fintype.equivFin New₂).symm j'' with p' | f' | u'
        · rw [hy, hy'] at h2
          change emb₁ p.1.2 = emb₁ p'.1.2 at h2
          have hpp2 := emb₁_injective h2
          have hf : p.1.1.1.image fold = p'.1.1.1.image fold := by rw [← p.2, ← p'.2, hpp2]
          have hfaces : p.1.1.1 = p'.1.1.1 :=
            fold_inj_B _ (newFacesB_subset _ p.1.1.2) _ (newFacesB_subset _ p'.1.1.2)
              (fun h0 => hB0 (ha.1 (by
                change (0 : Fin 4) ∈ D₂.scope (Fin.natAdd C₀.card j')
                rw [show D₂.scope (Fin.natAdd C₀.card j') = p.1.1.1 from by
                  change (D₂.cell _).1 = _; rw [D₂_cell_natAdd, hy]; rfl]
                exact h0)))
              (fun h0 => hB0 (hb.1 (by
                change (0 : Fin 4) ∈ D₂.scope (Fin.natAdd C₀.card j'')
                rw [show D₂.scope (Fin.natAdd C₀.card j'') = p'.1.1.1 from by
                  change (D₂.cell _).1 = _; rw [D₂_cell_natAdd, hy']; rfl]
                exact h0))) hf
          have hpp : p = p' := Subtype.ext (Prod.ext (Subtype.ext hfaces) hpp2)
          have : j' = j'' := by
            apply (Fintype.equivFin New₂).symm.injective
            rw [hy, hy', hpp]
          rw [this]
        · exfalso
          have hs : D₂.scope (Fin.natAdd _ j'') ⊆ B := hb.1
          rw [show D₂.scope (Fin.natAdd C₀.card j'') = Finset.univ from by
            change (D₂.cell _).1 = _; rw [D₂_cell_natAdd, hy']; rfl] at hs
          exact hB0 (hs (Finset.mem_univ _))
        · exact absurd (mute₂_natAdd_unit hy') (not_mute₂_of_B hB0 ⟨_, hb⟩)
      · exfalso
        have hs : D₂.scope (Fin.natAdd _ j') ⊆ B := ha.1
        rw [show D₂.scope (Fin.natAdd C₀.card j') = Finset.univ from by
          change (D₂.cell _).1 = _; rw [D₂_cell_natAdd, hy]; rfl] at hs
        exact hB0 (hs (Finset.mem_univ _))
      · exact absurd (mute₂_natAdd_unit hy) (not_mute₂_of_B hB0 ⟨_, ha⟩)

/-- The retraction is surjective from B-side lower sets onto input B's. -/
theorem retB_surj {B : Finset (Fin 4)} (hBp : B ∈ plan₄) (hB0 : (0 : Fin 4) ∉ B) {j : ℕ}
    (y : C₁.below (B.image fold, j)) : ∃ a : D₂.below (B, j), retB a.1 = y.1 := by
  have hy2 := y.2
  rw [Family.cell_eq] at hy2
  rcases hw : family₁.e.symm y.1 with c | H | s | a
  · rw [hw] at hy2
    have hsc : c.scope ⊆ B.image fold := hy2.1
    have hgc : c.gradeP ≤ j := hy2.2
    by_cases h0 : (0 : Fin 3) ∈ c.scope
    · obtain ⟨hnf, hsub, hfold⟩ := unfold_spec_B B hBp hB0 c.scope (Prop3.scope_mem c) hsc h0
      let p : CopyB := ⟨(⟨unfold c.scope, hnf⟩, y.1), by
        change (C₁.cell y.1).1 = _
        rw [Family.cell_eq, hw, hfold]; rfl⟩
      refine ⟨⟨Fin.natAdd C₀.card ((Fintype.equivFin New₂) (.inl p)), ?_⟩, ?_⟩
      · rw [D₂_cell_natAdd, Equiv.symm_apply_apply]
        exact ⟨hsub, by
          change (C₁.cell y.1).2 ≤ j
          rw [Family.cell_eq, hw]; exact hgc⟩
      · rw [retB_natAdd, Equiv.symm_apply_apply]; rfl
    · refine ⟨⟨Fin.castAdd (Fintype.card New₂) (family₀.e (.inl c)), ?_⟩, ?_⟩
      · rw [D₂_cell_castAdd, Family.cell_e]
        exact ⟨castSucc_sub_B B hBp hB0 c.scope hsc h0, hgc⟩
      · rw [retB_castAdd]
        change family₁.e (embX₀₁ (family₀.e.symm (family₀.e _))) = y.1
        rw [Equiv.symm_apply_apply, ← Equiv.apply_symm_apply family₁.e y.1, hw]; rfl
  all_goals
    rw [hw] at hy2
    have hu : B.image fold = Finset.univ := Finset.univ_subset_iff.mp hy2.1
    have hB : B = {1, 2, 3} := fold_univ_of_B B hBp hB0 hu
    let p : CopyB := ⟨(⟨{1, 2, 3}, one_two_three_mem_newFacesB⟩, y.1), by
      change (C₁.cell y.1).1 = _
      rw [Family.cell_eq, hw, image_fold_one_two_three]; rfl⟩
    refine ⟨⟨Fin.natAdd C₀.card ((Fintype.equivFin New₂) (.inl p)), ?_⟩, ?_⟩
    · rw [D₂_cell_natAdd, Equiv.symm_apply_apply]
      exact ⟨by rw [hB]; exact Finset.Subset.refl _, by
        change (C₁.cell y.1).2 ≤ j
        rw [Family.cell_eq, hw]; exact hy2.2⟩
    · rw [retB_natAdd, Equiv.symm_apply_apply]; rfl

/-- **The B-side bijection** onto input B's lower sets. -/
noncomputable def eB {B : Finset (Fin 4)} (hBp : B ∈ plan₄) (hB0 : (0 : Fin 4) ∉ B) (j : ℕ) :
    D₂.below (B, j) ≃ C₁.below (B.image fold, j) :=
  Equiv.ofBijective (fun a => ⟨retB a.1, retB_mem_below hB0 a⟩)
    ⟨fun a b hab => retB_inj hB0 a b (congrArg Subtype.val hab),
     fun y => by obtain ⟨a, ha⟩ := retB_surj hBp hB0 y; exact ⟨a, Subtype.ext ha⟩⟩

theorem eB_val {B : Finset (Fin 4)} (hBp : B ∈ plan₄) (hB0 : (0 : Fin 4) ∉ B) (j : ℕ)
    (a : D₂.below (B, j)) : (eB hBp hB0 j a).1 = retB a.1 := rfl

theorem eB_grade {B : Finset (Fin 4)} (hBp : B ∈ plan₄) (hB0 : (0 : Fin 4) ∉ B) (j : ℕ)
    (a : D₂.below (B, j)) : D₂.grade a.1 = C₁.grade (eB hBp hB0 j a).1 := by
  rw [eB_val]
  change _ = (C₁.cell (retB a.1)).2
  rw [cell_retB hB0 a]

theorem eB_scope {B : Finset (Fin 4)} (hBp : B ∈ plan₄) (hB0 : (0 : Fin 4) ∉ B) (j : ℕ)
    (a b : D₂.below (B, j)) :
    D₂.scope a.1 ⊆ D₂.scope b.1 ↔ C₁.scope (eB hBp hB0 j a).1 ⊆ C₁.scope (eB hBp hB0 j b).1 := by
  rw [eB_val, eB_val]
  change _ ↔ (C₁.cell (retB a.1)).1 ⊆ (C₁.cell (retB b.1)).1
  rw [cell_retB hB0 a, cell_retB hB0 b]
  constructor
  · exact Finset.image_subset_image
  · intro hs x hx
    have hx' : fold x ∈ (D₂.scope b.1).image fold :=
      hs (Finset.mem_image_of_mem fold hx)
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx'
    have := fold_injOn B hBp (B_ne_univ B hBp hB0) y (b.2.1 hy) x (a.2.1 hx) hxy
    rw [← this]; exact hy

theorem eB_rows {B : Finset (Fin 4)} (hBp : B ∈ plan₄) (hB0 : (0 : Fin 4) ∉ B) (j : ℕ)
    (Sig : D₂.below (B, j)) (d : D₂.below (D₂.cell Sig.1))
    (hd : GradedLe (C₁.cell (eB hBp hB0 j ⟨d.1, d.2.trans Sig.2⟩).1)
      (C₁.cell (eB hBp hB0 j Sig).1)) :
    rows₂.E Sig.1 d = family₁.rows.E (eB hBp hB0 j Sig).1
      ⟨(eB hBp hB0 j ⟨d.1, d.2.trans Sig.2⟩).1, hd⟩ :=
  rows₂_E_emb₁ (not_mute₂_of_B hB0 Sig) d _ _ (ret₂_eq_emb₁_retB hB0 Sig)
    (ret₂_eq_emb₁_retB hB0 ⟨d.1, d.2.trans Sig.2⟩) hd

theorem respects_iff_B {B : Finset (Fin 4)} (hBp : B ∈ plan₄) (hB0 : (0 : Fin 4) ∉ B) (j : ℕ)
    (q : D₂.below (B, j) → ExtOrd) :
    RespectsSemanticsBelow rows₂ (B, j) q ↔
      RespectsSemanticsBelow family₁.rows (B.image fold, j) (q ∘ (eB hBp hB0 j).symm) :=
  respects_iff_of_equiv (eB hBp hB0 j) (eB_grade hBp hB0 j) (eB_scope hBp hB0 j)
    (eB_rows hBp hB0 j) q

/-- **Bountifulness inside the fresh face**: transported from input B. -/
theorem bountiful₂_B (CI BJ : Finset (Fin 4) × ℕ) (hCI : CI ∈ Plan.gradedPlan plan₄)
    (hBJ : BJ ∈ Plan.gradedPlan plan₄) (h : GradedLe CI BJ) (hB0 : (0 : Fin 4) ∉ BJ.1)
    (p : D₂.below CI → ExtOrd) (q : D₂.below BJ → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow rows₂ CI p) (hq : RespectsSemanticsBelow rows₂ BJ q)
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ)
    (hagree : ∀ d : D₂.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D₂.below BJ → ExtOrd, RespectsSemanticsBelow rows₂ BJ q' ∧
      (∀ d : D₂.below BJ, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D₂.below CI, q' (CellScheme.below.mono h d) = p d) := by
  obtain ⟨C, i⟩ := CI
  obtain ⟨B, j⟩ := BJ
  dsimp only at hB0 hγ
  have hBp : B ∈ plan₄ := (Plan.mem_gradedPlan.mp hBJ).1
  have hCp : C ∈ plan₄ := (Plan.mem_gradedPlan.mp hCI).1
  have hC0 : (0 : Fin 4) ∉ C := fun hx => hB0 (h.1 hx)
  by_cases hne : (C, i) = (B, j)
  · obtain ⟨hCB, hij⟩ := Prod.mk.inj hne
    subst hCB; subst hij
    refine ⟨p, hp, fun d => ?_, fun d => ?_⟩
    · have := hagree d
      rw [show CellScheme.below.mono h d = d from Subtype.ext rfl] at this
      exact this.symm
    · rw [show CellScheme.below.mono h d = d from Subtype.ext rfl]
  have hfoldC : (C.image fold, i) ∈ Plan.gradedPlan Prop3.plan := by
    obtain ⟨-, hi0, hiC⟩ := Plan.mem_gradedPlan.mp hCI
    exact Plan.mem_gradedPlan.mpr ⟨fold_mem_plan C hCp (B_ne_univ C hCp hC0), hi0, by
      change i ≤ (C.image fold).card; rw [card_fold_proper C hCp (B_ne_univ C hCp hC0)]
      exact hiC⟩
  have hfoldB : (B.image fold, j) ∈ Plan.gradedPlan Prop3.plan := by
    obtain ⟨-, hj0, hjB⟩ := Plan.mem_gradedPlan.mp hBJ
    exact Plan.mem_gradedPlan.mpr ⟨fold_mem_plan B hBp (B_ne_univ B hBp hB0), hj0, by
      change j ≤ (B.image fold).card; rw [card_fold_proper B hBp (B_ne_univ B hBp hB0)]
      exact hjB⟩
  have h' : GradedLe (C.image fold, i) (B.image fold, j) := ⟨Finset.image_subset_image h.1, h.2⟩
  have hne' : (C.image fold, i) ≠ (B.image fold, j) := by
    intro he
    apply hne
    have hc := fold_inj_B C hCp B hBp hC0 hB0 (congrArg Prod.fst he)
    rw [hc, show i = j from congrArg Prod.snd he]
  exact bountiful_of_equiv h h' (eB hBp hB0 j) (eB hCp hC0 i) (fun d => Subtype.ext rfl)
    (respects_iff_B hBp hB0 j) (respects_iff_B hCp hC0 i)
    (semScheme₁.bountiful _ _ hfoldC hfoldB h' hne') rfl p q γ hp hq hγ hagree

end FacesB

/-! ## Part B7: the scope-changing pairs — rigidity, descent, and the extension principle -/

section ScopeChange

theorem not_mute₂_of_low {j : ℕ} (hj : j ≤ 3) (a : D₂.below (Finset.univ, j)) : ¬ mute₂ a.1 := by
  intro h
  change D₂.cell a.1 = (Finset.univ, 4) at h
  have := a.2.2
  rw [h] at this
  change 4 ≤ j at this
  omega

theorem not_mute₂_of_proper {C : Finset (Fin 4)} {i : ℕ} (hC : C ≠ Finset.univ)
    (a : D₂.below (C, i)) : ¬ mute₂ a.1 := by
  intro h
  change D₂.cell a.1 = (Finset.univ, 4) at h
  have := a.2.1
  rw [h] at this
  exact hC (Finset.univ_subset_iff.mp this)

/-- **Rigidity — uniqueness of extension over a fixed labelling of the three-cell family**: a
respecting labelling of a full-scope lower set of grade at most three is constant on the fibres
of the retraction (the controller-probe lemma: every controller reads the pulled-back row). -/
theorem rigidity₂ {j : ℕ} (hj : j ≤ 3) {q : D₂.below (Finset.univ, j) → ExtOrd}
    (hq : RespectsSemanticsBelow rows₂ (Finset.univ, j) q) (x y : D₂.below (Finset.univ, j))
    (hxy : ret₂ x.1 = ret₂ y.1) : q x = q y := by
  apply hq.eq_of_controller_probes x y
  · rw [grade_ret₂ _ (not_mute₂_of_low hj x), grade_ret₂ _ (not_mute₂_of_low hj y), hxy]
  · obtain ⟨c, hc⟩ := D₂_complete (Finset.univ, D₂.grade x.1)
      (Plan.mem_gradedPlan.mpr ⟨D₂.isPlan.domain_mem, D₂.grade_pos x.1,
        (x.2.2.trans hj).trans (by decide : 3 ≤ (Finset.univ : Finset (Fin 4)).card)⟩)
    exact ⟨⟨c, by rw [hc]; exact ⟨Finset.Subset.refl _, x.2.2⟩⟩, hc⟩
  · intro c hx hy hc
    exact (rows₂_E_of_not_mute (not_mute₂_of_low hj c) ⟨x.1, hx⟩).trans
      ((family₂.rows.E_congr' rfl hxy).trans
        (rows₂_E_of_not_mute (not_mute₂_of_low hj c) ⟨y.1, hy⟩).symm)

theorem exists_emb₀_of_proper (c : Cell C₂) (hc : C₂.scope c ≠ Finset.univ) :
    ∃ i, emb₀ i = c := by
  rcases hw : family₂.e.symm c with p | H | s | a
  · refine ⟨family₀.e (.inl p), ?_⟩
    change family₂.e (embX₀ (family₀.e.symm (family₀.e _))) = _
    rw [Equiv.symm_apply_apply]
    change family₂.e (Sum.inl p) = c
    rw [← hw, Equiv.apply_symm_apply]
  all_goals exact absurd (by change (C₂.cell c).1 = _; rw [Family.cell_eq, hw]; rfl) hc

/-- **A section of the retraction** over the three-cell family, on cells: full cells to their
fresh copies, proper cells to the old cells. -/
noncomputable def secCell (c : Cell C₂) : Cell D₂ :=
  if h : C₂.scope c = Finset.univ then
    Fin.natAdd C₀.card ((Fintype.equivFin New₂) (.inr (.inl ⟨c, h⟩)))
  else
    Fin.castAdd (Fintype.card New₂) (Classical.choose (exists_emb₀_of_proper c h))

theorem secCell_of_full (c : Cell C₂) (h : C₂.scope c = Finset.univ) :
    secCell c = Fin.natAdd C₀.card ((Fintype.equivFin New₂) (.inr (.inl ⟨c, h⟩))) := by
  unfold secCell; exact dite_of_pos h

theorem secCell_of_proper (c : Cell C₂) (h : ¬ C₂.scope c = Finset.univ) :
    secCell c = Fin.castAdd (Fintype.card New₂) (Classical.choose (exists_emb₀_of_proper c h)) := by
  unfold secCell; exact dite_of_neg h

theorem ret₂_secCell (c : Cell C₂) : ret₂ (secCell c) = c := by
  by_cases h : C₂.scope c = Finset.univ
  · rw [secCell_of_full c h, ret₂_natAdd, Equiv.symm_apply_apply]; rfl
  · rw [secCell_of_proper c h, ret₂_castAdd]
    exact Classical.choose_spec (exists_emb₀_of_proper c h)

theorem cell_secCell (c : Cell C₂) :
    D₂.cell (secCell c) =
      (if C₂.scope c = Finset.univ then Finset.univ else (C₂.scope c).image Fin.castSuccEmb,
        C₂.grade c) := by
  by_cases h : C₂.scope c = Finset.univ
  · rw [secCell_of_full c h, D₂_cell_natAdd, Equiv.symm_apply_apply, ite_eq_left h]; rfl
  · rw [secCell_of_proper c h, D₂_cell_castAdd, ite_eq_right h]
    have hc := Classical.choose_spec (exists_emb₀_of_proper c h)
    have e : C₀.cell (Classical.choose (exists_emb₀_of_proper c h)) = C₂.cell c := by
      rw [← cell_emb₀, hc]
    rw [e]; rfl

/-- The section on lower sets. -/
noncomputable def sec₂ (j : ℕ) (c : C₂.below (Finset.univ, j)) : D₂.below (Finset.univ, j) :=
  ⟨secCell c.1, by rw [cell_secCell]; exact ⟨Finset.subset_univ _, c.2.2⟩⟩

theorem sec₂_val {j : ℕ} (c : C₂.below (Finset.univ, j)) : (sec₂ j c).1 = secCell c.1 := rfl

theorem sec₂_ret {j : ℕ} (c : C₂.below (Finset.univ, j)) : ret₂ (sec₂ j c).1 = c.1 :=
  ret₂_secCell c.1

theorem cell_sec₂ {j : ℕ} (c : C₂.below (Finset.univ, j)) :
    D₂.cell (sec₂ j c).1 =
      (if C₂.scope c.1 = Finset.univ then Finset.univ else (C₂.scope c.1).image Fin.castSuccEmb,
        C₂.grade c.1) := cell_secCell c.1

theorem not_mute₂_sec₂ {j : ℕ} (hj : j ≤ 3) (c : C₂.below (Finset.univ, j)) :
    ¬ mute₂ (sec₂ j c).1 := not_mute₂_of_low hj _

theorem hsec₂_le {j : ℕ} (d Sig : C₂.below (Finset.univ, j))
    (h : GradedLe (C₂.cell d.1) (C₂.cell Sig.1)) :
    GradedLe (D₂.cell (sec₂ j d).1) (D₂.cell (sec₂ j Sig).1) := by
  rw [cell_sec₂, cell_sec₂]
  refine ⟨?_, h.2⟩
  dsimp only
  split_ifs with h1 h2 h2
  · exact Finset.Subset.refl _
  · exfalso; apply h2
    have := h.1
    change C₂.scope d.1 ⊆ C₂.scope Sig.1 at this
    rw [h1] at this
    exact Finset.univ_subset_iff.mp this
  · exact Finset.subset_univ _
  · exact Finset.image_subset_image h.1

theorem hsec₂_scope {j : ℕ} (d Sig : C₂.below (Finset.univ, j))
    (h : C₂.scope d.1 ⊆ C₂.scope Sig.1) :
    D₂.scope (sec₂ j d).1 ⊆ D₂.scope (sec₂ j Sig).1 := by
  change (D₂.cell (sec₂ j d).1).1 ⊆ (D₂.cell (sec₂ j Sig).1).1
  rw [cell_sec₂, cell_sec₂]
  dsimp only
  split_ifs with h1 h2 h2
  · exact Finset.Subset.refl _
  · exfalso; apply h2
    rw [h1] at h
    exact Finset.univ_subset_iff.mp h
  · exact Finset.subset_univ _
  · exact Finset.image_subset_image h

theorem hretB₂ {j : ℕ} (hj : j ≤ 3) (a : D₂.below (Finset.univ, j)) :
    GradedLe (C₂.cell (ret₂ a.1)) (Finset.univ, j) := by
  refine ⟨Finset.subset_univ _, ?_⟩
  change C₂.grade (ret₂ a.1) ≤ j
  rw [← grade_ret₂ a.1 (not_mute₂_of_low hj a)]
  exact a.2.2

/-- **Descent**: a respecting labelling of a full-scope lower set of grade `≤ 3` descends along
the section to a respecting labelling of the three-cell family. -/
theorem descend₂ {j : ℕ} (hj : j ≤ 3) {q : D₂.below (Finset.univ, j) → ExtOrd}
    (hq : RespectsSemanticsBelow rows₂ (Finset.univ, j) q) :
    RespectsSemanticsBelow family₂.rows (Finset.univ, j) (fun d => q (sec₂ j d)) :=
  RespectsSemanticsBelow.descend hq (not_mute₂_of_low hj) (hretB₂ hj) (rigidity₂ hj hq) (sec₂ j)
    sec₂_ret hsec₂_le hsec₂_scope

theorem ret₂_le_univ {C : Finset (Fin 4)} {i j : ℕ} (hC : C ≠ Finset.univ)
    (h : GradedLe (C, i) (Finset.univ, j)) (d : D₂.below (C, i)) :
    GradedLe (C₂.cell (ret₂ d.1)) (Finset.univ, j) := by
  refine ⟨Finset.subset_univ _, ?_⟩
  change C₂.grade (ret₂ d.1) ≤ j
  rw [← grade_ret₂ d.1 (not_mute₂_of_proper hC d)]
  exact d.2.2.trans h.2

/-- **The extension principle on the three-cell family** for a proper pair `(C, i)` below
`(univ, j)`: a respecting labelling `p` of the pair's lower set, read into the three-cell family
along the retraction, extends to a respecting labelling of `(univ, j)` agreeing below `γ` with a
given one.  When the retraction is onto the fold's lower set this is `family₂`'s bountifulness;
for the two grade-three faces it is the genuine two-context obligation. -/
def Ext (C : Finset (Fin 4)) (i j : ℕ) (hC : C ≠ Finset.univ)
    (h : GradedLe (C, i) (Finset.univ, j)) : Prop :=
  ∀ (p : D₂.below (C, i) → ExtOrd) (q : C₂.below (Finset.univ, j) → ExtOrd) (γ : ExtOrd),
    RespectsSemanticsBelow rows₂ (C, i) p →
    RespectsSemanticsBelow family₂.rows (Finset.univ, j) q →
    extVisibilityReplace γ j j = γ →
    (∀ d : D₂.below (C, i), min (q ⟨ret₂ d.1, ret₂_le_univ hC h d⟩) γ = min (p d) γ) →
    ∃ q' : C₂.below (Finset.univ, j) → ExtOrd,
      RespectsSemanticsBelow family₂.rows (Finset.univ, j) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D₂.below (C, i), q' ⟨ret₂ d.1, ret₂_le_univ hC h d⟩ = p d)

/-- **Scope change from the extension principle**: descend, extend, pull back. -/
theorem scopeChange_of_ext {C : Finset (Fin 4)} {i j : ℕ} (hj : j ≤ 3) (hC : C ≠ Finset.univ)
    (h : GradedLe (C, i) (Finset.univ, j)) (hext : Ext C i j hC h)
    (p : D₂.below (C, i) → ExtOrd) (q : D₂.below (Finset.univ, j) → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow rows₂ (C, i) p)
    (hq : RespectsSemanticsBelow rows₂ (Finset.univ, j) q)
    (hγ : extVisibilityReplace γ j j = γ)
    (hagree : ∀ d : D₂.below (C, i), min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D₂.below (Finset.univ, j) → ExtOrd, RespectsSemanticsBelow rows₂ (Finset.univ, j) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D₂.below (C, i), q' (CellScheme.below.mono h d) = p d) := by
  have hqq := descend₂ hj hq
  obtain ⟨qq', hqq', hqq'γ, hqq'p⟩ := hext p (fun d => q (sec₂ j d)) γ hp hqq hγ (by
    intro d
    rw [← hagree d]
    congr 1
    exact rigidity₂ hj hq _ _ (sec₂_ret _))
  refine ⟨fun a => qq' ⟨ret₂ a.1, hretB₂ hj a⟩,
    RespectsSemanticsBelow.pullback_of_sect' (not_mute₂_of_low hj) (hretB₂ hj) hsect₂ hqq',
    ?_, ?_⟩
  · intro a
    rw [hqq'γ ⟨ret₂ a.1, hretB₂ hj a⟩]
    congr 1
    exact rigidity₂ hj hq _ _ (sec₂_ret _)
  · intro d
    exact hqq'p d

end ScopeChange


section Assembly

theorem exists_emb₁_of_proper (c : Cell C₂) (hc : C₂.scope c ≠ Finset.univ) :
    ∃ i, emb₁ i = c := by
  rcases hw : family₂.e.symm c with p | H | s | a
  · refine ⟨family₁.e (.inl p), ?_⟩
    change family₂.e (embX₁ (family₁.e.symm (family₁.e _))) = _
    rw [Equiv.symm_apply_apply]
    change family₂.e (Sum.inl p) = c
    rw [← hw, Equiv.apply_symm_apply]
  all_goals exact absurd (by change (C₂.cell c).1 = _; rw [Family.cell_eq, hw]; rfl) hc

theorem exists_emb₀_of_grade_le_two (c : Cell C₂) (hc : C₂.grade c ≤ 2) : ∃ i, emb₀ i = c := by
  rcases hw : family₂.e.symm c with p | H | s | a
  · exact exists_emb₀_of_proper c (by
      change (C₂.cell c).1 ≠ _; rw [Family.cell_eq, hw]; exact Prop3.scope_ne_univ p)
  · refine ⟨family₀.e (.inr (.inl ⟨H.1, H.2⟩)), ?_⟩
    change family₂.e (embX₀ (family₀.e.symm (family₀.e _))) = _
    rw [Equiv.symm_apply_apply]
    change family₂.e (Sum.inr (Sum.inl H)) = c
    rw [← hw, Equiv.apply_symm_apply]
  · refine ⟨family₀.e (.inr (.inr (.inl ⟨s.1, s.2⟩))), ?_⟩
    change family₂.e (embX₀ (family₀.e.symm (family₀.e _))) = _
    rw [Equiv.symm_apply_apply]
    change family₂.e (Sum.inr (Sum.inr (Sum.inl s))) = c
    rw [← hw, Equiv.apply_symm_apply]
  · exfalso
    have : C₂.grade c = 3 := by change (C₂.cell c).2 = 3; rw [Family.cell_eq, hw]; rfl
    omega

theorem exists_emb₁_of_grade_le_two (c : Cell C₂) (hc : C₂.grade c ≤ 2) : ∃ i, emb₁ i = c := by
  rcases hw : family₂.e.symm c with p | H | s | a
  · exact exists_emb₁_of_proper c (by
      change (C₂.cell c).1 ≠ _; rw [Family.cell_eq, hw]; exact Prop3.scope_ne_univ p)
  · refine ⟨family₁.e (.inr (.inl ⟨H.1, H.2⟩)), ?_⟩
    change family₂.e (embX₁ (family₁.e.symm (family₁.e _))) = _
    rw [Equiv.symm_apply_apply]
    change family₂.e (Sum.inr (Sum.inl H)) = c
    rw [← hw, Equiv.apply_symm_apply]
  · refine ⟨family₁.e (.inr (.inr (.inl ⟨s.1, s.2⟩))), ?_⟩
    change family₂.e (embX₁ (family₁.e.symm (family₁.e _))) = _
    rw [Equiv.symm_apply_apply]
    change family₂.e (Sum.inr (Sum.inr (Sum.inl s))) = c
    rw [← hw, Equiv.apply_symm_apply]
  · exfalso
    have : C₂.grade c = 3 := by change (C₂.cell c).2 = 3; rw [Family.cell_eq, hw]; rfl
    omega

theorem exists_emb₀_below {S : Finset (Fin 3)} {i : ℕ} (hk : i ≤ 2 ∨ S ≠ Finset.univ)
    (y : Cell C₂) (hy : GradedLe (C₂.cell y) (S, i)) : ∃ i', emb₀ i' = y := by
  by_cases hs : C₂.scope y = Finset.univ
  · rcases hk with hk | hk
    · exact exists_emb₀_of_grade_le_two y ((hy.2 : C₂.grade y ≤ i).trans hk)
    · exfalso; apply hk
      have := hy.1
      change C₂.scope y ⊆ S at this
      rw [hs] at this
      exact Finset.univ_subset_iff.mp this
  · exact exists_emb₀_of_proper y hs

theorem exists_emb₁_below {S : Finset (Fin 3)} {i : ℕ} (hk : i ≤ 2 ∨ S ≠ Finset.univ)
    (y : Cell C₂) (hy : GradedLe (C₂.cell y) (S, i)) : ∃ i', emb₁ i' = y := by
  by_cases hs : C₂.scope y = Finset.univ
  · rcases hk with hk | hk
    · exact exists_emb₁_of_grade_le_two y ((hy.2 : C₂.grade y ≤ i).trans hk)
    · exfalso; apply hk
      have := hy.1
      change C₂.scope y ⊆ S at this
      rw [hs] at this
      exact Finset.univ_subset_iff.mp this
  · exact exists_emb₁_of_proper y hs

/-- Every proper face avoids `3` or avoids `0`. -/
theorem proper_side : ∀ C ∈ plan₄, C ≠ Finset.univ → (3 : Fin 4) ∉ C ∨ (0 : Fin 4) ∉ C := by
  decide

theorem ret₂_inj_proper {C : Finset (Fin 4)} {i : ℕ} (hCp : C ∈ plan₄) (hC : C ≠ Finset.univ)
    (a b : D₂.below (C, i)) (h : ret₂ a.1 = ret₂ b.1) : a = b := by
  rcases proper_side C hCp hC with h3 | h0
  · have hB := sub_castSucc_of_not_last C hCp h3
    obtain ⟨x, hx⟩ := old_of_A hB a
    obtain ⟨y, hy⟩ := old_of_A hB b
    rw [← hx, ← hy, ret₂_castAdd, ret₂_castAdd] at h
    apply Subtype.ext
    rw [← hx, ← hy, emb₀_injective h]
  · apply retB_inj h0
    rw [ret₂_eq_emb₁_retB h0 a, ret₂_eq_emb₁_retB h0 b] at h
    exact emb₁_injective h

theorem ret₂_mem_fold {C : Finset (Fin 4)} {i : ℕ} (hC : C ≠ Finset.univ) (a : D₂.below (C, i)) :
    GradedLe (C₂.cell (ret₂ a.1)) (C.image fold, i) := by
  have hnm := not_mute₂_of_proper hC a
  refine ⟨?_, ?_⟩
  · change C₂.scope (ret₂ a.1) ⊆ _
    rw [scope_ret₂ _ hnm]
    exact Finset.image_subset_image a.2.1
  · change C₂.grade (ret₂ a.1) ≤ i
    rw [← grade_ret₂ _ hnm]; exact a.2.2

theorem ret₂_surj_proper {C : Finset (Fin 4)} {i : ℕ} (hCp : C ∈ plan₄) (hC : C ≠ Finset.univ)
    (hk : i ≤ 2 ∨ C.image fold ≠ Finset.univ) (y : C₂.below (C.image fold, i)) :
    ∃ a : D₂.below (C, i), ret₂ a.1 = y.1 := by
  rcases proper_side C hCp hC with h3 | h0
  · obtain ⟨i', hi'⟩ := exists_emb₀_below hk y.1 y.2
    have hy' : GradedLe (C₀.cell i') (C.image fold, i) := by rw [← cell_emb₀, hi']; exact y.2
    obtain ⟨a, ha⟩ := (eA hCp h3 i).surjective ⟨i', hy'⟩
    refine ⟨a, ?_⟩
    obtain ⟨x, hx⟩ := old_of_A (sub_castSucc_of_not_last C hCp h3) a
    have hr : retA a.1 = i' := congrArg Subtype.val ha
    rw [← hx, retA_castAdd] at hr
    rw [← hx, ret₂_castAdd, hr, hi']
  · obtain ⟨i', hi'⟩ := exists_emb₁_below hk y.1 y.2
    have hy' : GradedLe (C₁.cell i') (C.image fold, i) := by rw [← cell_emb₁, hi']; exact y.2
    obtain ⟨a, ha⟩ := retB_surj hCp h0 ⟨i', hy'⟩
    exact ⟨a, by rw [ret₂_eq_emb₁_retB h0 a, ha]; exact hi'⟩

/-- **The retraction is a bijection** from the lower set of a proper pair onto the fold's lower
set in the three-cell family, except at the two grade-three faces. -/
noncomputable def eC₂ {C : Finset (Fin 4)} {i : ℕ} (hCp : C ∈ plan₄) (hC : C ≠ Finset.univ)
    (hk : i ≤ 2 ∨ C.image fold ≠ Finset.univ) : D₂.below (C, i) ≃ C₂.below (C.image fold, i) :=
  Equiv.ofBijective (fun a => ⟨ret₂ a.1, ret₂_mem_fold hC a⟩)
    ⟨fun a b hab => ret₂_inj_proper hCp hC a b (congrArg Subtype.val hab),
     fun y => by obtain ⟨a, ha⟩ := ret₂_surj_proper hCp hC hk y; exact ⟨a, Subtype.ext ha⟩⟩

theorem eC₂_val {C : Finset (Fin 4)} {i : ℕ} (hCp : C ∈ plan₄) (hC : C ≠ Finset.univ)
    (hk : i ≤ 2 ∨ C.image fold ≠ Finset.univ) (a : D₂.below (C, i)) :
    (eC₂ hCp hC hk a).1 = ret₂ a.1 := rfl

theorem eC₂_scope {C : Finset (Fin 4)} {i : ℕ} (hCp : C ∈ plan₄) (hC : C ≠ Finset.univ)
    (hk : i ≤ 2 ∨ C.image fold ≠ Finset.univ) (a b : D₂.below (C, i)) :
    D₂.scope a.1 ⊆ D₂.scope b.1 ↔
      C₂.scope (eC₂ hCp hC hk a).1 ⊆ C₂.scope (eC₂ hCp hC hk b).1 := by
  rw [eC₂_val, eC₂_val, scope_ret₂ _ (not_mute₂_of_proper hC a),
    scope_ret₂ _ (not_mute₂_of_proper hC b)]
  constructor
  · exact Finset.image_subset_image
  · intro hs x hx
    have hx' : fold x ∈ (D₂.scope b.1).image fold := hs (Finset.mem_image_of_mem fold hx)
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx'
    have := fold_injOn C hCp hC y (b.2.1 hy) x (a.2.1 hx) hxy
    rw [← this]; exact hy

theorem respects_iff_C₂ {C : Finset (Fin 4)} {i : ℕ} (hCp : C ∈ plan₄) (hC : C ≠ Finset.univ)
    (hk : i ≤ 2 ∨ C.image fold ≠ Finset.univ) (q : D₂.below (C, i) → ExtOrd) :
    RespectsSemanticsBelow rows₂ (C, i) q ↔
      RespectsSemanticsBelow family₂.rows (C.image fold, i) (q ∘ (eC₂ hCp hC hk).symm) :=
  respects_iff_of_equiv (eC₂ hCp hC hk) (fun a => grade_ret₂ _ (not_mute₂_of_proper hC a))
    (eC₂_scope hCp hC hk) (fun Sig d _ => rows₂_E_of_not_mute (not_mute₂_of_proper hC Sig) d) q

/-- **The extension principle holds off the grade-three faces**: it is `family₂`'s bountifulness
through the bijection. -/
theorem ext_of_bij {C : Finset (Fin 4)} {i j : ℕ} (hCp : C ∈ plan₄) (hC : C ≠ Finset.univ)
    (hCI : (C, i) ∈ Plan.gradedPlan plan₄) (hj : (Finset.univ, j) ∈ Plan.gradedPlan plan₄)
    (hj3 : j ≤ 3) (h : GradedLe (C, i) (Finset.univ, j))
    (hk : i ≤ 2 ∨ C.image fold ≠ Finset.univ) : Ext C i j hC h := by
  intro p q γ hp hq hγ hagree
  set e := eC₂ hCp hC hk with he
  have hp' : RespectsSemanticsBelow family₂.rows (C.image fold, i) (p ∘ e.symm) :=
    (respects_iff_C₂ hCp hC hk p).mp hp
  have hfoldC : (C.image fold, i) ∈ Plan.gradedPlan Prop3.plan := by
    obtain ⟨-, hi0, hiC⟩ := Plan.mem_gradedPlan.mp hCI
    exact Plan.mem_gradedPlan.mpr ⟨fold_mem_plan C hCp hC, hi0, by
      change i ≤ (C.image fold).card; rw [card_fold_proper C hCp hC]; exact hiC⟩
  have hunivj : (Finset.univ, j) ∈ Plan.gradedPlan Prop3.plan := by
    obtain ⟨-, hj0, -⟩ := Plan.mem_gradedPlan.mp hj
    exact Plan.mem_gradedPlan.mpr ⟨C₂.isPlan.domain_mem, hj0, by
      change j ≤ (Finset.univ : Finset (Fin 3)).card
      rw [Finset.card_univ, Fintype.card_fin]; exact hj3⟩
  have h' : GradedLe (C.image fold, i) (Finset.univ, j) := ⟨Finset.subset_univ _, h.2⟩
  have hag' : ∀ d' : C₂.below (C.image fold, i),
      min (q (CellScheme.below.mono h' d')) γ = min ((p ∘ e.symm) d') γ := by
    intro d'
    have := hagree (e.symm d')
    have e1 : (⟨ret₂ (e.symm d').1, ret₂_le_univ hC h (e.symm d')⟩ : C₂.below (Finset.univ, j)) =
        CellScheme.below.mono h' d' := by
      apply Subtype.ext
      change ret₂ (e.symm d').1 = d'.1
      exact congrArg Subtype.val (e.apply_symm_apply d')
    rw [e1] at this
    exact this
  by_cases hne : (C.image fold, i) = (Finset.univ, j)
  · refine ⟨fun d => (p ∘ e.symm) ⟨d.1, by rw [hne]; exact d.2⟩,
      RespectsSemanticsBelow.cast hne hp', ?_, ?_⟩
    · intro d
      exact (hag' ⟨d.1, by rw [hne]; exact d.2⟩).symm
    · intro d
      change p (e.symm ⟨ret₂ d.1, _⟩) = p d
      rw [show (⟨ret₂ d.1, _⟩ : C₂.below (C.image fold, i)) = e d from Subtype.ext rfl,
        e.symm_apply_apply]
  · obtain ⟨q', hq', hq'γ, hq'p⟩ :=
      semScheme₂.bountiful _ _ hfoldC hunivj h' hne (p ∘ e.symm) q γ hp' hq hγ hag'
    refine ⟨q', hq', hq'γ, fun d => ?_⟩
    have h2 := hq'p (e d)
    change q' (CellScheme.below.mono h' (e d)) = p (e.symm (e d)) at h2
    rw [e.symm_apply_apply] at h2
    have e3 : (⟨ret₂ d.1, ret₂_le_univ hC h d⟩ : C₂.below (Finset.univ, j)) =
        CellScheme.below.mono h' (e d) := Subtype.ext rfl
    rw [e3]; exact h2

theorem face_of_fold_univ : ∀ C ∈ plan₄, C ≠ Finset.univ → C.image fold = Finset.univ →
    C = {0, 1, 2} ∨ C = {1, 2, 3} := by decide

/-- **The two grade-three face obligations** — the genuine two-context content: a respecting
labelling of a face's top lower set (input A's, resp. input B's), together with a respecting
labelling of the three-cell family agreeing with it below `γ`, extends to a respecting labelling
of the three-cell family agreeing with the given one below `γ`. -/
def FaceExtA : Prop := Ext {0, 1, 2} 3 3 (by decide) ⟨Finset.subset_univ _, le_rfl⟩
def FaceExtB : Prop := Ext {1, 2, 3} 3 3 (by decide) ⟨Finset.subset_univ _, le_rfl⟩

def ProperToFull₂ : Prop :=
  ∀ (CI : Finset (Fin 4) × ℕ) (j : ℕ), CI ∈ Plan.gradedPlan plan₄ → CI.1 ≠ Finset.univ →
    (Finset.univ, j) ∈ Plan.gradedPlan plan₄ → (h : GradedLe CI (Finset.univ, j)) →
    ∀ (p : D₂.below CI → ExtOrd) (q : D₂.below (Finset.univ, j) → ExtOrd) (γ : ExtOrd),
      RespectsSemanticsBelow rows₂ CI p → RespectsSemanticsBelow rows₂ (Finset.univ, j) q →
      extVisibilityReplace γ j j = γ →
      (∀ d : D₂.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) →
      ∃ q' : D₂.below (Finset.univ, j) → ExtOrd, RespectsSemanticsBelow rows₂ (Finset.univ, j) q' ∧
        (∀ d, min (q' d) γ = min (q d) γ) ∧
        (∀ d : D₂.below CI, q' (CellScheme.below.mono h d) = p d)

/-- The scope-changing cases of grade at most three: `family₂`'s bountifulness off the grade-three
faces, the two face obligations at them. -/
theorem properToFull₂_low (HA : FaceExtA) (HB : FaceExtB) (CI : Finset (Fin 4) × ℕ) (j : ℕ)
    (hj3 : j ≤ 3) (hCI : CI ∈ Plan.gradedPlan plan₄) (hC : CI.1 ≠ Finset.univ)
    (hj : (Finset.univ, j) ∈ Plan.gradedPlan plan₄) (h : GradedLe CI (Finset.univ, j))
    (p : D₂.below CI → ExtOrd) (q : D₂.below (Finset.univ, j) → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow rows₂ CI p) (hq : RespectsSemanticsBelow rows₂ (Finset.univ, j) q)
    (hγ : extVisibilityReplace γ j j = γ)
    (hagree : ∀ d : D₂.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D₂.below (Finset.univ, j) → ExtOrd, RespectsSemanticsBelow rows₂ (Finset.univ, j) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D₂.below CI, q' (CellScheme.below.mono h d) = p d) := by
  obtain ⟨C, i⟩ := CI
  dsimp only at hC
  have hCp : C ∈ plan₄ := (Plan.mem_gradedPlan.mp hCI).1
  by_cases hk : i ≤ 2 ∨ C.image fold ≠ Finset.univ
  · exact scopeChange_of_ext hj3 hC h (ext_of_bij hCp hC hCI hj hj3 h hk) p q γ hp hq hγ hagree
  · rw [not_or, not_le, not_ne_iff] at hk
    obtain ⟨hi2, hfu⟩ := hk
    have hi3 : i = 3 := by
      obtain ⟨-, -, hiC⟩ := Plan.mem_gradedPlan.mp hCI
      have h1 : (C.image fold).card = 3 := by
        rw [hfu, Finset.card_univ, Fintype.card_fin]
      have h2 := card_fold_proper C hCp hC
      change i ≤ C.card at hiC
      omega
    have hj3' : j = 3 := by
      have := h.2
      change i ≤ j at this
      omega
    subst hi3
    subst hj3'
    rcases face_of_fold_univ C hCp hC hfu with rfl | rfl
    · exact scopeChange_of_ext le_rfl hC h HA p q γ hp hq hγ hagree
    · exact scopeChange_of_ext le_rfl hC h HB p q γ hp hq hγ hagree

/-- **The scope-changing cases**: grade four by the general full-scope extension. -/
theorem properToFull₂ (HA : FaceExtA) (HB : FaceExtB) : ProperToFull₂ := by
  intro CI j hCI hC hj h p q γ hp hq hγ hagree
  by_cases hj3 : j ≤ 3
  · exact properToFull₂_low HA HB CI j hj3 hCI hC hj h p q γ hp hq hγ hagree
  · have hj4 : j = 4 := by
      obtain ⟨-, -, hjc⟩ := Plan.mem_gradedPlan.mp hj
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
    obtain ⟨q₃, hq₃, hq₃γ, hq₃ext⟩ := properToFull₂_low HA HB CI 3 le_rfl hCI hC hu3 hC3
      p (fun d => q (CellScheme.below.mono h₃ d)) γ hp (hq.mono h₃)
      ((show SelfVis 4 γ from hγ).mono (by omega)) (fun d => hagree d)
    obtain ⟨q', hq', hq'γ, hq'ext⟩ := bountiful_full_scope rows₂ h₃ q₃ q γ hq₃ hq hγ
      (fun d => (hq₃γ d).symm)
    refine ⟨q', hq', hq'γ, fun d => ?_⟩
    have e : CellScheme.below.mono h d =
        CellScheme.below.mono h₃ (CellScheme.below.mono hC3 d) := rfl
    rw [e, hq'ext, hq₃ext]

/-- **Bountifulness of the glued scheme**, conditional on the two face obligations. -/
theorem rows₂_isBountiful_of (HA : FaceExtA) (HB : FaceExtB) : rows₂.IsBountiful := by
  intro CI BJ hCI hBJ h _ p q γ hp hq hγ hagree
  by_cases hB : BJ.1 = Finset.univ
  · by_cases hC : CI.1 = Finset.univ
    · obtain ⟨B, j⟩ := BJ
      obtain ⟨C, i⟩ := CI
      dsimp only at hB hC
      subst hB hC
      exact bountiful_full_scope rows₂ h p q γ hp hq hγ hagree
    · obtain ⟨B, j⟩ := BJ
      dsimp only at hB
      subst hB
      exact properToFull₂ HA HB CI j hCI hC hBJ h p q γ hp hq hγ hagree
  · have hBp : BJ.1 ∈ plan₄ := (Plan.mem_gradedPlan.mp hBJ).1
    rcases proper_side BJ.1 hBp hB with h3 | h0
    · exact bountiful₂_A CI BJ hCI hBJ h h3 p q γ hp hq hγ hagree
    · exact bountiful₂_B CI BJ hCI hBJ h h0 p q γ hp hq hγ hagree

/-- **The glued four-point domain with its associated semantics**, conditional on the two
grade-three face obligations. -/
noncomputable abbrev semSchemeGlue (HA : FaceExtA) (HB : FaceExtB) : SemScheme 4 where
  scheme := D₂
  rows := rows₂
  rows_coded := rows₂_isCoded
  consistent := rows₂_isConsistent
  bountiful := rows₂_isBountiful_of HA HB
  complete := D₂_complete

end Assembly

/-! ## Part B8: literal preservation of input A, freshness, and the face obligations in
three-point terms -/

section Endpoint

theorem vis₂ : Finset.univ.image Fin.castSuccEmb ∈ D₂.plan := CellScheme.extendOneWith_visible

/-- **Input A is preserved literally**: the initial face of the glued scheme is `family₀`'s
scheme. -/
theorem hE₂ : D₂.restrictFace Fin.castSuccEmb vis₂ = C₀ :=
  CellScheme.restrictFace_extendOneWith newCell₂_last

theorem hcard₂ : (D₂.restrictFace Fin.castSuccEmb vis₂).card = C₀.card :=
  congrArg CellScheme.card hE₂

theorem toCell_cast₂ (i : Cell C₀) :
    toCell D₂ Fin.castSuccEmb vis₂ (Fin.cast hcard₂.symm i) = Fin.castAdd (Fintype.card New₂) i :=
  CellScheme.restrictFace.toCell_cast_eq_of_emb D₂ Fin.castSuccEmb vis₂ (e := Fin.castAdd _)
    (Fin.strictMono_castAdd _)
    (fun c => (CellScheme.extendOneWith_scope_subset_iff newCell₂_last _).mpr ⟨c, rfl⟩) hcard₂ i

/-- The restricted rows are input A's rows. -/
theorem rows₂_restrict (Sig : Cell C₀) (d : C₀.below (C₀.cell Sig))
    (pf : GradedLe ((D₂.restrictFace Fin.castSuccEmb vis₂).cell (Fin.cast hcard₂.symm d.1))
      ((D₂.restrictFace Fin.castSuccEmb vis₂).cell (Fin.cast hcard₂.symm Sig))) :
    (rows₂.restrictFace Fin.castSuccEmb vis₂).E (Fin.cast hcard₂.symm Sig)
      ⟨Fin.cast hcard₂.symm d.1, pf⟩ = family₀.rows.E Sig d := by
  change rows₂.E (toCell D₂ Fin.castSuccEmb vis₂ (Fin.cast hcard₂.symm Sig))
    ⟨toCell D₂ Fin.castSuccEmb vis₂ (Fin.cast hcard₂.symm d.1), _⟩ = family₀.rows.E Sig d
  have hc : GradedLe (D₂.cell (Fin.castAdd (Fintype.card New₂) d.1))
      (D₂.cell (Fin.castAdd (Fintype.card New₂) Sig)) := by
    rw [D₂_cell_castAdd, D₂_cell_castAdd]
    exact (CellScheme.restrictFace.gradedLe_pushGraded_iff _).mpr d.2
  rw [rows₂.E_congr (toCell_cast₂ Sig) (toCell_cast₂ d.1) (hd := hc)]
  exact rows₂_E_castAdd Sig ⟨Fin.castAdd _ d.1, hc⟩ d.1 rfl d.2

/-- **Literal old-face preservation of input A** (rows included), for the conditional domain. -/
theorem extendsDomainGlue (HA : FaceExtA) (HB : FaceExtB) :
    ExtendsDomain p₀ (semSchemeGlue HA HB) where
  visible := vis₂
  restrict := by
    refine SemScheme.ext_of_components (congrArg CellScheme.plan hE₂) (congrArg CellScheme.card hE₂)
      (fun i => CellScheme.cell_cast_of_eq hE₂ i) (fun Sig d => ?_)
    exact rows₂_restrict Sig d _

/-! ### Freshness: the fresh face's level-three cell is nobody's copy -/

noncomputable def b₁cell₁ : Cell C₁ :=
  family₁.e (.inr (.inr (.inr ⟨b₁, Finset.mem_singleton_self _⟩)))

theorem scope_b₁cell₁ : C₁.scope b₁cell₁ = Finset.univ := by
  change (C₁.cell (family₁.e _)).1 = _
  rw [Family.cell_e]; rfl

/-- The copy of input B's level-three cell at the fresh face `{1, 2, 3}`. -/
noncomputable def b₁copy : Cell D₂ :=
  Fin.natAdd C₀.card ((Fintype.equivFin New₂)
    (.inl ⟨(⟨{1, 2, 3}, one_two_three_mem_newFacesB⟩, b₁cell₁),
      by rw [scope_b₁cell₁, image_fold_one_two_three]⟩))

theorem cell_b₁copy : D₂.cell b₁copy = ({1, 2, 3}, 3) := by
  unfold b₁copy
  rw [D₂_cell_natAdd, Equiv.symm_apply_apply]
  change (({1, 2, 3} : Finset (Fin 4)), (C₁.cell b₁cell₁).2) = _
  unfold b₁cell₁
  rw [Family.cell_e]; rfl

theorem ret₂_b₁copy : ret₂ b₁copy = emb₁ b₁cell₁ := by
  unfold b₁copy
  rw [ret₂_natAdd, Equiv.symm_apply_apply]; rfl

theorem not_mute₂_b₁copy : ¬ mute₂ b₁copy := by
  intro h
  change D₂.cell b₁copy = _ at h
  rw [cell_b₁copy] at h
  exact absurd (congrArg Prod.snd h) (by decide)

/-- The fresh face's level-three cell reads its own cap `γ₁ = ω·2 + 3`. -/
theorem diag_b₁copy : rows₂.E b₁copy ⟨b₁copy, ⟨Finset.Subset.refl _, le_rfl⟩⟩ = γ₁ := by
  have hab : GradedLe (C₁.cell b₁cell₁) (C₁.cell b₁cell₁) := ⟨Finset.Subset.refl _, le_rfl⟩
  refine (rows₂_E_emb₁ not_mute₂_b₁copy _ b₁cell₁ b₁cell₁ ret₂_b₁copy ret₂_b₁copy hab).trans ?_
  change family₁.rowX (family₁.e.symm (family₁.e _)) (family₁.e.symm (family₁.e _)) = γ₁
  rw [Equiv.symm_apply_apply, Family.rowX_a_a]
  change min (meet₃ st₀ t₁ t₁) (min γ₁ γ₁) = γ₁
  rw [CappedCore3.meet₃_self', min_self]
  exact min_self _

theorem η₁_ne_γ₁ : η₁ ≠ γ₁ := by
  unfold η₁ γ₁
  intro h
  have h' := congrArg blockIdx (ofOrd_inj.mp h)
  rw [blockIdx_mul_add, blockIdx_mul_add] at h'
  exact absurd (Nat.cast_injective h') (by decide)

theorem A_face_mem : ({0, 1, 2} : Finset (Fin 4)) ∈ plan₄ := by decide
theorem three_not_mem_A : (3 : Fin 4) ∉ ({0, 1, 2} : Finset (Fin 4)) := by decide

/-- **Freshness**: no level-three cell of input A's face reads `γ₁` at itself — the fresh point
is not a duplicate of an old point (contrast `fourPointDomain`, whose copies read the old rows). -/
theorem fresh_not_duplicate (x : D₂.below ({0, 1, 2}, 3)) (hx : D₂.grade x.1 = 3) :
    rows₂.E x.1 ⟨x.1, ⟨Finset.Subset.refl _, le_rfl⟩⟩ ≠ γ₁ := by
  obtain ⟨i, hi⟩ := old_of_A (sub_castSucc_of_not_last _ A_face_mem three_not_mem_A) x
  have hgi : C₀.grade i = 3 := by rw [← D₂_grade_castAdd, hi]; exact hx
  have hcell : family₀.cellX (family₀.e.symm i) = (Finset.univ, 3) := by
    rw [← Family.cell_eq]
    refine Prod.ext ?_ hgi
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin]
    have h3 := C₀.grade_le_card_scope i
    rw [hgi] at h3
    exact le_antisymm ((Finset.card_le_univ _).trans (by simp)) h3
  obtain ⟨a, ha⟩ := old_full_three hcell
  have key : rows₂.E x.1 ⟨x.1, ⟨Finset.Subset.refl _, le_rfl⟩⟩ =
      family₀.rowX (family₀.e.symm i) (family₀.e.symm i) := by
    have hle : GradedLe (C₀.cell i) (C₀.cell i) := ⟨Finset.Subset.refl _, le_rfl⟩
    have e1 := rows₂_E_castAdd i ⟨Fin.castAdd _ i, by rw [D₂_cell_castAdd]; exact
      (CellScheme.restrictFace.gradedLe_pushGraded_iff _).mpr hle⟩ i rfl hle
    exact (rows₂.E_congr' hi.symm hi.symm).trans e1
  rw [key, ha, Family.rowX_a_a]
  have ha2 : a.1 ∈ ({a₁, a₂} : Finset (CappedCore3 Prop3.gradeP T₀)) := a.2
  rcases Finset.mem_insert.mp ha2 with h1 | h1
  · rw [h1]
    change min (meet₃ st₀ t₀ t₀) (min η₁ η₁) ≠ γ₁
    rw [CappedCore3.meet₃_self', min_self]
    change min γ₀ η₁ ≠ γ₁
    rw [min_eq_right η₁_le_γ₀]
    exact η₁_ne_γ₁
  · rw [Finset.mem_singleton.mp h1]
    change min (meet₃ st₀ t₀ t₀) (min γ₀ γ₀) ≠ γ₁
    rw [CappedCore3.meet₃_self', min_self]
    change min γ₀ γ₀ ≠ γ₁
    rw [min_self]
    exact γ₁_ne_γ₀.symm

/-! ### The face obligations in three-point terms -/

/-- The inclusion of input A's top lower set into the three-cell family's. -/
noncomputable def embBelow₀ (d : C₀.below (Finset.univ, 3)) : C₂.below (Finset.univ, 3) :=
  ⟨emb₀ d.1, by rw [cell_emb₀]; exact d.2⟩
noncomputable def embBelow₁ (d : C₁.below (Finset.univ, 3)) : C₂.below (Finset.univ, 3) :=
  ⟨emb₁ d.1, by rw [cell_emb₁]; exact d.2⟩

/-- **The A-face obligation, in three-point terms**: a respecting labelling of `family₀`'s top
lower set and a respecting labelling of `family₂`'s top lower set agreeing with it below `γ` on
`family₀`'s cells have a common respecting extension on `family₂`'s top lower set: equal to the
first on `family₀`'s cells (in particular at `a₁`, `a₂`), agreeing with the second below `γ`
(in particular at `b₁`). -/
def FaceExtA' : Prop :=
  ∀ (p : C₀.below (Finset.univ, 3) → ExtOrd) (q : C₂.below (Finset.univ, 3) → ExtOrd)
    (γ : ExtOrd), RespectsSemanticsBelow family₀.rows (Finset.univ, 3) p →
    RespectsSemanticsBelow family₂.rows (Finset.univ, 3) q → extVisibilityReplace γ 3 3 = γ →
    (∀ d, min (q (embBelow₀ d)) γ = min (p d) γ) →
    ∃ q' : C₂.below (Finset.univ, 3) → ExtOrd,
      RespectsSemanticsBelow family₂.rows (Finset.univ, 3) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧ (∀ d, q' (embBelow₀ d) = p d)

/-- **The B-face obligation, in three-point terms** (with `family₁`'s cells; the free cells are
`a₁`, `a₂`). -/
def FaceExtB' : Prop :=
  ∀ (p : C₁.below (Finset.univ, 3) → ExtOrd) (q : C₂.below (Finset.univ, 3) → ExtOrd)
    (γ : ExtOrd), RespectsSemanticsBelow family₁.rows (Finset.univ, 3) p →
    RespectsSemanticsBelow family₂.rows (Finset.univ, 3) q → extVisibilityReplace γ 3 3 = γ →
    (∀ d, min (q (embBelow₁ d)) γ = min (p d) γ) →
    ∃ q' : C₂.below (Finset.univ, 3) → ExtOrd,
      RespectsSemanticsBelow family₂.rows (Finset.univ, 3) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧ (∀ d, q' (embBelow₁ d) = p d)

theorem image_fold_A : (({0, 1, 2} : Finset (Fin 4)).image fold, 3) =
    ((Finset.univ : Finset (Fin 3)), 3) := by decide
theorem image_fold_B : (({1, 2, 3} : Finset (Fin 4)).image fold, 3) =
    ((Finset.univ : Finset (Fin 3)), 3) := by decide
theorem univ_sub_fold_A :
    (Finset.univ : Finset (Fin 3)) ⊆ ({0, 1, 2} : Finset (Fin 4)).image fold := by
  decide
theorem univ_sub_fold_B :
    (Finset.univ : Finset (Fin 3)) ⊆ ({1, 2, 3} : Finset (Fin 4)).image fold := by
  decide
theorem zero_not_mem_B : (0 : Fin 4) ∉ ({1, 2, 3} : Finset (Fin 4)) := by decide
theorem B_face_mem : ({1, 2, 3} : Finset (Fin 4)) ∈ plan₄ := by decide

/-- The A-face obligation reduces to its three-point form. -/
theorem faceExtA_of (H : FaceExtA') : FaceExtA := by
  intro p q γ hp hq hγ hagree
  let e := eA A_face_mem three_not_mem_A 3
  have hp' := (respects_iff_A A_face_mem three_not_mem_A 3 p).mp hp
  let cast : C₀.below (Finset.univ, 3) → C₀.below (({0, 1, 2} : Finset (Fin 4)).image fold, 3) :=
    fun d => ⟨d.1, ⟨d.2.1.trans univ_sub_fold_A, d.2.2⟩⟩
  have hp'' : RespectsSemanticsBelow family₀.rows (Finset.univ, 3) ((p ∘ e.symm) ∘ cast) :=
    RespectsSemanticsBelow.cast image_fold_A hp'
  have hret : ∀ d : D₂.below ({0, 1, 2}, 3), ret₂ d.1 = emb₀ (e d).1 := by
    intro d
    obtain ⟨i, hi⟩ := old_of_A (sub_castSucc_of_not_last _ A_face_mem three_not_mem_A) d
    rw [← hi, ret₂_castAdd, eA_val, ← hi, retA_castAdd]
  have hC : ({0, 1, 2} : Finset (Fin 4)) ≠ Finset.univ := by decide
  have h : GradedLe (({0, 1, 2} : Finset (Fin 4)), 3) (Finset.univ, 3) :=
    ⟨Finset.subset_univ _, le_rfl⟩
  have key : ∀ d : C₀.below (Finset.univ, 3),
      (⟨ret₂ (e.symm (cast d)).1, ret₂_le_univ hC h (e.symm (cast d))⟩ :
        C₂.below (Finset.univ, 3)) = embBelow₀ d := by
    intro d
    apply Subtype.ext
    change ret₂ (e.symm (cast d)).1 = emb₀ d.1
    rw [hret, e.apply_symm_apply]
  obtain ⟨q', hq', hq'γ, hq'p⟩ := H ((p ∘ e.symm) ∘ cast) q γ hp'' hq hγ (by
    intro d
    exact (congrArg (fun z => min (q z) γ) (key d).symm).trans (hagree (e.symm (cast d))))
  refine ⟨q', hq', hq'γ, fun d => ?_⟩
  have h2 := hq'p ⟨(e d).1, ⟨(e d).2.1.trans (Finset.subset_univ _), (e d).2.2⟩⟩
  change q' (embBelow₀ _) = p (e.symm (cast ⟨(e d).1, _⟩)) at h2
  rw [show cast ⟨(e d).1, ⟨(e d).2.1.trans (Finset.subset_univ _), (e d).2.2⟩⟩ = e d from
    Subtype.ext rfl, e.symm_apply_apply] at h2
  have e4 : (⟨ret₂ d.1, ret₂_le_univ hC h d⟩ : C₂.below (Finset.univ, 3)) =
      embBelow₀ ⟨(e d).1, ⟨(e d).2.1.trans (Finset.subset_univ _), (e d).2.2⟩⟩ :=
    Subtype.ext (hret d)
  exact (congrArg q' e4).trans h2

/-- The B-face obligation reduces to its three-point form. -/
theorem faceExtB_of (H : FaceExtB') : FaceExtB := by
  intro p q γ hp hq hγ hagree
  let e := eB B_face_mem zero_not_mem_B 3
  have hp' := (respects_iff_B B_face_mem zero_not_mem_B 3 p).mp hp
  let cast : C₁.below (Finset.univ, 3) → C₁.below (({1, 2, 3} : Finset (Fin 4)).image fold, 3) :=
    fun d => ⟨d.1, ⟨d.2.1.trans univ_sub_fold_B, d.2.2⟩⟩
  have hp'' : RespectsSemanticsBelow family₁.rows (Finset.univ, 3) ((p ∘ e.symm) ∘ cast) :=
    RespectsSemanticsBelow.cast image_fold_B hp'
  have hret : ∀ d : D₂.below ({1, 2, 3}, 3), ret₂ d.1 = emb₁ (e d).1 :=
    fun d => ret₂_eq_emb₁_retB zero_not_mem_B d
  have hC : ({1, 2, 3} : Finset (Fin 4)) ≠ Finset.univ := by decide
  have h : GradedLe (({1, 2, 3} : Finset (Fin 4)), 3) (Finset.univ, 3) :=
    ⟨Finset.subset_univ _, le_rfl⟩
  have key : ∀ d : C₁.below (Finset.univ, 3),
      (⟨ret₂ (e.symm (cast d)).1, ret₂_le_univ hC h (e.symm (cast d))⟩ :
        C₂.below (Finset.univ, 3)) = embBelow₁ d := by
    intro d
    apply Subtype.ext
    change ret₂ (e.symm (cast d)).1 = emb₁ d.1
    rw [hret, e.apply_symm_apply]
  obtain ⟨q', hq', hq'γ, hq'p⟩ := H ((p ∘ e.symm) ∘ cast) q γ hp'' hq hγ (by
    intro d
    exact (congrArg (fun z => min (q z) γ) (key d).symm).trans (hagree (e.symm (cast d))))
  refine ⟨q', hq', hq'γ, fun d => ?_⟩
  have h2 := hq'p ⟨(e d).1, ⟨(e d).2.1.trans (Finset.subset_univ _), (e d).2.2⟩⟩
  change q' (embBelow₁ _) = p (e.symm (cast ⟨(e d).1, _⟩)) at h2
  rw [show cast ⟨(e d).1, ⟨(e d).2.1.trans (Finset.subset_univ _), (e d).2.2⟩⟩ = e d from
    Subtype.ext rfl, e.symm_apply_apply] at h2
  have e4 : (⟨ret₂ d.1, ret₂_le_univ hC h d⟩ : C₂.below (Finset.univ, 3)) =
      embBelow₁ ⟨(e d).1, ⟨(e d).2.1.trans (Finset.subset_univ _), (e d).2.2⟩⟩ :=
    Subtype.ext (hret d)
  exact (congrArg q' e4).trans h2

/-- **The glued domain from the three-point obligations.** -/
noncomputable def semSchemeGlue' (HA : FaceExtA') (HB : FaceExtB') : SemScheme 4 :=
  semSchemeGlue (faceExtA_of HA) (faceExtB_of HB)

end Endpoint


/-- **Claim 1 — matching shared faces**: the two inputs' top rows agree at every proper cell
(both read the common proper row, under caps above it), in particular on the shared pair. -/
theorem shared_face_agree (c : Prop3) :
    family₀.rowX (.inr (.inr (.inr ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)))
        (.inl c) =
      family₁.rowX (.inr (.inr (.inr ⟨b₁, Finset.mem_singleton_self _⟩))) (.inl c) := by
  rw [Family.rowX_a_inl, Family.rowX_a_inl]
  change min (t₀.F c) γ₀ = min (t₁.F c) γ₁
  rw [min_eq_left (show t₀.F c ≤ γ₀ from t₀.F_le c), min_eq_left (show t₁.F c ≤ γ₁ from t₁.F_le c)]
  rfl


end VaughtConjecture.Knight
