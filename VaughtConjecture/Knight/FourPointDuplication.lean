/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExtendOneWith
public import VaughtConjecture.Knight.PullbackSemantics
public import VaughtConjecture.Knight.AssembledReferenceContext
public import VaughtConjecture.Knight.RowReadback

/-! # The four-point duplication context over the assembled scheme

A **legal extension of the assembled three-point domain** by one fresh point, with literal old-face
preservation and universal fresh-cell readback.

**The construction.**  The fourth point is a *copy* of the point `0`: the folding
`fold : Fin 4 → Fin 3` sends `3 ↦ 0` and fixes the rest.  The plan `plan₄` consists of the old
faces (pushed along `castSucc`), their copies under the fold (`{3}`, `{1,3}`, `{1,2,3}`), and the
domain — a support plan with pivots `3, 0` (`isPlan₄`, and the face equation `hface₄`, by
`decide`).  The new cells are one copy of every old cell for every new face whose fold is the
cell's scope (`Copy`), plus one mute cell at `(univ, 4)`.  The retraction `ret` sends a copy to
its original, and the rows are the old rows pulled back
(`rows₄ := family₀.rows.pullback ret mute₄ …`, `Knight/PullbackSemantics.lean`).

**Legality.**  `D₄` is complete (`D₄_complete`); `rows₄` is coded and consistent
(`rows₄_isCoded`, `rows₄_isConsistent`, by the pullback theorems with the section property
`hsect₄`).  Bountifulness: at proper-scope pairs it transports from `semScheme₀` — the retraction is
a bijection of lower sets on every proper face, old or copied (`eProper`, `bountiful₄_proper`); at
full-scope pairs it is `bountiful_full_scope`; the proper-to-full cases (`ProperToFull₄`) reduce,
through restriction to the old cells (`restrict_old_respects`) and the pullback of the old extension
(`pullback_of_sect`), to old bountifulness plus **rigidity** (`Rigidity₄`,
`properToFull₄_of_rigidity`; the grade-four case by `bountiful_full_scope`).  Rigidity —
**uniqueness of extension over a fixed old labelling**: every respecting labelling of a full-scope
lower set of grade at most three agrees at a cell and at its retraction — is the controller-probe
lemma applied to a copy and its original (`rigidity₄`).  Hence `fourPointDomain : SemScheme 4`.

**Readback.**  The old labelled type `p₀ : S (ω·2) 3` carries the row of the capped cell with cap
`ω + 4`; `extendsDomain_fourPoint` is literal face readback (rows included); the coface
`fourPointCoface` is the old labelling pulled back (`isCoface_fourPoint`).  The inherited reference
data `R₄` keep the old cap and trigger (grade three, `ω + 4`), threshold `3`, the old singleton at
`ω + 1` as representative, and one fresh request at the copied singleton `s3copy` (block `ω`,
offset `1`); every controller at `(univ, 3)` is correct because both full copies read the old row at
the singleton (`fourPointInputs`).  `readback_fourPoint` is Lemma 10.1.1's readback: every coface
with the `⊥`-pattern of the coface reads `ω + 1` at the fresh cell; `fourPointCoface_readback`
realizes it with the trigger active.

**Scope.**  This is a legal *duplication* extension.  It forces the copied cell's label to equal
its original's; it does not support independently prescribed fresh labels, arbitrary requests, or
realization inside two fixed models (the two-context experiment).  Construction-private (not
root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

section FourPoint

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-- The folding of the fourth point onto the first. -/
def fold : Fin 4 → Fin 3
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 0

theorem fold_castSucc (i : Fin 3) : fold (Fin.castSuccEmb i) = i := by revert i; decide

theorem image_fold_image_castSucc (B : Finset (Fin 3)) :
    (B.image Fin.castSuccEmb).image fold = B := by
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := B)]
  exact Finset.image_congr fun i _ => fold_castSucc i

/-- The two-copy plan on `Fin 4`. -/
def plan₄ : Finset (Finset (Fin 4)) :=
  {∅, {0}, {1}, {2}, {3}, {0, 1}, {1, 2}, {1, 3}, {0, 1, 2}, {1, 2, 3}, Finset.univ}

/-- The plan on a pair `{x, y}` (the full powerset). -/
theorem isPlan_pair (x y : Fin 4) (hxy : x ≠ y) :
    Plan.IsPlan ({x, y} : Finset (Fin 4)) {∅, {x}, {y}, {x, y}} := by
  refine Plan.IsPlan.step (a := x) (b := y) (Q := {∅, {y}}) (R := {∅, {x}})
    (by simp) (by simp) hxy ?_ ?_ ?_ ?_ ?_
  · rw [Finset.erase_insert (by simpa using hxy)]; exact Plan.IsPlan.singleton y
  · rw [Finset.pair_comm, Finset.erase_insert (by simpa using hxy.symm)]
    exact Plan.IsPlan.singleton x
  · rw [Finset.erase_insert (by simpa using hxy), Finset.erase_singleton]; simp
  · rw [Finset.erase_insert (by simpa using hxy), Finset.erase_singleton]
    ext B; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_powerset, Finset.subset_empty]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact ⟨Or.inl h1, h2⟩
      · exact absurd (h1 ▸ h2) (by simp)
    · rintro ⟨h1 | h1, h2⟩
      · exact ⟨Or.inl h1, h2⟩
      · exact absurd (h1 ▸ h2) (by simp)
  · ext B
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    tauto

theorem isPlan₄ : Plan.IsPlan (Finset.univ : Finset (Fin 4)) plan₄ := by
  have hR : Plan.IsPlan ({1, 2, 3} : Finset (Fin 4))
      {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {1, 2, 3}} := by
    refine Plan.IsPlan.step (a := 3) (b := 2) (Q := {∅, {1}, {2}, {1, 2}})
      (R := {∅, {1}, {3}, {1, 3}})
      (by decide) (by decide) (by decide) ?_ ?_ (by decide) (by decide) (by decide)
    · rw [show ({1, 2, 3} : Finset (Fin 4)).erase 3 = {1, 2} by decide]
      exact isPlan_pair 1 2 (by decide)
    · rw [show ({1, 2, 3} : Finset (Fin 4)).erase 2 = {1, 3} by decide]
      exact isPlan_pair 1 3 (by decide)
  have hQ : Plan.IsPlan ({0, 1, 2} : Finset (Fin 4))
      {∅, {0}, {1}, {2}, {0, 1}, {1, 2}, {0, 1, 2}} := by
    refine Plan.IsPlan.step (a := 0) (b := 2) (Q := {∅, {1}, {2}, {1, 2}})
      (R := {∅, {0}, {1}, {0, 1}})
      (by decide) (by decide) (by decide) ?_ ?_ (by decide) (by decide) (by decide)
    · rw [show ({0, 1, 2} : Finset (Fin 4)).erase 0 = {1, 2} by decide]
      exact isPlan_pair 1 2 (by decide)
    · rw [show ({0, 1, 2} : Finset (Fin 4)).erase 2 = {0, 1} by decide]
      exact isPlan_pair 0 1 (by decide)
  refine Plan.IsPlan.step (a := 3) (b := 0) (Q := {∅, {0}, {1}, {2}, {0, 1}, {1, 2}, {0, 1, 2}})
    (R := {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {1, 2, 3}}) (by decide) (by decide) (by decide) ?_ ?_
    (by decide) (by decide) (by decide)
  · rw [show (Finset.univ : Finset (Fin 4)).erase 3 = {0, 1, 2} by decide]; exact hQ
  · rw [show (Finset.univ : Finset (Fin 4)).erase 0 = {1, 2, 3} by decide]; exact hR

/-- The face equation of the plan: a face of `Fin 3` is visible iff its push-forward is. -/
theorem hface₄ : ∀ B : Finset (Fin 3), B.image Fin.castSuccEmb ∈ plan₄ ↔ B ∈ Prop3.plan := by
  decide

/-- The new faces: the copies of the old faces, and the domain. -/
def newFaces : Finset (Finset (Fin 4)) := {{3}, {1, 3}, {1, 2, 3}, Finset.univ}

theorem newFaces_subset : ∀ B ∈ newFaces, B ∈ plan₄ := by decide
theorem last_mem_newFaces : ∀ B ∈ newFaces, (3 : Fin 4) ∈ B := by decide
theorem mem_newFaces_of_last : ∀ B ∈ plan₄, (3 : Fin 4) ∈ B → B ∈ newFaces := by decide
theorem fold_newFaces_mem : ∀ B ∈ newFaces, B.image fold ∈ Prop3.plan := by decide
theorem card_fold_newFaces : ∀ B ∈ newFaces, B ≠ Finset.univ → (B.image fold).card = B.card := by
  decide
theorem card_fold_univ : ((Finset.univ : Finset (Fin 4)).image fold).card = 3 := by decide

/-- The old scheme. -/
noncomputable abbrev C₀ : CellScheme (ι := Fin 3) Finset.univ := family₀.scheme

/-- **The copies**: an old cell together with a new face whose fold is its scope. -/
abbrev Copy : Type := {p : ↥newFaces × Cell C₀ // C₀.scope p.2 = (p.1.1).image fold}

/-- The new cells: the copies and the mute top cell. -/
abbrev New : Type := Copy ⊕ Unit

noncomputable def newCell₄ : New → Finset (Fin 4) × ℕ
  | .inl p => (p.1.1.1, C₀.grade p.1.2)
  | .inr _ => (Finset.univ, 4)

theorem newCell₄_mem (x : New) : newCell₄ x ∈ Plan.gradedPlan plan₄ := by
  rcases x with p | _
  · refine Plan.mem_gradedPlan.mpr ⟨newFaces_subset _ p.1.1.2, C₀.grade_pos _, ?_⟩
    change C₀.grade p.1.2 ≤ (p.1.1.1).card
    calc C₀.grade p.1.2 ≤ (C₀.scope p.1.2).card := C₀.grade_le_card_scope _
      _ = ((p.1.1.1).image fold).card := by rw [p.2]
      _ ≤ (p.1.1.1).card := Finset.card_image_le
  · change (Finset.univ, 4) ∈ _
    exact Plan.mem_gradedPlan.mpr ⟨by decide, by decide, by decide⟩

theorem newCell₄_last (x : New) : Fin.last 3 ∈ (newCell₄ x).1 := by
  rcases x with p | _
  · exact last_mem_newFaces _ p.1.1.2
  · exact Finset.mem_univ _

/-- **The four-point scheme.** -/
noncomputable abbrev D₄ : CellScheme (ι := Fin 4) Finset.univ :=
  CellScheme.extendOneWith C₀ plan₄ isPlan₄ hface₄ newCell₄ newCell₄_mem

theorem D₄_complete : D₄.IsComplete := by
  refine CellScheme.IsComplete.extendOneWith family₀.scheme_isComplete ?_
  rintro ⟨B, j⟩ hBJ hlast
  obtain ⟨hB, hj0, hjB⟩ := Plan.mem_gradedPlan.mp hBJ
  dsimp only at hB hj0 hjB hlast
  have hBn : B ∈ newFaces := mem_newFaces_of_last B hB hlast
  by_cases htop : B = Finset.univ ∧ j = 4
  · exact ⟨.inr (), by rw [htop.1, htop.2]; rfl⟩
  · have hj3 : j ≤ (B.image fold).card := by
      by_cases hBu : B = Finset.univ
      · subst hBu
        rw [card_fold_univ]
        have : j ≠ 4 := fun h => htop ⟨rfl, h⟩
        rw [Finset.card_univ, Fintype.card_fin] at hjB
        omega
      · rw [card_fold_newFaces B hBn hBu]; exact hjB
    obtain ⟨x, hx⟩ := family₀.scheme_isComplete (B.image fold, j)
      (Plan.mem_gradedPlan.mpr ⟨fold_newFaces_mem B hBn, hj0, hj3⟩)
    refine ⟨.inl ⟨(⟨B, hBn⟩, x), congrArg Prod.fst hx⟩, ?_⟩
    change (B, C₀.grade x) = (B, j)
    rw [show C₀.grade x = j from congrArg Prod.snd hx]

/-- The old cell with cap `ω + 4`, the target of the mute cell under the (irrelevant) retraction. -/
noncomputable def a₂cell : Cell C₀ := family₀.e (.inr (.inr (.inr a₂c)))

/-- The retraction on new cells. -/
noncomputable def retNew : New → Cell C₀
  | .inl p => p.1.2
  | .inr _ => a₂cell

/-- **The retraction**: old cells to themselves, copies to their originals. -/
noncomputable def ret : Cell D₄ → Cell C₀ :=
  Fin.addCases (fun i => i) (fun j => retNew ((Fintype.equivFin New).symm j))

theorem ret_castAdd (i : Cell C₀) : ret (Fin.castAdd (Fintype.card New) i) = i := by
  unfold ret; exact Fin.addCases_left i

theorem ret_natAdd (j : Fin (Fintype.card New)) :
    ret (Fin.natAdd C₀.card j) = retNew ((Fintype.equivFin New).symm j) := by
  unfold ret; exact Fin.addCases_right j

/-- The mute cell: the graded index `(univ, 4)`. -/
noncomputable def mute₄ (d : Cell D₄) : Prop := D₄.cell d = (Finset.univ, 4)

noncomputable instance : DecidablePred mute₄ := fun d => inferInstanceAs (Decidable (D₄.cell d = _))

theorem D₄_cell_castAdd (i : Cell C₀) :
    D₄.cell (Fin.castAdd (Fintype.card New) i) = pushGraded Fin.castSuccEmb (C₀.cell i) :=
  CellScheme.extendOneWith_cell_castAdd i

theorem D₄_cell_natAdd (j : Fin (Fintype.card New)) :
    D₄.cell (Fin.natAdd C₀.card j) = newCell₄ ((Fintype.equivFin New).symm j) :=
  CellScheme.extendOneWith_cell_natAdd j

theorem D₄_scope_castAdd (i : Cell C₀) :
    D₄.scope (Fin.castAdd (Fintype.card New) i) = (C₀.scope i).image Fin.castSuccEmb :=
  CellScheme.extendOneWith_scope_castAdd i
theorem D₄_grade_castAdd (i : Cell C₀) : D₄.grade (Fin.castAdd (Fintype.card New) i) = C₀.grade i :=
  CellScheme.extendOneWith_grade_castAdd i
theorem D₄_scope_natAdd (j : Fin (Fintype.card New)) :
    D₄.scope (Fin.natAdd C₀.card j) = (newCell₄ ((Fintype.equivFin New).symm j)).1 :=
  congrArg Prod.fst (D₄_cell_natAdd j)
theorem D₄_grade_natAdd (j : Fin (Fintype.card New)) :
    D₄.grade (Fin.natAdd C₀.card j) = (newCell₄ ((Fintype.equivFin New).symm j)).2 :=
  congrArg Prod.snd (D₄_cell_natAdd j)

/-- The scope of the retraction of a non-mute cell is the fold of its scope. -/
theorem scope_ret (x : Cell D₄) (hx : ¬ mute₄ x) : C₀.scope (ret x) = (D₄.scope x).image fold := by
  induction x using Fin.addCases with
  | left i =>
    rw [ret_castAdd]
    change C₀.scope i = ((D₄.cell (Fin.castAdd _ i)).1).image fold
    rw [D₄_cell_castAdd]
    exact (image_fold_image_castSucc _).symm
  | right j =>
    rw [ret_natAdd]
    change C₀.scope (retNew _) = ((D₄.cell (Fin.natAdd _ j)).1).image fold
    rw [D₄_cell_natAdd]
    rcases hy : (Fintype.equivFin New).symm j with p | u
    · exact p.2
    · exfalso; apply hx
      change D₄.cell (Fin.natAdd _ j) = _
      rw [D₄_cell_natAdd, hy]; rfl

/-- The grade of the retraction of a non-mute cell is its grade. -/
theorem grade_ret (x : Cell D₄) (hx : ¬ mute₄ x) : D₄.grade x = C₀.grade (ret x) := by
  induction x using Fin.addCases with
  | left i =>
    rw [ret_castAdd]
    exact CellScheme.extendOneWith_grade_castAdd i
  | right j =>
    rw [ret_natAdd]
    change (D₄.cell (Fin.natAdd _ j)).2 = _
    rw [D₄_cell_natAdd]
    rcases hy : (Fintype.equivFin New).symm j with p | u
    · rfl
    · exfalso; apply hx
      change D₄.cell (Fin.natAdd _ j) = _
      rw [D₄_cell_natAdd, hy]; rfl

theorem hscope₄ (x y : Cell D₄) (hx : ¬ mute₄ x) (hy : ¬ mute₄ y) (h : D₄.scope x ⊆ D₄.scope y) :
    C₀.scope (ret x) ⊆ C₀.scope (ret y) := by
  rw [scope_ret x hx, scope_ret y hy]
  exact Finset.image_subset_image h

/-- Mute cells lie below no non-mute cell. -/
theorem hmute_below₄ (x d : Cell D₄) (hx : ¬ mute₄ x) (h : GradedLe (D₄.cell d) (D₄.cell x)) :
    ¬ mute₄ d := by
  intro hd
  apply hx
  change D₄.cell d = (Finset.univ, 4) at hd
  have hs : Finset.univ ⊆ D₄.scope x := by
    have := h.1; rw [hd] at this; exact this
  have hg : 4 ≤ D₄.grade x := by
    have := h.2; rw [hd] at this; exact this
  have hcard : D₄.grade x ≤ 4 := by
    have := D₄.grade_le_card_scope x
    have h4 : (D₄.scope x).card ≤ 4 := (Finset.card_le_univ _).trans (by simp)
    omega
  change D₄.cell x = (Finset.univ, 4)
  exact Prod.ext (Finset.univ_subset_iff.mp hs) (by change D₄.grade x = 4; omega)

/-- **Sections over graded indices**: an old cell of the graded index of a copy's original has a
copy at the graded index of that copy. -/
theorem hsect₄ (Xi₀ : Cell D₄) (Xi' : Cell C₀) (hXi₀ : ¬ mute₄ Xi₀)
    (h : C₀.cell Xi' = C₀.cell (ret Xi₀)) :
    ∃ Xi : Cell D₄, D₄.cell Xi = D₄.cell Xi₀ ∧ ret Xi = Xi' := by
  induction Xi₀ using Fin.addCases with
  | left i =>
    rw [ret_castAdd] at h
    refine ⟨Fin.castAdd _ Xi', ?_, ret_castAdd _⟩
    rw [D₄_cell_castAdd, D₄_cell_castAdd, h]
  | right j =>
    rw [ret_natAdd] at h
    rcases hy : (Fintype.equivFin New).symm j with p | u
    · rw [hy] at h
      change C₀.cell Xi' = C₀.cell p.1.2 at h
      have hs : C₀.scope Xi' = (p.1.1.1).image fold := by
        rw [← p.2]; exact congrArg Prod.fst h
      refine ⟨Fin.natAdd C₀.card ((Fintype.equivFin New) (.inl ⟨(p.1.1, Xi'), hs⟩)), ?_, ?_⟩
      · rw [D₄_cell_natAdd, D₄_cell_natAdd, Equiv.symm_apply_apply, hy]
        change (p.1.1.1, C₀.grade Xi') = (p.1.1.1, C₀.grade p.1.2)
        rw [show C₀.grade Xi' = C₀.grade p.1.2 from congrArg Prod.snd h]
      · rw [ret_natAdd, Equiv.symm_apply_apply]; rfl
    · exfalso; apply hXi₀
      change D₄.cell (Fin.natAdd _ j) = _
      rw [D₄_cell_natAdd, hy]; rfl

/-- **The rows of the four-point scheme**: the old rows pulled back along the retraction, the top
cell mute. -/
noncomputable def rows₄ : Semantics D₄ :=
  family₀.rows.pullback ret mute₄ grade_ret hscope₄ hmute_below₄

theorem rows₄_E_of_not_mute {x : Cell D₄} (hx : ¬ mute₄ x) (d : D₄.below (D₄.cell x)) :
    rows₄.E x d = family₀.rows.E (ret x) (retBelow ret mute₄ grade_ret hscope₄ hmute_below₄ hx d) :=
  Semantics.pullback_E_of_not_mute hx d

theorem rows₄_E_of_mute {x : Cell D₄} (hx : mute₄ x) (d : D₄.below (D₄.cell x)) :
    rows₄.E x d = ⊥ :=
  Semantics.pullback_E_of_mute hx d

theorem rows₄_isCoded : rows₄.IsCoded := Semantics.pullback_isCoded family₀.rows_isCoded

theorem rows₄_isConsistent : rows₄.IsConsistent :=
  Semantics.pullback_isConsistent family₀.rows_isConsistent hsect₄


/-! ### Bountifulness: proper-scope pairs transport, full-scope pairs are general -/

/-- Decidable facts about the plan and the fold. -/
theorem copy_no_zero : ∀ B ∈ plan₄, (3 : Fin 4) ∈ B → B ≠ Finset.univ → (0 : Fin 4) ∉ B := by decide
theorem fold_injOn : ∀ B ∈ plan₄, B ≠ Finset.univ →
    ∀ x ∈ B, ∀ y ∈ B, fold x = fold y → x = y := by decide
theorem fold_mem_plan : ∀ B ∈ plan₄, B ≠ Finset.univ → B.image fold ∈ Prop3.plan := by decide
theorem card_fold_proper : ∀ B ∈ plan₄, B ≠ Finset.univ → (B.image fold).card = B.card := by decide
theorem newFaces_fold_inj : ∀ B' ∈ newFaces, ∀ B'' ∈ newFaces, B' ≠ Finset.univ →
    B'' ≠ Finset.univ → B'.image fold = B''.image fold → B' = B'' := by decide
theorem castSucc_sub_old : ∀ B ∈ plan₄, (3 : Fin 4) ∉ B →
    ∀ S : Finset (Fin 3), S ⊆ B.image fold → S.image Fin.castSuccEmb ⊆ B := by decide
theorem castSucc_sub_copy : ∀ B ∈ plan₄, (3 : Fin 4) ∈ B → B ≠ Finset.univ →
    ∀ S : Finset (Fin 3), S ⊆ B.image fold → (0 : Fin 3) ∉ S → S.image Fin.castSuccEmb ⊆ B := by
  decide

/-- The unfolding of an old face containing `0` into the copy containing `3`. -/
def unfold (S : Finset (Fin 3)) : Finset (Fin 4) :=
  S.image fun i => if i = 0 then 3 else Fin.castSuccEmb i

theorem unfold_spec : ∀ B ∈ plan₄, (3 : Fin 4) ∈ B → B ≠ Finset.univ →
    ∀ S ∈ Prop3.plan, S ⊆ B.image fold → (0 : Fin 3) ∈ S →
      unfold S ∈ newFaces ∧ unfold S ⊆ B ∧ (unfold S).image fold = S := by decide

/-- Cells below a proper graded pair are non-mute. -/
theorem not_mute_of_proper {B : Finset (Fin 4)} {j : ℕ} (hB : B ≠ Finset.univ)
    (a : D₄.below (B, j)) : ¬ mute₄ a.1 := by
  intro h
  change D₄.cell a.1 = (Finset.univ, 4) at h
  have := a.2.1
  rw [h] at this
  exact hB (Finset.univ_subset_iff.mp this)

/-- Cells below a full-scope pair of grade at most three are non-mute. -/
theorem not_mute_of_proper' {j : ℕ} (hj : j ≤ 3) (a : D₄.below (Finset.univ, j)) :
    ¬ mute₄ a.1 := by
  intro h
  change D₄.cell a.1 = (Finset.univ, 4) at h
  have := a.2.2
  rw [h] at this
  change 4 ≤ j at this
  omega

/-- The retraction maps the lower set of a proper pair into the lower set of its fold. -/
theorem ret_mem_below {B : Finset (Fin 4)} {j : ℕ} (hB : B ≠ Finset.univ) (a : D₄.below (B, j)) :
    GradedLe (C₀.cell (ret a.1)) (B.image fold, j) := by
  have hnm := not_mute_of_proper hB a
  refine ⟨?_, ?_⟩
  · change C₀.scope (ret a.1) ⊆ B.image fold
    rw [scope_ret _ hnm]
    exact Finset.image_subset_image a.2.1
  · change C₀.grade (ret a.1) ≤ j
    rw [← grade_ret _ hnm]; exact a.2.2

/-- The retraction reflects the graded order on the lower set of a proper pair. -/
theorem hle_proper {B : Finset (Fin 4)} {j : ℕ} (hBp : B ∈ plan₄) (hB : B ≠ Finset.univ)
    (a b : D₄.below (B, j)) :
    GradedLe (D₄.cell a.1) (D₄.cell b.1) ↔ GradedLe (C₀.cell (ret a.1)) (C₀.cell (ret b.1)) := by
  have hna := not_mute_of_proper hB a
  have hnb := not_mute_of_proper hB b
  constructor
  · exact gradedLe_ret ret mute₄ grade_ret hscope₄ hmute_below₄ hnb
  · rintro ⟨hs, hg⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      have hs' : C₀.scope (ret a.1) ⊆ C₀.scope (ret b.1) := hs
      rw [scope_ret _ hna, scope_ret _ hnb] at hs'
      have hx' : fold x ∈ (D₄.scope b.1).image fold :=
        hs' (Finset.mem_image_of_mem fold (hx : x ∈ D₄.scope a.1))
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx'
      have := fold_injOn B hBp hB y (b.2.1 hy) x (a.2.1 hx) hxy
      rw [← this]; exact hy
    · change D₄.grade a.1 ≤ D₄.grade b.1
      rw [grade_ret _ hna, grade_ret _ hnb]; exact hg

/-- The retraction is injective on the lower set of a proper pair. -/
theorem ret_inj_proper {B : Finset (Fin 4)} {j : ℕ} (hBp : B ∈ plan₄) (hB : B ≠ Finset.univ)
    (a b : D₄.below (B, j)) (h : ret a.1 = ret b.1) : a = b := by
  apply Subtype.ext
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  change ret a = ret b at h
  change a = b
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left i' =>
      rw [ret_castAdd, ret_castAdd] at h; rw [h]
    | right j' =>
      exfalso
      rw [ret_castAdd, ret_natAdd] at h
      rcases hy : (Fintype.equivFin New).symm j' with p | u
      · rw [hy] at h
        change i = p.1.2 at h
        -- the scope of the copy's original contains `0`, so the old cell's scope contains `0 ∈ B`
        have h0 : (0 : Fin 3) ∈ C₀.scope i := by
          rw [h, p.2]
          exact Finset.mem_image_of_mem fold (last_mem_newFaces _ p.1.1.2)
        have hsub : D₄.scope (Fin.castAdd _ i) ⊆ B := ha.1
        rw [D₄_scope_castAdd] at hsub
        have h0' : (0 : Fin 4) ∈ B := hsub (Finset.mem_image_of_mem _ h0)
        have h3 : (3 : Fin 4) ∈ B := by
          have := hb.1
          change D₄.scope (Fin.natAdd _ j') ⊆ B at this
          exact this (CellScheme.last_mem_extendOneWith_scope_natAdd newCell₄_last j')
        exact copy_no_zero B hBp h3 hB h0'
      · exfalso
        apply not_mute_of_proper hB ⟨Fin.natAdd _ j', hb⟩
        change D₄.cell (Fin.natAdd _ j') = _
        rw [D₄_cell_natAdd, hy]; rfl
  | right j' =>
    induction b using Fin.addCases with
    | left i' =>
      exfalso
      rw [ret_natAdd, ret_castAdd] at h
      rcases hy : (Fintype.equivFin New).symm j' with p | u
      · rw [hy] at h
        change p.1.2 = i' at h
        have h0 : (0 : Fin 3) ∈ C₀.scope i' := by
          rw [← h, p.2]
          exact Finset.mem_image_of_mem fold (last_mem_newFaces _ p.1.1.2)
        have hsub : D₄.scope (Fin.castAdd _ i') ⊆ B := hb.1
        rw [D₄_scope_castAdd] at hsub
        have h0' : (0 : Fin 4) ∈ B := hsub (Finset.mem_image_of_mem _ h0)
        have h3 : (3 : Fin 4) ∈ B := by
          have := ha.1
          change D₄.scope (Fin.natAdd _ j') ⊆ B at this
          exact this (CellScheme.last_mem_extendOneWith_scope_natAdd newCell₄_last j')
        exact copy_no_zero B hBp h3 hB h0'
      · exfalso
        apply not_mute_of_proper hB ⟨Fin.natAdd _ j', ha⟩
        change D₄.cell (Fin.natAdd _ j') = _
        rw [D₄_cell_natAdd, hy]; rfl
    | right j'' =>
      rw [ret_natAdd, ret_natAdd] at h
      rcases hy : (Fintype.equivFin New).symm j' with p | u
      · rcases hy' : (Fintype.equivFin New).symm j'' with p' | u'
        · rw [hy, hy'] at h
          change p.1.2 = p'.1.2 at h
          -- the two faces have the same fold, hence coincide
          have hf : p.1.1.1.image fold = p'.1.1.1.image fold := by rw [← p.2, ← p'.2, h]
          have hp3 : (3 : Fin 4) ∈ B := by
            have := ha.1
            change D₄.scope (Fin.natAdd _ j') ⊆ B at this
            exact this (CellScheme.last_mem_extendOneWith_scope_natAdd newCell₄_last j')
          have hBu : p.1.1.1 ≠ Finset.univ := by
            intro hu
            apply hB
            have := ha.1
            change D₄.scope (Fin.natAdd _ j') ⊆ B at this
            rw [D₄_scope_natAdd, hy] at this
            change p.1.1.1 ⊆ B at this
            rw [hu] at this
            exact Finset.univ_subset_iff.mp this
          have hBu' : p'.1.1.1 ≠ Finset.univ := by
            intro hu
            apply hB
            have := hb.1
            change D₄.scope (Fin.natAdd _ j'') ⊆ B at this
            rw [D₄_scope_natAdd, hy'] at this
            change p'.1.1.1 ⊆ B at this
            rw [hu] at this
            exact Finset.univ_subset_iff.mp this
          have hfaces : p.1.1.1 = p'.1.1.1 :=
            newFaces_fold_inj _ p.1.1.2 _ p'.1.1.2 hBu hBu' hf
          have hpp : p = p' := by
            apply Subtype.ext
            exact Prod.ext (Subtype.ext hfaces) h
          have : j' = j'' := by
            apply (Fintype.equivFin New).symm.injective
            rw [hy, hy', hpp]
          rw [this]
        · exfalso
          apply not_mute_of_proper hB ⟨Fin.natAdd _ j'', hb⟩
          change D₄.cell (Fin.natAdd _ j'') = _
          rw [D₄_cell_natAdd, hy']; rfl
      · exfalso
        apply not_mute_of_proper hB ⟨Fin.natAdd _ j', ha⟩
        change D₄.cell (Fin.natAdd _ j') = _
        rw [D₄_cell_natAdd, hy]; rfl

/-- The retraction is surjective from the lower set of a proper pair onto that of its fold. -/
theorem ret_surj_proper {B : Finset (Fin 4)} {j : ℕ} (hBp : B ∈ plan₄) (hB : B ≠ Finset.univ)
    (y : C₀.below (B.image fold, j)) : ∃ a : D₄.below (B, j), ret a.1 = y.1 := by
  by_cases h3 : (3 : Fin 4) ∈ B
  · by_cases h0 : (0 : Fin 3) ∈ C₀.scope y.1
    · -- the copy of `y` in the unfolded face
      obtain ⟨hnf, hsub, hfold⟩ := unfold_spec B hBp h3 hB _ (C₀.scope_mem_plan y.1) y.2.1 h0
      let p : Copy := ⟨(⟨unfold (C₀.scope y.1), hnf⟩, y.1), hfold.symm⟩
      refine ⟨⟨Fin.natAdd C₀.card ((Fintype.equivFin New) (.inl p)), ?_⟩, ?_⟩
      · refine ⟨?_, ?_⟩
        · change D₄.scope _ ⊆ B
          rw [D₄_scope_natAdd, Equiv.symm_apply_apply]
          exact hsub
        · change D₄.grade _ ≤ j
          rw [D₄_grade_natAdd, Equiv.symm_apply_apply]
          exact y.2.2
      · rw [ret_natAdd, Equiv.symm_apply_apply]; rfl
    · refine ⟨⟨Fin.castAdd _ y.1, ?_⟩, ret_castAdd _⟩
      refine ⟨?_, ?_⟩
      · change D₄.scope _ ⊆ B
        rw [D₄_scope_castAdd]
        exact castSucc_sub_copy B hBp h3 hB _ y.2.1 h0
      · change D₄.grade _ ≤ j
        rw [D₄_grade_castAdd]; exact y.2.2
  · refine ⟨⟨Fin.castAdd _ y.1, ?_⟩, ret_castAdd _⟩
    refine ⟨?_, ?_⟩
    · change D₄.scope _ ⊆ B
      rw [D₄_scope_castAdd]
      exact castSucc_sub_old B hBp h3 _ y.2.1
    · change D₄.grade _ ≤ j
      rw [D₄_grade_castAdd]; exact y.2.2

/-- **The bijection of lower sets** at a proper pair. -/
noncomputable def eProper {B : Finset (Fin 4)} {j : ℕ} (hBp : B ∈ plan₄) (hB : B ≠ Finset.univ) :
    D₄.below (B, j) ≃ C₀.below (B.image fold, j) :=
  Equiv.ofBijective (fun a => ⟨ret a.1, ret_mem_below hB a⟩)
    ⟨fun a b h => ret_inj_proper hBp hB a b (congrArg Subtype.val h),
     fun y => by
      obtain ⟨a, ha⟩ := ret_surj_proper hBp hB y
      exact ⟨a, Subtype.ext ha⟩⟩

theorem eProper_val {B : Finset (Fin 4)} {j : ℕ} (hBp : B ∈ plan₄) (hB : B ≠ Finset.univ)
    (a : D₄.below (B, j)) : (eProper hBp hB a).1 = ret a.1 := rfl

/-- **Bountifulness at proper-scope pairs**, transported from `semScheme₀`. -/
theorem bountiful₄_proper (CI BJ : Finset (Fin 4) × ℕ) (hCI : CI ∈ Plan.gradedPlan plan₄)
    (hBJ : BJ ∈ Plan.gradedPlan plan₄) (h : GradedLe CI BJ) (hne : CI ≠ BJ)
    (hB : BJ.1 ≠ Finset.univ)
    (p : D₄.below CI → ExtOrd) (q : D₄.below BJ → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow rows₄ CI p) (hq : RespectsSemanticsBelow rows₄ BJ q)
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ)
    (hagree : ∀ d : D₄.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D₄.below BJ → ExtOrd, RespectsSemanticsBelow rows₄ BJ q' ∧
      (∀ d : D₄.below BJ, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D₄.below CI, q' (CellScheme.below.mono h d) = p d) := by
  obtain ⟨B, j⟩ := BJ
  obtain ⟨C, i⟩ := CI
  dsimp only at hB
  have hBp : B ∈ plan₄ := (Plan.mem_gradedPlan.mp hBJ).1
  have hCp : C ∈ plan₄ := (Plan.mem_gradedPlan.mp hCI).1
  have hC : C ≠ Finset.univ := fun e => hB (Finset.univ_subset_iff.mp (e ▸ h.1))
  have hfoldC : (C.image fold, i) ∈ Plan.gradedPlan Prop3.plan := by
    obtain ⟨-, hi0, hiC⟩ := Plan.mem_gradedPlan.mp hCI
    exact Plan.mem_gradedPlan.mpr ⟨fold_mem_plan C hCp hC, hi0, by
      change i ≤ (C.image fold).card; rw [card_fold_proper C hCp hC]; exact hiC⟩
  have hfoldB : (B.image fold, j) ∈ Plan.gradedPlan Prop3.plan := by
    obtain ⟨-, hj0, hjB⟩ := Plan.mem_gradedPlan.mp hBJ
    exact Plan.mem_gradedPlan.mpr ⟨fold_mem_plan B hBp hB, hj0, by
      change j ≤ (B.image fold).card; rw [card_fold_proper B hBp hB]; exact hjB⟩
  have h' : GradedLe (C.image fold, i) (B.image fold, j) :=
    ⟨Finset.image_subset_image h.1, h.2⟩
  have hne' : (C.image fold, i) ≠ (B.image fold, j) := by
    intro e
    apply hne
    have hi : i = j := congrArg Prod.snd e
    have hCB : C = B := by
      apply Finset.Subset.antisymm h.1
      intro x hx
      have hx' : fold x ∈ C.image fold := by
        rw [show C.image fold = B.image fold from congrArg Prod.fst e]
        exact Finset.mem_image_of_mem fold hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx'
      rw [← fold_injOn B hBp hB y (h.1 hy) x hx hxy]; exact hy
    rw [hi, hCB]
  exact bountiful_pullback_of_bij (sem := family₀.rows) h h' (not_mute_of_proper hB)
    (not_mute_of_proper hC) (eProper hBp hB) (eProper_val hBp hB) (hle_proper hBp hB)
    (eProper hCp hC) (eProper_val hCp hC) (hle_proper hCp hC)
    (semScheme₀.bountiful _ _ hfoldC hfoldB h' hne') rfl p q γ hp hq hγ hagree

/-- **The remaining obligation**: bountifulness from a proper-scope pair to a full-scope pair of
the four-point scheme (the scope-changing cases). -/
def ProperToFull₄ : Prop :=
  ∀ (CI : Finset (Fin 4) × ℕ) (j : ℕ), CI ∈ Plan.gradedPlan plan₄ → CI.1 ≠ Finset.univ →
    (Finset.univ, j) ∈ Plan.gradedPlan plan₄ → (h : GradedLe CI (Finset.univ, j)) →
    ∀ (p : D₄.below CI → ExtOrd) (q : D₄.below (Finset.univ, j) → ExtOrd) (γ : ExtOrd),
      RespectsSemanticsBelow rows₄ CI p → RespectsSemanticsBelow rows₄ (Finset.univ, j) q →
      extVisibilityReplace γ j j = γ →
      (∀ d : D₄.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) →
      ∃ q' : D₄.below (Finset.univ, j) → ExtOrd, RespectsSemanticsBelow rows₄ (Finset.univ, j) q' ∧
        (∀ d, min (q' d) γ = min (q d) γ) ∧
        (∀ d : D₄.below CI, q' (CellScheme.below.mono h d) = p d)

/-- Bountifulness of the four-point scheme from the scope-changing cases. -/
theorem rows₄_isBountiful_of (H : ProperToFull₄) : rows₄.IsBountiful := by
  intro CI BJ hCI hBJ h hne p q γ hp hq hγ hagree
  by_cases hB : BJ.1 = Finset.univ
  · by_cases hC : CI.1 = Finset.univ
    · obtain ⟨B, j⟩ := BJ
      obtain ⟨C, i⟩ := CI
      dsimp only at hB hC
      subst hB hC
      exact bountiful_full_scope rows₄ h p q γ hp hq hγ hagree
    · obtain ⟨B, j⟩ := BJ
      dsimp only at hB
      subst hB
      exact H CI j hCI hC hBJ h p q γ hp hq hγ hagree
  · exact bountiful₄_proper CI BJ hCI hBJ h hne hB p q γ hp hq hγ hagree

/-- **The four-point domain with its associated semantics**, conditional on the scope-changing
cases. -/
noncomputable abbrev semScheme₄ (H : ProperToFull₄) : SemScheme 4 where
  scheme := D₄
  rows := rows₄
  rows_coded := rows₄_isCoded
  consistent := rows₄_isConsistent
  bountiful := rows₄_isBountiful_of H
  complete := D₄_complete


/-! ## Part 4 — the old labelled type, literal face readback, the coface, the readback inputs -/

/-- Every old cell lies below the top cell. -/
theorem hall₀ (d : Cell C₀) : GradedLe (C₀.cell d) (C₀.cell top) := by
  rw [cell_top]
  refine ⟨Finset.subset_univ _, ?_⟩
  change C₀.grade d ≤ 3
  exact (C₀.grade_le_card_scope d).trans ((Finset.card_le_univ _).trans (by simp))

/-- **The old labelled type**: `semScheme₀` labelled by the row of the capped cell with cap
`ω + 4`, at the stage `ω·2`. -/
noncomputable def p₀ : S stage 3 where
  scheme := semScheme₀
  label d := rowA₂ ⟨d, hall₀ d⟩
  label_bound _ := Or.inl (rowA₂_stage_bound _)
  respects := rowA₂_respects.toRespects hall₀

theorem vis₄ : Finset.univ.image Fin.castSuccEmb ∈ D₄.plan := CellScheme.extendOneWith_visible

theorem hE₄ : D₄.restrictFace Fin.castSuccEmb vis₄ = C₀ :=
  CellScheme.restrictFace_extendOneWith newCell₄_last

theorem hcard₄ : (D₄.restrictFace Fin.castSuccEmb vis₄).card = C₀.card :=
  congrArg CellScheme.card hE₄

/-- The cell map of the face restriction is `castAdd`. -/
theorem toCell_cast₄ (i : Cell C₀) :
    toCell D₄ Fin.castSuccEmb vis₄ (Fin.cast hcard₄.symm i) = Fin.castAdd (Fintype.card New) i :=
  CellScheme.restrictFace.toCell_cast_eq_of_emb D₄ Fin.castSuccEmb vis₄ (e := Fin.castAdd _)
    (Fin.strictMono_castAdd _)
    (fun c => (CellScheme.extendOneWith_scope_subset_iff newCell₄_last _).mpr ⟨c, rfl⟩) hcard₄ i

theorem not_mute_castAdd (i : Cell C₀) : ¬ mute₄ (Fin.castAdd (Fintype.card New) i) := by
  intro h
  change D₄.cell _ = _ at h
  rw [D₄_cell_castAdd] at h
  have h2 : C₀.grade i = 4 := congrArg Prod.snd h
  have := (C₀.grade_le_card_scope i).trans
    ((Finset.card_le_univ _).trans (by simp : Fintype.card (Fin 3) ≤ 3))
  omega

/-- The restricted rows are the old rows (read through `castAdd` and the retraction). -/
theorem rows₄_restrict (Sig : Cell C₀) (d : C₀.below (C₀.cell Sig))
    (pf : GradedLe ((D₄.restrictFace Fin.castSuccEmb vis₄).cell (Fin.cast hcard₄.symm d.1))
      ((D₄.restrictFace Fin.castSuccEmb vis₄).cell (Fin.cast hcard₄.symm Sig))) :
    (rows₄.restrictFace Fin.castSuccEmb vis₄).E (Fin.cast hcard₄.symm Sig)
      ⟨Fin.cast hcard₄.symm d.1, pf⟩ = family₀.rows.E Sig d := by
  change rows₄.E (toCell D₄ Fin.castSuccEmb vis₄ (Fin.cast hcard₄.symm Sig))
    ⟨toCell D₄ Fin.castSuccEmb vis₄ (Fin.cast hcard₄.symm d.1), _⟩ = family₀.rows.E Sig d
  have hc : GradedLe (D₄.cell (Fin.castAdd (Fintype.card New) d.1))
      (D₄.cell (Fin.castAdd (Fintype.card New) Sig)) := by
    rw [D₄_cell_castAdd, D₄_cell_castAdd]
    exact (CellScheme.restrictFace.gradedLe_pushGraded_iff _).mpr d.2
  rw [rows₄.E_congr (toCell_cast₄ Sig) (toCell_cast₄ d.1) (hd := hc)]
  erw [rows₄_E_of_not_mute (not_mute_castAdd Sig)]
  change family₀.rows.E (ret (Fin.castAdd _ Sig)) ⟨ret (Fin.castAdd _ d.1), _⟩ = _
  exact family₀.rows.E_congr (ret_castAdd Sig) (ret_castAdd d.1)

variable (H : ProperToFull₄)

/-- **Literal face readback**: the four-point domain extends the old labelled type — its face
restriction along the initial segment is `semScheme₀`, rows included. -/
theorem extendsDomain₄ : ExtendsDomain p₀ (semScheme₄ H) where
  visible := vis₄
  restrict := by
    refine SemScheme.ext_of_components (congrArg CellScheme.plan hE₄) (congrArg CellScheme.card hE₄)
      (fun i => CellScheme.cell_cast_of_eq hE₄ i) (fun Sig d => ?_)
    exact rows₄_restrict Sig d _

theorem cellOf₄ (d : Cell C₀) : (extendsDomain₄ H).cellOf d = Fin.castAdd (Fintype.card New) d :=
  toCell_cast₄ d

/-! ### The coface: the pullback of the old labelling -/

/-- The labelling of the four-point scheme: the old labelling pulled back along the retraction,
`⊥` at the mute cell. -/
noncomputable def label₄ (d : Cell D₄) : ExtOrd :=
  if mute₄ d then ⊥ else rowA₂ ⟨ret d, hall₀ (ret d)⟩

theorem label₄_of_not_mute {d : Cell D₄} (hd : ¬ mute₄ d) :
    label₄ d = rowA₂ ⟨ret d, hall₀ (ret d)⟩ := by
  unfold label₄; rw [ite_eq_right hd]

theorem label₄_castAdd (i : Cell C₀) : label₄ (Fin.castAdd (Fintype.card New) i) = p₀.label i := by
  rw [label₄_of_not_mute (not_mute_castAdd i)]
  change rowA₂ ⟨ret (Fin.castAdd _ i), _⟩ = rowA₂ ⟨i, _⟩
  congr 1
  exact Subtype.ext (ret_castAdd i)

theorem scope_a₂cell : C₀.scope a₂cell = Finset.univ := by
  change (family₀.cellX (family₀.e.symm (family₀.e _))).1 = _
  rw [Equiv.symm_apply_apply]; rfl

theorem grade_a₂cell : C₀.grade a₂cell = 3 := by
  change (family₀.cellX (family₀.e.symm (family₀.e _))).2 = _
  rw [Equiv.symm_apply_apply]; rfl

theorem univ_mem_newFaces : (Finset.univ : Finset (Fin 4)) ∈ newFaces := by decide
theorem image_fold_univ : (Finset.univ : Finset (Fin 4)).image fold = Finset.univ := by decide

/-- The copy of the capped cell with cap `ω + 4` at the full face: the controller. -/
noncomputable def u3b : Cell D₄ :=
  Fin.natAdd C₀.card ((Fintype.equivFin New)
    (.inl ⟨(⟨Finset.univ, univ_mem_newFaces⟩, a₂cell), by rw [scope_a₂cell, image_fold_univ]⟩))

theorem cell_u3b : D₄.cell u3b = (Finset.univ, 3) := by
  unfold u3b
  rw [D₄_cell_natAdd, Equiv.symm_apply_apply]
  change (Finset.univ, C₀.grade a₂cell) = _
  rw [grade_a₂cell]

theorem ret_u3b : ret u3b = a₂cell := by
  unfold u3b; rw [ret_natAdd, Equiv.symm_apply_apply]; rfl

theorem not_mute_u3b : ¬ mute₄ u3b := by
  intro h; change D₄.cell u3b = _ at h; rw [cell_u3b] at h
  exact absurd (congrArg Prod.snd h) (by decide)

/-- Every non-mute cell lies below the controller. -/
theorem below_u3b {d : Cell D₄} (hd : ¬ mute₄ d) : GradedLe (D₄.cell d) (D₄.cell u3b) := by
  rw [cell_u3b]
  refine ⟨Finset.subset_univ _, ?_⟩
  change D₄.grade d ≤ 3
  have h4 : D₄.grade d ≤ 4 :=
    (D₄.grade_le_card_scope d).trans ((Finset.card_le_univ _).trans (by simp))
  by_contra hlt
  apply hd
  have hg : D₄.grade d = 4 := by omega
  have hs : D₄.scope d = Finset.univ := by
    apply Finset.eq_univ_of_card
    have := D₄.grade_le_card_scope d
    have h4' : (D₄.scope d).card ≤ 4 := (Finset.card_le_univ _).trans (by simp)
    rw [Fintype.card_fin]; omega
  exact Prod.ext hs hg

/-- The controller's row is the labelling on its lower set. -/
theorem rows₄_u3b (d : D₄.below (D₄.cell u3b)) : rows₄.E u3b d = label₄ d.1 := by
  have hd : ¬ mute₄ d.1 := hmute_below₄ u3b d.1 not_mute_u3b d.2
  rw [rows₄_E_of_not_mute not_mute_u3b, label₄_of_not_mute hd]
  change family₀.rows.E (ret u3b) ⟨ret d.1, _⟩ = family₀.rows.E top ⟨ret d.1, _⟩
  exact family₀.rows.E_congr ret_u3b rfl

/-- **The coface**: the four-point domain labelled by the pulled-back labelling. -/
noncomputable def q₀ : S stage 4 where
  scheme := semScheme₄ H
  label := label₄
  label_bound d := by
    by_cases hd : mute₄ d
    · left; unfold label₄; rw [ite_eq_left hd]; exact bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)
    · left; rw [label₄_of_not_mute hd]; exact rowA₂_stage_bound _
  respects := by
    have hu := rows₄_isConsistent u3b
    refine ⟨?_, ?_, ?_⟩
    · intro d
      by_cases hd : mute₄ d
      · unfold label₄; rw [ite_eq_left hd]; exact (extVisibilityReplace_bot _ _).symm
      · have := hu.orderly ⟨d, below_u3b hd⟩
        dsimp only at this
        erw [rows₄_u3b] at this
        exact this
    · intro Sig
      by_cases hSig : mute₄ Sig
      · refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
        funext d
        unfold label₄; rw [ite_eq_left hSig, min_eq_right bot_le]
      · have key := hu.locality ⟨Sig, below_u3b hSig⟩
        refine transformsTo_congr rfl rfl ?_ key
        funext d
        erw [rows₄_u3b, rows₄_u3b]
        rfl
    · intro Sig Xi₀ hs hg
      by_cases hSig : mute₄ Sig
      · have hXi : mute₄ Xi₀ := by
          change D₄.cell Xi₀ = _
          change D₄.cell Sig = _ at hSig
          have hs' : Finset.univ ⊆ D₄.scope Xi₀ := by
            have := hs; change (D₄.cell Sig).1 ⊆ _ at this; rw [hSig] at this; exact this
          have hg' : D₄.grade Xi₀ = 4 := by
            have := hg; change (D₄.cell Sig).2 = _ at this; rw [hSig] at this; exact this.symm
          exact Prod.ext (Finset.univ_subset_iff.mp hs') hg'
        refine ⟨Xi₀, rfl, ?_⟩
        unfold label₄; rw [ite_eq_left hSig]; exact bot_le
      · have hXi : ¬ mute₄ Xi₀ := by
          intro hXi
          apply hSig
          change D₄.cell Xi₀ = _ at hXi
          change D₄.cell Sig = _
          have hg' : D₄.grade Sig = 4 := by
            have := hg; change _ = (D₄.cell Xi₀).2 at this; rw [hXi] at this; exact this
          have hs' : D₄.scope Sig = Finset.univ := by
            apply Finset.eq_univ_of_card
            have := D₄.grade_le_card_scope Sig
            have h4' : (D₄.scope Sig).card ≤ 4 := (Finset.card_le_univ _).trans (by simp)
            rw [Fintype.card_fin]; omega
          exact Prod.ext hs' hg'
        obtain ⟨Xi, hcell, hle⟩ := hu.availability ⟨Sig, below_u3b hSig⟩ ⟨Xi₀, below_u3b hXi⟩ hs hg
        refine ⟨Xi.1, hcell, ?_⟩
        erw [rows₄_u3b, rows₄_u3b] at hle; exact hle

/-- **The coface relation**: the face restriction of `q₀` along the initial segment is `p₀`. -/
theorem isCoface₄ : IsCoface p₀ (q₀ H) := by
  change typeMap Fin.castSuccEmb (q₀ H) = some p₀
  rw [typeMap_eq_some _ _ vis₄]
  congr 1
  refine StageType.ext_of_components (congrArg CellScheme.plan hE₄) (congrArg CellScheme.card hE₄)
    (fun i => CellScheme.cell_cast_of_eq hE₄ i) (fun i => ?_) (fun Sig d => ?_)
  · change label₄ (toCell D₄ Fin.castSuccEmb vis₄ (Fin.cast hcard₄.symm i)) = p₀.label i
    erw [toCell_cast₄, label₄_castAdd]
  · exact rows₄_restrict Sig d _

/-! ### The inherited reference data and the fresh request -/

/-- The old singleton cell of the point `0`. -/
noncomputable def s0cell : Cell C₀ := family₀.e (.inl .s0)

theorem scope_s0cell : C₀.scope s0cell = {0} := by
  change (family₀.cellX (family₀.e.symm (family₀.e _))).1 = _
  rw [Equiv.symm_apply_apply]; rfl

theorem grade_s0cell : C₀.grade s0cell = 1 := by
  change (family₀.cellX (family₀.e.symm (family₀.e _))).2 = _
  rw [Equiv.symm_apply_apply]; rfl

theorem three_mem_newFaces : ({3} : Finset (Fin 4)) ∈ newFaces := by decide
theorem image_fold_three : ({3} : Finset (Fin 4)).image fold = {0} := by decide

/-- **The fresh cell**: the copy of the singleton cell at the new point. -/
noncomputable def s3copy : Cell D₄ :=
  Fin.natAdd C₀.card ((Fintype.equivFin New)
    (.inl ⟨(⟨{3}, three_mem_newFaces⟩, s0cell), by rw [scope_s0cell, image_fold_three]⟩))

theorem ret_s3copy : ret s3copy = s0cell := by
  unfold s3copy; rw [ret_natAdd, Equiv.symm_apply_apply]; rfl

theorem cell_s3copy : D₄.cell s3copy = ({3}, 1) := by
  unfold s3copy
  rw [D₄_cell_natAdd, Equiv.symm_apply_apply]
  change ({3}, C₀.grade s0cell) = _
  rw [grade_s0cell]

/-- **The inherited reference data**: threshold `3`, cap and trigger the old capped cell, the
old singleton cell as representative, one fresh request at the copied singleton: block `ω`,
offset `1`. -/
noncomputable def R₄ : FiniteReferenceData (Cell D₄) D₄.grade where
  N := 3
  cap := Fin.castAdd (Fintype.card New) a₂cell
  cap_grade := by rw [D₄_grade_castAdd, grade_a₂cell]
  trigger := Fin.castAdd (Fintype.card New) a₂cell
  rep _ := Fin.castAdd (Fintype.card New) s0cell
  requests := [⟨s3copy, Ordinal.omega0 * (1 : ℕ), 1⟩]
  req_grade_le r hr := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    change D₄.grade s3copy ≤ 3
    rw [CellScheme.grade, cell_s3copy]; decide
  rep_grade_le r _ := by
    rw [D₄_grade_castAdd, grade_s0cell]; decide
  offset_lt r hr := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; decide

theorem p₀_label_a₂cell : p₀.label a₂cell = γ₀ := rowA₂_cap
theorem p₀_label_s0cell : p₀.label s0cell = ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ)) := rowA₂_s0

/-- Cells of the old scheme at the full grade-three index are the capped cells. -/
theorem old_full_three {x : family₀.X} (h : family₀.cellX x = (Finset.univ, 3)) :
    ∃ b : ↥family₀.S₃, x = .inr (.inr (.inr b)) := by
  rcases x with c | H' | s' | b
  · exact absurd (congrArg Prod.fst h) (Prop3.scope_ne_univ c)
  · exact absurd (congrArg Prod.snd h) (by decide : (1 : ℕ) ≠ 3)
  · exact absurd (congrArg Prod.snd h) (by decide : (2 : ℕ) ≠ 3)
  · exact ⟨b, rfl⟩

theorem v₀_le_η₁ : v₀ ≤ η₁ := by
  unfold v₀ η₁; rw [ofOrd_le_ofOrd]
  exact add_le_add_right
    (Nat.cast_le.mpr (by decide : (1 : ℕ) ≤ 3) : ((1 : ℕ) : Ordinal) ≤ (3 : ℕ)) _

/-- The value of an old grade-three row at the singleton cell is `ω + 1`. -/
theorem old_three_at_s0 (y : Cell C₀) (hy : C₀.cell y = (Finset.univ, 3))
    (hd : GradedLe (C₀.cell s0cell) (C₀.cell y)) :
    family₀.rows.E y ⟨s0cell, hd⟩ = ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ)) := by
  have hy' : family₀.cellX (family₀.e.symm y) = (Finset.univ, 3) := by
    rw [← Family.cell_eq]; exact hy
  obtain ⟨b, hb⟩ := old_full_three hy'
  change family₀.rowX (family₀.e.symm y) (family₀.e.symm (family₀.e (.inl .s0))) = _
  rw [Equiv.symm_apply_apply, hb, Family.rowX_a_inl]
  rcases mem_S₃_cases b.2 with hb' | hb' <;> rw [hb']
  · change min (t₀.F .s0) η₁ = _
    rw [t₀_F_eq (by decide)]; exact min_eq_left v₀_le_η₁
  · change min (t₀.F .s0) γ₀ = _
    rw [t₀_F_eq (by decide)]; exact min_eq_left v₀_le_γ₀

theorem evr_omega_add_one :
    extVisibilityReplace (ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ))) 3 1 =
      ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ)) := by
  rw [extVisibilityReplace_ofOrd, visibilityReplace,
    ite_eq_left (by rw [finitePart_mul_add]; decide),
    ordinalReplace, limitPart_omega_add_one]

/-- **The readback inputs** for the four-point context, with the fresh request at the copied
singleton and every controller at `(univ, 3)` correct. -/
noncomputable def inputs₄ : ReadbackInputs (extendsDomain₄ H) (q₀ H).label R₄ where
  trigger_grade_le_m := by
    change D₄.grade (Fin.castAdd _ a₂cell) ≤ 3
    rw [D₄_grade_castAdd, grade_a₂cell]
  trigger_grade_le_N := by
    change D₄.grade (Fin.castAdd _ a₂cell) ≤ 3
    rw [D₄_grade_castAdd, grade_a₂cell]
  trigger_pattern := by
    change label₄ (Fin.castAdd _ a₂cell) ≠ ⊥
    rw [label₄_castAdd, p₀_label_a₂cell]; exact ofOrd_ne_bot _
  capBase := a₂cell
  cap_eq := (cellOf₄ H a₂cell).symm
  cap_dom r hr := by
    simp only [R₄, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    change ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ)) < p₀.label a₂cell
    rw [p₀_label_a₂cell]; unfold γ₀; rw [ofOrd_lt_ofOrd]
    exact add_lt_add_right
      (Nat.cast_lt.mpr (by decide : (1 : ℕ) < 4) : ((1 : ℕ) : Ordinal) < (4 : ℕ)) _
  repBase _ := s0cell
  repOff _ := 1
  rep_eq r _ := (cellOf₄ H s0cell).symm
  rep_label r hr := by
    simp only [R₄, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact p₀_label_s0cell
  rep_off_lt r _ := by change (1 : ℕ) < 3; decide
  rep_le_cap r _ := by rw [p₀_label_s0cell, p₀_label_a₂cell]; exact v₀_le_γ₀
  block_limit r hr := by
    simp only [R₄, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact limitPart_mul_nat _
  controller_exists := ⟨u3b, cell_u3b⟩
  rows_correct Ξ hΞ := by
    intro _ r hr
    simp only [R₄, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    -- both the fresh cell and the representative read the old row at the singleton cell
    have hΞn : ¬ mute₄ Ξ := by
      intro h; change D₄.cell Ξ = _ at h; rw [hΞ] at h
      have h4 : R₄.N = 4 := congrArg Prod.snd h
      exact absurd h4 (by decide : ¬ ((3 : ℕ) = 4))
    have hbelow : ∀ d : Cell D₄, D₄.grade d ≤ 3 → GradedLe (D₄.cell d) (D₄.cell Ξ) := fun d hd => by
      rw [hΞ]; exact ⟨Finset.subset_univ _, hd⟩
    have hΘ : D₄.grade s3copy ≤ 3 := by rw [CellScheme.grade, cell_s3copy]; decide
    have hrep : D₄.grade (Fin.castAdd (Fintype.card New) s0cell) ≤ 3 := by
      rw [D₄_grade_castAdd, grade_s0cell]; decide
    have hretΞ : C₀.cell (ret Ξ) = (Finset.univ, 3) := by
      have h1 : C₀.scope (ret Ξ) = Finset.univ := by
        rw [scope_ret Ξ hΞn, show D₄.scope Ξ = Finset.univ from congrArg Prod.fst hΞ,
          image_fold_univ]
      have h2 : C₀.grade (ret Ξ) = 3 := by
        rw [← grade_ret Ξ hΞn]; exact congrArg Prod.snd hΞ
      exact Prod.ext h1 h2
    have hval : ∀ (d : Cell D₄) (hd : D₄.grade d ≤ 3), ret d = s0cell →
        (semScheme₄ H).rowOf Ξ d = ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ)) := fun d hd hret => by
      rw [SemScheme.rowOf_of_le _ _ (hbelow d hd)]
      change rows₄.E Ξ ⟨d, _⟩ = _
      erw [rows₄_E_of_not_mute hΞn]
      change family₀.rows.E (ret Ξ) ⟨ret d, _⟩ = _
      have hd' : GradedLe (C₀.cell s0cell) (C₀.cell (ret Ξ)) := by
        rw [hretΞ]
        exact ⟨Finset.subset_univ _, by change C₀.grade s0cell ≤ 3; rw [grade_s0cell]; decide⟩
      rw [family₀.rows.E_congr rfl hret (hd := hd')]
      exact old_three_at_s0 (ret Ξ) hretΞ hd'
    change min ((semScheme₄ H).rowOf Ξ s3copy) _ =
      min (extVisibilityReplace ((semScheme₄ H).rowOf Ξ (Fin.castAdd _ s0cell)) 3 1) _
    rw [hval s3copy hΘ ret_s3copy, hval _ hrep (ret_castAdd s0cell), evr_omega_add_one]

/-- **The universal fresh readback**: every coface of `p₀` on the four-point domain with the
`⊥`-pattern of `q₀` reads `ω + 1` at the fresh cell. -/
theorem readback₄ (q : S stage 4) (hqD : q.scheme = semScheme₄ H)
    (hpat : ∀ Θ : (semScheme₄ H).scheme.below (Finset.univ, 3),
      q.label (SemScheme.castCell hqD.symm Θ.1) = ⊥ ↔ label₄ Θ.1 = ⊥)
    (hq : IsCoface p₀ q) :
    q.label (SemScheme.castCell hqD.symm s3copy) = ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ)) := by
  have := (inputs₄ H).readback q hqD hpat hq ⟨s3copy, Ordinal.omega0 * (1 : ℕ), 1⟩
    (List.mem_singleton_self _)
  exact this

theorem castCell_q₀ (h : semScheme₄ H = (q₀ H).scheme) (d : Cell (semScheme₄ H).scheme) :
    SemScheme.castCell h d = d := Fin.ext rfl

/-- The realization: `q₀` itself, with the trigger active. -/
theorem q₀_readback : (q₀ H).label s3copy = ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ)) := by
  have := readback₄ H (q₀ H) rfl (fun Θ => by rw [castCell_q₀]; exact Iff.rfl) (isCoface₄ H)
  rwa [castCell_q₀] at this

theorem q₀_trigger : (q₀ H).label R₄.trigger ≠ ⊥ := (inputs₄ H).trigger_pattern


/-! ## Part 5 — the scope-changing cases: reduction to old bountifulness through rigidity -/

/-- Respect transports along an equality of graded pairs. -/
theorem RespectsSemanticsBelow.cast {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ BJ' : Finset ι × ℕ} (h : BJ = BJ') {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) :
    RespectsSemanticsBelow sem BJ' (fun d => r ⟨d.1, by rw [h]; exact d.2⟩) := by
  subst h
  exact hr

/-- The old cells inside a full-scope lower set. -/
noncomputable def toOld (j : ℕ) (d : C₀.below (Finset.univ, j)) : D₄.below (Finset.univ, j) :=
  ⟨Fin.castAdd (Fintype.card New) d.1, by
    rw [D₄_cell_castAdd]; exact ⟨Finset.subset_univ _, d.2.2⟩⟩

theorem toOld_val (j : ℕ) (d : C₀.below (Finset.univ, j)) :
    (toOld j d).1 = Fin.castAdd (Fintype.card New) d.1 := rfl

/-- A cell of the four-point scheme with a pushed graded index is an old cell of that index. -/
theorem old_of_cell_push {x : Cell D₄} {y : Cell C₀}
    (h : D₄.cell x = pushGraded Fin.castSuccEmb (C₀.cell y)) :
    ∃ i : Cell C₀, x = Fin.castAdd (Fintype.card New) i ∧ C₀.cell i = C₀.cell y := by
  have hvis : D₄.scope x ⊆ Finset.univ.image Fin.castSuccEmb := by
    change (D₄.cell x).1 ⊆ _
    rw [h]
    exact Finset.image_subset_image (Finset.subset_univ _)
  obtain ⟨i, rfl⟩ := (CellScheme.extendOneWith_scope_subset_iff newCell₄_last x).mp hvis
  rw [D₄_cell_castAdd] at h
  exact ⟨i, rfl, CellScheme.restrictFace.pushGraded_injective _ h⟩

/-- **Restriction to the old cells** of a respecting labelling of a full-scope lower set respects
the old semantics (old cells below old cells are old; availability witnesses at old indices are
old). -/
theorem restrict_old_respects {j : ℕ} {q : D₄.below (Finset.univ, j) → ExtOrd}
    (hq : RespectsSemanticsBelow rows₄ (Finset.univ, j) q) :
    RespectsSemanticsBelow family₀.rows (Finset.univ, j) (q ∘ toOld j) where
  orderly d := by
    have := hq.orderly (toOld j d)
    dsimp only at this ⊢
    rw [toOld_val, D₄_grade_castAdd] at this
    exact this
  locality Sig := by
    let φ : C₀.below (C₀.cell Sig.1) → D₄.below (D₄.cell (toOld j Sig).1) := fun d =>
      ⟨Fin.castAdd _ d.1, by
        rw [toOld_val, D₄_cell_castAdd, D₄_cell_castAdd]
        exact (CellScheme.restrictFace.gradedLe_pushGraded_iff _).mpr d.2⟩
    have key := (hq.locality (toOld j Sig)).reindex φ
    refine transformsTo_congr ?_ ?_ ?_ key
    · funext d
      change D₄.grade (Fin.castAdd _ d.1) = C₀.grade d.1
      exact D₄_grade_castAdd d.1
    · funext d
      change rows₄.E (Fin.castAdd _ Sig.1) (φ d) = family₀.rows.E Sig.1 d
      erw [rows₄_E_of_not_mute (not_mute_castAdd Sig.1)]
      change family₀.rows.E (ret (Fin.castAdd _ Sig.1)) ⟨ret (Fin.castAdd _ d.1), _⟩ = _
      exact family₀.rows.E_congr (ret_castAdd Sig.1) (ret_castAdd d.1)
    · funext d
      rfl
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hcell, hle⟩ := hq.availability (toOld j Sig) (toOld j Xi₀)
      (by change D₄.scope (Fin.castAdd _ Sig.1) ⊆ D₄.scope (Fin.castAdd _ Xi₀.1)
          rw [D₄_scope_castAdd, D₄_scope_castAdd]; exact Finset.image_subset_image hs)
      (by change D₄.grade (Fin.castAdd _ Sig.1) = D₄.grade (Fin.castAdd _ Xi₀.1)
          rw [D₄_grade_castAdd, D₄_grade_castAdd]; exact hg)
    have hcell' : D₄.cell Xi.1 = pushGraded Fin.castSuccEmb (C₀.cell Xi₀.1) := by
      rw [hcell, toOld_val, D₄_cell_castAdd]
    obtain ⟨y, hy, hcy⟩ := old_of_cell_push hcell'
    have hy₂ : GradedLe (C₀.cell y) (Finset.univ, j) := by
      have := Xi.2
      rw [hy, D₄_cell_castAdd] at this
      exact ⟨Finset.subset_univ _, this.2⟩
    refine ⟨⟨y, hy₂⟩, hcy, ?_⟩
    have e : toOld j ⟨y, hy₂⟩ = Xi := Subtype.ext hy.symm
    change q (toOld j Sig) ≤ q (toOld j ⟨y, hy₂⟩)
    rw [e]; exact hle

/-- **Rigidity**: every respecting labelling of a full-scope lower set of grade at most three takes
the same value at a cell and at the old cell it retracts to. -/
def Rigidity₄ : Prop :=
  ∀ (j : ℕ) (hj : j ≤ 3) (q : D₄.below (Finset.univ, j) → ExtOrd),
    RespectsSemanticsBelow rows₄ (Finset.univ, j) q →
    ∀ x : D₄.below (Finset.univ, j),
      q x = q ⟨Fin.castAdd (Fintype.card New) (ret x.1), by
        rw [D₄_cell_castAdd]
        refine ⟨Finset.subset_univ _, ?_⟩
        change C₀.grade (ret x.1) ≤ j
        rw [← grade_ret x.1 (not_mute_of_proper' hj x)]
        exact x.2.2⟩

/-- The scope-changing cases of grade at most three, from rigidity. -/
theorem properToFull₄_low_of_rigidity (R : Rigidity₄) (CI : Finset (Fin 4) × ℕ) (j : ℕ)
    (hj3 : j ≤ 3) (hCI : CI ∈ Plan.gradedPlan plan₄) (hC : CI.1 ≠ Finset.univ)
    (hj : (Finset.univ, j) ∈ Plan.gradedPlan plan₄) (h : GradedLe CI (Finset.univ, j))
    (p : D₄.below CI → ExtOrd) (q : D₄.below (Finset.univ, j) → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow rows₄ CI p) (hq : RespectsSemanticsBelow rows₄ (Finset.univ, j) q)
    (hγ : extVisibilityReplace γ j j = γ)
    (hagree : ∀ d : D₄.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D₄.below (Finset.univ, j) → ExtOrd, RespectsSemanticsBelow rows₄ (Finset.univ, j) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D₄.below CI, q' (CellScheme.below.mono h d) = p d) := by
  obtain ⟨C, i⟩ := CI
  dsimp only at hC
  have hCp : C ∈ plan₄ := (Plan.mem_gradedPlan.mp hCI).1
  -- the old lower sets
  have hfoldC : (C.image fold, i) ∈ Plan.gradedPlan Prop3.plan := by
    obtain ⟨-, hi0, hiC⟩ := Plan.mem_gradedPlan.mp hCI
    exact Plan.mem_gradedPlan.mpr ⟨fold_mem_plan C hCp hC, hi0, by
      change i ≤ (C.image fold).card; rw [card_fold_proper C hCp hC]; exact hiC⟩
  have hunivj : (Finset.univ, j) ∈ Plan.gradedPlan Prop3.plan := by
    obtain ⟨-, hj0, -⟩ := Plan.mem_gradedPlan.mp hj
    exact Plan.mem_gradedPlan.mpr ⟨C₀.isPlan.domain_mem, hj0, by
      change j ≤ (Finset.univ : Finset (Fin 3)).card
      rw [Finset.card_univ, Fintype.card_fin]; exact hj3⟩
  have h' : GradedLe (C.image fold, i) (Finset.univ, j) := ⟨Finset.subset_univ _, h.2⟩
  -- the old data
  let e := eProper (j := i) hCp hC
  have hp' : RespectsSemanticsBelow family₀.rows (C.image fold, i) (p ∘ e.symm) :=
    RespectsSemanticsBelow.of_pullback (not_mute_of_proper hC) e (eProper_val hCp hC)
      (hle_proper hCp hC) hp
  have hq' := restrict_old_respects hq
  -- old agreement, through rigidity
  have hag' : ∀ d' : C₀.below (C.image fold, i),
      min ((q ∘ toOld j) (CellScheme.below.mono h' d')) γ = min ((p ∘ e.symm) d') γ := by
    intro d'
    have hr := R j hj3 q hq (CellScheme.below.mono h (e.symm d'))
    have hret : ret (CellScheme.below.mono h (e.symm d')).1 = d'.1 :=
      ret_symm_val e (eProper_val hCp hC) d'
    change min (q (toOld j (CellScheme.below.mono h' d'))) γ = min (p (e.symm d')) γ
    rw [← hagree (e.symm d'), hr]
    congr 2
    apply Subtype.ext
    change Fin.castAdd _ d'.1 = Fin.castAdd _ (ret (CellScheme.below.mono h (e.symm d')).1)
    rw [hret]
  -- the old extension: by old bountifulness, or `p` itself when the pairs coincide
  obtain ⟨p₁, hp₁, hp₁γ, hp₁ext⟩ : ∃ p₁ : C₀.below (Finset.univ, j) → ExtOrd,
      RespectsSemanticsBelow family₀.rows (Finset.univ, j) p₁ ∧
      (∀ d, min (p₁ d) γ = min ((q ∘ toOld j) d) γ) ∧
      (∀ d : C₀.below (C.image fold, i), p₁ (CellScheme.below.mono h' d) = (p ∘ e.symm) d) := by
    by_cases hne' : (C.image fold, i) = (Finset.univ, j)
    · refine ⟨fun d => (p ∘ e.symm) ⟨d.1, by rw [hne']; exact d.2⟩, ?_, ?_, ?_⟩
      · have := RespectsSemanticsBelow.cast hne' hp'
        exact this
      · intro d
        have := hag' ⟨d.1, by rw [hne']; exact d.2⟩
        exact this.symm
      · intro d; rfl
    · exact semScheme₀.bountiful _ _ hfoldC hunivj h' hne' (p ∘ e.symm) (q ∘ toOld j) γ hp' hq'
        hγ hag'
  -- the pullback of the old extension
  have hretB : ∀ a : D₄.below (Finset.univ, j), GradedLe (C₀.cell (ret a.1)) (Finset.univ, j) := by
    intro a
    refine ⟨Finset.subset_univ _, ?_⟩
    change C₀.grade (ret a.1) ≤ j
    rw [← grade_ret a.1 (not_mute_of_proper' hj3 a)]
    exact a.2.2
  refine ⟨fun a => p₁ ⟨ret a.1, hretB a⟩,
    RespectsSemanticsBelow.pullback_of_sect (not_mute_of_proper' hj3) hretB hsect₄ hp₁, ?_, ?_⟩
  · intro x
    rw [R j hj3 q hq x]
    exact hp₁γ ⟨ret x.1, hretB x⟩
  · intro d
    have h2 := hp₁ext (e d)
    change p₁ (CellScheme.below.mono h' (e d)) = p (e.symm (e d)) at h2
    rw [e.symm_apply_apply] at h2
    have e3 : (⟨ret (CellScheme.below.mono h d).1, hretB _⟩ : C₀.below (Finset.univ, j)) =
        CellScheme.below.mono h' (e d) := by
      apply Subtype.ext
      change ret d.1 = (e d).1
      rw [eProper_val]
    change p₁ ⟨ret (CellScheme.below.mono h d).1, hretB _⟩ = p d
    rw [e3]; exact h2

/-- **The scope-changing cases from rigidity**: grade four by the general full-scope extension. -/
theorem properToFull₄_of_rigidity (R : Rigidity₄) : ProperToFull₄ := by
  intro CI j hCI hC hj h p q γ hp hq hγ hagree
  by_cases hj3 : j ≤ 3
  · exact properToFull₄_low_of_rigidity R CI j hj3 hCI hC hj h p q γ hp hq hγ hagree
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
    obtain ⟨q₃, hq₃, hq₃γ, hq₃ext⟩ := properToFull₄_low_of_rigidity R CI 3 le_rfl hCI hC hu3 hC3
      p (fun d => q (CellScheme.below.mono h₃ d)) γ hp (hq.mono h₃)
      ((show SelfVis 4 γ from hγ).mono (by omega)) (fun d => hagree d)
    obtain ⟨q', hq', hq'γ, hq'ext⟩ := bountiful_full_scope rows₄ h₃ q₃ q γ hq₃ hq hγ
      (fun d => (hq₃γ d).symm)
    refine ⟨q', hq', hq'γ, fun d => ?_⟩
    have e : CellScheme.below.mono h d =
        CellScheme.below.mono h₃ (CellScheme.below.mono hC3 d) := rfl
    rw [e, hq'ext, hq₃ext]

/-- **Rigidity — uniqueness of extension over a fixed old labelling**: every respecting labelling
of a full-scope lower set of grade at most three agrees at a cell and at its retraction, by the
controller-probe lemma with the copy and its original, whose controller readings agree by the
pullback definition. -/
theorem rigidity₄ : Rigidity₄ := by
  intro j hj q hq x
  let y : D₄.below (Finset.univ, j) :=
    ⟨Fin.castAdd (Fintype.card New) (ret x.1), by
      rw [D₄_cell_castAdd]
      refine ⟨Finset.subset_univ _, ?_⟩
      change C₀.grade (ret x.1) ≤ j
      rw [← grade_ret x.1 (not_mute_of_proper' hj x)]
      exact x.2.2⟩
  change q x = q y
  apply hq.eq_of_controller_probes x y
  · change D₄.grade x.1 = D₄.grade (Fin.castAdd (Fintype.card New) (ret x.1))
    rw [D₄_grade_castAdd]
    exact grade_ret x.1 (not_mute_of_proper' hj x)
  · obtain ⟨c, hc⟩ := D₄_complete (Finset.univ, D₄.grade x.1)
      (Plan.mem_gradedPlan.mpr ⟨D₄.isPlan.domain_mem, D₄.grade_pos x.1,
        (x.2.2.trans hj).trans (by decide : 3 ≤ (Finset.univ : Finset (Fin 4)).card)⟩)
    exact ⟨⟨c, by rw [hc]; exact ⟨Finset.Subset.refl _, x.2.2⟩⟩, hc⟩
  · intro c hx hy hc
    have hret : ret x.1 = ret y.1 := (ret_castAdd (ret x.1)).symm
    exact (rows₄_E_of_not_mute (not_mute_of_proper' hj c) ⟨x.1, hx⟩).trans
      ((family₀.rows.E_congr rfl hret).trans
        (rows₄_E_of_not_mute (not_mute_of_proper' hj c) ⟨y.1, hy⟩).symm)

/-- **The scope-changing cases**, unconditionally. -/
theorem properToFull₄ : ProperToFull₄ := properToFull₄_of_rigidity rigidity₄


/-! ## The endpoint: the legal duplication extension

A **legal duplication extension**: the fourth point duplicates the point `0`; the four-point domain
with its associated semantics is unconditional (`fourPointDomain`: coded, complete, consistent,
bountiful); it extends the old labelled type with literal old-face preservation
(`extendsDomain_fourPoint`, `isCoface_fourPoint`); and the fresh cell reads back universally
(`readback_fourPoint`: every coface with the `⊥`-pattern of the coface `fourPointCoface` reads
`ω + 1` at the copied singleton), realized by the coface with the trigger active
(`fourPointCoface_readback`, `fourPointCoface_trigger`).

**Scope.**  The extension forces the copied cell's label to equal its original's (uniqueness of
extension over a fixed old labelling).  It does not support independently prescribed fresh
labels, arbitrary requests, or realization inside two fixed models. -/

/-- **The four-point domain with its associated semantics**, unconditional. -/
noncomputable def fourPointDomain : SemScheme 4 := semScheme₄ properToFull₄

theorem fourPointDomain_scheme : fourPointDomain.scheme = D₄ := rfl
theorem fourPointDomain_rows : fourPointDomain.rows = rows₄ := rfl

/-- Literal face readback, unconditional. -/
theorem extendsDomain_fourPoint : ExtendsDomain p₀ fourPointDomain := extendsDomain₄ properToFull₄

/-- The coface, unconditional. -/
noncomputable def fourPointCoface : S stage 4 := q₀ properToFull₄

theorem isCoface_fourPoint : IsCoface p₀ fourPointCoface := isCoface₄ properToFull₄

/-- The readback inputs with the inherited reference data, unconditional. -/
noncomputable def fourPointInputs :
    ReadbackInputs extendsDomain_fourPoint fourPointCoface.label R₄ :=
  inputs₄ properToFull₄

/-- **Universal fresh readback**: every coface of `p₀` on the four-point domain with the
`⊥`-pattern of the coface reads `ω + 1` at the copied singleton. -/
theorem readback_fourPoint (q : S stage 4) (hqD : q.scheme = fourPointDomain)
    (hpat : ∀ Θ : fourPointDomain.scheme.below (Finset.univ, 3),
      q.label (SemScheme.castCell hqD.symm Θ.1) = ⊥ ↔ label₄ Θ.1 = ⊥)
    (hq : IsCoface p₀ q) :
    q.label (SemScheme.castCell hqD.symm s3copy) = ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ)) :=
  readback₄ properToFull₄ q hqD hpat hq

/-- The realization, with the trigger active. -/
theorem fourPointCoface_readback :
    fourPointCoface.label s3copy = ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ)) :=
  q₀_readback properToFull₄

theorem fourPointCoface_trigger : fourPointCoface.label R₄.trigger ≠ ⊥ := q₀_trigger properToFull₄

end FourPoint

end VaughtConjecture.Knight
