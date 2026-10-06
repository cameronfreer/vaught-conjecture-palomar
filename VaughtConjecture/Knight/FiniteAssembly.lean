/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedCoreCoding
public import VaughtConjecture.Knight.ThreeLevelLocality
public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.Domain
public import VaughtConjecture.Knight.OnePointSuccessor
public import Mathlib.Tactic.DeriveFintype

/-! # The fixed finite assembly over a constant proper part

A genuine finite scheme assembled from the provenance-preserving capped cores
(`Knight/CappedCore.lean`), with an explicit valid proper part and full-scope cells at every grade
its scope requires.

**The scheme.**  Scope `Fin 3`, plan `{∅, {0}, {1}, {2}, {0,1}, {1,2}, univ}` (a support plan:
step with pivots `0, 2`, `Prop3.isPlan`).  Required grades: `({x},1)`, `(B,1)`, `(B,2)` for the two
pairs `B`, and `(univ,1)`, `(univ,2)`, `(univ,3)` — exactly the three levels of the fragment.

* **Proper part** (seven cells, `Prop3`): the three singletons and the pair cells at grades
  `1, 2`.  Its rows are the **constant proper part**: every grade-one proper row is the constant
  `v ≠ ⊥` (self-visible at one), every grade-two proper row is `⊥`.  This is consistent, and it is
  compatible with every full-scope row whose proper values are constant on the grade-one cells and
  `⊥` on the grade-two cells: locality at a grade-one proper cell is a constant-to-constant
  transform (`transformsTo_const_const`, by `constNonbot`), at a grade-two proper cell the target
  is forced to `⊥` (`TransformsTo.to_bot`).
* **Full-scope cells** (`Family`): finite families `S₁ ⊆ Row1`, `S₂ ⊆ Core2`, `S₃ ⊆ CappedCore3`,
  nonempty, closed under the owned witnesses (`Core2.wit`, `witness1`, `Core3.wit2`) — the
  availability witnesses — with constant proper values.  Rows are the fragment rows (`Row1.row`,
  `Core2.row`, `CappedCore3.expandedRow`).  Cells are enumerated from the finite type
  `Prop3 ⊕ (S₁ ⊕ (S₂ ⊕ S₃))` (`CellScheme.ofFintype`).

**Proved for every family**: owner-grade coding (`Family.rows_isCoded`), completeness
(`Family.scheme_isComplete`), consistency (`Family.rows_isConsistent`: ambient locality by the
fragment localities reindexed along the lower sets, availability by the owned witnesses, on the
enlarged cell set including the capped cells).

**Bountifulness** splits by the scopes of the pair `⟨C,i⟩ ≺ ⟨B,j⟩`:

* `C = A = B`: `bountiful_full_scope` (every semantics);
* `B ≠ A`: `Family.bountiful_proper` — respecting labellings of a proper lower set are the constant
  labellings (`respects_proper_const`, `respects_constLabel`);
* `C ≠ A = B`: **the remaining obligation** `Family.ProperToFull`, sharpened to the relabelling
  lemma `Family.Relabel` (`properToFull_of_relabel`) and reduced to its grade-one case
  (`relabel_iff_gradeOne`).  The conditional domain is `Family.toSemScheme`.

The unconditional concrete instance is `Knight/FiniteAssemblyInstance.lean`; bountifulness for a
general `Family` remains open.  Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Constant-to-constant transforms at grade one -/

/-- A nonbottom constant row on cells of grade `≤ 1` transforms to any constant row whose value is
self-visible at one. -/
theorem transformsTo_const_const {D : Type*} {grade : D → ℕ} (hK : ∀ d, grade d ≤ 1)
    {v w : ExtOrd} (hv : v ≠ ⊥) (hw : SelfVis 1 w) :
    TransformsTo grade (fun _ => v) (fun _ => w) := by
  by_cases hw0 : w = ⊥
  · subst hw0; exact TransformsTo.to_bot _
  have h := (isStepShifter_constNonbot (K := 1) hw0 hw).transformsTo hK (fun _ : D => v)
  have e : (fun _ : D => constNonbot w v) = fun _ => w := by
    funext _; simp [constNonbot, hv]
  rwa [e] at h

/-! ## The concrete proper part: seven cells over `Fin 3` -/

/-- The proper cells: singletons `s0 s1 s2` (grade one), pair cells `p01a p12a` (grade one) and
`p01b p12b` (grade two). -/
inductive Prop3 : Type
  | s0 | s1 | s2 | p01a | p01b | p12a | p12b
  deriving DecidableEq

namespace Prop3

instance : Fintype Prop3 :=
  ⟨{s0, s1, s2, p01a, p01b, p12a, p12b}, fun x => by cases x <;> decide⟩

def scope : Prop3 → Finset (Fin 3)
  | s0 => {0} | s1 => {1} | s2 => {2}
  | p01a => {0, 1} | p01b => {0, 1} | p12a => {1, 2} | p12b => {1, 2}

def gradeP : Prop3 → ℕ
  | p01b => 2 | p12b => 2 | _ => 1

theorem gradeP_pos (c : Prop3) : 1 ≤ gradeP c := by cases c <;> decide
theorem gradeP_le_two (c : Prop3) : gradeP c ≤ 2 := by cases c <;> decide
theorem scope_ne_univ (c : Prop3) : scope c ≠ Finset.univ := by cases c <;> decide
theorem card_eq : Fintype.card Prop3 = 7 := rfl

/-- The singleton cell of a point. -/
def single : Fin 3 → Prop3
  | 0 => s0 | 1 => s1 | 2 => s2

theorem scope_single (x : Fin 3) : (single x).scope = {x} := by revert x; decide
theorem gradeP_single (x : Fin 3) : (single x).gradeP = 1 := by revert x; decide

/-- Every grade-one cell lies inside one of the two pair cells. -/
theorem grade_one_in_pair : ∀ c : Prop3, gradeP c = 1 →
    scope c ⊆ scope p01a ∨ scope c ⊆ scope p12a := by decide

theorem eq_of_grade_two {c c' : Prop3} (hc : c.gradeP = 2) (hc' : c'.gradeP = 2)
    (hs : c'.scope ⊆ c.scope) : c' = c := by
  revert c c'; decide

/-- The plan: the empty face, the singletons, the pairs `{0,1}` and `{1,2}`, and the domain. -/
def plan : Finset (Finset (Fin 3)) := {∅, {0}, {1}, {2}, {0, 1}, {1, 2}, Finset.univ}

theorem isPlan : AmalgamationPlan.Plan.IsPlan (Finset.univ : Finset (Fin 3)) plan := by
  have hQ : AmalgamationPlan.Plan.IsPlan ({1, 2} : Finset (Fin 3)) {∅, {1}, {2}, {1, 2}} := by
    refine AmalgamationPlan.Plan.IsPlan.step (a := 1) (b := 2) (Q := {∅, {2}}) (R := {∅, {1}})
      (by decide) (by decide) (by decide) ?_ ?_ (by decide) (by decide) (by decide)
    · rw [show ({1, 2} : Finset (Fin 3)).erase 1 = {2} by decide]
      exact AmalgamationPlan.Plan.IsPlan.singleton 2
    · rw [show ({1, 2} : Finset (Fin 3)).erase 2 = {1} by decide]
      exact AmalgamationPlan.Plan.IsPlan.singleton 1
  have hR : AmalgamationPlan.Plan.IsPlan ({0, 1} : Finset (Fin 3)) {∅, {0}, {1}, {0, 1}} := by
    refine AmalgamationPlan.Plan.IsPlan.step (a := 0) (b := 1) (Q := {∅, {1}}) (R := {∅, {0}})
      (by decide) (by decide) (by decide) ?_ ?_ (by decide) (by decide) (by decide)
    · rw [show ({0, 1} : Finset (Fin 3)).erase 0 = {1} by decide]
      exact AmalgamationPlan.Plan.IsPlan.singleton 1
    · rw [show ({0, 1} : Finset (Fin 3)).erase 1 = {0} by decide]
      exact AmalgamationPlan.Plan.IsPlan.singleton 0
  refine AmalgamationPlan.Plan.IsPlan.step (a := 0) (b := 2) (Q := {∅, {1}, {2}, {1, 2}})
    (R := {∅, {0}, {1}, {0, 1}}) (by decide) (by decide) (by decide) ?_ ?_ (by decide)
    (by decide) (by decide)
  · rw [show (Finset.univ : Finset (Fin 3)).erase 0 = {1, 2} by decide]; exact hQ
  · rw [show (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} by decide]; exact hR

theorem cell_mem (c : Prop3) : (scope c, gradeP c) ∈ AmalgamationPlan.Plan.gradedPlan plan := by
  rw [AmalgamationPlan.Plan.mem_gradedPlan]
  cases c <;> exact ⟨by decide, by decide, by decide⟩

/-- Inside a proper face, two grade-one cells coincide or are both inside the grade-one pair
cell of that face. -/
theorem grade_one_connected : ∀ B ∈ plan, B ≠ Finset.univ → ∀ c c' : Prop3,
    gradeP c = 1 → gradeP c' = 1 → scope c ⊆ B → scope c' ⊆ B →
    c = c' ∨ ∃ c₁, gradeP c₁ = 1 ∧ scope c₁ ⊆ B ∧ scope c ⊆ scope c₁ ∧ scope c' ⊆ scope c₁ := by
  decide

/-- The fragment's setting for the proper part, at any alphabet bound `T ≥ 8`. -/
theorem setting {T : ℕ} (hT : 8 ≤ T) : Setting gradeP T :=
  ⟨gradeP_pos, by rw [card_eq]; omega⟩

end Prop3

/-! ## A cell scheme from a finite type of cells -/

/-- A cell scheme whose cells are enumerated from a finite type `X` by `Fintype.equivFin`. -/
noncomputable def CellScheme.ofFintype {ι : Type*} [DecidableEq ι] {A : Finset ι} (X : Type*)
    [Fintype X] (plan : Finset (Finset ι)) (hplan : AmalgamationPlan.Plan.IsPlan A plan)
    (cellX : X → Finset ι × ℕ) (hmem : ∀ x, cellX x ∈ AmalgamationPlan.Plan.gradedPlan plan) :
    CellScheme A where
  plan := plan
  isPlan := hplan
  card := Fintype.card X
  cell i := cellX ((Fintype.equivFin X).symm i)
  cell_mem _ := hmem _

/-! ## The families and the cells -/

section Assembly

variable {T : ℕ} (st : Setting Prop3.gradeP T)

open Prop3 in
/-- **A constant-proper-part family**: the proper constant `v`, and finite families of level-one,
level-two and level-three (capped) cells, nonempty, with constant grade-one proper values and
`⊥` grade-two proper values, closed under the owned availability witnesses. -/
structure Family where
  v : ExtOrd
  v_ne : v ≠ ⊥
  v_vis : SelfVis 1 v
  v_coded : IsCodedLabel 1 v
  S₁ : Finset (Row1 Prop3.gradeP T)
  S₂ : Finset (Core2 (gradeP := Prop3.gradeP) (T := T))
  S₃ : Finset (CappedCore3 Prop3.gradeP T)
  ne₁ : S₁.Nonempty
  ne₂ : S₂.Nonempty
  ne₃ : S₃.Nonempty
  const₁ : ∀ H ∈ S₁, ∀ c c', gradeP c ≤ 1 → gradeP c' ≤ 1 → H.G c = H.G c'
  const₂ : ∀ s ∈ S₂, ∀ c c', gradeP c ≤ 1 → gradeP c' ≤ 1 → s.F c = s.F c'
  bot₂ : ∀ s ∈ S₂, ∀ c, gradeP c = 2 → s.F c = ⊥
  const₃ : ∀ a ∈ S₃, ∀ c c', gradeP c ≤ 1 → gradeP c' ≤ 1 → a.base.F c = a.base.F c'
  bot₃ : ∀ a ∈ S₃, ∀ c, gradeP c = 2 → a.base.F c = ⊥
  wit₂ : ∀ s ∈ S₂, s.wit st ∈ S₁
  wit₃₁ : ∀ a ∈ S₃, witness1 st.hT a.base.F (a.base.orderly st) ∈ S₁
  wit₃₂ : ∀ a ∈ S₃, a.base.wit2 st ∈ S₂

namespace Family

variable {st} (F : Family st)

/-- The cells: the proper cells and the three families. -/
abbrev X : Type 1 := Prop3 ⊕ (↥F.S₁ ⊕ (↥F.S₂ ⊕ ↥F.S₃))

/-- The graded index of a cell. -/
def cellX : F.X → Finset (Fin 3) × ℕ
  | .inl c => (c.scope, c.gradeP)
  | .inr (.inl _) => (Finset.univ, 1)
  | .inr (.inr (.inl _)) => (Finset.univ, 2)
  | .inr (.inr (.inr _)) => (Finset.univ, 3)

theorem cellX_mem (x : F.X) : F.cellX x ∈ AmalgamationPlan.Plan.gradedPlan Prop3.plan := by
  rcases x with c | H | s | a
  · exact Prop3.cell_mem c
  · change (Finset.univ, 1) ∈ _
    exact AmalgamationPlan.Plan.mem_gradedPlan.mpr ⟨by decide, by decide, by decide⟩
  · change (Finset.univ, 2) ∈ _
    exact AmalgamationPlan.Plan.mem_gradedPlan.mpr ⟨by decide, by decide, by decide⟩
  · change (Finset.univ, 3) ∈ _
    exact AmalgamationPlan.Plan.mem_gradedPlan.mpr ⟨by decide, by decide, by decide⟩

/-- Default cells (for the junk branches of the lower-set embeddings). -/
noncomputable def H₀ : Row1 Prop3.gradeP T := F.ne₁.choose
noncomputable def s₀ : Core2 (gradeP := Prop3.gradeP) (T := T) := F.ne₂.choose
noncomputable def a₀ : CappedCore3 Prop3.gradeP T := F.ne₃.choose

/-- The lower-set embeddings into the fragment's lower sets (junk off the lower sets). -/
noncomputable def toLow1 : F.X → Low1 Prop3.gradeP T
  | .inl c => if h : c.gradeP ≤ 1 then .inl ⟨c, h⟩ else .inr F.H₀
  | .inr (.inl H) => .inr H.1
  | .inr (.inr _) => .inr F.H₀

noncomputable def toLow2 : F.X → Low2 Prop3.gradeP T
  | .inl c => .inl ⟨c, c.gradeP_le_two⟩
  | .inr (.inl H) => .inr (.inl H.1)
  | .inr (.inr (.inl s)) => .inr (.inr s.1)
  | .inr (.inr (.inr _)) => .inr (.inr F.s₀)

noncomputable def toLow3 : F.X → CappedCore3.ExpandedLow3 (gradeP := Prop3.gradeP) (T := T)
  | .inl c => .inl ⟨c, c.gradeP_le_two.trans (by omega)⟩
  | .inr (.inl H) => .inr (.inl H.1)
  | .inr (.inr (.inl s)) => .inr (.inr (.inl s.1))
  | .inr (.inr (.inr a)) => .inr (.inr (.inr a.1))

/-- **The rows**, as total functions on pairs of cells (only the values at cells of the lower set
are read).  Proper rows: the constant `v` at grade one, `⊥` at grade two.  Full-scope rows: the
fragment rows. -/
noncomputable def rowX : F.X → F.X → ExtOrd
  | .inl c, _ => if c.gradeP ≤ 1 then F.v else ⊥
  | .inr (.inl H), y => H.1.row (F.toLow1 y)
  | .inr (.inr (.inl s)), y => s.1.row st (F.toLow2 y)
  | .inr (.inr (.inr a)), y => CappedCore3.expandedRow st a.1 (F.toLow3 y)

/-- The scheme. -/
noncomputable def scheme : CellScheme (ι := Fin 3) Finset.univ :=
  CellScheme.ofFintype F.X Prop3.plan Prop3.isPlan F.cellX F.cellX_mem

/-- The enumeration of the cells. -/
noncomputable def e : F.X ≃ Fin F.scheme.card := Fintype.equivFin F.X

theorem cell_e (x : F.X) : F.scheme.cell (F.e x) = F.cellX x := by
  change F.cellX ((Fintype.equivFin F.X).symm ((Fintype.equivFin F.X) x)) = _
  rw [Equiv.symm_apply_apply]

theorem cell_eq (i : Cell F.scheme) : F.scheme.cell i = F.cellX (F.e.symm i) := rfl

theorem grade_eq (i : Cell F.scheme) : F.scheme.grade i = (F.cellX (F.e.symm i)).2 := rfl
theorem scope_eq (i : Cell F.scheme) : F.scheme.scope i = (F.cellX (F.e.symm i)).1 := rfl


/-! ### Reading the rows -/

theorem toLow1_inl (c : Prop3) (h : c.gradeP ≤ 1) : F.toLow1 (.inl c) = .inl ⟨c, h⟩ := by
  simp [toLow1, h]

theorem rowX_H_inl (H : ↥F.S₁) (c : Prop3) (h : c.gradeP ≤ 1) :
    F.rowX (.inr (.inl H)) (.inl c) = H.1.G c := by
  change H.1.row (F.toLow1 (.inl c)) = _
  rw [toLow1_inl F c h]; rfl

theorem rowX_H_H (H H' : ↥F.S₁) : F.rowX (.inr (.inl H)) (.inr (.inl H')) = meet₁ H.1 H'.1 := rfl

theorem rowX_s_inl (s : ↥F.S₂) (c : Prop3) : F.rowX (.inr (.inr (.inl s))) (.inl c) = s.1.F c := rfl
theorem rowX_s_H (s : ↥F.S₂) (H : ↥F.S₁) :
    F.rowX (.inr (.inr (.inl s))) (.inr (.inl H)) = s.1.rho st H.1 := rfl
theorem rowX_s_s (s s' : ↥F.S₂) :
    F.rowX (.inr (.inr (.inl s))) (.inr (.inr (.inl s'))) = meet₂ st s.1 s'.1 := rfl

theorem expandedRow_inl (a : CappedCore3 Prop3.gradeP T) (c : {c : Prop3 // c.gradeP ≤ 3}) :
    CappedCore3.expandedRow st a (.inl c) = a.F c.1 := min_top_right _
theorem expandedRow_H (a : CappedCore3 Prop3.gradeP T) (H : Row1 Prop3.gradeP T) :
    CappedCore3.expandedRow st a (.inr (.inl H)) = a.rho1 st H := min_top_right _
theorem expandedRow_s (a : CappedCore3 Prop3.gradeP T)
    (s : Core2 (gradeP := Prop3.gradeP) (T := T)) :
    CappedCore3.expandedRow st a (.inr (.inr (.inl s))) = a.rho2 st s := min_top_right _

theorem rowX_a_inl (a : ↥F.S₃) (c : Prop3) :
    F.rowX (.inr (.inr (.inr a))) (.inl c) = a.1.F c := expandedRow_inl a.1 _
theorem rowX_a_H (a : ↥F.S₃) (H : ↥F.S₁) :
    F.rowX (.inr (.inr (.inr a))) (.inr (.inl H)) = a.1.rho1 st H.1 := expandedRow_H a.1 _
theorem rowX_a_s (a : ↥F.S₃) (s : ↥F.S₂) :
    F.rowX (.inr (.inr (.inr a))) (.inr (.inr (.inl s))) = a.1.rho2 st s.1 := expandedRow_s a.1 _
theorem rowX_a_a (a b : ↥F.S₃) :
    F.rowX (.inr (.inr (.inr a))) (.inr (.inr (.inr b))) = a.1.meetC st b.1 :=
  CappedCore3.expandedRow_at_capped st a.1 b.1

/-! ### The graded order on the cells -/

theorem gradedLe_inl_full {c : Prop3} {k : ℕ} :
    GradedLe (F.cellX (.inl c)) (Finset.univ, k) ↔ c.gradeP ≤ k :=
  ⟨fun h => h.2, fun h => ⟨Finset.subset_univ _, h⟩⟩

theorem not_gradedLe_full_inl {k : ℕ} {c : Prop3}
    (h : GradedLe (Finset.univ, k) (F.cellX (.inl c))) :
    False :=
  c.scope_ne_univ (Finset.univ_subset_iff.mp h.1)

/-- The cells below a proper cell are proper. -/
theorem below_inl {c : Prop3} {y : F.X} (h : GradedLe (F.cellX y) (F.cellX (.inl c))) :
    ∃ c' : Prop3, y = .inl c' ∧ c'.scope ⊆ c.scope ∧ c'.gradeP ≤ c.gradeP := by
  rcases y with c' | H | s | a
  · exact ⟨c', rfl, h.1, h.2⟩
  all_goals exact absurd h F.not_gradedLe_full_inl

/-! ### Self-visibility and coding of the rows -/

theorem isCodedLabel_mono {k k' : ℕ} {x : ExtOrd} (h : IsCodedLabel k x) (hk : k ≤ k') :
    IsCodedLabel k' x := by
  rcases h with rfl | ⟨i, j, hj, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, j, by omega, rfl⟩

/-- Every row value is self-visible at the grade of its cell (orderliness). -/
theorem rowX_selfVis (x y : F.X) (h : GradedLe (F.cellX y) (F.cellX x)) :
    SelfVis (F.cellX y).2 (F.rowX x y) := by
  rcases x with c | H | s | a
  · obtain ⟨c', rfl, -, hg⟩ := F.below_inl h
    change SelfVis c'.gradeP (if c.gradeP ≤ 1 then F.v else ⊥)
    split_ifs with hc
    · exact F.v_vis.mono (hg.trans hc)
    · exact selfVis_bot _
  · rcases y with c' | H' | s' | a'
    · have hc : c'.gradeP ≤ 1 := (F.gradedLe_inl_full).mp h
      rw [rowX_H_inl F H c' hc]; exact H.1.G_orderly c' hc
    · rw [rowX_H_H]; exact meet₁_selfVis _ _
    · exact absurd h.2 (by decide : ¬ ((2 : ℕ) ≤ 1))
    · exact absurd h.2 (by decide : ¬ ((3 : ℕ) ≤ 1))
  · rcases y with c' | H' | s' | a'
    · rw [rowX_s_inl]; exact s.1.F_orderly c' ((F.gradedLe_inl_full).mp h)
    · rw [rowX_s_H]; exact s.1.rho_selfVis st H'.1
    · rw [rowX_s_s]; exact meet₂_selfVis st _ _
    · exact absurd h.2 (by decide : ¬ ((3 : ℕ) ≤ 2))
  · rcases y with c' | H' | s' | a'
    · rw [rowX_a_inl]
      exact selfVis_min (a.1.base.F_orderly c' (c'.gradeP_le_two.trans (by omega)))
        (a.1.η_vis.mono ((F.gradedLe_inl_full).mp h))
    · rw [rowX_a_H]; change SelfVis 1 _
      exact selfVis_min (a.1.base.rho1_selfVis st H'.1) (a.1.η_vis.mono (by omega))
    · rw [rowX_a_s]; change SelfVis 2 _
      exact selfVis_min (a.1.base.rho2_selfVis st s'.1) (a.1.η_vis.mono (by omega))
    · rw [rowX_a_a]; exact CappedCore3.meetC_selfVis st _ _

/-- Every row value is coded at the grade of the row's owner (sharp coding). -/
theorem rowX_coded (x y : F.X) (h : GradedLe (F.cellX y) (F.cellX x)) :
    IsCodedLabel (F.cellX x).2 (F.rowX x y) := by
  rcases x with c | H | s | a
  · change IsCodedLabel c.gradeP (if c.gradeP ≤ 1 then F.v else ⊥)
    split_ifs with hc
    · exact isCodedLabel_mono F.v_coded c.gradeP_pos
    · exact Or.inl rfl
  · rcases y with c' | H' | s' | a'
    · have hc : c'.gradeP ≤ 1 := (F.gradedLe_inl_full).mp h
      rw [rowX_H_inl F H c' hc]
      exact (codedAlphabet_isAlph 1 T).coded _ (H.1.G_mem c' hc)
    · rw [rowX_H_H]; exact (codedAlphabet_isAlph 1 T).coded _ (meet₁_mem_V _ _)
    · exact absurd h.2 (by decide : ¬ ((2 : ℕ) ≤ 1))
    · exact absurd h.2 (by decide : ¬ ((3 : ℕ) ≤ 1))
  · rcases y with c' | H' | s' | a'
    · rw [rowX_s_inl]
      exact (codedAlphabet_isAlph 2 T).coded _ (s.1.F_mem c' ((F.gradedLe_inl_full).mp h))
    · rw [rowX_s_H]; exact (codedAlphabet_isAlph 2 T).coded _ (s.1.rho_mem st H'.1)
    · rw [rowX_s_s]; exact (codedAlphabet_isAlph 2 T).coded _ (meet₂_mem_V st _ _)
    · exact absurd h.2 (by decide : ¬ ((3 : ℕ) ≤ 2))
  · exact CappedCore3.expandedRow_coded st a.1 _

/-! ### The semantics -/

/-- The rows of the scheme, read through the enumeration. -/
noncomputable def rows : Semantics F.scheme where
  E Sig d := F.rowX (F.e.symm Sig) (F.e.symm d.1)
  orderly Sig d := (F.rowX_selfVis (F.e.symm Sig) (F.e.symm d.1) d.2).symm

theorem rows_E (Sig : Cell F.scheme) (d : F.scheme.below (F.scheme.cell Sig)) :
    F.rows.E Sig d = F.rowX (F.e.symm Sig) (F.e.symm d.1) := rfl

/-- **Owner-grade coding.** -/
theorem rows_isCoded : F.rows.IsCoded := fun Sig d =>
  F.rowX_coded (F.e.symm Sig) (F.e.symm d.1) d.2

/-- **Completeness**: every graded pair of the plan is the index of a cell. -/
theorem scheme_isComplete : F.scheme.IsComplete := by
  rintro ⟨B, j⟩ hBJ
  obtain ⟨hB, hj0, hjB⟩ := AmalgamationPlan.Plan.mem_gradedPlan.mp hBJ
  dsimp only at hj0 hjB
  have hcases : ∀ B ∈ Prop3.plan, B = ∅ ∨ B = {0} ∨ B = {1} ∨ B = {2} ∨ B = {0, 1} ∨
      B = {1, 2} ∨ B = Finset.univ := by decide
  rcases hcases B hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Finset.card_empty] at hjB; omega
  · rw [Finset.card_singleton] at hjB
    obtain rfl : j = 1 := by omega
    exact ⟨F.e (.inl .s0), by rw [cell_e]; rfl⟩
  · rw [Finset.card_singleton] at hjB
    obtain rfl : j = 1 := by omega
    exact ⟨F.e (.inl .s1), by rw [cell_e]; rfl⟩
  · rw [Finset.card_singleton] at hjB
    obtain rfl : j = 1 := by omega
    exact ⟨F.e (.inl .s2), by rw [cell_e]; rfl⟩
  · rw [show ({0, 1} : Finset (Fin 3)).card = 2 by decide] at hjB
    obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
    · exact ⟨F.e (.inl .p01a), by rw [cell_e]; rfl⟩
    · exact ⟨F.e (.inl .p01b), by rw [cell_e]; rfl⟩
  · rw [show ({1, 2} : Finset (Fin 3)).card = 2 by decide] at hjB
    obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
    · exact ⟨F.e (.inl .p12a), by rw [cell_e]; rfl⟩
    · exact ⟨F.e (.inl .p12b), by rw [cell_e]; rfl⟩
  · rw [Finset.card_univ, Fintype.card_fin] at hjB
    obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
    · exact ⟨F.e (.inr (.inl ⟨F.H₀, F.ne₁.choose_spec⟩)), by rw [cell_e]; rfl⟩
    · exact ⟨F.e (.inr (.inr (.inl ⟨F.s₀, F.ne₂.choose_spec⟩))), by rw [cell_e]; rfl⟩
    · exact ⟨F.e (.inr (.inr (.inr ⟨F.a₀, F.ne₃.choose_spec⟩))), by rw [cell_e]; rfl⟩

/-! ### Consistency: the constant proper values and the locality core -/

/-- Every row is constant on the grade-one proper cells. -/
theorem rowX_proper_const (x : F.X) {c c' : Prop3} (hc : c.gradeP ≤ 1) (hc' : c'.gradeP ≤ 1) :
    F.rowX x (.inl c) = F.rowX x (.inl c') := by
  rcases x with c₀ | H | s | a
  · rfl
  · rw [rowX_H_inl F H c hc, rowX_H_inl F H c' hc']; exact F.const₁ H.1 H.2 c c' hc hc'
  · rw [rowX_s_inl, rowX_s_inl]; exact F.const₂ s.1 s.2 c c' hc hc'
  · rw [rowX_a_inl, rowX_a_inl]
    change min _ _ = min _ _
    rw [F.const₃ a.1 a.2 c c' hc hc']

/-- Every row is `⊥` at a grade-two proper cell of its lower set. -/
theorem rowX_proper_bot (x : F.X) {c : Prop3} (hc : c.gradeP = 2)
    (hx : GradedLe (F.cellX (.inl c)) (F.cellX x)) : F.rowX x (.inl c) = ⊥ := by
  rcases x with c₀ | H | s | a
  · have h2 : c.gradeP ≤ c₀.gradeP := hx.2
    change (if c₀.gradeP ≤ 1 then F.v else ⊥) = ⊥
    rw [ite_eq_right (by omega)]
  · exfalso
    have h2 : c.gradeP ≤ 1 := hx.2
    omega
  · rw [rowX_s_inl]; exact F.bot₂ s.1 s.2 c hc
  · rw [rowX_a_inl]
    change min _ _ = ⊥
    rw [F.bot₃ a.1 a.2 c hc, min_eq_left bot_le]

/-- **The locality core**: for `y` below `x`, the row of `y` transforms to the row of `x` capped at
its value at `y`, along any indexing `ψ` of the lower set of `y`. -/
theorem locality_core (x y : F.X) (hxy : GradedLe (F.cellX y) (F.cellX x)) {D : Type*}
    (ψ : D → F.X) (hψ : ∀ d, GradedLe (F.cellX (ψ d)) (F.cellX y)) :
    TransformsTo (fun d => (F.cellX (ψ d)).2) (fun d => F.rowX y (ψ d))
      (fun d => min (F.rowX x (ψ d)) (F.rowX x y)) := by
  rcases y with c | H | s | a
  · -- a proper cell: constant-to-constant, or forced to `⊥`
    by_cases hc : c.gradeP ≤ 1
    · have hgr : ∀ d, (F.cellX (ψ d)).2 ≤ 1 := fun d => by
        obtain ⟨c', hd, -, hg⟩ := F.below_inl (hψ d)
        rw [hd]; exact hg.trans hc
      have hvis : SelfVis 1 (F.rowX x (.inl c)) :=
        (F.rowX_selfVis x (.inl c) hxy).mono c.gradeP_pos
      refine transformsTo_congr rfl ?_ ?_ (transformsTo_const_const hgr F.v_ne hvis)
      · funext d
        obtain ⟨c', hd, -, -⟩ := F.below_inl (hψ d)
        rw [hd]
        change F.v = if c.gradeP ≤ 1 then F.v else ⊥
        rw [ite_eq_left hc]
      · funext d
        obtain ⟨c', hd, -, hg⟩ := F.below_inl (hψ d)
        rw [hd, F.rowX_proper_const x (hg.trans hc) hc, min_self]
    · have hc2 : c.gradeP = 2 := by have := c.gradeP_le_two; omega
      have hbot : F.rowX x (.inl c) = ⊥ := F.rowX_proper_bot x hc2 hxy
      refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
      funext d
      rw [hbot, min_eq_right bot_le]
  · -- a level-one cell
    have hgr : ∀ d, (F.cellX (ψ d)).2 ≤ 1 := fun d => (hψ d).2
    have hg : (Low1.grade ∘ fun d => F.toLow1 (ψ d)) = fun d => (F.cellX (ψ d)).2 := by
      funext d
      have h := hgr d
      dsimp only [Function.comp_apply]
      rcases hd : ψ d with c' | H'' | s'' | a''
      · rw [hd] at h
        change Low1.grade (F.toLow1 (.inl c')) = c'.gradeP
        rw [toLow1_inl F c' h]; rfl
      · rfl
      · rw [hd] at h; exact absurd h (by decide : ¬ ((2 : ℕ) ≤ 1))
      · rw [hd] at h; exact absurd h (by decide : ¬ ((3 : ℕ) ≤ 1))
    rcases x with c₀ | H' | s' | a'
    · exact absurd hxy F.not_gradedLe_full_inl
    · exact transformsTo_congr hg rfl rfl ((Row1.same1 H.1 H'.1).reindex fun d => F.toLow1 (ψ d))
    · refine transformsTo_congr hg rfl ?_
        ((Core2.cross21 st s'.1 H.1).reindex fun d => F.toLow1 (ψ d))
      funext d
      have h := hgr d
      dsimp only [Function.comp_apply]
      rcases hd : ψ d with c' | H'' | s'' | a''
      · rw [hd] at h
        change min (s'.1.rowOn1 st (F.toLow1 (.inl c'))) _ = min (s'.1.F c') _
        rw [toLow1_inl F c' h]; rfl
      · rfl
      · rw [hd] at h; exact absurd h (by decide : ¬ ((2 : ℕ) ≤ 1))
      · rw [hd] at h; exact absurd h (by decide : ¬ ((3 : ℕ) ≤ 1))
    · refine transformsTo_congr hg rfl ?_
        ((CappedCore3.cross31C st a'.1 H.1).reindex fun d => F.toLow1 (ψ d))
      funext d
      have h := hgr d
      dsimp only [Function.comp_apply]
      rcases hd : ψ d with c' | H'' | s'' | a''
      · rw [hd] at h
        change min (a'.1.rowOn1 st (F.toLow1 (.inl c'))) _ =
          min (CappedCore3.expandedRow st a'.1 (.inl ⟨c', _⟩)) _
        rw [toLow1_inl F c' h, expandedRow_inl, rowX_a_H]; rfl
      · change min (a'.1.rowOn1 st (.inr H''.1)) _ =
          min (CappedCore3.expandedRow st a'.1 (.inr (.inl H''.1))) _
        rw [expandedRow_H, rowX_a_H]; rfl
      · rw [hd] at h; exact absurd h (by decide : ¬ ((2 : ℕ) ≤ 1))
      · rw [hd] at h; exact absurd h (by decide : ¬ ((3 : ℕ) ≤ 1))
  · -- a level-two cell
    have hgr : ∀ d, (F.cellX (ψ d)).2 ≤ 2 := fun d => (hψ d).2
    have hg : (Low2.grade ∘ fun d => F.toLow2 (ψ d)) = fun d => (F.cellX (ψ d)).2 := by
      funext d
      have h := hgr d
      dsimp only [Function.comp_apply]
      rcases hd : ψ d with c' | H'' | s'' | a''
      · rfl
      · rfl
      · rfl
      · rw [hd] at h; exact absurd h (by decide : ¬ ((3 : ℕ) ≤ 2))
    rcases x with c₀ | H' | s' | a'
    · exact absurd hxy F.not_gradedLe_full_inl
    · exact absurd hxy.2 (by decide : ¬ ((2 : ℕ) ≤ 1))
    · exact transformsTo_congr hg rfl rfl
        ((Core2.same2 st s.1 s'.1).reindex fun d => F.toLow2 (ψ d))
    · refine transformsTo_congr hg rfl ?_
        ((CappedCore3.cross32C st a'.1 s.1).reindex fun d => F.toLow2 (ψ d))
      funext d
      have h := hgr d
      dsimp only [Function.comp_apply]
      rcases hd : ψ d with c' | H'' | s'' | a''
      · change min (a'.1.rowOn2 st (.inl ⟨c', _⟩)) _ =
          min (CappedCore3.expandedRow st a'.1 (.inl ⟨c', _⟩)) _
        rw [expandedRow_inl, rowX_a_s]; rfl
      · change min (a'.1.rowOn2 st (.inr (.inl H''.1))) _ =
          min (CappedCore3.expandedRow st a'.1 (.inr (.inl H''.1))) _
        rw [expandedRow_H, rowX_a_s]; rfl
      · change min (a'.1.rowOn2 st (.inr (.inr s''.1))) _ =
          min (CappedCore3.expandedRow st a'.1 (.inr (.inr (.inl s''.1)))) _
        rw [expandedRow_s, rowX_a_s]; rfl
      · rw [hd] at h; exact absurd h (by decide : ¬ ((3 : ℕ) ≤ 2))
  · -- a level-three (capped) cell
    have hg : ((fun d => Low3.grade (CappedCore3.project d)) ∘ fun d => F.toLow3 (ψ d)) =
        fun d => (F.cellX (ψ d)).2 := by
      funext d
      dsimp only [Function.comp_apply]
      rcases ψ d with c' | H'' | s'' | a'' <;> rfl
    rcases x with c₀ | H' | s' | b
    · exact absurd hxy F.not_gradedLe_full_inl
    · exact absurd hxy.2 (by decide : ¬ ((3 : ℕ) ≤ 1))
    · exact absurd hxy.2 (by decide : ¬ ((3 : ℕ) ≤ 2))
    · refine transformsTo_congr hg rfl ?_
        ((CappedCore3.expanded_same3 st a.1 b.1).reindex fun d => F.toLow3 (ψ d))
      funext d
      dsimp only [Function.comp_apply]
      rw [rowX_a_a]
      rfl

/-- **The availability core**: for `y, z` below `x` with the scope of `y` inside that of `z` and
equal grades, a cell `w` of the index of `z` below `x` dominates `y` in the row of `x`. -/
theorem availability_core (x y z : F.X) (hy : GradedLe (F.cellX y) (F.cellX x))
    (hz : GradedLe (F.cellX z) (F.cellX x)) (hs : (F.cellX y).1 ⊆ (F.cellX z).1)
    (hg : (F.cellX y).2 = (F.cellX z).2) :
    ∃ w : F.X, GradedLe (F.cellX w) (F.cellX x) ∧ F.cellX w = F.cellX z ∧
      F.rowX x y ≤ F.rowX x w := by
  rcases z with c | H | s | a
  · -- a proper target: `y` is proper of the same grade; the rows agree there
    rcases y with c' | H' | s' | a'
    · refine ⟨.inl c, hz, rfl, le_of_eq ?_⟩
      have hg' : c'.gradeP = c.gradeP := hg
      by_cases hc : c.gradeP ≤ 1
      · exact F.rowX_proper_const x (by rw [hg']; exact hc) hc
      · have hc2 : c.gradeP = 2 := by have := c.gradeP_le_two; omega
        have hs' : c'.scope ⊆ c.scope := hs
        rw [Prop3.eq_of_grade_two hc2 (hg'.trans hc2) hs']
    all_goals exact absurd (Finset.univ_subset_iff.mp hs) c.scope_ne_univ
  · -- a level-one target
    rcases y with c' | H' | s' | a'
    · have hc : c'.gradeP ≤ 1 := hg.le
      rcases x with c₀ | H'' | s'' | a''
      · exact absurd hz F.not_gradedLe_full_inl
      · refine ⟨.inr (.inl H''), ⟨Finset.subset_univ _, le_rfl⟩, rfl, ?_⟩
        rw [rowX_H_inl F H'' c' hc, rowX_H_H, meet₁_self]
        exact H''.1.G_le c'
      · refine ⟨.inr (.inl ⟨s''.1.wit st, F.wit₂ s''.1 s''.2⟩),
          ⟨Finset.subset_univ _, (by decide : (1 : ℕ) ≤ 2)⟩, rfl, ?_⟩
        rw [rowX_s_inl, rowX_s_H, Core2.rho_wit]
        exact s''.1.F_le c'
      · refine ⟨.inr (.inl ⟨witness1 st.hT a''.1.base.F (a''.1.base.orderly st),
          F.wit₃₁ a''.1 a''.2⟩), ⟨Finset.subset_univ _, (by decide : (1 : ℕ) ≤ 3)⟩, rfl, ?_⟩
        rw [rowX_a_inl, rowX_a_H]
        change min _ _ ≤ min _ _
        rw [Core3.rho1_wit1]
        exact min_le_min (a''.1.base.F_le c') le_rfl
    · exact ⟨.inr (.inl H'), hy, rfl, le_rfl⟩
    · exact absurd hg (by decide : (2 : ℕ) ≠ 1)
    · exact absurd hg (by decide : (3 : ℕ) ≠ 1)
  · -- a level-two target
    rcases y with c' | H' | s' | a'
    · have hc : c'.gradeP = 2 := hg
      refine ⟨.inr (.inr (.inl s)), hz, rfl, ?_⟩
      rw [F.rowX_proper_bot x hc hy]
      exact bot_le
    · exact absurd hg (by decide : (1 : ℕ) ≠ 2)
    · exact ⟨.inr (.inr (.inl s')), hy, rfl, le_rfl⟩
    · exact absurd hg (by decide : (3 : ℕ) ≠ 2)
  · -- a level-three target
    rcases y with c' | H' | s' | a'
    · have hc : c'.gradeP = 3 := hg
      exact absurd hc (by have := c'.gradeP_le_two; omega)
    · exact absurd hg (by decide : (1 : ℕ) ≠ 3)
    · exact absurd hg (by decide : (2 : ℕ) ≠ 3)
    · exact ⟨.inr (.inr (.inr a')), hy, rfl, le_rfl⟩

theorem below_gradedLe {y : F.X} (d : F.scheme.below (F.scheme.cell (F.e y))) :
    GradedLe (F.cellX (F.e.symm d.1)) (F.cellX y) := by
  obtain ⟨i, hi⟩ := d
  rw [cell_e] at hi
  exact hi

/-- **Consistency** (Def. 2.5.12): every row respects the restricted semantics. -/
theorem rows_isConsistent : F.rows.IsConsistent := by
  intro Sig
  obtain ⟨x, rfl⟩ := F.e.surjective Sig
  have hx : F.e.symm (F.e x) = x := F.e.symm_apply_apply x
  refine ⟨F.rows.orderly (F.e x), ?_, ?_⟩
  · rintro ⟨i, hi⟩
    obtain ⟨y, rfl⟩ := F.e.surjective i
    have hy : F.e.symm (F.e y) = y := F.e.symm_apply_apply y
    have hxy : GradedLe (F.cellX y) (F.cellX x) := by rwa [cell_e, cell_e] at hi
    have key := F.locality_core x y hxy (fun d : F.scheme.below (F.scheme.cell (F.e y)) =>
      F.e.symm d.1) F.below_gradedLe
    refine transformsTo_congr rfl ?_ ?_ key
    · funext d
      change F.rowX y (F.e.symm d.1) = F.rowX (F.e.symm (F.e y)) (F.e.symm d.1)
      rw [hy]
    · funext d
      change min (F.rowX x (F.e.symm d.1)) (F.rowX x y) =
        min (F.rowX (F.e.symm (F.e x)) (F.e.symm d.1))
          (F.rowX (F.e.symm (F.e x)) (F.e.symm (F.e y)))
      rw [hx, hy]
  · rintro ⟨i, hi⟩ ⟨i', hi'⟩ hs hg
    obtain ⟨y, rfl⟩ := F.e.surjective i
    obtain ⟨z, rfl⟩ := F.e.surjective i'
    have hy : F.e.symm (F.e y) = y := F.e.symm_apply_apply y
    have hz : F.e.symm (F.e z) = z := F.e.symm_apply_apply z
    have hy' : GradedLe (F.cellX y) (F.cellX x) := by rwa [cell_e, cell_e] at hi
    have hz' : GradedLe (F.cellX z) (F.cellX x) := by rwa [cell_e, cell_e] at hi'
    have hs' : (F.cellX y).1 ⊆ (F.cellX z).1 := by rwa [scope_eq, scope_eq, hy, hz] at hs
    have hg' : (F.cellX y).2 = (F.cellX z).2 := by rwa [grade_eq, grade_eq, hy, hz] at hg
    obtain ⟨w, hw₁, hw₂, hw₃⟩ := F.availability_core x y z hy' hz' hs' hg'
    refine ⟨⟨F.e w, by rw [cell_e, cell_e]; exact hw₁⟩, by rw [cell_e, cell_e]; exact hw₂, ?_⟩
    change F.rowX (F.e.symm (F.e x)) (F.e.symm (F.e y)) ≤
      F.rowX (F.e.symm (F.e x)) (F.e.symm (F.e w))
    rw [hx, hy, F.e.symm_apply_apply w]
    exact hw₃

end Family

end Assembly

/-! ## Bountifulness for the assembled scheme -/

section Bountiful

variable {T : ℕ} {st : Setting Prop3.gradeP T} (F : Family st)

namespace Family

/-- The cell of the scheme carried by `x`, in a lower set. -/
noncomputable def cellOf {BJ : Finset (Fin 3) × ℕ} (x : F.X) (h : GradedLe (F.cellX x) BJ) :
    F.scheme.below BJ := ⟨F.e x, by rw [cell_e]; exact h⟩

theorem cellOf_val {BJ : Finset (Fin 3) × ℕ} (x : F.X) (h : GradedLe (F.cellX x) BJ) :
    (F.cellOf x h).1 = F.e x := rfl

/-- Graded indices determine proper cells. -/
theorem eq_inl_of_cellX_eq {w : F.X} {c : Prop3} (h : F.cellX w = F.cellX (.inl c)) :
    w = .inl c := by
  rcases w with c' | H | s | a
  · have : (c'.scope, c'.gradeP) = (c.scope, c.gradeP) := h
    have hinj : ∀ c c' : Prop3, (c'.scope, c'.gradeP) = (c.scope, c.gradeP) → c' = c := by decide
    rw [hinj c c' this]
  all_goals
    exact absurd (congrArg Prod.fst h) (fun e => c.scope_ne_univ e.symm)

/-- Every cell of a lower set is `cellOf` its underlying `X`-cell. -/
theorem eq_cellOf {BJ : Finset (Fin 3) × ℕ} (d : F.scheme.below BJ) :
    d = F.cellOf (F.e.symm d.1) (by rw [← cell_eq]; exact d.2) := by
  apply Subtype.ext
  rw [cellOf_val, Equiv.apply_symm_apply]

/-- A respecting labelling of a lower set containing a grade-one pair cell takes the same value at
the pair cell and at any grade-one proper cell inside its scope: locality at the pair cell (a
nonbottom constant source) forces the target to be constant, and availability lifts the smaller
cell to the pair cell (the unique cell of its graded index). -/
theorem respects_pair_const {BJ : Finset (Fin 3) × ℕ} {r : F.scheme.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow F.rows BJ r) {c₁ x : Prop3} (hc₁ : c₁.gradeP = 1)
    (hx : x.gradeP = 1) (hxs : x.scope ⊆ c₁.scope) (h₁ : GradedLe (F.cellX (.inl c₁)) BJ) :
    r (F.cellOf (.inl x) ⟨hxs.trans h₁.1,
        by rw [show (F.cellX (.inl x)).2 = 1 from hx]; exact hc₁ ▸ h₁.2⟩) =
      r (F.cellOf (.inl c₁) h₁) := by
  set hx' : GradedLe (F.cellX (.inl x)) BJ :=
    ⟨hxs.trans h₁.1, by rw [show (F.cellX (.inl x)).2 = 1 from hx]; exact hc₁ ▸ h₁.2⟩
  have hxc : GradedLe (F.cellX (.inl x)) (F.cellX (.inl c₁)) :=
    ⟨hxs, by change x.gradeP ≤ c₁.gradeP; rw [hx, hc₁]⟩
  apply le_antisymm
  · -- availability lifts `x` to the (unique) cell of index `c₁`
    obtain ⟨Xi, hcell, hle⟩ := hr.availability (F.cellOf (.inl x) hx') (F.cellOf (.inl c₁) h₁)
      (by rw [scope_eq, scope_eq, cellOf_val, cellOf_val, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]; exact hxs)
      (by rw [grade_eq, grade_eq, cellOf_val, cellOf_val, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]; change x.gradeP = c₁.gradeP; rw [hx, hc₁])
    have hXi : Xi = F.cellOf (.inl c₁) h₁ := by
      have h1 : F.cellX (F.e.symm Xi.1) = F.cellX (.inl c₁) := by
        have := hcell
        rw [cellOf_val, cell_e] at this
        exact this
      rw [F.eq_cellOf Xi]
      apply Subtype.ext
      rw [cellOf_val, cellOf_val, F.eq_inl_of_cellX_eq h1]
    rw [hXi] at hle
    exact hle
  · -- locality at `c₁`: constant source, hence constant target
    obtain ⟨g, σ, -, -, -, -, -, hrow⟩ := hr.locality (F.cellOf (.inl c₁) h₁)
    have e₁ : min (r (F.cellOf (.inl x) hx')) (r (F.cellOf (.inl c₁) h₁)) =
        min (σ (F.rowX (F.e.symm (F.e (.inl c₁))) (F.e.symm (F.e (.inl x)))))
          (g (F.scheme.grade (F.e (.inl x)))) :=
      hrow ⟨F.e (.inl x), by
        change GradedLe (F.scheme.cell (F.e (.inl x))) (F.scheme.cell (F.e (.inl c₁)))
        rw [cell_e, cell_e]; exact hxc⟩
    have e₂ : min (r (F.cellOf (.inl c₁) h₁)) (r (F.cellOf (.inl c₁) h₁)) =
        min (σ (F.rowX (F.e.symm (F.e (.inl c₁))) (F.e.symm (F.e (.inl c₁)))))
          (g (F.scheme.grade (F.e (.inl c₁)))) :=
      hrow ⟨F.e (.inl c₁), by
        change GradedLe (F.scheme.cell (F.e (.inl c₁))) (F.scheme.cell (F.e (.inl c₁)))
        exact GradedLe.refl _⟩
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at e₁
    rw [Equiv.symm_apply_apply] at e₂
    have hsrc : F.rowX (.inl c₁) (.inl x) = F.rowX (.inl c₁) (.inl c₁) := rfl
    have hgr : F.scheme.grade (F.e (.inl x)) = F.scheme.grade (F.e (.inl c₁)) := by
      rw [grade_eq, grade_eq, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      change x.gradeP = c₁.gradeP
      rw [hx, hc₁]
    rw [hsrc, hgr, ← e₂, min_self] at e₁
    exact min_eq_right_iff.mp e₁

/-- A respecting labelling is `⊥` at every grade-two proper cell of its lower set (the mute row). -/
theorem respects_bot_grade_two {BJ : Finset (Fin 3) × ℕ} {r : F.scheme.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow F.rows BJ r) {c : Prop3} (hc : c.gradeP = 2)
    (h : GradedLe (F.cellX (.inl c)) BJ) : r (F.cellOf (.inl c) h) = ⊥ := by
  obtain ⟨g, σ, -, -, hbot, -, -, hrow⟩ := hr.locality (F.cellOf (.inl c) h)
  have e : min (r (F.cellOf (.inl c) h)) (r (F.cellOf (.inl c) h)) =
      min (σ (F.rowX (F.e.symm (F.e (.inl c))) (F.e.symm (F.e (.inl c)))))
        (g (F.scheme.grade (F.e (.inl c)))) :=
    hrow ⟨F.e (.inl c), by
      change GradedLe (F.scheme.cell (F.e (.inl c))) (F.scheme.cell (F.e (.inl c)))
      exact GradedLe.refl _⟩
  rw [Equiv.symm_apply_apply, min_self] at e
  have hsrc : F.rowX (.inl c) (.inl c) = ⊥ := by
    change (if c.gradeP ≤ 1 then F.v else ⊥) = ⊥
    rw [ite_eq_right (by omega)]
  rw [hsrc, hbot, min_eq_left bot_le] at e
  exact e

/-- **The remaining obligation**: the instances of bountifulness from a proper-scope pair to a
full-scope pair.  For the constant proper part every respecting labelling of a proper lower set
is a constant `u'` on its grade-one cells; the obligation is a **relabelling of the full-scope
cells**: given `q` respecting `E⟨A,j⟩` (constant `u` on the grade-one proper cells) and `u'`
with `u' ∧ γ = u ∧ γ`, produce `q'` respecting `E⟨A,j⟩` with proper value `u'` and
`q' ∧ γ = q ∧ γ`.  When `u < γ` this is `q' = q` (then `u' = u`); the content is the case
`γ ≤ u, u'`, where the full-scope labels above `γ` must be re-fitted to the new proper value. -/
def ProperToFull : Prop :=
  ∀ (CI : Finset (Fin 3) × ℕ) (j : ℕ), CI ∈ AmalgamationPlan.Plan.gradedPlan Prop3.plan →
    CI.1 ≠ Finset.univ → (Finset.univ, j) ∈ AmalgamationPlan.Plan.gradedPlan Prop3.plan →
    (h : GradedLe CI (Finset.univ, j)) →
    ∀ (p : F.scheme.below CI → ExtOrd) (q : F.scheme.below (Finset.univ, j) → ExtOrd)
      (γ : ExtOrd), RespectsSemanticsBelow F.rows CI p →
      RespectsSemanticsBelow F.rows (Finset.univ, j) q →
      extVisibilityReplace γ j j = γ →
      (∀ d : F.scheme.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) →
      ∃ q' : F.scheme.below (Finset.univ, j) → ExtOrd,
        RespectsSemanticsBelow F.rows (Finset.univ, j) q' ∧
        (∀ d, min (q' d) γ = min (q d) γ) ∧
        (∀ d : F.scheme.below CI, q' (CellScheme.below.mono h d) = p d)

/-- Every cell of a proper lower set is a proper cell. -/
theorem exists_inl_of_proper {B : Finset (Fin 3)} (hB : B ≠ Finset.univ) {j : ℕ}
    (d : F.scheme.below (B, j)) : ∃ c : Prop3, F.e.symm d.1 = .inl c := by
  have h : GradedLe (F.cellX (F.e.symm d.1)) (B, j) := by rw [← cell_eq]; exact d.2
  rcases hx : F.e.symm d.1 with c | H | s' | a
  · exact ⟨c, rfl⟩
  all_goals
    rw [hx] at h
    exact absurd (Finset.univ_subset_iff.mp h.1) hB

/-- **Respecting labellings of a proper lower set are constant on its grade-one cells.** -/
theorem respects_proper_const {B : Finset (Fin 3)} (hBp : B ∈ Prop3.plan) (hB : B ≠ Finset.univ)
    {j : ℕ} {r : F.scheme.below (B, j) → ExtOrd} (hr : RespectsSemanticsBelow F.rows (B, j) r)
    {c c' : Prop3} (hc : c.gradeP = 1) (hc' : c'.gradeP = 1)
    (h : GradedLe (F.cellX (.inl c)) (B, j)) (h' : GradedLe (F.cellX (.inl c')) (B, j)) :
    r (F.cellOf (.inl c) h) = r (F.cellOf (.inl c') h') := by
  rcases Prop3.grade_one_connected B hBp hB c c' hc hc' h.1 h'.1 with
    rfl | ⟨c₁, hc₁, hs₁, hcs, hcs'⟩
  · rfl
  · have h₁ : GradedLe (F.cellX (.inl c₁)) (B, j) :=
      ⟨hs₁, by change c₁.gradeP ≤ j; rw [hc₁]; exact hc ▸ h.2⟩
    rw [F.respects_pair_const hr hc₁ hc hcs h₁, F.respects_pair_const hr hc₁ hc' hcs' h₁]

/-- **Respecting labellings of a full-scope lower set are constant on the grade-one proper
cells** (the two pair cells connect the three singletons). -/
theorem respects_full_const {j : ℕ} {r : F.scheme.below (Finset.univ, j) → ExtOrd}
    (hr : RespectsSemanticsBelow F.rows (Finset.univ, j) r) (hj : 1 ≤ j)
    {c c' : Prop3} (hc : c.gradeP = 1) (hc' : c'.gradeP = 1) :
    r (F.cellOf (.inl c) ⟨Finset.subset_univ _, by change c.gradeP ≤ j; omega⟩) =
      r (F.cellOf (.inl c') ⟨Finset.subset_univ _, by change c'.gradeP ≤ j; omega⟩) := by
  have h01 : GradedLe (F.cellX (.inl .p01a)) (Finset.univ, j) := ⟨Finset.subset_univ _, hj⟩
  have h12 : GradedLe (F.cellX (.inl .p12a)) (Finset.univ, j) := ⟨Finset.subset_univ _, hj⟩
  -- every grade-one cell agrees with `s1`
  have key : ∀ c : Prop3, (hc : c.gradeP = 1) →
      r (F.cellOf (.inl c) ⟨Finset.subset_univ _, by change c.gradeP ≤ j; omega⟩) =
        r (F.cellOf (.inl .s1) ⟨Finset.subset_univ _, hj⟩) := by
    intro c hc
    rcases Prop3.grade_one_in_pair c hc with hs | hs
    · exact (F.respects_pair_const hr rfl hc hs h01).trans
        (F.respects_pair_const hr rfl rfl (by decide) h01).symm
    · exact (F.respects_pair_const hr rfl hc hs h12).trans
        (F.respects_pair_const hr rfl rfl (by decide) h12).symm
  rw [key c hc, key c' hc']

/-- The constant labelling of a lower set: `u` at the grade-one cells, `⊥` at the others. -/
noncomputable def constLabel (BJ : Finset (Fin 3) × ℕ) (u : ExtOrd) : F.scheme.below BJ → ExtOrd :=
  fun d => if (F.cellX (F.e.symm d.1)).2 ≤ 1 then u else ⊥

/-- **Constant labellings respect the constant proper part** on every proper lower set. -/
theorem respects_constLabel {B : Finset (Fin 3)} (hB : B ≠ Finset.univ) (j : ℕ) {u : ExtOrd}
    (hu : SelfVis 1 u) : RespectsSemanticsBelow F.rows (B, j) (F.constLabel (B, j) u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    have : SelfVis (F.cellX (F.e.symm d.1)).2 (F.constLabel (B, j) u d) := by
      change SelfVis (F.cellX (F.e.symm d.1)).2 (if (F.cellX (F.e.symm d.1)).2 ≤ 1 then u else ⊥)
      split_ifs with hd
      · exact hu.mono hd
      · exact selfVis_bot _
    exact this.symm
  · intro Sig
    obtain ⟨c, hc⟩ := F.exists_inl_of_proper hB Sig
    have hSig : ∀ d : F.scheme.below (F.scheme.cell Sig.1),
        (F.cellX (F.e.symm d.1)).2 ≤ c.gradeP := fun d => by
      have h2 : (F.cellX (F.e.symm d.1)).2 ≤ (F.cellX (F.e.symm Sig.1)).2 := d.2.2
      rw [hc] at h2
      exact h2
    by_cases hc1 : c.gradeP ≤ 1
    · have hgr : ∀ d : F.scheme.below (F.scheme.cell Sig.1), F.scheme.grade d.1 ≤ 1 :=
        fun d => (hSig d).trans hc1
      refine transformsTo_congr rfl ?_ ?_ (transformsTo_const_const hgr F.v_ne hu)
      · funext d
        change F.v = F.rowX (F.e.symm Sig.1) (F.e.symm d.1)
        rw [hc]
        change F.v = if c.gradeP ≤ 1 then F.v else ⊥
        rw [ite_eq_left hc1]
      · funext d
        change u = min (if (F.cellX (F.e.symm d.1)).2 ≤ 1 then u else ⊥)
          (if (F.cellX (F.e.symm Sig.1)).2 ≤ 1 then u else ⊥)
        rw [ite_eq_left ((hSig d).trans hc1), hc]
        change u = min u (if c.gradeP ≤ 1 then u else ⊥)
        rw [ite_eq_left hc1, min_self]
    · refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
      funext d
      change ⊥ = min (if (F.cellX (F.e.symm d.1)).2 ≤ 1 then u else ⊥)
        (if (F.cellX (F.e.symm Sig.1)).2 ≤ 1 then u else ⊥)
      rw [hc]
      change ⊥ = min (if (F.cellX (F.e.symm d.1)).2 ≤ 1 then u else ⊥)
        (if c.gradeP ≤ 1 then u else ⊥)
      rw [ite_eq_right hc1, min_eq_right bot_le]
  · intro Sig Xi₀ hs hg
    refine ⟨Xi₀, rfl, le_of_eq ?_⟩
    change (if (F.cellX (F.e.symm Sig.1)).2 ≤ 1 then u else ⊥) =
      if (F.cellX (F.e.symm Xi₀.1)).2 ≤ 1 then u else ⊥
    have : (F.cellX (F.e.symm Sig.1)).2 = (F.cellX (F.e.symm Xi₀.1)).2 := hg
    rw [this]

/-- **Bountifulness between proper-scope pairs**: the extension is the constant labelling at the
grade-one value of `p`. -/
theorem bountiful_proper {CI BJ : Finset (Fin 3) × ℕ}
    (hCI : CI ∈ AmalgamationPlan.Plan.gradedPlan Prop3.plan)
    (hBJ : BJ ∈ AmalgamationPlan.Plan.gradedPlan Prop3.plan) (h : GradedLe CI BJ)
    (hB : BJ.1 ≠ Finset.univ)
    (p : F.scheme.below CI → ExtOrd) (q : F.scheme.below BJ → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow F.rows CI p) (hq : RespectsSemanticsBelow F.rows BJ q)
    (hagree : ∀ d : F.scheme.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : F.scheme.below BJ → ExtOrd, RespectsSemanticsBelow F.rows BJ q' ∧
      (∀ d : F.scheme.below BJ, min (q' d) γ = min (q d) γ) ∧
      (∀ d : F.scheme.below CI, q' (CellScheme.below.mono h d) = p d) := by
  obtain ⟨B, j⟩ := BJ
  obtain ⟨C, i⟩ := CI
  have hBp : B ∈ Prop3.plan := (AmalgamationPlan.Plan.mem_gradedPlan.mp hBJ).1
  obtain ⟨hCp, hi0, hiC⟩ := AmalgamationPlan.Plan.mem_gradedPlan.mp hCI
  dsimp only at hi0 hiC hB
  have hC : C ≠ Finset.univ := fun e => hB (Finset.univ_subset_iff.mp (e ▸ h.1))
  -- a point of the smaller face, and its singleton cell
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (lt_of_lt_of_le hi0 hiC)
  have hxC : GradedLe (F.cellX (.inl (Prop3.single x))) (C, i) := by
    refine ⟨?_, ?_⟩
    · change (Prop3.single x).scope ⊆ C
      rw [Prop3.scope_single]; exact Finset.singleton_subset_iff.mpr hx
    · change (Prop3.single x).gradeP ≤ i
      rw [Prop3.gradeP_single]; exact hi0
  set u' := p (F.cellOf (.inl (Prop3.single x)) hxC) with hu'
  have hu'vis : SelfVis 1 u' := by
    have h1 : SelfVis (F.scheme.grade (F.e (.inl (Prop3.single x)))) u' :=
      (hp.orderly (F.cellOf (.inl (Prop3.single x)) hxC)).symm
    rw [grade_eq, Equiv.symm_apply_apply] at h1
    have h2 : (F.cellX (.inl (Prop3.single x))).2 = 1 := Prop3.gradeP_single x
    rw [h2] at h1
    exact h1
  -- the values of `p` and `q` on their lower sets
  have hp_val : ∀ d : F.scheme.below (C, i), p d = F.constLabel (C, i) u' d := by
    intro d
    obtain ⟨c, hc⟩ := F.exists_inl_of_proper hC d
    have hd : GradedLe (F.cellX (.inl c)) (C, i) := by rw [← hc, ← cell_eq]; exact d.2
    have hd_eq : d = F.cellOf (.inl c) hd := by
      apply Subtype.ext; rw [cellOf_val, ← hc, Equiv.apply_symm_apply]
    change p d = if (F.cellX (F.e.symm d.1)).2 ≤ 1 then u' else ⊥
    rw [hc, hd_eq]
    change p (F.cellOf (.inl c) hd) = if c.gradeP ≤ 1 then u' else ⊥
    split_ifs with hc1
    · have hc1' : c.gradeP = 1 := by have := c.gradeP_pos; omega
      rw [hu']
      exact F.respects_proper_const hCp hC hp hc1' (Prop3.gradeP_single x) hd hxC
    · exact F.respects_bot_grade_two hp (by have := c.gradeP_le_two; omega) hd
  have hq_val : ∀ d : F.scheme.below (B, j), q d =
      F.constLabel (B, j)
        (q (CellScheme.below.mono h (F.cellOf (.inl (Prop3.single x)) hxC))) d := by
    intro d
    obtain ⟨c, hc⟩ := F.exists_inl_of_proper hB d
    have hd : GradedLe (F.cellX (.inl c)) (B, j) := by rw [← hc, ← cell_eq]; exact d.2
    have hd_eq : d = F.cellOf (.inl c) hd := by
      apply Subtype.ext; rw [cellOf_val, ← hc, Equiv.apply_symm_apply]
    change q d = if (F.cellX (F.e.symm d.1)).2 ≤ 1 then _ else ⊥
    rw [hc, hd_eq]
    change q (F.cellOf (.inl c) hd) = if c.gradeP ≤ 1 then _ else ⊥
    have hxB : GradedLe (F.cellX (.inl (Prop3.single x))) (B, j) := hxC.trans h
    have e' : CellScheme.below.mono h (F.cellOf (.inl (Prop3.single x)) hxC) =
        F.cellOf (.inl (Prop3.single x)) hxB := rfl
    rw [e']
    split_ifs with hc1
    · have hc1' : c.gradeP = 1 := by have := c.gradeP_pos; omega
      exact F.respects_proper_const hBp hB hq hc1' (Prop3.gradeP_single x) hd hxB
    · exact F.respects_bot_grade_two hq (by have := c.gradeP_le_two; omega) hd
  refine ⟨F.constLabel (B, j) u', F.respects_constLabel hB j hu'vis, ?_, ?_⟩
  · intro d
    rw [hq_val d]
    change min (if (F.cellX (F.e.symm d.1)).2 ≤ 1 then u' else ⊥) γ =
      min (if (F.cellX (F.e.symm d.1)).2 ≤ 1 then _ else ⊥) γ
    split_ifs
    · have := hagree (F.cellOf (.inl (Prop3.single x)) hxC)
      rw [this]
    · rfl
  · intro d
    rw [hp_val d]
    rfl

/-- **Bountifulness from the remaining obligation**: full-scope pairs by `bountiful_full_scope`,
proper-scope pairs by `bountiful_proper`, and proper-to-full by the hypothesis. -/
theorem isBountiful_of_properToFull (H : F.ProperToFull) : F.rows.IsBountiful := by
  intro CI BJ hCI hBJ h hne p q γ hp hq hγ hagree
  by_cases hB : BJ.1 = Finset.univ
  · by_cases hC : CI.1 = Finset.univ
    · obtain ⟨B, j⟩ := BJ
      obtain ⟨C, i⟩ := CI
      dsimp only at hB hC
      subst hB hC
      exact bountiful_full_scope F.rows h p q γ hp hq hγ hagree
    · obtain ⟨B, j⟩ := BJ
      dsimp only at hB
      subst hB
      exact H CI j hCI hC hBJ h p q γ hp hq hγ hagree
  · exact F.bountiful_proper hCI hBJ h hB p q γ hp hq hagree

/-- **The assembled domain with its associated semantics**, conditional on the remaining
proper-to-full bountifulness obligation. -/
noncomputable def toSemScheme (H : F.ProperToFull) : SemScheme 3 where
  scheme := F.scheme
  rows := F.rows
  rows_coded := F.rows_isCoded
  consistent := F.rows_isConsistent
  bountiful := F.isBountiful_of_properToFull H
  complete := F.scheme_isComplete

/-- **The remaining obligation, sharpened — the relabelling lemma.**  For a full-scope lower set
`D⟨A,j⟩`, a respecting labelling `q`, a cap `γ` self-visible at `j`, and a new grade-one proper
value `u'` (self-visible at one) agreeing with the old one below `γ`: a respecting `q'` agreeing
with `q` below `γ` and taking the value `u'` at the singleton cell `s0` (hence, by
`respects_full_const`, at every grade-one proper cell).  Only the case `γ ≤ u, u'` has content. -/
def Relabel : Prop :=
  ∀ (j : ℕ) (hj : 1 ≤ j), j ≤ 3 →
    ∀ (q : F.scheme.below (Finset.univ, j) → ExtOrd),
      RespectsSemanticsBelow F.rows (Finset.univ, j) q →
      ∀ (γ u' : ExtOrd), extVisibilityReplace γ j j = γ → SelfVis 1 u' →
        min u' γ = min (q (F.cellOf (.inl .s0) ⟨Finset.subset_univ _, hj⟩)) γ →
        ∃ q' : F.scheme.below (Finset.univ, j) → ExtOrd,
          RespectsSemanticsBelow F.rows (Finset.univ, j) q' ∧
          (∀ d, min (q' d) γ = min (q d) γ) ∧
          q' (F.cellOf (.inl .s0) ⟨Finset.subset_univ _, hj⟩) = u'

/-- **The reduction**: the relabelling lemma gives every proper-to-full instance of bountifulness
(the constant proper part forces `p` to be its grade-one constant and `⊥` at grade two). -/
theorem properToFull_of_relabel (H : F.Relabel) : F.ProperToFull := by
  intro CI j hCI hC hj h p q γ hp hq hγ hagree
  obtain ⟨C, i⟩ := CI
  obtain ⟨hCp, hi0, hiC⟩ := AmalgamationPlan.Plan.mem_gradedPlan.mp hCI
  obtain ⟨-, hj0, hj3⟩ := AmalgamationPlan.Plan.mem_gradedPlan.mp hj
  dsimp only at hCp hi0 hiC hC hj0 hj3
  rw [Finset.card_univ, Fintype.card_fin] at hj3
  have hj1 : 1 ≤ j := hj0
  -- the singleton cell of a point of `C`
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (lt_of_lt_of_le hi0 hiC)
  have hxC : GradedLe (F.cellX (.inl (Prop3.single x))) (C, i) := by
    refine ⟨?_, ?_⟩
    · change (Prop3.single x).scope ⊆ C
      rw [Prop3.scope_single]; exact Finset.singleton_subset_iff.mpr hx
    · change (Prop3.single x).gradeP ≤ i
      rw [Prop3.gradeP_single]; exact hi0
  set u' := p (F.cellOf (.inl (Prop3.single x)) hxC) with hu'
  have hu'vis : SelfVis 1 u' := by
    have h1 : SelfVis (F.scheme.grade (F.e (.inl (Prop3.single x)))) u' :=
      (hp.orderly (F.cellOf (.inl (Prop3.single x)) hxC)).symm
    rw [grade_eq, Equiv.symm_apply_apply] at h1
    have h2 : (F.cellX (.inl (Prop3.single x))).2 = 1 := Prop3.gradeP_single x
    rw [h2] at h1
    exact h1
  have hs0 : GradedLe (F.cellX (.inl .s0)) (Finset.univ, j) := ⟨Finset.subset_univ _, hj1⟩
  -- agreement transported to `s0` through the constancy of `q`
  have hag : min u' γ = min (q (F.cellOf (.inl .s0) hs0)) γ := by
    have e := hagree (F.cellOf (.inl (Prop3.single x)) hxC)
    have e' : CellScheme.below.mono h (F.cellOf (.inl (Prop3.single x)) hxC) =
        F.cellOf (.inl (Prop3.single x)) (hxC.trans h) := rfl
    rw [e', F.respects_full_const hq hj1 (c' := Prop3.s0) (Prop3.gradeP_single x) rfl] at e
    exact e.symm
  obtain ⟨q', hq', hq'γ, hq's0⟩ := H j hj1 hj3 q hq γ u' hγ hu'vis hag
  refine ⟨q', hq', hq'γ, ?_⟩
  intro d
  obtain ⟨c, hc⟩ := F.exists_inl_of_proper hC d
  have hd : GradedLe (F.cellX (.inl c)) (C, i) := by rw [← hc, ← cell_eq]; exact d.2
  have hd_eq : d = F.cellOf (.inl c) hd := by
    apply Subtype.ext; rw [cellOf_val, ← hc, Equiv.apply_symm_apply]
  rw [hd_eq]
  have e' : CellScheme.below.mono h (F.cellOf (.inl c) hd) = F.cellOf (.inl c) (hd.trans h) := rfl
  rw [e']
  by_cases hc1 : c.gradeP ≤ 1
  · have hc1' : c.gradeP = 1 := by have := c.gradeP_pos; omega
    rw [F.respects_full_const hq' hj1 (c' := Prop3.s0) hc1' rfl, hq's0, hu']
    exact F.respects_proper_const hCp hC hp (Prop3.gradeP_single x) hc1' hxC hd
  · have hc2 : c.gradeP = 2 := by have := c.gradeP_le_two; omega
    rw [F.respects_bot_grade_two hq' hc2 (hd.trans h), F.respects_bot_grade_two hp hc2 hd]

/-- **The grade-one reduction of the relabelling obligation** (contributed as a review scout,
2026-09-05): `Relabel` is equivalent to its case `j = 1`.  Restrict the labelling to `⟨A,1⟩`
(`RespectsSemanticsBelow.mono`), relabel there, and extend back to `⟨A,j⟩` by
`bountiful_full_scope`, so the higher-grade labels become `q ∧ γ` and their locality witnesses
are the capped originals — no higher-grade shifter is synthesized. -/
theorem relabel_iff_gradeOne :
    F.Relabel ↔
      ∀ (q : F.scheme.below (Finset.univ, 1) → ExtOrd),
        RespectsSemanticsBelow F.rows (Finset.univ, 1) q →
        ∀ (γ u' : ExtOrd), SelfVis 1 γ → SelfVis 1 u' →
          min u' γ = min (q (F.cellOf (.inl .s0)
            ⟨Finset.subset_univ _, le_rfl⟩)) γ →
          ∃ q' : F.scheme.below (Finset.univ, 1) → ExtOrd,
            RespectsSemanticsBelow F.rows (Finset.univ, 1) q' ∧
            (∀ d, min (q' d) γ = min (q d) γ) ∧
            q' (F.cellOf (.inl .s0) ⟨Finset.subset_univ _, le_rfl⟩) = u' := by
  constructor
  · intro H
    exact H 1 le_rfl (by omega)
  · intro H j hj _ q hq γ u' hγ hu' he
    let h : GradedLe ((Finset.univ : Finset (Fin 3)), 1) (Finset.univ, j) :=
      ⟨Finset.Subset.refl _, hj⟩
    let q₁ := fun d => q (CellScheme.below.mono h d)
    have hq₁ := hq.mono h
    obtain ⟨p, hp, he₁, hu₁⟩ := H q₁ hq₁ γ u'
      ((show SelfVis j γ from hγ).mono hj) hu' he
    obtain ⟨q', hq', he', hrestrict⟩ := bountiful_full_scope F.rows h p q γ hp hq hγ
      (fun d => (he₁ d).symm)
    refine ⟨q', hq', he', ?_⟩
    exact (hrestrict (F.cellOf (.inl .s0)
      ⟨Finset.subset_univ _, le_rfl⟩)).trans hu₁

end Family

end Bountiful

end VaughtConjecture.Knight
