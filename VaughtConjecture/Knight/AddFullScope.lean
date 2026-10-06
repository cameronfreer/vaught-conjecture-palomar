/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Semantics

/-! # Adding full-scope cells to a scheme, with rows

A family of full-scope controllers is added to a base scheme `D₀` on `A` whose cells all have
proper scope: `addFull D₀ level` has the old cells (indices `Fin.castAdd`) followed by one cell per
`j : Fin N` at the graded index `(A, level j)` (indices `Fin.natAdd`), on the same plan.  The
lower set of an old cell is the old lower set (`belowOld`), and the lower set of a new cell of
level `k` is the old cells of grade `≤ k` together with the new cells of level `≤ k`
(`belowNew`).  `addFullSem` carries the base rows on the old cells and prescribed rows on the new
cells; the base rows stay consistent (`respects_old`, through the generic transport of respect
along an index- and row-preserving equivalence of lower sets,
`RespectsSemanticsBelow.of_lowerEquiv`).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

/-! ## Transport of respect along an equivalence of lower sets -/

/-- **Transport of respect** between two schemes: an equivalence of lower sets preserving graded
indices, with compatible equivalences of the lower sets of each cell preserving indices,
inclusions and rows, transports respecting labellings. -/
theorem RespectsSemanticsBelow.of_lowerEquiv {D D' : CellScheme A} {sem : Semantics D}
    {sem' : Semantics D'} {BJ BJ' : Finset ι × ℕ} (e : D.below BJ ≃ D'.below BJ')
    (hcell : ∀ d, D'.cell (e d).1 = D.cell d.1)
    (rowEquiv : ∀ Sig : D.below BJ, D.below (D.cell Sig.1) ≃ D'.below (D'.cell (e Sig).1))
    (hrow_cell : ∀ Sig d, D'.cell (rowEquiv Sig d).1 = D.cell d.1)
    (hrow_incl : ∀ Sig d, CellScheme.below.incl (e Sig) (rowEquiv Sig d) =
      e (CellScheme.below.incl Sig d))
    (hrows : ∀ Sig d, sem'.E (e Sig).1 (rowEquiv Sig d) = sem.E Sig.1 d)
    {r : D.below BJ → ExtOrd} (hr : RespectsSemanticsBelow sem BJ r) :
    RespectsSemanticsBelow sem' BJ' (fun d' => r (e.symm d')) where
  orderly d' := by
    have h := hr.orderly (e.symm d')
    dsimp only at h ⊢
    unfold CellScheme.grade at h ⊢
    rw [← hcell (e.symm d'), Equiv.apply_symm_apply] at h
    exact h
  locality Sig' := by
    obtain ⟨Sig, rfl⟩ := e.surjective Sig'
    obtain ⟨g, σ, hanti, hsv, hbot, hmono, h5, heq⟩ := hr.locality Sig
    refine ⟨g, σ, hanti, hsv, hbot, hmono, h5, fun d' => ?_⟩
    have h := heq ((rowEquiv Sig).symm d')
    dsimp only at h ⊢
    have hd : rowEquiv Sig ((rowEquiv Sig).symm d') = d' := Equiv.apply_symm_apply _ _
    have hincl : e.symm (CellScheme.below.incl (e Sig) d') =
        CellScheme.below.incl Sig ((rowEquiv Sig).symm d') := by
      have := hrow_incl Sig ((rowEquiv Sig).symm d')
      rw [hd] at this
      rw [this, Equiv.symm_apply_apply]
    have hgr : D'.grade d'.1 = D.grade ((rowEquiv Sig).symm d').1 := by
      unfold CellScheme.grade
      rw [← hrow_cell Sig ((rowEquiv Sig).symm d'), hd]
    have hE : sem'.E (e Sig).1 d' = sem.E Sig.1 ((rowEquiv Sig).symm d') := by
      rw [← hrows Sig ((rowEquiv Sig).symm d'), hd]
    rw [hincl, Equiv.symm_apply_apply, hE, hgr]
    exact h
  availability Sig' Xi₀' hscope hgrade := by
    obtain ⟨Sig, rfl⟩ := e.surjective Sig'
    obtain ⟨Xi₀, rfl⟩ := e.surjective Xi₀'
    obtain ⟨Xi, hXi, hle⟩ := hr.availability Sig Xi₀
      (by unfold CellScheme.scope at hscope ⊢; rw [hcell, hcell] at hscope; exact hscope)
      (by unfold CellScheme.grade at hgrade ⊢; rw [hcell, hcell] at hgrade; exact hgrade)
    refine ⟨e Xi, by rw [hcell, hcell, hXi], ?_⟩
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact hle

/-! ## The scheme -/

namespace CellScheme

section Scheme

variable (D₀ : CellScheme A) {N : ℕ} (level : Fin N → ℕ)
  (hlevel : ∀ j, (A, level j) ∈ Plan.gradedPlan D₀.plan)

/-- **Adding full-scope cells**: the old cells (indices `Fin.castAdd`) followed by one cell per
`j : Fin N` at the graded index `(A, level j)` (indices `Fin.natAdd`), on the same plan. -/
noncomputable def addFull : CellScheme A where
  plan := D₀.plan
  isPlan := D₀.isPlan
  card := D₀.card + N
  cell := Fin.append D₀.cell fun j => (A, level j)
  cell_mem i := by
    induction i using Fin.addCases with
    | left i => rw [Fin.append_left]; exact D₀.cell_mem i
    | right j => rw [Fin.append_right]; exact hlevel _

end Scheme

namespace addFull

variable {D₀ : CellScheme A} {N : ℕ} {level : Fin N → ℕ}
  (hlevel : ∀ j, (A, level j) ∈ Plan.gradedPlan D₀.plan)

/-- An old cell. -/
def old (i : Cell D₀) : Cell (addFull D₀ level hlevel) := Fin.castAdd N i

/-- A new cell. -/
def new (j : Fin N) : Cell (addFull D₀ level hlevel) := Fin.natAdd D₀.card j

@[simp] theorem cell_old (i : Cell D₀) :
    (addFull D₀ level hlevel).cell (old hlevel i) = D₀.cell i :=
  Fin.append_left D₀.cell (fun j => (A, level j)) i

@[simp] theorem cell_new (j : Fin N) :
    (addFull D₀ level hlevel).cell (new hlevel j) = (A, level j) :=
  Fin.append_right D₀.cell (fun j => (A, level j)) j

theorem scope_old (i : Cell D₀) : (addFull D₀ level hlevel).scope (old hlevel i) = D₀.scope i :=
  congrArg Prod.fst (cell_old hlevel i)

theorem grade_old (i : Cell D₀) : (addFull D₀ level hlevel).grade (old hlevel i) = D₀.grade i :=
  congrArg Prod.snd (cell_old hlevel i)

theorem scope_new (j : Fin N) : (addFull D₀ level hlevel).scope (new hlevel j) = A :=
  congrArg Prod.fst (cell_new hlevel j)

theorem grade_new (j : Fin N) : (addFull D₀ level hlevel).grade (new hlevel j) = level j :=
  congrArg Prod.snd (cell_new hlevel j)

theorem old_injective : Function.Injective (old hlevel) :=
  fun a b h => Fin.ext (by simpa [old] using congrArg Fin.val h)

theorem new_injective : Function.Injective (new hlevel) :=
  fun a b h => Fin.ext (by simpa [new] using congrArg Fin.val h)

theorem old_ne_new (i : Cell D₀) (j : Fin N) : old hlevel i ≠ new hlevel j := by
  intro h
  have := congrArg Fin.val h
  simp [old, new] at this
  omega

/-- Every cell is old or new. -/
theorem cases (d : Cell (addFull D₀ level hlevel)) :
    (∃ i, d = old hlevel i) ∨ ∃ j, d = new hlevel j := by
  induction d using Fin.addCases with
  | left i => exact Or.inl ⟨i, rfl⟩
  | right j => exact Or.inr ⟨j, rfl⟩

/-- Below an old cell, every cell is old (all base cells have proper scope). -/
theorem exists_old_of_le (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A) {i : Cell D₀}
    {d : Cell (addFull D₀ level hlevel)}
    (hd : GradedLe ((addFull D₀ level hlevel).cell d)
      ((addFull D₀ level hlevel).cell (old hlevel i))) :
    ∃ j, d = old hlevel j := by
  rcases cases hlevel d with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact ⟨j, rfl⟩
  · exfalso
    apply hproper i
    have h := hd.1
    rw [cell_new, cell_old] at h
    exact le_antisymm (D₀.isPlan.subset_of_mem (D₀.scope_mem_plan i)) h

variable (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A)

/-- **The lower set of an old cell** is the old lower set. -/
noncomputable def belowOld (i : Cell D₀) :
    D₀.below (D₀.cell i) ≃
      (addFull D₀ level hlevel).below ((addFull D₀ level hlevel).cell (old hlevel i)) :=
  Equiv.ofBijective (fun d => ⟨old hlevel d.1, by rw [cell_old, cell_old]; exact d.2⟩)
    ⟨fun a b h => Subtype.ext (old_injective hlevel (congrArg Subtype.val h)), fun e => by
      obtain ⟨j, hj⟩ := exists_old_of_le hlevel hproper e.2
      refine ⟨⟨j, ?_⟩, Subtype.ext hj.symm⟩
      have := e.2
      rw [hj, cell_old, cell_old] at this
      exact this⟩

@[simp] theorem belowOld_val (i : Cell D₀) (d : D₀.below (D₀.cell i)) :
    (belowOld hlevel hproper i d).1 = old hlevel d.1 := rfl

/-- The old cells of grade at most `k` and the new cells of level at most `k`. -/
abbrev LowerOf (lv : Fin N → ℕ) (k : ℕ) : Type _ :=
  {d : Cell D₀ // D₀.grade d ≤ k} ⊕ {j : Fin N // lv j ≤ k}

/-- The cells of the lower set of a new cell, from the sum. -/
def newLower (j : Fin N) :
    LowerOf (D₀ := D₀) level (level j) →
      (addFull D₀ level hlevel).below ((addFull D₀ level hlevel).cell (new hlevel j))
  | Sum.inl d => ⟨old hlevel d.1, by
      rw [cell_old, cell_new]
      exact ⟨D₀.isPlan.subset_of_mem (D₀.scope_mem_plan d.1), d.2⟩⟩
  | Sum.inr j' => ⟨new hlevel j'.1, by rw [cell_new, cell_new]; exact ⟨subset_rfl, j'.2⟩⟩

/-- **The lower set of a new cell** of level `k`: the old cells of grade `≤ k` and the new cells of
level `≤ k`. -/
noncomputable def belowNew (j : Fin N) :
    LowerOf (D₀ := D₀) level (level j) ≃
      (addFull D₀ level hlevel).below ((addFull D₀ level hlevel).cell (new hlevel j)) :=
  Equiv.ofBijective (newLower hlevel j)
    ⟨by
      rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (Subtype.ext (old_injective hlevel (congrArg Subtype.val h)))
      · exact absurd (congrArg Subtype.val h) (old_ne_new hlevel _ _)
      · exact absurd (congrArg Subtype.val h).symm (old_ne_new hlevel _ _)
      · exact congrArg Sum.inr (Subtype.ext (new_injective hlevel (congrArg Subtype.val h))),
     fun e => by
      rcases cases hlevel e.1 with ⟨i, hi⟩ | ⟨j', hj'⟩
      · refine ⟨Sum.inl ⟨i, ?_⟩, Subtype.ext hi.symm⟩
        have := e.2.2
        rw [hi, cell_old, cell_new] at this
        exact this
      · refine ⟨Sum.inr ⟨j', ?_⟩, Subtype.ext hj'.symm⟩
        have := e.2.2
        rw [hj', cell_new, cell_new] at this
        exact this⟩

@[simp] theorem belowNew_inl (j : Fin N) (d : {d : Cell D₀ // D₀.grade d ≤ level j}) :
    (belowNew hlevel j (Sum.inl d)).1 = old hlevel d.1 := rfl

@[simp] theorem belowNew_inr (j : Fin N) (j' : {j' : Fin N // level j' ≤ level j}) :
    (belowNew hlevel j (Sum.inr j')).1 = new hlevel j'.1 := rfl

/-- The inverse of `belowOld` on an old cell. -/
theorem belowOld_symm (i b : Cell D₀) (hb : GradedLe (D₀.cell b) (D₀.cell i))
    (h : GradedLe ((addFull D₀ level hlevel).cell (old hlevel b))
      ((addFull D₀ level hlevel).cell (old hlevel i))) :
    (belowOld hlevel hproper i).symm ⟨old hlevel b, h⟩ = ⟨b, hb⟩ :=
  (belowOld hlevel hproper i).symm_apply_eq.mpr (Subtype.ext rfl)

/-- The inverse of `belowNew` on an old cell. -/
theorem belowNew_symm_old (j : Fin N) (b : Cell D₀) (hb : D₀.grade b ≤ level j)
    (h : GradedLe ((addFull D₀ level hlevel).cell (old hlevel b))
      ((addFull D₀ level hlevel).cell (new hlevel j))) :
    (belowNew hlevel j).symm ⟨old hlevel b, h⟩ = Sum.inl ⟨b, hb⟩ :=
  (belowNew hlevel j).symm_apply_eq.mpr (Subtype.ext rfl)

/-- The inverse of `belowNew` on a new cell. -/
theorem belowNew_symm_new (j j' : Fin N) (hj' : level j' ≤ level j)
    (h : GradedLe ((addFull D₀ level hlevel).cell (new hlevel j'))
      ((addFull D₀ level hlevel).cell (new hlevel j))) :
    (belowNew hlevel j).symm ⟨new hlevel j', h⟩ = Sum.inr ⟨j', hj'⟩ :=
  (belowNew hlevel j).symm_apply_eq.mpr (Subtype.ext rfl)

/-- The grade of a cell of the lower set of a new cell, on the sum. -/
def lowerGrade (lv : Fin N → ℕ) (k : ℕ) (x : LowerOf (D₀ := D₀) lv k) : ℕ :=
  Sum.elim (fun d => D₀.grade d.1) (fun j' => lv j'.1) x

theorem grade_belowNew (j : Fin N) (x : LowerOf (D₀ := D₀) level (level j)) :
    (addFull D₀ level hlevel).grade (belowNew hlevel j x).1 = lowerGrade level _ x := by
  rcases x with d | j'
  · rw [belowNew_inl]; exact grade_old hlevel d.1
  · rw [belowNew_inr]; exact grade_new hlevel j'.1

/-! ## The semantics -/

section Sem

variable (sem₀ : Semantics D₀)
  (newRow : (j : Fin N) → LowerOf (D₀ := D₀) level (level j) → ExtOrd)
  (hnew_orderly : ∀ j, IsOrderly (lowerGrade level (level j)) (newRow j))

/-- The rows: the base rows on old cells, the prescribed rows on new cells. -/
noncomputable def rowFun (Sig : Cell (addFull D₀ level hlevel)) :
    (addFull D₀ level hlevel).below ((addFull D₀ level hlevel).cell Sig) → ExtOrd :=
  Fin.addCases (motive := fun Sig =>
      (addFull D₀ level hlevel).below ((addFull D₀ level hlevel).cell Sig) → ExtOrd)
    (fun i d => sem₀.E i ((belowOld hlevel hproper i).symm d))
    (fun j d => newRow j ((belowNew hlevel j).symm d)) Sig

theorem rowFun_old (i : Cell D₀) :
    rowFun hlevel hproper sem₀ newRow (old hlevel i) =
      fun d : (addFull D₀ level hlevel).below ((addFull D₀ level hlevel).cell (old hlevel i)) =>
        sem₀.E i ((belowOld hlevel hproper i).symm d) :=
  by unfold rowFun old; exact Fin.addCases_left i

theorem rowFun_new (j : Fin N) :
    rowFun hlevel hproper sem₀ newRow (new hlevel j) =
      fun d : (addFull D₀ level hlevel).below ((addFull D₀ level hlevel).cell (new hlevel j)) =>
        newRow j ((belowNew hlevel j).symm d) :=
  by unfold rowFun new; exact Fin.addCases_right j

include hnew_orderly in
/-- The semantics on the extended scheme. -/
noncomputable def addFullSem : Semantics (addFull D₀ level hlevel) where
  E := rowFun hlevel hproper sem₀ newRow
  orderly Sig := by
    rcases cases hlevel Sig with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · intro d
      rw [rowFun_old]
      have h := sem₀.orderly i ((belowOld hlevel hproper i).symm d)
      dsimp only at h ⊢
      have hg : (addFull D₀ level hlevel).grade d.1 =
          D₀.grade ((belowOld hlevel hproper i).symm d).1 := by
        conv_lhs => rw [← Equiv.apply_symm_apply (belowOld hlevel hproper i) d]
        rw [belowOld_val]
        exact grade_old hlevel _
      rw [hg]
      exact h
    · intro d
      rw [rowFun_new]
      have h := hnew_orderly j ((belowNew hlevel j).symm d)
      dsimp only at h ⊢
      have hg : (addFull D₀ level hlevel).grade d.1 =
          lowerGrade level (level j) ((belowNew hlevel j).symm d) := by
        conv_lhs => rw [← Equiv.apply_symm_apply (belowNew hlevel j) d]
        exact grade_belowNew hlevel j _
      rw [hg]
      exact h

theorem addFullSem_E_old (i : Cell D₀) (d) :
    (addFullSem hlevel hproper sem₀ newRow hnew_orderly).E (old hlevel i) d =
      sem₀.E i ((belowOld hlevel hproper i).symm d) := by
  change rowFun hlevel hproper sem₀ newRow (old hlevel i) d = _
  rw [rowFun_old]

theorem addFullSem_E_old_apply (i : Cell D₀) (d : D₀.below (D₀.cell i)) :
    (addFullSem hlevel hproper sem₀ newRow hnew_orderly).E (old hlevel i)
      (belowOld hlevel hproper i d) = sem₀.E i d := by
  rw [addFullSem_E_old, Equiv.symm_apply_apply]

theorem addFullSem_E_new (j : Fin N) (d) :
    (addFullSem hlevel hproper sem₀ newRow hnew_orderly).E (new hlevel j) d =
      newRow j ((belowNew hlevel j).symm d) := by
  change rowFun hlevel hproper sem₀ newRow (new hlevel j) d = _
  rw [rowFun_new]

theorem addFullSem_E_new_apply (j : Fin N) (x) :
    (addFullSem hlevel hproper sem₀ newRow hnew_orderly).E (new hlevel j) (belowNew hlevel j x) =
      newRow j x := by
  rw [addFullSem_E_new, Equiv.symm_apply_apply]

/-- **The base rows stay consistent.** -/
theorem respects_old (hcons : sem₀.IsConsistent) (i : Cell D₀) :
    RespectsSemanticsBelow (addFullSem hlevel hproper sem₀ newRow hnew_orderly)
      ((addFull D₀ level hlevel).cell (old hlevel i))
      ((addFullSem hlevel hproper sem₀ newRow hnew_orderly).E (old hlevel i)) := by
  have key := RespectsSemanticsBelow.of_lowerEquiv (sem := sem₀)
    (sem' := addFullSem hlevel hproper sem₀ newRow hnew_orderly) (belowOld hlevel hproper i)
    (fun d => cell_old hlevel d.1) (fun Sig => belowOld hlevel hproper Sig.1)
    (fun Sig d => cell_old hlevel d.1) (fun Sig d => Subtype.ext rfl)
    (fun Sig d => addFullSem_E_old_apply hlevel hproper sem₀ newRow hnew_orderly Sig.1 d) (hcons i)
  convert key using 1
  funext d
  exact addFullSem_E_old hlevel hproper sem₀ newRow hnew_orderly i d

end Sem

end addFull

end CellScheme

end VaughtConjecture.Knight
