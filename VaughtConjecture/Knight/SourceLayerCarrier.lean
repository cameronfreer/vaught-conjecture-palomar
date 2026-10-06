/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneSourceCarrier

/-! # Appending a full-scope layer above an actual lower inventory

Unlike the first-grade carrier, inherited owners may already have full scope.
Strictly smaller grade, not proper scope, keeps every new controller out of
their lower domains. All inherited occurrences and their enumeration survive.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.SourceLayerCarrier

open AmalgamationPlan Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q : Type*) [Fintype Q] (k : ℕ)
variable (hk : 0 < k) (hA : k ≤ A.card)

noncomputable def scheme : CellScheme A where
  plan := D.plan
  isPlan := D.isPlan
  card := D.card + Fintype.card Q
  cell := Fin.addCases D.cell (fun _ => (A, k))
  cell_mem c := by
    refine Fin.addCases ?_ ?_ c
    · intro d; simpa only [Fin.addCases_left] using D.cell_mem d
    · intro q
      simp only [Fin.addCases_right]
      exact Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem, hk, hA⟩

noncomputable def enumeration : (Cell D ⊕ Q) ≃ Cell (scheme D Q k hk hA) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin Q)).trans finSumFinEquiv

noncomputable def toCell (d : Cell D ⊕ Q) : Cell (scheme D Q k hk hA) :=
  enumeration D Q k hk hA d

noncomputable def toOcc (d : Cell (scheme D Q k hk hA)) : Cell D ⊕ Q :=
  (enumeration D Q k hk hA).symm d

@[simp] theorem toOcc_toCell (d : Cell D ⊕ Q) :
    toOcc D Q k hk hA (toCell D Q k hk hA d) = d :=
  (enumeration D Q k hk hA).symm_apply_apply d

@[simp] theorem toCell_toOcc (d : Cell (scheme D Q k hk hA)) :
    toCell D Q k hk hA (toOcc D Q k hk hA d) = d :=
  (enumeration D Q k hk hA).apply_symm_apply d

def index : Cell D ⊕ Q → Finset ι × ℕ
  | .inl d => D.cell d
  | .inr _ => (A, k)

theorem cell_toCell (d : Cell D ⊕ Q) :
    (scheme D Q k hk hA).cell (toCell D Q k hk hA d) = index D Q k d := by
  cases d with
  | inl d =>
    change Fin.addCases D.cell (fun _ => (A, k)) (Fin.castAdd (Fintype.card Q) d) = D.cell d
    exact Fin.addCases_left d
  | inr q =>
    change Fin.addCases D.cell (fun _ => (A, k))
      (Fin.natAdd D.card (Fintype.equivFin Q q)) = (A, k)
    exact Fin.addCases_right (Fintype.equivFin Q q)

theorem cell_eq (d : Cell (scheme D Q k hk hA)) :
    (scheme D Q k hk hA).cell d = index D Q k (toOcc D Q k hk hA d) := by
  rw [← cell_toCell, toCell_toOcc]

theorem old_order : StrictMono (fun d : Cell D => toCell D Q k hk hA (.inl d)) :=
  Fin.strictMono_castAdd _

variable (hgrade : ∀ d : Cell D, D.grade d < k)

omit [Fintype Q] in
include hgrade in
theorem below_old (x : Cell D ⊕ Q) (c : Cell D)
    (h : GradedLe (index D Q k x) (D.cell c)) :
    ∃ d : D.below (D.cell c), x = .inl d.1 := by
  cases x with
  | inl d => exact ⟨⟨d, h⟩, rfl⟩
  | inr q => exact False.elim (not_le_of_gt (hgrade c) h.2)

noncomputable def ownerEquiv (c : Cell D) : D.below (D.cell c) ≃
    (scheme D Q k hk hA).below ((scheme D Q k hk hA).cell (toCell D Q k hk hA (.inl c))) :=
  Equiv.ofBijective
    (fun d => ⟨toCell D Q k hk hA (.inl d.1), by
      simpa only [cell_toCell, index] using d.2⟩)
    ⟨by
      intro d e h
      exact Subtype.ext ((old_order D Q k hk hA).injective (congrArg Subtype.val h)), by
      intro e
      have he : GradedLe (index D Q k (toOcc D Q k hk hA e.1)) (D.cell c) := by
        simpa only [cell_eq, toOcc_toCell, index] using e.2
      obtain ⟨d, hd⟩ := below_old D Q k hgrade _ c he
      refine ⟨d, Subtype.ext ?_⟩
      change toCell D Q k hk hA (.inl d.1) = e.1
      rw [← hd, toCell_toOcc]⟩

theorem ownerEquiv_val (c : Cell D) (d : D.below (D.cell c)) :
    (ownerEquiv D Q k hk hA hgrade c d).1 = toCell D Q k hk hA (.inl d.1) := rfl

include hgrade in
theorem old_not_full (d : Cell D) :
    (scheme D Q k hk hA).cell (toCell D Q k hk hA (.inl d)) ≠ (A, k) := by
  rw [cell_toCell]
  exact fun he => (ne_of_lt (hgrade d)) (congrArg Prod.snd he)

theorem old_occurrence (d : Cell (scheme D Q k hk hA))
    (hd : (scheme D Q k hk hA).cell d ≠ (A, k)) :
    ∃ x : Cell D, d = toCell D Q k hk hA (.inl x) := by
  cases he : toOcc D Q k hk hA d with
  | inl x => exact ⟨x, by rw [← he, toCell_toOcc]⟩
  | inr q => exact False.elim (hd (by rw [cell_eq, he]; rfl))

noncomputable def controller (q : Q) :
    SourcePrefixLayer.Controller (scheme D Q k hk hA) k :=
  ⟨toCell D Q k hk hA (.inr q), cell_toCell D Q k hk hA (.inr q)⟩

noncomputable def controllerEquiv : Q ≃ SourcePrefixLayer.Controller (scheme D Q k hk hA) k :=
  Equiv.ofBijective (controller D Q k hk hA) ⟨by
    intro p q hpq
    exact Sum.inr.inj ((enumeration D Q k hk hA).injective (congrArg Subtype.val hpq)), by
    intro c
    have hc := c.2
    rw [cell_eq] at hc
    cases he : toOcc D Q k hk hA c.1 with
    | inl d =>
      rw [he] at hc
      exact False.elim ((ne_of_lt (hgrade d)) (congrArg Prod.snd hc))
    | inr q =>
      refine ⟨q, Subtype.ext ?_⟩
      change toCell D Q k hk hA (.inr q) = c.1
      rw [← he, toCell_toOcc]⟩

variable (sem : Semantics D)

noncomputable def oldTable : (Cell D ⊕ Q) → (Cell D ⊕ Q) → ExtOrd
  | .inl c, .inl d => AmalgamatedBoundaryRows.total sem c d
  | _, _ => ⊥

omit [Fintype Q] in
include hgrade in
theorem oldTable_visible (c d : Cell D ⊕ Q) (h : GradedLe (index D Q k d) (index D Q k c)) :
    SelfVis (index D Q k d).2 (oldTable D Q sem c d) := by
  cases c with
  | inl c =>
    obtain ⟨e, rfl⟩ := below_old D Q k hgrade d c h
    change SelfVis (D.grade e.1) (AmalgamatedBoundaryRows.total sem c e.1)
    rw [AmalgamatedBoundaryRows.total_below]
    exact (sem.orderly c e).symm
  | inr q => cases d <;> exact selfVis_bot _

noncomputable def base : Semantics (scheme D Q k hk hA) where
  E c d := oldTable D Q sem (toOcc D Q k hk hA c) (toOcc D Q k hk hA d.1)
  orderly c d := by
    have h : GradedLe (index D Q k (toOcc D Q k hk hA d.1))
        (index D Q k (toOcc D Q k hk hA c)) := by
      simpa only [← cell_eq] using d.2
    have hv := oldTable_visible D Q k hgrade sem _ _ h
    change oldTable D Q sem (toOcc D Q k hk hA c) (toOcc D Q k hk hA d.1) =
      extVisibilityReplace (oldTable D Q sem (toOcc D Q k hk hA c) (toOcc D Q k hk hA d.1))
        ((scheme D Q k hk hA).cell d.1).2 ((scheme D Q k hk hA).cell d.1).2
    simpa only [cell_eq] using hv.symm

theorem base_old (c : Cell D) (d : D.below (D.cell c)) :
    (base D Q k hk hA hgrade sem).E (toCell D Q k hk hA (.inl c))
      (ownerEquiv D Q k hk hA hgrade c d) = sem.E c d := by
  change oldTable D Q sem (toOcc D Q k hk hA (toCell D Q k hk hA (.inl c)))
    (toOcc D Q k hk hA (ownerEquiv D Q k hk hA hgrade c d).1) = _
  rw [ownerEquiv_val, toOcc_toCell, toOcc_toCell]
  exact AmalgamatedBoundaryRows.total_below sem c d

theorem base_respects_iff (c : Cell D)
    (p : (scheme D Q k hk hA).below
      ((scheme D Q k hk hA).cell (toCell D Q k hk hA (.inl c))) → ExtOrd) :
    RespectsSemanticsBelow (base D Q k hk hA hgrade sem) _ p ↔
      RespectsSemanticsBelow sem (D.cell c) (p ∘ ownerEquiv D Q k hk hA hgrade c) := by
  have h := respects_iff_of_equiv (sem' := sem) (sem := base D Q k hk hA hgrade sem)
    (ownerEquiv D Q k hk hA hgrade c)
    (fun d => (congrArg Prod.snd (cell_toCell D Q k hk hA (.inl d.1))).symm)
    (fun d e => ?_) (fun b d hd => ?_) (p ∘ ownerEquiv D Q k hk hA hgrade c)
  · have he : (p ∘ ownerEquiv D Q k hk hA hgrade c) ∘
        (ownerEquiv D Q k hk hA hgrade c).symm = p := by
      funext d; simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rw [he] at h
    exact h.symm
  · change D.scope d.1 ⊆ D.scope e.1 ↔
      ((scheme D Q k hk hA).cell (toCell D Q k hk hA (.inl d.1))).1 ⊆
      ((scheme D Q k hk hA).cell (toCell D Q k hk hA (.inl e.1))).1
    rw [cell_toCell, cell_toCell]
    rfl
  · exact (base_old D Q k hk hA hgrade sem b.1 d).symm

end VaughtConjecture.Knight.SourceLayerCarrier
