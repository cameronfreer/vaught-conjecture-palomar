/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneBoundaryFamily
public import VaughtConjecture.Knight.SourcePrefixLayer
public import VaughtConjecture.Knight.AmalgamatedBoundaryRows
public import VaughtConjecture.Knight.FiniteOffset

/-! # Actual occurrences for the first supported controller layer

Append exactly the constructed normalized family to the proper grade-one
boundary. The old cells keep their enumeration and complete lower domains.
There are no lower positive full-scope grades and no mute higher placeholders.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GradeOneSourceCarrier

open AmalgamationPlan Transform Value ExtOrd GradeOneBoundaryFamily

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 0 < A.card)

noncomputable def scheme : CellScheme A where
  plan := D.plan
  isPlan := D.isPlan
  card := D.card + Fintype.card (Profile sem)
  cell := Fin.addCases D.cell (fun _ => (A, 1))
  cell_mem c := by
    refine Fin.addCases ?_ ?_ c
    · intro d; simpa only [Fin.addCases_left] using D.cell_mem d
    · intro q
      simp only [Fin.addCases_right]
      exact Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem, Nat.one_pos, hA⟩

abbrev Occ := Cell D ⊕ Profile sem

noncomputable def enumeration : Occ sem ≃ Cell (scheme sem hA) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin (Profile sem))).trans finSumFinEquiv

noncomputable def toCell (d : Occ sem) : Cell (scheme sem hA) := enumeration sem hA d
noncomputable def toOcc (d : Cell (scheme sem hA)) : Occ sem := (enumeration sem hA).symm d

@[simp] theorem toOcc_toCell (d : Occ sem) : toOcc sem hA (toCell sem hA d) = d :=
  (enumeration sem hA).symm_apply_apply d

@[simp] theorem toCell_toOcc (d : Cell (scheme sem hA)) : toCell sem hA (toOcc sem hA d) = d :=
  (enumeration sem hA).apply_symm_apply d

def index : Occ sem → Finset ι × ℕ
  | .inl d => D.cell d
  | .inr _ => (A, 1)

theorem cell_toCell (d : Occ sem) : (scheme sem hA).cell (toCell sem hA d) = index sem d := by
  cases d with
  | inl d =>
    change Fin.addCases D.cell (fun _ => (A, 1))
      (Fin.castAdd (Fintype.card (Profile sem)) d) = D.cell d
    exact Fin.addCases_left d
  | inr q =>
    change Fin.addCases D.cell (fun _ => (A, 1))
      (Fin.natAdd D.card (Fintype.equivFin (Profile sem) q)) = (A, 1)
    exact Fin.addCases_right (Fintype.equivFin (Profile sem) q)

theorem cell_eq (d : Cell (scheme sem hA)) :
    (scheme sem hA).cell d = index sem (toOcc sem hA d) := by
  rw [← cell_toCell, toCell_toOcc]

theorem old_order : StrictMono (fun d : Cell D => toCell sem hA (.inl d)) :=
  Fin.strictMono_castAdd _

variable (hproper : ∀ d : Cell D, D.scope d ≠ A)

include hproper in
theorem below_old (x : Occ sem) (c : Cell D)
    (h : GradedLe (index sem x) (D.cell c)) :
    ∃ d : D.below (D.cell c), x = .inl d.1 := by
  cases x with
  | inl d => exact ⟨⟨d, h⟩, rfl⟩
  | inr q => exact False.elim (hproper c (Finset.Subset.antisymm
      (D.isPlan.subset_of_mem (D.scope_mem_plan c)) h.1))

noncomputable def ownerEquiv (c : Cell D) :
    D.below (D.cell c) ≃ (scheme sem hA).below ((scheme sem hA).cell (toCell sem hA (.inl c))) :=
  Equiv.ofBijective
    (fun d => ⟨toCell sem hA (.inl d.1), by simpa only [cell_toCell, index] using d.2⟩)
    ⟨by
      intro d e h
      exact Subtype.ext ((old_order sem hA).injective (congrArg Subtype.val h)), by
      intro e
      have he : GradedLe (index sem (toOcc sem hA e.1)) (D.cell c) := by
        simpa only [cell_eq, toOcc_toCell, index] using e.2
      obtain ⟨d, hd⟩ := below_old sem hproper _ c he
      refine ⟨d, Subtype.ext ?_⟩
      change toCell sem hA (.inl d.1) = e.1
      rw [← hd, toCell_toOcc]⟩

theorem ownerEquiv_val (c : Cell D) (d : D.below (D.cell c)) :
    (ownerEquiv sem hA hproper c d).1 = toCell sem hA (.inl d.1) := rfl

noncomputable def oldTable : Occ sem → Occ sem → ExtOrd
  | .inl c, .inl d => AmalgamatedBoundaryRows.total sem c d
  | _, _ => ⊥

include hproper in
theorem oldTable_visible (c d : Occ sem) (h : GradedLe (index sem d) (index sem c)) :
    SelfVis (index sem d).2 (oldTable sem c d) := by
  cases c with
  | inl c =>
    obtain ⟨e, rfl⟩ := below_old sem hproper d c h
    change SelfVis (D.grade e.1) (AmalgamatedBoundaryRows.total sem c e.1)
    rw [AmalgamatedBoundaryRows.total_below]
    exact (sem.orderly c e).symm
  | inr q => cases d <;> exact selfVis_bot _

noncomputable def base : Semantics (scheme sem hA) where
  E c d := oldTable sem (toOcc sem hA c) (toOcc sem hA d.1)
  orderly c d := by
    have h : GradedLe (index sem (toOcc sem hA d.1)) (index sem (toOcc sem hA c)) := by
      simpa only [← cell_eq] using d.2
    have hv := oldTable_visible sem hproper _ _ h
    change oldTable sem (toOcc sem hA c) (toOcc sem hA d.1) =
      extVisibilityReplace (oldTable sem (toOcc sem hA c) (toOcc sem hA d.1))
      ((scheme sem hA).cell d.1).2
      ((scheme sem hA).cell d.1).2
    simpa only [cell_eq] using hv.symm

theorem base_old (c : Cell D) (d : D.below (D.cell c)) :
    (base sem hA hproper).E (toCell sem hA (.inl c)) (ownerEquiv sem hA hproper c d) =
      sem.E c d := by
  change oldTable sem (toOcc sem hA (toCell sem hA (.inl c)))
    (toOcc sem hA (ownerEquiv sem hA hproper c d).1) = _
  rw [ownerEquiv_val, toOcc_toCell, toOcc_toCell]
  exact AmalgamatedBoundaryRows.total_below sem c d

theorem base_respects_iff (c : Cell D)
    (p : (scheme sem hA).below ((scheme sem hA).cell (toCell sem hA (.inl c))) → ExtOrd) :
    RespectsSemanticsBelow (base sem hA hproper) _ p ↔
      RespectsSemanticsBelow sem (D.cell c) (p ∘ ownerEquiv sem hA hproper c) := by
  have h := respects_iff_of_equiv (sem' := sem) (sem := base sem hA hproper)
    (ownerEquiv sem hA hproper c)
    (fun d => (congrArg Prod.snd (cell_toCell sem hA (.inl d.1))).symm)
    (fun d e => ?_) (fun b d hd => ?_) (p ∘ ownerEquiv sem hA hproper c)
  · have he : (p ∘ ownerEquiv sem hA hproper c) ∘
        (ownerEquiv sem hA hproper c).symm = p := by
      funext d; simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rw [he] at h
    exact h.symm
  · change D.scope d.1 ⊆ D.scope e.1 ↔
      ((scheme sem hA).cell (toCell sem hA (.inl d.1))).1 ⊆
      ((scheme sem hA).cell (toCell sem hA (.inl e.1))).1
    rw [cell_toCell, cell_toCell]
    rfl
  · exact (base_old sem hA hproper b.1 d).symm

theorem grade_one (hg : ∀ d : Cell D, D.grade d = 1) (c : Cell (scheme sem hA)) :
    (scheme sem hA).grade c = 1 := by
  change ((scheme sem hA).cell c).2 = 1
  rw [cell_eq]
  cases toOcc sem hA c with
  | inl d => exact hg d
  | inr q => rfl

include hproper in
theorem old_not_full (d : Cell D) :
    (scheme sem hA).cell (toCell sem hA (.inl d)) ≠ (A, 1) := by
  rw [cell_toCell]
  exact fun he => hproper d (congrArg Prod.fst he)

noncomputable def controller (q : Profile sem) :
    SourcePrefixLayer.Controller (scheme sem hA) 1 :=
  ⟨toCell sem hA (.inr q), cell_toCell sem hA (.inr q)⟩

noncomputable def controllerEquiv :
    Profile sem ≃ SourcePrefixLayer.Controller (scheme sem hA) 1 :=
  Equiv.ofBijective (controller sem hA) ⟨by
    intro p q hpq
    have h := (enumeration sem hA).injective (congrArg Subtype.val hpq)
    exact Sum.inr.inj h, by
    intro c
    have hc := c.2
    rw [cell_eq] at hc
    cases he : toOcc sem hA c.1 with
    | inl d =>
      rw [he] at hc
      exact False.elim (hproper d (congrArg Prod.fst hc))
    | inr q =>
      refine ⟨q, Subtype.ext ?_⟩
      change toCell sem hA (.inr q) = c.1
      rw [← he, toCell_toOcc]⟩

end VaughtConjecture.Knight.GradeOneSourceCarrier
