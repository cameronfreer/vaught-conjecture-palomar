/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.DuplicationPlan
public import VaughtConjecture.Knight.ExtendOneWith
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # The finite carrier for a rounded-meet one-point extension

Use the duplicated plan, copy every old cell at every fresh visible scope
with the same folded scope, and add the grade-`K` term and a mute apex.
The old cells occur first and their face restriction is literally unchanged.
Multiplicity at old indices is retained. Completeness is proved from old
completeness, not assumed of the new carrier.

This file constructs geometry and occurrences only. The intended rows are
described by `RoundedMeetRow`; their installation and whole-scheme legality
remain separate obligations.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.RoundedMeetCarrier

open AmalgamationPlan

variable {n : ℕ}

def pointMap : Option (Fin n) ↪ Fin (n + 1) := finSuccEquivLast.symm.toEmbedding

@[simp] theorem pointMap_some (a : Fin n) : pointMap (some a) = Fin.castSuccEmb a :=
  finSuccEquivLast_symm_some a

@[simp] theorem pointMap_none : pointMap (none : Option (Fin n)) = Fin.last n :=
  finSuccEquivLast_symm_none

def fold (v : Fin n) (a : Fin (n + 1)) : Fin n :=
  DuplicationPlan.fold v (finSuccEquivLast a)

@[simp] theorem fold_pointMap (v : Fin n) (a : Option (Fin n)) :
    fold v (pointMap a) = DuplicationPlan.fold v a := by
  simp [fold, pointMap]

@[simp] theorem fold_castSucc (v a : Fin n) : fold v (Fin.castSuccEmb a) = a := by
  change DuplicationPlan.fold v (finSuccEquivLast (Fin.castSucc a)) = a
  simp [DuplicationPlan.fold]

def plan (v : Fin n) (P : Finset (Finset (Fin n))) : Finset (Finset (Fin (n + 1))) :=
  (DuplicationPlan.plan v Finset.univ P).image (Finset.image pointMap)

theorem domain_eq_univ : DuplicationPlan.domain (Finset.univ : Finset (Fin n)) = Finset.univ := by
  ext a
  cases a <;> simp [DuplicationPlan.domain, DuplicationPlan.old]

theorem pointMap_domain :
    (DuplicationPlan.domain (Finset.univ : Finset (Fin n))).image pointMap = Finset.univ := by
  rw [domain_eq_univ]
  exact Finset.image_univ_of_surjective finSuccEquivLast.symm.surjective

theorem isPlan {P : Finset (Finset (Fin n))} (hP : Plan.IsPlan Finset.univ P)
    (v : Fin n) (hv : Finset.univ.erase v ∈ P) : Plan.IsPlan Finset.univ (plan v P) := by
  have h := Plan.isPlan_image pointMap (DuplicationPlan.isPlan hP (Finset.mem_univ v) hv)
  rw [pointMap_domain] at h
  exact h

theorem image_old (B : Finset (Fin n)) :
    (B.image DuplicationPlan.old).image pointMap = B.image Fin.castSuccEmb := by
  simp [Finset.image_image, Function.comp_def]

theorem old_face_iff (v : Fin n) (P : Finset (Finset (Fin n))) (B : Finset (Fin n)) :
    B.image Fin.castSuccEmb ∈ plan v P ↔ B ∈ P := by
  rw [← image_old]
  constructor
  · intro h
    obtain ⟨S, hS, he⟩ := Finset.mem_image.mp h
    have he' := Finset.image_injective pointMap.injective he
    exact (DuplicationPlan.old_face_iff v Finset.univ P B).mp (he' ▸ hS)
  · intro h
    exact Finset.mem_image.mpr ⟨B.image DuplicationPlan.old,
      (DuplicationPlan.old_face_iff v Finset.univ P B).mpr h, rfl⟩

@[simp] theorem image_fold_pointMap (v : Fin n) (S : Finset (Option (Fin n))) :
    (S.image pointMap).image (fold v) = S.image (DuplicationPlan.fold v) := by
  simp [Finset.image_image, Function.comp_def]

theorem fold_univ (v : Fin n) : (Finset.univ : Finset (Fin (n + 1))).image (fold v) =
    Finset.univ := by
  rw [← pointMap_domain, image_fold_pointMap]
  exact DuplicationPlan.fold_domain (Finset.mem_univ v)

theorem fold_mem {P : Finset (Finset (Fin n))} (hP : Plan.IsPlan Finset.univ P)
    {v : Fin n} {B : Finset (Fin (n + 1))} (hB : B ∈ plan v P) : B.image (fold v) ∈ P := by
  by_cases hfull : B = Finset.univ
  · rw [hfull, fold_univ]
    exact hP.domain_mem
  · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hB
    rw [image_fold_pointMap]
    apply DuplicationPlan.fold_mem hS
    intro he
    exact hfull (he ▸ pointMap_domain)

theorem card_fold {P : Finset (Finset (Fin n))} {v : Fin n}
    {B : Finset (Fin (n + 1))} (hB : B ∈ plan v P) (hne : B ≠ Finset.univ) :
    (B.image (fold v)).card = B.card := by
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hB
  have hS' : S ≠ DuplicationPlan.domain Finset.univ := fun he => hne (he ▸ pointMap_domain)
  rw [image_fold_pointMap, DuplicationPlan.card_fold hS hS',
    Finset.card_image_of_injective _ pointMap.injective]

variable (C : CellScheme (ι := Fin n) Finset.univ) (v : Fin n)
  (hv : Finset.univ.erase v ∈ C.plan) (K : ℕ) (hK0 : 0 < K) (hKn : K ≤ n)

def newFaces : Finset (Finset (Fin (n + 1))) := (plan v C.plan).filter (Fin.last n ∈ ·)

/-- One copy for each old cell, not just one representative per graded index. -/
abbrev Copy := {p : ↥(newFaces C v) × Cell C // C.scope p.2 = p.1.1.image (fold v)}

/-- `false` names the rounded-meet owner, `true` the mute highest-grade apex. -/
abbrev New := Copy C v ⊕ Bool

noncomputable def newCell : New C v → Finset (Fin (n + 1)) × ℕ
  | .inl p => (p.1.1.1, C.grade p.1.2)
  | .inr false => (Finset.univ, K)
  | .inr true => (Finset.univ, n + 1)

include hv hK0 hKn in
theorem newCell_mem (x : New C v) : newCell C v K x ∈ Plan.gradedPlan (plan v C.plan) := by
  rcases x with p | (_ | _)
  · apply Plan.mem_gradedPlan.mpr
    refine ⟨(Finset.mem_filter.mp p.1.1.2).1, C.grade_pos _, ?_⟩
    have h := C.grade_le_card_scope p.1.2
    rw [p.2] at h
    exact h.trans Finset.card_image_le
  · exact Plan.mem_gradedPlan.mpr ⟨(isPlan C.isPlan v hv).domain_mem, hK0,
      by simpa [newCell] using hKn.trans (Nat.le_succ n)⟩
  · exact Plan.mem_gradedPlan.mpr ⟨(isPlan C.isPlan v hv).domain_mem,
      Nat.zero_lt_succ _, by simp [newCell]⟩

theorem newCell_last (x : New C v) : Fin.last n ∈ (newCell C v K x).1 := by
  rcases x with p | (_ | _)
  · exact (Finset.mem_filter.mp p.1.1.2).2
  · exact Finset.mem_univ _
  · exact Finset.mem_univ _

noncomputable def scheme : CellScheme (ι := Fin (n + 1)) Finset.univ :=
  CellScheme.extendOneWith C (plan v C.plan) (isPlan C.isPlan v hv)
    (old_face_iff v C.plan) (newCell C v K) (newCell_mem C v hv K hK0 hKn)

theorem complete (hC : C.IsComplete) : (scheme C v hv K hK0 hKn).IsComplete := by
  apply CellScheme.IsComplete.extendOneWith hC
  rintro ⟨B, j⟩ hBJ hlast
  obtain ⟨hB, hj0, hjB⟩ := Plan.mem_gradedPlan.mp hBJ
  have hnew : B ∈ newFaces C v := Finset.mem_filter.mpr ⟨hB, hlast⟩
  by_cases hapex : B = Finset.univ ∧ j = n + 1
  · exact ⟨.inr true, by rw [hapex.1, hapex.2]; rfl⟩
  · have hjfold : j ≤ (B.image (fold v)).card := by
      by_cases hfull : B = Finset.univ
      · rw [hfull, fold_univ, Finset.card_univ, Fintype.card_fin]
        have hjne : j ≠ n + 1 := fun he => hapex ⟨hfull, he⟩
        rw [hfull, Finset.card_univ, Fintype.card_fin] at hjB
        omega
      · rw [card_fold hB hfull]
        exact hjB
    obtain ⟨c, hc⟩ := hC (B.image (fold v), j)
      (Plan.mem_gradedPlan.mpr ⟨fold_mem C.isPlan hB, hj0, hjfold⟩)
    refine ⟨.inl ⟨(⟨B, hnew⟩, c), congrArg Prod.fst hc⟩, ?_⟩
    change (B, C.grade c) = (B, j)
    have hg : C.grade c = j := congrArg Prod.snd hc
    rw [hg]

theorem old_visible : Finset.univ.image Fin.castSuccEmb ∈ (scheme C v hv K hK0 hKn).plan :=
  CellScheme.extendOneWith_visible

/-- The old cell scheme survives as a literal initial face, with its original ordering. -/
theorem restrict_old : (scheme C v hv K hK0 hKn).restrictFace Fin.castSuccEmb
    (old_visible C v hv K hK0 hKn) = C :=
  CellScheme.restrictFace_extendOneWith (newCell_last C v K)

def oldCell (c : Cell C) : Cell (scheme C v hv K hK0 hKn) :=
  Fin.castAdd (Fintype.card (New C v)) c

noncomputable def addedCell (x : New C v) : Cell (scheme C v hv K hK0 hKn) :=
  Fin.natAdd C.card ((Fintype.equivFin (New C v)) x)

@[simp] theorem oldCell_index (c : Cell C) :
    (scheme C v hv K hK0 hKn).cell (oldCell C v hv K hK0 hKn c) =
      ((C.scope c).image Fin.castSuccEmb, C.grade c) :=
  CellScheme.extendOneWith_cell_castAdd c

@[simp] theorem addedCell_index (x : New C v) :
    (scheme C v hv K hK0 hKn).cell (addedCell C v hv K hK0 hKn x) = newCell C v K x := by
  unfold addedCell scheme
  rw [CellScheme.extendOneWith_cell_natAdd, Equiv.symm_apply_apply]

theorem oldCell_injective : Function.Injective (oldCell C v hv K hK0 hKn) := by
  intro a b h
  have hval := congrArg Fin.val h
  exact Fin.ext hval

theorem addedCell_injective : Function.Injective (addedCell C v hv K hK0 hKn) := by
  intro a b h
  apply (Fintype.equivFin (New C v)).injective
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg Fin.val h)

theorem oldCell_ne_added (c : Cell C) (x : New C v) :
    oldCell C v hv K hK0 hKn c ≠ addedCell C v hv K hK0 hKn x := by
  apply Fin.ne_of_val_ne
  simp only [oldCell, addedCell, Fin.val_castAdd, Fin.val_natAdd]
  have := c.isLt
  omega

/-- The new full-scope term cell. Its semantic value will be forced, not freely chosen. -/
noncomputable def term : Cell (scheme C v hv K hK0 hKn) :=
  addedCell C v hv K hK0 hKn (.inr false)

noncomputable def apex : Cell (scheme C v hv K hK0 hKn) :=
  addedCell C v hv K hK0 hKn (.inr true)

@[simp] theorem term_index : (scheme C v hv K hK0 hKn).cell (term C v hv K hK0 hKn) =
    (Finset.univ, K) := addedCell_index C v hv K hK0 hKn (.inr false)

@[simp] theorem apex_index : (scheme C v hv K hK0 hKn).cell (apex C v hv K hK0 hKn) =
    (Finset.univ, n + 1) := addedCell_index C v hv K hK0 hKn (.inr true)

include hK0 hKn in
/-- No nonempty old plan needs a supplied pivot for the complete carrier construction. -/
theorem exists_complete_carrier (hC : C.IsComplete) :
    ∃ (E : CellScheme (ι := Fin (n + 1)) Finset.univ)
      (hface : Finset.univ.image Fin.castSuccEmb ∈ E.plan),
      E.IsComplete ∧ E.restrictFace Fin.castSuccEmb hface = C ∧
      ∃ ρ z : Cell E, E.cell ρ = (Finset.univ, K) ∧ E.cell z = (Finset.univ, n + 1) := by
  have hn : 0 < n := hK0.trans_le hKn
  obtain ⟨w, _, hw⟩ := DuplicationPlan.exists_pivot C.isPlan
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
  exact ⟨scheme C w hw K hK0 hKn, old_visible C w hw K hK0 hKn,
    complete C w hw K hK0 hKn hC, restrict_old C w hw K hK0 hKn,
    term C w hw K hK0 hKn, apex C w hw K hK0 hKn,
    term_index C w hw K hK0 hKn, apex_index C w hw K hK0 hKn⟩

end VaughtConjecture.Knight.RoundedMeetCarrier
