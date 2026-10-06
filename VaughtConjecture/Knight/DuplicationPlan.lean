/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.AmalgamationPlan.Plan

/-! # One-point duplication of an arbitrary support plan

Duplicate a pivot whose deletion is visible. The two coatoms carry the old
plan and its renamed copy; their overlap is identified literally. Folding
the new point back to the pivot is injective on every proper visible face.
Unlike a generic plan extension, this retains the exact geometry needed by
a definitional row extension. No semantic or lifting assertion is made here.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.DuplicationPlan

open AmalgamationPlan

variable {ι : Type*} [DecidableEq ι]

def old : ι ↪ Option ι := ⟨some, Option.some_injective _⟩

/-- Rename the pivot to the fresh point, fixing every other point. -/
def rename (v : ι) (a : ι) : Option ι := if a = v then none else some a

def fold (v : ι) (a : Option ι) : ι := a.getD v

omit [DecidableEq ι] in
@[simp] theorem old_apply (a : ι) : old a = some a := rfl
omit [DecidableEq ι] in
@[simp] theorem fold_old (v a : ι) : fold v (old a) = a := rfl
omit [DecidableEq ι] in
@[simp] theorem fold_none (v : ι) : fold v none = v := rfl
@[simp] theorem rename_self (v : ι) : rename v v = none := by simp [rename]
@[simp] theorem fold_rename (v a : ι) : fold v (rename v a) = a := by
  by_cases h : a = v <;> simp [rename, h, fold]

def renamed (v : ι) : ι ↪ Option ι :=
  ⟨rename v, fun a b h => by simpa using congrArg (fold v) h⟩

@[simp] theorem renamed_apply (v a : ι) : renamed v a = rename v a := rfl

theorem renamed_eq_old {v a : ι} (h : a ≠ v) : renamed v a = old a := by
  simp [rename, h]

@[simp] theorem none_mem_renamed (v : ι) (B : Finset ι) :
    none ∈ B.image (renamed v) ↔ v ∈ B := by
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    have hav : a = v := by simpa using congrArg (fold v) he
    simpa [hav] using ha
  · intro hv
    exact ⟨v, hv, rename_self v⟩

@[simp] theorem none_notMem_old (B : Finset ι) : none ∉ B.image old := by
  simp [old]

theorem image_renamed_of_notMem {v : ι} {B : Finset ι} (h : v ∉ B) :
    B.image (renamed v) = B.image old := by
  apply Finset.image_congr
  intro a ha
  exact renamed_eq_old (fun he => h (he ▸ ha))

@[simp] theorem image_fold_old (v : ι) (B : Finset ι) :
    (B.image old).image (fold v) = B := by
  simp [Finset.image_image, Function.comp_def, fold]

@[simp] theorem image_fold_renamed (v : ι) (B : Finset ι) :
    (B.image (renamed v)).image (fold v) = B := by
  simp [Finset.image_image, Function.comp_def]

def domain (A : Finset ι) : Finset (Option ι) := insert none (A.image old)

def plan (v : ι) (A : Finset ι) (P : Finset (Finset ι)) :
    Finset (Finset (Option ι)) :=
  P.image (Finset.image old) ∪ P.image (Finset.image (renamed v)) ∪ {domain A}

@[simp] theorem erase_none (A : Finset ι) : (domain A).erase none = A.image old := by
  simp [domain]

theorem erase_old (A : Finset ι) {v : ι} (hv : v ∈ A) :
    (domain A).erase (old v) = A.image (renamed v) := by
  have hr : A.image (renamed v) = insert none ((A.erase v).image old) := by
    conv_lhs => rw [← Finset.insert_erase hv, Finset.image_insert]
    rw [show renamed v v = none from rename_self v,
      image_renamed_of_notMem (Finset.notMem_erase v A)]
  rw [hr, domain, Finset.erase_insert_of_ne (by simp [old]),
    Finset.image_erase old.injective]

theorem overlap (A : Finset ι) (v : ι) :
    ((domain A).erase none).erase (old v) = (A.erase v).image old := by
  rw [erase_none, Finset.image_erase old.injective]

/-- The two embedded plans have exactly the same restriction to the overlap. -/
theorem overlap_agreement (A : Finset ι) (P : Finset (Finset ι)) (v : ι) :
    P.image (Finset.image old) ∩ ((A.erase v).image old).powerset =
      P.image (Finset.image (renamed v)) ∩ ((A.erase v).image old).powerset := by
  ext S
  simp only [Finset.mem_inter, Finset.mem_powerset]
  constructor
  · rintro ⟨hS, hsub⟩
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hS
    have hvB : v ∉ B := by
      intro hvB
      have hm := hsub (Finset.mem_image.mpr ⟨v, hvB, rfl⟩)
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hm
      exact Finset.notMem_erase v A (old.injective he ▸ ha)
    exact ⟨Finset.mem_image.mpr ⟨B, hB, image_renamed_of_notMem hvB⟩, hsub⟩
  · rintro ⟨hS, hsub⟩
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hS
    have hvB : v ∉ B := fun h => none_notMem_old _ (hsub ((none_mem_renamed v B).mpr h))
    exact ⟨Finset.mem_image.mpr ⟨B, hB, (image_renamed_of_notMem hvB).symm⟩, hsub⟩

/-- The exact duplicated plan, not just an unspecified amalgamation plan. -/
theorem isPlan {A : Finset ι} {P : Finset (Finset ι)} (hP : Plan.IsPlan A P)
    {v : ι} (hv : v ∈ A) (hface : A.erase v ∈ P) :
    Plan.IsPlan (domain A) (plan v A P) := by
  have hQ : Plan.IsPlan ((domain A).erase none) (P.image (Finset.image old)) := by
    rw [erase_none]
    exact Plan.isPlan_image old hP
  have hR : Plan.IsPlan ((domain A).erase (old v))
      (P.image (Finset.image (renamed v))) := by
    rw [erase_old A hv]
    exact Plan.isPlan_image (renamed v) hP
  apply Plan.IsPlan.step (A := domain A) (a := none) (b := old v)
    (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
    (by simp) hQ hR
  · rw [overlap]
    exact ⟨Finset.mem_image.mpr ⟨A.erase v, hface, rfl⟩,
      Finset.mem_image.mpr ⟨A.erase v, hface,
        image_renamed_of_notMem (Finset.notMem_erase v A)⟩⟩
  · rw [overlap]
    exact overlap_agreement A P v
  · rfl

theorem old_face_mem {A : Finset ι} {P : Finset (Finset ι)} (hP : Plan.IsPlan A P)
    (v : ι) : A.image old ∈ plan v A P := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨A, hP.domain_mem, rfl⟩

/-- No additional old face becomes visible. -/
theorem old_face_iff (v : ι) (A : Finset ι) (P : Finset (Finset ι)) (B : Finset ι) :
    B.image old ∈ plan v A P ↔ B ∈ P := by
  constructor
  · intro h
    simp only [plan, Finset.mem_union, Finset.mem_singleton] at h
    rcases h with (h | h) | h
    · obtain ⟨C, hC, he⟩ := Finset.mem_image.mp h
      have hCB := congrArg (Finset.image (fold v)) he
      simpa using (show C = B by simpa using hCB) ▸ hC
    · obtain ⟨C, hC, he⟩ := Finset.mem_image.mp h
      have hCB := congrArg (Finset.image (fold v)) he
      simpa using (show C = B by simpa using hCB) ▸ hC
    · exact (none_notMem_old B (h ▸ Finset.mem_insert_self none (A.image old))).elim
  · intro hB
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨B, hB, rfl⟩))

theorem fold_mem {v : ι} {A : Finset ι} {P : Finset (Finset ι)}
    {B : Finset (Option ι)} (hB : B ∈ plan v A P) (hne : B ≠ domain A) :
    B.image (fold v) ∈ P := by
  simp only [plan, Finset.mem_union, Finset.mem_singleton] at hB
  rcases hB with (hB | hB) | hB
  · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
    simpa using hC
  · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
    simpa using hC
  · exact (hne hB).elim

private theorem fold_injOn_image (v : ι) (B : Finset ι) (e : ι ↪ Option ι)
    (he : ∀ a, fold v (e a) = a) : Set.InjOn (fold v) ↑(B.image e) := by
  intro x hx y hy hxy
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
  rw [he, he] at hxy
  exact congrArg e hxy

/-- Every proper visible scope has a bijective fold onto an old visible scope. -/
theorem fold_injOn {v : ι} {A : Finset ι} {P : Finset (Finset ι)}
    {B : Finset (Option ι)} (hB : B ∈ plan v A P) (hne : B ≠ domain A) :
    Set.InjOn (fold v) ↑B := by
  simp only [plan, Finset.mem_union, Finset.mem_singleton] at hB
  rcases hB with (hB | hB) | hB
  · obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hB
    exact fold_injOn_image v C old (fold_old v)
  · obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hB
    exact fold_injOn_image v C (renamed v) (fold_rename v)
  · exact (hne hB).elim

theorem card_fold {v : ι} {A : Finset ι} {P : Finset (Finset ι)}
    {B : Finset (Option ι)} (hB : B ∈ plan v A P) (hne : B ≠ domain A) :
    (B.image (fold v)).card = B.card :=
  Finset.card_image_iff.mpr (fold_injOn hB hne)

theorem fold_domain {A : Finset ι} {v : ι} (hv : v ∈ A) :
    (domain A).image (fold v) = A := by
  simp [domain, hv]

/-- Every nonempty plan supplies a pivot; it is not extra geometric data. -/
theorem exists_pivot {A : Finset ι} {P : Finset (Finset ι)}
    (hP : Plan.IsPlan A P) (hne : A.Nonempty) : ∃ v ∈ A, A.erase v ∈ P := by
  cases hP with
  | empty => exact (Finset.not_nonempty_empty hne).elim
  | singleton a => exact ⟨a, by simp, by simp⟩
  | @step A a b Q R P ha hb hab hQ hR hmem hre hPeq =>
    subst P
    exact ⟨a, ha, Finset.mem_union_left _ (Finset.mem_union_left _ hQ.domain_mem)⟩

end VaughtConjecture.Knight.DuplicationPlan
