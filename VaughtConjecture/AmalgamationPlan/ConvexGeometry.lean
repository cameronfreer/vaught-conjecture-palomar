/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.AmalgamationPlan.ClosedGeometry
public import VaughtConjecture.Knight.VisibleFaceOneStep

/-! # The finite convex-geometry characterization of support plans

We use the closed-set presentation: empty and full sets, intersection closure,
and one-point accessibility upwards. This does not identify plans with linear
intervals, matroids, or the unrelated notion of convex dimension two.
-/

@[expose] public section

namespace VaughtConjecture.AmalgamationPlan.Plan

variable {α : Type*} [DecidableEq α]

/-- The finite closed-set axioms for a convex geometry. -/
structure IsConvexGeometry (A : Finset α) (P : Finset (Finset α)) : Prop where
  bounded : ∀ B ∈ P, B ⊆ A
  empty_mem : ∅ ∈ P
  domain_mem : A ∈ P
  inter_mem : ∀ B ∈ P, ∀ C ∈ P, B ∩ C ∈ P
  accessible : ∀ B ∈ P, B ≠ A → ∃ x ∈ A, x ∉ B ∧ insert x B ∈ P

/-- Removable points of a closed set, expressed without choosing pivots. -/
def extremes (P : Finset (Finset α)) (B : Finset α) : Finset α :=
  B.filter fun x => B.erase x ∈ P

theorem mem_extremes {P : Finset (Finset α)} {B : Finset α} {x : α} :
    x ∈ extremes P B ↔ x ∈ B ∧ B.erase x ∈ P := Finset.mem_filter

theorem IsPlan.convexGeometry {A : Finset α} {P : Finset (Finset α)} (hP : IsPlan A P) :
    IsConvexGeometry A P where
  bounded _ := hP.subset_of_mem
  empty_mem := hP.empty_mem
  domain_mem := hP.domain_mem
  inter_mem _ hB _ hC := hP.inter_mem hB hC
  accessible B hB hne := by
    obtain ⟨C, hC, hBC, hcard⟩ := hP.exists_visible_card_succ_superface hB hne
    obtain ⟨x, hxC, hxB⟩ := Finset.exists_of_ssubset hBC
    refine ⟨x, hP.subset_of_mem hC hxC, hxB, ?_⟩
    have he : insert x B = C := Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hxC hBC.subset) (by rw [Finset.card_insert_of_notMem hxB, hcard])
    rwa [he]

/-- Global accessibility restricts to every closed face. The proof maximizes a
closed set whose intersection with that face has not yet grown. -/
theorem IsConvexGeometry.accessible_inside {A B C : Finset α} {P : Finset (Finset α)}
    (hP : IsConvexGeometry A P) (hB : B ∈ P) (hC : C ∈ P) (hBC : B ⊂ C) :
    ∃ x ∈ C, x ∉ B ∧ insert x B ∈ P := by
  let F := P.filter fun E => E ∩ C = B
  have hinit : B ∈ F := Finset.mem_filter.mpr ⟨hB, Finset.inter_eq_left.mpr hBC.subset⟩
  obtain ⟨E, hE, hmax⟩ := F.exists_max_image Finset.card ⟨B, hinit⟩
  obtain ⟨hEP, hEC⟩ := Finset.mem_filter.mp hE
  have hne : E ≠ A := by
    intro h
    have hCB : C = B := by simpa [h, Finset.inter_eq_right.mpr (hP.bounded C hC)] using hEC
    exact hBC.ne hCB.symm
  obtain ⟨x, hxA, hxE, hxP⟩ := hP.accessible E hEP hne
  have hxC : x ∈ C := by
    by_contra hn
    have hi : insert x E ∈ F := Finset.mem_filter.mpr ⟨hxP, by
      rw [Finset.insert_inter_of_notMem hn, hEC]⟩
    have := hmax _ hi
    rw [Finset.card_insert_of_notMem hxE] at this
    omega
  have hxB : x ∉ B := by
    rw [← hEC]
    exact fun h => hxE (Finset.mem_inter.mp h).1
  refine ⟨x, hxC, hxB, ?_⟩
  have hi := hP.inter_mem _ hxP C hC
  rwa [Finset.insert_inter_of_mem hxC, hEC] at hi

theorem IsConvexGeometry.restrict {A B : Finset α} {P : Finset (Finset α)}
    (hP : IsConvexGeometry A P) (hB : B ∈ P) :
    IsConvexGeometry B (restrictPlan P B) where
  bounded _ h := Finset.mem_powerset.mp (Finset.mem_inter.mp h).2
  empty_mem := Finset.mem_inter.mpr ⟨hP.empty_mem, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
  domain_mem := Finset.mem_inter.mpr ⟨hB, Finset.mem_powerset.mpr (Finset.Subset.refl _)⟩
  inter_mem C hC D hD := Finset.mem_inter.mpr
    ⟨hP.inter_mem C (Finset.mem_inter.mp hC).1 D (Finset.mem_inter.mp hD).1,
      Finset.mem_powerset.mpr (Finset.inter_subset_left.trans
        (Finset.mem_powerset.mp (Finset.mem_inter.mp hC).2))⟩
  accessible C hC hne := by
    obtain ⟨hCP, hCB⟩ := Finset.mem_inter.mp hC
    have hsub := Finset.mem_powerset.mp hCB
    obtain ⟨x, hx, hn, hi⟩ := hP.accessible_inside hCP hB
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    exact ⟨x, hx, hn, Finset.mem_inter.mpr
      ⟨hi, Finset.mem_powerset.mpr (Finset.insert_subset hx hsub)⟩⟩

theorem extremes_restrict {B C : Finset α} {P : Finset (Finset α)} (hCB : C ⊆ B) :
    extremes (restrictPlan P B) C = extremes P C := by
  ext x
  simp only [mem_extremes, restrictPlan, Finset.mem_inter, Finset.mem_powerset]
  exact ⟨fun h => ⟨h.1, h.2.1⟩,
    fun h => ⟨h.1, h.2, (Finset.erase_subset _ _).trans hCB⟩⟩

theorem IsPlan.extremes_card {A B : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) (hB : B ∈ P) (hcard : 2 ≤ B.card) : (extremes P B).card = 2 := by
  obtain ⟨a, b, ha, hb, hab, hpiv, _, _⟩ := (restrict_isPlan hP hB).pivot_pair hcard
  have he : extremes (restrictPlan P B) B = {a, b} := by
    ext x
    simp only [mem_extremes, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => (hpiv x h.1).mp h.2,
      fun h => ⟨h.elim (fun e => e ▸ ha) (fun e => e ▸ hb),
        (hpiv x (h.elim (fun e => e ▸ ha) (fun e => e ▸ hb))).mpr h⟩⟩
  rw [extremes_restrict (Finset.Subset.refl _)] at he
  simp [he, hab]

/-- Every proper closed set is contained in a removable-point coatom. -/
theorem IsConvexGeometry.exists_coatom {A B : Finset α} {P : Finset (Finset α)}
    (hP : IsConvexGeometry A P) (hB : B ∈ P) (hne : B ≠ A) :
    ∃ x ∈ extremes P A, B ⊆ A.erase x := by
  let F := P.filter fun C => B ⊆ C ∧ C ≠ A
  have hinit : B ∈ F := Finset.mem_filter.mpr ⟨hB, Finset.Subset.refl _, hne⟩
  obtain ⟨C, hC, hmax⟩ := F.exists_max_image Finset.card ⟨B, hinit⟩
  obtain ⟨hCP, hBC, hCA⟩ := Finset.mem_filter.mp hC
  obtain ⟨x, hxA, hxC, hi⟩ := hP.accessible C hCP hCA
  have he : insert x C = A := by
    by_contra hn
    have hm := hmax _ (Finset.mem_filter.mpr
      ⟨hi, hBC.trans (Finset.subset_insert _ _), hn⟩)
    rw [Finset.card_insert_of_notMem hxC] at hm
    omega
  have herase : A.erase x = C := by rw [← he, Finset.erase_insert hxC]
  exact ⟨x, mem_extremes.mpr ⟨hxA, herase.symm ▸ hCP⟩, herase.symm ▸ hBC⟩

/-- Convex geometries with two removable points on every nonsingleton closed
set give exactly the inductive support plans. -/
theorem IsConvexGeometry.isPlan {A : Finset α} {P : Finset (Finset α)}
    (hP : IsConvexGeometry A P)
    (hTwo : ∀ B ∈ P, 2 ≤ B.card → (extremes P B).card = 2) : IsPlan A P := by
  classical
  induction hn : A.card using Nat.strong_induction_on generalizing A P with
  | h n ih =>
    by_cases hzero : A = ∅
    · subst A
      have he : P = {∅} := by
        ext B
        simp only [Finset.mem_singleton]
        exact ⟨fun h => Finset.subset_empty.mp (hP.bounded B h),
          fun h => h ▸ hP.empty_mem⟩
      rw [he]; exact IsPlan.empty
    by_cases hone : A.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hone
      have he : P = {∅, {a}} := by
        ext B
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun h => Finset.subset_singleton_iff.mp (hP.bounded B h),
          fun h => h.elim (fun e => e ▸ hP.empty_mem) (fun e => e ▸ hP.domain_mem)⟩
      rw [he]; exact IsPlan.singleton a
    have hcard : 2 ≤ A.card := by
      have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hzero)
      omega
    obtain ⟨a, b, hab, hext⟩ := Finset.card_eq_two.mp (hTwo A hP.domain_mem hcard)
    have ha : a ∈ extremes P A := by rw [hext]; simp
    have hb : b ∈ extremes P A := by rw [hext]; simp
    obtain ⟨haA, haP⟩ := mem_extremes.mp ha
    obtain ⟨hbA, hbP⟩ := mem_extremes.mp hb
    have make {C : Finset α} (hC : C ∈ P) (hlt : C.card < n) :
        IsPlan C (restrictPlan P C) := by
      apply ih C.card hlt (hP.restrict hC)
      · intro B hB hc
        have hm := Finset.mem_inter.mp hB
        rw [extremes_restrict (Finset.mem_powerset.mp hm.2)]
        exact hTwo B hm.1 hc
      · rfl
    have hQ := make haP (by rw [Finset.card_erase_of_mem haA]; omega)
    have hR := make hbP (by rw [Finset.card_erase_of_mem hbA]; omega)
    have hAB : A.erase a ∩ A.erase b = (A.erase a).erase b := by
      ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto
    have hCP : (A.erase a).erase b ∈ P := hAB ▸ hP.inter_mem _ haP _ hbP
    have hCb : (A.erase a).erase b ⊆ A.erase b := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1,
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)⟩
    apply IsPlan.step haA hbA hab hQ hR
    · exact ⟨Finset.mem_inter.mpr ⟨hCP, Finset.mem_powerset.mpr (Finset.erase_subset _ _)⟩,
        Finset.mem_inter.mpr ⟨hCP, Finset.mem_powerset.mpr hCb⟩⟩
    · ext X
      simp only [restrictPlan, Finset.mem_inter, Finset.mem_powerset]
      constructor
      · exact fun h => ⟨⟨h.1.1, h.2.trans hCb⟩, h.2⟩
      · exact fun h => ⟨⟨h.1.1, h.2.trans (Finset.erase_subset _ _)⟩, h.2⟩
    · ext X
      simp only [Finset.mem_union, Finset.mem_singleton, restrictPlan,
        Finset.mem_inter, Finset.mem_powerset]
      constructor
      · intro hX
        by_cases he : X = A
        · exact Or.inr he
        obtain ⟨x, hx, hsub⟩ := hP.exists_coatom hX he
        rw [hext, Finset.mem_insert, Finset.mem_singleton] at hx
        exact Or.inl (hx.elim (fun e => Or.inl ⟨hX, e ▸ hsub⟩)
          (fun e => Or.inr ⟨hX, e ▸ hsub⟩))
      · rintro ((h | h) | rfl)
        · exact h.1
        · exact h.1
        · exact hP.domain_mem

theorem isPlan_iff_convexGeometry {A : Finset α} {P : Finset (Finset α)} :
    IsPlan A P ↔ IsConvexGeometry A P ∧
      ∀ B ∈ P, 2 ≤ B.card → (extremes P B).card = 2 :=
  ⟨fun h => ⟨h.convexGeometry, fun _ => h.extremes_card⟩, fun h => h.1.isPlan h.2⟩

end VaughtConjecture.AmalgamationPlan.Plan
