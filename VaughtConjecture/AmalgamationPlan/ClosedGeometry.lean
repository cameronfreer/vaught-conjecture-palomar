/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.AmalgamationPlan.Plan
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Closed-set geometry of finite support plans

The inductive construction interface is unchanged. Visible faces are closed under
intersection, so a finite set of points has a least visible superset inside the domain.
This is a canonical support, not a canonical enumeration of that support.
-/

@[expose] public section

namespace VaughtConjecture.AmalgamationPlan.Plan

variable {α : Type*} [DecidableEq α]

/-- Intersections of visible faces are visible. -/
theorem IsPlan.inter_mem {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) {X Y : Finset α} (hX : X ∈ P) (hY : Y ∈ P) : X ∩ Y ∈ P := by
  induction hP generalizing X Y with
  | empty =>
    simp only [Finset.mem_singleton] at hX hY
    simp [hX, hY]
  | singleton a =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY ⊢
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp
  | @step A a b Q R P ha hb hab hQ hR hm he hP ihQ ihR =>
    subst P
    have cross {U V : Finset α} (hU : U ∈ Q) (hV : V ∈ R) : U ∩ V ∈ R := by
      have hcut := ihQ hU hm.1
      have hcutR : U ∩ (A.erase a).erase b ∈ R := by
        have hc : U ∩ (A.erase a).erase b ∈ Q ∩ ((A.erase a).erase b).powerset :=
          Finset.mem_inter.mpr ⟨hcut, Finset.mem_powerset.mpr Finset.inter_subset_right⟩
        rw [he] at hc
        exact (Finset.mem_inter.mp hc).1
      have hc := ihR hcutR hV
      have eqn : (U ∩ (A.erase a).erase b) ∩ V = U ∩ V := by
        ext x
        simp only [Finset.mem_inter]
        constructor
        · exact fun h => ⟨h.1.1, h.2⟩
        · intro h
          exact ⟨⟨h.1, Finset.mem_erase.mpr
            ⟨(Finset.mem_erase.mp (hR.subset_of_mem hV h.2)).1,
              hQ.subset_of_mem hU h.1⟩⟩, h.2⟩
      rwa [eqn] at hc
    simp only [Finset.mem_union, Finset.mem_singleton] at hX hY ⊢
    rcases hX with (hX | hX) | rfl
    · rcases hY with (hY | hY) | rfl
      · exact Or.inl (Or.inl (ihQ hX hY))
      · exact Or.inl (Or.inr (cross hX hY))
      · rw [Finset.inter_eq_left.mpr ((hQ.subset_of_mem hX).trans (Finset.erase_subset _ _))]
        exact Or.inl (Or.inl hX)
    · rcases hY with (hY | hY) | rfl
      · rw [Finset.inter_comm]; exact Or.inl (Or.inr (cross hY hX))
      · exact Or.inl (Or.inr (ihR hX hY))
      · rw [Finset.inter_eq_left.mpr ((hR.subset_of_mem hX).trans (Finset.erase_subset _ _))]
        exact Or.inl (Or.inr hX)
    · rcases hY with (hY | hY) | rfl
      · rw [Finset.inter_eq_right.mpr ((hQ.subset_of_mem hY).trans (Finset.erase_subset _ _))]
        exact Or.inl (Or.inl hY)
      · rw [Finset.inter_eq_right.mpr ((hR.subset_of_mem hY).trans (Finset.erase_subset _ _))]
        exact Or.inl (Or.inr hY)
      · simp

/-- Finite intersection of all visible supersets, with the domain as the default bound.
The closure laws below require that the input is contained in that domain. -/
def hull (A : Finset α) (P : Finset (Finset α)) (S : Finset α) : Finset α :=
  (insert A (P.filter (S ⊆ ·))).inf' (Finset.insert_nonempty _ _) id

theorem mem_hull {A S : Finset α} {P : Finset (Finset α)} {x : α} :
    x ∈ hull A P S ↔ x ∈ A ∧ ∀ B ∈ P, S ⊆ B → x ∈ B := by
  simp [hull, Finset.mem_inf']

theorem subset_hull {A S : Finset α} {P : Finset (Finset α)} (hS : S ⊆ A) :
    S ⊆ hull A P S := by
  intro x hx
  exact mem_hull.mpr ⟨hS hx, fun _ _ h => h hx⟩

theorem hull_subset_domain (A S : Finset α) (P : Finset (Finset α)) :
    hull A P S ⊆ A := fun _ hx => (mem_hull.mp hx).1

theorem hull_minimal {A S B : Finset α} {P : Finset (Finset α)}
    (hB : B ∈ P) (hSB : S ⊆ B) : hull A P S ⊆ B :=
  fun _ hx => (mem_hull.mp hx).2 B hB hSB

theorem IsPlan.hull_mem {A S : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) : hull A P S ∈ P := by
  apply Finset.inf'_induction
  · exact fun _ hX _ hY => hP.inter_mem hX hY
  · intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact hP.domain_mem
    · exact (Finset.mem_filter.mp hB).1

theorem IsPlan.hull_eq {A B : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) (hB : B ∈ P) : hull A P B = B :=
  Finset.Subset.antisymm (hull_minimal hB (Finset.Subset.refl _))
    (subset_hull (hP.subset_of_mem hB))

theorem hull_mono {A S T : Finset α} {P : Finset (Finset α)} (hST : S ⊆ T) :
    hull A P S ⊆ hull A P T := by
  intro x hx
  obtain ⟨ha, h⟩ := mem_hull.mp hx
  exact mem_hull.mpr ⟨ha, fun B hB hTB => h B hB (hST.trans hTB)⟩

theorem IsPlan.hull_idem {A S : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) : hull A P (hull A P S) = hull A P S := hP.hull_eq hP.hull_mem

theorem IsPlan.hull_eq_iff_mem {A S : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) : hull A P S = S ↔ S ∈ P :=
  ⟨fun h => h ▸ hP.hull_mem, hP.hull_eq⟩

/-- Computing a hull inside a visible face gives the same literal support. -/
theorem IsPlan.hull_restrict {A B S : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) (hB : B ∈ P) (hSB : S ⊆ B) :
    hull B (restrictPlan P B) S = hull A P S := by
  apply Finset.Subset.antisymm
  · exact hull_minimal (Finset.mem_inter.mpr
      ⟨hP.hull_mem, Finset.mem_powerset.mpr (hull_minimal hB hSB)⟩)
      (subset_hull (hSB.trans (hP.subset_of_mem hB)))
  · exact hull_minimal
      (Finset.mem_inter.mp ((restrict_isPlan hP hB).hull_mem (S := S))).1
      (subset_hull hSB)

end VaughtConjecture.AmalgamationPlan.Plan
