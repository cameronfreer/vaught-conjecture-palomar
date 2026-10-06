/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.AmalgamationPlan.Plan

/-! # Visible faces have one-coordinate visible superfaces

Every proper visible face in an amalgamation plan lies below a visible face obtained by
adding exactly one coordinate — the plan kernel that iterates the paper's literal one-point
Proposition 7.3.3 (`Knight/OnePointRootedExtension.lean`).  Reviewer probe (2026-09-04),
graduated. -/

@[expose] public section

namespace VaughtConjecture.AmalgamationPlan.Plan

variable {alpha : Type*} [DecidableEq alpha]

theorem IsPlan.exists_visible_card_succ_superface
    {A : Finset alpha} {P : Finset (Finset alpha)}
    (hP : IsPlan A P) {B : Finset alpha} (hB : B ∈ P) (hne : B ≠ A) :
    ∃ C : Finset alpha, C ∈ P ∧ B ⊂ C ∧ C.card = B.card + 1 := by
  induction hP generalizing B with
  | empty =>
      simp only [Finset.mem_singleton] at hB
      exact absurd hB hne
  | singleton a =>
      simp only [Finset.mem_insert, Finset.mem_singleton] at hB
      rcases hB with rfl | hB
      · refine ⟨{a}, by simp, ?_, by simp⟩
        exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.empty_subset _, by simp⟩
      · exact absurd hB hne
  | @step A a b Q R P ha hb hab hQ hR h_inter h_restr hP ihQ ihR =>
      subst hP
      simp only [Finset.mem_union, Finset.mem_singleton] at hB
      rcases hB with (hBQ | hBR) | hBA
      · by_cases htop : B = A.erase a
        · subst B
          refine ⟨A, by simp, ?_, ?_⟩
          · exact Finset.ssubset_iff_subset_ne.mpr
              ⟨Finset.erase_subset _ _, fun h =>
                Finset.notMem_erase a A (by rw [h]; exact ha)⟩
          · exact (Finset.card_erase_add_one ha).symm
        · obtain ⟨C, hCQ, hBC, hcard⟩ := ihQ hBQ htop
          exact ⟨C, by simp [hCQ], hBC, hcard⟩
      · by_cases htop : B = A.erase b
        · subst B
          refine ⟨A, by simp, ?_, ?_⟩
          · exact Finset.ssubset_iff_subset_ne.mpr
              ⟨Finset.erase_subset _ _, fun h =>
                Finset.notMem_erase b A (by rw [h]; exact hb)⟩
          · exact (Finset.card_erase_add_one hb).symm
        · obtain ⟨C, hCR, hBC, hcard⟩ := ihR hBR htop
          exact ⟨C, by simp [hCR], hBC, hcard⟩
      · exact absurd hBA hne

end VaughtConjecture.AmalgamationPlan.Plan
