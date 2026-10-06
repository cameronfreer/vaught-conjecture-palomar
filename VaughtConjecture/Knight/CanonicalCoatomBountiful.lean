/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalOriginalLift
public import VaughtConjecture.Knight.CanonicalLowerAllCaps
public import VaughtConjecture.Knight.CanonicalProperDomain
public import VaughtConjecture.Knight.EffectiveGradeLifting

/-! # Bountifulness of the fixed canonical two-grade coatom carrier

The inputs are old proper-face lifting, old grade-one/two completeness, and
the two-face plan geometry. No completion, locality, serving controller, or
lifting theorem for the output is supplied. Nominal higher grades are handled
at the actual grade ceiling, retaining their original permitted caps.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalCoatomBountiful
open Transform Value ExtOrd CanonicalMixedGradeLayers CoatomBoundaryExtension AmalgamationPlan
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 2 ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ 2)

/-- The old proper-target clauses, including equality of indices. This is
supplied by the two inherited schemes, not by prospective output bountifulness. -/
def OldLifts : Prop :=
  ∀ I J, I ∈ Plan.gradedPlan D.plan → J ∈ Plan.gradedPlan D.plan → J.1 ≠ A →
    (h : GradedLe I J) → CappedLift sem h

variable (hold : OldLifts sem)

include hold in
private theorem overlap_lift {L R : Finset ι} (hR : R ∈ D.plan) (hRA : R ≠ A)
    (hO : L ∩ R ∈ D.plan) {n : ℕ} (hn : 0 < n) (hnR : n ≤ R.card) :
    CappedLift sem (target_le_right (U := (L, n)) (V := (R, n))) := by
  by_cases hne : (L ∩ R).Nonempty
  · exact hold _ _ (target_mem_gradedPlan hO hn hn hne)
      (Plan.mem_gradedPlan.mpr ⟨hR, hn, hnR⟩) hRA target_le_right
  · let := target_empty (D := D) (U := (L, n)) (V := (R, n))
      (Finset.not_nonempty_iff_eq_empty.mp hne)
    exact lift_empty target_le_right

include hold in
/-- Complete the full-index same-grade pair when the original face lies
on the designated left input. All numerical inputs remain arbitrary. -/
private theorem full_lift_left {L R C : Finset ι}
    (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
    (hLc : 2 ≤ L.card) (hRc : 2 ≤ R.card) (hO : L ∩ R ∈ D.plan)
    (hcover : ∀ d : Cell D, D.scope d ⊆ L ∨ D.scope d ⊆ R)
    (hC : C ∈ D.plan) (hCA : C ≠ A) (hCL : C ⊆ L)
    (hfull₁ : C.Nonempty → ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    (hfull₂ : 2 ≤ C.card → ∃ c : D.below (C, 2), D.cell c.1 = (C, 2))
    {n : ℕ} (hn : 0 < n) (hn2 : n ≤ 2) (hnC : n ≤ C.card)
    (h : GradedLe (C, n) (A, n)) :
    CappedLift (rows sem 1 (by decide) (by omega) hproper 2 hg
      (by decide) hA (by decide)) h := by
  have hCn : (C, n) ∈ Plan.gradedPlan D.plan := Plan.mem_gradedPlan.mpr ⟨hC, hn, hnC⟩
  have hC1 : (C, 1) ∈ Plan.gradedPlan D.plan :=
    Plan.mem_gradedPlan.mpr ⟨hC, (by decide : 0 < 1), (Nat.one_le_of_lt hn).trans hnC⟩
  have hCnot : ¬ A ⊆ C := fun ha => hCA (Finset.Subset.antisymm h.1 ha)
  have cover₂ (d : Cell D) : GradedLe (D.cell d) (L, 2) ∨ GradedLe (D.cell d) (R, 2) :=
    (hcover d).imp (fun hd => ⟨hd, hg d⟩) (fun hd => ⟨hd, hg d⟩)
  have cover₁ (d : Cell D) (hd : D.grade d ≤ 1) :
      GradedLe (D.cell d) (L, 1) ∨ GradedLe (D.cell d) (R, 1) :=
    (hcover d).imp (fun hs => ⟨hs, hd⟩) (fun hs => ⟨hs, hd⟩)
  have left₂ : CappedLift sem (show GradedLe (C, n) (L, 2) from ⟨hCL, hn2⟩) :=
    hold _ _ hCn (Plan.mem_gradedPlan.mpr ⟨hL, (by decide : 0 < 2), hLc⟩) hLA ⟨hCL, hn2⟩
  have left₁ : CappedLift sem (show GradedLe (C, 1) (L, 1) from ⟨hCL, le_rfl⟩) :=
    hold (C, 1) (L, 1) hC1 (Plan.mem_gradedPlan.mpr
      ⟨hL, (by decide : 0 < 1), (by decide : 1 ≤ 2).trans hLc⟩)
      hLA ⟨hCL, le_rfl⟩
  have right₂ := overlap_lift sem hold hR hRA hO (by decide : 0 < 2) hRc
  have right₁ := overlap_lift sem hold hR hRA hO (by decide : 0 < 1) (by omega)
  have inter (m : ℕ) (d : Cell D) (hl : GradedLe (D.cell d) (L, m))
      (hr : GradedLe (D.cell d) (R, m)) :
      GradedLe (D.cell d) (overlapTarget (L, m) (R, m)) := below_target_iff d |>.mpr ⟨hl, hr⟩
  intro p q γ hp hq hγ hag
  let e := CanonicalProperDomain.equiv sem 1 (by decide) (by omega) 2 (by decide) hA
    (C, n) hCnot
  have hp' := CanonicalProperDomain.pullback_respects sem 1 (by decide) (by omega) hproper
    2 hg (by decide) hA (by decide) hCnot hp
  have hncase : n = 1 ∨ n = 2 := by omega
  rcases hncase with rfl | rfl
  · obtain ⟨r, hr, hread, hcap⟩ := CanonicalLowerAllCaps.exists_lift sem hA hproper hg hfull₁
      hp' hq hγ (fun d => (hag (e d)).symm)
      cover₂ ⟨hCL, (by decide : 1 ≤ 2)⟩ target_le_left target_le_right (inter 2) left₂ right₂
      cover₁ ⟨hCL, le_rfl⟩ target_le_left target_le_right (inter 1) left₁ right₁ le_rfl le_rfl
    refine ⟨r, hr, hcap, fun d => ?_⟩
    have hh := hread (e.symm d)
    change r (CellScheme.below.mono h (e (e.symm d))) = p (e (e.symm d)) at hh
    simpa only [Equiv.apply_symm_apply] using hh
  · obtain ⟨r, hr, hread, hcap⟩ := CanonicalOriginalLift.exists_lift sem hA hproper hg le_rfl
      hfull₁ hfull₂ hp' hq hγ (fun d => (hag (e d)).symm)
      cover₂ ⟨hCL, le_rfl⟩ target_le_left target_le_right (inter 2) left₂ right₂ le_rfl le_rfl
      cover₁ ⟨hCL, le_rfl⟩ target_le_left target_le_right (inter 1) left₁ right₁ le_rfl le_rfl
    refine ⟨r, hr, hcap, fun d => ?_⟩
    have hh := hread (e.symm d)
    change r (CellScheme.below.mono h (e (e.symm d))) = p (e (e.symm d)) at hh
    simpa only [Equiv.apply_symm_apply] using hh

include hold in
/-- Whole-scheme bountifulness on the unchanged two-grade rows. The proper
input faces have room for grade two. Only their actual bountiful clauses,
grade-one/two owner incidences, and two-face geometry are premises.
This does not assert all-grade completeness, coding, or ordered installation. -/
theorem bountiful {L R : Finset ι}
    (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
    (hLc : 2 ≤ L.card) (hRc : 2 ≤ R.card) (hO : L ∩ R ∈ D.plan)
    (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ 2 →
      ∃ d : Cell D, D.cell d = (C, i)) :
    (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (fun d => (data sem 1 (by decide) (by omega) hproper 2 hg
      (by decide) hA (by decide)).max_grade d) (by decide : 0 < 2)
  intro C B i hCi hBi hi hCB
  change (C, i) ∈ Plan.gradedPlan D.plan at hCi
  change (B, i) ∈ Plan.gradedPlan D.plan at hBi
  by_cases hBA : B = A
  · subst B
    by_cases hCA : C = A
    · subst C; exact lift_refl
    have hc := Plan.mem_gradedPlan.mp hCi
    have hfull₁ (hne : C.Nonempty) : ∃ c : D.below (C, 1), D.cell c.1 = (C, 1) := by
      obtain ⟨c, he⟩ := hcomplete C hc.1 hCA 1 (by decide) (Finset.card_pos.mpr hne)
        (by decide)
      exact ⟨⟨c, by rw [he]; exact GradedLe.refl _⟩, he⟩
    have hfull₂ (hcard : 2 ≤ C.card) : ∃ c : D.below (C, 2), D.cell c.1 = (C, 2) := by
      obtain ⟨c, he⟩ := hcomplete C hc.1 hCA 2 (by decide) hcard le_rfl
      exact ⟨⟨c, by rw [he]; exact GradedLe.refl _⟩, he⟩
    have cells (d : Cell D) : D.scope d ⊆ L ∨ D.scope d ⊆ R :=
      hcover (D.scope d) (D.scope_mem_plan d) (hproper d)
    rcases hcover C hc.1 hCA with hl | hr
    · exact full_lift_left sem hA hproper hg hold hL hR hLA hRA hLc hRc hO cells
        hc.1 hCA hl hfull₁ hfull₂ hc.2.1 hi hc.2.2 ⟨hCB, le_rfl⟩
    · exact full_lift_left sem hA hproper hg hold hR hL hRA hLA hRc hLc
        (Finset.inter_comm L R ▸ hO) (fun d => (cells d).symm)
        hc.1 hCA hr hfull₁ hfull₂ hc.2.1 hi hc.2.2 ⟨hCB, le_rfl⟩
  · have hBnot : ¬ A ⊆ B := fun hb => hBA (Finset.Subset.antisymm
      (D.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hBi).1) hb)
    exact CanonicalProperDomain.lift sem 1 (by decide) (by omega) hproper 2 hg (by decide)
      hA (by decide) (I := (C, i)) (J := (B, i)) ⟨hCB, le_rfl⟩ hBnot
      (hold _ _ hCi hBi hBA ⟨hCB, le_rfl⟩)

end
end VaughtConjecture.Knight.CanonicalCoatomBountiful
