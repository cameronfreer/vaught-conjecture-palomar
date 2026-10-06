/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSeedFullLift
public import VaughtConjecture.Knight.CanonicalCoatomBountiful

/-! # Bountifulness of the actual recursive grade-three seed

The predecessor retains higher proper owners. Only its current grade cut is
supplied by the proved lower-pair theorem at initialization; this layer supplies
bountifulness at the grade-three cut.
Every proper row and occurrence remains literal, and the constructed state
already supplies the selected-section contract. Old coatom geometry and
old-face lifting remain explicit, separate from ordered installation.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalSeedBountiful
open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan
open CanonicalRecursiveSeedRows CanonicalSeedCutPrefix CanonicalSeedActiveLift
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)
variable (hb : CanonicalSeedRestoration.LowerBountiful sem hA hp)
variable (hold : CanonicalCoatomBountiful.OldLifts sem) {L R : Finset ι}
variable (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
variable (hLc : 3 ≤ L.card) (hRc : 3 ≤ R.card) (hO : L ∩ R ∈ D.plan)
variable (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
variable (hcomplete : ∀ C ∈ D.plan, C ≠ A → 3 ≤ C.card →
  ∃ d : Cell D, D.cell d = (C, 3))

include hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
theorem full_left {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A)
    (hCc : 3 ≤ C.card) (hCL : C ⊆ L) :
    CappedLift (outputRows sem hA hp)
      (show GradedLe (C, 3) (A, 3) from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  have cover (d : Cell (cut (D := D))) :
      GradedLe ((cut (D := D)).cell d) (L, 3) ∨
      GradedLe ((cut (D := D)).cell d) (R, 3) :=
    (hcover _ (D.scope_mem_plan _) (hp (occurrence (D := D) d))).imp
      (fun h => ⟨h, GradeCutBoundary.grade_bound D _ d⟩)
      (fun h => ⟨h, GradeCutBoundary.grade_bound D _ d⟩)
  have left : CappedLift (cutRows sem)
      (show GradedLe (C, 3) (L, 3) from ⟨hCL, le_rfl⟩) :=
    (GradeCutLifting.lift_iff sem 3 _ le_rfl).mpr
      (hold (C, 3) (L, 3) (Plan.mem_gradedPlan.mpr ⟨hC, by omega, hCc⟩)
        (Plan.mem_gradedPlan.mpr ⟨hL, by omega, hLc⟩) hLA ⟨hCL, le_rfl⟩)
  have right : CappedLift (cutRows sem)
      (target_le_right (U := (L, 3)) (V := (R, 3))) := by
    apply (GradeCutLifting.lift_iff sem 3 _ le_rfl).mpr
    by_cases hne : (L ∩ R).Nonempty
    · exact hold _ _ (target_mem_gradedPlan hO
        (by omega : 0 < 3) (by omega : 0 < 3) hne)
        (Plan.mem_gradedPlan.mpr ⟨hR, by omega, hRc⟩) hRA target_le_right
    · let := target_empty (D := D) (U := (L, 3)) (V := (R, 3))
        (Finset.not_nonempty_iff_eq_empty.mp hne)
      exact lift_empty target_le_right
  have hfull : ∃ c : (cut (D := D)).below (C, 3),
      (cut (D := D)).cell c.1 = (C, 3) := by
    obtain ⟨d, hd⟩ := hcomplete C hC hCA hCc
    have hgd : D.grade d ≤ 3 := (congrArg Prod.snd hd).le
    let c := GradeCutBoundary.fromCell D 3 d hgd
    have hc : (cut (D := D)).cell c = (C, 3) := by
      change D.cell (GradeCutBoundary.toCell D 3 c) = _
      rw [GradeCutBoundary.to_from, hd]
    exact ⟨⟨c, by rw [hc]; exact GradedLe.refl _⟩, hc⟩
  exact CanonicalSeedFullLift.full_lift sem hA hp hC hCA cover
    ⟨hCL, le_rfl⟩ target_le_left target_le_right
    (fun d hl hr => (below_target_iff d).mpr ⟨hl, hr⟩) left right hb hCc hfull le_rfl le_rfl

include hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
theorem full_lift {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A)
    (hCc : 3 ≤ C.card) :
    CappedLift (outputRows sem hA hp)
      (show GradedLe (C, 3) (A, 3) from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  rcases hcover C hC hCA with hl | hr
  · exact full_left sem hA hp hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete
      hC hCA hCc hl
  · exact full_left sem hA hp hb hold hR hL hRA hLA hRc hLc
      (Finset.inter_comm L R ▸ hO) (fun C hC hCA => (hcover C hC hCA).symm)
      hcomplete hC hCA hCc hr

include hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
/-- Exhaustive literal-pair ledger on the enlarged actual grade cut.
The original permitted cap is unchanged, including bottom and literal top. -/
theorem bountiful :
    (GradeCutBoundary.rows (carrier sem hA) 3 (outputRows sem hA hp)).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (GradeCutBoundary.grade_bound (carrier sem hA) 3) (by omega)
  intro C B i hC hB hi hCB
  change (C, i) ∈ Plan.gradedPlan (carrier sem hA).plan at hC
  change (B, i) ∈ Plan.gradedPlan (carrier sem hA).plan at hB
  have hc : (C, i) ∈ Plan.gradedPlan D.plan := by
    simpa only [carrier_eq_recursive, CanonicalRecursiveBoundaryTransport.plan_eq] using hC
  have hb' : (B, i) ∈ Plan.gradedPlan D.plan := by
    simpa only [carrier_eq_recursive, CanonicalRecursiveBoundaryTransport.plan_eq] using hB
  apply (GradeCutLifting.lift_iff (outputRows sem hA hp) 3 _ hi).mpr
  by_cases hil : i ≤ 2
  · apply CanonicalSeedLifting.lower_lift sem hA hp
      _ hil
    apply (GradeCutLifting.lift_iff (predecessorRows sem hA hp) 2 _ hil).mp
    apply lift_of_bountiful hb
    · change (C, i) ∈ Plan.gradedPlan D.plan
      exact hc
    · change (B, i) ∈ Plan.gradedPlan D.plan
      exact hb'
  have hik : i = 3 := by omega
  subst i
  by_cases hBA : B = A
  · subst B
    by_cases hCA : C = A
    · subst C; exact lift_refl
    · exact full_lift sem hA hp hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete
        (Plan.mem_gradedPlan.mp hc).1 hCA (Plan.mem_gradedPlan.mp hc).2.2
  · apply CanonicalRecursiveBoundaryTransport.proper_lift sem hp 0 hA _
      (fun h => hBA (Finset.Subset.antisymm
        (D.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hb').1) h))
    exact hold _ _ hc hb' hBA ⟨hCB, le_rfl⟩

end
end VaughtConjecture.Knight.CanonicalSeedBountiful
