/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalPairBoundary
public import VaughtConjecture.Knight.CanonicalCoatomBountiful

/-! # Actual two-grade restoration with higher proper owners retained

The lower carrier is the proved canonical two-grade output, not an assumed
future completion. Its arbitrary single-face lifts transport to the enlarged
carrier through grade two. This includes all controller coordinates and literal
top. No simultaneous prescription of independent old faces is asserted, and no
conclusion about the grade-three tail is inferred from the lower lift.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalPairLowerLifting
open Transform Value ExtOrd CanonicalPairBoundary CoatomBoundaryExtension AmalgamationPlan
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j k : ℕ)
variable (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A) (hjk : j < k)

theorem transport_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 ≤ k)
    (hl : CappedLift (lowerRows sem j k hj hjA hk hkA hp hjk) h) :
    CappedLift (rows sem j k hj hjA hk hkA hp hjk) h := by
  let eI := GradeCutPairCarrier.belowEquiv D (firstProfiles sem j k) (secondProfiles sem k)
    j k hj hjA hk hkA I (h.2.trans hJ)
  let eJ := GradeCutPairCarrier.belowEquiv D (firstProfiles sem j k) (secondProfiles sem k)
    j k hj hjA hk hkA J hJ
  have respect (B : Finset ι × ℕ) (hB : B.2 ≤ k)
      (q : (scheme sem j k hj hjA hk hkA).below B → ExtOrd)
      (hq : RespectsSemanticsBelow (rows sem j k hj hjA hk hkA hp hjk) B q) :
      RespectsSemanticsBelow (lowerRows sem j k hj hjA hk hkA hp hjk) B
        (q ∘ GradeCutPairCarrier.belowEquiv D _ _ j k hj hjA hk hkA B hB) := by
    apply (GradeCutPairRows.lower_respects_iff D _ _ j k hj hjA hk hkA hp hjk.le sem _
      (overlap sem j k hj hjA hk hkA hp hjk) B hB _).mpr
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using hq
  have hm (d : (lower sem j k hj hjA hk hkA).below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  intro p q γ hpr hqr hγ hag
  obtain ⟨r, hr, hcap, hread⟩ := hl (p ∘ eI) (q ∘ eJ) γ
    (respect I (h.2.trans hJ) p hpr) (respect J hJ q hqr) hγ (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm,
    (GradeCutPairRows.lower_respects_iff D _ _ j k hj hjA hk hkA hp hjk.le sem _
      (overlap sem j k hj hjA hk hkA hp hjk) J hJ r).mp hr,
    fun d => ?_, fun d => ?_⟩
  · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (eJ.symm d)
  · have he : eJ.symm (CellScheme.below.mono h d) = CellScheme.below.mono h (eI.symm d) := by
      apply eJ.injective
      rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply]
    rw [Function.comp_apply, he, hread]
    exact congrArg p (eI.apply_symm_apply d)

include hk in
/-- Grade restriction obtains its proper-target clauses from the old schemes.
Nominal indices above the cut are handled at the effective grade, without
changing the external cap. -/
theorem cut_oldLifts (hold : CanonicalCoatomBountiful.OldLifts sem) :
    CanonicalCoatomBountiful.OldLifts (boundaryRows sem k) := by
  intro I J hI hJ hJA h
  apply EffectiveGradeLifting.lift (GradeCutBoundary.grade_bound D k) h
  apply CanonicalLowerLift.cut_lift (EffectiveGradeLifting.cut_le h) (min_le_right _ _)
  have mem (B : Finset ι × ℕ) (hB : B ∈ Plan.gradedPlan D.plan) :
      EffectiveGradeLifting.cut (K := k) B ∈ Plan.gradedPlan D.plan := by
    obtain ⟨hs, hi, hc⟩ := Plan.mem_gradedPlan.mp hB
    exact Plan.mem_gradedPlan.mpr ⟨hs, lt_min hi hk, (min_le_left _ _).trans hc⟩
  exact hold _ _ (mem I hI) (mem J hJ) hJA (EffectiveGradeLifting.cut_le h)

variable (hA : 2 ≤ A.card) (hold : CanonicalCoatomBountiful.OldLifts sem)
variable {L R : Finset ι}
variable (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
variable (hLc : 2 ≤ L.card) (hRc : 2 ≤ R.card) (hO : L ∩ R ∈ D.plan)
variable (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
variable (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ 2 →
  ∃ d : Cell D, D.cell d = (C, i))

include hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
/-- Bountifulness of the actual grade-one/two lower carrier is constructed
from the two old schemes' clauses even when their proper owners have grade three
or higher. All original occurrences through grade two are retained. -/
theorem lower_bountiful :
    (lowerRows sem 1 2 (by decide) ((by decide : 1 ≤ 2).trans hA)
      (by decide) hA hp (by decide)).IsBountiful := by
  apply CanonicalCoatomBountiful.bountiful (boundaryRows sem 2) hA
    (GradeCutBoundary.proper D 2 hp) (GradeCutBoundary.grade_bound D 2)
    (cut_oldLifts sem 2 (by decide) hold) hL hR hLA hRA hLc hRc hO hcover
  intro C hC hCA i hi hiC hi2
  obtain ⟨d, hd⟩ := hcomplete C hC hCA i hi hiC hi2
  have hg : D.grade d ≤ 2 := by change (D.cell d).2 ≤ 2; rw [hd]; exact hi2
  refine ⟨GradeCutBoundary.fromCell D 2 d hg, ?_⟩
  exact (congrArg D.cell (GradeCutBoundary.to_from D 2 d hg)).trans hd

include hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
/-- One arbitrary lawful prescribed face, one arbitrary lawful lower ambient,
and the original permitted cap. The conclusion preserves the entire auxiliary
vector through grade two; no conditions on a future grade-three row are inputs. -/
theorem lower_lift {I J : Finset ι × ℕ}
    (hI : I ∈ Plan.gradedPlan D.plan) (hJ : J ∈ Plan.gradedPlan D.plan)
    (h : GradedLe I J) (hJ2 : J.2 ≤ 2) :
    CappedLift (rows sem 1 2 (by decide) ((by decide : 1 ≤ 2).trans hA)
      (by decide) hA hp (by decide)) h := by
  apply transport_lift sem 1 2 (by decide) ((by decide : 1 ≤ 2).trans hA)
    (by decide) hA hp (by decide) h hJ2
  have hb := lower_bountiful sem hp hA hold hL hR hLA hRA hLc hRc hO hcover hcomplete
  by_cases he : I = J
  · subst J; exact lift_refl
  · exact hb I J hI hJ h he

end
end VaughtConjecture.Knight.CanonicalPairLowerLifting
