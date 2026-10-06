/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalProperOwnerLayer
public import VaughtConjecture.Knight.HighLayerBountiful

/-! # The retained pair supplies actual lower restoration

The new upper row is absent from every grade-two target. Its lower lift is
therefore the proved two-grade lift transported across literal rows. Proper
original faces retain their exact local semantics, including long rows.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalProperOwnerLower
open Transform Value ExtOrd CanonicalProperOwnerLayer CoatomBoundaryExtension
open AmalgamationPlan
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (k : ℕ) (h2k : 2 < k) (hkA : k ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ k)

abbrev equiv (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, k) J) :=
  HighLayerBountiful.equiv (lowerScheme sem k h2k hkA) (Profile sem k)
    k (positive k h2k) hkA J hJ

theorem respects_iff (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, k) J)
    (p : (lowerScheme sem k h2k hkA).below J → ExtOrd) :
    RespectsSemanticsBelow (lowerSem sem k h2k hkA hp) J p ↔
      RespectsSemanticsBelow (rows sem k h2k hkA hp hg) J
        (p ∘ (equiv sem k h2k hkA J hJ).symm) := by
  apply respects_iff_of_equiv (equiv sem k h2k hkA J hJ)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell
      (lowerScheme sem k h2k hkA) (Profile sem k) k (positive k h2k) hkA J hJ d)).symm)
    (fun d e => ?_) (fun b d _ => ?_) p
  · simp only [CellScheme.scope, equiv, HighLayerBountiful.equiv_cell]
  · exact (inherited_row sem k h2k hkA hp hg b.1 d).symm

theorem pullback_respects {J : Finset ι × ℕ} (hJ : ¬ GradedLe (A, k) J)
    {q : (scheme sem k h2k hkA).below J → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem k h2k hkA hp hg) J q) :
    RespectsSemanticsBelow (lowerSem sem k h2k hkA hp) J
      (q ∘ equiv sem k h2k hkA J hJ) := by
  apply (respects_iff sem k h2k hkA hp hg J hJ _).mpr
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hq

theorem transport_lift {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hJ : ¬ GradedLe (A, k) J) (hb : CappedLift (lowerSem sem k h2k hkA hp) h) :
    CappedLift (rows sem k h2k hkA hp hg) h := by
  intro p q γ hpr hqr hγ hag
  have hI : ¬ GradedLe (A, k) I := fun hI => hJ (hI.trans h)
  let eI := equiv sem k h2k hkA I hI
  let eJ := equiv sem k h2k hkA J hJ
  have hm (d : (lowerScheme sem k h2k hkA).below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  obtain ⟨r, hr, hcap, hread⟩ := hb (p ∘ eI) (q ∘ eJ) γ
    (pullback_respects sem k h2k hkA hp hg hI hpr)
    (pullback_respects sem k h2k hkA hp hg hJ hqr) hγ (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm,
    (respects_iff sem k h2k hkA hp hg J hJ r).mp hr, fun d => ?_, fun d => ?_⟩
  · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (eJ.symm d)
  · have hd : eJ.symm (CellScheme.below.mono h d) =
        CellScheme.below.mono h (eI.symm d) := by
      apply eJ.injective
      rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply]
    rw [Function.comp_apply, hd, hread]
    exact congrArg p (eI.apply_symm_apply d)

def properEquiv (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) :
    D.below J ≃ (scheme sem k h2k hkA).below J :=
  (GradeCutPairCarrier.properEquiv D
    (CanonicalPairBoundary.firstProfiles sem 1 2) (CanonicalPairBoundary.secondProfiles sem 2)
    1 2 (by decide) (one_le k h2k hkA) (by decide) (two_le k h2k hkA) J hJ).trans
    (equiv sem k h2k hkA J (fun h => hJ h.1))

theorem proper_respects_iff (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1)
    (p : D.below J → ExtOrd) :
    RespectsSemanticsBelow sem J p ↔
      RespectsSemanticsBelow (rows sem k h2k hkA hp hg) J
        (p ∘ (properEquiv sem k h2k hkA J hJ).symm) := by
  exact (GradeCutPairRows.proper_respects_iff D _ _ 1 2 (by decide)
    (one_le k h2k hkA) (by decide) (two_le k h2k hkA) hp (by decide) sem
    (CanonicalPairBoundary.lowerRows sem 1 2 (by decide) (one_le k h2k hkA)
      (by decide) (two_le k h2k hkA) hp (by decide)) J hJ p).trans
    (respects_iff sem k h2k hkA hp hg J (fun h => hJ h.1) _)

variable (hold : CanonicalCoatomBountiful.OldLifts sem) {L R : Finset ι}
variable (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
variable (hLc : 2 ≤ L.card) (hRc : 2 ≤ R.card) (hO : L ∩ R ∈ D.plan)
variable (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
variable (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ 2 →
  ∃ d : Cell D, D.cell d = (C, i))

include hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
/-- Arbitrary lower prescriptions and ambients, with every actual auxiliary
cap retained. The lower carrier's lifting is proved from old-face clauses. -/
theorem lower_lift {I J : Finset ι × ℕ}
    (hI : I ∈ Plan.gradedPlan D.plan) (hJ : J ∈ Plan.gradedPlan D.plan)
    (h : GradedLe I J) (hJ2 : J.2 ≤ 2) :
    CappedLift (rows sem k h2k hkA hp hg) h := by
  apply transport_lift sem k h2k hkA hp hg h
    (fun hnew => (not_le_of_gt h2k) (hnew.2.trans hJ2))
  exact CanonicalPairLowerLifting.lower_lift sem hp (two_le k h2k hkA) hold
    hL hR hLA hRA hLc hRc hO hcover hcomplete hI hJ h hJ2

end
end VaughtConjecture.Knight.CanonicalProperOwnerLower
