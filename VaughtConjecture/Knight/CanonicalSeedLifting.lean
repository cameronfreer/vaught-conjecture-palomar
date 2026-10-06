/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics
public import VaughtConjecture.Knight.SameScopeBountiful
public import VaughtConjecture.Knight.GradeCutLifting

/-! # Recursive lifting: inherited targets and vertical pasting

Inherited lifting is transported by actual row and occurrence equations, not
catalogue equivalence. Vertical pasting retains the original upper-visible
cap and requires no bountifulness of the new output.
The active new-grade proper-face lift is not asserted here.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalSeedLifting
open Transform Value ExtOrd CoatomBoundaryExtension
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)
open CanonicalRecursiveSeedRows CanonicalRecursiveSeedSections

/-- Every target omitting the new controller index transports its full
single-face lifting clause from the actual predecessor semantics. -/
theorem inherited_lift {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hJ : ¬ GradedLe (A, 3) J) (hb : CappedLift (predecessorRows sem hA hp) h) :
    CappedLift (rows sem hA hp) h := by
  intro p q γ hpr hqr hγ hag
  have hI : ¬ GradedLe (A, 3) I := fun hi => hJ (hi.trans h)
  let eI := equiv sem hA I hI
  let eJ := equiv sem hA J hJ
  have pull (B : Finset ι × ℕ) (hB : ¬ GradedLe (A, 3) B)
      (u : (carrier sem hA).below B → ExtOrd)
      (hu : RespectsSemanticsBelow (rows sem hA hp) B u) :
      RespectsSemanticsBelow (predecessorRows sem hA hp) B (u ∘ equiv sem hA B hB) := by
    apply (respects_iff sem hA hp B hB _).mpr
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using hu
  have hm (d : (predecessor sem hA).below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  obtain ⟨r, hr, hcap, hread⟩ := hb (p ∘ eI) (q ∘ eJ) γ
    (pull I hI p hpr) (pull J hJ q hqr) hγ (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm, (respects_iff sem hA hp J hJ r).mp hr,
    fun d => ?_, fun d => ?_⟩
  · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (eJ.symm d)
  · have hd : eJ.symm (CellScheme.below.mono h d) =
        CellScheme.below.mono h (eI.symm d) := by
      apply eJ.injective
      rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply]
    rw [Function.comp_apply, hd, hread]
    exact congrArg p (eI.apply_symm_apply d)

theorem lower_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 ≤ 2)
    (hb : CappedLift (predecessorRows sem hA hp) h) : CappedLift (rows sem hA hp) h :=
  inherited_lift sem hA hp h (fun he => by have := he.2; omega) hb

/-- Vertical lifting uses the fixed rows at the original upper-visible cap;
it does not demand positive upward continuation of every lower state. -/
theorem same_scope_lift {B : Finset ι} {i j : ℕ} (h : GradedLe (B, i) (B, j)) :
    CappedLift (rows sem hA hp) h := bountiful_same_scope _ h

/-- Actual lower-pair bountifulness comes from the banked two-grade theorem
through its proved row transport, not from a catalogue identification. -/
theorem predecessor_bountiful (hold : CanonicalCoatomBountiful.OldLifts sem)
    {L R : Finset ι} (hL : L ∈ D.plan) (hR : R ∈ D.plan)
    (hLA : L ≠ A) (hRA : R ≠ A) (hLc : 2 ≤ L.card) (hRc : 2 ≤ R.card)
    (hO : L ∩ R ∈ D.plan)
    (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ 2 →
      ∃ d : Cell D, D.cell d = (C, i)) :
    (GradeCutBoundary.rows (predecessor sem hA) 2 (predecessorRows sem hA hp)).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (GradeCutBoundary.grade_bound (predecessor sem hA) 2) (by decide)
  intro C B i hC hB hi hCB
  apply (GradeCutLifting.lift_iff (predecessorRows sem hA hp) 2 _ hi).mpr
  exact CanonicalPairLowerLifting.lower_lift sem hp (two_le hA)
    hold hL hR hLA hRA hLc hRc hO hcover hcomplete hC hB ⟨hCB, le_rfl⟩ hi

end
end VaughtConjecture.Knight.CanonicalSeedLifting
