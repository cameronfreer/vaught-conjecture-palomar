/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics
public import VaughtConjecture.Knight.SameScopeBountiful

/-! # Recursive lifting: inherited targets and vertical pasting

Inherited lifting is transported by actual row and occurrence equations, not
catalogue equivalence. Vertical pasting retains the original upper-visible
cap and requires no bountifulness of the new output.
The active new-grade proper-face lift is not asserted here.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveLifting
open Transform Value ExtOrd CoatomBoundaryExtension
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))
open CanonicalRecursiveSuccessorRows CanonicalRecursiveSuccessorSections

/-- Every target omitting the new controller index transports its full
single-face lifting clause from the actual predecessor semantics. -/
theorem inherited_lift {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hJ : ¬ GradedLe (A, n + 4) J) (hb : CappedLift P.rows h) :
    CappedLift (rows sem n hA hp P) h := by
  intro p q γ hpr hqr hγ hag
  have hI : ¬ GradedLe (A, n + 4) I := fun hi => hJ (hi.trans h)
  let eI := equiv sem n hA I hI
  let eJ := equiv sem n hA J hJ
  have pull (B : Finset ι × ℕ) (hB : ¬ GradedLe (A, n + 4) B)
      (u : (carrier sem n hA).below B → ExtOrd)
      (hu : RespectsSemanticsBelow (rows sem n hA hp P) B u) :
      RespectsSemanticsBelow P.rows B (u ∘ equiv sem n hA B hB) := by
    apply (respects_iff sem n hA hp P B hB _).mpr
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using hu
  have hm (d : (predecessor sem n hA).below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  obtain ⟨r, hr, hcap, hread⟩ := hb (p ∘ eI) (q ∘ eJ) γ
    (pull I hI p hpr) (pull J hJ q hqr) hγ (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm, (respects_iff sem n hA hp P J hJ r).mp hr,
    fun d => ?_, fun d => ?_⟩
  · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (eJ.symm d)
  · have hd : eJ.symm (CellScheme.below.mono h d) =
        CellScheme.below.mono h (eI.symm d) := by
      apply eJ.injective
      rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply]
    rw [Function.comp_apply, hd, hread]
    exact congrArg p (eI.apply_symm_apply d)

theorem lower_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 ≤ n + 3)
    (hb : CappedLift P.rows h) : CappedLift (rows sem n hA hp P) h :=
  inherited_lift sem n hA hp P h (fun he => by have := he.2; omega) hb

/-- Vertical lifting uses the fixed rows at the original upper-visible cap;
it does not demand positive upward continuation of every lower state. -/
theorem same_scope_lift {B : Finset ι} {i j : ℕ} (h : GradedLe (B, i) (B, j)) :
    CappedLift (rows sem n hA hp P) h := bountiful_same_scope _ h

end
end VaughtConjecture.Knight.CanonicalRecursiveLifting
