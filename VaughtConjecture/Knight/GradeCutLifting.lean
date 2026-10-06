/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutBoundary
public import VaughtConjecture.Knight.CoatomBoundaryExtension

/-! # Exact lifting transport across an actual grade cut -/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GradeCutLifting
open Transform Value ExtOrd CoatomBoundaryExtension GradeCutBoundary
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (k : ℕ)

theorem lift_iff {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 ≤ k) :
    CappedLift (rows D k sem) h ↔ CappedLift sem h := by
  let eI := belowEquiv D k I (h.2.trans hJ)
  let eJ := belowEquiv D k J hJ
  have hm (d : (scheme D k).below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  have hi (d : D.below I) :
      eJ.symm (CellScheme.below.mono h d) = CellScheme.below.mono h (eI.symm d) := by
    apply eJ.injective
    rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply]
  constructor
  · intro hl p q γ hp hq hγ hag
    obtain ⟨r, hr, hc, hread⟩ := hl (p ∘ eI) (q ∘ eJ) γ
      (pullback_respects D k sem (h.2.trans hJ) hp)
      (pullback_respects D k sem hJ hq) hγ (fun d => hag (eI d))
    refine ⟨r ∘ eJ.symm, (respects_iff D k sem J hJ r).mp hr, ?_, ?_⟩
    · intro d
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hc (eJ.symm d)
    · intro d
      rw [Function.comp_apply, hi, hread]
      exact congrArg p (eI.apply_symm_apply d)
  · intro hl p q γ hp hq hγ hag
    obtain ⟨r, hr, hc, hread⟩ := hl (p ∘ eI.symm) (q ∘ eJ.symm) γ
      ((respects_iff D k sem I (h.2.trans hJ) p).mp hp)
      ((respects_iff D k sem J hJ q).mp hq) hγ (fun d => by
        simpa only [Function.comp_apply, hi] using hag (eI.symm d))
    refine ⟨r ∘ eJ, pullback_respects D k sem hJ hr, ?_, ?_⟩
    · intro d
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hc (eJ d)
    · intro d
      rw [Function.comp_apply, hm, hread]
      exact congrArg p (eI.symm_apply_apply d)

end VaughtConjecture.Knight.GradeCutLifting
