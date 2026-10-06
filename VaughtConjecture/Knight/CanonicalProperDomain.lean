/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedOwnerLift

/-! # Exact proper-domain transport through both canonical layers

Neither new layer adds an occurrence to a proper scope. The equivalences below
transport all rows and lawful target-local ambients, not only chosen sections.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalProperDomain
open Transform Value ExtOrd CanonicalMixedGradeLayers CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)
variable (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
variable (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

def equiv (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) :
    D.below BJ ≃ (scheme sem j hj hjA k hk hkA).below BJ :=
  (GradeCutLayerCarrier.properEquiv D (CanonicalGradeCutSections.Profiles sem j)
    j hj hjA BJ hB).trans
    (GradeCutLayerCarrier.properEquiv (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA BJ hB)

theorem equiv_cell (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) (d : D.below BJ) :
    (scheme sem j hj hjA k hk hkA).cell (equiv sem j hj hjA k hk hkA BJ hB d).1 =
      D.cell d.1 := by
  change (SourceLayerCarrier.scheme _ _ _ _ _).cell
    (SourceLayerCarrier.toCell _ _ _ _ _ (.inl
      (SourceLayerCarrier.toCell _ _ _ _ _ (.inl d.1)))) = _
  simp only [SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]

theorem respects_iff (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) (p : D.below BJ → ExtOrd) :
    RespectsSemanticsBelow sem BJ p ↔
      RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) BJ
        (p ∘ (equiv sem j hj hjA k hk hkA BJ hB).symm) := by
  apply respects_iff_of_equiv (equiv sem j hj hjA k hk hkA BJ hB)
    (fun d => ?_) (fun d e => ?_) (fun b d _ => ?_) p
  · exact (congrArg Prod.snd (equiv_cell sem j hj hjA k hk hkA BJ hB d)).symm
  · change (D.cell d.1).1 ⊆ (D.cell e.1).1 ↔ _
    simp only [CellScheme.scope, equiv_cell]
  · exact (original_row sem j hj hjA hproper k hg hk hkA hjk b.1 d).symm

theorem pullback_respects {BJ : Finset ι × ℕ} (hB : ¬ A ⊆ BJ.1)
    {q : (scheme sem j hj hjA k hk hkA).below BJ → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) BJ q) :
    RespectsSemanticsBelow sem BJ (q ∘ equiv sem j hj hjA k hk hkA BJ hB) := by
  apply (respects_iff sem j hj hjA hproper k hg hk hkA hjk BJ hB _).mpr
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hq

/-- Every proper-target lifting clause is exactly an old clause. -/
theorem lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hB : ¬ A ⊆ J.1)
    (hlift : CappedLift sem h) :
    CappedLift (rows sem j hj hjA hproper k hg hk hkA hjk) h := by
  intro p q γ hp hq hγ hag
  have hC : ¬ A ⊆ I.1 := fun hc => hB (hc.trans h.1)
  let eI := equiv sem j hj hjA k hk hkA I hC
  let eJ := equiv sem j hj hjA k hk hkA J hB
  have hm (d : D.below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  obtain ⟨r, hr, hcap, hread⟩ := hlift (p ∘ eI) (q ∘ eJ) γ
    (pullback_respects sem j hj hjA hproper k hg hk hkA hjk hC hp)
    (pullback_respects sem j hj hjA hproper k hg hk hkA hjk hB hq) hγ
    (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm, (respects_iff sem j hj hjA hproper k hg hk hkA hjk J hB r).mp hr,
    fun d => ?_, fun d => ?_⟩
  · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (eJ.symm d)
  · have hd : eJ.symm (CellScheme.below.mono h d) =
        CellScheme.below.mono h (eI.symm d) := by
      apply eJ.injective
      rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply]
    rw [Function.comp_apply, hd, hread]
    exact congrArg p (eI.apply_symm_apply d)

end
end VaughtConjecture.Knight.CanonicalProperDomain
