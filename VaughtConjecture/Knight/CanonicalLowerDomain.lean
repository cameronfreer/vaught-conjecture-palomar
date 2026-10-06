/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedGradeLayers

/-! # The actual lower domain of the canonical two-layer output

Adding the upper layer does not alter the lower-grade domain, its rows, or
availability. These are literal occurrence equivalences, not an assumption
that an arbitrary lower ambient extends to the whole output.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalLowerDomain
open Transform Value ExtOrd CanonicalMixedGradeLayers
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)
variable (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
variable (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

def upperEquiv (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j) :
    (lowerScheme sem j hj hjA).below BJ ≃ (scheme sem j hj hjA k hk hkA).below BJ :=
  Equiv.ofBijective (fun d => ⟨oldCell sem j hj hjA k hk hkA d.1, by
    simpa only [oldCell, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using d.2⟩)
    ⟨by
      intro d e he
      exact Subtype.ext ((inherited_order sem j hj hjA k hk hkA).injective
        (congrArg Subtype.val he)), by
      intro d
      have hd : (scheme sem j hj hjA k hk hkA).cell d.1 ≠ (A, k) := by
        intro he
        have hg := d.2.2
        rw [he] at hg
        exact (not_le_of_gt hjk) (hg.trans hBJ)
      obtain ⟨e, he⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
        (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA d.1 hd
      have hem : GradedLe ((lowerScheme sem j hj hjA).cell e) BJ := by
        have hm := d.2
        rw [he, SourceLayerCarrier.cell_toCell] at hm
        exact hm
      exact ⟨⟨e, hem⟩, Subtype.ext he.symm⟩⟩

theorem upperEquiv_cell (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j)
    (d : (lowerScheme sem j hj hjA).below BJ) :
    (scheme sem j hj hjA k hk hkA).cell
      (upperEquiv sem j hj hjA k hk hkA hjk BJ hBJ d).1 =
      (lowerScheme sem j hj hjA).cell d.1 :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d.1)

theorem upper_respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j)
    (p : (lowerScheme sem j hj hjA).below BJ → ExtOrd) :
    RespectsSemanticsBelow (lowerSem sem j hj hjA hproper) BJ p ↔
      RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) BJ
        (p ∘ (upperEquiv sem j hj hjA k hk hkA hjk BJ hBJ).symm) := by
  apply respects_iff_of_equiv (upperEquiv sem j hj hjA k hk hkA hjk BJ hBJ)
    (fun d => ?_) (fun d e => ?_) (fun b d _ => ?_) p
  · exact (congrArg Prod.snd (upperEquiv_cell sem j hj hjA k hk hkA hjk BJ hBJ d)).symm
  · change ((lowerScheme sem j hj hjA).cell d.1).1 ⊆
        ((lowerScheme sem j hj hjA).cell e.1).1 ↔ _
    simp only [CellScheme.scope, upperEquiv_cell]
  · exact (inherited_row sem j hj hjA hproper k hg hk hkA hjk b.1 d).symm

def equiv (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j) :
    (CanonicalGradeCutSections.lower sem j hj hjA).below BJ ≃
      (scheme sem j hj hjA k hk hkA).below BJ :=
  (GradeCutLayerCarrier.belowEquiv D (CanonicalGradeCutSections.Profiles sem j)
    j hj hjA BJ hBJ).trans (upperEquiv sem j hj hjA k hk hkA hjk BJ hBJ)

theorem respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j)
    (p : (CanonicalGradeCutSections.lower sem j hj hjA).below BJ → ExtOrd) :
    RespectsSemanticsBelow (CanonicalGradeCutSections.lowerRows sem j hj hjA hproper) BJ p ↔
      RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) BJ
        (p ∘ (equiv sem j hj hjA k hk hkA hjk BJ hBJ).symm) := by
  exact (GradeCutLayerRows.lower_respects_iff D (CanonicalGradeCutSections.Profiles sem j)
    j hj hjA hproper sem (CanonicalGradeCutSections.lowerRows sem j hj hjA hproper)
    (CanonicalGradeCutSections.overlap sem j hj hjA hproper) BJ hBJ p).trans
    (upper_respects_iff sem j hj hjA hproper k hg hk hkA hjk BJ hBJ _)

theorem pullback_respects {BJ : Finset ι × ℕ} (hBJ : BJ.2 ≤ j)
    {q : (scheme sem j hj hjA k hk hkA).below BJ → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) BJ q) :
    RespectsSemanticsBelow (CanonicalGradeCutSections.lowerRows sem j hj hjA hproper) BJ
      (q ∘ equiv sem j hj hjA k hk hkA hjk BJ hBJ) := by
  apply (respects_iff sem j hj hjA hproper k hg hk hkA hjk BJ hBJ _).mpr
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hq

end
end VaughtConjecture.Knight.CanonicalLowerDomain
