/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSections
public import VaughtConjecture.Knight.CanonicalLowerLift

/-! # Original grade-one faces: bottom and positive caps on the actual lower target -/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalLowerAllCaps
open Transform Value ExtOrd CanonicalMixedGradeLayers CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 2 ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ 2)

theorem exists_lift {C : Finset ι}
    (hfull : C.Nonempty → ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    {p : D.below (C, 1) → ExtOrd} (hp : RespectsSemanticsBelow sem (C, 1) p)
    {q : (scheme sem 1 (by decide) (by omega) 2 (by decide) hA).below (A, 1) → ExtOrd}
    (hq : RespectsSemanticsBelow
      (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)) (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ)
    (hag : ∀ e : D.below (C, 1), min (p e) γ =
      min (q (CanonicalLowerLift.oldLow sem (by omega) 2 (by decide) hA e.1 e.2.2)) γ)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hCU : GradedLe (C, 1) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hCU) (hright : CappedLift sem hOV)
    {U₁ V₁ O₁ : Finset ι × ℕ}
    (hcover₁ : ∀ d : Cell D, D.grade d ≤ 1 →
      GradedLe (D.cell d) U₁ ∨ GradedLe (D.cell d) V₁)
    (hCU₁ : GradedLe (C, 1) U₁) (hOU₁ : GradedLe O₁ U₁) (hOV₁ : GradedLe O₁ V₁)
    (hinter₁ : ∀ d : Cell D, GradedLe (D.cell d) U₁ → GradedLe (D.cell d) V₁ →
      GradedLe (D.cell d) O₁)
    (hleft₁ : CappedLift sem hCU₁) (hright₁ : CappedLift sem hOV₁)
    (hU₁ : U₁.2 ≤ 1) (hV₁ : V₁.2 ≤ 1) :
    ∃ r : (scheme sem 1 (by decide) (by omega) 2 (by decide) hA).below (A, 1) → ExtOrd,
      RespectsSemanticsBelow
        (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)) (A, 1) r ∧
      (∀ e : D.below (C, 1),
        r (CanonicalLowerLift.oldLow sem (by omega) 2 (by decide) hA e.1 e.2.2) = p e) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  by_cases hne : C.Nonempty
  swap
  · refine ⟨q, hq, ?_, fun _ => rfl⟩
    intro e
    exact (hne (Finset.card_pos.mp ((D.grade_pos e.1).trans_le
      ((D.grade_le_card_scope e.1).trans (Finset.card_le_card e.2.1))))).elim
  by_cases hγb : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := CanonicalSections.exists_section sem 1 (by decide) (by omega)
      hproper 2 hg (by decide) hA (by decide) hcover hCU hOU hOV hinter hleft hright hp
    let h12 : GradedLe (A, 1) (A, 2) := ⟨Finset.Subset.refl _, (by decide : 1 ≤ 2)⟩
    exact ⟨fun d => r (CellScheme.below.mono h12 d), hr.mono h12,
      hread, fun _ => by simp only [hγb, min_bot_right]⟩
  · exact CanonicalLowerLift.exists_positive_lift sem (by omega) hproper 2 hg (by decide)
      hA (by decide) (hfull hne) hp hq hγ hγb hag hcover₁ hCU₁ hOU₁ hOV₁ hinter₁
      hleft₁ hright₁ hU₁ hV₁

end
end VaughtConjecture.Knight.CanonicalLowerAllCaps
