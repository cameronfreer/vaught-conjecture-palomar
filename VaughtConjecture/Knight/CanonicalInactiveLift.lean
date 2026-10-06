/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalTwoGradeLift

/-! # Inactive upper prescriptions at the original positive cap

The ambient is clipped at the external cap, its lower layer is lifted at that
same cap, and the results are spliced. No prescribed grade-two owner is needed.
In particular a grade-one face may retain arbitrary distinct values and top.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalInactiveLift
open Transform Value ExtOrd CanonicalMixedGradeLayers CanonicalMixedOwnerLift
open CoatomBoundaryExtension GradeTailRestoration
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 2 ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ 2)

/-- The inactive branch includes grade-one sources, empty lower domains,
and grade-two prescriptions with no active owner. Only old grade-one face
lifts are consumed; the ambient need not extend outside its actual target. -/
theorem exists_lift {C : Finset ι} {n : ℕ} (hn : 1 ≤ n)
    (hfull₁ : IsEmpty (D.below (C, 1)) ∨ ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    {p : D.below (C, n) → ExtOrd} (hp : RespectsSemanticsBelow sem (C, n) p)
    {q : CanonicalMixedAmbient.target sem 1 (by decide) (by omega) 2 (by decide) hA → ExtOrd}
    (hq : RespectsSemanticsBelow
      (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e : D.below (C, n), min (p e) γ =
      min (q (oldTarget sem 1 (by decide) (by omega) hproper 2 hg
        (by decide) hA (by decide) e.1)) γ)
    (hinactive : ∀ e : D.below (C, n), D.grade e.1 = 2 → p e ≤ γ)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, D.grade d ≤ 1 →
      GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hCU : GradedLe (C, 1) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hCU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ 1) (hV : V.2 ≤ 1) :
    ∃ r : CanonicalMixedAmbient.target sem 1 (by decide) (by omega) 2 (by decide) hA → ExtOrd,
      RespectsSemanticsBelow
        (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)) (A, 2) r ∧
      (∀ e : D.below (C, n), r (oldTarget sem 1 (by decide) (by omega) hproper 2 hg
        (by decide) hA (by decide) e.1) = p e) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  let v := fun d => min (q d) γ
  have hv : RespectsSemanticsBelow
      (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)) (A, 2) v :=
    hq.cap hγ
  let p₁ : D.below (C, 1) → ExtOrd := fun e => p ⟨e.1, e.2.1, e.2.2.trans hn⟩
  have hp₁ : RespectsSemanticsBelow sem (C, 1) p₁ :=
    hp.mono (show GradedLe (C, 1) (C, n) from ⟨Finset.Subset.refl _, hn⟩)
  let q₁ := fun d => v (lowerIncl (by decide : 1 ≤ 2) d)
  have hq₁ : RespectsSemanticsBelow
      (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)) (A, 1) q₁ :=
    hv.mono (show GradedLe (A, 1) (A, 2) from
      ⟨Finset.Subset.refl _, (by decide : 1 ≤ 2)⟩)
  have hag₁ (e : D.below (C, 1)) : min (p₁ e) γ =
      min (q₁ (CanonicalLowerLift.oldLow sem (by omega) 2 (by decide) hA e.1 e.2.2)) γ := by
    change min (p₁ e) γ = min (min (q (oldTarget sem 1 (by decide) (by omega) hproper
      2 hg (by decide) hA (by decide) e.1)) γ) γ
    rw [min_assoc, min_self]
    exact hag ⟨e.1, e.2.1, e.2.2.trans hn⟩
  have hex : ∃ w : (scheme sem 1 (by decide) (by omega) 2 (by decide) hA).below (A, 1) → ExtOrd,
      RespectsSemanticsBelow
        (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)) (A, 1) w ∧
      (∀ e : D.below (C, 1),
        w (CanonicalLowerLift.oldLow sem (by omega) 2 (by decide) hA e.1 e.2.2) = p₁ e) ∧
      ∀ d, min (w d) γ = min (q₁ d) γ := by
    rcases hfull₁ with he | hf
    · let := he
      exact ⟨q₁, hq₁, fun e => isEmptyElim e, fun _ => rfl⟩
    · exact CanonicalLowerLift.exists_positive_lift sem (by omega) hproper 2 hg
        (by decide) hA (by decide) hf hp₁ hq₁ (hγ.mono (by decide)) hγb hag₁
        hcover hCU hOU hOV hinter hleft hright hU hV
  obtain ⟨w, hw, hwread, hwcap⟩ := hex
  refine ⟨splice v w, splice_respects (by decide : 1 ≤ 2) hv hw
    (fun _ _ => min_le_right _ _) hwcap, ?_, ?_⟩
  · intro e
    by_cases he : D.grade e.1 ≤ 1
    · rw [splice_low v w _ (by rw [oldTarget_grade]; exact he)]
      exact hwread ⟨e.1, e.2.1, he⟩
    · rw [splice_high v w _ (by rw [oldTarget_grade]; exact he)]
      have he₂ : D.grade e.1 = 2 := by have := hg e.1; omega
      exact (hag e).symm.trans (min_eq_left (hinactive e he₂))
  · intro d
    exact (splice_cap (by decide : 1 ≤ 2) hwcap d).trans
      (show min (min (q d) γ) γ = min (q d) γ by rw [min_assoc, min_self])

end
end VaughtConjecture.Knight.CanonicalInactiveLift
