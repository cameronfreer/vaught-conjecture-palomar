/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalLowerLift
public import VaughtConjecture.Knight.CanonicalMixedOwnerLift
public import VaughtConjecture.Knight.GradeTailRestoration

/-! # Literal restoration without lower-value domination

Choose a maximal prescribed grade-two owner, construct the owner-capped lift,
clip its upper tail, lift the actual grade-one prescription at the owner cap,
then splice. Every lower value is restored, including distinct invisible
values and top. Only old-face lifting is supplied, never output bountifulness.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalTwoGradeLift
open Transform Value ExtOrd CanonicalMixedGradeLayers CanonicalMixedOwnerLift
open CoatomBoundaryExtension GradeTailRestoration
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 2 ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ 2)

/-- The active grade-two branch with arbitrary literal lower prescription.
Both pairs of lifting inputs concern the two OLD boundary faces. Their grade
one clauses are used at the newly chosen owner cap, not the external cap.
The low owner incidence is explicit and follows from old-face completeness.
No domination, lower output lift, alignment, or completed ambient is assumed. -/
theorem exists_lift {C : Finset ι}
    (hfull₂ : ∃ c : D.below (C, 2), D.cell c.1 = (C, 2))
    (hfull₁ : ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    {p : D.below (C, 2) → ExtOrd} (hp : RespectsSemanticsBelow sem (C, 2) p)
    {q : CanonicalMixedAmbient.target sem 1 (by decide) (by omega) 2 (by decide) hA → ExtOrd}
    (hq : RespectsSemanticsBelow
      (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e : D.below (C, 2), min (p e) γ =
      min (q (oldTarget sem 1 (by decide) (by omega) hproper 2 hg
        (by decide) hA (by decide) e.1)) γ)
    (hactive : ∃ d : D.below (C, 2), D.grade d.1 = 2 ∧ γ < p d)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hCU : GradedLe (C, 2) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hCU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ 2) (hV : V.2 ≤ 2)
    {U₁ V₁ O₁ : Finset ι × ℕ}
    (hcover₁ : ∀ d : Cell D, D.grade d ≤ 1 →
      GradedLe (D.cell d) U₁ ∨ GradedLe (D.cell d) V₁)
    (hCU₁ : GradedLe (C, 1) U₁) (hOU₁ : GradedLe O₁ U₁) (hOV₁ : GradedLe O₁ V₁)
    (hinter₁ : ∀ d : Cell D, GradedLe (D.cell d) U₁ → GradedLe (D.cell d) V₁ →
      GradedLe (D.cell d) O₁)
    (hleft₁ : CappedLift sem hCU₁) (hright₁ : CappedLift sem hOV₁)
    (hU₁ : U₁.2 ≤ 1) (hV₁ : V₁.2 ≤ 1) :
    ∃ r : CanonicalMixedAmbient.target sem 1 (by decide) (by omega) 2 (by decide) hA → ExtOrd,
      RespectsSemanticsBelow
        (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)) (A, 2) r ∧
      (∀ e : D.below (C, 2), r (oldTarget sem 1 (by decide) (by omega) hproper 2 hg
        (by decide) hA (by decide) e.1) = p e) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨c, hci, hmax⟩ := AmbientGradeCharts.exists_maximizer hp hfull₂
  let M := p c
  have hpc : γ < M := by
    obtain ⟨d, hd, hpd⟩ := hactive
    exact hpd.trans_le (hmax d hd)
  have hc : D.grade c.1 = 2 := congrArg Prod.snd hci
  have hM : SelfVis 2 M := by simpa only [hc] using (hp.orderly c).symm
  have hMb : M ≠ ⊥ := (bot_le.trans_lt hpc).ne.symm
  have hcle : GradedLe (D.cell c.1) (C, 2) := by rw [hci]; exact GradedLe.refl _
  let pc : D.below (D.cell c.1) → ExtOrd := fun e => p ⟨e.1, e.2.trans hcle⟩
  have hpcLaw : RespectsSemanticsBelow sem (D.cell c.1) pc := hp.mono hcle
  have hcU : GradedLe (D.cell c.1) U := hcle.trans hCU
  have hleftc : CappedLift sem hcU := by simpa only [hci] using hleft
  obtain ⟨u, hu, hread, hcap⟩ := exists_owner_capped_lift sem 1 (by decide) (by omega)
    hproper 2 hg (by decide) hA (by decide) c.1 hc hpcLaw hq hγ hγb
    (fun e => hag ⟨e.1, e.2.trans hcle⟩) hpc hcover hcU hOU hOV hinter hleftc hright hU hV
  have huold (e : D.below (C, 2)) :
      u (oldTarget sem 1 (by decide) (by omega) hproper 2 hg
        (by decide) hA (by decide) e.1) = min (p e) M := by
    have he : GradedLe (D.cell e.1) (D.cell c.1) := by rw [hci]; exact e.2
    exact hread ⟨e.1, he⟩
  let v := fun d => min (u d) M
  have hv : RespectsSemanticsBelow
      (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)) (A, 2) v :=
    hu.cap hM
  let p₁ : D.below (C, 1) → ExtOrd := fun e =>
    p ⟨e.1, e.2.1, e.2.2.trans (by decide : 1 ≤ 2)⟩
  have hp₁ : RespectsSemanticsBelow sem (C, 1) p₁ :=
    hp.mono (show GradedLe (C, 1) (C, 2) from
      ⟨Finset.Subset.refl _, (by decide : 1 ≤ 2)⟩)
  let q₁ := fun d => v (lowerIncl (by decide : 1 ≤ 2) d)
  have hq₁ : RespectsSemanticsBelow
      (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)) (A, 1) q₁ :=
    hv.mono (show GradedLe (A, 1) (A, 2) from
      ⟨Finset.Subset.refl _, (by decide : 1 ≤ 2)⟩)
  have hag₁ (e : D.below (C, 1)) : min (p₁ e) M =
      min (q₁ (CanonicalLowerLift.oldLow sem (by omega) 2 (by decide) hA e.1 e.2.2)) M := by
    change min (p₁ e) M = min (min (u (oldTarget sem 1 (by decide) (by omega) hproper
      2 hg (by decide) hA (by decide) e.1)) M) M
    rw [huold ⟨e.1, e.2.1, e.2.2.trans (by decide : 1 ≤ 2)⟩,
      min_assoc, min_self, min_assoc, min_self]
  obtain ⟨w, hw, hwold, hwcap⟩ := CanonicalLowerLift.exists_positive_lift sem (by omega)
    hproper 2 hg (by decide) hA (by decide) hfull₁ hp₁ hq₁ (hM.mono (by decide)) hMb hag₁
    hcover₁ hCU₁ hOU₁ hOV₁ hinter₁ hleft₁ hright₁ hU₁ hV₁
  have hrest := splice_respects (by decide : 1 ≤ 2) hv hw
    (fun d _ => min_le_right _ _) hwcap
  refine ⟨splice v w, hrest, ?_, ?_⟩
  · intro e
    by_cases he : D.grade e.1 ≤ 1
    · rw [splice_low v w _ (by rw [oldTarget_grade]; exact he)]
      exact hwold ⟨e.1, e.2.1, he⟩
    · rw [splice_high v w _ (by rw [oldTarget_grade]; exact he)]
      change min (u (oldTarget sem 1 (by decide) (by omega) hproper 2 hg
        (by decide) hA (by decide) e.1)) M = p e
      have he₂ : D.grade e.1 = 2 := by have := hg e.1; omega
      rw [huold, min_assoc, min_self, min_eq_left (hmax e he₂)]
  · intro d
    have he := cap_below (splice_cap (by decide : 1 ≤ 2) (u := v) (v := w) hwcap d) hpc.le
    exact he.trans (by
      change min (min (u d) M) γ = min (q d) γ
      rw [min_assoc, min_eq_right hpc.le]
      exact hcap d)

end
end VaughtConjecture.Knight.CanonicalTwoGradeLift
