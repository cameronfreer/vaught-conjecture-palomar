/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSeedOwnerLift
public import VaughtConjecture.Knight.CanonicalSeedRestoration

/-! # Literal active-owner lifting on the recursive seed

The prescription and ambient are arbitrary lawful physical sections. A maximal
prescribed owner is constructed by availability. Old-face lifting constructs
the coded boundary repair; predecessor bountifulness restores the complete
lower prescription, including distinct values above the owner and literal top.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalSeedActiveLift
open Transform Value ExtOrd CoatomBoundaryExtension
open CanonicalRecursiveSeedRows CanonicalSeedCutPrefix
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)

abbrev outputRows := rows sem hA hp

def faceEquiv (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) (hj : J.2 ≤ 3) :
    (cut (D := D)).below J ≃ (carrier sem hA).below J :=
  (GradeCutBoundary.belowEquiv D 3 J hj).trans
    (CanonicalRecursiveBoundaryTransport.properEquiv sem 0 hA J hJ)

theorem faceEquiv_val (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) (hj : J.2 ≤ 3)
    (d : (cut (D := D)).below J) :
    (faceEquiv sem hA J hJ hj d).1 = (oldTarget sem hA d.1).1 :=
  CanonicalRecursiveBoundaryTransport.properEquiv_val sem 0 hA J hJ _

theorem faceEquiv_cell (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) (hj : J.2 ≤ 3)
    (d : (cut (D := D)).below J) :
    (carrier sem hA).cell (faceEquiv sem hA J hJ hj d).1 =
      (cut (D := D)).cell d.1 := by
  rw [faceEquiv_val, oldTarget_cell]

theorem pullback_respects (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) (hj : J.2 ≤ 3)
    {p : (carrier sem hA).below J → ExtOrd}
    (hpr : RespectsSemanticsBelow (outputRows sem hA hp) J p) :
    RespectsSemanticsBelow (cutRows sem) J (p ∘ faceEquiv sem hA J hJ hj) :=
  GradeCutBoundary.pullback_respects D 3 sem hj
    (CanonicalRecursiveBoundaryTransport.pullback_respects sem hp 0 hA J hJ hpr)

/-- Active seed branch. Every auxiliary cap is retained. The only lifting
inputs concern the actual predecessor and the two old boundary faces. -/
theorem exists_lift
    (hb : CanonicalSeedRestoration.LowerBountiful sem hA hp)
    {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A) (hCc : 3 ≤ C.card)
    (hfull : ∃ c : (cut (D := D)).below (C, 3),
      (cut (D := D)).cell c.1 = (C, 3))
    {p : (carrier sem hA).below (C, 3) → ExtOrd}
    (hpr : RespectsSemanticsBelow (outputRows sem hA hp) (C, 3) p)
    {q : CanonicalSeedAmbient.target sem hA → ExtOrd}
    (hqr : RespectsSemanticsBelow (outputRows sem hA hp) (A, 3) q)
    {γ : ExtOrd} (hγ : SelfVis 3 γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e, min (p e) γ = min (q (CellScheme.below.mono
      (show GradedLe (C, 3) (A, 3) from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e)) γ)
    (hactive : ∃ d : (carrier sem hA).below (C, 3),
      (carrier sem hA).grade d.1 = 3 ∧ γ < p d)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell (cut (D := D)),
      GradedLe ((cut (D := D)).cell d) U ∨ GradedLe ((cut (D := D)).cell d) V)
    (hCU : GradedLe (C, 3) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell (cut (D := D)), GradedLe ((cut (D := D)).cell d) U →
      GradedLe ((cut (D := D)).cell d) V → GradedLe ((cut (D := D)).cell d) O)
    (hleft : CappedLift (cutRows sem) hCU) (hright : CappedLift (cutRows sem) hOV)
    (hU : U.2 ≤ 3) (hV : V.2 ≤ 3) :
    ∃ r : CanonicalSeedAmbient.target sem hA → ExtOrd,
      RespectsSemanticsBelow (outputRows sem hA hp) (A, 3) r ∧
      (∀ e, r (CellScheme.below.mono
        (show GradedLe (C, 3) (A, 3) from
          ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) = p e) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  have hCnot : ¬ A ⊆ C := fun h =>
    hCA (Finset.Subset.antisymm (D.isPlan.subset_of_mem hC) h)
  let E := faceEquiv sem hA (C, 3) hCnot le_rfl
  let p₀ := p ∘ E
  have hp₀ := pullback_respects sem hA hp (C, 3) hCnot le_rfl hpr
  obtain ⟨c, hci, hmax⟩ := AmbientGradeCharts.exists_maximizer hp₀ hfull
  let M := p₀ c
  have hpc : γ < M := by
    obtain ⟨d, hd, hpd⟩ := hactive
    obtain ⟨e, rfl⟩ := E.surjective d
    have he : (cut (D := D)).grade e.1 = 3 := by
      change ((carrier sem hA).cell (E e).1).2 = 3 at hd
      rw [faceEquiv_cell] at hd
      exact hd
    exact hpd.trans_le (hmax e he)
  have hc : (cut (D := D)).grade c.1 = 3 := congrArg Prod.snd hci
  have hM : SelfVis 3 M := by simpa only [hc] using (hp₀.orderly c).symm
  have hcle : GradedLe ((cut (D := D)).cell c.1) (C, 3) := c.2
  let pc := fun e : (cut (D := D)).below ((cut (D := D)).cell c.1) =>
    p₀ ⟨e.1, e.2.trans hcle⟩
  have hpcLaw : RespectsSemanticsBelow (cutRows sem)
      ((cut (D := D)).cell c.1) pc := hp₀.mono hcle
  have hag₀ (e : (cut (D := D)).below (C, 3)) :
      min (p₀ e) γ = min (q (oldTarget sem hA e.1)) γ := by
    have he : CellScheme.below.mono
        (show GradedLe (C, 3) (A, 3) from
          ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) (E e) = oldTarget sem hA e.1 :=
      Subtype.ext (faceEquiv_val sem hA _ hCnot le_rfl e)
    simpa only [p₀, Function.comp_apply, he] using hag (E e)
  have hl : CappedLift (cutRows sem) (hcle.trans hCU) := by
    simpa only [hci] using hleft
  obtain ⟨u, hu, hread, hcap⟩ := CanonicalSeedOwnerLift.exists_owner_capped_lift
    sem hA hp  c.1 hc hpcLaw hqr hγ hγb
    (fun e => hag₀ ⟨e.1, e.2.trans hcle⟩) hpc
    hcover (hcle.trans hCU) hOU hOV hinter hl hright hU hV
  have huold (e : (cut (D := D)).below (C, 3)) :
      u (oldTarget sem hA e.1) = min (p₀ e) M := by
    have he : GradedLe ((cut (D := D)).cell e.1) ((cut (D := D)).cell c.1) := by
      rw [hci]; exact e.2
    exact hread ⟨e.1, he⟩
  have hreadPhys (e : (carrier sem hA).below (C, 3)) :
      u (CellScheme.below.mono
        (show GradedLe (C, 3) (A, 3) from
          ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) = min (p e) M := by
    obtain ⟨d, rfl⟩ := E.surjective e
    have hd : CellScheme.below.mono
        (show GradedLe (C, 3) (A, 3) from
          ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) (E d) = oldTarget sem hA d.1 :=
      Subtype.ext (faceEquiv_val sem hA _ hCnot le_rfl d)
    rw [hd]
    exact huold d
  have hmaxPhys (e : (carrier sem hA).below (C, 3))
      (he : (carrier sem hA).grade e.1 = 3) : p e ≤ M := by
    obtain ⟨d, rfl⟩ := E.surjective e
    apply hmax d
    change ((carrier sem hA).cell (E d).1).2 = 3 at he
    rw [faceEquiv_cell] at he
    exact he
  obtain ⟨r, hr, hrlit, hrcap, _⟩ := CanonicalSeedRestoration.restore
    sem hA hp  hb hC (Nat.le_of_succ_le hCc)
    hpr hu hM hpc.le hreadPhys hmaxPhys hcap
  exact ⟨r, hr, hrlit, hrcap⟩

end
end VaughtConjecture.Knight.CanonicalSeedActiveLift
