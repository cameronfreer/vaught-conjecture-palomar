/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepDonorRepair
public import VaughtConjecture.Knight.LowOnlyPaddedStepFaces

/-! # Higher active donor lifting from the lower invariant

Donor source repair and independent lower lifting restore the entire donor
prescription, including distinct lower values above the owner and literal top.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedStepDonorLift
open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse
open LowOnlyPaddedContract LowOnlyPaddedStepRows LowOnlyOrderedLadder
open LowOnlyPaddedStepDecode LowOnlyPaddedStepFaces LowOnlyPaddedStepDonorRepair
open LowOnlyPaddedFaces (fullEquiv full_respects_iff)
open AmalgamationPlan
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

theorem active_donor_lift
    (hplan : P.carrier.plan = R) (hprev : TargetGradeLifting.Through P.rows k)
    {p : I.left.scheme.below (effC n (k + 1)) → ExtOrd}
    {q : (carrier P hnext).below (A, (k + 1)) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n (k + 1)) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ) (hpos : ⊥ < γ)
    (hactive : ∃ d, I.left.scheme.grade d.1 = (k + 1) ∧ γ < p d)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨d, hd, hpd⟩ := hactive
  have hn : (k + 1) ≤ n := by simpa only [hd] using gradeC_le d.1
  obtain ⟨c₀, hc₀⟩ := I.left.complete (effC n (k + 1))
    (CappedDonor.effC_mem (by omega) (by omega))
  obtain ⟨c, hc, hmax⟩ := AmbientGradeCharts.exists_maximizer hp
    ⟨⟨c₀, by rw [hc₀]; exact GradedLe.refl _⟩,
      by simpa only [effC, min_eq_left hn] using hc₀⟩
  have hg : I.left.scheme.grade c.1 = (k + 1) := congrArg Prod.snd hc
  have hci : I.left.scheme.cell c.1 = effC n (k + 1) := by
    simpa only [effC, min_eq_left hn] using hc
  have hpc : γ < p c := hpd.trans_le (hmax d hd)
  obtain ⟨u, hu, hread, hcap, hbound⟩ :=
    owner_capped P hk hnext c hci hg hp hq hγ hpos hpc hag
  have hM : SelfVis (k + 1) (p c) := by simpa only [hg] using (hp.orderly c).symm
  let e := fullEquiv I.left I.placeLeft I.imageLeft (donorFace P hk hnext) (k + 1)
  let p' := p ∘ e.symm
  have hid (d) : CellScheme.below.mono
      (show GradedLe (B, k + 1) (A, k + 1) from ⟨hB.subset, le_rfl⟩) (e d) =
      donorAt P hnext d := by
    apply Subtype.ext
    rfl
  have hp' : RespectsSemanticsBelow (rows P hk hnext) (B, k + 1) p' := by
    apply (full_respects_iff I.left I.placeLeft I.imageLeft
      (donorFace P hk hnext) (k + 1) p').mpr
    change RespectsSemanticsBelow I.left.rows (effC n (k + 1)) ((p ∘ e.symm) ∘ e)
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hp
  have hcard : B.card = n := by
    rw [← I.imageLeft, Finset.card_image_of_injective _ I.placeLeft.injective]
    simp only [Finset.card_univ, Fintype.card_fin]
  have hCmem : (B, k) ∈ Plan.gradedPlan (carrier P hnext).plan := by
    change (B, k) ∈ Plan.gradedPlan P.carrier.plan
    rw [hplan]
    exact Plan.mem_gradedPlan.mpr
      ⟨I.leftPlan_le I.leftScheme.isPlan.domain_mem, by omega, by change k ≤ B.card; omega⟩
  have hAmem : (A, k) ∈ Plan.gradedPlan (carrier P hnext).plan :=
    Plan.mem_gradedPlan.mpr
      ⟨(carrier P hnext).isPlan.domain_mem, by omega, by change k ≤ A.card; omega⟩
  obtain ⟨r, hr, hrc, hrr⟩ := TargetGradeLifting.restore (rows P hk hnext)
    (lower_lifting P hk hnext hprev) hCmem hAmem hB.subset hp' hu hM hpc.le
    (fun d => by
      obtain ⟨x, rfl⟩ := e.surjective d
      simpa only [p', Function.comp_apply, Equiv.symm_apply_apply, hid] using hread x)
    (fun d hd => by
      obtain ⟨x, rfl⟩ := e.surjective d
      have hg' : I.left.scheme.grade x.1 = k + 1 :=
        (congrArg Prod.snd ((donorFace P hk hnext).index x.1)).symm.trans hd
      simpa only [p', Function.comp_apply, Equiv.symm_apply_apply] using hmax x hg')
    hcap
  refine ⟨r, hr, ?_, hrc⟩
  intro d
  simpa only [p', Function.comp_apply, Equiv.symm_apply_apply, hid] using hrr (e d)

end
end VaughtConjecture.Knight.LowOnlyPaddedStepDonorLift
