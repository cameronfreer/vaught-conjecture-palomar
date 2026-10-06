/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedDonorRepair
public import VaughtConjecture.Knight.GradeTailRestoration

/-! # Active positive-cap donor lifting on the unchanged padded successor

Literal restoration uses the already-proved grade-one scope-raising lift.
The successor's bountifulness is neither assumed nor claimed here.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedDonorLift
open Transform Value ExtOrd CappedDonor LowOnly
open LowOnlyPaddedSuccessor LowOnlyPaddedDecode LowOnlyPaddedCharts LowOnlyPaddedDonorRepair
open GradeTailRestoration
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

/-- Restore the entire donor lower vector using the unchanged padded base.
Every lower auxiliary retains its owner cap; every upper locality target stays
unchanged. This is a proved restoration, not an input to the final endpoint. -/
theorem restore
    {p : I.left.scheme.below (effC n 2) → ExtOrd}
    {u : (carrier I F hroot hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n 2) p)
    (hu : RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) u)
    {M : ExtOrd} (hM : SelfVis 2 M)
    (hread : ∀ d, u (donorAt I F hroot hA hB hC d) = min (p d) M)
    (hbound : ∀ d, u d ≤ M)
    (hmax : ∀ d, I.left.scheme.grade d.1 = 2 → p d ≤ M) :
    ∃ r, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) r ∧
      (∀ d, r (donorAt I F hroot hA hB hC d) = p d) ∧
      ∀ d, min (r d) M = min (u d) M := by
  let e := lowerEquiv I F hroot hA hB hC
  let inc := CellScheme.below.mono (D := I.left.scheme)
    (CappedDonor.Ref.effC_mono (by decide : 1 ≤ 2))
  let u₁ := fun d => u (lowerIncl (by decide : 1 ≤ 2) (e d))
  have hu₁ : RespectsSemanticsBelow (input I F hroot hA hB hC).lowerRows (A, 1) u₁ := by
    apply (lower_respects_iff I F hroot hA hB hC u₁).mpr
    have h := hu.mono (show GradedLe (A, 1) (A, 2) from
      ⟨Finset.Subset.refl _, by omega⟩)
    simpa only [u₁, e, Function.comp_def, Equiv.apply_symm_apply,
      lowerIncl, CellScheme.below.mono] using h
  have hid (d : I.left.scheme.below (effC n 1)) :
      lowerIncl (by decide : 1 ≤ 2)
        (e (Family.donorAt F I.boundary (by omega) (LowOnlyOrderedLadder.donorIncl I) d)) =
      donorAt I F hroot hA hB hC (inc d) := rfl
  obtain ⟨v, hv, hvread, hvcap⟩ := LowOnlyOrderedLadder.donor_lift I F hroot
    (by omega) hB hC (hp.mono (CappedDonor.Ref.effC_mono (by decide : 1 ≤ 2))) hu₁
    (hM.mono (by decide : 1 ≤ 2)) (fun d => by
      change min (u (lowerIncl _ (e _))) M = min (p (inc d)) M
      rw [hid, hread, min_assoc, min_self])
  let v₁ := v ∘ e.symm
  have hv₁ : RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 1) v₁ :=
    (lower_respects_iff I F hroot hA hB hC v).mp hv
  have hag (d) : min (v₁ d) M = min (u (lowerIncl (by decide : 1 ≤ 2) d)) M := by
    simpa only [u₁, v₁, Function.comp_apply, Equiv.apply_symm_apply] using hvcap (e.symm d)
  refine ⟨splice u v₁, splice_respects (by decide : 1 ≤ 2) hu hv₁
    (fun d _ => hbound d) hag, ?_, splice_cap (by decide : 1 ≤ 2) hag⟩
  intro d
  by_cases hd : I.left.scheme.grade d.1 ≤ 1
  · have hd' : (carrier I F hroot hA hB hC).grade
        (donorAt I F hroot hA hB hC d).1 ≤ 1 :=
      (donor_grade I F hroot hA hB hC d).le.trans hd
    rw [splice_low u v₁ _ hd']
    let d₁ : I.left.scheme.below (effC n 1) :=
      ⟨d.1, Finset.subset_univ _, le_min hd (gradeC_le d.1)⟩
    have he : (⟨(donorAt I F hroot hA hB hC d).1,
        (donorAt I F hroot hA hB hC d).2.1, hd'⟩ :
        (carrier I F hroot hA hB hC).below (A, 1)) =
        e (Family.donorAt F I.boundary (by omega) (LowOnlyOrderedLadder.donorIncl I) d₁) := rfl
    change v (e.symm _) = p d
    rw [he, Equiv.symm_apply_apply]
    exact hvread d₁
  · rw [splice_high u v₁ _ (by simpa only [donor_grade] using hd), hread]
    apply min_eq_left
    apply hmax d
    have : I.left.scheme.grade d.1 ≤ 2 := d.2.2.trans (min_le_left 2 n)
    omega

/-- Arbitrary lawful donor prescription and target-local ambient, with an
active prescribed grade-two value. The maximal owner, chart, source-cut
prescription, admitted repair, and lower restoration are all constructed.
Every physical auxiliary has its own original-cap receipt, including unused
rungs and the long tips. Literal top is not excluded. -/
theorem active_donor_lift
    {p : I.left.scheme.below (effC n 2) → ExtOrd}
    {q : (carrier I F hroot hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n 2) p)
    (hq : RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ) (hpos : ⊥ < γ)
    (hactive : ∃ d, I.left.scheme.grade d.1 = 2 ∧ γ < p d)
    (hag : ∀ d, min (q (donorAt I F hroot hA hB hC d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) r ∧
      (∀ d, r (donorAt I F hroot hA hB hC d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨d, hd, hpd⟩ := hactive
  have hn : 2 ≤ n := by simpa only [hd] using gradeC_le d.1
  obtain ⟨c₀, hc₀⟩ := I.left.complete (effC n 2)
    (CappedDonor.effC_mem (by decide) (by omega))
  obtain ⟨c, hc, hmax⟩ := AmbientGradeCharts.exists_maximizer hp
    ⟨⟨c₀, by rw [hc₀]; exact GradedLe.refl _⟩,
      by simpa only [effC, min_eq_left hn] using hc₀⟩
  have hg : I.left.scheme.grade c.1 = 2 := congrArg Prod.snd hc
  have hci : I.left.scheme.cell c.1 = effC n 2 := by
    simpa only [effC, min_eq_left hn] using hc
  have hpc : γ < p c := hpd.trans_le (hmax d hd)
  obtain ⟨u, hu, hread, hcap, hbound⟩ :=
    owner_capped I F hroot hA hB hC c hci hg hp hq hγ hpos hpc hag
  have hM : SelfVis 2 (p c) := by simpa only [hg] using (hp.orderly c).symm
  obtain ⟨r, hr, hrr, hrc⟩ := restore I F hroot hA hB hC hp hu hM hread hbound hmax
  exact ⟨r, hr, hrr, fun e => (cap_below (hrc e) hpc.le).trans (hcap e)⟩

end
end VaughtConjecture.Knight.LowOnlyPaddedDonorLift
