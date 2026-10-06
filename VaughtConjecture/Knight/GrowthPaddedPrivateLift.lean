/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedPrivateRepair
public import VaughtConjecture.Knight.GradeTailRestoration

/-! # Active positive-cap private lifting on the unchanged padded successor

Literal restoration uses the already-proved grade-one scope-raising lift.
The successor's bountifulness is neither assumed nor claimed here.
Adapted from `LowOnlyPaddedPrivateLift`; the predecessor lift and source fibre
are growth theorems, not LOW-family substitutions.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedPrivateLift
open Transform Value ExtOrd CappedDonor Growth
open GrowthPaddedSuccessor GrowthPaddedDecode GrowthPaddedCharts GrowthPaddedPrivateRepair
open GradeTailRestoration AmalgamationPlan
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

/-- Restore the entire private lower vector using the unchanged padded base.
Every lower auxiliary retains its owner cap; every upper locality target stays
unchanged. This is a proved restoration, not an input to the final endpoint. -/
theorem restore
    {p : I.right.scheme.below (Finset.univ, 2) → ExtOrd}
    {u : (carrier I X T hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 2) p)
    (hu : RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) u)
    {M : ExtOrd} (hM : SelfVis 2 M)
    (hread : ∀ d, u (privateAt I X T hA hB hC d) = min (p d) M)
    (hbound : ∀ d, u d ≤ M)
    (hmax : ∀ d, I.right.scheme.grade d.1 = 2 → p d ≤ M) :
    ∃ r, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) r ∧
      (∀ d, r (privateAt I X T hA hB hC d) = p d) ∧
      ∀ d, min (r d) M = min (u d) M := by
  let e := lowerEquiv I X T hA hB hC
  let inc := CellScheme.below.mono (D := I.right.scheme)
    (show GradedLe (Finset.univ, 1) (Finset.univ, 2) from
      ⟨Finset.Subset.refl _, by omega⟩)
  let u₁ := fun d => u (lowerIncl (by decide : 1 ≤ 2) (e d))
  have hu₁ : RespectsSemanticsBelow (input I X T hA hB hC).lowerRows (A, 1) u₁ := by
    apply (lower_respects_iff I X T hA hB hC u₁).mpr
    have h := hu.mono (show GradedLe (A, 1) (A, 2) from
      ⟨Finset.Subset.refl _, by omega⟩)
    simpa only [u₁, e, Function.comp_def, Equiv.apply_symm_apply,
      lowerIncl, CellScheme.below.mono] using h
  have hid (d : I.right.scheme.below (Finset.univ, 1)) :
      lowerIncl (by decide : 1 ≤ 2)
        (e (GrowthOrderedBase.privateAt I X (by omega) d)) =
      privateAt I X T hA hB hC (inc d) := rfl
  obtain ⟨v, hv, hvread, hvcap⟩ := GrowthOrderedBase.private_lift I X T
    (by omega) hB hC (hp.mono (show GradedLe (Finset.univ, 1) (Finset.univ, 2) from
      ⟨Finset.Subset.refl _, by omega⟩)) hu₁
    (hM.mono (by decide : 1 ≤ 2)) (fun d => by
      change min (u (lowerIncl _ (e _))) M = min (p (inc d)) M
      rw [hid, hread, min_assoc, min_self])
  let v₁ := v ∘ e.symm
  have hv₁ : RespectsSemanticsBelow (rows I X T hA hB hC) (A, 1) v₁ :=
    (lower_respects_iff I X T hA hB hC v).mp hv
  have hag (d) : min (v₁ d) M = min (u (lowerIncl (by decide : 1 ≤ 2) d)) M := by
    simpa only [u₁, v₁, Function.comp_apply, Equiv.apply_symm_apply] using hvcap (e.symm d)
  refine ⟨splice u v₁, splice_respects (by decide : 1 ≤ 2) hu hv₁
    (fun d _ => hbound d) hag, ?_, splice_cap (by decide : 1 ≤ 2) hag⟩
  intro d
  by_cases hd : I.right.scheme.grade d.1 ≤ 1
  · have hd' : (carrier I X T hA hB hC).grade
        (privateAt I X T hA hB hC d).1 ≤ 1 :=
      (private_grade I X T hA hB hC d).le.trans hd
    rw [splice_low u v₁ _ hd']
    let d₁ : I.right.scheme.below (Finset.univ, 1) :=
      ⟨d.1, Finset.subset_univ _, hd⟩
    have he : (⟨(privateAt I X T hA hB hC d).1,
        (privateAt I X T hA hB hC d).2.1, hd'⟩ :
        (carrier I X T hA hB hC).below (A, 1)) =
        e (GrowthOrderedBase.privateAt I X (by omega) d₁) := rfl
    change v (e.symm _) = p d
    rw [he, Equiv.symm_apply_apply]
    exact hvread d₁
  · rw [splice_high u v₁ _ (by simpa only [private_grade] using hd), hread]
    apply min_eq_left
    apply hmax d
    have : I.right.scheme.grade d.1 ≤ 2 := d.2.2
    omega

/-- Arbitrary lawful private prescription and target-local ambient, with an
active prescribed grade-two value. The maximal owner, chart, source-cut
prescription, admitted repair, and lower restoration are all constructed.
Every physical auxiliary has its own original-cap receipt, including unused
rungs and the long tips. Literal top is not excluded. -/
theorem active_private_lift
    {p : I.right.scheme.below (Finset.univ, 2) → ExtOrd}
    {q : (carrier I X T hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 2) p)
    (hq : RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ) (hpos : ⊥ < γ)
    (hactive : ∃ d, I.right.scheme.grade d.1 = 2 ∧ γ < p d)
    (hag : ∀ d, min (q (privateAt I X T hA hB hC d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) r ∧
      (∀ d, r (privateAt I X T hA hB hC d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨d, hd, hpd⟩ := hactive
  have hn : 2 ≤ J := by simpa only [hd] using gradeC_le d.1
  obtain ⟨c₀, hc₀⟩ := I.right.complete (Finset.univ, 2)
    (Plan.mem_gradedPlan.mpr ⟨I.right.scheme.isPlan.domain_mem, by omega,
      by simpa only [Finset.card_univ, Fintype.card_fin] using hn⟩)
  obtain ⟨c, hc, hmax⟩ := AmbientGradeCharts.exists_maximizer hp
    ⟨⟨c₀, by rw [hc₀]; exact GradedLe.refl _⟩,
      hc₀⟩
  have hg : I.right.scheme.grade c.1 = 2 := congrArg Prod.snd hc
  have hci : I.right.scheme.cell c.1 = (Finset.univ, 2) := hc
  have hpc : γ < p c := hpd.trans_le (hmax d hd)
  obtain ⟨u, hu, hread, hcap, hbound⟩ :=
    owner_capped I X T hA hB hC c hci hg hp hq hγ hpos hpc hag
  have hM : SelfVis 2 (p c) := by simpa only [hg] using (hp.orderly c).symm
  obtain ⟨r, hr, hrr, hrc⟩ := restore I X T hA hB hC hp hu hM hread hbound hmax
  exact ⟨r, hr, hrr, fun e => (cap_below (hrc e) hpc.le).trans (hcap e)⟩

end
end VaughtConjecture.Knight.GrowthPaddedPrivateLift
