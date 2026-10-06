/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedStepDonorRepair
public import VaughtConjecture.Knight.GrowthPaddedOriginalLifts
public import VaughtConjecture.Knight.GradeTailRestoration

/-! # Active positive-cap donor lifting on the unchanged padded successor

Literal restoration uses the previously proved original-face lift.
The concrete grade-three endpoint discharges the lower input using the
checked all-cap grade-two theorem. No output bountifulness is assumed.
Adapted from `LowOnlyPaddedPrivateLift`; the predecessor lift and source fibre
are growth theorems, not LOW-family substitutions.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedStepDonorLift
open Transform Value ExtOrd CappedDonor Growth
open GrowthPaddedContract GrowthPaddedStepRows GrowthPaddedStepDecode
open GrowthPaddedStepDonorRepair
open GradeTailRestoration AmalgamationPlan
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)


/-- The previous donor face, on the actual predecessor. -/
def previousDonorAt (d : I.left.scheme.below (Finset.univ, k)) :
    P.carrier.below (A, k) :=
  ⟨P.baseMap (RelativeLadderLayer.old I.boundary (by omega) (I.leftFace.map d.1)), by
    rw [P.base_index, RelativeLadderLayer.old_index]
    exact ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2⟩⟩

/-- Only the predecessor's original-donor lift is needed for restoration. -/
def DonorLowerLift : Prop :=
  ∀ (p : I.left.scheme.below (Finset.univ, k) → ExtOrd)
    (q : P.carrier.below (A, k) → ExtOrd) (γ : ExtOrd),
    RespectsSemanticsBelow I.left.rows (Finset.univ, k) p →
    RespectsSemanticsBelow P.rows (A, k) q → SelfVis k γ →
    (∀ d, min (q (previousDonorAt P d)) γ = min (p d) γ) →
    ∃ r, RespectsSemanticsBelow P.rows (A, k) r ∧
      (∀ d, r (previousDonorAt P d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ

def lowerEquiv : P.carrier.below (A, k) ≃ (carrier P hnext).below (A, k) :=
  HighLayerBountiful.equiv P.carrier (Catalogue X (k + 1))
    (k + 1) (Nat.succ_pos k) hnext (A, k) (fun h => by have := h.2; omega)

theorem lower_respects_iff (p : P.carrier.below (A, k) → ExtOrd) :
    RespectsSemanticsBelow P.rows (A, k) p ↔
      RespectsSemanticsBelow (rows P hk hnext) (A, k)
        (p ∘ (lowerEquiv P hnext).symm) := by
  apply respects_iff_of_equiv (lowerEquiv P hnext)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell _ _ _ _ _ _ _ d)).symm)
    (fun d e => ?_) (fun b d _ => ?_) p
  · simp only [CellScheme.scope, lowerEquiv, HighLayerBountiful.equiv_cell]
  · exact (inherited_row P hk hnext b.1 d).symm

/-- Restore the entire donor lower vector using the actual predecessor.
Every lower auxiliary retains its owner cap; every upper locality target stays
unchanged. This is a proved restoration, not an input to the final endpoint. -/
theorem restore (hprev : DonorLowerLift P)
    {p : I.left.scheme.below (Finset.univ, k + 1) → ExtOrd}
    {u : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p)
    (hu : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) u)
    {M : ExtOrd} (hM : SelfVis (k + 1) M)
    (hread : ∀ d, u (donorAt P hnext d) = min (p d) M)
    (hbound : ∀ d, u d ≤ M)
    (hmax : ∀ d, I.left.scheme.grade d.1 = k + 1 → p d ≤ M) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      ∀ d, min (r d) M = min (u d) M := by
  let e := lowerEquiv P hnext
  let inc := CellScheme.below.mono (D := I.left.scheme)
    (show GradedLe (Finset.univ, k) (Finset.univ, k + 1) from
      ⟨Finset.Subset.refl _, by omega⟩)
  let u₁ := fun d => u (lowerIncl (by omega : k ≤ k + 1) (e d))
  have hu₁ : RespectsSemanticsBelow P.rows (A, k) u₁ := by
    apply (lower_respects_iff P hk hnext u₁).mpr
    have h := hu.mono (show GradedLe (A, k) (A, k + 1) from
      ⟨Finset.Subset.refl _, by omega⟩)
    simpa only [u₁, e, Function.comp_def, Equiv.apply_symm_apply,
      lowerIncl, CellScheme.below.mono] using h
  have hid (d : I.left.scheme.below (Finset.univ, k)) :
      lowerIncl (by omega : k ≤ k + 1)
        (e (previousDonorAt P d)) =
      donorAt P hnext (inc d) := rfl
  obtain ⟨v, hv, hvread, hvcap⟩ := hprev _ _ M
    (hp.mono (show GradedLe (Finset.univ, k) (Finset.univ, k + 1) from
      ⟨Finset.Subset.refl _, by omega⟩)) hu₁
    (hM.mono (by omega : k ≤ k + 1)) (fun d => by
      change min (u (lowerIncl _ (e _))) M = min (p (inc d)) M
      rw [hid, hread, min_assoc, min_self])
  let v₁ := v ∘ e.symm
  have hv₁ : RespectsSemanticsBelow (rows P hk hnext) (A, k) v₁ :=
    (lower_respects_iff P hk hnext v).mp hv
  have hag (d) : min (v₁ d) M = min (u (lowerIncl (by omega : k ≤ k + 1) d)) M := by
    simpa only [u₁, v₁, Function.comp_apply, Equiv.apply_symm_apply] using hvcap (e.symm d)
  refine ⟨splice u v₁, splice_respects (by omega : k ≤ k + 1) hu hv₁
    (fun d _ => hbound d) hag, ?_, splice_cap (by omega : k ≤ k + 1) hag⟩
  intro d
  by_cases hd : I.left.scheme.grade d.1 ≤ k
  · have hd' : (carrier P hnext).grade
        (donorAt P hnext d).1 ≤ k :=
      (donor_grade P hnext d).le.trans hd
    rw [splice_low u v₁ _ hd']
    let d₁ : I.left.scheme.below (Finset.univ, k) :=
      ⟨d.1, Finset.subset_univ _, hd⟩
    have he : (⟨(donorAt P hnext d).1,
        (donorAt P hnext d).2.1, hd'⟩ :
        (carrier P hnext).below (A, k)) =
        e (previousDonorAt P d₁) := rfl
    change v (e.symm _) = p d
    rw [he, Equiv.symm_apply_apply]
    exact hvread d₁
  · rw [splice_high u v₁ _ (by simpa only [donor_grade] using hd), hread]
    apply min_eq_left
    apply hmax d
    have : I.left.scheme.grade d.1 ≤ k + 1 := d.2.2
    omega

/-- Arbitrary lawful donor prescription and target-local ambient, with an
active prescribed current-grade value. The maximal owner, chart, source-cut
prescription, admitted repair, and lower restoration are all constructed.
Every physical auxiliary has its own original-cap receipt, including unused
rungs and the long tips. Literal top is not excluded. -/
theorem active_donor_lift (hN : k + 1 < X.req.N) (hprev : DonorLowerLift P)
    {p : I.left.scheme.below (Finset.univ, k + 1) → ExtOrd}
    {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ) (hpos : ⊥ < γ)
    (hactive : ∃ d, I.left.scheme.grade d.1 = k + 1 ∧ γ < p d)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨d, hd, hpd⟩ := hactive
  have hn : k + 1 ≤ n + 1 := by simpa only [hd] using gradeC_le d.1
  obtain ⟨c₀, hc₀⟩ := I.left.complete (Finset.univ, k + 1)
    (Plan.mem_gradedPlan.mpr ⟨I.left.scheme.isPlan.domain_mem, by omega,
      by simpa only [Finset.card_univ, Fintype.card_fin] using hn⟩)
  obtain ⟨c, hc, hmax⟩ := AmbientGradeCharts.exists_maximizer hp
    ⟨⟨c₀, by rw [hc₀]; exact GradedLe.refl _⟩,
      hc₀⟩
  have hg : I.left.scheme.grade c.1 = k + 1 := congrArg Prod.snd hc
  have hci : I.left.scheme.cell c.1 = (Finset.univ, k + 1) := hc
  have hpc : γ < p c := hpd.trans_le (hmax d hd)
  obtain ⟨u, hu, hread, hcap, hbound⟩ :=
    owner_capped P hk hnext hN c hci hg hp hq hγ hpos hpc hag
  have hM : SelfVis (k + 1) (p c) := by simpa only [hg] using (hp.orderly c).symm
  obtain ⟨r, hr, hrr, hrc⟩ := restore P hk hnext hprev hp hu hM hread hbound hmax
  exact ⟨r, hr, hrr, fun e => (cap_below (hrc e) hpc.le).trans (hcap e)⟩

variable (I X T hA hB hC)

/-- The actual grade-two lift initializes higher literal restoration. -/
theorem initial_donor (hN : 2 < X.req.N) : DonorLowerLift (initial I X T hA hB hC) := by
  intro p q γ hp hq hγ hag
  exact GrowthPaddedOriginalLifts.donor_lift I X T hA hB hC hN hp hq hγ hag

/-- First higher active lift, on integration's actual grade-three output.
There is no supplied predecessor lift, source-cut prescription, alignment,
admitted replacement, decoder, or decoded-lawfulness premise. -/
theorem grade_three (hN : 3 < X.req.N) (ht : 3 ≤ A.card)
    {p : I.left.scheme.below (Finset.univ, 3) → ExtOrd}
    {q : (GrowthPaddedIteration.gradeThree I X T hA hB hC ht).carrier.below (A, 3) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 3) p)
    (hq : RespectsSemanticsBelow
      (GrowthPaddedIteration.gradeThree I X T hA hB hC ht).rows (A, 3) q)
    {γ : ExtOrd} (hγ : SelfVis 3 γ) (hpos : ⊥ < γ)
    (hactive : ∃ d, I.left.scheme.grade d.1 = 3 ∧ γ < p d)
    (hag : ∀ d, min (q (donorAt (initial I X T hA hB hC) ht d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow
        (GrowthPaddedIteration.gradeThree I X T hA hB hC ht).rows (A, 3) r ∧
      (∀ d, r (donorAt (initial I X T hA hB hC) ht d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ :=
  active_donor_lift (initial I X T hA hB hC) (by decide) ht hN
    (initial_donor I X T hA hB hC (by omega)) hp hq hγ hpos hactive hag

end
end VaughtConjecture.Knight.GrowthPaddedStepDonorLift
