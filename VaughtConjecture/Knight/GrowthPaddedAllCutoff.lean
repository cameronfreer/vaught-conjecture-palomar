/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedCutTransport
public import VaughtConjecture.Knight.GrowthPaddedLayerFaces
public import VaughtConjecture.Knight.CappedLiftComposition

/-! # Original-face lifting at all cutoffs on one fixed growth carrier

The native-height lifts transport through literal later installations. Proper
subface prescriptions are first extended inside their original legal scheme.
No mixed-prescription lifting or whole-carrier bountifulness is asserted.
-/
@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedAllCutoff
open Transform Value ExtOrd Growth
open GrowthPaddedContract GrowthPaddedIteration GrowthPaddedLayerFaces
open AmalgamationPlan CoatomBoundaryExtension
noncomputable section
section Layer
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k)


theorem native_private (hl : GrowthPaddedStepPrivateLift.PrivateLowerLift P) :
    CappedLift P.rows (show GradedLe (C, k) (A, k) from ⟨hC.subset, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  let e := fullEquiv I.right I.placeRight I.imageRight (privateFace P) k
  have hid (d) : CellScheme.below.mono
      (show GradedLe (C, k) (A, k) from ⟨hC.subset, le_rfl⟩) (e d) =
      GrowthPaddedStepPrivateLift.previousPrivateAt P d := rfl
  obtain ⟨r, hr, hread, hcap⟩ := hl (p ∘ e) q γ
    ((full_respects_iff I.right I.placeRight I.imageRight (privateFace P) k p).mp hp)
    hq hγ (fun d => hag (e d))
  refine ⟨r, hr, hcap, ?_⟩
  intro d
  obtain ⟨x, rfl⟩ := e.surjective d
  rw [hid]
  exact hread x

theorem native_donor (hl : GrowthPaddedStepDonorLift.DonorLowerLift P) :
    CappedLift P.rows (show GradedLe (B, k) (A, k) from ⟨hB.subset, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  let e := fullEquiv I.left I.placeLeft I.imageLeft (donorFace P) k
  have hid (d) : CellScheme.below.mono
      (show GradedLe (B, k) (A, k) from ⟨hB.subset, le_rfl⟩) (e d) =
      GrowthPaddedStepDonorLift.previousDonorAt P d := rfl
  obtain ⟨r, hr, hread, hcap⟩ := hl (p ∘ e) q γ
    ((full_respects_iff I.left I.placeLeft I.imageLeft (donorFace P) k p).mp hp)
    hq hγ (fun d => hag (e d))
  refine ⟨r, hr, hcap, ?_⟩
  intro d
  obtain ⟨x, rfl⟩ := e.surjective d
  rw [hid]
  exact hread x

/-- Every installed layer has exactly the checked padded grade-one lift. -/
theorem private_one :
    CappedLift P.rows (show GradedLe (C, 1) (A, 1) from ⟨hC.subset, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  let e := fullEquiv I.right I.placeRight I.imageRight (privateFace P) 1
  let b := GrowthPaddedCutTransport.baseEquiv P
  have hq' : RespectsSemanticsBelow (baseRows I X T hA hB hC) (A, 1) (q ∘ b) := by
    apply (GrowthPaddedCutTransport.base_respects_iff P _).mpr
    simpa only [b, Function.comp_def, Equiv.apply_symm_apply] using hq
  obtain ⟨r, hr, hread, hcap⟩ := GrowthOrderedBase.private_lift I X T
    (by omega) hB hC
    ((full_respects_iff I.right I.placeRight I.imageRight (privateFace P) 1 p).mp hp)
    hq' hγ (fun d => hag (e d))
  refine ⟨r ∘ b.symm, (GrowthPaddedCutTransport.base_respects_iff P r).mp hr, ?_, ?_⟩
  · intro d
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (b.symm d)
  · intro d
    obtain ⟨x, rfl⟩ := e.surjective d
    have hid : CellScheme.below.mono
        (show GradedLe (C, 1) (A, 1) from ⟨hC.subset, le_rfl⟩) (e x) =
        b (GrowthOrderedBase.privateAt I X (by omega) x) := rfl
    rw [Function.comp_apply, hid, Equiv.symm_apply_apply]
    exact hread x

theorem donor_one (hsmall : n + 1 < X.req.N) :
    CappedLift P.rows (show GradedLe (B, 1) (A, 1) from ⟨hB.subset, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  let e := fullEquiv I.left I.placeLeft I.imageLeft (donorFace P) 1
  let b := GrowthPaddedCutTransport.baseEquiv P
  have hq' : RespectsSemanticsBelow (baseRows I X T hA hB hC) (A, 1) (q ∘ b) := by
    apply (GrowthPaddedCutTransport.base_respects_iff P _).mpr
    simpa only [b, Function.comp_def, Equiv.apply_symm_apply] using hq
  obtain ⟨r, hr, hread, hcap⟩ := GrowthOrderedBase.donor_lift_of_arity I X T
    (by omega) hB hC hsmall
    ((full_respects_iff I.left I.placeLeft I.imageLeft (donorFace P) 1 p).mp hp)
    hq' hγ (fun d => hag (e d))
  refine ⟨r ∘ b.symm, (GrowthPaddedCutTransport.base_respects_iff P r).mp hr, ?_, ?_⟩
  · intro d
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (b.symm d)
  · intro d
    obtain ⟨x, rfl⟩ := e.surjective d
    have hid : CellScheme.below.mono
        (show GradedLe (B, 1) (A, 1) from ⟨hB.subset, le_rfl⟩) (e x) =
        b (GrowthOrderedBase.donorAt I X (by omega) x) := rfl
    rw [Function.comp_apply, hid, Equiv.symm_apply_apply]
    exact hread x
end Layer

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

/-- Every positive cutoff on one fixed built carrier; all external caps. -/
theorem private_clause (t : ℕ) (ht : t + 2 ≤ A.card)
    (j : ℕ) (hj : 1 ≤ j) (hjt : j ≤ t + 2) :
    CappedLift (build I X T hA hB hC t ht).rows
      (show GradedLe (C, j) (A, j) from ⟨hC.subset, le_rfl⟩) := by
  induction t with
  | zero =>
    have he : j = 1 ∨ j = 2 := by omega
    rcases he with rfl | rfl
    · exact private_one _
    · exact native_private _ (GrowthPaddedOriginalInduction.build_private I X T hA hB hC 0 ht)
  | succ t ih =>
    by_cases he : j = t + 1 + 2
    · subst j
      exact native_private _ (GrowthPaddedOriginalInduction.build_private I X T hA hB hC _ ht)
    · exact GrowthPaddedCutTransport.step_lift (build I X T hA hB hC t (by omega))
        (by omega) (by omega) _ (by omega) (ih (by omega) (by omega))

/-- Strict donor arity suffices at every cutoff, including activated heights. -/
theorem donor_clause (hsmall : n + 1 < X.req.N) (t : ℕ) (ht : t + 2 ≤ A.card)
    (j : ℕ) (hj : 1 ≤ j) (hjt : j ≤ t + 2) :
    CappedLift (build I X T hA hB hC t ht).rows
      (show GradedLe (B, j) (A, j) from ⟨hB.subset, le_rfl⟩) := by
  induction t with
  | zero =>
    have he : j = 1 ∨ j = 2 := by omega
    rcases he with rfl | rfl
    · exact donor_one _ hsmall
    · exact native_donor _
        (GrowthPaddedOriginalInduction.build_donor I X T hA hB hC hsmall 0 ht)
  | succ t ih =>
    by_cases he : j = t + 1 + 2
    · subst j
      exact native_donor _
        (GrowthPaddedOriginalInduction.build_donor I X T hA hB hC hsmall _ ht)
    · exact GrowthPaddedCutTransport.step_lift (build I X T hA hB hC t (by omega))
        (by omega) (by omega) _ (by omega) (ih (by omega) (by omega))

/-- A private-contained subface is extended inside the original legal scheme
against the restricted actual ambient before the full private lift is used. -/
theorem private_subface (t : ℕ) (ht : t + 2 ≤ A.card)
    {S : Finset ι} {i j : ℕ} (hS : (S, i) ∈ Plan.gradedPlan R)
    (hSC : S ⊆ C) (hij : i ≤ j) (hj : j ≤ t + 2) :
    CappedLift (build I X T hA hB hC t ht).rows
      (show GradedLe (S, i) (A, j) from ⟨hSC.trans hC.subset, hij⟩) := by
  have hCi : (C, i) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
    ⟨I.rightPlan_le I.rightScheme.isPlan.domain_mem, (Plan.mem_gradedPlan.mp hS).2.1,
      (Plan.mem_gradedPlan.mp hS).2.2.trans (Finset.card_le_card hSC)⟩
  have hl := (inherited_lift (build I X T hA hB hC t ht) hS hCi
    (show GradedLe (S, i) (C, i) from ⟨hSC, le_rfl⟩)
    (Or.inr (Finset.Subset.refl _))).comp
      (private_clause I X T hA hB hC t ht i (Plan.mem_gradedPlan.mp hS).2.1 (hij.trans hj))
  exact hl.raise_target (h := hSC.trans hC.subset) hij

/-- The donor direction uses its own constructed lifts; the asymmetric
growth admission is not exchanged with the private family. -/
theorem donor_subface (hsmall : n + 1 < X.req.N) (t : ℕ) (ht : t + 2 ≤ A.card)
    {S : Finset ι} {i j : ℕ} (hS : (S, i) ∈ Plan.gradedPlan R)
    (hSB : S ⊆ B) (hij : i ≤ j) (hj : j ≤ t + 2) :
    CappedLift (build I X T hA hB hC t ht).rows
      (show GradedLe (S, i) (A, j) from ⟨hSB.trans hB.subset, hij⟩) := by
  have hBi : (B, i) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
    ⟨I.leftPlan_le I.leftScheme.isPlan.domain_mem, (Plan.mem_gradedPlan.mp hS).2.1,
      (Plan.mem_gradedPlan.mp hS).2.2.trans (Finset.card_le_card hSB)⟩
  have hl := (inherited_lift (build I X T hA hB hC t ht) hS hBi
    (show GradedLe (S, i) (B, i) from ⟨hSB, le_rfl⟩)
    (Or.inl (Finset.Subset.refl _))).comp
      (donor_clause I X T hA hB hC hsmall t ht i (Plan.mem_gradedPlan.mp hS).2.1
        (hij.trans hj))
  exact hl.raise_target (h := hSB.trans hB.subset) hij

/-- Exactly the original-contained pair fragment. There is no mixed-source
clause and no assertion of TargetGradeLifting.Through. -/
theorem lift (hsmall : n + 1 < X.req.N) (t : ℕ) (ht : t + 2 ≤ A.card)
    {U V : Finset ι × ℕ}
    (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V)
    (hcase : (V.1 ⊆ B ∨ V.1 ⊆ C) ∨
      (V.1 = A ∧ V.2 ≤ t + 2 ∧ (U.1 ⊆ B ∨ U.1 ⊆ C))) :
    CappedLift (build I X T hA hB hC t ht).rows h := by
  rcases hcase with ho | ⟨hf, hj, ho⟩
  · exact inherited_lift _ hU hV h ho
  · rcases U with ⟨S, i⟩
    rcases V with ⟨V, j⟩
    dsimp only at hf hj ho
    subst V
    rcases ho with hb | hc
    · exact donor_subface I X T hA hB hC hsmall t ht hU hb h.2 hj
    · exact private_subface I X T hA hB hC t ht hU hc h.2 hj

/-- Acceptance endpoint on the final full-height carrier. The entire lawful
subface prescription, including invisible values and top above the cap, is
retained; cap equality quantifies over every actual target occurrence. -/
theorem full_height (hsmall : n + 1 < X.req.N)
    {U V : Finset ι × ℕ}
    (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R) (h : GradedLe U V)
    (hcase : (V.1 ⊆ B ∨ V.1 ⊆ C) ∨ (V.1 = A ∧ (U.1 ⊆ B ∨ U.1 ⊆ C))) :
    CappedLift (build I X T hA hB hC (A.card - 2) (by omega)).rows h := by
  apply lift I X T hA hB hC hsmall _ _ hU hV h
  rcases hcase with ho | ⟨hf, ho⟩
  · exact Or.inl ho
  · refine Or.inr ⟨hf, ?_, ho⟩
    have hg := (Plan.mem_gradedPlan.mp hV).2.2
    rw [hf] at hg
    omega

/-- Expanded acceptance test: a genuinely lower target cutoff on the final
full-height carrier, arbitrary original-contained subface input and all caps.
No bound is imposed on prescribed values above the cap, and top is allowed. -/
theorem lower_cutoff (hsmall : n + 1 < X.req.N)
    {S : Finset ι} {i j : ℕ} (hS : (S, i) ∈ Plan.gradedPlan R)
    (hface : S ⊆ B ∨ S ⊆ C) (hij : i ≤ j) (hj : j < A.card)
    {p : (build I X T hA hB hC (A.card - 2) (by omega)).carrier.below (S, i) → ExtOrd}
    {q : (build I X T hA hB hC (A.card - 2) (by omega)).carrier.below (A, j) → ExtOrd}
    (hp : RespectsSemanticsBelow
      (build I X T hA hB hC (A.card - 2) (by omega)).rows (S, i) p)
    (hq : RespectsSemanticsBelow
      (build I X T hA hB hC (A.card - 2) (by omega)).rows (A, j) q)
    {γ : ExtOrd} (hγ : SelfVis j γ)
    (hag : ∀ d, min (q (CellScheme.below.mono
      (show GradedLe (S, i) (A, j) from
        ⟨hface.elim (fun h => h.trans hB.subset) (fun h => h.trans hC.subset), hij⟩) d)) γ =
      min (p d) γ) :
    ∃ r : (build I X T hA hB hC (A.card - 2) (by omega)).carrier.below (A, j) → ExtOrd,
      RespectsSemanticsBelow
        (build I X T hA hB hC (A.card - 2) (by omega)).rows (A, j) r ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ d, r (CellScheme.below.mono
        (show GradedLe (S, i) (A, j) from
          ⟨hface.elim (fun h => h.trans hB.subset) (fun h => h.trans hC.subset), hij⟩) d) =
        p d := by
  apply full_height I X T hA hB hC hsmall hS
    (Plan.mem_gradedPlan.mpr ⟨I.isPlan.domain_mem,
      (Plan.mem_gradedPlan.mp hS).2.1.trans_le hij, hj.le⟩) _
    (Or.inr ⟨rfl, hface⟩) p q γ hp hq hγ hag

end
end VaughtConjecture.Knight.GrowthPaddedAllCutoff
