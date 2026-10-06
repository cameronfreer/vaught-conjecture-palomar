/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedExtension
public import VaughtConjecture.Knight.GrowthMixedGradeOneLedger
public import VaughtConjecture.Knight.EffectiveGradeLifting

/-! # Bountifulness of the fixed full-height replicated growth carrier

The ledger uses the constructed mixed extension, restriction injectivity,
KVC's fixed-carrier original-face lifts, and the literal inherited faces.
Every target ambient is arbitrary and every actual auxiliary keeps its own cap.
Same-grade pairs exhaust the plan; the existing grade-change reduction supplies
all graded pairs. No bountifulness of an unfinished carrier is assumed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthReplicatedBountiful
open AmalgamationPlan Transform Value ExtOrd Growth CoatomBoundaryExtension
open GrowthHigherMixed
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

section Cutoff
variable (t : ℕ) (ht : t + 2 ≤ A.card)
local notation "Rows" => rows I X T hA hB hC t ht

/-- Extend the actual mixed-target ambient, use the constructed original-face
lift at full scope, and restrict back. This includes source grade changes. -/
theorem original_to_mixed (hsmall : n + 1 < X.req.N)
    {S V : Finset ι} {i j : ℕ} (hS : (S, i) ∈ Plan.gradedPlan R)
    (hV : V ∈ R) (hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V)
    (hv : j ≤ V.card) (hjt : j ≤ t + 2)
    (h : GradedLe (S, i) (V, j)) (hs : S ⊆ B ∨ S ⊆ C) :
    CappedLift Rows h := by
  have hVA : V ⊆ A := I.isPlan.subset_of_mem hV
  have hj0 : 1 ≤ j := (Plan.mem_gradedPlan.mp hS).2.1.trans_le h.2
  have hfull : CappedLift Rows
      (show GradedLe (S, i) (A, j) from ⟨h.1.trans hVA, h.2⟩) := by
    rcases hs with hb | hc
    · exact GrowthReplicatedAllCutoff.donor_subface I X T hA hB hC t ht
        hsmall hS hb h.2 hjt
    · exact GrowthReplicatedAllCutoff.private_subface I X T hA hB hC t ht
        hS hc h.2 hjt
  intro p q γ hp hq hγ hag
  let hvA : GradedLe (V, j) (A, j) := ⟨hVA, le_rfl⟩
  obtain ⟨q', hq', hqeq⟩ := lawfulExtension I X T hA hB hC t ht
    V hV hmV j hv hj0 hjt A hVA q hq
  obtain ⟨r, hr, hcap, hread⟩ := hfull p q' γ hp hq' hγ (fun d =>
    (congrArg (fun z => min z γ) (hqeq (CellScheme.below.mono h d))).trans (hag d))
  refine ⟨fun d => r (CellScheme.below.mono hvA d), hr.mono hvA, ?_, fun d => hread d⟩
  intro d
  exact (hcap (CellScheme.below.mono hvA d)).trans (congrArg (fun z => min z γ) (hqeq d))

/-- Every same-grade pair at an installed cutoff on one fixed carrier.
The strict arity hypothesis is used only for the donor-original direction. -/
theorem same_grade (hsmall : n + 1 < X.req.N) (S V : Finset ι) (j : ℕ)
    (hS : (S, j) ∈ Plan.gradedPlan R) (hV : (V, j) ∈ Plan.gradedPlan R)
    (hjt : j ≤ t + 2) (hSV : S ⊆ V) :
    CappedLift Rows (show GradedLe (S, j) (V, j) from ⟨hSV, le_rfl⟩) := by
  by_cases htarget : V ⊆ B ∨ V ⊆ C
  · exact GrowthReplicatedRows.inherited_lift t ht hS hV _ htarget
  have hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V := Or.inr
    ⟨fun hb => htarget (Or.inl hb), fun hc => htarget (Or.inr hc)⟩
  by_cases hs : S ⊆ B ∨ S ⊆ C
  · exact original_to_mixed I X T hA hB hC t ht hsmall hS
      (Plan.mem_gradedPlan.mp hV).1 hmV (Plan.mem_gradedPlan.mp hV).2.2 hjt ⟨hSV, le_rfl⟩ hs
  · exact cappedLift I X T hA hB hC t ht S (Plan.mem_gradedPlan.mp hS).1
      (Or.inr ⟨fun hb => hs (Or.inl hb), fun hc => hs (Or.inr hc)⟩)
      j (Plan.mem_gradedPlan.mp hS).2.2 (Plan.mem_gradedPlan.mp hS).2.1 hjt
      V (Plan.mem_gradedPlan.mp hV).1 hmV (Plan.mem_gradedPlan.mp hV).2.2 hSV

end Cutoff

/-- The unchanged replicated growth rows are bountiful at full height.
Literal top, bottom caps, arbitrary lawful local ambients and all individual
auxiliary caps are included in the repository's `IsBountiful` conclusion. -/
theorem bountiful (hsmall : n + 1 < X.req.N) :
    (rows I X T hA hB hC (A.card - 2) (by omega)).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_same_grade
  intro S V j hS hV hSV
  have hp : (carrier I X T hA hB hC (A.card - 2) (by omega)).plan = R :=
    GrowthPaddedIteration.build_plan I X T hA hB hC (A.card - 2) (by omega)
  have hS' : (S, j) ∈ Plan.gradedPlan R := by rwa [hp] at hS
  have hV' : (V, j) ∈ Plan.gradedPlan R := by rwa [hp] at hV
  have hj := (Plan.mem_gradedPlan.mp hV').2.2
  have hc := Finset.card_le_card (I.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hV').1)
  exact same_grade I X T hA hB hC (A.card - 2) (by omega) hsmall
    S V j hS' hV' (by omega) hSV

end
end VaughtConjecture.Knight.GrowthReplicatedBountiful
