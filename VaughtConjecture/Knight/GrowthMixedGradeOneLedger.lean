/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthMixedGradeOne
public import VaughtConjecture.Knight.GrowthReplicatedAllCutoff

/-! # The complete same-grade-one ledger on every built growth carrier

Three steps close grade one on the replicated growth carrier.

* **Mixed to mixed** (`cappedLift_to`): for eligible scopes `U ⊆ V`, extend the prescription to the
  full scope (`GrowthMixedGradeOne.lawfulExtension`) and restrict back to `V`; two lawful sections
  below `(V, 1)` agreeing on the `U`-copies agree everywhere, by the same recognition at `V`.
  `ExtensionInjectivity` then gives the capped lift `(U, 1) ≤ (V, 1)`.
* **Original-contained source, mixed target** (`face_to_mixed`): extend the target ambient to the
  full scope, lift the prescription there by KVC's fixed-carrier original-face lift
  (`GrowthReplicatedAllCutoff`, with the explicit strict donor-arity bound on the donor side),
  and restrict the result back to the target; every cap and the literal prescription survive.
* **The ledger** (`ledger`): every grade-one graded pair of the plan on every built carrier —
  original-contained targets by the inherited face lifts, mixed targets by the two steps above.

No row changes, no higher grade, no admission or activation hypothesis beyond KVC's explicit
donor-arity bound. -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GrowthMixedGradeOneLedger

open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
open GrowthPaddedContract ScopeReplicationCarrier CoatomBoundaryExtension GrowthMixedGradeOne

noncomputable section

theorem le_target {ι : Type*} {U V : Finset ι} (hUV : U ⊆ V) :
    GradedLe ((U, 1) : Finset ι × ℕ) (V, 1) := ⟨hUV, le_rfl⟩

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

/-! ## Mixed source, mixed target, on any installed layer -/

section Layer

variable {k : ℕ} (P : Layer I X T hA hB hC k)
  (U V : Finset ι) (hU : U ∈ P.carrier.plan) (hV : V ∈ P.carrier.plan)
  (hmU : U = A ∨ Mixed B C U) (hmV : V = A ∨ Mixed B C V) (hUV : U ⊆ V)

local notation "Carrier" => GrowthReplicatedRows.carrier P
local notation "Rows" => GrowthReplicatedRows.rows P

include hU hV hmU in
/-- Extend to the full scope, then restrict to the target: literal on the source. -/
theorem lawfulExtension_to :
    ExtensionInjectivity.LawfulExtension Rows (le_target hUV) := by
  intro p hp
  obtain ⟨r, hr, hres⟩ := lawfulExtension I X T hA hB hC P U hU hmU p hp
  refine ⟨fun d => r (CellScheme.below.mono (le_full I X T hA hB hC P V hV) d),
    hr.mono (le_full I X T hA hB hC P V hV), fun d => ?_⟩
  exact hres d

include hU hV hmU hmV in
/-- Two lawful sections below `(V, 1)` agreeing on the `U`-copies agree everywhere. -/
theorem eq_of_restriction_to {r r' : CellScheme.below Carrier (V, 1) → ExtOrd}
    (hr : RespectsSemanticsBelow Rows (V, 1) r) (hr' : RespectsSemanticsBelow Rows (V, 1) r')
    (hag : ∀ z : CellScheme.below Carrier (U, 1),
      r (CellScheme.below.mono (le_target hUV) z) =
        r' (CellScheme.below.mono (le_target hUV) z))
    (z : CellScheme.below Carrier (V, 1)) : r z = r' z := by
  have haux (w : CellScheme.below Carrier (V, 1))
      (hw : P.carrier.scope (GrowthReplicatedRows.erase P w.1) = A) : r w = r' w :=
    ScopeReplicationRestriction.auxiliary_eq P.carrier B C
      (GrowthReplicatedRows.proper_covered P) P.rows hU hmU (one_le_card hA hmU) hV hmV
      (one_le_card hA hmV) hUV hr hr' hag w hw
  have hg : P.carrier.grade (GrowthReplicatedRows.erase P z.1) ≤ 1 := by
    rw [erase_grade]; exact z.2.2
  obtain ⟨b, hb⟩ := eq_baseMap_of_grade_le_one I X T hA hB hC P _ hg
  rcases RelativeLadderLayer.cell_cases I.boundary (GrowthLeafRecognition.card_pos hA) b with
    ⟨d, rfl⟩ | ⟨v, rfl⟩
  · rw [original_readback_one I X T hA hB hC P V hV hmV hr z d hb,
      original_readback_one I X T hA hB hC P V hV hmV hr' z d hb]
    apply Finset.sup_congr rfl
    intro c _
    apply haux
    rw [erase_ladder]
    exact scope_added I X T hA hB hC P _
  · apply haux
    rw [hb]
    exact scope_added I X T hA hB hC P v

include hU hV hmU hmV in
theorem restrictionInjective_to :
    ExtensionInjectivity.RestrictionInjective Rows (le_target hUV) :=
  fun _ _ hr hr' hag => eq_of_restriction_to I X T hA hB hC P U V hU hV hmU hmV hUV hr hr' hag

include hU hV hmU hmV in
/-- Mixed-to-mixed extension is independent of all subsequently supplied caps and ambients. -/
theorem allCapsExtension_to : ExtensionInjectivity.AllCapsExtension Rows (le_target hUV) :=
  ExtensionInjectivity.allCapsExtension_of_extension_injective
    (lawfulExtension_to I X T hA hB hC P U V hU hV hmU hUV)
    (restrictionInjective_to I X T hA hB hC P U V hU hV hmU hmV hUV)

include hU hV hmU hmV in
/-- **The mixed-to-mixed grade-one capped lift**, on any installed layer, every permitted cap. -/
theorem cappedLift_to : CappedLift Rows (le_target hUV) :=
  (allCapsExtension_to I X T hA hB hC P U V hU hV hmU hmV hUV).cappedLift

end Layer

/-! ## Original-contained source, mixed target, on a built carrier -/

section Fixed

variable (t : ℕ) (ht : t + 2 ≤ A.card)

local notation "Built" => GrowthPaddedIteration.build I X T hA hB hC t ht
local notation "BRows" =>
  GrowthReplicatedRows.rows (GrowthPaddedIteration.build I X T hA hB hC t ht)

theorem mem_plan_of_graded {U : Finset ι} (hU : (U, 1) ∈ Plan.gradedPlan R) :
    U ∈ (GrowthPaddedIteration.build I X T hA hB hC t ht).carrier.plan := by
  rw [GrowthPaddedIteration.build_plan]
  exact (Plan.mem_gradedPlan.mp hU).1

/-- Lift an original-contained prescription against a mixed target: extend the target ambient to
the full scope, lift there by the fixed-carrier original-face lift, restrict back. -/
theorem face_to_mixed_of_full {S V : Finset ι} (hV : (V, 1) ∈ Plan.gradedPlan R)
    (hmV : V = A ∨ Mixed B C V) (hSV : S ⊆ V)
    (hfull : CappedLift BRows (show GradedLe (S, 1) (A, 1) from
      ⟨hSV.trans ((GrowthPaddedIteration.build I X T hA hB hC t ht).carrier.isPlan.subset_of_mem
        (mem_plan_of_graded I X T hA hB hC t ht hV)), le_rfl⟩)) :
    CappedLift BRows (show GradedLe (S, 1) (V, 1) from ⟨hSV, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  have hVp := mem_plan_of_graded I X T hA hB hC t ht hV
  obtain ⟨qf, hqf, hqres⟩ := lawfulExtension I X T hA hB hC Built V hVp hmV q hq
  obtain ⟨rf, hrf, hrcap, hrres⟩ := hfull p qf γ hp hqf hγ (fun d => by
    change min (qf (CellScheme.below.mono (le_full I X T hA hB hC Built V hVp)
      (CellScheme.below.mono (show GradedLe (S, 1) (V, 1) from ⟨hSV, le_rfl⟩) d))) γ = _
    rw [hqres]
    exact hag d)
  refine ⟨fun d => rf (CellScheme.below.mono (le_full I X T hA hB hC Built V hVp) d),
    hrf.mono (le_full I X T hA hB hC Built V hVp), fun d => ?_, fun d => hrres d⟩
  rw [hrcap, hqres]

/-- Private-face source (inside `C`), mixed target. -/
theorem private_to_mixed {S V : Finset ι} (hS : (S, 1) ∈ Plan.gradedPlan R)
    (hSC : S ⊆ C) (hV : (V, 1) ∈ Plan.gradedPlan R) (hmV : V = A ∨ Mixed B C V) (hSV : S ⊆ V) :
    CappedLift BRows (show GradedLe (S, 1) (V, 1) from ⟨hSV, le_rfl⟩) :=
  face_to_mixed_of_full I X T hA hB hC t ht hV hmV hSV
    (GrowthReplicatedAllCutoff.private_subface I X T hA hB hC t ht hS hSC le_rfl (by omega))

/-- Donor-face source (inside `B`), mixed target; the strict donor-arity bound stays explicit. -/
theorem donor_to_mixed (hsmall : n + 1 < X.req.N) {S V : Finset ι}
    (hS : (S, 1) ∈ Plan.gradedPlan R) (hSB : S ⊆ B) (hV : (V, 1) ∈ Plan.gradedPlan R)
    (hmV : V = A ∨ Mixed B C V) (hSV : S ⊆ V) :
    CappedLift BRows (show GradedLe (S, 1) (V, 1) from ⟨hSV, le_rfl⟩) :=
  face_to_mixed_of_full I X T hA hB hC t ht hV hmV hSV
    (GrowthReplicatedAllCutoff.donor_subface I X T hA hB hC t ht hsmall hS hSB le_rfl (by omega))

/-! ## The ledger -/

/-- **The complete same-grade-one ledger** on every built carrier: every grade-one graded pair
of the plan has the capped lift at every permitted cap. -/
theorem ledger (hsmall : n + 1 < X.req.N) {U V : Finset ι}
    (hU : (U, 1) ∈ Plan.gradedPlan R) (hV : (V, 1) ∈ Plan.gradedPlan R) (hUV : U ⊆ V) :
    CappedLift BRows (show GradedLe (U, 1) (V, 1) from ⟨hUV, le_rfl⟩) := by
  by_cases hside : V ⊆ B ∨ V ⊆ C
  · exact GrowthReplicatedRows.inherited_lift t ht hU hV ⟨hUV, le_rfl⟩ hside
  have hmV : V = A ∨ Mixed B C V :=
    Or.inr ⟨fun h => hside (Or.inl h), fun h => hside (Or.inr h)⟩
  by_cases hUB : U ⊆ B
  · exact donor_to_mixed I X T hA hB hC t ht hsmall hU hUB hV hmV hUV
  by_cases hUC : U ⊆ C
  · exact private_to_mixed I X T hA hB hC t ht hU hUC hV hmV hUV
  exact cappedLift_to I X T hA hB hC Built U V (mem_plan_of_graded I X T hA hB hC t ht hU)
    (mem_plan_of_graded I X T hA hB hC t ht hV) (Or.inr ⟨hUB, hUC⟩) hmV hUV

end Fixed

end
end VaughtConjecture.Knight.GrowthMixedGradeOneLedger
