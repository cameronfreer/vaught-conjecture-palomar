/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryPlanScopeStep

/-! # The ordinary producer on its actual raw boundary

Factor the existing canonical constructors over their old-boundary premises.
No second enumeration, independently chosen facet, or output lifting theorem
is supplied. The binary facets and their common plan come from this plan.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryRawScope
open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension
open OrdinaryScopeOperator AmalgamatedBoundaryPlan
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D)

/-- Properties of the existing proper boundary, not of a prospective output. -/
structure Ready : Prop where
  proper : ∀ d : Cell D, D.scope d ≠ A
  consistent : sem.IsConsistent
  coded : sem.IsCoded
  lifts : CanonicalCoatomBountiful.OldLifts sem
  complete : ∀ J ∈ Plan.gradedPlan D.plan, J.1 ≠ A → ∃ d, D.cell d = J

variable (H : Ready sem) (s : Step A) (hplan : D.plan = s.plan)

include hplan in
theorem left_mem : A.erase s.a ∈ D.plan := by
  rw [hplan]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ s.left_plan.domain_mem)

include hplan in
theorem right_mem : A.erase s.b ∈ D.plan := by
  rw [hplan]
  exact Finset.mem_union_left _ (Finset.mem_union_right _ s.right_plan.domain_mem)

include hplan in
theorem overlap_mem : A.erase s.a ∩ A.erase s.b ∈ D.plan := by
  rw [hplan, erased_inter]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ s.common_left)

include hplan in
theorem coverage (C : Finset ι) (hC : C ∈ D.plan) (hCA : C ≠ A) :
    C ⊆ A.erase s.a ∨ C ⊆ A.erase s.b :=
  OrdinaryPlanScopeStep.coverage s C (hplan ▸ hC) hCA

include H in
theorem boundary_grade {k : ℕ} (hA : A.card ≤ k + 1) (d : Cell D) : D.grade d ≤ k := by
  have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), H.proper d⟩)
  have hg := D.grade_le_card_scope d
  omega

private def bottomProfile (j : ℕ) : CanonicalFieldLayer.Profile sem j (Cell D) id := by
  refine ⟨fun _ => ⊥, ⟨?_, ?_, ?_⟩, rfl, fun _ => bot_ne_top⟩
  · intro d; exact (extVisibilityReplace_bot _ _).symm
  · intro c
    simpa only [Function.comp_apply, min_self] using TransformsTo.to_bot (sem.E c)
  · intro _ b _ _; exact ⟨b, rfl, le_rfl⟩

def one (hA : 1 ≤ A.card) (hg : ∀ d : Cell D, D.grade d ≤ 1)
    (hL : 1 ≤ (A.erase s.a).card) (hR : 1 ≤ (A.erase s.b).card) :
    OrdinaryScopeOperator.Core sem 1 where
  carrier := CanonicalOneCoatom.scheme sem hA
  rows := CanonicalOneCoatom.rows sem hA H.proper hg
  plan := rfl
  original := OrderEmbedding.ofStrictMono (CanonicalOneCoatom.old sem hA)
    (SourceLayerCarrier.old_order _ _ _ _ _)
  index d := SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)
  coverage d := by
    obtain ⟨x, rfl⟩ := (SourceLayerCarrier.enumeration D
      (CanonicalFieldLayer.Profile sem 1 (Cell D) id) 1 (by decide) hA).surjective d
    cases x with
    | inl c => exact Or.inl ⟨c, rfl⟩
    | inr q => exact Or.inr (congrArg Prod.fst (SourceLayerCarrier.cell_toCell _ _ _ _ _ _))
  row := CanonicalFieldLayer.inherited_row sem 1 (Cell D) id (by decide) hA H.proper hg
  consistent := CanonicalFieldLayer.consistent sem 1 (Cell D) id (by decide) hA
    H.proper hg H.consistent
  coded := CanonicalSeedCoding.fieldLayer sem 1 (Cell D) id (by decide) hA H.proper hg H.coded
  bountiful := CanonicalOneCoatom.bountiful sem hA H.proper hg H.lifts
    (left_mem s hplan) (right_mem s hplan)
    (OrdinaryPlanScopeStep.left_proper s) (OrdinaryPlanScopeStep.right_proper s)
    hL hR (overlap_mem s hplan) (coverage s hplan)
    (fun C hC hCA hc => H.complete (C, 1) (Plan.mem_gradedPlan.mpr ⟨hC, Nat.zero_lt_one, hc⟩) hCA)
  grade := (CanonicalFieldLayer.data sem 1 (Cell D) id (by decide) hA H.proper hg).max_grade
  complete J hJ hj := by
    have hj1 : J.2 = 1 := by have := (Plan.mem_gradedPlan.mp hJ).2.1; omega
    by_cases hJA : J.1 = A
    · exact ⟨(CanonicalFieldLayer.controller sem 1 (Cell D) id (by decide) hA
        (bottomProfile sem 1)).1,
        (CanonicalFieldLayer.controller sem 1 (Cell D) id (by decide) hA
          (bottomProfile sem 1)).2.trans (Prod.ext hJA.symm hj1.symm)⟩
    · obtain ⟨d, hd⟩ := H.complete J hJ hJA
      exact ⟨CanonicalOneCoatom.old sem hA d,
        (SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)).trans hd⟩
  short := CanonicalFieldLayer.full_source_short sem 1 (Cell D) id (by decide) hA H.proper hg
  render := CanonicalFieldLayer.sectionOf sem 1 (Cell D) id (by decide) hA H.proper hg
  readback := CanonicalFieldLayer.section_old sem 1 (Cell D) id (by decide) hA H.proper hg
  lawful := CanonicalFieldLayer.section_lawful sem 1 (Cell D) id (by decide) hA H.proper hg
  bound := CanonicalFieldLayer.section_bound sem 1 (Cell D) id (by decide) hA H.proper hg
  support := CanonicalFieldLayer.section_supported sem 1 (Cell D) id (by decide) hA H.proper hg
  agreement := fun hp ht hq htq => CanonicalFieldLayer.section_agreement sem 1 (Cell D) id
    (by decide) hA H.proper hg hp ht hq htq

def two (hA : 3 ≤ A.card) (hg : ∀ d : Cell D, D.grade d ≤ 2)
    (hL : 2 ≤ (A.erase s.a).card) (hR : 2 ≤ (A.erase s.b).card) :
    OrdinaryScopeOperator.Core sem 2 where
  carrier := CanonicalPairLocalSections.carrier sem (by omega)
  rows := CanonicalPairLocalSections.semantics sem (by omega) H.proper
  plan := rfl
  original := CanonicalRecursiveInventory.boundary sem 2 (by omega)
  index := CanonicalRecursiveInventory.boundary_cell sem 2 (by omega)
  coverage d := by
    rcases RecursiveSourceCarrier.classify D (CanonicalRecursiveInventory.Profile sem)
      2 (by omega) d with ⟨c, rfl⟩ | ⟨j, _, _, he⟩
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr (congrArg Prod.fst he)
  row := GradeCutPairRows.old_row D _ _ 1 2 (by decide)
    (CanonicalPairLocalSections.one_le (by omega)) (by decide) (by omega) H.proper
    (by decide) sem (CanonicalPairLocalSections.smallRows sem (by omega) H.proper)
  consistent := CanonicalPairBoundary.consistent sem 1 2 (by decide) (by omega) (by decide)
    (by omega) H.proper (by decide) H.consistent
  coded := CanonicalSeedCoding.pair sem (by omega) H.proper H.coded
  bountiful := by
    apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
      (CanonicalRecursiveCoverage.grade_bound sem 2 (by omega) hg) (by decide : 0 < 2)
    intro C T j hC hT hj hCT
    exact CanonicalPairLowerLifting.lower_lift sem H.proper (by omega) H.lifts
      (left_mem s hplan) (right_mem s hplan)
      (OrdinaryPlanScopeStep.left_proper s) (OrdinaryPlanScopeStep.right_proper s)
      hL hR (overlap_mem s hplan) (coverage s hplan)
      (fun C hC hCA j hj hjC _ => H.complete (C, j) (Plan.mem_gradedPlan.mpr ⟨hC, hj, hjC⟩) hCA)
      hC hT ⟨hCT, le_rfl⟩ hj
  grade := CanonicalRecursiveCoverage.grade_bound sem 2 (by omega) hg
  complete := CanonicalRecursiveCoverage.complete_through sem 2 (by omega) H.complete
  short := CanonicalProperOwnerSections.lower_full_short sem 3 (by decide) hA H.proper
  render := fun hp ht => CanonicalPairLocalSections.sectionOf sem (by omega) H.proper
    (by omega : 2 ≤ A.card) (hp.toBelow (A, A.card)) ht
  readback := by
    intro p hp ht G θ _ _ d
    exact CanonicalPairLocalSections.section_old sem (by omega) H.proper
      (by omega : 2 ≤ A.card) (hp.toBelow (A, A.card)) ht d
  lawful := by
    intro p hp ht G θ hG hθ
    apply (CanonicalPairLocalSections.section_lawful sem (by omega) H.proper
      (by omega : 2 ≤ A.card) (hp.toBelow (A, A.card)) ht hG hθ).toRespects
    intro d
    exact ⟨(CanonicalPairLocalSections.carrier sem (by omega)).isPlan.subset_of_mem
      ((CanonicalPairLocalSections.carrier sem (by omega)).scope_mem_plan d),
      (CanonicalRecursiveCoverage.grade_bound sem 2 (by omega) hg d).trans (by omega)⟩
  bound := fun hp ht => CanonicalPairLocalSections.section_bound sem (by omega) H.proper
    (by omega : 2 ≤ A.card) (hp.toBelow (A, A.card)) ht
  support := fun hp ht => CanonicalPairLocalSections.section_supported sem (by omega) H.proper
    (by omega : 2 ≤ A.card) (hp.toBelow (A, A.card)) ht
  agreement := fun hp ht hq htq => CanonicalPairLocalSections.section_agreement sem
    (by omega) H.proper
    (by omega : 2 ≤ A.card) (hp.toBelow (A, A.card)) ht (hq.toBelow (A, A.card)) htq

def higher (n : ℕ) (hA : n + 3 ≤ A.card) (hg : ∀ d : Cell D, D.grade d ≤ n + 3)
    (hL : n + 3 ≤ (A.erase s.a).card) (hR : n + 3 ≤ (A.erase s.b).card) :
    OrdinaryScopeOperator.Core sem (n + 3) where
  carrier := CanonicalRecursiveContract.carrier sem n hA
  rows := CanonicalRecursiveSemantics.rows sem H.proper n hA
  plan := CanonicalRecursiveBoundaryTransport.plan_eq sem (n + 3) hA
  original := CanonicalRecursiveInventory.boundary sem (n + 3) hA
  index := CanonicalRecursiveInventory.boundary_cell sem (n + 3) hA
  coverage d := by
    rcases RecursiveSourceCarrier.classify D (CanonicalRecursiveInventory.Profile sem)
      (n + 3) hA d with ⟨c, rfl⟩ | ⟨j, _, _, he⟩
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr (congrArg Prod.fst he)
  row := CanonicalRecursiveLiteralRows.row sem H.proper n hA
  consistent := CanonicalRecursiveSemantics.consistent sem H.proper H.consistent n hA
  coded := CanonicalRecursiveCoding.coded sem H.proper H.coded n hA
  bountiful := by
    apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
      (CanonicalRecursiveCoverage.grade_bound sem (n + 3) hA hg) (by omega : 0 < n + 3)
    intro C T j hC hT hj hCT
    rw [CanonicalRecursiveBoundaryTransport.plan_eq] at hC hT
    exact CanonicalRecursiveInitialized.lift sem H.proper H.consistent H.lifts
      (left_mem s hplan) (right_mem s hplan)
      (OrdinaryPlanScopeStep.left_proper s) (OrdinaryPlanScopeStep.right_proper s)
      (overlap_mem s hplan) (coverage s hplan) n hA hL hR
      (fun C hC hCA j hj hjC _ => H.complete (C, j) (Plan.mem_gradedPlan.mpr ⟨hC, hj, hjC⟩) hCA)
      hC hT ⟨hCT, le_rfl⟩ hj
  grade := CanonicalRecursiveCoverage.grade_bound sem (n + 3) hA hg
  complete := CanonicalRecursiveCoverage.complete_through sem (n + 3) hA H.complete
  short := (CanonicalRecursiveSemantics.state sem H.proper n hA).full_short
  render := fun hp ht => (CanonicalRecursiveSemantics.state sem H.proper n hA).sectionOf
    hA (hp.toBelow (A, A.card)) ht
  readback := fun hp ht => (CanonicalRecursiveSemantics.state sem H.proper n hA).section_boundary
    hA (hp.toBelow (A, A.card)) ht
  lawful := by
    intro p hp ht G θ hG hθ
    apply ((CanonicalRecursiveSemantics.state sem H.proper n hA).section_lawful
      hA (hp.toBelow (A, A.card)) ht hG hθ).toRespects
    intro d
    exact ⟨(CanonicalRecursiveContract.carrier sem n hA).isPlan.subset_of_mem
      ((CanonicalRecursiveContract.carrier sem n hA).scope_mem_plan d),
      (CanonicalRecursiveCoverage.grade_bound sem (n + 3) hA hg d).trans hA⟩
  bound := fun hp ht => (CanonicalRecursiveSemantics.state sem H.proper n hA).section_bound
    hA (hp.toBelow (A, A.card)) ht
  support := fun hp ht => (CanonicalRecursiveSemantics.state sem H.proper n hA).section_supported
    hA (hp.toBelow (A, A.card)) ht
  agreement := fun hp ht hq htq =>
    (CanonicalRecursiveSemantics.state sem H.proper n hA).section_agreement
    hA (hp.toBelow (A, A.card)) ht (hq.toBelow (A, A.card)) htq

/-- Construct the operation on this raw boundary; derive the binary facets
from its actual plan, rather than requesting legal copies of those facets. -/
def build (k : ℕ) (hk : 0 < k) (hcard : A.card = k + 1) :
    OrdinaryScopeOperator.Core sem k := by
  let s := Classical.choose (exists_step D.isPlan (by omega : 2 ≤ A.card))
  have hplan := Classical.choose_spec (exists_step D.isPlan (by omega : 2 ≤ A.card))
  have hL := (OrdinaryPlanScopeStep.left_height s hcard).ge
  have hR := (OrdinaryPlanScopeStep.right_height s hcard).ge
  have hg := boundary_grade sem H hcard.le
  rcases k with _ | _ | _ | n
  · omega
  · exact one sem H s hplan.symm (by omega) hg hL hR
  · exact two sem H s hplan.symm (by omega) hg hL hR
  · exact higher sem H s hplan.symm n (by omega) hg hL hR

end

section Mute
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable {sem : Semantics D} {k : ℕ} (S : OrdinaryScopeOperator.Core sem k)

theorem completed_highest_row (hk : 0 < k) (hcard : A.card = k + 1)
    (c : Cell (S.finish hk hcard).carrier)
    (hc : (S.finish hk hcard).carrier.grade c = k + 1)
    (d : (S.finish hk hcard).carrier.below ((S.finish hk hcard).carrier.cell c)) :
    (S.finish hk hcard).rows.E c d = ⊥ := by
  rcases OrdinaryScopeMute.covered S.carrier k (k + 1) (Nat.lt_succ_self k) hcard.ge c with
    ⟨c, rfl⟩ | rfl
  · have he := congrArg Prod.snd
      (MaximalFullLayer.old_index S.carrier k (k + 1) (Nat.lt_succ_self k) hcard.ge c)
    have hg : S.carrier.grade c = k + 1 := he.symm.trans hc
    have := S.grade c
    omega
  · exact OrdinaryScopeMute.apex_row S.carrier S.rows k (k + 1) S.grade
      (Nat.lt_succ_self k) hcard.ge d

end Mute
end VaughtConjecture.Knight.OrdinaryRawScope
