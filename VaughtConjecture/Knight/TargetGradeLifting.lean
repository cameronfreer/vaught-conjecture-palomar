/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedLiftComposition
public import VaughtConjecture.Knight.SeparatedLayerFace
public import VaughtConjecture.Knight.SingleFaceTailRestoration
public import VaughtConjecture.Knight.GradeCutLifting

/-! # Target-grade induction for original-cap lifting

The induction ranges over all graded pairs on one actual carrier, including
scope-raising clauses. It is not a bountifulness assumption on an unfinished
output. Literal separated-layer transport supplies the lower clauses when a
successor is installed. Native repair and independent bottom supply remain
separate construction obligations.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.TargetGradeLifting
open Transform Value ExtOrd AmalgamationPlan CoatomBoundaryExtension
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D)

/-- Every valid pair up to a target grade; no completeness assertion is included. -/
def Through (r : ℕ) : Prop :=
  ∀ {I J : Finset ι × ℕ}, I ∈ Plan.gradedPlan D.plan →
    J ∈ Plan.gradedPlan D.plan → (h : GradedLe I J) → J.2 ≤ r → CappedLift sem h

theorem zero : Through sem 0 := by
  intro I J _ hJ _ hj
  exact False.elim ((not_lt_of_ge hj) (Plan.mem_gradedPlan.mp hJ).2.1)

/-- The successor ledger requires only the genuinely new same-grade clauses.
All lower-source grade changes are constructed using the lawful upper ambient. -/
theorem successor {r : ℕ} (hprev : Through sem r)
    (hnext : ∀ (C B : Finset ι), (C, r + 1) ∈ Plan.gradedPlan D.plan →
      (B, r + 1) ∈ Plan.gradedPlan D.plan → (h : C ⊆ B) →
      CappedLift sem (show GradedLe (C, r + 1) (B, r + 1) from ⟨h, le_rfl⟩)) :
    Through sem (r + 1) := by
  rintro ⟨C, i⟩ ⟨B, j⟩ hC hB h hj
  by_cases hi : i ≤ r
  · have hBi : (B, i) ∈ Plan.gradedPlan D.plan := Plan.mem_gradedPlan.mpr
      ⟨(Plan.mem_gradedPlan.mp hB).1, (Plan.mem_gradedPlan.mp hC).2.1,
        h.2.trans (Plan.mem_gradedPlan.mp hB).2.2⟩
    exact (hprev hC hBi (show GradedLe (C, i) (B, i) from ⟨h.1, le_rfl⟩) hi).raise_target
      (h := h.1) h.2
  · have hi' : i = r + 1 := by have := h.2; dsimp only at hj this; omega
    have hj' : j = r + 1 := by have := h.2; dsimp only at hj this; omega
    subst i; subst j
    exact hnext C B hC hB h.1

/-- Restore lower labels above the owner from the already proved target-grade
induction hypothesis. The lower ambient is constructed by the splice theorem.
The lawful owner-capped repair is an internal composition input, not a claim
that its source producer has been supplied. -/
theorem restore {C B : Finset ι} {j : ℕ} (hprev : Through sem j)
    (hC : (C, j) ∈ Plan.gradedPlan D.plan) (hB : (B, j) ∈ Plan.gradedPlan D.plan)
    (hCB : C ⊆ B)
    {p : D.below (C, j + 1) → ExtOrd} {u q : D.below (B, j + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (C, j + 1) p)
    (hu : RespectsSemanticsBelow sem (B, j + 1) u)
    {M γ : ExtOrd} (hM : SelfVis (j + 1) M) (hγM : γ ≤ M)
    (hread : ∀ d, u (CellScheme.below.mono
      (show GradedLe (C, j + 1) (B, j + 1) from ⟨hCB, le_rfl⟩) d) = min (p d) M)
    (hmax : ∀ d : D.below (C, j + 1), D.grade d.1 = j + 1 → p d ≤ M)
    (hcap : ∀ d, min (u d) γ = min (q d) γ) :
    ∃ r, RespectsSemanticsBelow sem (B, j + 1) r ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ d, r (CellScheme.below.mono
        (show GradedLe (C, j + 1) (B, j + 1) from ⟨hCB, le_rfl⟩) d) = p d := by
  obtain ⟨r, hr, hread', hcap', _⟩ := SingleFaceTailRestoration.exists_restore sem hCB
    (hprev hC hB ⟨hCB, le_rfl⟩ le_rfl) hp hu hM hread hmax
  exact ⟨r, hr, fun d => (GradeTailRestoration.cap_below (hcap' d) hγM).trans (hcap d), hread'⟩

/-- The induction invariant gives bountifulness of the actual grade-cut
semantics, not of the unfilled full carrier. The cut retains the point plan;
this statement does not add missing higher owners. -/
theorem gradeCut_bountiful {r : ℕ} (hr : 0 < r) (hprev : Through sem r) :
    (GradeCutBoundary.rows D r sem).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (fun d => GradeCutBoundary.grade_bound D r d) hr
  intro C B i hC hB hi hCB
  apply (GradeCutLifting.lift_iff sem r
    (show GradedLe (C, i) (B, i) from ⟨hCB, le_rfl⟩) hi).mpr
  exact hprev hC hB ⟨hCB, le_rfl⟩ hi

section Transport
variable (Q : Type*) [Fintype Q] (k : ℕ) (hk : 0 < k) (hA : k ≤ A.card)
  (hs : ∀ d : Cell D, ¬ GradedLe (A, k) (D.cell d))
  (out : Semantics (SourceLayerCarrier.scheme D Q k hk hA))
  (hrow : ∀ (c : Cell D) (d : D.below (D.cell c)),
    out.E (SourceLayerCarrier.toCell D Q k hk hA (.inl c))
      (SeparatedSourceLayerCarrier.ownerEquiv D Q k hk hA hs c d) = sem.E c d)

include hrow in
/-- Transfer the complete lower induction invariant through literal installation.
Retained proper owners may be above the new grade; only full-scope separation
is used. The generic row premise must be discharged by the concrete installer. -/
theorem through_separated {r : ℕ} (hrk : r < k) (hprev : Through sem r) :
    Through out r := by
  intro I J hI hJ h hj
  apply SeparatedLayerFace.lift D Q k hk hA hs sem out hrow h
    (fun hn => (not_le_of_gt hrk) (hn.2.trans hj))
  exact hprev hI hJ h hj
end Transport

end
end VaughtConjecture.Knight.TargetGradeLifting
