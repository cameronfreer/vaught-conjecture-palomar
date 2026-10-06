/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveLifting
public import VaughtConjecture.Knight.SingleFaceTailRestoration
public import VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport
public import VaughtConjecture.Knight.GradeCutLifting

/-! # Predecessor-powered restoration on the actual recursive successor

The predecessor supplies the lower lift through exact occurrence and row
transport. The lower ambient is constructed, not supplied. Arbitrary distinct
lower labels, including top and upper-invisible values, remain literal.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveRestoration
open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan
open CanonicalRecursiveSuccessorRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))
abbrev LowerBountiful :=
  (GradeCutBoundary.rows (predecessor sem n hA) (n + 3) P.rows).IsBountiful
variable (hb : LowerBountiful sem n hA P) {C : Finset ι}
variable (hC : C ∈ D.plan) (hCc : n + 3 ≤ C.card)

include hb hC hCc in
theorem lower_clause : CappedLift (rows sem n hA hp P)
    (show GradedLe (C, n + 3) (A, n + 3) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  apply CanonicalRecursiveLifting.lower_lift sem n hA hp P _ le_rfl
  apply (GradeCutLifting.lift_iff P.rows (n + 3) _ le_rfl).mp
  apply lift_of_bountiful hb
  · change (C, n + 3) ∈ Plan.gradedPlan (predecessor sem n hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]
    exact Plan.mem_gradedPlan.mpr ⟨hC, by omega, hCc⟩
  · change (A, n + 3) ∈ Plan.gradedPlan (predecessor sem n hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]
    exact Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem, by omega, Nat.le_of_succ_le hA⟩

include hb hC hCc in
/-- Restore a constructed owner-capped lift. The capped lift is an internal
input to this composition lemma, not an assumed public active-branch result. -/
theorem restore
    {p : (carrier sem n hA).below (C, n + 4) → ExtOrd}
    (hpr : RespectsSemanticsBelow (rows sem n hA hp P) (C, n + 4) p)
    {u q : (carrier sem n hA).below (A, n + 4) → ExtOrd}
    (hu : RespectsSemanticsBelow (rows sem n hA hp P) (A, n + 4) u)
    {M γ : ExtOrd} (hM : SelfVis (n + 4) M) (hγM : γ ≤ M)
    (hread : ∀ e, u (CellScheme.below.mono
      (show GradedLe (C, n + 4) (A, n + 4) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) =
        min (p e) M)
    (hhigh : ∀ e : (carrier sem n hA).below (C, n + 4),
      (carrier sem n hA).grade e.1 = n + 4 → p e ≤ M)
    (hcap : ∀ d, min (u d) γ = min (q d) γ) :
    ∃ r : (carrier sem n hA).below (A, n + 4) → ExtOrd,
      RespectsSemanticsBelow (rows sem n hA hp P) (A, n + 4) r ∧
      (∀ e, r (CellScheme.below.mono
        (show GradedLe (C, n + 4) (A, n + 4) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) =
          p e) ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ d, n + 3 < (carrier sem n hA).grade d.1 → r d ≤ M := by
  obtain ⟨r, hr, hrlit, hrM, hrbound⟩ := SingleFaceTailRestoration.exists_restore
    (rows sem n hA hp P) (D.isPlan.subset_of_mem hC)
    (lower_clause sem n hA hp P hb hC hCc) hpr hu hM hread hhigh
  exact ⟨r, hr, hrlit, fun d =>
    (GradeTailRestoration.cap_below (hrM d) hγM).trans (hcap d), hrbound⟩

include hb hC hCc in
/-- Complete inactive branch, uniformly in the successor grade. No serving
controller, completion, or lawful lower ambient is an input. -/
theorem inactive
    {p : (carrier sem n hA).below (C, n + 4) → ExtOrd}
    (hpr : RespectsSemanticsBelow (rows sem n hA hp P) (C, n + 4) p)
    {q : (carrier sem n hA).below (A, n + 4) → ExtOrd}
    (hqr : RespectsSemanticsBelow (rows sem n hA hp P) (A, n + 4) q)
    {γ : ExtOrd} (hγ : SelfVis (n + 4) γ)
    (hag : ∀ e, min (q (CellScheme.below.mono
      (show GradedLe (C, n + 4) (A, n + 4) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e)) γ =
        min (p e) γ)
    (hhigh : ∀ e : (carrier sem n hA).below (C, n + 4),
      (carrier sem n hA).grade e.1 = n + 4 → p e ≤ γ) :
    ∃ r : (carrier sem n hA).below (A, n + 4) → ExtOrd,
      RespectsSemanticsBelow (rows sem n hA hp P) (A, n + 4) r ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ e, r (CellScheme.below.mono
        (show GradedLe (C, n + 4) (A, n + 4) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) =
          p e :=
  SingleFaceTailRestoration.exists_inactive (rows sem n hA hp P) (D.isPlan.subset_of_mem hC)
    (lower_clause sem n hA hp P hb hC hCc) hpr hqr hγ hag hhigh

end
end VaughtConjecture.Knight.CanonicalRecursiveRestoration
