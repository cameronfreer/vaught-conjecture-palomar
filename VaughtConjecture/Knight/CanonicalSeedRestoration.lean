/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSeedLifting
public import VaughtConjecture.Knight.SingleFaceTailRestoration
public import VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport
public import VaughtConjecture.Knight.GradeCutLifting

/-! # Predecessor-powered restoration on the actual recursive seed

The predecessor supplies the lower lift through exact occurrence and row
transport. The lower ambient is constructed, not supplied. Arbitrary distinct
lower labels, including top and upper-invisible values, remain literal.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalSeedRestoration
open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan
open CanonicalRecursiveSeedRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)
abbrev LowerBountiful :=
  (GradeCutBoundary.rows (predecessor sem hA) 2 (predecessorRows sem hA hp)).IsBountiful
variable (hb : LowerBountiful sem hA hp) {C : Finset ι}
variable (hC : C ∈ D.plan) (hCc : 2 ≤ C.card)

include hb hC hCc in
theorem lower_clause : CappedLift (rows sem hA hp)
    (show GradedLe (C, 2) (A, 2) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  apply CanonicalSeedLifting.lower_lift sem hA hp _ le_rfl
  apply (GradeCutLifting.lift_iff (predecessorRows sem hA hp) 2 _ le_rfl).mp
  apply lift_of_bountiful hb
  · change (C, 2) ∈ Plan.gradedPlan D.plan
    exact Plan.mem_gradedPlan.mpr ⟨hC, (by decide : 0 < 2), hCc⟩
  · change (A, 2) ∈ Plan.gradedPlan D.plan
    exact Plan.mem_gradedPlan.mpr
      ⟨D.isPlan.domain_mem, (by decide : 0 < 2), Nat.le_of_succ_le hA⟩

include hb hC hCc in
/-- Restore a constructed owner-capped lift. The capped lift is an internal
input to this composition lemma, not an assumed public active-branch result. -/
theorem restore
    {p : (carrier sem hA).below (C, 3) → ExtOrd}
    (hpr : RespectsSemanticsBelow (rows sem hA hp) (C, 3) p)
    {u q : (carrier sem hA).below (A, 3) → ExtOrd}
    (hu : RespectsSemanticsBelow (rows sem hA hp) (A, 3) u)
    {M γ : ExtOrd} (hM : SelfVis 3 M) (hγM : γ ≤ M)
    (hread : ∀ e, u (CellScheme.below.mono
      (show GradedLe (C, 3) (A, 3) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) =
        min (p e) M)
    (hhigh : ∀ e : (carrier sem hA).below (C, 3),
      (carrier sem hA).grade e.1 = 3 → p e ≤ M)
    (hcap : ∀ d, min (u d) γ = min (q d) γ) :
    ∃ r : (carrier sem hA).below (A, 3) → ExtOrd,
      RespectsSemanticsBelow (rows sem hA hp) (A, 3) r ∧
      (∀ e, r (CellScheme.below.mono
        (show GradedLe (C, 3) (A, 3) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) =
          p e) ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ d, 2 < (carrier sem hA).grade d.1 → r d ≤ M := by
  obtain ⟨r, hr, hrlit, hrM, hrbound⟩ := SingleFaceTailRestoration.exists_restore
    (rows sem hA hp) (D.isPlan.subset_of_mem hC)
    (lower_clause sem hA hp hb hC hCc) hpr hu hM hread hhigh
  exact ⟨r, hr, hrlit, fun d =>
    (GradeTailRestoration.cap_below (hrM d) hγM).trans (hcap d), hrbound⟩

include hb hC hCc in
/-- Complete inactive branch, uniformly in the successor grade. No serving
controller, completion, or lawful lower ambient is an input. -/
theorem inactive
    {p : (carrier sem hA).below (C, 3) → ExtOrd}
    (hpr : RespectsSemanticsBelow (rows sem hA hp) (C, 3) p)
    {q : (carrier sem hA).below (A, 3) → ExtOrd}
    (hqr : RespectsSemanticsBelow (rows sem hA hp) (A, 3) q)
    {γ : ExtOrd} (hγ : SelfVis 3 γ)
    (hag : ∀ e, min (q (CellScheme.below.mono
      (show GradedLe (C, 3) (A, 3) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e)) γ =
        min (p e) γ)
    (hhigh : ∀ e : (carrier sem hA).below (C, 3),
      (carrier sem hA).grade e.1 = 3 → p e ≤ γ) :
    ∃ r : (carrier sem hA).below (A, 3) → ExtOrd,
      RespectsSemanticsBelow (rows sem hA hp) (A, 3) r ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ e, r (CellScheme.below.mono
        (show GradedLe (C, 3) (A, 3) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) =
          p e :=
  SingleFaceTailRestoration.exists_inactive (rows sem hA hp) (D.isPlan.subset_of_mem hC)
    (lower_clause sem hA hp hb hC hCc) hpr hqr hγ hag hhigh

end
end VaughtConjecture.Knight.CanonicalSeedRestoration
