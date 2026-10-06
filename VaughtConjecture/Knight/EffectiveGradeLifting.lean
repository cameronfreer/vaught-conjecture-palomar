/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoatomBoundaryExtension
public import VaughtConjecture.Knight.SameScopeBountiful
public import VaughtConjecture.Knight.PartialSections

/-! # Exhaustive lifting reduction at the actual grade ceiling

Clamping a nominal grade loses no occurrence when all actual grades are
bounded. The original cap is retained, using visibility only downwards.
Same-scope grade changes then reduce the ledger to same-grade pairs.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.EffectiveGradeLifting
open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable {sem : Semantics D} {K : ℕ} (hK : ∀ d : Cell D, D.grade d ≤ K)

def cut (J : Finset ι × ℕ) : Finset ι × ℕ := (J.1, min J.2 K)

def equiv (J : Finset ι × ℕ) : D.below (cut (K := K) J) ≃ D.below J where
  toFun d := ⟨d.1, d.2.1, (le_min_iff.mp d.2.2).1⟩
  invFun d := ⟨d.1, d.2.1, le_min d.2.2 (hK d.1)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem respects_iff (J : Finset ι × ℕ) (p : D.below (cut (K := K) J) → ExtOrd) :
    RespectsSemanticsBelow sem (cut (K := K) J) p ↔
      RespectsSemanticsBelow sem J (p ∘ (equiv hK J).symm) :=
  respects_iff_of_equiv (equiv hK J) (fun _ => rfl) (fun _ _ => Iff.rfl)
    (fun _ _ _ => rfl) p

theorem pullback_respects {J : Finset ι × ℕ} {q : D.below J → ExtOrd}
    (hq : RespectsSemanticsBelow sem J q) :
    RespectsSemanticsBelow sem (cut (K := K) J) (q ∘ equiv hK J) := by
  apply (respects_iff hK J _).mpr
  exact hq

omit [DecidableEq ι] in
theorem cut_le {I J : Finset ι × ℕ} (h : GradedLe I J) :
    GradedLe (cut (K := K) I) (cut (K := K) J) :=
  ⟨h.1, min_le_min_right K h.2⟩

include hK in
/-- Transfer the actual capped lift, not just section existence. -/
theorem lift {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hl : CappedLift sem (cut_le (K := K) h)) : CappedLift sem h := by
  apply CappedLift.of_equiv (equiv hK I) (equiv hK J) (fun _ => rfl)
    (min_le_left _ _) (fun _ hp => pullback_respects hK hp) _ hl
  intro q
  exact ⟨fun hq => pullback_respects hK hq, fun hq => by
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using (respects_iff hK J _).mp hq⟩

/-- Every literal graded pair follows from same-grade pairs, without
completeness or a hypothesis about an already extended ambient. -/
theorem bountiful_of_same_grade
    (hsame : ∀ (C B : Finset ι) (i : ℕ), (C, i) ∈ Plan.gradedPlan D.plan →
      (B, i) ∈ Plan.gradedPlan D.plan → (h : C ⊆ B) →
      CappedLift sem (show GradedLe (C, i) (B, i) from ⟨h, le_rfl⟩)) :
    sem.IsBountiful := by
  rintro ⟨C, i⟩ ⟨B, j⟩ hCI hBJ h _
  have hBi : (B, i) ∈ Plan.gradedPlan D.plan := Plan.mem_gradedPlan.mpr
    ⟨(Plan.mem_gradedPlan.mp hBJ).1, (Plan.mem_gradedPlan.mp hCI).2.1,
      h.2.trans (Plan.mem_gradedPlan.mp hBJ).2.2⟩
  let hi : GradedLe (C, i) (B, i) := ⟨h.1, le_rfl⟩
  let hj : GradedLe (B, i) (B, j) := ⟨Finset.Subset.refl _, h.2⟩
  exact CappedLift.comp (hIJ := hi) (hJK := hj) (hsame C B i hCI hBi h.1)
    (bountiful_same_scope sem hj)

include hK in
/-- Only the nonempty effective grades need separate lifting proofs. -/
theorem bountiful_of_bounded_same_grade (hpos : 0 < K)
    (hsame : ∀ (C B : Finset ι) (i : ℕ), (C, i) ∈ Plan.gradedPlan D.plan →
      (B, i) ∈ Plan.gradedPlan D.plan → i ≤ K → (h : C ⊆ B) →
      CappedLift sem (show GradedLe (C, i) (B, i) from ⟨h, le_rfl⟩)) :
    sem.IsBountiful := by
  apply bountiful_of_same_grade
  intro C B i hC hB h
  apply lift hK
  have mem (S : Finset ι) (hm : (S, i) ∈ Plan.gradedPlan D.plan) :
      (S, min i K) ∈ Plan.gradedPlan D.plan := by
    obtain ⟨hs, hi, hc⟩ := Plan.mem_gradedPlan.mp hm
    exact Plan.mem_gradedPlan.mpr ⟨hs, lt_min hi hpos, (min_le_left _ _).trans hc⟩
  exact hsame C B (min i K) (mem C hC) (mem B hB) (min_le_right _ _) h

end VaughtConjecture.Knight.EffectiveGradeLifting
