/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ScopeReplicationCharts

/-! # The auxiliary part of mixed extension, with individual cap receipts

At each target auxiliary use the prescription's actual copy of the same
prototype at the prescribed mixed scope. Literal retention follows from
nested copy equality. For cap retention, compare both occurrences to their
common target-scope copy in the actual ambient. No field readout determines
an unused rung's value, and no hidden-original lawfulness is assumed.
This is the auxiliary part only, not a theorem of whole extension lawfulness.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ScopeReplicationAuxExtension
open AmalgamationPlan Transform Value ExtOrd ScopeReplicationCarrier ScopeReplicationSemantics
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (B C : Finset ι)
  (hcover : ∀ c : Cell D, D.scope c ≠ A → D.scope c ⊆ B ∨ D.scope c ⊆ C)
  (sem : Semantics D)

def replica {U : Finset ι} {j : ℕ} (hU : U ∈ D.plan)
    (hm : U = A ∨ Mixed B C U) (hj : j ≤ U.card)
    (c : Cell D) (hc : D.scope c = A) (hg : D.grade c ≤ j) :
    (scheme D B C).below (U, j) :=
  ⟨atScope D B C U hU hm c hc (hg.trans hj),
    (atScope_index D B C U hU hm c hc (hg.trans hj)) ▸ ⟨le_rfl, hg⟩⟩

theorem replica_index {U j} (hU : U ∈ D.plan) (hm : U = A ∨ Mixed B C U) (hj : j ≤ U.card)
    (c) (hc) (hg) :
    (scheme D B C).cell (replica D B C hU hm hj c hc hg).1 = (U, D.grade c) :=
  atScope_index D B C U hU hm c hc (hg.trans hj)

theorem erase_replica {U j} (hU : U ∈ D.plan) (hm : U = A ∨ Mixed B C U) (hj : j ≤ U.card)
    (c) (hc) (hg) : erase D B C (replica D B C hU hm hj c hc hg).1 = c :=
  erase_atScope D B C U hU hm c hc (hg.trans hj)

variable {U V : Finset ι} {j : ℕ}
  (hU : U ∈ D.plan) (hmU : U = A ∨ Mixed B C U) (hjU : j ≤ U.card)

def value (p : (scheme D B C).below (U, j) → ExtOrd)
    (z : (scheme D B C).below (V, j)) (hz : D.scope (erase D B C z.1) = A) : ExtOrd :=
  p (replica D B C hU hmU hjU (erase D B C z.1) hz
    ((erase_grade D B C z.1).le.trans z.2.2))

/-- Exact retention at each prescribed auxiliary, irrespective of its height. -/
theorem literal (p : (scheme D B C).below (U, j) → ExtOrd)
    (hp : RespectsSemanticsBelow (rows D B C hcover sem) (U, j) p)
    (hUV : U ⊆ V) (z : (scheme D B C).below (U, j))
    (hz : D.scope (erase D B C z.1) = A) :
    value D B C hU hmU hjU p
      (CellScheme.below.mono (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) z) hz = p z := by
  exact (copy_eq D B C hcover sem hp z
    (replica D B C hU hmU hjU (erase D B C z.1) hz
      ((erase_grade D B C z.1).le.trans z.2.2))
    (by
      change (scheme D B C).scope z.1 ⊆ ((scheme D B C).cell _).1
      rw [replica_index]; exact z.2.1)
    (erase_replica D B C hU hmU hjU _ _ _).symm).symm

/-- Any auxiliary under the target equals its own target-scope copy, in an
arbitrary lawful target-local section. -/
theorem eq_target_copy (hV : V ∈ D.plan) (hmV : V = A ∨ Mixed B C V) (hjV : j ≤ V.card)
    {q : (scheme D B C).below (V, j) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows D B C hcover sem) (V, j) q)
    (z : (scheme D B C).below (V, j)) (hz : D.scope (erase D B C z.1) = A) :
    q z = q (replica D B C hV hmV hjV (erase D B C z.1) hz
      ((erase_grade D B C z.1).le.trans z.2.2)) :=
  copy_eq D B C hcover sem hq z _
    (by
      change (scheme D B C).scope z.1 ⊆ ((scheme D B C).cell _).1
      rw [replica_index]; exact z.2.1)
    (erase_replica D B C hV hmV hjV _ _ _).symm

/-- Every auxiliary keeps its own old cap, including unused rungs and tips.
Only the actual prescription's cap equations and target lawfulness are used. -/
theorem cap (hV : V ∈ D.plan) (hmV : V = A ∨ Mixed B C V) (hjV : j ≤ V.card)
    (hUV : U ⊆ V) (p : (scheme D B C).below (U, j) → ExtOrd)
    {q : (scheme D B C).below (V, j) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows D B C hcover sem) (V, j) q)
    {γ : ExtOrd} (hag : ∀ d, min (q (CellScheme.below.mono
      (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) d)) γ = min (p d) γ)
    (z : (scheme D B C).below (V, j)) (hz : D.scope (erase D B C z.1) = A) :
    min (value D B C hU hmU hjU p z hz) γ = min (q z) γ := by
  let u := replica D B C hU hmU hjU (erase D B C z.1) hz
    ((erase_grade D B C z.1).le.trans z.2.2)
  let v := replica D B C hV hmV hjV (erase D B C z.1) hz
    ((erase_grade D B C z.1).le.trans z.2.2)
  let u' := CellScheme.below.mono (D := scheme D B C) (show GradedLe (U, j) (V, j)
    from ⟨hUV, le_rfl⟩) u
  have huq : q u' = q v := copy_eq D B C hcover sem hq u' v
    (by
      change ((scheme D B C).cell u.1).1 ⊆ ((scheme D B C).cell v.1).1
      rw [replica_index, replica_index]; exact hUV)
    ((erase_replica D B C hU hmU hjU (erase D B C z.1) hz
      ((erase_grade D B C z.1).le.trans z.2.2)).trans
      (erase_replica D B C hV hmV hjV (erase D B C z.1) hz
        ((erase_grade D B C z.1).le.trans z.2.2)).symm)
  have hzq : q z = q v := eq_target_copy D B C hcover sem hV hmV hjV hq z hz
  exact (hag u).symm.trans (congrArg (fun x => min x γ) (huq.trans hzq.symm))

end
end VaughtConjecture.Knight.ScopeReplicationAuxExtension
