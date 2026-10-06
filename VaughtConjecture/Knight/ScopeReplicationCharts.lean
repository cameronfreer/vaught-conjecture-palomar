/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ScopeReplicationSemantics
public import VaughtConjecture.Knight.AmbientGradeCharts

/-! # Maximal charts directly on a mixed lower domain

No whole-section extension is used. An actual chart at a mixed index has a
full-scope prototype, and reads the original prototype row through erasure.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ScopeReplicationCharts
open AmalgamationPlan Transform Value ExtOrd ScopeReplicationCarrier
open ScopeReplicationSemantics AmbientGradeCharts
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (B C : Finset ι)
  (hcover : ∀ c : Cell D, D.scope c ≠ A → D.scope c ⊆ B ∨ D.scope c ⊆ C)
  (sem : Semantics D)

include hcover in
theorem erase_index {U : Finset ι} {j : ℕ} (hm : U = A ∨ Mixed B C U)
    (c : Cell (scheme D B C)) (hc : (scheme D B C).cell c = (U, j)) :
    D.cell (erase D B C c) = (A, j) := by
  apply Prod.ext
  · change D.scope (erase D B C c) = A
    by_contra hne
    have hs : D.scope (erase D B C c) = U :=
      (erase_scope_of_ne D B C c hne).trans (congrArg Prod.fst hc)
    rcases hm with rfl | hm
    · exact hne hs
    · rcases hcover _ hne with hb | hc'
      · exact hm.1 (hs ▸ hb)
      · exact hm.2 (hs ▸ hc')
  · change D.grade (erase D B C c) = j
    exact (erase_grade D B C c).trans (congrArg Prod.snd hc)

theorem exists_chart {U : Finset ι} {j : ℕ}
    (hU : U ∈ D.plan) (hm : U = A ∨ Mixed B C U) (hj : j ≤ U.card)
    (c : Cell D) (hc : D.cell c = (A, j))
    {p : (scheme D B C).below (U, j) → ExtOrd}
    (hp : RespectsSemanticsBelow (rows D B C hcover sem) (U, j) p) :
    Nonempty (Chart (rows D B C hcover sem) (U, j) p j) := by
  let d := atScope D B C U hU hm c (congrArg Prod.fst hc)
    ((congrArg Prod.snd hc).le.trans hj)
  have hd : (scheme D B C).cell d = (U, j) :=
    (atScope_index D B C U hU hm c _ _).trans
      (by rw [show D.grade c = j from congrArg Prod.snd hc])
  exact AmbientGradeCharts.exists_chart hp ⟨⟨d, hd ▸ GradedLe.refl _⟩, hd⟩

variable {U : Finset ι} {j : ℕ} {p : (scheme D B C).below (U, j) → ExtOrd}
  (Ch : Chart (rows D B C hcover sem) (U, j) p j)

theorem chart_prototype_index (hm : U = A ∨ Mixed B C U) :
    D.cell (erase D B C Ch.owner.1) = (A, j) :=
  erase_index D B C hcover hm Ch.owner.1 Ch.index

/-- Read the original row on the actual mixed domain; no missing original
coordinate is assigned a value or assumed lawful. -/
theorem read_erased (d : (scheme D B C).below (U, j)) :
    Ch.shift (sem.E (erase D B C Ch.owner.1)
      (belowErase D B C hcover Ch.owner.1 (Ch.occurrence d d.2.2))) =
      min (p d) (p Ch.owner) :=
  Ch.read_capped d d.2.2

end
end VaughtConjecture.Knight.ScopeReplicationCharts
