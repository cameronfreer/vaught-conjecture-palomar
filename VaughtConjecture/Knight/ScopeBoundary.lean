/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutBoundary

/-! # Literal restriction to a point scope without changing point names

This restriction keeps the actual ordered occurrences whose supports lie in
`B`. Every retained owner's entire lower domain is preserved. It is used before
installing a full-scope source layer on a proper mixed scope of a larger carrier.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ScopeBoundary
open AmalgamationPlan Transform Value ExtOrd
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (B : Finset ι) (hB : B ∈ D.plan)

def inventory : Finset (Cell D) := Finset.univ.filter (fun d => D.scope d ⊆ B)

def scheme : CellScheme B where
  plan := Plan.restrictPlan D.plan B
  isPlan := Plan.restrict_isPlan D.isPlan hB
  card := (inventory D B).card
  cell c := D.cell ((inventory D B).orderEmbOfFin rfl c)
  cell_mem c := by
    obtain ⟨hs, hk, hc⟩ := Plan.mem_gradedPlan.mp
      (D.cell_mem ((inventory D B).orderEmbOfFin rfl c))
    exact Plan.mem_gradedPlan.mpr ⟨Finset.mem_inter.mpr
      ⟨hs, Finset.mem_powerset.mpr
        (Finset.mem_filter.mp ((inventory D B).orderEmbOfFin_mem rfl c)).2⟩, hk, hc⟩

def toCell : Cell (scheme D B hB) ↪o Cell D := (inventory D B).orderEmbOfFin rfl

theorem cell_eq (d : Cell (scheme D B hB)) :
    (scheme D B hB).cell d = D.cell (toCell D B hB d) := rfl

theorem scope_bound (d : Cell (scheme D B hB)) : D.scope (toCell D B hB d) ⊆ B :=
  (Finset.mem_filter.mp ((inventory D B).orderEmbOfFin_mem rfl d)).2

theorem exhaustive {d : Cell D} (hd : D.scope d ⊆ B) : ∃ c, toCell D B hB c = d := by
  have hm : d ∈ Set.range ((inventory D B).orderEmbOfFin (k := (inventory D B).card) rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
  exact hm

def belowEquiv (BJ : Finset ι × ℕ) (hBJ : BJ.1 ⊆ B) :
    (scheme D B hB).below BJ ≃ D.below BJ :=
  Equiv.ofBijective (fun d => ⟨toCell D B hB d.1, d.2⟩) ⟨by
    intro a b hab
    exact Subtype.ext ((toCell D B hB).injective
      (congrArg (fun z : D.below BJ => z.1) hab)), by
    intro d
    obtain ⟨c, hc⟩ := exhaustive D B hB (d.2.1.trans hBJ)
    refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
    simpa only [cell_eq, hc] using d.2⟩

variable (sem : Semantics D)

def rows : Semantics (scheme D B hB) where
  E c d := sem.E (toCell D B hB c)
    (belowEquiv D B hB ((scheme D B hB).cell c) (scope_bound D B hB c) d)
  orderly c _d := sem.orderly (toCell D B hB c) _

theorem row_read (c : Cell (scheme D B hB))
    (d : (scheme D B hB).below ((scheme D B hB).cell c)) :
    (rows D B hB sem).E c d = sem.E (toCell D B hB c)
      (belowEquiv D B hB ((scheme D B hB).cell c) (scope_bound D B hB c) d) := rfl

theorem respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.1 ⊆ B)
    (p : (scheme D B hB).below BJ → ExtOrd) :
    RespectsSemanticsBelow (rows D B hB sem) BJ p ↔
      RespectsSemanticsBelow sem BJ (p ∘ (belowEquiv D B hB BJ hBJ).symm) :=
  respects_iff_of_equiv (belowEquiv D B hB BJ hBJ) (fun _ => rfl) (fun _ _ => Iff.rfl)
    (fun _ _ _ => rfl) p

theorem pullback_respects {BJ : Finset ι × ℕ} (hBJ : BJ.1 ⊆ B)
    {p : D.below BJ → ExtOrd} (hp : RespectsSemanticsBelow sem BJ p) :
    RespectsSemanticsBelow (rows D B hB sem) BJ (p ∘ belowEquiv D B hB BJ hBJ) := by
  apply (respects_iff D B hB sem BJ hBJ _).mpr
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hp

theorem consistent (hs : sem.IsConsistent) : (rows D B hB sem).IsConsistent := by
  intro c
  exact pullback_respects D B hB sem (scope_bound D B hB c) (hs (toCell D B hB c))

theorem coded (hs : sem.IsCoded) : (rows D B hB sem).IsCoded := fun _ _ => hs _ _

end
end VaughtConjecture.Knight.ScopeBoundary
