/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PairedBoundarySections

/-! # Exact ordered grade cuts of the retained boundary

Grade restriction filters actual occurrences, not source values. Every lower
domain at a retained grade is unchanged, including all availability witnesses.
The point plan is retained; completeness at grades above the cut is not asserted.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GradeCutBoundary

open Transform Value ExtOrd
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (j : ℕ)

def inventory : Finset (Cell D) := Finset.univ.filter (fun d => D.grade d ≤ j)

def scheme : CellScheme A where
  plan := D.plan
  isPlan := D.isPlan
  card := (inventory D j).card
  cell c := D.cell ((inventory D j).orderEmbOfFin rfl c)
  cell_mem _c := D.cell_mem _

def toCell : Cell (scheme D j) ↪o Cell D := (inventory D j).orderEmbOfFin rfl

theorem cell_eq (d : Cell (scheme D j)) : (scheme D j).cell d = D.cell (toCell D j d) := rfl

theorem grade_bound (d : Cell (scheme D j)) : D.grade (toCell D j d) ≤ j :=
  (Finset.mem_filter.mp ((inventory D j).orderEmbOfFin_mem rfl d)).2

theorem exhaustive {d : Cell D} (hd : D.grade d ≤ j) : ∃ c, toCell D j c = d := by
  have hm : d ∈ Set.range ((inventory D j).orderEmbOfFin (k := (inventory D j).card) rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
  exact hm

def fromCell (d : Cell D) (hd : D.grade d ≤ j) : Cell (scheme D j) :=
  (exhaustive D j hd).choose

theorem to_from (d : Cell D) (hd : D.grade d ≤ j) :
    toCell D j (fromCell D j d hd) = d := (exhaustive D j hd).choose_spec

theorem from_to (d : Cell (scheme D j)) :
    fromCell D j (toCell D j d) (grade_bound D j d) = d :=
  (toCell D j).injective (to_from D j _ _)

def belowEquiv (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j) :
    (scheme D j).below BJ ≃ D.below BJ :=
  Equiv.ofBijective (fun d => ⟨toCell D j d.1, d.2⟩) ⟨by
    intro a b hab
    have he : toCell D j a.1 = toCell D j b.1 :=
      congrArg (fun z : D.below BJ => z.1) hab
    exact Subtype.ext ((toCell D j).injective he), by
    intro d
    obtain ⟨c, hc⟩ := exhaustive D j (d.2.2.trans hBJ)
    refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
    simpa only [cell_eq, hc] using d.2⟩

theorem belowEquiv_val (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j)
    (d : (scheme D j).below BJ) : (belowEquiv D j BJ hBJ d).1 = toCell D j d.1 := rfl

variable (sem : Semantics D)

def rows : Semantics (scheme D j) where
  E c d := sem.E (toCell D j c) (belowEquiv D j ((scheme D j).cell c) (grade_bound D j c) d)
  orderly c _d := sem.orderly (toCell D j c) _

theorem row_read (c : Cell (scheme D j)) (d : (scheme D j).below ((scheme D j).cell c)) :
    (rows D j sem).E c d =
      sem.E (toCell D j c) (belowEquiv D j ((scheme D j).cell c) (grade_bound D j c) d) := rfl

theorem respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j)
    (p : (scheme D j).below BJ → ExtOrd) :
    RespectsSemanticsBelow (rows D j sem) BJ p ↔
      RespectsSemanticsBelow sem BJ (p ∘ (belowEquiv D j BJ hBJ).symm) :=
  respects_iff_of_equiv (belowEquiv D j BJ hBJ) (fun _ => rfl) (fun _ _ => Iff.rfl)
    (fun _ _ _ => rfl) p

theorem pullback_respects {BJ : Finset ι × ℕ} (hBJ : BJ.2 ≤ j)
    {p : D.below BJ → ExtOrd} (hp : RespectsSemanticsBelow sem BJ p) :
    RespectsSemanticsBelow (rows D j sem) BJ (p ∘ belowEquiv D j BJ hBJ) := by
  apply (respects_iff D j sem BJ hBJ _).mpr
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hp

theorem restrict_respects {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    RespectsSemantics (rows D j sem) (fun d => p (toCell D j d)) := by
  have hr := pullback_respects D j sem le_rfl (hp.toBelow (A, j))
  exact hr.toRespects (fun d => ⟨D.isPlan.subset_of_mem (D.scope_mem_plan _), grade_bound D j d⟩)

theorem consistent (hs : sem.IsConsistent) : (rows D j sem).IsConsistent := by
  intro c
  exact pullback_respects D j sem (grade_bound D j c) (hs (toCell D j c))

theorem proper (hp : ∀ d : Cell D, D.scope d ≠ A) (d : Cell (scheme D j)) :
    (scheme D j).scope d ≠ A := hp (toCell D j d)

end
end VaughtConjecture.Knight.GradeCutBoundary
