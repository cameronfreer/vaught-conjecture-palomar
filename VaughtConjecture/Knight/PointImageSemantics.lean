/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AmalgamatedBoundaryRows

/-! # Literal semantics under an injective change of point domain

Changing the point domain leaves the occurrence enumeration and every row
value unchanged. The lower-domain equivalences transport consistency and
coding without changing labels or composing transformations.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.PointImageSemantics

open AmalgamationPlan Transform Value ExtOrd AmalgamatedBoundary

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {B : Finset ι} {C : Finset κ} (D : CellScheme B) (e : ι ↪ κ)
variable (he : B.image e = C) (sem : Semantics D)

local notation "K" => pointImage D e he

theorem below_iff (d c : Cell D) :
    GradedLe ((K).cell d) ((K).cell c) ↔ GradedLe (D.cell d) (D.cell c) := by
  change ((D.scope d).image e ⊆ (D.scope c).image e ∧ D.grade d ≤ D.grade c) ↔ _
  rw [Finset.image_subset_image_iff e.injective]
  rfl

def belowEquiv (c : Cell D) : D.below (D.cell c) ≃ (K).below ((K).cell c) where
  toFun d := ⟨d.1, (below_iff D e he d.1 c).mpr d.2⟩
  invFun d := ⟨d.1, (below_iff D e he d.1 c).mp d.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rows : Semantics K where
  E c d := sem.E c ((belowEquiv D e he c).symm d)
  orderly c d := sem.orderly c ((belowEquiv D e he c).symm d)

theorem row (c : Cell D) (d : D.below (D.cell c)) :
    (rows D e he sem).E c (belowEquiv D e he c d) = sem.E c d := by
  change sem.E c ((belowEquiv D e he c).symm (belowEquiv D e he c d)) = _
  rw [Equiv.symm_apply_apply]

theorem consistent (hc : sem.IsConsistent) : (rows D e he sem).IsConsistent := by
  intro c
  exact RespectsSemanticsBelow.of_equiv (sem := sem) (sem' := rows D e he sem)
    (belowEquiv D e he c).symm (fun _ => rfl)
    (fun _ _ => Finset.image_subset_image_iff e.injective) (fun _ _ _ => rfl) (hc c)

theorem coded (hc : sem.IsCoded) : (rows D e he sem).IsCoded := by
  intro c d
  exact hc c ((belowEquiv D e he c).symm d)

theorem total_eq (c d : Cell D) :
    AmalgamatedBoundaryRows.total (rows D e he sem) c d =
      AmalgamatedBoundaryRows.total sem c d := by
  classical
  by_cases h : GradedLe (D.cell d) (D.cell c)
  · have hh := (below_iff D e he d c).mpr h
    exact (AmalgamatedBoundaryRows.total_below (rows D e he sem) c ⟨d, hh⟩).trans
      (AmalgamatedBoundaryRows.total_below sem c ⟨d, h⟩).symm
  · rw [AmalgamatedBoundaryRows.total_outside _ _ _
      (fun hh => h ((below_iff D e he d c).mp hh)),
      AmalgamatedBoundaryRows.total_outside _ _ _ h]

/-- Whole labellings remain literal under the point-domain change. -/
theorem respects_iff (p : Cell D → ExtOrd) :
    RespectsSemantics (rows D e he sem) p ↔ RespectsSemantics sem p := by
  constructor
  · intro hp
    refine ⟨hp.orderly, ?_, ?_⟩
    · intro c
      have h := (hp.locality c).reindex (belowEquiv D e he c)
      exact transformsTo_congr rfl (by funext d; exact row D e he sem c d) rfl h
    · intro c d hs hg
      obtain ⟨z, hz, hle⟩ := hp.availability c d (Finset.image_subset_image hs) hg
      refine ⟨z, ?_, hle⟩
      apply Prod.ext
      · exact Finset.image_injective e.injective (congrArg Prod.fst hz)
      · exact congrArg (fun x : Finset κ × ℕ => x.2) hz
  · intro hp
    refine ⟨hp.orderly, ?_, ?_⟩
    · intro c
      exact (hp.locality c).reindex (belowEquiv D e he c).symm
    · intro c d hs hg
      obtain ⟨z, hz, hle⟩ := hp.availability c d
        ((Finset.image_subset_image_iff e.injective).mp hs) hg
      refine ⟨z, ?_, hle⟩
      exact Prod.ext (congrArg (Finset.image e) (congrArg Prod.fst hz))
        (congrArg (fun x : Finset ι × ℕ => x.2) hz)

end VaughtConjecture.Knight.PointImageSemantics
