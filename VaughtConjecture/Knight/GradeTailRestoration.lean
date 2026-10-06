/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeSplice
public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.WitnessSplice

/-! # Restoring a lower grade under a bounded upper tail

The splice theorem uses an actual lower-domain section, not bountifulness of
the whole output. The second theorem constructs such a section by a faithful
raise. This construction restores one common saturated lower value; it does
not split distinct values that an earlier clipping identified.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GradeTailRestoration
open Transform Value ExtOrd SharpWitnessComposition
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable {sem : Semantics D} {BJ : Finset ι × ℕ} {j : ℕ}

/-- The explicit raising map fixes every value below `M`, and preserves the
`M`-cap of every input, including literal top. -/
theorem raise_cap {ξ : Ordinal.{0}} {L x : ExtOrd} :
    min (raiseShifter id ξ L x) (ofOrd ξ) = min x (ofOrd ξ) := by
  by_cases h : x < ofOrd ξ
  · rw [raiseShifter_of_lt h]; rfl
  · have hx : ofOrd ξ ≤ x := not_lt.mp h
    rw [min_eq_right hx, min_eq_right (hx.trans (le_raiseShifter id ξ L x))]

/-- Construct a lawful lower section and splice it into a bounded upper tail.
Clause 5 is supplied by `Witness.raise`; positive-cap transport handles long
semantic rows without composing faithful transformations. -/
theorem raise_lower_respects (hj : j ≤ BJ.2) {u : D.below BJ → ExtOrd}
    (hu : RespectsSemanticsBelow sem BJ u) {ξ : Ordinal.{0}} {L : ExtOrd}
    (hξ : j < finitePart ξ) (hL : SelfVis j L)
    (hbound : ∀ d, j < D.grade d.1 → u d ≤ ofOrd ξ) :
    RespectsSemanticsBelow sem BJ
      (splice u (fun d => raiseShifter id ξ L (u (lowerIncl hj d)))) := by
  have hl := hu.mono (show GradedLe (BJ.1, j) BJ from ⟨Finset.Subset.refl _, hj⟩)
  have hw := (witness_id j).raise j (fun _ h => gTop_of_gt h) hξ hL
  apply splice_respects hj hu _ hbound (fun _ => raise_cap)
  exact map_respects_of_positive_cap_agreement hl hl (fun d => d.2.2)
    (boundedMap_of_witness hw) (ofOrd_ne_bot ξ) (fun _ => raise_cap)

/-- Literal readback for one saturated value. Values strictly below the
restoration cap stay literal, while the common value `L` may be proper or top.
In particular `L` need not be visible at any of the upper grades. -/
theorem raise_readback {ξ : Ordinal.{0}} {L x : ExtOrd} (hML : ofOrd ξ ≤ L)
    (hx : x < ofOrd ξ ∨ x = L) :
    raiseShifter id ξ L (min x (ofOrd ξ)) = x := by
  rcases hx with hx | rfl
  · rw [min_eq_left hx.le, raiseShifter_of_lt hx]; rfl
  · rw [min_eq_right hML, raiseShifter_of_ge le_rfl (ofOrd_ne_bot ξ)]
    exact max_eq_right hML

/-- A constructed restoration theorem, not an assumed lower-layer lift.
The explicit restriction is one common saturated low value. Distinct lower
values above the cap require a stronger lower-layer completion theorem. -/
theorem exists_single_class_restoration (hj : j ≤ BJ.2)
    {u : D.below BJ → ExtOrd} (hu : RespectsSemanticsBelow sem BJ u)
    {ξ : Ordinal.{0}} {L : ExtOrd} (hM : SelfVis BJ.2 (ofOrd ξ))
    (hξ : j < finitePart ξ) (hL : SelfVis j L) (hML : ofOrd ξ ≤ L)
    {X : Type*} (f : X → D.below BJ) (p : X → ExtOrd)
    (hread : ∀ e, u (f e) = min (p e) (ofOrd ξ))
    (hlow : ∀ e, D.grade (f e).1 ≤ j → p e < ofOrd ξ ∨ p e = L)
    (hhigh : ∀ e, j < D.grade (f e).1 → p e ≤ ofOrd ξ) :
    ∃ r : D.below BJ → ExtOrd,
      RespectsSemanticsBelow sem BJ r ∧ (∀ e, r (f e) = p e) ∧
      (∀ d, min (r d) (ofOrd ξ) = min (u d) (ofOrd ξ)) ∧
      (∀ d, j < D.grade d.1 → r d ≤ ofOrd ξ) := by
  let v : D.below BJ → ExtOrd := fun d => min (u d) (ofOrd ξ)
  let w : D.below (BJ.1, j) → ExtOrd :=
    fun d => raiseShifter id ξ L (v (lowerIncl hj d))
  have hv : RespectsSemanticsBelow sem BJ v := hu.cap hM
  have hr := raise_lower_respects hj hv hξ hL (fun d _ => min_le_right _ _)
  refine ⟨splice v w, hr, ?_, ?_, ?_⟩
  · intro e
    by_cases he : D.grade (f e).1 ≤ j
    · rw [splice_low v w (f e) he]
      change raiseShifter id ξ L (min (u (f e)) (ofOrd ξ)) = p e
      rw [hread, min_assoc, min_self]
      exact raise_readback hML (hlow e he)
    · rw [splice_high v w (f e) he]
      change min (u (f e)) (ofOrd ξ) = p e
      rw [hread, min_assoc, min_self, min_eq_left (hhigh e (not_le.mp he))]
  · intro d
    exact (splice_cap hj (u := v) (v := w) (fun _ => raise_cap) d).trans
      (by dsimp only [v]; rw [min_assoc, min_self])
  · intro d hd
    rw [splice_high v w d (not_le.mpr hd)]
    exact min_le_right _ _

/-- A scalar map cannot undo identification of two distinct values by clipping.
This rejects that restoration recipe, not semantic lifting on a carrier. -/
theorem no_scalar_split {M x y : ExtOrd} (hx : M ≤ x) (hy : M ≤ y) (hne : x ≠ y) :
    ¬ ∃ σ : ExtOrd → ExtOrd, σ (min x M) = x ∧ σ (min y M) = y := by
  rintro ⟨σ, hσx, hσy⟩
  rw [min_eq_right hx] at hσx
  rw [min_eq_right hy] at hσy
  exact hne (hσx.symm.trans hσy)

end
end VaughtConjecture.Knight.GradeTailRestoration
