/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.OrbitBlock
public import VaughtConjecture.Knight.CoupledGradeOne
public import VaughtConjecture.Knight.RelativeLiftData
public import VaughtConjecture.Knight.GradeTwoCodedBountiful

/-! # The common visible positive floor, and bottom-reflecting transport on long rows

The reviewer's notes5 (`plan13.md` §2, 2026-09-18).  For a nonbottom `K`-visible `w`, the
**positive floor** `F_w x = ⊥` if `x = ⊥`, `max x w` otherwise, is a bottom-reflecting
normalized grade-`K` witness (`witness_positiveFloor`): replacement at any grade at most `K`
commutes with it (`positiveFloor_evr`), because replacement is monotone and fixes `w`.  The
visibility of `w` at `K` is what makes one common floor respect every active grade below `K`;
a floor visible only at a lower grade would not.

**Transport on unchanged long rows** (`map_respects_of_bottom_reflecting`,
`positiveFloor_respects`): a bounded replacement-commuting, bottom-reflecting scalar image of a
lawful section is lawful — from the ported source-block theorem
`map_respects_iff_rowBlockBottom`, since a bottom-reflecting map preserves the row-block bottom
law.  No source-shortness is assumed.  Also `flat_section`: replacing every positive value of a
lawful section by one `K`-visible `w` is lawful (a cap at a visible value).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-! ## The floor -/

/-- The positive floor at `w`. -/
noncomputable def positiveFloor (w x : ExtOrd) : ExtOrd := if x = ⊥ then ⊥ else max x w

theorem positiveFloor_bot (w : ExtOrd) : positiveFloor w ⊥ = ⊥ := ite_eq_left rfl

theorem positiveFloor_of_ne {w x : ExtOrd} (hx : x ≠ ⊥) : positiveFloor w x = max x w :=
  ite_eq_right hx

theorem positiveFloor_eq_bot_iff {w x : ExtOrd} : positiveFloor w x = ⊥ ↔ x = ⊥ := by
  constructor
  · intro h
    by_contra hx
    rw [positiveFloor_of_ne hx] at h
    exact hx (le_bot_iff.mp ((le_max_left x w).trans h.le))
  · rintro rfl; exact positiveFloor_bot w

theorem positiveFloor_mono (w : ExtOrd) : Monotone (positiveFloor w) := by
  intro x y hxy
  by_cases hx : x = ⊥
  · rw [hx, positiveFloor_bot]; exact bot_le
  · have hy : y ≠ ⊥ := fun h => hx (le_bot_iff.mp (h ▸ hxy))
    rw [positiveFloor_of_ne hx, positiveFloor_of_ne hy]
    exact max_le_max hxy le_rfl

theorem le_positiveFloor {w x : ExtOrd} (hx : x ≠ ⊥) : w ≤ positiveFloor w x := by
  rw [positiveFloor_of_ne hx]; exact le_max_right _ _

theorem self_le_positiveFloor (w x : ExtOrd) : x ≤ positiveFloor w x := by
  by_cases hx : x = ⊥
  · rw [hx]; exact bot_le
  · rw [positiveFloor_of_ne hx]; exact le_max_left _ _

theorem positiveFloor_of_le {w x : ExtOrd} (hx : x ≠ ⊥) (h : w ≤ x) : positiveFloor w x = x := by
  rw [positiveFloor_of_ne hx]; exact max_eq_left h

/-- **Replacement commutes with the floor** at every grade at most the floor's visibility. -/
theorem positiveFloor_evr {w : ExtOrd} {K : ℕ} (hw : SelfVis K w) {k i : ℕ} (hk : k ≤ K)
    (hi : i ≤ k) (x : ExtOrd) :
    positiveFloor w (extVisibilityReplace x k i) =
      extVisibilityReplace (positiveFloor w x) k i := by
  by_cases hx : x = ⊥
  · rw [hx, extVisibilityReplace_bot, positiveFloor_bot, extVisibilityReplace_bot]
  · have hne : extVisibilityReplace x k i ≠ ⊥ := fun h => hx ((evr_eq_bot_iff k i).mp h)
    rw [positiveFloor_of_ne hne, positiveFloor_of_ne hx, (evr_monotone k i hi).map_max,
      evr_eq_self_of_selfVis (hw.mono hk) i]

/-- **The positive floor is a normalized grade-`K` witness.** -/
theorem witness_positiveFloor {w : ExtOrd} {K : ℕ} (hw : SelfVis K w) :
    Witness (gTop K) (positiveFloor w) where
  anti := (witness_id K).anti
  vis := (witness_id K).vis
  bot := positiveFloor_bot w
  mono := positiveFloor_mono w
  clause5 α k hle i hi := by
    by_cases hk : k ≤ K
    · exact positiveFloor_evr hw hk hi α
    · have h0 : positiveFloor w α = ⊥ := by
        rw [gTop, ite_eq_right hk] at hle
        exact le_bot_iff.mp hle
      have hα : α = ⊥ := positiveFloor_eq_bot_iff.mp h0
      rw [hα, extVisibilityReplace_bot, positiveFloor_bot, extVisibilityReplace_bot]

theorem boundedMap_positiveFloor {w : ExtOrd} {K : ℕ} (hw : SelfVis K w) :
    BoundedMap K (positiveFloor w) :=
  boundedMap_of_witness (witness_positiveFloor hw)

/-! ## Transport on unchanged long rows -/

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- **Bottom-reflecting transport**: a bounded replacement-commuting, bottom-reflecting scalar
image of a lawful section is lawful on the unchanged rows. -/
theorem map_respects_of_bottom_reflecting {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) {K : ℕ} (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    {ν : ExtOrd → ExtOrd} (hν : BoundedMap K ν) (hrefl : ∀ x, ν x = ⊥ → x = ⊥) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) := by
  refine (map_respects_iff_rowBlockBottom hr hK hν).mpr ?_
  intro c d e hb hz
  have h0 := rowBlockBottom_of_respects hr c d e hb
  change min (ν (r (CellScheme.below.incl c d))) (ν (r c)) = ⊥ at hz
  change min (ν (r (CellScheme.below.incl c e))) (ν (r c)) = ⊥
  rw [← hν.mono.map_min] at hz ⊢
  rw [h0 (hrefl _ hz), hν.bot]

/-- **The floor transports lawfulness** through grade `K` on arbitrary unchanged rows. -/
theorem positiveFloor_respects {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) {K : ℕ} (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    {w : ExtOrd} (hw : SelfVis K w) :
    RespectsSemanticsBelow sem BJ (fun d => positiveFloor w (r d)) :=
  map_respects_of_bottom_reflecting hr hK (boundedMap_positiveFloor hw)
    (fun _ h => positiveFloor_eq_bot_iff.mp h)

/-- The whole-labelling form, on a scheme dominated by a top index. -/
theorem positiveFloor_respects_whole {top : Finset ι × ℕ} (htop : ∀ d, GradedLe (D.cell d) top)
    {r : Cell D → ExtOrd} (hr : RespectsSemantics sem r) {K : ℕ} (hK : top.2 ≤ K) {w : ExtOrd}
    (hw : SelfVis K w) : RespectsSemantics sem (fun d => positiveFloor w (r d)) :=
  RespectsSemantics.of_below_top htop
    (positiveFloor_respects (hr.toBelow top) (fun d => d.2.2.trans hK) hw)

/-- **The flat section**: capping every value at a `K`-visible `w` is lawful; on a section whose
positive values are all at least `w` this replaces every positive value by `w`. -/
theorem flat_section {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) {K : ℕ} (hK : BJ.2 ≤ K) {w : ExtOrd}
    (hw : SelfVis K w) :
    RespectsSemanticsBelow sem BJ (fun d => min (r d) w) ∧
      ∀ d, w ≤ r d → min (r d) w = w :=
  ⟨hr.gradeCap (fun _ => w) (fun _ _ _ => le_rfl) (fun _ hk => hw.mono (hk.trans hK)),
    fun _ h => min_eq_right h⟩

end VaughtConjecture.Knight
