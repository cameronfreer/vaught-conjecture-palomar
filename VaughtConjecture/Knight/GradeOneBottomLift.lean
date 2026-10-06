/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneLeastLift

/-! # Bottom-cap grade-one sections by finite bottom-pattern branching

At bottom cap the ambient imposes no equations. Enumerate the bottom flags of
the target occurrences instead. A flag assignment must satisfy the source-block
bottom implications at every actual nested controller. Seed each nonbottom
occurrence with the least nonbottom grade-one-visible value, ordinal one, and
use the existing finite source-order closure for each full controller.

The test is necessary and sufficient, and a passing branch constructs its least
source-order-compatible section. The ordinal one used to encode the flags is
not a replacement external cap: the actual clause remains at bottom. This is
a finite test on supplied inputs, not an enumeration of all ordinal inputs, and
has no mixed-grade conclusion.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

namespace BottomPattern

/-- Ordinal one is the least nonbottom self-visible label at grade one. -/
theorem one_le_of_visible {x : ExtOrd} (hv : SelfVis 1 x) (hx : x ≠ ⊥) :
    ofOrd 1 ≤ x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact (hx rfl).elim
  · exact le_top
  · apply ofOrd_le_ofOrd.mpr
    have hf := selfVis_ofOrd_iff.mp hv
    calc
      (1 : Ordinal) ≤ (finitePart a : Ordinal) := by exact_mod_cast hf
      _ ≤ limitPart a + (finitePart a : Ordinal) := le_add_self
      _ = a := decomposition a

theorem one_visible : SelfVis 1 (ofOrd 1) := by
  rw [selfVis_ofOrd_iff]
  simpa only [Nat.cast_one] using (finitePart_natCast 1).ge

/-- True means bottom. A false flag is represented by ordinal one, not zero. -/
def seed {Y : Type*} (z : Y → Bool) (d : Y) : ExtOrd :=
  if z d then ⊥ else ofOrd 1

@[simp] theorem seed_eq_bot {Y : Type*} (z : Y → Bool) (d : Y) :
    seed z d = ⊥ ↔ z d = true := by
  cases hz : z d <;> simp [seed, hz]

theorem seed_visible {Y : Type*} (z : Y → Bool) (d : Y) : SelfVis 1 (seed z d) := by
  unfold seed
  split_ifs
  · exact selfVis_bot 1
  · exact one_visible

/-- Capping a visible labelling at ordinal one records exactly its bottom flags. -/
theorem seed_cap {Y : Type*} {r : Y → ExtOrd} (hr : ∀ d, SelfVis 1 (r d))
    {z : Y → Bool} (hz : ∀ d, z d = true ↔ r d = ⊥) (d : Y) :
    min (r d) (ofOrd 1) = min (seed z d) (ofOrd 1) := by
  by_cases hd : z d = true
  · rw [(hz d).mp hd]
    simp [seed, hd]
  · have hn : r d ≠ ⊥ := fun h => hd ((hz d).mpr h)
    simp only [seed, ite_eq_right hd, min_self,
      min_eq_right (one_le_of_visible (hr d) hn)]

end BottomPattern

namespace Propagation

/-- A passing propagation check certifies the displayed closure's boundary,
without any semantic hypothesis about its seed values. -/
theorem close_boundary {Y X S : Type*} [Fintype Y] [Fintype X]
    [LinearOrder S] [OrderBot S] {E : Y → S} {embed : X → Y}
    {p : X → ExtOrd} {q : Y → ExtOrd} {γ : ExtOrd} (h : Check E embed p q γ) :
    (∀ d, min (close E embed p q γ d) γ = min (q d) γ) ∧
      (∀ x, close E embed p q γ (embed x) = p x) := by
  constructor
  · intro d
    apply (cap_eq_iff_profile _ _ _).mpr
    constructor
    · intro hd
      apply le_antisymm (h.1 d hd)
      have hh := cap_le_close E embed p q γ d
      rwa [min_eq_left hd.le] at hh
    · intro hd
      have hh := cap_le_close E embed p q γ d
      rwa [min_eq_right hd] at hh
  · intro x
    exact le_antisymm (h.2.1 x) (prescribed_le_close E embed p q γ x)

end Propagation

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

noncomputable local instance : Fintype (D.below BJ) := Fintype.ofFinite _

namespace BottomPattern

/-- Boolean source-block implications at every actual controller and occurrence.
No row-locality witness or completion is part of this predicate. -/
def Compatible (sem : Semantics D) (z : D.below BJ → Bool) : Prop :=
  ∀ (c : D.below BJ) (d e : D.below (D.cell c.1)),
    blockFloor (sem.E c.1 d) = blockFloor (sem.E c.1 e) →
    (z (CellScheme.below.incl c d) = true ∨ z c = true) →
    (z (CellScheme.below.incl c e) = true ∨ z c = true)

theorem compatible_iff (z : D.below BJ → Bool) :
    Compatible sem z ↔ RowBlockBottom sem BJ (seed z) := by
  simp only [Compatible, RowBlockBottom, min_eq_bot, seed_eq_bot]

/-- Exact branch check: finite source-order propagation plus Boolean block laws. -/
def Check {X : Type*} [Fintype X] (c : Controller D BJ) (z : D.below BJ → Bool)
    (embed : X → D.below BJ) (p : X → ExtOrd) : Prop :=
  Propagation.Check (c.row sem) embed p (seed z) (ofOrd 1) ∧ Compatible sem z

end BottomPattern

/-- A visible source-monotone table is lawful exactly when the actual source-block
bottom laws hold. Consistency supplies the donor row, not the requested section. -/
theorem respects_of_order_and_blocks (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    (c : Controller D BJ) {r : D.below BJ → ExtOrd}
    (hv : ∀ d, SelfVis BJ.2 (r d))
    (hord : ∀ d e, c.row sem d ≤ c.row sem e → r d ≤ r e)
    (hbot : ∀ d, c.row sem d = ⊥ → r d = ⊥)
    (hblocks : RowBlockBottom sem BJ r) : RespectsSemanticsBelow sem BJ r := by
  have hE : ∀ d, SelfVis BJ.2 (c.row sem d) := by
    intro d
    have hh : SelfVis (D.grade d.1) (c.row sem d) := ((c.row_respects hc).orderly d).symm
    rwa [grade_eq_one hgrade d, ← hgrade] at hh
  have he := funext (orderInterpolate_read hord hbot)
  have hr := (map_respects_iff_rowBlockBottom (c.row_respects hc)
    (fun d => d.2.2) (orderInterpolate_bounded hE hv)).mpr (he.symm ▸ hblocks)
  exact he ▸ hr

/-- The least candidate in a passing bottom-pattern branch is an actual section.
No lawful ambient or ambient completion is needed at bottom cap. -/
theorem least_bottom_lift_of_check (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    {X : Type*} [Fintype X] {embed : X → D.below BJ} {p : X → ExtOrd}
    (hp : ∀ x, SelfVis BJ.2 (p x)) (c : Controller D BJ) (z : D.below BJ → Bool)
    (hcheck : BottomPattern.Check (sem := sem) c z embed p)
    (q : D.below BJ → ExtOrd) :
    RespectsSemanticsBelow sem BJ
        (Propagation.close (c.row sem) embed p (BottomPattern.seed z) (ofOrd 1)) ∧
      Boundary embed p q ⊥
        (Propagation.close (c.row sem) embed p (BottomPattern.seed z) (ofOrd 1)) := by
  have hb := Propagation.close_boundary hcheck.1
  have hpattern := bottom_pattern_of_cap_agreement (ofOrd_ne_bot 1) hb.1
  have hblocks := rowBlockBottom_of_same_pattern
    ((BottomPattern.compatible_iff z).mp hcheck.2) hpattern
  have hv : ∀ d, SelfVis BJ.2
      (Propagation.close (c.row sem) embed p (BottomPattern.seed z) (ofOrd 1) d) := by
    intro d
    apply Propagation.close_visible (c.row sem) embed hp
    · intro e
      rw [hgrade]
      exact BottomPattern.seed_visible z e
    · rw [hgrade]
      exact BottomPattern.one_visible
  refine ⟨respects_of_order_and_blocks hc hgrade c hv
    (fun _ _ => Propagation.close_order _ _ _ _ _) hcheck.1.2.2 hblocks, ?_⟩
  exact ⟨fun _ => by simp only [min_bot_right], hb.2⟩

/-- Exact grade-one bottom-cap test. The only search variables are a full
controller and finitely many Boolean bottom flags; the output is propagated. -/
theorem bottom_lift_iff_exists_check (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    (c₀ : Controller D BJ) {X : Type*} [Fintype X] {embed : X → D.below BJ}
    {p : X → ExtOrd} {q : D.below BJ → ExtOrd} (hp : ∀ x, SelfVis BJ.2 (p x)) :
    HasLift (sem := sem) embed p q ⊥ ↔
      ∃ c : Controller D BJ, ∃ z : D.below BJ → Bool,
        BottomPattern.Check (sem := sem) c z embed p := by
  classical
  constructor
  · rintro ⟨r, hr, hb⟩
    obtain ⟨c, τ, hτ, _, he⟩ := exists_full_row_representation hgrade c₀ hr
    let z : D.below BJ → Bool := fun d => decide (r d = ⊥)
    have hz : ∀ d, z d = true ↔ r d = ⊥ := fun d => by simp [z]
    have hv : ∀ d, SelfVis 1 (r d) := by
      intro d
      have hh : SelfVis (D.grade d.1) (r d) := (hr.orderly d).symm
      rwa [grade_eq_one hgrade d] at hh
    refine ⟨c, z, Propagation.check_iff.mpr ⟨r, ?_, ?_,
      BottomPattern.seed_cap hv hz, hb.2⟩, ?_⟩
    · intro d e hde
      rw [← he d, ← he e]
      exact hτ.mono hde
    · intro d hd
      rw [← he d, hd, hτ.bot]
    · apply (BottomPattern.compatible_iff z).mpr
      apply rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects hr)
      intro d
      exact (BottomPattern.seed_eq_bot z d).trans (hz d)
  · rintro ⟨c, z, hcheck⟩
    exact ⟨_, least_bottom_lift_of_check hc hgrade hp c z hcheck q⟩

/-- Minimality is within a fixed controller and bottom-pattern branch. There
is no assertion that different controller branches share one least section. -/
theorem bottom_close_le {X : Type*} [Fintype X] {embed : X → D.below BJ}
    {p : X → ExtOrd} (c : Controller D BJ) (z : D.below BJ → Bool)
    {r : D.below BJ → ExtOrd} (hv : ∀ d, SelfVis 1 (r d))
    (hz : ∀ d, z d = true ↔ r d = ⊥)
    (hord : ∀ d e, c.row sem d ≤ c.row sem e → r d ≤ r e)
    (hface : ∀ x, r (embed x) = p x) (d : D.below BJ) :
    Propagation.close (c.row sem) embed p (BottomPattern.seed z) (ofOrd 1) d ≤ r d := by
  apply Propagation.close_le hord _ (fun x => (hface x).ge)
  intro e
  rw [← BottomPattern.seed_cap hv hz]
  exact min_le_left _ _

/-- Finite output alphabet for bottom-cap sections: prescribed values together
with bottom and ordinal one suffice. Literal top, if prescribed, remains top. -/
theorem bottom_close_value {X : Type*} [Fintype X] (embed : X → D.below BJ)
    (p : X → ExtOrd) (c : Controller D BJ) (z : D.below BJ → Bool) (d : D.below BJ) :
    Propagation.close (c.row sem) embed p (BottomPattern.seed z) (ofOrd 1) d = ⊥ ∨
      Propagation.close (c.row sem) embed p (BottomPattern.seed z) (ofOrd 1) d = ofOrd 1 ∨
      ∃ x, Propagation.close (c.row sem) embed p (BottomPattern.seed z) (ofOrd 1) d = p x := by
  rcases Propagation.close_value (c.row sem) embed p (BottomPattern.seed z) (ofOrd 1) d
    with h | ⟨e, he⟩ | h
  · exact Or.inl h
  · cases hz : z e
    · exact Or.inr (Or.inl (by simpa [BottomPattern.seed, hz] using he))
    · exact Or.inl (by simpa [BottomPattern.seed, hz] using he)
  · exact Or.inr (Or.inr h)

/-- One exact grade-one criterion for all permitted caps, bottom and literal top
included. Positive caps retain their original value and need no flag search. -/
theorem lift_iff_all_cap_check (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    (c₀ : Controller D BJ) {X : Type*} [Fintype X] {embed : X → D.below BJ}
    {p : X → ExtOrd} {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) (hp : ∀ x, SelfVis BJ.2 (p x))
    (hγvis : SelfVis BJ.2 γ) :
    HasLift (sem := sem) embed p q γ ↔
      (γ = ⊥ ∧ ∃ c : Controller D BJ, ∃ z : D.below BJ → Bool,
        BottomPattern.Check (sem := sem) c z embed p) ∨
      (γ ≠ ⊥ ∧ ∃ c : Controller D BJ, Propagation.Check (c.row sem) embed p q γ) := by
  by_cases hγ : γ = ⊥
  · subst γ
    simpa only [true_and, ne_eq, not_true_eq_false, false_and, or_false] using
      (bottom_lift_iff_exists_check hc hgrade c₀ hp (q := q))
  · simpa only [hγ, false_and, ne_eq, not_false_eq_true, true_and, false_or] using
      (lift_iff_exists_check hc hgrade c₀ hq hp hγvis hγ)

end VaughtConjecture.Knight.FullRowLifting
