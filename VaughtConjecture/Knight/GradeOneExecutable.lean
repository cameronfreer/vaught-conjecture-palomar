/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneFiniteBountiful

/-! # Executable grade-one row queries

The executable data contains natural-number source ranks for every full
controller and triples recording the block-bottom implications at every nested
row. The interpretation of label zero is bottom, not ordinal zero. All other
label codes are proper natural ordinals. The checker uses only finite maxima,
natural comparisons, and Boolean flags; no ordinal comparison is executed.

The semantic adapter below requires exact source-order, source-bottom, and
nested-block identifications. A controller enumeration must be exhaustive.
Rejecting the resulting complete query is distinct from rejecting a proposed
witness. This file does not manufacture a consistent scheme from numerical data.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting.Executable

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-- Zero encodes bottom; positive codes encode proper natural ordinals. -/
noncomputable def value (n : ℕ) : ExtOrd := if n = 0 then ⊥ else ofOrd n

@[simp] theorem value_zero : value 0 = ⊥ := rfl

@[simp] theorem value_one : value 1 = ofOrd 1 := by simp [value]

@[simp] theorem value_eq_bot {n : ℕ} : value n = ⊥ ↔ n = 0 := by
  by_cases hn : n = 0 <;> simp [value, hn]

@[simp] theorem value_le {a b : ℕ} : value a ≤ value b ↔ a ≤ b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb, ha, le_bot_iff]
  simp only [value, ite_eq_right ha, ite_eq_right hb, ofOrd_le_ofOrd]
  exact_mod_cast Iff.rfl

theorem value_mono : Monotone value := fun _ _ h => value_le.mpr h

@[simp] theorem value_lt {a b : ℕ} : value a < value b ↔ a < b := by
  simp only [lt_iff_le_not_ge, value_le]

@[simp] theorem value_inj {a b : ℕ} : value a = value b ↔ a = b := by
  simp only [le_antisymm_iff, value_le]

@[simp] theorem value_min (a b : ℕ) : value (min a b) = min (value a) (value b) :=
  value_mono.map_min

@[simp] theorem value_max (a b : ℕ) : value (max a b) = max (value a) (value b) :=
  value_mono.map_max

theorem value_visible (n : ℕ) : SelfVis 1 (value n) := by
  by_cases hn : n = 0
  · simp only [hn, value_zero]; exact selfVis_bot 1
  · simp only [value, ite_eq_right hn, selfVis_ofOrd_iff, finitePart_natCast]
    exact Nat.one_le_iff_ne_zero.mpr hn

theorem value_finiteValue {N : ℕ} (i : Fin (N + 1)) : value i.val = finiteValue i := rfl

section Propagation

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem value_sup (f : Y → ℕ) :
    value (Finset.univ.sup f) = Finset.univ.sup (fun y => value (f y)) :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder value value_mono value_zero

/-- Exact interpretation of the numerical closure. Sources need only have the
same order; they are not changed in the semantic scheme. -/
theorem value_close {S : Type*} [LinearOrder S] (E : Y → ℕ) (F : Y → S)
    (horder : ∀ d e, E d ≤ E e ↔ F d ≤ F e)
    (embed : X → Y) (p : X → ℕ) (q : Y → ℕ) (γ : ℕ) (d : Y) :
    value (Propagation.close E embed p q γ d) =
      Propagation.close F embed (fun x => value (p x)) (fun y => value (q y)) (value γ) d := by
  unfold Propagation.close
  rw [value_max, value_sup, value_sup]
  congr 1 <;> apply Finset.sup_congr rfl <;> intro e _
  all_goals simp only [horder]; split_ifs <;> simp

theorem check_iff {E : Y → ℕ} {F : Y → ExtOrd}
    (horder : ∀ d e, E d ≤ E e ↔ F d ≤ F e)
    (hbot : ∀ d, E d = 0 ↔ F d = ⊥)
    (embed : X → Y) (p : X → ℕ) (q : Y → ℕ) (γ : ℕ) :
    Propagation.Check E embed p q γ ↔
      Propagation.Check F embed (fun x => value (p x)) (fun y => value (q y)) (value γ) := by
  simp only [Propagation.Check, ← value_close E F horder, value_le, value_lt,
    value_eq_bot, ← hbot]
  rfl

end Propagation

/-- Fixed finite data. A triple (c,d,e) records the implication at owner c
from a bottom capped reading at d to one at e. Cells remain distinct. -/
structure Data (Y C : Type*) where
  source : C → Y → ℕ
  blocks : Finset (Y × Y × Y)

namespace Data

variable {Y C X B : Type*} [Fintype Y] [Fintype C] [Fintype X] [Fintype B]
  [DecidableEq X] [DecidableEq Y]

/-- All nested-row bottom implications, including the actual owner cap. -/
def Blocks (T : Data Y C) (r : Y → ℕ) : Prop :=
  ∀ t ∈ T.blocks, (r t.2.1 = 0 ∨ r t.1 = 0) → (r t.2.2 = 0 ∨ r t.1 = 0)

/-- Lawfulness test: block implications and an exhaustive full-row order query. -/
def Respect (T : Data Y C) (r : Y → ℕ) : Prop :=
  T.Blocks r ∧ ∃ c, (∀ d e, T.source c d ≤ T.source c e → r d ≤ r e) ∧
    (∀ d, T.source c d = 0 → r d = 0)

/-- True flags denote bottom; the numerical seed one is the least positive label. -/
def seed (z : Y → Bool) (d : Y) : ℕ := if z d then 0 else 1

/-- Exact output query, not a test of a preselected witness. -/
def Lift (T : Data Y C) (embed : X → Y) (p : X → ℕ) (q : Y → ℕ) (γ : ℕ) : Prop :=
  (γ = 0 ∧ ∃ c, ∃ z : Y → Bool,
    Propagation.Check (T.source c) embed p (seed z) 1 ∧ T.Blocks (seed z)) ∨
  (γ ≠ 0 ∧ ∃ c, Propagation.Check (T.source c) embed p q γ)

instance (T : Data Y C) (r : Y → ℕ) : Decidable (T.Blocks r) :=
  inferInstanceAs (Decidable (∀ t ∈ T.blocks, _))

instance (T : Data Y C) (r : Y → ℕ) : Decidable (T.Respect r) :=
  inferInstanceAs (Decidable (T.Blocks r ∧ ∃ _, _))

instance (E : Y → ℕ) (embed : X → Y) (p : X → ℕ) (q : Y → ℕ) (γ : ℕ) :
    Decidable (Propagation.Check E embed p q γ) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop)))

instance (T : Data Y C) (embed : X → Y) (p : X → ℕ) (q : Y → ℕ) (γ : ℕ) :
    Decidable (T.Lift embed p q γ) :=
  inferInstanceAs (Decidable ((_ : Prop) ∨ (_ : Prop)))

def liftCheck (T : Data Y C) (embed : X → Y) (p : X → ℕ) (q : Y → ℕ) (γ : ℕ) : Bool :=
  decide (T.Lift embed p q γ)

/-- At positive caps, do not evaluate the bottom-pattern search. -/
def fastLiftCheck (T : Data Y C) (embed : X → Y) (p : X → ℕ) (q : Y → ℕ) (γ : ℕ) : Bool :=
  if γ = 0 then
    decide (∃ c, ∃ z : Y → Bool,
      Propagation.Check (T.source c) embed p (seed z) 1 ∧ T.Blocks (seed z))
  else decide (∃ c, Propagation.Check (T.source c) embed p q γ)

omit [DecidableEq X] in
theorem fastLiftCheck_eq (T : Data Y C) (embed : X → Y)
    (p : X → ℕ) (q : Y → ℕ) (γ : ℕ) :
    fastLiftCheck T embed p q γ = liftCheck T embed p q γ := by
  by_cases hγ : γ = 0 <;> simp [fastLiftCheck, liftCheck, Lift, hγ]

/-- Universal bounded test; no ordinal-valued variables occur. -/
def Universal (P : Data X B) (T : Data Y C) (embed : X → Y) (N : ℕ) : Prop :=
  ∀ (p : X → Fin (N + 1)) (q : Y → Fin (N + 1)) (γ : Fin (N + 1)),
    P.Respect (fun x => (p x).val) → T.Respect (fun y => (q y).val) →
    (∀ x, min (q (embed x)).val γ.val = min (p x).val γ.val) →
    T.Lift embed (fun x => (p x).val) (fun y => (q y).val) γ.val

instance (P : Data X B) (T : Data Y C) (embed : X → Y) (N : ℕ) :
    Decidable (Universal P T embed N) :=
  inferInstanceAs (Decidable (∀ (_ : X → Fin (N + 1)) (_ : Y → Fin (N + 1))
    (_ : Fin (N + 1)), _))

def universalCheck (P : Data X B) (T : Data Y C) (embed : X → Y) (N : ℕ) : Bool :=
  decide (Universal P T embed N)

/-- Screen each ambient once, then each prescription, before trying the caps.
This avoids recomputing the same row-law tests for every cap and boundary. -/
def screenedCheck (P : Data X B) (T : Data Y C) (embed : X → Y) (N : ℕ) : Bool :=
  decide (∀ (q : Y → Fin (N + 1)), T.Respect (fun y => (q y).val) →
    ∀ (p : X → Fin (N + 1)), P.Respect (fun x => (p x).val) →
    ∀ (γ : Fin (N + 1)),
      (∀ x, min (q (embed x)).val γ.val = min (p x).val γ.val) →
      T.fastLiftCheck embed (fun x => (p x).val) (fun y => (q y).val) γ.val = true)

/-- Screening changes only evaluation order; every input and output branch is retained. -/
theorem screenedCheck_eq (P : Data X B) (T : Data Y C) (embed : X → Y) (N : ℕ) :
    screenedCheck P T embed N = universalCheck P T embed N := by
  unfold screenedCheck universalCheck
  simp only [fastLiftCheck_eq, liftCheck, decide_eq_true_eq]
  congr 1
  apply propext
  constructor
  · intro hs p q γ hp hq hag
    exact hs q hq p hp γ hag
  · intro hs q hq p hp γ hag
    exact hs p q γ hp hq hag

end Data

section Semantics

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ CI : Finset ι × ℕ} {C B : Type*}

/-- Exact identification with an existing scheme. The block soundness field
excludes spurious triples; completeness retains every actual nested occurrence.
No respect or lifting assumption is concealed in the data identification. -/
structure Realizes (T : Data (D.below BJ) C) (sem : Semantics D) where
  owner : C → Controller D BJ
  covers : Function.Surjective owner
  source_order : ∀ c d e, T.source c d ≤ T.source c e ↔
    (owner c).row sem d ≤ (owner c).row sem e
  source_bottom : ∀ c d, T.source c d = 0 ↔ (owner c).row sem d = ⊥
  blocks_sound : ∀ c d e, (c, d, e) ∈ T.blocks →
    ∃ hd : GradedLe (D.cell d.1) (D.cell c.1),
    ∃ he : GradedLe (D.cell e.1) (D.cell c.1),
      blockFloor (sem.E c.1 ⟨d.1, hd⟩) = blockFloor (sem.E c.1 ⟨e.1, he⟩)
  blocks_complete : ∀ (c : D.below BJ) (d e : D.below (D.cell c.1)),
    blockFloor (sem.E c.1 d) = blockFloor (sem.E c.1 e) →
    (c, CellScheme.below.incl c d, CellScheme.below.incl c e) ∈ T.blocks

namespace Realizes

variable {T : Data (D.below BJ) C} (R : Realizes T sem)

include R

theorem blocks_iff (r : D.below BJ → ℕ) :
    T.Blocks r ↔ RowBlockBottom sem BJ (fun d => value (r d)) := by
  constructor
  · intro h c d e heq hz
    have hh := h _ (R.blocks_complete c d e heq)
    simpa only [min_eq_bot, value_eq_bot] using
      hh (by simpa only [min_eq_bot, value_eq_bot] using hz)
  · intro h ⟨c, d, e⟩ ht hz
    obtain ⟨hd, he, hb⟩ := R.blocks_sound c d e ht
    have hh := h c ⟨d.1, hd⟩ ⟨e.1, he⟩ hb
    change min (value (r d)) (value (r c)) = ⊥ →
      min (value (r e)) (value (r c)) = ⊥ at hh
    simpa only [min_eq_bot, value_eq_bot] using
      hh (by simpa only [min_eq_bot, value_eq_bot] using hz)

theorem finiteRespect_iff (r : D.below BJ → ℕ) :
    T.Respect r ↔ FiniteRespect sem BJ (fun d => value (r d)) := by
  constructor
  · rintro ⟨hb, c, hord, hbot⟩
    refine ⟨(R.blocks_iff r).mp hb, R.owner c, ?_, ?_⟩
    · intro d e hde
      exact value_le.mpr (hord d e ((R.source_order c d e).mpr hde))
    · intro d hd
      exact value_eq_bot.mpr (hbot d ((R.source_bottom c d).mpr hd))
  · rintro ⟨hb, c, hord, hbot⟩
    obtain ⟨i, rfl⟩ := R.covers c
    refine ⟨(R.blocks_iff r).mpr hb, i, ?_, ?_⟩
    · intro d e hde
      exact value_le.mp (hord d e ((R.source_order i d e).mp hde))
    · intro d hd
      exact value_eq_bot.mp (hbot d ((R.source_bottom i d).mp hd))

theorem respects_iff (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    (c₀ : Controller D BJ) (r : D.below BJ → ℕ) :
    T.Respect r ↔ RespectsSemanticsBelow sem BJ (fun d => value (r d)) := by
  rw [respects_iff_finiteRespect hc hgrade c₀ (fun d => hgrade ▸ value_visible (r d))]
  exact R.finiteRespect_iff r

omit R in
theorem seed_value (z : D.below BJ → Bool) :
    (fun d => value (Data.seed z d)) = BottomPattern.seed z := by
  funext d
  cases h : z d <;> simp [Data.seed, BottomPattern.seed, h, value]

theorem seed_blocks_iff (z : D.below BJ → Bool) :
    T.Blocks (Data.seed z) ↔ BottomPattern.Compatible sem z := by
  rw [R.blocks_iff, seed_value, BottomPattern.compatible_iff]

variable {X : Type*} [Fintype X] [Fintype (D.below BJ)]

/-- Every branch of the finite output query is identified with the semantic
test, in both directions. This theorem uses no consistency assumption. -/
theorem capCheck_iff (embed : X → D.below BJ) (p : X → ℕ)
    (q : D.below BJ → ℕ) (γ : ℕ) :
    T.Lift embed p q γ ↔
      CapCheck sem embed (fun x => value (p x)) (fun d => value (q d)) (value γ) := by
  have hp c : Propagation.Check (T.source c) embed p q γ ↔
      Propagation.Check ((R.owner c).row sem) embed
        (fun x => value (p x)) (fun d => value (q d)) (value γ) :=
    check_iff (R.source_order c) (R.source_bottom c) embed p q γ
  have hb c z : Propagation.Check (T.source c) embed p (Data.seed z) 1 ↔
      Propagation.Check ((R.owner c).row sem) embed
        (fun x => value (p x)) (BottomPattern.seed z) (ofOrd 1) := by
    simpa only [seed_value, value_one] using
      check_iff (R.source_order c) (R.source_bottom c) embed p (Data.seed z) 1
  constructor
  · rintro (⟨hg, c, z, hc, hz⟩ | ⟨hg, c, hc⟩)
    · refine Or.inl ⟨value_eq_bot.mpr hg, R.owner c, z, ?_,
        (R.seed_blocks_iff z).mp hz⟩
      simpa only [Propagation.check_iff] using (hb c z).mp hc
    · refine Or.inr ⟨fun h => hg (value_eq_bot.mp h), R.owner c, ?_⟩
      simpa only [Propagation.check_iff] using (hp c).mp hc
  · rintro (⟨hg, c, z, hc, hz⟩ | ⟨hg, c, hc⟩)
    · obtain ⟨i, rfl⟩ := R.covers c
      refine Or.inl ⟨value_eq_bot.mp hg, i, z, (hb i z).mpr ?_,
        (R.seed_blocks_iff z).mpr hz⟩
      simpa only [Propagation.check_iff] using hc
    · obtain ⟨i, rfl⟩ := R.covers c
      refine Or.inr ⟨fun h => hg (value_eq_bot.mpr h), i, (hp i).mpr ?_⟩
      simpa only [Propagation.check_iff] using hc

variable [Fintype C]

/-- A passing computation is equivalent to an actual lift; the ambient's
lawfulness is checked by the numerical test, not assumed as an ordinal completion. -/
theorem liftCheck_iff [DecidableEq (D.below BJ)]
    (hc : sem.IsConsistent) (hgrade : BJ.2 = 1) (c₀ : Controller D BJ)
    (embed : X → D.below BJ) (p : X → ℕ) (q : D.below BJ → ℕ) (γ : ℕ)
    (hq : T.Respect q) :
    T.liftCheck embed p q γ = true ↔
      HasLift (sem := sem) embed (fun x => value (p x))
        (fun d => value (q d)) (value γ) := by
  rw [Data.liftCheck, decide_eq_true_eq, R.capCheck_iff]
  exact (lift_iff_all_cap_check hc hgrade c₀ ((R.respects_iff hc hgrade c₀ q).mp hq)
    (fun x => hgrade ▸ value_visible (p x)) (hgrade ▸ value_visible γ)).symm

/-- With the exact data and lawful ambient, a false *complete* check rules out
every lift, unlike rejection of a single serialized witness. -/
theorem liftCheck_false_iff [DecidableEq (D.below BJ)]
    (hc : sem.IsConsistent) (hgrade : BJ.2 = 1) (c₀ : Controller D BJ)
    (embed : X → D.below BJ) (p : X → ℕ) (q : D.below BJ → ℕ) (γ : ℕ)
    (hq : T.Respect q) :
    T.liftCheck embed p q γ = false ↔
      ¬ HasLift (sem := sem) embed (fun x => value (p x))
        (fun d => value (q d)) (value γ) := by
  rw [← R.liftCheck_iff hc hgrade c₀ embed p q γ hq]
  exact Bool.eq_false_iff

end Realizes

variable [Fintype B] [Fintype C] [Fintype (D.below CI)] [Fintype (D.below BJ)]
  [DecidableEq (D.below CI)] [DecidableEq (D.below BJ)]

/-- The executable universal test is equivalent to the literal unrestricted
grade-one clause. The numerical bound is identified explicitly, so executing
the test never has to compute a classical cardinality or an ordinal. -/
theorem universalCheck_iff (P : Data (D.below CI) B) (T : Data (D.below BJ) C)
    (RP : Realizes P sem) (RT : Realizes T sem) (hc : sem.IsConsistent)
    (h : GradedLe CI BJ) (hsmall : CI.2 = 1) (hlarge : BJ.2 = 1)
    (csmall : Controller D CI) (clarge : Controller D BJ)
    (N : ℕ) (hN : N = inputBound D CI BJ) :
    Data.universalCheck P T (CellScheme.below.mono h) N = true ↔ LiftsAt sem h := by
  rw [Data.universalCheck, decide_eq_true_eq,
    liftsAt_iff_finiteTest hc h hsmall hlarge csmall clarge, ← hN]
  unfold Data.Universal FiniteTest
  simp only [← value_finiteValue, ← RP.finiteRespect_iff, ← RT.finiteRespect_iff,
    ← RT.capCheck_iff, ← value_min, value_inj]
  simp only [Data.Lift, Propagation.check_iff]

end Semantics

end VaughtConjecture.Knight.FullRowLifting.Executable
