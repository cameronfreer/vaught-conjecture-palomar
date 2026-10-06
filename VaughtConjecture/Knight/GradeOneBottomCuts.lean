/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneExecutable
public import VaughtConjecture.Knight.GradeOneSectionLifting

/-! # Bottom patterns are source cuts

For a fixed full row, every source-monotone labelling has an initial-segment
bottom set. Thus at most n+1 cuts replace the 2^n Boolean bottom patterns in
the exact grade-one query. All nested block implications are still checked.
This is an equivalence, not heuristic pruning or a new consistency theorem.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

namespace BottomCut

variable {Y X S L : Type*} [LinearOrder S] [LinearOrder L] [OrderBot L]

/-- None is the empty bottom set. A selected occurrence supplies a closed
source cut, retaining ties and all distinct occurrences. -/
def flag (E : Y → S) : Option Y → Y → Bool
  | none, _ => false
  | some a, d => decide (E d ≤ E a)

/-- The binary seed for any nonbottom value u. -/
def seed (u : L) (z : Y → Bool) (d : Y) : L := if z d then ⊥ else u

theorem seed_eq_bot {u : L} (hu : u ≠ ⊥) (z : Y → Bool) (d : Y) :
    seed u z d = ⊥ ↔ z d = true := by
  cases hz : z d <;> simp [seed, hz, hu]

/-- A finite source-monotone labelling has one of the n+1 source-cut patterns. -/
theorem exists_flag [Finite Y] {E : Y → S} {r : Y → L}
    (hr : ∀ d e, E d ≤ E e → r d ≤ r e) :
    ∃ a : Option Y, ∀ d, flag E a d = true ↔ r d = ⊥ := by
  classical
  by_cases hb : ∃ d, r d = ⊥
  · let Z := {d : Y // r d = ⊥}
    have : Nonempty Z := ⟨⟨hb.choose, hb.choose_spec⟩⟩
    obtain ⟨a, ha⟩ := Finite.exists_max (fun d : Z => E d.1)
    refine ⟨some a.1, fun d => ?_⟩
    simp only [flag, decide_eq_true_eq]
    constructor
    · intro hd
      exact le_bot_iff.mp ((hr d a.1 hd).trans_eq a.2)
    · intro hd
      exact ha ⟨d, hd⟩
  · refine ⟨none, fun d => ?_⟩
    simp only [flag, Bool.false_eq_true, false_iff]
    exact fun hd => hb ⟨d, hd⟩

variable [Fintype X] [Fintype Y] [OrderBot S]

/-- Passing an order-closure check forces its chosen Boolean flags to be a
source cut. Hence replacing arbitrary flags by cuts loses no passing branch. -/
theorem flag_of_check {E : Y → S} {embed : X → Y} {p : X → L}
    {u : L} (hu : u ≠ ⊥) {z : Y → Bool}
    (h : Propagation.Check E embed p (seed u z) u) :
    ∃ a : Option Y, flag E a = z := by
  obtain ⟨r, hr, _, hcap, _⟩ := Propagation.check_iff.mp h
  obtain ⟨a, ha⟩ := exists_flag hr
  refine ⟨a, funext fun d => Bool.eq_iff_iff.mpr ?_⟩
  have hb : r d = ⊥ ↔ seed u z d = ⊥ := by
    have he : min (r d) u = ⊥ ↔ min (seed u z d) u = ⊥ := by rw [hcap d]
    simpa only [min_eq_bot, hu, or_false] using he
  exact (ha d).trans (hb.trans (seed_eq_bot hu z d))

end BottomCut

section Semantic

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

noncomputable local instance : Fintype (D.below BJ) := Fintype.ofFinite _

/-- Exact bottom-cap test with source cuts rather than arbitrary flags.
The complete controller disjunction and every block condition are retained. -/
theorem bottom_lift_iff_exists_cut (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    (c₀ : Controller D BJ) {X : Type*} [Fintype X] {embed : X → D.below BJ}
    {p : X → ExtOrd} {q : D.below BJ → ExtOrd} (hp : ∀ x, SelfVis BJ.2 (p x)) :
    HasLift (sem := sem) embed p q ⊥ ↔
      ∃ c : Controller D BJ, ∃ a : Option (D.below BJ),
        BottomPattern.Check (sem := sem) c (BottomCut.flag (c.row sem) a) embed p := by
  rw [bottom_lift_iff_exists_check hc hgrade c₀ hp]
  constructor
  · rintro ⟨c, z, hz⟩
    obtain ⟨a, ha⟩ := BottomCut.flag_of_check (ofOrd_ne_bot 1) hz.1
    exact ⟨c, a, ha.symm ▸ hz⟩
  · rintro ⟨c, a, ha⟩
    exact ⟨c, BottomCut.flag (c.row sem) a, ha⟩

/-- At a unique grade-one target, all cap-compatible lawful ambients have
the same lift-existence answer: the prescription's n+1 section-cut tests. -/
theorem lift_iff_fixed_cut_of_unique (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    (c : Controller D BJ) (hu : ∀ a : Controller D BJ, a = c)
    {X : Type*} [Fintype X] {embed : X → D.below BJ} {p : X → ExtOrd}
    {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) (hp : ∀ x, SelfVis BJ.2 (p x))
    (hγ : SelfVis BJ.2 γ)
    (hag : ∀ x, min (q (embed x)) γ = min (p x) γ) :
    HasLift (sem := sem) embed p q γ ↔
      ∃ a : Option (D.below BJ),
        BottomPattern.Check (sem := sem) c (BottomCut.flag (c.row sem) a) embed p := by
  have he : HasLift (sem := sem) embed p q γ ↔ HasLift (sem := sem) embed p q ⊥ := by
    rw [lift_iff_section_of_unique hc hgrade c hu hq hγ hag,
      lift_iff_section_of_unique hc hgrade c hu hq (selfVis_bot _) (by simp)]
  rw [he, bottom_lift_iff_exists_cut hc hgrade c hp]
  constructor
  · rintro ⟨b, a, ha⟩
    exact ⟨a, hu b ▸ ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨c, a, ha⟩

end Semantic

namespace Executable.Data

variable {X Y C : Type*} [Fintype X] [Fintype Y] [Fintype C] [DecidableEq Y]

/-- Only the n+1 initial-segment bottom patterns are needed. The positive
branch is unchanged; the external bottom cap is never replaced by the seed. -/
def cutLiftCheck (T : Data Y C) (embed : X → Y) (p : X → ℕ) (q : Y → ℕ) (γ : ℕ) : Bool :=
  if γ = 0 then
    decide (∃ c, ∃ a : Option Y,
      Propagation.Check (T.source c) embed p (seed (BottomCut.flag (T.source c) a)) 1 ∧
        T.Blocks (seed (BottomCut.flag (T.source c) a)))
  else decide (∃ c, Propagation.Check (T.source c) embed p q γ)

/-- Equality holds for all raw finite data, not merely semantically lawful
inputs. The old nested block tests are transported without changing flags. -/
theorem cutLiftCheck_eq
    (T : Data Y C) (embed : X → Y) (p : X → ℕ) (q : Y → ℕ) (γ : ℕ) :
    T.cutLiftCheck embed p q γ = T.liftCheck embed p q γ := by
  rw [← fastLiftCheck_eq]
  unfold cutLiftCheck fastLiftCheck
  by_cases hγ : γ = 0
  · simp only [hγ, ↓reduceIte]
    congr 1
    apply propext
    constructor
    · rintro ⟨c, a, ha⟩
      exact ⟨c, BottomCut.flag (T.source c) a, ha⟩
    · rintro ⟨c, z, hz⟩
      obtain ⟨a, ha⟩ := BottomCut.flag_of_check (by decide : (1 : ℕ) ≠ ⊥) hz.1
      exact ⟨c, a, ha.symm ▸ hz⟩
  · simp only [hγ, ↓reduceIte]

/-- The universal checker with the same input domain, now using cut branches. -/
def cutUniversalCheck [DecidableEq X] {B : Type*} [Fintype B]
    (P : Data X B) (T : Data Y C) (embed : X → Y) (N : ℕ) : Bool :=
  decide (∀ (q : Y → Fin (N + 1)), T.Respect (fun y => (q y).val) →
    ∀ (p : X → Fin (N + 1)), P.Respect (fun x => (p x).val) →
    ∀ (γ : Fin (N + 1)),
      (∀ x, min (q (embed x)).val γ.val = min (p x).val γ.val) →
      T.cutLiftCheck embed (fun x => (p x).val) (fun y => (q y).val) γ.val = true)

theorem cutUniversalCheck_eq [DecidableEq X]
    {B : Type*} [Fintype B] (P : Data X B) (T : Data Y C) (embed : X → Y) (N : ℕ) :
    cutUniversalCheck P T embed N = universalCheck P T embed N := by
  rw [← screenedCheck_eq]
  simp only [cutUniversalCheck, screenedCheck, cutLiftCheck_eq, fastLiftCheck_eq]

end Executable.Data

end VaughtConjecture.Knight.FullRowLifting
