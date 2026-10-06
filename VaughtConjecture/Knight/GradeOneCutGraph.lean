/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneCutTrace
public import VaughtConjecture.Knight.GradeOneCutExtension
public import Mathlib.Logic.Relation

/-! # Unary implication graphs for grade-one bottom cuts

In a fixed source order, the guarded block implication
`bottom d → bottom e ∨ bottom c` is unary: it forces bottom at the
source-smaller of c and e. Together with downward source-order edges,
these implications describe exactly the admissible bottom cuts.

Extension is possible exactly when reachability from the required bottom
occurrences does not reach a protected nonbottom occurrence. A retraction
of the new implication graph into the old reachability relation proves
preservation, without assuming sections or choosing ordinal output labels.

These are grade-one structural results. A source/block table must still
be identified with the actual consistent semantics before the semantic
corollary applies. No new geometry or general successor is constructed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd

namespace CutGraph

variable {X Y S : Type*} [LinearOrder S]

/-- Select an occurrence, not a quotient source class. -/
def lower (E : Y → S) (c e : Y) : Y := if E c ≤ E e then c else e

theorem lower_le_left (E : Y → S) (c e : Y) : E (lower E c e) ≤ E c := by
  unfold lower
  split_ifs with h
  · exact le_rfl
  · exact le_of_lt (lt_of_not_ge h)

theorem lower_le_right (E : Y → S) (c e : Y) : E (lower E c e) ≤ E e := by
  unfold lower
  split_ifs with h
  · exact h
  · exact le_rfl

/-- Downward source propagation and one unary edge per actual block triple. -/
def Edge (E : Y → S) (B : Y → Y → Y → Prop) (d e : Y) : Prop :=
  E e ≤ E d ∨ ∃ c f, B c d f ∧ e = lower E c f

/-- Bottom flags are downward closed in the full source order. -/
def Down (E : Y → S) (z : Y → Bool) : Prop :=
  ∀ d e, E e ≤ E d → z d = true → z e = true

/-- Closed under unary bottom implications. -/
def Closed (R : Y → Y → Prop) (z : Y → Bool) : Prop :=
  ∀ d e, R d e → z d = true → z e = true

/-- The guarded block laws become unary exactly, not merely sufficiently. -/
theorem closed_iff (E : Y → S) (B : Y → Y → Y → Prop) (z : Y → Bool) :
    Closed (Edge E B) z ↔ Down E z ∧ BottomCut.Closed B z := by
  constructor
  · intro h
    refine ⟨fun d e hd => h d e (Or.inl hd), ?_⟩
    intro c d e hb hz
    rcases hz with hd | hc
    · have hl := h d (lower E c e) (Or.inr ⟨c, e, hb, rfl⟩) hd
      unfold lower at hl
      split_ifs at hl with he
      · exact Or.inr hl
      · exact Or.inl hl
    · exact Or.inr hc
  · rintro ⟨hd, hb⟩ d e (he | ⟨c, f, hcf, rfl⟩) hz
    · exact hd d e he hz
    · rcases hb c d f hcf (Or.inl hz) with hf | hc
      · exact hd f _ (lower_le_right E c f) hf
      · exact hd c _ (lower_le_left E c f) hc

theorem flag_down (E : Y → S) (a : Option Y) : Down E (BottomCut.flag E a) := by
  intro d e he hd
  cases a with
  | none => contradiction
  | some a =>
    simp only [BottomCut.flag, decide_eq_true_eq] at hd ⊢
    exact he.trans hd

/-- The least implication-closed set containing the mandatory bottom seeds. -/
def Forced (R : Y → Y → Prop) (Z : Y → Prop) (e : Y) : Prop :=
  ∃ d, Z d ∧ Relation.ReflTransGen R d e

theorem forced_self {R : Y → Y → Prop} {Z : Y → Prop} {d : Y} (hd : Z d) :
    Forced R Z d := ⟨d, hd, .refl⟩

theorem forced_step {R : Y → Y → Prop} {Z : Y → Prop} {d e : Y}
    (hd : Forced R Z d) (hde : R d e) : Forced R Z e := by
  obtain ⟨a, ha, had⟩ := hd
  exact ⟨a, ha, had.tail hde⟩

theorem Closed.reachable {R : Y → Y → Prop} {z : Y → Bool}
    (h : Closed R z) {d e : Y} (hde : Relation.ReflTransGen R d e)
    (hd : z d = true) : z e = true := by
  induction hde with
  | refl => exact hd
  | tail _ he ih => exact h _ _ he ih

theorem forced_le {R : Y → Y → Prop} {Z : Y → Prop} {z : Y → Bool}
    (h : Closed R z) (hZ : ∀ d, Z d → z d = true) {e : Y}
    (he : Forced R Z e) : z e = true := by
  obtain ⟨d, hd, hde⟩ := he
  exact h.reachable hde (hZ d hd)

variable [OrderBot S]

/-- Required bottom sources and literal protected bottom occurrences. -/
def Seeds (E : Y → S) (embed : X → Y) (z : X → Bool) (d : Y) : Prop :=
  E d = ⊥ ∨ ∃ x, embed x = d ∧ z x = true

/-- Raw admissibility retains both block laws and bottom-source obligations. -/
def Admissible (E : Y → S) (B : Y → Y → Y → Prop) (a : Option Y) : Prop :=
  BottomCut.Closed B (BottomCut.flag E a) ∧
    ∀ d, E d = ⊥ → BottomCut.flag E a d = true

omit [OrderBot S] in
/-- Every downward Boolean pattern on a finite source inventory is an
actual source cut; no distinct occurrences are identified. -/
theorem exists_cut [Finite Y] {E : Y → S} {z : Y → Bool} (hz : Down E z) :
    ∃ a : Option Y, BottomCut.flag E a = z := by
  have ho : ∀ d e, E d ≤ E e → BottomPattern.seed z d ≤ BottomPattern.seed z e := by
    intro d e hde
    by_cases he : z e = true
    · have hd := hz e d hde he
      simp [BottomPattern.seed, hd, he]
    · simp only [BottomPattern.seed, ite_eq_right he]
      split_ifs <;> simp
  obtain ⟨a, ha⟩ := BottomCut.exists_flag ho
  exact ⟨a, funext fun d => Bool.eq_iff_iff.mpr
    ((ha d).trans (BottomPattern.seed_eq_bot z d))⟩

/-- Exact extension test: no forced bottom may leak into a protected
nonbottom occurrence. Reachability includes bottom-source seeds. -/
theorem extension_iff [Finite Y] (E : Y → S) (B : Y → Y → Y → Prop)
    (embed : X → Y) (z : X → Bool) :
    (∃ a, Admissible E B a ∧ ∀ x, BottomCut.flag E a (embed x) = z x) ↔
      ∀ x, Forced (Edge E B) (Seeds E embed z) (embed x) → z x = true := by
  constructor
  · rintro ⟨a, ha, he⟩ x hx
    rw [← he x]
    apply forced_le ((closed_iff E B _).mpr ⟨flag_down E a, ha.1⟩) ?_ hx
    intro d hd
    rcases hd with hb | ⟨x, rfl, hz⟩
    · exact ha.2 d hb
    · exact (he x).trans hz
  · intro h
    classical
    let w : Y → Bool := fun d => decide (Forced (Edge E B) (Seeds E embed z) d)
    have hw : Closed (Edge E B) w := by
      intro d e hde hd
      exact decide_eq_true (forced_step (of_decide_eq_true hd) hde)
    obtain ⟨a, ha⟩ := exists_cut ((closed_iff E B w).mp hw).1
    refine ⟨a, ⟨?_, ?_⟩, ?_⟩
    · rw [ha]
      exact ((closed_iff E B w).mp hw).2
    · intro d hd
      rw [ha]
      exact decide_eq_true (forced_self (Or.inl hd))
    · intro x
      rw [ha]
      apply Bool.eq_iff_iff.mpr
      change decide (Forced (Edge E B) (Seeds E embed z) (embed x)) = true ↔ z x = true
      rw [decide_eq_true_eq]
      exact ⟨h x, fun hx => forced_self (Or.inr ⟨x, rfl, hx⟩)⟩

variable {T : Type*} [LinearOrder T] [OrderBot T]

/-- A graph retraction preserves every admissible old cut. New edges may
map to multi-step old implications; semantic section existence is not assumed. -/
theorem extension_of_retraction [Finite Y]
    (E : X → T) (F : Y → S) (B : X → X → X → Prop) (C : Y → Y → Y → Prop)
    (embed : X → Y) (π : Y → X) (hπ : ∀ x, π (embed x) = x)
    (hEdge : ∀ d e, Edge F C d e → Relation.ReflTransGen (Edge E B) (π d) (π e))
    (hBot : ∀ d, F d = ⊥ → E (π d) = ⊥)
    (a : Option X) (ha : Admissible E B a) :
    ∃ t, Admissible F C t ∧ ∀ x, BottomCut.flag F t (embed x) = BottomCut.flag E a x := by
  apply (extension_iff F C embed (BottomCut.flag E a)).mpr
  have ho := (closed_iff E B _).mpr ⟨flag_down E a, ha.1⟩
  have hn : Closed (Edge F C) (fun d => BottomCut.flag E a (π d)) :=
    fun d e hd => ho.reachable (hEdge d e hd)
  intro x hx
  have hh := forced_le hn (fun d hd => ?_) hx
  · simpa only [hπ] using hh
  · rcases hd with hb | ⟨x, rfl, hz⟩
    · exact ha.2 _ (hBot d hb)
    · simpa only [hπ] using hz

/-- Graph retractions compose at the implication level. This transports
paths, not faithful transformations. -/
theorem map_reachable {U V : Type*} {R : U → U → Prop} {R' : V → V → Prop}
    (π : U → V) (hπ : ∀ d e, R d e → Relation.ReflTransGen R' (π d) (π e))
    {d e : U} (h : Relation.ReflTransGen R d e) :
    Relation.ReflTransGen R' (π d) (π e) := by
  induction h with
  | refl => exact .refl
  | tail _ he ih => exact ih.trans (hπ _ _ he)

end CutGraph

end VaughtConjecture.Knight.FullRowLifting
