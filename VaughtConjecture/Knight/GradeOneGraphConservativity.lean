/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneCutGraph

/-! # Exact preservation by no new inherited bottom consequences

Every admissible inherited cut extends if and only if the target graph
has no new bottom consequences on inherited occurrences. Consequences
are computed from bottom sources and optionally one assumed bottom
occurrence. The no-assumption case is essential.

Unlike the sufficient graph-retraction rule, this is an exact criterion
and requires no choice of a donor for each new occurrence. It composes
under literal occurrence maps. These are finite source/block statements,
not a construction of consistent rows or a uniform successor theorem.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting.CutGraph

variable {X Y S T : Type*} [LinearOrder S] [OrderBot S] [LinearOrder T] [OrderBot T]

/-- Bottom consequences with zero or one assumed bottom occurrence, always
including consequences of actual bottom sources. -/
def Rooted (E : X → S) (B : X → X → X → Prop) (a : Option X) (d : X) : Prop :=
  Forced (Edge E B) (fun e => E e = ⊥ ∨ a = some e) d

theorem rooted_self (E : X → S) (B : X → X → X → Prop) (d : X) :
    Rooted E B (some d) d := forced_self (Or.inr rfl)

/-- Every admissible bottom pattern obeys these rooted consequences. -/
theorem rooted_le {E : X → S} {B : X → X → X → Prop} {z : X → Bool}
    (hz : Closed (Edge E B) z) (hbot : ∀ d, E d = ⊥ → z d = true)
    {a : Option X} (ha : ∀ d, a = some d → z d = true)
    {d : X} (hd : Rooted E B a d) : z d = true := by
  apply forced_le hz ?_ hd
  intro e he
  exact he.elim (hbot e) (ha e)

/-- The complete set of rooted consequences is itself an admissible cut.
This gives the separating test pattern used in the necessity proof. -/
theorem rooted_cut [Finite X] (E : X → S) (B : X → X → X → Prop) (a : Option X) :
    ∃ b, Admissible E B b ∧ ∀ d, BottomCut.flag E b d = true ↔ Rooted E B a d := by
  classical
  let z : X → Bool := fun d => decide (Rooted E B a d)
  have hz : Closed (Edge E B) z := by
    intro d e he hd
    exact decide_eq_true (forced_step (of_decide_eq_true hd) he)
  obtain ⟨b, hb⟩ := exists_cut ((closed_iff E B z).mp hz).1
  refine ⟨b, ⟨?_, ?_⟩, ?_⟩
  · rw [hb]
    exact ((closed_iff E B z).mp hz).2
  · intro d hd
    rw [hb]
    exact decide_eq_true (forced_self (Or.inl hd))
  · intro d
    rw [hb]
    change decide (Rooted E B a d) = true ↔ Rooted E B a d
    exact ⟨of_decide_eq_true, decide_eq_true⟩

/-- Reflection of all inherited bottom consequences. The root `none`
tests mandatory bottom-source consequences, not an assumed bottom label. -/
def Conservative (E : X → S) (F : Y → T)
    (B : X → X → X → Prop) (C : Y → Y → Y → Prop) (embed : X → Y) : Prop :=
  ∀ (a : Option X) (d : X), Rooted F C (a.map embed) (embed d) → Rooted E B a d

/-- No new inherited consequence is exactly extension of every admissible
old cut. There is no graph-retraction or semantic-section hypothesis. -/
theorem allCuts_iff_conservative [Finite X] [Finite Y]
    (E : X → S) (F : Y → T) (B : X → X → X → Prop) (C : Y → Y → Y → Prop)
    (embed : X → Y) :
    (∀ a, Admissible E B a →
      ∃ b, Admissible F C b ∧ ∀ d, BottomCut.flag F b (embed d) = BottomCut.flag E a d) ↔
      Conservative E F B C embed := by
  constructor
  · intro hext a d hd
    obtain ⟨b, hb, hpat⟩ := rooted_cut E B a
    obtain ⟨t, ht, he⟩ := hext b hb
    have hclosed := (closed_iff F C _).mpr ⟨flag_down F t, ht.1⟩
    have hflag : BottomCut.flag F t (embed d) = true := by
      apply rooted_le hclosed ht.2 ?_ hd
      intro e heq
      cases a with
      | none => cases heq
      | some a =>
        have he' : embed a = e := Option.some.inj heq
        subst e
        rw [he a]
        exact (hpat a).mpr (rooted_self E B a)
    exact (hpat d).mp ((he d).symm.trans hflag)
  · intro h a ha
    apply (extension_iff F C embed (BottomCut.flag E a)).mpr
    have hclosed := (closed_iff E B _).mpr ⟨flag_down E a, ha.1⟩
    intro d hd
    obtain ⟨e, he, hed⟩ := hd
    rcases he with he | ⟨x, rfl, hx⟩
    · have hr : Rooted F C none (embed d) := ⟨e, Or.inl he, hed⟩
      apply rooted_le (a := none) hclosed ha.2 ?_ (h none d hr)
      intro e he
      cases he
    · have hr : Rooted F C (some (embed x)) (embed d) :=
        ⟨embed x, Or.inr rfl, hed⟩
      apply rooted_le hclosed ha.2 ?_ (h (some x) d hr)
      intro e he
      have he' : x = e := Option.some.inj he
      exact he' ▸ hx

/-- The earlier graph-retraction rule implies the exact condition, with
no finiteness needed for this implication. -/
theorem conservative_of_retraction
    (E : X → S) (F : Y → T) (B : X → X → X → Prop) (C : Y → Y → Y → Prop)
    (embed : X → Y) (π : Y → X) (hπ : ∀ d, π (embed d) = d)
    (hEdge : ∀ d e, Edge F C d e → Relation.ReflTransGen (Edge E B) (π d) (π e))
    (hBot : ∀ d, F d = ⊥ → E (π d) = ⊥) : Conservative E F B C embed := by
  intro a d hd
  obtain ⟨e, he, hed⟩ := hd
  have hp := map_reachable π hEdge hed
  rw [hπ] at hp
  refine ⟨π e, ?_, hp⟩
  rcases he with he | he
  · exact Or.inl (hBot e he)
  · cases a with
    | none => cases he
    | some a =>
      have he' : embed a = e := Option.some.inj he
      rw [← he', hπ]
      exact Or.inr rfl

/-- Consequence reflection composes, independently of any chosen retraction. -/
theorem Conservative.comp {Z U : Type*} [LinearOrder U] [OrderBot U]
    {E : X → S} {F : Y → T} {G : Z → U}
    {B : X → X → X → Prop} {C : Y → Y → Y → Prop} {H : Z → Z → Z → Prop}
    {i : X → Y} {j : Y → Z} (hi : Conservative E F B C i)
    (hj : Conservative F G C H j) : Conservative E G B H (j ∘ i) := by
  intro a d hd
  apply hi a d
  apply hj (a.map i) (i d)
  simpa only [Option.map_map, Function.comp_apply] using hd

end VaughtConjecture.Knight.FullRowLifting.CutGraph
