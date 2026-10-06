/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TwoPointSlots

/-! # Literal two-point faces of the next three-point boundary

The nine occurrences are three singletons, two controllers on each of the
faces `{0,1}` and `{1,2}`, and one mute cell on each face. Both faces are the
actual complete bountiful two-point domain, not a single source profile.

This module supplies simultaneous proper-face sections and original-cap
retuning, retaining every controller occurrence. Full-scope rows and a legal
three-point extension are not supplied by this boundary predicate.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ThreePointSlotBoundary

open Transform Value ExtOrd

def left : Fin 5 → Fin 9 := ![0, 1, 3, 4, 7]
def right : Fin 5 → Fin 9 := ![1, 2, 5, 6, 8]

theorem left_injective : Function.Injective left := by decide
theorem right_injective : Function.Injective right := by decide

/-- Only the shared singleton is identified; the four controllers remain distinct. -/
theorem overlap (d e : Fin 5) : left d = right e ↔ d = 1 ∧ e = 0 := by
  fin_cases d <;> fin_cases e <;> decide

theorem covered (d : Fin 9) : (∃ e, left e = d) ∨ ∃ e, right e = d := by
  fin_cases d <;> decide

def Lawful (p : Fin 9 → ExtOrd) : Prop :=
  RespectsSemantics TwoPointSlots.rows (p ∘ left) ∧
  RespectsSemantics TwoPointSlots.rows (p ∘ right)

theorem Lawful.visible {p : Fin 9 → ExtOrd} (hp : Lawful p) (d : Fin 9) :
    SelfVis 1 (p d) := by
  have hg : ∀ e : Fin 5, 1 ≤ TwoPointSlots.scheme.grade e := by decide
  rcases covered d with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · exact selfVis_mono (hp.1.orderly e).symm (hg e)
  · exact selfVis_mono (hp.2.orderly e).symm (hg e)

def join (p q : Fin 5 → ExtOrd) : Fin 9 → ExtOrd :=
  ![p 0, p 1, q 1, p 2, p 3, q 2, q 3, p 4, q 4]

theorem join_left (p q : Fin 5 → ExtOrd) (d : Fin 5) : join p q (left d) = p d := by
  fin_cases d <;> rfl

theorem join_right {p q : Fin 5 → ExtOrd} (h : p 1 = q 0) (d : Fin 5) :
    join p q (right d) = q d := by
  fin_cases d
  · exact h
  all_goals rfl

theorem join_lawful {p q : Fin 5 → ExtOrd}
    (hp : RespectsSemantics TwoPointSlots.rows p)
    (hq : RespectsSemantics TwoPointSlots.rows q) (h : p 1 = q 0) : Lawful (join p q) := by
  constructor
  · have he : join p q ∘ left = p := funext (join_left p q)
    rwa [he]
  · have he : join p q ∘ right = q := funext (join_right h)
    rwa [he]

/-- Simultaneous lawful faces require exactly their literal overlap equality.
All auxiliary labels on both faces are part of the prescription. -/
theorem section_iff {p q : Fin 5 → ExtOrd}
    (hp : RespectsSemantics TwoPointSlots.rows p)
    (hq : RespectsSemantics TwoPointSlots.rows q) :
    (∃ r, Lawful r ∧ (∀ d, r (left d) = p d) ∧ (∀ d, r (right d) = q d)) ↔
      p 1 = q 0 := by
  constructor
  · rintro ⟨r, _, hl, hr⟩
    exact (hl 1).symm.trans (hr 0)
  · intro h
    exact ⟨join p q, join_lawful hp hq h, join_left p q, join_right h⟩

/-- A whole lawful left face extends with an arbitrary independent third
singleton. Neither of the left face's controller choices is changed. -/
theorem extend_face {p : Fin 5 → ExtOrd} (hp : RespectsSemantics TwoPointSlots.rows p)
    {v : ExtOrd} (hv : SelfVis 1 v) :
    ∃ r, Lawful r ∧ (∀ d, r (left d) = p d) ∧ r 2 = v := by
  have hu : SelfVis 1 (p 1) := (hp.orderly 1).symm
  obtain ⟨q, hq, h0, h1, _⟩ := TwoPointSlots.sections hu hv
    (selfVis_max hu hv) (le_max_left _ _) (le_max_right _ _)
  exact ⟨join p q, join_lawful hp hq h0.symm, join_left p q, h1⟩

/-- Simultaneously retune the left face and third singleton against an
arbitrary lawful boundary ambient. Every right-face auxiliary retains its
original capped value; the ambient is not assumed to have a full extension. -/
theorem capped_extend_face {a : Fin 9 → ExtOrd} (ha : Lawful a)
    {p : Fin 5 → ExtOrd} (hp : RespectsSemantics TwoPointSlots.rows p)
    {v γ : ExtOrd} (hv : SelfVis 1 v) (hγ : SelfVis 1 γ)
    (hl : ∀ d, min (p d) γ = min (a (left d)) γ)
    (hvag : min v γ = min (a 2) γ) :
    ∃ r, Lawful r ∧ (∀ d, r (left d) = p d) ∧ r 2 = v ∧
      ∀ d, min (r d) γ = min (a d) γ := by
  have hu : SelfVis 1 (p 1) := (hp.orderly 1).symm
  obtain ⟨q, hq, h0, h1, hc⟩ := TwoPointSlots.simultaneous_lift
    (by decide : 1 ≤ 2) (ha.2.toBelow (Finset.univ, 2)) hu hv hγ
    (by simpa [TwoPointSlots.low, TwoPointSlots.embed, DonorSlotAssembly.old,
      right, left, Function.comp_def] using (hl 1).symm)
    (by simpa [TwoPointSlots.low, TwoPointSlots.embed, DonorSlotAssembly.fresh,
      right, Function.comp_def] using hvag.symm)
  refine ⟨join p q, join_lawful hp hq h0.symm, join_left p q, h1, ?_⟩
  intro d
  rcases covered d with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · rw [join_left]
    exact hl e
  · rw [join_right h0.symm]
    have he : GradedLe (TwoPointSlots.scheme.cell e) (Finset.univ, 2) := by
      have hh : ∀ e : Fin 5,
          GradedLe (TwoPointSlots.scheme.cell e) (Finset.univ, 2) := by
        unfold GradedLe
        decide
      exact hh e
    exact hc ⟨e, he⟩

end VaughtConjecture.Knight.ThreePointSlotBoundary
