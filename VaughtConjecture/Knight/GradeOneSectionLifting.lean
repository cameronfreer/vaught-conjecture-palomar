/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneFiniteBountiful

/-! # Grade-one sections give capped lifts under a common full-row order

A lawful section and a lawful ambient that follow the same full-row source
order can be joined by the finite least-order closure. Positive cap agreement
retains the ambient's bottom pattern, so the existing locality-repair theorem
proves respect without assuming composition of faithful transformations.

In particular, a unique full controller makes the common-order condition
automatic. At such a grade-one target, arbitrary sections are equivalent to
unrestricted capped lifting. Every target occurrence is retained, and neither
the external cap nor any prescribed label is changed. Bottom uses the supplied
section itself. This does not identify a KVC scheme or apply to mixed grades.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

namespace Propagation

section Order

variable {X Y S L : Type*} [Fintype X] [Fintype Y]
  [LinearOrder S] [OrderBot S] [LinearOrder L] [OrderBot L]

/-- If the prescription and ambient obey one source order, cap agreement
is enough for the least closure to pass. No assumption on the cap is needed
for this purely ordered statement. -/
theorem check_of_compatible_order {E : Y → S} {embed : X → Y}
    {p : X → L} {q : Y → L} {γ : L}
    (hp : ∀ x y, E (embed x) ≤ E (embed y) → p x ≤ p y)
    (hq : ∀ d e, E d ≤ E e → q d ≤ q e)
    (hpb : ∀ x, E (embed x) = ⊥ → p x = ⊥)
    (hqb : ∀ d, E d = ⊥ → q d = ⊥)
    (hag : ∀ x, min (q (embed x)) γ = min (p x) γ) :
    Check E embed p q γ := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    apply max_le
    · apply Finset.sup_le
      intro e _
      split_ifs with he
      · exact (min_le_left _ _).trans (hq e d he)
      · exact bot_le
    · apply Finset.sup_le
      intro x _
      split_ifs with hx
      · have he : q (embed x) < γ := (hq _ _ hx).trans_lt hd
        have hpin := ((cap_eq_iff_profile _ _ _).mp (hag x).symm).1 he
        exact hpin ▸ hq _ _ hx
      · exact bot_le
  · intro x
    apply max_le
    · apply Finset.sup_le
      intro e _
      split_ifs with he
      · calc
          min (q e) γ ≤ min (q (embed x)) γ := min_le_min_right _ (hq _ _ he)
          _ = min (p x) γ := hag x
          _ ≤ p x := min_le_left _ _
      · exact bot_le
    · apply Finset.sup_le
      intro y _
      split_ifs with hy
      · exact hp y x hy
      · exact bot_le
  · intro d hd
    apply le_bot_iff.mp
    apply max_le
    · apply Finset.sup_le
      intro e _
      split_ifs with he
      · rw [hqb e (le_bot_iff.mp (he.trans_eq hd)), min_bot_left]
      · exact bot_le
    · apply Finset.sup_le
      intro x _
      split_ifs with hx
      · exact (hpb x (le_bot_iff.mp (hx.trans_eq hd))).le
      · exact bot_le

end Order

end Propagation

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ CI : Finset ι × ℕ}

noncomputable local instance (J : Finset ι × ℕ) : Fintype (D.below J) := Fintype.ofFinite _

/-- One full row whose source comparisons and bottom sources hold in every
full row. This is structural data, not an assumed existence of sections. -/
structure CommonOrder (c : Controller D BJ) : Prop where
  order : ∀ a : Controller D BJ, ∀ d e,
    c.row sem d ≤ c.row sem e → a.row sem d ≤ a.row sem e
  bottom : ∀ a : Controller D BJ, ∀ d,
    c.row sem d = ⊥ → a.row sem d = ⊥

/-- Uniqueness at this target, not global index injectivity, suffices. -/
theorem commonOrder_of_unique (c : Controller D BJ)
    (hu : ∀ a : Controller D BJ, a = c) : CommonOrder (sem := sem) c where
  order a d e h := by simpa only [hu a] using h
  bottom a d h := by simpa only [hu a] using h

/-- Every lawful labelling follows the common row order and its bottom set. -/
theorem CommonOrder.of_respects {c : Controller D BJ}
    (H : CommonOrder (sem := sem) c) (hgrade : BJ.2 = 1)
    {q : D.below BJ → ExtOrd} (hq : RespectsSemanticsBelow sem BJ q) :
    (∀ d e, c.row sem d ≤ c.row sem e → q d ≤ q e) ∧
      (∀ d, c.row sem d = ⊥ → q d = ⊥) := by
  obtain ⟨a, τ, hτ, _, he⟩ := exists_full_row_representation hgrade c hq
  constructor
  · intro d e hde
    rw [← he d, ← he e]
    exact hτ.mono (H.order a d e hde)
  · intro d hd
    rw [← he d, H.bottom a d hd, hτ.bot]

/-- Any lawful section gives a cap-preserving lift against any compatible
lawful ambient under the common-order condition. The protected map is arbitrary;
it need not be injective or enumerate an entire face. -/
theorem lift_of_section_commonOrder (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    {c : Controller D BJ} (H : CommonOrder (sem := sem) c)
    {X : Type*} [Finite X] {embed : X → D.below BJ} {p : X → ExtOrd}
    {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) (hγ : SelfVis BJ.2 γ)
    (hag : ∀ x, min (q (embed x)) γ = min (p x) γ)
    (hs : ∃ s, RespectsSemanticsBelow sem BJ s ∧ ∀ x, s (embed x) = p x) :
    HasLift (sem := sem) embed p q γ := by
  let := Fintype.ofFinite X
  obtain ⟨s, hs, hsp⟩ := hs
  by_cases hb : γ = ⊥
  · exact ⟨s, hs, by simp [hb], hsp⟩
  obtain ⟨hsord, hsbot⟩ := H.of_respects hgrade hs
  obtain ⟨hqord, hqbot⟩ := H.of_respects hgrade hq
  have hpord : ∀ x y, c.row sem (embed x) ≤ c.row sem (embed y) → p x ≤ p y := by
    intro x y hxy
    rw [← hsp x, ← hsp y]
    exact hsord _ _ hxy
  have hpbot : ∀ x, c.row sem (embed x) = ⊥ → p x = ⊥ := by
    intro x hx
    rw [← hsp x]
    exact hsbot _ hx
  have hpvis : ∀ x, SelfVis BJ.2 (p x) := by
    intro x
    have hv : SelfVis (D.grade (embed x).1) (s (embed x)) := (hs.orderly (embed x)).symm
    rw [grade_eq_one hgrade (embed x), hsp x, ← hgrade] at hv
    exact hv
  exact ⟨_, least_lift_of_check hc hgrade hq hpvis hγ hb c
    (Propagation.check_of_compatible_order hpord hqord hpbot hqbot hag)⟩

/-- At a unique grade-one target the only existence obligation is a section. -/
theorem lift_iff_section_of_unique (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    (c : Controller D BJ) (hu : ∀ a : Controller D BJ, a = c)
    {X : Type*} [Finite X] {embed : X → D.below BJ} {p : X → ExtOrd}
    {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) (hγ : SelfVis BJ.2 γ)
    (hag : ∀ x, min (q (embed x)) γ = min (p x) γ) :
    HasLift (sem := sem) embed p q γ ↔
      ∃ s, RespectsSemanticsBelow sem BJ s ∧ ∀ x, s (embed x) = p x := by
  constructor
  · rintro ⟨s, hs, _, hsp⟩
    exact ⟨s, hs, hsp⟩
  · exact lift_of_section_commonOrder hc hgrade (commonOrder_of_unique c hu) hq hγ hag

/-- The full literal clause reduces to arbitrary lawful face sections.
The reverse implication uses an actual consistent row at bottom cap. -/
theorem liftsAt_iff_sections_of_unique (hc : sem.IsConsistent) (h : GradedLe CI BJ)
    (hgrade : BJ.2 = 1) (c : Controller D BJ) (hu : ∀ a : Controller D BJ, a = c) :
    LiftsAt sem h ↔ ∀ p : D.below CI → ExtOrd,
      RespectsSemanticsBelow sem CI p → ∃ s, RespectsSemanticsBelow sem BJ s ∧
        ∀ x, s (CellScheme.below.mono h x) = p x := by
  constructor
  · intro hl p hp
    obtain ⟨s, hs, _, hsp⟩ := hl p (c.row sem) ⊥ hp (c.row_respects hc)
      (selfVis_bot _) (by simp)
    exact ⟨s, hs, hsp⟩
  · intro hsec p q γ hp hq hγ hag
    exact (lift_iff_section_of_unique hc hgrade c hu hq hγ hag).mpr (hsec p hp)

/-- Source information at a face: comparisons and bottom reads required by
the target row are already required by the face row. No label appears here. -/
structure RowTrace (h : GradedLe CI BJ) (b : Controller D CI) (c : Controller D BJ) : Prop where
  order : ∀ d e, c.row sem (CellScheme.below.mono h d) ≤
    c.row sem (CellScheme.below.mono h e) → b.row sem d ≤ b.row sem e
  bottom : ∀ d, c.row sem (CellScheme.below.mono h d) = ⊥ → b.row sem d = ⊥

/-- Literal restriction of the row supplies the trace condition. This is the
form used by a family of mixed rows obtained by restricting one donor row. -/
theorem rowTrace_of_restriction (h : GradedLe CI BJ)
    (b : Controller D CI) (c : Controller D BJ)
    (he : ∀ d, c.row sem (CellScheme.below.mono h d) = b.row sem d) :
    RowTrace (sem := sem) h b c where
  order d e hd := by simpa only [he] using hd
  bottom d hd := by simpa only [he] using hd

/-- Positive-cap lifting follows directly from structural row traces and
common full-row orders on the face and target. No face-completion hypothesis
is required. Bottom-cap sections remain a separate obligation. -/
theorem positive_lift_of_rowTrace (hc : sem.IsConsistent) (h : GradedLe CI BJ)
    (hface : CI.2 = 1) (htarget : BJ.2 = 1)
    {b : Controller D CI} {c : Controller D BJ}
    (Hb : CommonOrder (sem := sem) b) (Hc : CommonOrder (sem := sem) c)
    (Ht : RowTrace (sem := sem) h b c)
    {p : D.below CI → ExtOrd} {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hp : RespectsSemanticsBelow sem CI p) (hq : RespectsSemanticsBelow sem BJ q)
    (hγ : SelfVis BJ.2 γ) (hne : γ ≠ ⊥)
    (hag : ∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    HasLift (sem := sem) (CellScheme.below.mono h) p q γ := by
  obtain ⟨hpo, hpb⟩ := Hb.of_respects hface hp
  obtain ⟨hqo, hqb⟩ := Hc.of_respects htarget hq
  have hv : ∀ d, SelfVis BJ.2 (p d) := by
    intro d
    have hh : SelfVis (D.grade d.1) (p d) := (hp.orderly d).symm
    rwa [grade_eq_one hface d, ← htarget] at hh
  exact ⟨_, least_lift_of_check hc htarget hq hv hγ hne c
    (Propagation.check_of_compatible_order
      (fun d e he => hpo d e (Ht.order d e he)) hqo
      (fun d he => hpb d (Ht.bottom d he)) hqb hag)⟩

/-- Structural index injectivity supplies the unique-controller specialization. -/
theorem liftsAt_iff_sections_of_cell_injective (hc : sem.IsConsistent)
    (hinj : Function.Injective D.cell) (h : GradedLe CI BJ)
    (hgrade : BJ.2 = 1) (c : Controller D BJ) :
    LiftsAt sem h ↔ ∀ p : D.below CI → ExtOrd,
      RespectsSemanticsBelow sem CI p → ∃ s, RespectsSemanticsBelow sem BJ s ∧
        ∀ x, s (CellScheme.below.mono h x) = p x :=
  liftsAt_iff_sections_of_unique hc h hgrade c
    (fun a => Subtype.ext (hinj (a.2.trans c.2.symm)))

end VaughtConjecture.Knight.FullRowLifting
