/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FullRowLifting

/-! # Whole-face coverage and the ambient's inactive occurrences

The tower-independent acceptance theorem keeps the actual dominating controller
label and every protected occurrence. The stronger row query also pins every
ambient occurrence below the external cap, including those outside the face.
Its cap equations are exactly literal reads at inactive occurrences and lower
bounds at active ones. A source-order obstruction between these occurrences
rejects a whole row query, not just a proposed off-row interpolation formula.

None of the source-order filters below is advertised as sufficient.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

/-- Generic whole-face acceptance, with the actual self-visible controller cap.
In fact the same controller represents the entire target, not just the face.
The protected set need not be a face and the ambient need not be assumed lawful. -/
theorem active_coverage_of_lift (hgrade : BJ.2 = 1) (c₀ : Controller D BJ)
    {X : Type*} {embed : X → D.below BJ} {p : X → ExtOrd}
    {q : D.below BJ → ExtOrd} {γ : ExtOrd} (hreaches : ∃ x, γ ≤ p x)
    (h : HasLift (sem := sem) embed p q γ) :
    ∃ c : Controller D BJ, γ ≤ q c.here ∧
      ∃ κ : ExtOrd, SelfVis BJ.2 κ ∧ (∀ x, p x ≤ κ) ∧
        ∃ τ : ExtOrd → ExtOrd, Witness (gTop BJ.2) τ ∧
          (∀ t, τ t ≤ κ) ∧ τ (c.row sem c.here) = κ ∧
          Boundary embed p q γ (fun d => τ (c.row sem d)) ∧
          TransformsTo (fun x => D.grade (embed x).1) (fun x => c.row sem (embed x)) p := by
  obtain ⟨r, hr, hcap, hread⟩ := h
  obtain ⟨c, τ, hτ, hb, he⟩ := exists_full_row_representation hgrade c₀ hr
  have hdom : ∀ x, p x ≤ r c.here := fun x =>
    (hread x).symm ▸ ((he (embed x)) ▸ hb (c.row sem (embed x)))
  have hact : γ ≤ q c.here := by
    obtain ⟨x, hx⟩ := hreaches
    have hh := hcap c.here
    rw [min_eq_right (hx.trans (hdom x))] at hh
    exact min_eq_right_iff.mp hh.symm
  refine ⟨c, hact, r c.here, ?_, hdom, τ, hτ, hb, he c.here, ?_, ?_⟩
  · have hv : SelfVis (D.grade c.here.1) (r c.here) := (hr.orderly c.here).symm
    rw [c.grade_here] at hv
    exact hv
  · exact (funext he).symm ▸ And.intro hcap hread
  · apply hτ.transformsTo
    intro x
    have hg : D.grade (embed x).1 ≤ BJ.2 := (embed x).2.2
    rw [gTop_of_le hg, min_top_right, he, hread]

section Scalar

variable {α : Type*} [LinearOrder α]

/-- Cap agreement is literal below the cap and only a lower bound at or above it. -/
theorem cap_eq_iff_profile (r q γ : α) :
    min r γ = min q γ ↔ (q < γ → r = q) ∧ (γ ≤ q → γ ≤ r) := by
  constructor
  · intro h
    constructor
    · intro hq
      have hr : r < γ := by
        by_contra hn
        rw [min_eq_right (not_lt.mp hn), min_eq_left hq.le] at h
        exact (ne_of_lt hq) h.symm
      simpa only [min_eq_left hr.le, min_eq_left hq.le] using h
    · intro hq
      rw [min_eq_right hq] at h
      exact min_eq_right_iff.mp h
  · rintro ⟨hlo, hhi⟩
    rcases lt_or_ge q γ with h | h
    · rw [hlo h]
    · rw [min_eq_right (hhi h), min_eq_right h]

end Scalar

/-- Every cap equation can be expanded without changing the query. Protected
reads remain literal even where the prescription exceeds the cap. -/
theorem boundary_iff_profile {X : Type*} (embed : X → D.below BJ) (p : X → ExtOrd)
    (q : D.below BJ → ExtOrd) (γ : ExtOrd) (r : D.below BJ → ExtOrd) :
    Boundary embed p q γ r ↔
      (∀ d, q d < γ → r d = q d) ∧ (∀ d, γ ≤ q d → γ ≤ r d) ∧
        ∀ x, r (embed x) = p x := by
  constructor
  · rintro ⟨hc, hp⟩
    exact ⟨fun d => ((cap_eq_iff_profile _ _ _).mp (hc d)).1,
      fun d => ((cap_eq_iff_profile _ _ _).mp (hc d)).2, hp⟩
  · rintro ⟨hlo, hhi, hp⟩
    exact ⟨fun d => (cap_eq_iff_profile _ _ _).mpr ⟨hlo d, hhi d⟩, hp⟩

/-- Any pinned inactive occurrence must be strictly before a protected occurrence
at or above the cap in the chosen row's source order. The occurrence may lie
outside the face, and no comparison of graded indices substitutes for this test. -/
theorem source_lt_of_inactive_boundary {X : Type*} {embed : X → D.below BJ}
    {p : X → ExtOrd} {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    {c : Controller D BJ} {τ : ExtOrd → ExtOrd} (hτ : Monotone τ)
    (hb : Boundary embed p q γ (fun d => τ (c.row sem d)))
    {d : D.below BJ} {x : X} (hd : q d < γ) (hx : γ ≤ p x) :
    c.row sem d < c.row sem (embed x) := by
  have hfixed := ((boundary_iff_profile embed p q γ _).mp hb).1 d hd
  apply lt_of_not_ge
  intro hrev
  have hh := hτ hrev
  have hp : τ (c.row sem (embed x)) = p x := hb.2 x
  rw [hp, hfixed] at hh
  exact (not_le_of_gt (hd.trans_le hx)) hh

/-- A finite-style source-order rejection for the entire existential row query.
Each possible controller may have its own obstructing pair. It refutes every
faithful witness for that controller, not merely a chosen table. -/
theorem no_rowQuery_of_inactive_collision {X : Type*} {embed : X → D.below BJ}
    {p : X → ExtOrd} {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hbad : ∀ c : Controller D BJ, ∃ d : D.below BJ, ∃ x : X,
      q d < γ ∧ γ ≤ p x ∧ c.row sem (embed x) ≤ c.row sem d) :
    ¬ RowQuery (sem := sem) embed p q γ := by
  rintro ⟨c, τ, hτ, hb⟩
  obtain ⟨d, x, hd, hx, hrev⟩ := hbad c
  exact (not_le_of_gt (source_lt_of_inactive_boundary hτ.mono hb hd hx)) hrev

/-- Semantic impossibility from the source-order rejection, with no consistency
assumption. Grade one and an inhabited full target are used only for necessity. -/
theorem no_lift_of_inactive_collision (hgrade : BJ.2 = 1) (c₀ : Controller D BJ)
    {X : Type*} {embed : X → D.below BJ} {p : X → ExtOrd}
    {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hbad : ∀ c : Controller D BJ, ∃ d : D.below BJ, ∃ x : X,
      q d < γ ∧ γ ≤ p x ∧ c.row sem (embed x) ≤ c.row sem d) :
    ¬ HasLift (sem := sem) embed p q γ :=
  fun h => no_rowQuery_of_inactive_collision hbad (rowQuery_of_lift hgrade c₀ h)

end VaughtConjecture.Knight.FullRowLifting
