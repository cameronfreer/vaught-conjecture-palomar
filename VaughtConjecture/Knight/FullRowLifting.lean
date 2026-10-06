/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import Mathlib.Data.Fintype.Lattice

/-! # Grade-one lifting as a single full-row witness problem

At an inhabited grade-one target, availability gives a full-index controller
dominating every value of any respecting labelling. Its locality, normalized
to an exact bounded witness, represents the entire labelling as a scalar image
of that controller's row. No index injectivity or tower presentation is used.

For consistent rows and a lawful ambient, a positive-cap lift is therefore
equivalent to one full-row witness satisfying the literal protected reads and
ALL target-occurrence cap equations. These equations supply the bottom-pattern
test needed to repair composition; faithful transformations are not assumed
transitive. At bottom cap the source-block test is retained explicitly.

This is an exact reduction, not a producer of a controller or a witness. It
does not identify mixed-grade labellings with one dominating controller.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

/-- A cell at the actual target index, not merely somewhere below it. -/
def Controller (D : CellScheme A) (BJ : Finset ι × ℕ) :=
  {c : Cell D // D.cell c = BJ}

namespace Controller

/-- The same controller as an occurrence in the target lower domain. -/
def here (c : Controller D BJ) : D.below BJ :=
  ⟨c.1, by rw [c.2]; exact GradedLe.refl _⟩

/-- Literal row transport to its propositionally equal target domain. -/
def row (c : Controller D BJ) (sem : Semantics D) (d : D.below BJ) : ExtOrd :=
  sem.E c.1 ⟨d.1, by rw [c.2]; exact d.2⟩

theorem row_respects (c : Controller D BJ) (hc : sem.IsConsistent) :
    RespectsSemanticsBelow sem BJ (c.row sem) := by
  rcases c with ⟨c, rfl⟩
  exact hc c

theorem grade_here (c : Controller D BJ) : D.grade c.here.1 = BJ.2 :=
  congrArg Prod.snd c.2

/-- A dominating full controller gives exact readback on every occurrence,
including all other controllers, with a globally bounded faithful witness. -/
theorem represents {q : D.below BJ → ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) (c : Controller D BJ)
    (hdom : ∀ d, q d ≤ q c.here) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop BJ.2) τ ∧
      (∀ x, τ x ≤ q c.here) ∧ (∀ d, τ (c.row sem d) = q d) := by
  let pc : D.below (D.cell c.1) → ExtOrd :=
    fun d => q (CellScheme.below.incl c.here d)
  let self : D.below (D.cell c.1) := ⟨c.1, GradedLe.refl _⟩
  have hv : SelfVis (D.grade self.1) (pc self) := (hq.orderly c.here).symm
  obtain ⟨τ, hτ, hb, hr⟩ := exists_bounded_exact_capped_witness
    (c := self) (fun d => d.2.2) hv (hq.locality c.here)
  refine ⟨τ, ?_, hb, ?_⟩
  · have hg : D.grade self.1 = BJ.2 := c.grade_here
    change Witness (gTop (D.grade self.1)) τ at hτ
    rwa [hg] at hτ
  · intro d
    let e : D.below (D.cell c.1) := ⟨d.1, by rw [c.2]; exact d.2⟩
    have he := hr e
    change τ (c.row sem d) = min (q d) (q c.here) at he
    exact he.trans (min_eq_left (hdom d))

end Controller

/-- All cells of a grade-one lower domain have grade one. -/
theorem grade_eq_one (hgrade : BJ.2 = 1) (d : D.below BJ) : D.grade d.1 = 1 :=
  le_antisymm (hgrade ▸ d.2.2) (D.grade_pos d.1)

/-- Availability at a maximum of the WHOLE target supplies one dominating
full controller. Neither uniqueness of indices nor a chosen branch is needed. -/
theorem exists_dominating_controller (hgrade : BJ.2 = 1)
    (c₀ : Controller D BJ) {q : D.below BJ → ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) :
    ∃ c : Controller D BJ, ∀ d, q d ≤ q c.here := by
  have : Nonempty (D.below BJ) := ⟨c₀.here⟩
  obtain ⟨dmax, hmax⟩ := Finite.exists_max q
  obtain ⟨c, hc, hle⟩ := hq.availability dmax c₀.here
    (by change D.scope dmax.1 ⊆ (D.cell c₀.1).1; rw [c₀.2]; exact dmax.2.1)
    ((grade_eq_one hgrade dmax).trans (grade_eq_one hgrade c₀.here).symm)
  refine ⟨⟨c.1, hc.trans c₀.2⟩, fun d => ?_⟩
  exact (hmax d).trans hle

/-- The single-row normal form of any lawful grade-one labelling. -/
theorem exists_full_row_representation (hgrade : BJ.2 = 1)
    (c₀ : Controller D BJ) {q : D.below BJ → ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) :
    ∃ c : Controller D BJ, ∃ τ : ExtOrd → ExtOrd,
      Witness (gTop BJ.2) τ ∧ (∀ x, τ x ≤ q c.here) ∧
      (∀ d, τ (c.row sem d) = q d) := by
  obtain ⟨c, hc⟩ := exists_dominating_controller hgrade c₀ hq
  obtain ⟨τ, hτ, hb, hr⟩ := c.represents hq hc
  exact ⟨c, τ, hτ, hb, hr⟩

/-- Literal protected values and cap agreement at EVERY target occurrence.
An arbitrary protected map is allowed; it need not be an entire face. -/
def Boundary {X : Type*} (embed : X → D.below BJ) (p : X → ExtOrd)
    (q : D.below BJ → ExtOrd) (γ : ExtOrd) (r : D.below BJ → ExtOrd) : Prop :=
  (∀ d, min (r d) γ = min (q d) γ) ∧ ∀ x, r (embed x) = p x

/-- The literal lift problem on the target lower domain. -/
def HasLift {X : Type*} (embed : X → D.below BJ) (p : X → ExtOrd)
    (q : D.below BJ → ExtOrd) (γ : ExtOrd) : Prop :=
  ∃ r, RespectsSemanticsBelow sem BJ r ∧ Boundary embed p q γ r

/-- A scalar witness query, retaining actual source occurrences and all caps.
No respect or extension-existence field is hidden in this predicate. -/
def RowQuery {X : Type*} (embed : X → D.below BJ) (p : X → ExtOrd)
    (q : D.below BJ → ExtOrd) (γ : ExtOrd) : Prop :=
  ∃ c : Controller D BJ, ∃ τ : ExtOrd → ExtOrd,
    Witness (gTop BJ.2) τ ∧ Boundary embed p q γ (fun d => τ (c.row sem d))

/-- Necessary without consistency, ambient lawfulness, or positive cap. -/
theorem rowQuery_of_lift (hgrade : BJ.2 = 1) (c₀ : Controller D BJ)
    {X : Type*} {embed : X → D.below BJ} {p : X → ExtOrd}
    {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (h : HasLift (sem := sem) embed p q γ) : RowQuery (sem := sem) embed p q γ := by
  obtain ⟨r, hr, hb⟩ := h
  obtain ⟨c, τ, hτ, _, he⟩ := exists_full_row_representation hgrade c₀ hr
  exact ⟨c, τ, hτ, (funext he).symm ▸ hb⟩

/-- At a positive cap, boundary agreement supplies the source-block bottom
condition at every nested controller. All localities and availability follow. -/
theorem lift_of_rowQuery (hc : sem.IsConsistent)
    {X : Type*} {embed : X → D.below BJ} {p : X → ExtOrd}
    {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) (hγ : γ ≠ ⊥)
    (h : RowQuery (sem := sem) embed p q γ) : HasLift (sem := sem) embed p q γ := by
  obtain ⟨c, τ, hτ, hcap, hread⟩ := h
  refine ⟨fun d => τ (c.row sem d), ?_, hcap, hread⟩
  exact map_respects_of_positive_cap_agreement (c.row_respects hc) hq
    (fun d => d.2.2) (boundedMap_of_witness hτ) hγ hcap

/-- Exact positive-cap lifting criterion for arbitrary consistent schemes at
inhabited grade-one targets. No stronger visibility of the external cap is used. -/
theorem lift_iff_rowQuery (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    (c₀ : Controller D BJ) {X : Type*} {embed : X → D.below BJ}
    {p : X → ExtOrd} {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) (hγ : γ ≠ ⊥) :
    HasLift (sem := sem) embed p q γ ↔ RowQuery (sem := sem) embed p q γ :=
  ⟨rowQuery_of_lift hgrade c₀, lift_of_rowQuery hc hq hγ⟩

/-- At any cap, including bottom, the additional source-block test is exact.
The test uses all actual nested source rows, not just the selected full row. -/
theorem lift_iff_rowQuery_with_blocks (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    (c₀ : Controller D BJ) {X : Type*} {embed : X → D.below BJ}
    {p : X → ExtOrd} {q : D.below BJ → ExtOrd} {γ : ExtOrd} :
    HasLift (sem := sem) embed p q γ ↔
    ∃ c : Controller D BJ, ∃ τ : ExtOrd → ExtOrd,
      Witness (gTop BJ.2) τ ∧
      Boundary embed p q γ (fun d => τ (c.row sem d)) ∧
      RowBlockBottom sem BJ (fun d => τ (c.row sem d)) := by
  constructor
  · rintro ⟨r, hr, hb⟩
    obtain ⟨c, τ, hτ, _, he⟩ := exists_full_row_representation hgrade c₀ hr
    refine ⟨c, τ, hτ, (funext he).symm ▸ hb, ?_⟩
    exact (funext he).symm ▸ rowBlockBottom_of_respects hr
  · rintro ⟨c, τ, hτ, hb, hblocks⟩
    exact ⟨fun d => τ (c.row sem d),
      (map_respects_iff_rowBlockBottom (c.row_respects hc) (fun d => d.2.2)
        (boundedMap_of_witness hτ)).mpr hblocks, hb⟩

/-- If every nested row is source-short at its own controller grade, composition
can be repaired structurally. Then the single-row query is exact even at bottom
cap, without an ambient-lawfulness hypothesis. This is stronger than codedness. -/
theorem lift_iff_rowQuery_of_short (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    (c₀ : Controller D BJ)
    (hshort : ∀ c : D.below BJ, ∀ d : D.below (D.cell c.1),
      Short (D.grade c.1) (sem.E c.1 d))
    {X : Type*} {embed : X → D.below BJ} {p : X → ExtOrd}
    {q : D.below BJ → ExtOrd} {γ : ExtOrd} :
    HasLift (sem := sem) embed p q γ ↔ RowQuery (sem := sem) embed p q γ := by
  refine ⟨rowQuery_of_lift hgrade c₀, ?_⟩
  rintro ⟨c, τ, hτ, hb⟩
  exact ⟨fun d => τ (c.row sem d),
    map_respects_of_short (c.row_respects hc) (fun d => d.2.2) hshort hτ, hb⟩

end VaughtConjecture.Knight.FullRowLifting
