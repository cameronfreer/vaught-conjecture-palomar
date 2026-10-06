/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Lattice.Lemmas
public import Mathlib.Order.Interval.Finset.Nat

/-! # Knight's finite support plans and visible faces

Ported from Knight-VC `KnightVC/Plans.lean` @ f7c7847d (plus `IsPlan.pivot_pair` from
`PaperExactPlanTraceGlue.lean`, `IsPlan.singleton_mem` from `PaperExactSingletonFaces.lean`,
and `IsPlan.step_cases` from `PaperExactBoundaryPreservation.lean`).

A **support plan** on a finite set `A` (Knight, Def. 2.1.1, "amalgamation plan") is a family
`P` of subsets of `A` — the **visible faces** — built by binary amalgamation: the plans on `∅`
and on singletons are the full powersets, and a plan on `A` with `|A| ≥ 2` is `Q ∪ R ∪ {A}`
where `Q`, `R` are plans on the two one-point erasures `A ∖ {a}`, `A ∖ {b}` (`a ≠ b`) that
both see the double erasure `A ∖ {a, b}` and agree below it.  `IsPlan A P` is an inductive
predicate, so most proofs are by induction on a derivation.

The calculus on plans:

* `restrictPlan P B := P ∩ 𝒫 B` (Def. 2.1.5) — restriction to a visible face is again a plan
  (`restrict_isPlan`);
* `gradedPlan P` (Def. 2.1.8, Knight's `P̂`) — the pairs `(B, j)` with `B ∈ P` and grade
  `0 < j ≤ |B|`, which index the cells of a cell scheme over `P`;
* transport along injections: preimage (`isPlan_comap`), image (`isPlan_image`), and the
  `Fin`-indexed partial pullback `pullbackPlan f P : Option _`, defined exactly when the range
  of `f` is a visible face, with the conditional composition law `pullbackPlan_trans`;
* existence: the canonical plan `canonicalPlan A` on a linearly ordered finite set
  (`isPlan_canonicalPlan`, `exists_isPlan`) and one-point extension (`isPlan_extend_one`);
* structure: every plan contains `∅`, every singleton, and its domain; on a domain with at
  least two points the pivots `a, b` of a step are determined by the plan (`pivot_pair`: the
  visible co-arity-one faces are exactly `A ∖ {a}` and `A ∖ {b}`); a plan on three or more
  points is never the full powerset (`isPlan_ne_powerset`).

Plans are the horizontal (finite-support) coordinate of Knight's construction
(`docs/DESIGN.md` §1); the stage types `S^α_A` of the Knight instance carry a plan on `A`,
and `pull` of the `TypeTower` is defined precisely on the visible faces of that plan. -/

@[expose] public section

namespace VaughtConjecture.AmalgamationPlan

namespace Plan

variable {α : Type*} [DecidableEq α]

/-- `IsPlan A P`: `P` is a support plan on the finite set `A` (Knight, Def. 2.1.1).

Implemented as an inductive predicate: `empty` and `singleton` are the two base plans (the full
powersets of `∅` and `{a}`), and `step` amalgamates plans `Q` on `A ∖ {a}` and `R` on
`A ∖ {b}` (`a ≠ b`) that both see `A ∖ {a, b}` and agree below it into `Q ∪ R ∪ {A}`. -/
inductive IsPlan : Finset α → Finset (Finset α) → Prop
  | empty :
      IsPlan (∅ : Finset α) {∅}
  | singleton (a : α) :
      IsPlan ({a} : Finset α) {∅, {a}}
  | step {A : Finset α} {a b : α}
      {Q R P : Finset (Finset α)}
      (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
      (hQ : IsPlan (A.erase a) Q)
      (hR : IsPlan (A.erase b) R)
      (h_inter_mem : ((A.erase a).erase b) ∈ Q ∧ ((A.erase a).erase b) ∈ R)
      (h_restr_eq : Q ∩ (((A.erase a).erase b).powerset) =
                    R ∩ (((A.erase a).erase b).powerset))
      (hP : P = Q ∪ R ∪ {A}) :
      IsPlan A P

/-- Restriction of a plan to a subset `B` of its domain (Knight, Def. 2.1.5): the visible
faces contained in `B`. -/
def restrictPlan (P : Finset (Finset α)) (B : Finset α) : Finset (Finset α) :=
  P ∩ B.powerset

/-- The graded plan `P̂` (Knight, Def. 2.1.8): the pairs `(B, j)` with `B` a visible face and
grade `0 < j ≤ |B|`.  These index the cells of a cell scheme over `P`. -/
def gradedPlan (P : Finset (Finset α)) : Finset (Finset α × ℕ) :=
  P.biUnion (fun B =>
    (Finset.Ioc 0 B.card).image (fun j => (B, j))
  )

/-- Membership in the graded plan, spelled out: the face is visible and the grade is positive
and at most the size of the face. -/
def MemGraded (P : Finset (Finset α)) (BJ : Finset α × ℕ) : Prop :=
  BJ.1 ∈ P ∧ 0 < BJ.2 ∧ BJ.2 ≤ BJ.1.card

theorem mem_gradedPlan {P : Finset (Finset α)} {BJ : Finset α × ℕ} :
    BJ ∈ gradedPlan P ↔ MemGraded P BJ := by
  unfold gradedPlan MemGraded
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_Ioc]
  constructor
  · rintro ⟨B, hBP, j, ⟨hj0, hjcard⟩, hjB⟩
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hjB
    rw [← h1, ← h2]
    exact ⟨hBP, hj0, hjcard⟩
  · rintro ⟨hBP, hj0, hjcard⟩
    exact ⟨BJ.1, hBP, BJ.2, ⟨hj0, hjcard⟩, rfl⟩

/-! ### Basic structure of a plan -/

/-- Every visible face is a subset of the domain. -/
theorem IsPlan.subset_of_mem {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) {S : Finset α} (hS : S ∈ P) : S ⊆ A := by
  induction hP with
  | empty =>
    simp only [Finset.mem_singleton] at hS
    subst hS; exact Finset.empty_subset _
  | singleton a =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl
    · exact Finset.empty_subset _
    · exact Finset.Subset.refl _
  | step ha hb hab hQ hR h_inter_mem h_restr_eq hP ihQ ihR =>
    subst hP
    simp only [Finset.mem_union, Finset.mem_singleton] at hS
    rcases hS with (hS | hS) | rfl
    · exact (ihQ hS).trans (Finset.erase_subset _ _)
    · exact (ihR hS).trans (Finset.erase_subset _ _)
    · exact Finset.Subset.refl _

/-- The domain is a visible face. -/
theorem IsPlan.domain_mem {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) : A ∈ P := by
  induction hP with
  | empty => exact Finset.mem_singleton_self _
  | singleton a => simp
  | step ha hb hab hQ hR h_inter_mem h_restr_eq hP ihQ ihR =>
    subst hP; simp

/-- The empty face is visible. -/
theorem IsPlan.empty_mem {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) : ∅ ∈ P := by
  induction hP with
  | empty => exact Finset.mem_singleton_self _
  | singleton a => simp
  | step ha hb hab hQ hR h_inter_mem h_restr_eq hP ihQ ihR =>
    subst hP
    simp only [Finset.mem_union, Finset.mem_singleton]
    left; left; exact ihQ

/-- Every singleton of the domain is a visible face: a plan never drops a one-point face.
In the `step` case `P = Q ∪ R ∪ {A}`, the singleton `{x}` lives in `Q` when `x ≠ a` and in
`R` when `x = a` (then `x ≠ b`). -/
theorem IsPlan.singleton_mem {A : Finset α} {P : Finset (Finset α)} (hP : IsPlan A P)
    {x : α} (hx : x ∈ A) : {x} ∈ P := by
  induction hP with
  | empty => exact absurd hx (Finset.notMem_empty x)
  | singleton a =>
    rw [Finset.mem_singleton] at hx
    subst hx
    simp
  | @step A a b Q R P ha hb hab hQ hR h_inter_mem h_restr_eq hP ihQ ihR =>
    subst hP
    by_cases hxa : x = a
    · subst hxa
      have hxR : {x} ∈ R := ihR (Finset.mem_erase.mpr ⟨hab, hx⟩)
      simp [hxR]
    · have hxQ : {x} ∈ Q := ihQ (Finset.mem_erase.mpr ⟨hxa, hx⟩)
      simp [hxQ]

/-- Step inversion: a plan on a domain with at least two points is a `step`, with the two
pivots, the two sub-plans, and the double-erasure memberships exposed. -/
theorem IsPlan.step_cases {A : Finset α} {P : Finset (Finset α)} (hP : IsPlan A P)
    (hcard : 2 ≤ A.card) :
    ∃ (a b : α) (Q R : Finset (Finset α)), a ∈ A ∧ b ∈ A ∧ a ≠ b ∧
      IsPlan (A.erase a) Q ∧ IsPlan (A.erase b) R ∧
      (A.erase a).erase b ∈ Q ∧ (A.erase a).erase b ∈ R ∧
      P = Q ∪ R ∪ {A} := by
  cases hP with
  | empty => simp at hcard
  | singleton c => simp at hcard
  | @step A a b Q R P ha hb hab hQ hR h_inter_mem h_restr_eq hPeq =>
    exact ⟨a, b, Q, R, ha, hb, hab, hQ, hR, h_inter_mem.1, h_inter_mem.2, hPeq⟩

/-- **Pivot rigidity** (Knight-VC `PaperExactPlanTraceGlue`): for `2 ≤ |A|` the visible
co-arity-one faces `A ∖ {z}` are exactly those at the two pivots `a ≠ b` of (any) step
derivation of the plan, the double erasure `A ∖ {a, b}` is visible, and no visible face other
than `A` contains both pivots.  So the pivot pair is determined by the plan, and every step
decomposition uses it. -/
theorem IsPlan.pivot_pair {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) (hA : 2 ≤ A.card) :
    ∃ a b, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧
      (∀ z ∈ A, A.erase z ∈ P ↔ (z = a ∨ z = b)) ∧
      (A.erase a).erase b ∈ P ∧
      ∀ M ∈ P, a ∈ M → b ∈ M → M = A := by
  match hP with
  | .empty => simp at hA
  | .singleton c => simp at hA
  | .step (a := a) (b := b) ha hb hab hQ hR hmem _hre rfl =>
    refine ⟨a, b, ha, hb, hab, ?_, ?_, ?_⟩
    · intro z hz
      constructor
      · intro hzP
        rcases Finset.mem_union.mp hzP with h | h
        · rcases Finset.mem_union.mp h with hq | hr
          · left
            by_contra hne
            have haz : a ∈ A.erase z := Finset.mem_erase.mpr ⟨fun h ↦ hne h.symm, ha⟩
            exact Finset.notMem_erase a A (hQ.subset_of_mem hq haz)
          · right
            by_contra hne
            have hbz : b ∈ A.erase z := Finset.mem_erase.mpr ⟨fun h ↦ hne h.symm, hb⟩
            exact Finset.notMem_erase b A (hR.subset_of_mem hr hbz)
        · rw [Finset.mem_singleton] at h
          have hz' := Finset.notMem_erase z A
          rw [h] at hz'
          exact absurd hz hz'
      · rintro (rfl | rfl)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hQ.domain_mem)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hR.domain_mem)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hmem.1)
    · intro M hM haM hbM
      rcases Finset.mem_union.mp hM with h | h
      · rcases Finset.mem_union.mp h with hq | hr
        · exact absurd (hQ.subset_of_mem hq haM) (Finset.notMem_erase a A)
        · exact absurd (hR.subset_of_mem hr hbM) (Finset.notMem_erase b A)
      · exact Finset.mem_singleton.mp h

/-! ### Restriction -/

/-- Restriction of a plan to a visible face is again a plan (Def. 2.1.5). -/
theorem restrict_isPlan {A B : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) (hB : B ∈ P) :
    IsPlan B (restrictPlan P B) := by
  induction hP with
  | empty =>
    simp only [Finset.mem_singleton] at hB
    subst hB
    unfold restrictPlan
    simp only [Finset.powerset_empty, Finset.inter_self]
    exact IsPlan.empty
  | singleton a =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | rfl
    · unfold restrictPlan
      simp only [Finset.powerset_empty]
      have : ({∅, {a}} : Finset (Finset α)) ∩ ({∅} : Finset (Finset α)) = {∅} := by
        ext S
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨_, rfl⟩; rfl
        · intro h; exact ⟨Or.inl h, h⟩
      rw [this]
      exact IsPlan.empty
    · unfold restrictPlan
      have : ({∅, {a}} : Finset (Finset α)) ∩ ({a} : Finset α).powerset = {∅, {a}} := by
        ext S
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
                    Finset.mem_powerset]
        constructor
        · rintro ⟨h, _⟩; exact h
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, Finset.empty_subset _⟩
          · exact ⟨Or.inr rfl, Finset.Subset.refl _⟩
      rw [this]
      exact IsPlan.singleton a
  | @step A a b Q R P' ha hb hab hQ hR h_inter_mem h_restr_eq hP' ihQ ihR =>
    subst hP'
    simp only [Finset.mem_union, Finset.mem_singleton] at hB
    -- `S ⊆ A ∖ {a, b}` when `S ⊆ A ∖ {a}` and `S ⊆ A ∖ {b}`
    have sub_erase_erase : ∀ S : Finset α, S ⊆ A.erase a → S ⊆ A.erase b →
        S ⊆ (A.erase a).erase b := by
      intro S h1 h2 x hx
      rw [Finset.mem_erase]
      exact ⟨fun hxb => by rw [hxb] at hx; exact absurd (h2 hx) (Finset.notMem_erase b _),
             h1 hx⟩
    -- if `B ∈ Q` and `S ∈ R` with `S ⊆ B`, then `S ∈ Q`
    have r_to_q : ∀ S : Finset α, S ∈ R → S ⊆ B → B ∈ Q → S ∈ Q := by
      intro S hSR hSB hBQ
      have hSa : S ⊆ A.erase a := hSB.trans (hQ.subset_of_mem hBQ)
      have hSb : S ⊆ A.erase b := hR.subset_of_mem hSR
      have hSmem : S ∈ R ∩ ((A.erase a).erase b).powerset :=
        Finset.mem_inter.mpr ⟨hSR, Finset.mem_powerset.mpr (sub_erase_erase S hSa hSb)⟩
      have hSmem' : S ∈ Q ∩ ((A.erase a).erase b).powerset :=
        h_restr_eq ▸ hSmem
      exact (Finset.mem_inter.mp hSmem').1
    have q_to_r : ∀ S : Finset α, S ∈ Q → S ⊆ B → B ∈ R → S ∈ R := by
      intro S hSQ hSB hBR
      have hSa : S ⊆ A.erase a := hQ.subset_of_mem hSQ
      have hSb : S ⊆ A.erase b := hSB.trans (hR.subset_of_mem hBR)
      have hSmem : S ∈ Q ∩ ((A.erase a).erase b).powerset :=
        Finset.mem_inter.mpr ⟨hSQ, Finset.mem_powerset.mpr (sub_erase_erase S hSa hSb)⟩
      have hSmem' : S ∈ R ∩ ((A.erase a).erase b).powerset :=
        h_restr_eq ▸ hSmem
      exact (Finset.mem_inter.mp hSmem').1
    have hA_not_sub_erase_a : ¬ (A ⊆ A.erase a) := by
      intro h; exact absurd (h ha) (Finset.notMem_erase a A)
    have hA_not_sub_erase_b : ¬ (A ⊆ A.erase b) := by
      intro h; exact absurd (h hb) (Finset.notMem_erase b A)
    rcases hB with (hBQ | hBR) | rfl
    · have hrestr : restrictPlan (Q ∪ R ∪ {A}) B = restrictPlan Q B := by
        unfold restrictPlan
        ext S
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton, Finset.mem_powerset]
        constructor
        · rintro ⟨(hSQ | hSR) | rfl, hSB⟩
          · exact ⟨hSQ, hSB⟩
          · exact ⟨r_to_q S hSR hSB hBQ, hSB⟩
          · exact absurd (hSB.trans (hQ.subset_of_mem hBQ)) hA_not_sub_erase_a
        · rintro ⟨hSQ, hSB⟩
          exact ⟨Or.inl (Or.inl hSQ), hSB⟩
      rw [hrestr]
      exact ihQ hBQ
    · have hrestr : restrictPlan (Q ∪ R ∪ {A}) B = restrictPlan R B := by
        unfold restrictPlan
        ext S
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton, Finset.mem_powerset]
        constructor
        · rintro ⟨(hSQ | hSR) | rfl, hSB⟩
          · exact ⟨q_to_r S hSQ hSB hBR, hSB⟩
          · exact ⟨hSR, hSB⟩
          · exact absurd (hSB.trans (hR.subset_of_mem hBR)) hA_not_sub_erase_b
        · rintro ⟨hSR, hSB⟩
          exact ⟨Or.inl (Or.inr hSR), hSB⟩
      rw [hrestr]
      exact ihR hBR
    · have hrestr : restrictPlan (Q ∪ R ∪ {B}) B = Q ∪ R ∪ {B} := by
        unfold restrictPlan
        ext S
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton, Finset.mem_powerset]
        constructor
        · rintro ⟨h, _⟩; exact h
        · intro h
          refine ⟨h, ?_⟩
          rcases h with (hSQ | hSR) | rfl
          · exact (hQ.subset_of_mem hSQ).trans (Finset.erase_subset _ _)
          · exact (hR.subset_of_mem hSR).trans (Finset.erase_subset _ _)
          · exact Finset.Subset.refl _
      rw [hrestr]
      exact IsPlan.step ha hb hab hQ hR h_inter_mem h_restr_eq rfl

/-- In a step `P = Q ∪ R ∪ {A}` at pivots `a, b`, restricting to `A ∖ {a}` recovers `Q`. -/
private theorem restrictPlan_step_erase {A : Finset α} {a b : α}
    {Q R : Finset (Finset α)}
    (ha : a ∈ A) (hQ : IsPlan (A.erase a) Q) (hR : IsPlan (A.erase b) R)
    (h_restr_eq : Q ∩ ((A.erase a).erase b).powerset =
                  R ∩ ((A.erase a).erase b).powerset) :
    restrictPlan (Q ∪ R ∪ {A}) (A.erase a) = Q := by
  unfold restrictPlan
  ext S
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton, Finset.mem_powerset]
  constructor
  · rintro ⟨(hSQ | hSR) | rfl, hS_sub⟩
    · exact hSQ
    · have hS_ea : S ⊆ A.erase a := hS_sub
      have hS_eb : S ⊆ A.erase b := hR.subset_of_mem hSR
      have hS_eab : S ⊆ (A.erase a).erase b := by
        intro x hx
        rw [Finset.mem_erase]
        exact ⟨fun hxb => by rw [hxb] at hx; exact absurd (hS_eb hx) (Finset.notMem_erase b _),
               hS_ea hx⟩
      have : S ∈ R ∩ ((A.erase a).erase b).powerset :=
        Finset.mem_inter.mpr ⟨hSR, Finset.mem_powerset.mpr hS_eab⟩
      exact (Finset.mem_inter.mp (h_restr_eq ▸ this)).1
    · exact absurd rfl (Finset.ne_of_mem_erase (hS_sub ha))
  · intro hSQ
    exact ⟨Or.inl (Or.inl hSQ), hQ.subset_of_mem hSQ⟩

/-! ### Transport along injections -/

/-- Preimage transport: if `Q` is a plan on `B = f[A]` for an injection `f`, then
`{C ⊆ A | f[C] ∈ Q}` is a plan on `A`. -/
theorem isPlan_comap {β : Type*} [DecidableEq β]
    {B : Finset β} {Q : Finset (Finset β)}
    (hQ : IsPlan B Q) (f : α ↪ β) {A : Finset α} (hAB : A.image f = B) :
    IsPlan A (A.powerset.filter (fun C => C.image f ∈ Q)) := by
  induction hQ generalizing A with
  | empty =>
    rw [Finset.image_eq_empty] at hAB; subst hAB
    simp only [Finset.powerset_empty, Finset.filter_singleton, Finset.image_empty,
      Finset.mem_singleton, ite_true]
    exact IsPlan.empty
  | singleton b =>
    have hcard : A.card = 1 := by
      rw [← Finset.card_image_of_injective A f.injective, hAB, Finset.card_singleton]
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    simp only [Finset.image_singleton] at hAB
    have hfa : f a = b := Finset.singleton_injective hAB
    subst hfa
    have : ({a} : Finset α).powerset.filter
        (fun C => C.image f ∈ ({∅, {f a}} : Finset (Finset β))) = {∅, {a}} := by
      ext C
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hC, _⟩
        rcases Finset.subset_singleton_iff.mp hC with rfl | rfl
        · left; rfl
        · right; rfl
      · rintro (rfl | rfl)
        · exact ⟨Finset.empty_subset _, Or.inl (Finset.image_empty f)⟩
        · exact ⟨Finset.Subset.refl _, Or.inr (Finset.image_singleton f a)⟩
    rw [this]
    exact IsPlan.singleton a
  | @step B' a b Qa Qb _ ha hb hab hQa hQb h_inter_mem h_restr_eq hP ihQa ihQb =>
    subst hP
    rw [← hAB] at ha hb
    obtain ⟨a', ha'_mem, hfa'⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb'_mem, hfb'⟩ := Finset.mem_image.mp hb
    have hab' : a' ≠ b' := fun h => by subst h; exact hab (hfa' ▸ hfb')
    have img_erase_a : (A.erase a').image f = B'.erase a := by
      rw [Finset.image_erase f.injective, hAB, hfa']
    have img_erase_b : (A.erase b').image f = B'.erase b := by
      rw [Finset.image_erase f.injective, hAB, hfb']
    have ihA := ihQa img_erase_a
    have ihB := ihQb img_erase_b
    have img_erase_ab : ((A.erase a').erase b').image f = (B'.erase a).erase b := by
      rw [Finset.image_erase f.injective, img_erase_a, hfb']
    have erase_ab_mem_a : (A.erase a').erase b' ∈
        (A.erase a').powerset.filter (fun C => C.image f ∈ Qa) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.erase_subset _ _),
        img_erase_ab ▸ h_inter_mem.1⟩
    have erase_comm_ab : (A.erase a').erase b' = (A.erase b').erase a' :=
      Finset.erase_right_comm
    have erase_ab_mem_b : (A.erase b').erase a' ∈
        (A.erase b').powerset.filter (fun C => C.image f ∈ Qb) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.erase_subset _ _, ?_⟩
      rw [Finset.image_erase f.injective, img_erase_b, hfa', Finset.erase_right_comm]
      exact h_inter_mem.2
    have sub_of_img {C S : Finset α} (hCS : C.image f ⊆ S.image f) : C ⊆ S :=
      (Finset.image_subset_image_iff f.injective).mp hCS
    have restr_eq :
        (A.erase a').powerset.filter (fun C => C.image f ∈ Qa) ∩
          ((A.erase a').erase b').powerset =
        (A.erase b').powerset.filter (fun C => C.image f ∈ Qb) ∩
          ((A.erase a').erase b').powerset := by
      ext C
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨_, hCQa⟩, hCab⟩
        refine ⟨⟨?_, ?_⟩, hCab⟩
        · rw [erase_comm_ab] at hCab; exact hCab.trans (Finset.erase_subset _ _)
        · have hCimg_sub : C.image f ⊆ (B'.erase a).erase b :=
            img_erase_ab ▸ Finset.image_subset_image hCab
          have hmem : C.image f ∈ Qa ∩ ((B'.erase a).erase b).powerset :=
            Finset.mem_inter.mpr ⟨hCQa, Finset.mem_powerset.mpr hCimg_sub⟩
          exact (h_restr_eq ▸ hmem |> Finset.mem_inter.mp).1
      · rintro ⟨⟨_, hCQb⟩, hCab⟩
        refine ⟨⟨hCab.trans (Finset.erase_subset _ _), ?_⟩, hCab⟩
        have hCimg_sub : C.image f ⊆ (B'.erase a).erase b :=
          img_erase_ab ▸ Finset.image_subset_image hCab
        have hmem : C.image f ∈ Qb ∩ ((B'.erase a).erase b).powerset :=
          Finset.mem_inter.mpr ⟨hCQb, Finset.mem_powerset.mpr hCimg_sub⟩
        exact (h_restr_eq ▸ hmem |> Finset.mem_inter.mp).1
    have union_eq :
        A.powerset.filter (fun C => C.image f ∈ Qa ∪ Qb ∪ {B'}) =
        (A.erase a').powerset.filter (fun C => C.image f ∈ Qa) ∪
        (A.erase b').powerset.filter (fun C => C.image f ∈ Qb) ∪
        {A} := by
      ext C
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨hCA, (hCQa | hCQb) | hCB'⟩
        · left; left
          exact ⟨sub_of_img (img_erase_a ▸ hQa.subset_of_mem hCQa), hCQa⟩
        · left; right
          exact ⟨sub_of_img (img_erase_b ▸ hQb.subset_of_mem hCQb), hCQb⟩
        · right
          exact (Finset.image_injective f.injective).eq_iff.mp (hAB ▸ hCB')
      · rintro ((⟨hCa, hCQa⟩ | ⟨hCb, hCQb⟩) | rfl)
        · exact ⟨hCa.trans (Finset.erase_subset _ _), Or.inl (Or.inl hCQa)⟩
        · exact ⟨hCb.trans (Finset.erase_subset _ _), Or.inl (Or.inr hCQb)⟩
        · exact ⟨Finset.Subset.refl _, Or.inr hAB⟩
    rw [union_eq]
    exact IsPlan.step ha'_mem hb'_mem hab' ihA ihB
      ⟨erase_ab_mem_a, erase_comm_ab ▸ erase_ab_mem_b⟩
      restr_eq rfl

/-- Image transport: the image of a plan on `A` under an injection `f` is a plan on `f[A]`. -/
theorem isPlan_image {β : Type*} [DecidableEq β]
    {A : Finset α} {P : Finset (Finset α)} (f : α ↪ β)
    (hP : IsPlan A P) :
    IsPlan (A.image f) (P.image (Finset.image f)) := by
  induction hP with
  | empty =>
    simp only [Finset.image_empty, Finset.image_singleton]
    exact IsPlan.empty
  | singleton a =>
    simp only [Finset.image_singleton, Finset.image_insert, Finset.image_empty]
    exact IsPlan.singleton (f a)
  | @step A a b Q R P' ha hb hab hQ hR h_inter_mem h_restr_eq hP' ihQ ihR =>
    subst hP'
    have ha' : f a ∈ A.image f := Finset.mem_image_of_mem f ha
    have hb' : f b ∈ A.image f := Finset.mem_image_of_mem f hb
    have hab' : f a ≠ f b := fun h => hab (f.injective h)
    have img_erase_a : (A.erase a).image f = (A.image f).erase (f a) :=
      Finset.image_erase f.injective A a
    have img_erase_b : (A.erase b).image f = (A.image f).erase (f b) :=
      Finset.image_erase f.injective A b
    have img_erase_ab : ((A.erase a).erase b).image f =
        ((A.image f).erase (f a)).erase (f b) := by
      rw [Finset.image_erase f.injective, img_erase_a]
    have img_P : (Q ∪ R ∪ {A}).image (Finset.image f) =
        Q.image (Finset.image f) ∪ R.image (Finset.image f) ∪ {A.image f} := by
      simp only [Finset.image_union, Finset.image_singleton]
    have h_inter_mem' :
        ((A.image f).erase (f a)).erase (f b) ∈ Q.image (Finset.image f) ∧
        ((A.image f).erase (f a)).erase (f b) ∈ R.image (Finset.image f) := by
      constructor
      · rw [← img_erase_ab]; exact Finset.mem_image_of_mem _ h_inter_mem.1
      · rw [← img_erase_ab]; exact Finset.mem_image_of_mem _ h_inter_mem.2
    have h_restr_eq' :
        Q.image (Finset.image f) ∩ (((A.image f).erase (f a)).erase (f b)).powerset =
        R.image (Finset.image f) ∩ (((A.image f).erase (f a)).erase (f b)).powerset := by
      rw [← img_erase_ab]
      ext S
      simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨T, hTQ, rfl⟩, hS_sub⟩
        have hT_sub : T ⊆ (A.erase a).erase b :=
          (Finset.image_subset_image_iff f.injective).mp hS_sub
        have hT_inter : T ∈ Q ∩ ((A.erase a).erase b).powerset :=
          Finset.mem_inter.mpr ⟨hTQ, Finset.mem_powerset.mpr hT_sub⟩
        have hT_inter' : T ∈ R ∩ ((A.erase a).erase b).powerset :=
          h_restr_eq ▸ hT_inter
        exact ⟨⟨T, (Finset.mem_inter.mp hT_inter').1, rfl⟩, hS_sub⟩
      · rintro ⟨⟨T, hTR, rfl⟩, hS_sub⟩
        have hT_sub : T ⊆ (A.erase a).erase b :=
          (Finset.image_subset_image_iff f.injective).mp hS_sub
        have hT_inter : T ∈ R ∩ ((A.erase a).erase b).powerset :=
          Finset.mem_inter.mpr ⟨hTR, Finset.mem_powerset.mpr hT_sub⟩
        have hT_inter' : T ∈ Q ∩ ((A.erase a).erase b).powerset :=
          h_restr_eq ▸ hT_inter
        exact ⟨⟨T, (Finset.mem_inter.mp hT_inter').1, rfl⟩, hS_sub⟩
    rw [img_erase_a] at ihQ
    rw [img_erase_b] at ihR
    rw [img_P]
    exact IsPlan.step ha' hb' hab' ihQ ihR h_inter_mem' h_restr_eq' rfl

/-! ### `Fin`-indexed pullback -/

/-- Pullback of a plan on `Fin n` along `f : Fin m ↪ Fin n` whose range is a visible face:
`{C ⊆ Fin m | f[C] ∈ P}` is a plan on `Fin m`. -/
theorem pullback_isPlan_fin {n m : ℕ} (f : Fin m ↪ Fin n)
    {P : Finset (Finset (Fin n))} (hP : IsPlan Finset.univ P)
    (hr : Finset.univ.image f ∈ P) :
    IsPlan (Finset.univ : Finset (Fin m))
      ((Finset.univ : Finset (Fin m)).powerset.filter
        (fun C => (C.image f) ∈ P)) := by
  have hres := restrict_isPlan hP hr
  have heq : (Finset.univ : Finset (Fin m)).powerset.filter (fun C => (C.image f) ∈ P) =
      (Finset.univ : Finset (Fin m)).powerset.filter
        (fun C => (C.image f) ∈ restrictPlan P (Finset.univ.image f)) := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_powerset, restrictPlan, Finset.mem_inter,
      Finset.mem_powerset]
    constructor
    · rintro ⟨hC, hCf⟩
      exact ⟨hC, hCf, Finset.image_subset_image hC |>.trans
        (Finset.subset_univ _ |> Finset.image_subset_image)⟩
    · rintro ⟨hC, hCf, _⟩
      exact ⟨hC, hCf⟩
  rw [heq]
  exact isPlan_comap hres f (by simp)

/-- Partial pullback of a plan along an embedding of index sets (the plan-level shadow of the
`TypeTower` partial `pull`): for `f : Fin n ↪ Fin m` and `P` on `Fin m`, the pullback is
`{C ⊆ Fin n | f[C] ∈ P}` when the range `f[Fin n]` is a visible face of `P`, and `none`
otherwise. -/
def pullbackPlan {n m : ℕ} (f : Fin n ↪ Fin m) (P : Finset (Finset (Fin m))) :
    Option (Finset (Finset (Fin n))) :=
  if _ : Finset.univ.image f ∈ P then
    some ((Finset.univ : Finset (Fin n)).powerset.filter (fun C => (C.image f) ∈ P))
  else
    none

theorem pullbackPlan_eq_some {n m : ℕ} (f : Fin n ↪ Fin m) {P : Finset (Finset (Fin m))}
    (hr : Finset.univ.image f ∈ P) :
    pullbackPlan f P =
      some ((Finset.univ : Finset (Fin n)).powerset.filter (fun C => (C.image f) ∈ P)) :=
  dite_eq_left hr

theorem pullbackPlan_eq_none {n m : ℕ} (f : Fin n ↪ Fin m) {P : Finset (Finset (Fin m))}
    (hr : Finset.univ.image f ∉ P) :
    pullbackPlan f P = none :=
  dite_eq_right hr

/-- The pullback is defined exactly when the range of `f` is a visible face. -/
theorem pullbackPlan_isSome_iff {n m : ℕ} (f : Fin n ↪ Fin m) (P : Finset (Finset (Fin m))) :
    (pullbackPlan f P).isSome ↔ Finset.univ.image f ∈ P := by
  by_cases hr : Finset.univ.image f ∈ P
  · simp [pullbackPlan_eq_some f hr, hr]
  · simp [pullbackPlan_eq_none f hr, hr]

/-- A defined pullback of a plan is a plan. -/
theorem isPlan_of_pullbackPlan_eq_some {n m : ℕ} (f : Fin n ↪ Fin m)
    {P : Finset (Finset (Fin m))} (hP : IsPlan Finset.univ P)
    {Q : Finset (Finset (Fin n))} (hQ : pullbackPlan f P = some Q) :
    IsPlan Finset.univ Q := by
  by_cases hr : Finset.univ.image f ∈ P
  · rw [pullbackPlan_eq_some f hr, Option.some.injEq] at hQ
    exact hQ ▸ pullback_isPlan_fin f hP hr
  · rw [pullbackPlan_eq_none f hr] at hQ
    exact absurd hQ (by simp)

/-- Pullback along the identity is the identity on plans on `Fin n`. -/
theorem pullbackPlan_refl {n : ℕ} {P : Finset (Finset (Fin n))} (hP : IsPlan Finset.univ P) :
    pullbackPlan (Function.Embedding.refl (Fin n)) P = some P := by
  have hr : Finset.univ.image (Function.Embedding.refl (Fin n)) ∈ P := by
    simpa [Function.Embedding.coe_refl] using hP.domain_mem
  rw [pullbackPlan_eq_some _ hr]
  congr 1
  ext C
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
    Function.Embedding.coe_refl, Finset.image_id]

/-- **Conditional composition** of pullbacks (Knight, Lemma 2.1.11 style): when the
intermediate pullback `pullbackPlan g P` is defined (i.e. the range of `g` is visible), pulling
it back further along `f` agrees with the pullback along the composite `f.trans g` — including
definedness.  Nothing is asserted when the intermediate face is invisible, which is exactly the
conditional `pull_trans` law of `TypeTower`.  Holds for an arbitrary family `P`. -/
theorem pullbackPlan_trans {ℓ m n : ℕ} (f : Fin ℓ ↪ Fin m) (g : Fin m ↪ Fin n)
    {P : Finset (Finset (Fin n))} {Q : Finset (Finset (Fin m))}
    (hQ : pullbackPlan g P = some Q) :
    pullbackPlan f Q = pullbackPlan (f.trans g) P := by
  by_cases hg : Finset.univ.image g ∈ P
  · rw [pullbackPlan_eq_some g hg, Option.some.injEq] at hQ
    subst hQ
    have key : ∀ C : Finset (Fin ℓ),
        C.image f ∈ (Finset.univ : Finset (Fin m)).powerset.filter
          (fun D => D.image g ∈ P) ↔ C.image (f.trans g) ∈ P := by
      intro C
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
        Finset.image_image]
      rfl
    by_cases hf : Finset.univ.image f ∈ (Finset.univ : Finset (Fin m)).powerset.filter
        (fun D => D.image g ∈ P)
    · rw [pullbackPlan_eq_some f hf, pullbackPlan_eq_some (f.trans g) ((key _).1 hf)]
      congr 1
      ext C
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
        Finset.image_image]
      rfl
    · rw [pullbackPlan_eq_none f hf, pullbackPlan_eq_none (f.trans g) (fun h => hf ((key _).2 h))]
  · rw [pullbackPlan_eq_none g hg] at hQ
    exact absurd hQ (by simp)

/-! ### The canonical plan -/

section CanonicalPlan

variable [LinearOrder α]

/-- A canonical plan on a finite linearly ordered set, by well-founded recursion on the
cardinality: for `|A| ≤ 1` the base plans; for `|A| ≥ 2` the step at the two least elements
of `A`, recursing on the two one-point erasures. -/
noncomputable def canonicalPlan (A : Finset α) : Finset (Finset α) :=
  if _h0 : A.card = 0 then {∅}
  else if _h1 : A.card = 1 then {∅, A}
  else
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    have hne' : (A.erase (A.min' hne)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h
      have := Finset.card_erase_of_mem (Finset.min'_mem A hne)
      rw [h, Finset.card_empty] at this; omega
    canonicalPlan (A.erase (A.min' hne)) ∪
      canonicalPlan (A.erase ((A.erase (A.min' hne)).min' hne')) ∪ {A}
termination_by A.card
decreasing_by
  · rw [Finset.card_erase_of_mem (Finset.min'_mem A hne)]; omega
  · rw [Finset.card_erase_of_mem
      (Finset.mem_of_mem_erase (Finset.min'_mem (A.erase (A.min' hne)) hne'))]; omega

/-- If the least element of `B` is not `b ∈ B`, it is also the least element of `B ∖ {b}`. -/
private theorem min'_erase_of_ne {B : Finset α} (hne : B.Nonempty) {b : α}
    (hab : B.min' hne ≠ b)
    (hne_eb : (B.erase b).Nonempty) :
    (B.erase b).min' hne_eb = B.min' hne := by
  set a := B.min' hne
  have ha_in_eb : a ∈ B.erase b := Finset.mem_erase.mpr ⟨hab, Finset.min'_mem B hne⟩
  apply le_antisymm
  · exact Finset.min'_le (s := B.erase b) a ha_in_eb
  · apply Finset.le_min'
    intro y hy
    exact Finset.min'_le (s := B) y (Finset.mem_of_mem_erase hy)

/-- `canonicalPlan B` is a plan, and restricting it to the two recursive sub-domains recovers
the sub-plans (both claims are needed together for the induction). -/
private theorem isPlan_and_restrict_aux :
    ∀ n, ∀ (B : Finset α), B.card = n →
    IsPlan B (canonicalPlan B) ∧
    (B.card ≥ 2 →
      ∀ (hne : B.Nonempty) (hne' : (B.erase (B.min' hne)).Nonempty),
        restrictPlan (canonicalPlan B) (B.erase (B.min' hne)) =
          canonicalPlan (B.erase (B.min' hne)) ∧
        restrictPlan (canonicalPlan B)
          (B.erase ((B.erase (B.min' hne)).min' hne')) =
          canonicalPlan (B.erase ((B.erase (B.min' hne)).min' hne'))) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro B hBn
  by_cases h0 : n = 0
  · subst h0; have : B = ∅ := Finset.card_eq_zero.mp hBn; subst this
    exact ⟨by unfold canonicalPlan; simp only [Finset.card_empty, ↓reduceDIte]; exact IsPlan.empty,
           fun h2 => absurd h2 (by simp)⟩
  by_cases h1 : n = 1
  · subst h1; obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hBn
    exact ⟨by unfold canonicalPlan; simp only [Finset.card_singleton, one_ne_zero, ↓reduceDIte]
              exact IsPlan.singleton x,
           fun h2 => absurd h2 (by simp)⟩
  have h2 : n ≥ 2 := by omega
  have hne : B.Nonempty := Finset.card_pos.mp (by omega)
  set a := B.min' hne with ha_def
  have ha_mem : a ∈ B := Finset.min'_mem B hne
  have hne' : (B.erase a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    have := Finset.card_erase_of_mem ha_mem; rw [h, Finset.card_empty] at this; omega
  set b := (B.erase a).min' hne' with hb_def
  have hb_in_ea : b ∈ B.erase a := Finset.min'_mem (B.erase a) hne'
  have hb_mem : b ∈ B := Finset.mem_of_mem_erase hb_in_ea
  have hab : a ≠ b := fun heq => by
    have : b ∉ B.erase a := heq ▸ Finset.notMem_erase a B; exact this hb_in_ea
  set C := (B.erase a).erase b
  set Q := canonicalPlan (B.erase a) with hQ_def
  set R := canonicalPlan (B.erase b) with hR_def
  have card_ea : (B.erase a).card = n - 1 := by
    rw [Finset.card_erase_of_mem ha_mem, hBn]
  have card_eb : (B.erase b).card = n - 1 := by
    rw [Finset.card_erase_of_mem hb_mem, hBn]
  have ih_ea := ih (n - 1) (by omega) (B.erase a) card_ea
  have ih_eb := ih (n - 1) (by omega) (B.erase b) card_eb
  have hQ_plan : IsPlan (B.erase a) Q := ih_ea.1
  have hR_plan : IsPlan (B.erase b) R := ih_eb.1
  have hne_eb : (B.erase b).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; have := card_eb
    rw [h, Finset.card_empty] at this; omega
  have ha_min_eb : (B.erase b).min' hne_eb = a :=
    min'_erase_of_ne hne hab hne_eb
  have hC_comm : C = (B.erase b).erase a := Finset.erase_right_comm
  have unfold_cp : canonicalPlan B = Q ∪ R ∪ {B} := by
    change canonicalPlan B = canonicalPlan (B.erase a) ∪ canonicalPlan (B.erase b) ∪ {B}
    have h0' : ¬ B.card = 0 := by omega
    have h1' : ¬ B.card = 1 := by omega
    rw [canonicalPlan, dite_eq_right h0', dite_eq_right h1']
  have card_C : C.card = n - 2 := by
    change ((B.erase a).erase b).card = n - 2
    rw [Finset.card_erase_of_mem hb_in_ea, card_ea]; omega
  have ih_C := ih (n - 2) (by omega) C card_C
  have restrictQ_C : Q ∩ C.powerset = canonicalPlan C := by
    by_cases h_ea2 : (B.erase a).card ≥ 2
    · have hne'_ea : ((B.erase a).erase ((B.erase a).min' hne')).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro h
        have := Finset.card_erase_of_mem (Finset.min'_mem _ hne')
        rw [h, Finset.card_empty] at this; omega
      exact (ih_ea.2 h_ea2 hne' hne'_ea).1
    · have hea1 : (B.erase a).card = 1 := by omega
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hea1
      have hby : b = y := by
        have hb_in : b ∈ ({y} : Finset α) := hy ▸ hb_in_ea
        exact Finset.mem_singleton.mp hb_in
      have hQ_val : Q = ({∅, {y}} : Finset (Finset α)) := by
        change canonicalPlan (B.erase a) = _
        conv_lhs => rw [show B.erase a = {y} from hy]; unfold canonicalPlan; simp
      have hcp0 : canonicalPlan (∅ : Finset α) = {∅} := by unfold canonicalPlan; simp
      change Q ∩ ((B.erase a).erase b).powerset = canonicalPlan ((B.erase a).erase b)
      rw [show (B.erase a).erase b = (∅ : Finset α) from by rw [hby, hy, Finset.erase_singleton]]
      rw [Finset.powerset_empty, hQ_val, hcp0]
      ext S; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨Or.inl h, h⟩⟩
  have restrictR_C : R ∩ C.powerset = canonicalPlan C := by
    by_cases h_eb2 : (B.erase b).card ≥ 2
    · have hne'_eb : ((B.erase b).erase ((B.erase b).min' hne_eb)).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro h
        have := Finset.card_erase_of_mem (Finset.min'_mem _ hne_eb)
        rw [h, Finset.card_empty] at this; omega
      have hh := (ih_eb.2 h_eb2 hne_eb hne'_eb).1; rw [ha_min_eb] at hh
      rw [show (C : Finset α) = (B.erase b).erase a from hC_comm]; exact hh
    · have heb1 : (B.erase b).card = 1 := by omega
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp heb1
      have hay : a = y := by
        have ha_in : a ∈ ({y} : Finset α) := hy ▸ (ha_min_eb ▸ Finset.min'_mem _ hne_eb)
        exact Finset.mem_singleton.mp ha_in
      change R ∩ ((B.erase a).erase b).powerset = canonicalPlan ((B.erase a).erase b)
      rw [show ((B.erase a).erase b : Finset α) = (B.erase b).erase a from hC_comm,
          hay, hy, Finset.erase_singleton, Finset.powerset_empty]
      have : R = ({∅, {y}} : Finset (Finset α)) := by
        change canonicalPlan (B.erase b) = _; rw [hy]; unfold canonicalPlan; simp
      rw [this, show canonicalPlan (∅ : Finset α) = {∅} from by unfold canonicalPlan; simp]
      ext S; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨Or.inl h, h⟩⟩
  have h_restr_eq : Q ∩ C.powerset = R ∩ C.powerset := by
    rw [restrictQ_C, restrictR_C]
  have hC_mem_Q : C ∈ Q := (Finset.mem_inter.mp (restrictQ_C ▸ ih_C.1.domain_mem)).1
  have hC_mem_R : C ∈ R := (Finset.mem_inter.mp (restrictR_C ▸ ih_C.1.domain_mem)).1
  refine ⟨?_, ?_⟩
  · rw [unfold_cp]
    exact IsPlan.step ha_mem hb_mem hab hQ_plan hR_plan ⟨hC_mem_Q, hC_mem_R⟩ h_restr_eq rfl
  · intro _ hne₀ hne₀'
    have mem_C_of_mem_ea_eb : ∀ x, x ∈ B.erase a → x ∈ B.erase b → x ∈ C := by
      intro x hx_ea hx_eb
      change x ∈ (B.erase a).erase b
      refine Finset.mem_erase.mpr ⟨?_, hx_ea⟩
      exact (Finset.mem_erase.mp hx_eb).1
    have r_sub_q : ∀ S, S ∈ R → S ⊆ B.erase a → S ∈ Q := by
      intro S hSR hS_ea
      have hS_eb : S ⊆ B.erase b := hR_plan.subset_of_mem hSR
      have hS_C : S ⊆ C := fun x hx => mem_C_of_mem_ea_eb x (hS_ea hx) (hS_eb hx)
      have : S ∈ R ∩ C.powerset :=
        Finset.mem_inter.mpr ⟨hSR, Finset.mem_powerset.mpr hS_C⟩
      exact (Finset.mem_inter.mp (h_restr_eq ▸ this)).1
    have q_sub_r : ∀ S, S ∈ Q → S ⊆ B.erase b → S ∈ R := by
      intro S hSQ hS_eb
      have hS_ea : S ⊆ B.erase a := hQ_plan.subset_of_mem hSQ
      have hS_C : S ⊆ C := fun x hx => mem_C_of_mem_ea_eb x (hS_ea hx) (hS_eb hx)
      have : S ∈ Q ∩ C.powerset :=
        Finset.mem_inter.mpr ⟨hSQ, Finset.mem_powerset.mpr hS_C⟩
      exact (Finset.mem_inter.mp (h_restr_eq ▸ this)).1
    constructor
    · rw [unfold_cp]; unfold restrictPlan; ext S
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton, Finset.mem_powerset]
      constructor
      · rintro ⟨(hSQ | hSR) | rfl, hS_sub⟩
        · exact hSQ
        · exact r_sub_q S hSR hS_sub
        · exact absurd (hS_sub ha_mem) (Finset.notMem_erase a _)
      · intro hSQ; exact ⟨Or.inl (Or.inl hSQ), hQ_plan.subset_of_mem hSQ⟩
    · rw [unfold_cp]; unfold restrictPlan; ext S
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton, Finset.mem_powerset]
      constructor
      · rintro ⟨(hSQ | hSR) | rfl, hS_sub⟩
        · exact q_sub_r S hSQ hS_sub
        · exact hSR
        · exact absurd (hS_sub hb_mem) (Finset.notMem_erase b _)
      · intro hSR; exact ⟨Or.inl (Or.inr hSR), hR_plan.subset_of_mem hSR⟩

/-- `canonicalPlan A` is a support plan on `A`. -/
theorem isPlan_canonicalPlan (A : Finset α) :
    IsPlan A (canonicalPlan A) :=
  (isPlan_and_restrict_aux A.card A rfl).1

end CanonicalPlan

/-- Every finite subset of a linearly ordered type admits a support plan. -/
theorem exists_isPlan [LinearOrder α] (A : Finset α) :
    ∃ P, IsPlan A P :=
  ⟨canonicalPlan A, isPlan_canonicalPlan A⟩

/-! ### One-point extension -/

/-- One-point extension: a plan `P` on `A` and a fresh point `x ∉ A` yield a plan `Q` on
`A ∪ {x}` in which `A` is visible and whose restriction to `A` is `P`. -/
theorem isPlan_extend_one
    {A : Finset α} {P : Finset (Finset α)} {x : α}
    (hx : x ∉ A) (hP : IsPlan A P) :
    ∃ Q : Finset (Finset α),
      IsPlan (A ∪ {x}) Q ∧ A ∈ Q ∧ restrictPlan Q A = P := by
  induction hP with
  | empty =>
    refine ⟨{∅, {x}}, ?_, ?_, ?_⟩
    · rw [Finset.empty_union]; exact IsPlan.singleton x
    · simp
    · unfold restrictPlan
      simp only [Finset.powerset_empty]
      ext S
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun ⟨_, rfl⟩ => rfl, fun h => ⟨Or.inl h, h⟩⟩
  | singleton a =>
    have hax : a ≠ x := fun h => by subst h; exact hx (Finset.mem_singleton_self a)
    refine ⟨{∅, {x}} ∪ {∅, {a}} ∪ {{a} ∪ {x}}, ?_, ?_, ?_⟩
    · have ha_mem : a ∈ ({a} : Finset α) ∪ {x} :=
        Finset.mem_union_left _ (Finset.mem_singleton_self a)
      have hx_mem : x ∈ ({a} : Finset α) ∪ {x} :=
        Finset.mem_union_right _ (Finset.mem_singleton_self x)
      have h_erase_a : (({a} : Finset α) ∪ {x}).erase a = {x} := by
        rw [Finset.union_singleton, Finset.erase_insert_of_ne hax.symm,
            Finset.erase_singleton, Finset.insert_empty]
      have h_erase_x : (({a} : Finset α) ∪ {x}).erase x = {a} := by
        rw [Finset.union_singleton, Finset.erase_insert (by simpa using hax.symm)]
      have h_erase_ax : ((({a} : Finset α) ∪ {x}).erase a).erase x = ∅ := by
        rw [h_erase_a, Finset.erase_singleton]
      have h_inter_mem : ∅ ∈ ({∅, {x}} : Finset (Finset α)) ∧
          ∅ ∈ ({∅, {a}} : Finset (Finset α)) := by simp
      have h_restr : ({∅, {x}} : Finset (Finset α)) ∩ (∅ : Finset α).powerset =
          ({∅, {a}} : Finset (Finset α)) ∩ (∅ : Finset α).powerset := by
        simp only [Finset.powerset_empty]; ext S
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun ⟨_, rfl⟩ => ⟨Or.inl rfl, rfl⟩, fun ⟨_, rfl⟩ => ⟨Or.inl rfl, rfl⟩⟩
      have hQ_s : IsPlan ((({a} : Finset α) ∪ {x}).erase a) {∅, {x}} := by
        rw [h_erase_a]; exact IsPlan.singleton x
      have hR_s : IsPlan ((({a} : Finset α) ∪ {x}).erase x) {∅, {a}} := by
        rw [h_erase_x]; exact IsPlan.singleton a
      have h_inter' :
          ((({a} : Finset α) ∪ {x}).erase a).erase x ∈ ({∅, {x}} : Finset (Finset α)) ∧
          ((({a} : Finset α) ∪ {x}).erase a).erase x ∈ ({∅, {a}} : Finset (Finset α)) := by
        rw [h_erase_ax]; exact h_inter_mem
      have h_restr' : ({∅, {x}} : Finset (Finset α)) ∩
          (((({a} : Finset α) ∪ {x}).erase a).erase x).powerset =
          ({∅, {a}} : Finset (Finset α)) ∩
          (((({a} : Finset α) ∪ {x}).erase a).erase x).powerset := by
        rw [h_erase_ax]; exact h_restr
      exact IsPlan.step ha_mem hx_mem hax hQ_s hR_s h_inter' h_restr' rfl
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    · unfold restrictPlan; ext S
      constructor
      · intro hS
        have hS_mem := (Finset.mem_inter.mp hS).1
        have hS_sub := Finset.mem_powerset.mp (Finset.mem_inter.mp hS).2
        rcases Finset.mem_union.mp hS_mem with hLR | hR
        · rcases Finset.mem_union.mp hLR with hLL | hLR'
          · rcases Finset.mem_insert.mp hLL with rfl | hS_x
            · exact Finset.mem_insert_self _ _
            · exact absurd
                (hS_sub (Finset.mem_singleton.mp hS_x ▸ Finset.mem_singleton_self _)) hx
          · exact hLR'
        · exact absurd (hS_sub (Finset.mem_singleton.mp hR ▸
            Finset.mem_union_right _ (Finset.mem_singleton_self x))) hx
      · intro hS
        apply Finset.mem_inter.mpr
        constructor
        · rcases Finset.mem_insert.mp hS with rfl | hS'
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_insert_self _ _))
          · have := Finset.mem_singleton.mp hS'
            exact Finset.mem_union_left _ (Finset.mem_union_right _
              (this ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
        · rcases Finset.mem_insert.mp hS with rfl | hS'
          · exact Finset.mem_powerset.mpr (Finset.empty_subset _)
          · exact Finset.mem_powerset.mpr (Finset.mem_singleton.mp hS' ▸ Finset.Subset.refl _)
  | @step A' a b Q₀ R₀ P' ha hb hab hQ₀ hR₀ h_inter_mem h_restr_eq hP' ihQ ihR =>
    subst hP'
    have hx_ea : x ∉ A'.erase a := fun h => hx (Finset.mem_of_mem_erase h)
    obtain ⟨Qext, hQext_plan, hQext_mem, hQext_restr⟩ := ihQ hx_ea
    have hax : a ≠ x := fun h => by subst h; exact hx ha
    have h_erase_x : (A' ∪ {x}).erase x = A' := by
      rw [Finset.union_singleton, Finset.erase_insert hx]
    have h_erase_a : (A' ∪ {x}).erase a = (A'.erase a) ∪ {x} := by
      rw [Finset.union_singleton, Finset.erase_insert_of_ne hax.symm, Finset.union_singleton]
    have h_erase_xa : ((A' ∪ {x}).erase x).erase a = A'.erase a := by
      rw [h_erase_x]
    have hea_in_P : A'.erase a ∈ Q₀ ∪ R₀ ∪ {A'} :=
      Finset.mem_union_left _ (Finset.mem_union_left _ hQ₀.domain_mem)
    have hrestr_P_ea : (Q₀ ∪ R₀ ∪ {A'}) ∩ (A'.erase a).powerset = Q₀ := by
      have := restrictPlan_step_erase ha hQ₀ hR₀ h_restr_eq
      unfold restrictPlan at this; exact this
    have hQext_restr' : Qext ∩ (A'.erase a).powerset = Q₀ := by
      unfold restrictPlan at hQext_restr; exact hQext_restr
    have h_restr_eq' : (Q₀ ∪ R₀ ∪ {A'}) ∩ (A'.erase a).powerset =
        Qext ∩ (A'.erase a).powerset := by
      rw [hrestr_P_ea, hQext_restr']
    set result := (Q₀ ∪ R₀ ∪ {A'}) ∪ Qext ∪ {A' ∪ {x}} with hresult_def
    refine ⟨result, ?_, ?_, ?_⟩
    · have hx_mem : x ∈ A' ∪ {x} := Finset.mem_union_right _ (Finset.mem_singleton_self x)
      have ha_mem : a ∈ A' ∪ {x} := Finset.mem_union_left _ ha
      have hQ_sub : IsPlan ((A' ∪ {x}).erase x) (Q₀ ∪ R₀ ∪ {A'}) := by
        rw [h_erase_x]; exact IsPlan.step ha hb hab hQ₀ hR₀ h_inter_mem h_restr_eq rfl
      have hR_sub : IsPlan ((A' ∪ {x}).erase a) Qext := by
        rw [h_erase_a]; exact hQext_plan
      have h_inter_mem' : ((A' ∪ {x}).erase x).erase a ∈ (Q₀ ∪ R₀ ∪ {A'}) ∧
          ((A' ∪ {x}).erase x).erase a ∈ Qext := by
        rw [h_erase_xa]; exact ⟨hea_in_P, hQext_mem⟩
      have h_restr' : (Q₀ ∪ R₀ ∪ {A'}) ∩ (((A' ∪ {x}).erase x).erase a).powerset =
          Qext ∩ (((A' ∪ {x}).erase x).erase a).powerset := by
        rw [h_erase_xa]; exact h_restr_eq'
      exact IsPlan.step hx_mem ha_mem (fun h => hax h.symm)
        hQ_sub hR_sub h_inter_mem' h_restr' hresult_def
    · change A' ∈ (Q₀ ∪ R₀ ∪ {A'}) ∪ Qext ∪ {A' ∪ {x}}
      exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_singleton_self _)))
    · unfold restrictPlan; ext S
      simp only [hresult_def, Finset.mem_inter, Finset.mem_union, Finset.mem_singleton,
                  Finset.mem_powerset]
      constructor
      · rintro ⟨((((hS_Q | hS_R) | rfl) | hS_Qext) | rfl), hS_sub⟩
        · left; left; exact hS_Q
        · left; right; exact hS_R
        · right; rfl
        · have hS_sub_ext : S ⊆ (A'.erase a) ∪ {x} :=
            h_erase_a ▸ hQext_plan.subset_of_mem hS_Qext
          have hS_ea : S ⊆ A'.erase a := by
            intro y hy
            rcases Finset.mem_union.mp (hS_sub_ext hy) with h | h
            · exact h
            · exact absurd hy (Finset.mem_singleton.mp h ▸ fun h' => hx (hS_sub h'))
          have hS_mem : S ∈ Qext ∩ (A'.erase a).powerset :=
            Finset.mem_inter.mpr ⟨hS_Qext, Finset.mem_powerset.mpr hS_ea⟩
          rw [hQext_restr'] at hS_mem
          left; left; exact hS_mem
        · exfalso; exact hx (hS_sub (Finset.mem_union_right _ (Finset.mem_singleton_self x)))
      · rintro ((hS_Q | hS_R) | rfl)
        · exact ⟨Or.inl (Or.inl (Or.inl (Or.inl hS_Q))),
                 (hQ₀.subset_of_mem hS_Q).trans (Finset.erase_subset _ _)⟩
        · exact ⟨Or.inl (Or.inl (Or.inl (Or.inr hS_R))),
                 (hR₀.subset_of_mem hS_R).trans (Finset.erase_subset _ _)⟩
        · exact ⟨Or.inl (Or.inl (Or.inr rfl)), Finset.Subset.refl _⟩

/-! ### Plans are never full on three or more points -/

/-- A plan on a set of three or more points is never the full powerset: the pair `{a, b}`
of pivots of the top-level step is invisible (`{a, b} ∉ Q` since `a ∉ A ∖ {a}`,
`{a, b} ∉ R` since `b ∉ A ∖ {b}`, and `{a, b} ≠ A` by cardinality). -/
theorem isPlan_ne_powerset
    {A : Finset α} (hcard : 3 ≤ A.card)
    {P : Finset (Finset α)} (hP : IsPlan A P) :
    P ≠ A.powerset := by
  intro heq
  match hP with
  | .empty => simp at hcard
  | .singleton _ => simp at hcard
  | .step (a := a) (b := b) ha hb hab hQ hR _ _ rfl =>
    have hab_sub : ({a, b} : Finset α) ⊆ A :=
      Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
    have hab_pow : ({a, b} : Finset α) ∈ A.powerset :=
      Finset.mem_powerset.mpr hab_sub
    rw [← heq] at hab_pow
    simp only [Finset.mem_union, Finset.mem_singleton] at hab_pow
    rcases hab_pow with (hab_Q | hab_R) | hab_A
    · have := hQ.subset_of_mem hab_Q (Finset.mem_insert_self a {b})
      exact (Finset.mem_erase.mp this).1 rfl
    · have hb_mem : b ∈ ({a, b} : Finset α) :=
        Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      have := hR.subset_of_mem hab_R hb_mem
      exact (Finset.mem_erase.mp this).1 rfl
    · have h2 : ({a, b} : Finset α).card ≤ 2 := by
        calc ({a, b} : Finset α).card
            ≤ ({a} : Finset α).card + ({b} : Finset α).card :=
              Finset.card_union_le {a} {b}
          _ = 2 := by simp
      have := congrArg Finset.card hab_A; omega

end Plan

end VaughtConjecture.AmalgamationPlan
