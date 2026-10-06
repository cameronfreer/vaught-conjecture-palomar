/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SynchronizedOrbitCap

/-! # One lawful grade-cap assignment for nested old domains

The respect proof below is adapted, with attribution, from V-C's
`GradeTwoCodedBountiful.lean` (`RespectsSemanticsBelow.gradeCap`, #457), read
at #460 head 27bea62. It is isolated here without importing the refuted tower.
No tower theorem or tower construction is used.

The new content specializes this operation to two independently visible caps,
preserves restrictions literally, and tests every protected label and external
capped value. Higher grades use the smaller cap; this is a sufficient coherent
class, not a necessity theorem about every possible lawful adjustment.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.CoherentGradeCaps

open Transform Value ExtOrd AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {BJ : Finset ι × ℕ}

noncomputable def clipped (g : ℕ → ExtOrd) (p : D.below BJ → ExtOrd)
    (d : D.below BJ) : ExtOrd := min (p d) (g (D.grade d.1))

/-- V-C's generic grade-cap argument, independent of its tower. -/
theorem respects {sem : Semantics D} {p : D.below BJ → ExtOrd}
    (hp : RespectsSemanticsBelow sem BJ p) (g : ℕ → ExtOrd)
    (ha : Antitone g) (hv : ∀ k, k ≤ BJ.2 → SelfVis k (g k)) :
    RespectsSemanticsBelow sem BJ (clipped g p) where
  orderly d := (selfVis_min (hp.orderly d).symm (hv _ d.2.2)).symm
  locality c := by
    have hmax : ∀ d : D.below (D.cell c.1), D.grade d.1 ≤ D.grade c.1 := fun d => d.2.2
    have ht := TransformsTo.capped hmax (hv (D.grade c.1) c.2.2) (hp.locality c)
    refine transformsTo_congr rfl rfl ?_ ht
    funext d
    change min (min (p (CellScheme.below.incl c d)) (p c)) (g (D.grade c.1)) =
      min (min (p (CellScheme.below.incl c d)) (g (D.grade d.1)))
        (min (p c) (g (D.grade c.1)))
    have hgd : g (D.grade c.1) ≤ g (D.grade d.1) := ha d.2.2
    rw [min_min_min_comm, min_eq_right hgd]
  availability c e hs hg := by
    obtain ⟨w, hw, hle⟩ := hp.availability c e hs hg
    refine ⟨w, hw, ?_⟩
    have hgrade : D.grade w.1 = D.grade c.1 := (congrArg Prod.snd hw).trans hg.symm
    change min (p c) (g (D.grade c.1)) ≤ min (p w) (g (D.grade w.1))
    rw [hgrade]
    exact min_le_min_right _ hle

/-- The same global grade-cap assignment gives identical labels on overlap;
restriction does not choose a second cap or a second old completion. -/
theorem restrict_eq {CI : Finset ι × ℕ} (h : GradedLe CI BJ)
    (g : ℕ → ExtOrd) (p : D.below BJ → ExtOrd) :
    (fun d => clipped g p (CellScheme.below.mono h d)) =
      clipped g (fun d => p (CellScheme.below.mono h d)) := rfl

/-- At any controller cap, all cells below it give the old capped target. -/
theorem at_cap (g : ℕ → ExtOrd) (ha : Antitone g) (p : D.below BJ → ExtOrd)
    (d : D.below BJ) {j : ℕ} (hd : D.grade d.1 ≤ j) :
    min (clipped g p d) (g j) = min (p d) (g j) := by
  change min (min (p d) (g (D.grade d.1))) (g j) = _
  rw [min_assoc, min_eq_right (ha hd)]

theorem receipts_iff (g : ℕ → ExtOrd) (p γ : D.below BJ → ExtOrd) :
    (∀ d, min (clipped g p d) (γ d) = min (p d) (γ d)) ↔
      ∀ d, min (p d) (γ d) ≤ g (D.grade d.1) := by
  simp only [clipped, min_right_comm (p _), min_eq_left_iff]

theorem protected_iff (g : ℕ → ExtOrd) (p : D.below BJ → ExtOrd)
    (S : Set (D.below BJ)) :
    (∀ d ∈ S, clipped g p d = p d) ↔ ∀ d ∈ S, p d ≤ g (D.grade d.1) := by
  simp only [clipped, min_eq_left_iff]

/-- Leave grades below j unchanged, cap grade j at U, and higher grades at V. -/
noncomputable def twoCaps (j : ℕ) (U V : ExtOrd) (k : ℕ) : ExtOrd :=
  if k < j then ⊤ else if k = j then U else V

theorem twoCaps_low (j : ℕ) (U V : ExtOrd) : twoCaps j U V j = U := by
  simp only [twoCaps, lt_self_iff_false, ↓reduceIte]

theorem twoCaps_high {j k : ℕ} (hjk : j < k) (U V : ExtOrd) : twoCaps j U V k = V := by
  simp only [twoCaps, ite_eq_right (show ¬ k < j by omega),
    ite_eq_right (show k ≠ j by omega)]

theorem twoCaps_antitone (j : ℕ) {U V : ExtOrd} (hVU : V ≤ U) :
    Antitone (twoCaps j U V) := by
  intro a b hab
  unfold twoCaps
  split_ifs <;> first | exact le_top | exact le_rfl | exact hVU | omega

theorem twoCaps_visible {j K : ℕ} {U V : ExtOrd}
    (hU : SelfVis j U) (hV : SelfVis K V) (k : ℕ) (hk : k ≤ K) :
    SelfVis k (twoCaps j U V k) := by
  unfold twoCaps
  split_ifs with hlt heq
  · exact extVisibilityReplace_top _ _
  · exact heq ▸ hU
  · exact hV.mono hk

/-- A single respecting old labelling serves both cap choices simultaneously.
In particular U need not be visible at the higher grade. -/
theorem twoCaps_respects {sem : Semantics D} {p : D.below BJ → ExtOrd}
    (hp : RespectsSemanticsBelow sem BJ p) (j : ℕ) {U V : ExtOrd}
    (hU : SelfVis j U) (hV : SelfVis BJ.2 V) (hVU : V ≤ U) :
    RespectsSemanticsBelow sem BJ (clipped (twoCaps j U V) p) :=
  respects hp _ (twoCaps_antitone j hVU) (twoCaps_visible hU hV)

theorem twoCaps_prefix (j : ℕ) (U V : ExtOrd) (p : D.below BJ → ExtOrd)
    (d : D.below BJ) (hd : D.grade d.1 < j) : clipped (twoCaps j U V) p d = p d := by
  simp only [clipped, twoCaps, ite_eq_left hd, min_top_right]

/-- Exact original-cap bounds for the two-grade adjustment, with every
intermediate higher-grade occurrence included on the V side. -/
theorem twoCaps_receipts_iff (j : ℕ) (U V : ExtOrd) (p γ : D.below BJ → ExtOrd) :
    (∀ d, min (clipped (twoCaps j U V) p d) (γ d) = min (p d) (γ d)) ↔
      (∀ d, D.grade d.1 = j → min (p d) (γ d) ≤ U) ∧
      (∀ d, j < D.grade d.1 → min (p d) (γ d) ≤ V) := by
  rw [receipts_iff]
  constructor
  · intro h
    exact ⟨fun d hd => by simpa only [hd, twoCaps_low] using h d,
      fun d hd => by simpa only [twoCaps_high hd] using h d⟩
  · rintro ⟨hl, hh⟩ d
    rcases lt_trichotomy (D.grade d.1) j with hd | hd | hd
    · simp only [twoCaps, ite_eq_left hd, le_top]
    · simpa only [hd, twoCaps_low] using hl d hd
    · simpa only [twoCaps_high hd] using hh d hd

/-- Exact literal preservation, including every protected auxiliary in the
higher-grade tail rather than just the two named controllers. -/
theorem twoCaps_protected_iff (j : ℕ) (U V : ExtOrd) (p : D.below BJ → ExtOrd)
    (S : Set (D.below BJ)) :
    (∀ d ∈ S, clipped (twoCaps j U V) p d = p d) ↔
      (∀ d ∈ S, D.grade d.1 = j → p d ≤ U) ∧
      (∀ d ∈ S, j < D.grade d.1 → p d ≤ V) := by
  rw [protected_iff]
  constructor
  · intro h
    exact ⟨fun d hd hg => by simpa only [hg, twoCaps_low] using h d hd,
      fun d hd hg => by simpa only [twoCaps_high hg] using h d hd⟩
  · rintro ⟨hl, hh⟩ d hd
    rcases lt_trichotomy (D.grade d.1) j with hg | hg | hg
    · simp only [twoCaps, ite_eq_left hg, le_top]
    · simpa only [hg, twoCaps_low] using hl d hd hg
    · simpa only [twoCaps_high hg] using hh d hd hg

/-- Any donor can use its cap from the common assignment. Every earlier
grade-cap adjustment below it is invisible at this cap. Thus the row witness
survives simultaneous clipping, not just a separately normalized local input. -/
theorem donor_orbit {sem : Semantics D} (c : Cell D)
    {p : D.below (D.cell c) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    (g : ℕ → ExtOrd) (ha : Antitone g) (hv : SelfVis (D.grade c) (g (D.grade c)))
    {I : Type*} (newGrade : I → ℕ) (ref : I → D.below (D.cell c)) (offset : I → ℕ)
    (hnew : ∀ i, newGrade i ≤ D.grade c) (hoff : ∀ i, offset i ≤ D.grade c)
    (y : I → ExtOrd) (hcut : g (D.grade c) ≤ p ⟨c, GradedLe.refl _⟩)
    (he : ∀ i, min (y i) (g (D.grade c)) =
      min (extVisibilityReplace (p (ref i)) (D.grade c) (offset i)) (g (D.grade c))) :
    TransformsTo (Sum.elim (fun d : D.below (D.cell c) => D.grade d.1) newGrade)
      (OrbitCap.row (sem.E c) ref offset (D.grade c))
      (fun d => min (OrbitCap.labels (clipped g p) y d) (g (D.grade c))) := by
  have ht := (OrbitCap.synchronizedCap_actual_donor c hp newGrade ref offset hnew hoff
    y hv hcut he).2.1
  refine transformsTo_congr rfl rfl ?_ ht
  funext d
  cases d with
  | inl d =>
    exact (OrbitCap.synchronizedCap_capped p (g (D.grade c)) d).trans
      (at_cap g ha p d d.2.2).symm
  | inr i => rfl

end VaughtConjecture.Knight.CoherentGradeCaps
