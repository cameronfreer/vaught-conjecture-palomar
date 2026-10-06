/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FreeDiagonal

/-! # Arbitrary ambients represented grade by grade

Availability promotes each label to a full-scope controller at the same grade.
Taking a maximum among those finitely many controllers yields one controller
dominating the entire grade. Normalizing its actual locality witness then reads
that grade exactly, and all lower grades capped at its own label. This strengthens
the per-cell availability observation in `Knight/Producer.lean` to an exact
grade-by-grade representation on arbitrary lower domains, without assuming a
bountiful scheme or that the ambient is one of its semantic rows.

At an external cap, a grade is frozen if its maximum lies strictly below the
cap. Otherwise any replacement maximum must be a controller whose *old* label
already reaches the cap. The eligible set is preserved exactly. These facts do
not assume a designated controller stays maximal, nor that one controller
dominates labels at other grades.

The charts are extracted from respect, not a converse characterization of it.
Recombining or changing charts still requires every controller locality and
availability. In particular their shifters are not asserted bottom-reflecting,
and no unrestricted composition of faithful transformations is used.
-/

@[expose] public section

namespace VaughtConjecture.Knight.AmbientGradeCharts

open Transform Value ExtOrd VaughtConjecture.AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ} {q : D.below BJ → ExtOrd}

/-- A normalized witness at a controller dominating its own grade. -/
structure Chart (sem : Semantics D) (BJ : Finset ι × ℕ) (q : D.below BJ → ExtOrd)
    (k : ℕ) where
  owner : D.below BJ
  index : D.cell owner.1 = (BJ.1, k)
  dominates : ∀ d : D.below BJ, D.grade d.1 = k → q d ≤ q owner
  shift : ExtOrd → ExtOrd
  witness : Witness (gTop k) shift
  bounded : ∀ x, shift x ≤ q owner
  read : ∀ d : D.below (D.cell owner.1),
    shift (sem.E owner.1 d) = min (q (CellScheme.below.incl owner d)) (q owner)

namespace Chart

variable {k : ℕ} (C : Chart sem BJ q k)

theorem grade : D.grade C.owner.1 = k := congrArg Prod.snd C.index

/-- Every occurrence of grade at most `k` lies below this full-scope owner. -/
def occurrence (d : D.below BJ) (hd : D.grade d.1 ≤ k) : D.below (D.cell C.owner.1) :=
  ⟨d.1, by rw [C.index]; exact ⟨d.2.1, hd⟩⟩

theorem read_capped (d : D.below BJ) (hd : D.grade d.1 ≤ k) :
    C.shift (sem.E C.owner.1 (C.occurrence d hd)) = min (q d) (q C.owner) :=
  C.read (C.occurrence d hd)

/-- Exact readback on the owner's grade, including all its sibling controllers. -/
theorem read_grade (d : D.below BJ) (hd : D.grade d.1 = k) :
    C.shift (sem.E C.owner.1 (C.occurrence d hd.le)) = q d := by
  rw [C.read_capped, min_eq_left (C.dominates d hd)]

/-- If this grade's maximum reaches the external cap, its one witness recovers
the externally capped labels at every lower grade as well. -/
theorem read_under_cap {γ : ExtOrd} (hactive : γ ≤ q C.owner)
    (d : D.below BJ) (hd : D.grade d.1 ≤ k) :
    min (C.shift (sem.E C.owner.1 (C.occurrence d hd))) γ = min (q d) γ := by
  rw [C.read_capped, min_assoc, min_eq_right hactive]

/-- Different choices of maximizing controller yield the same maximum value. -/
theorem maximum_eq (C' : Chart sem BJ q k) : q C.owner = q C'.owner :=
  le_antisymm (C'.dominates C.owner C.grade) (C.dominates C'.owner C'.grade)

end Chart

/-- One full-scope controller suffices to make the maximizing set nonempty.
Availability, not a cross-grade domination assumption, supplies the final bound. -/
theorem exists_maximizer (hq : RespectsSemanticsBelow sem BJ q) {k : ℕ}
    (hfull : ∃ c : D.below BJ, D.cell c.1 = (BJ.1, k)) :
    ∃ c : D.below BJ, D.cell c.1 = (BJ.1, k) ∧
      ∀ d : D.below BJ, D.grade d.1 = k → q d ≤ q c := by
  classical
  let _ := Fintype.ofFinite (D.below BJ)
  let s := Finset.univ.filter (fun c : D.below BJ => D.cell c.1 = (BJ.1, k))
  have hs : s.Nonempty := by
    obtain ⟨c, hc⟩ := hfull
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image s q hs
  have hci : D.cell c.1 = (BJ.1, k) := (Finset.mem_filter.mp hc).2
  refine ⟨c, hci, ?_⟩
  intro d hd
  have hscope : D.scope d.1 ⊆ D.scope c.1 := by
    change D.scope d.1 ⊆ (D.cell c.1).1
    rw [hci]
    exact d.2.1
  have hgrade : D.grade d.1 = D.grade c.1 := hd.trans (congrArg Prod.snd hci).symm
  obtain ⟨e, he, hde⟩ := hq.availability d c hscope hgrade
  exact hde.trans (hmax e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.trans hci⟩))

/-- Extract an actual bounded faithful witness; bottom and literal top need no exclusion. -/
theorem exists_chart (hq : RespectsSemanticsBelow sem BJ q) {k : ℕ}
    (hfull : ∃ c : D.below BJ, D.cell c.1 = (BJ.1, k)) :
    Nonempty (Chart sem BJ q k) := by
  obtain ⟨c, hc, hmax⟩ := exists_maximizer hq hfull
  let self : D.below (D.cell c.1) := ⟨c.1, GradedLe.refl _⟩
  let p : D.below (D.cell c.1) → ExtOrd := fun d => q (CellScheme.below.incl c d)
  have hm : ∀ d : D.below (D.cell c.1), D.grade d.1 ≤ D.grade self.1 := fun d => d.2.2
  have hv : SelfVis (D.grade self.1) (p self) := (hq.orderly c).symm
  obtain ⟨τ, hτ, hb, hr⟩ := exists_bounded_exact_capped_witness hm hv (hq.locality c)
  have hg : D.grade self.1 = k := congrArg Prod.snd hc
  exact ⟨⟨c, hc, hmax, τ, hg ▸ hτ, hb, hr⟩⟩

/-- A complete lower domain has one such chart at every positive grade it contains. -/
theorem exists_chart_of_complete (hq : RespectsSemanticsBelow sem BJ q)
    (hD : D.IsComplete) (hBJ : BJ ∈ Plan.gradedPlan D.plan)
    {k : ℕ} (hk0 : 0 < k) (hk : k ≤ BJ.2) : Nonempty (Chart sem BJ q k) := by
  obtain ⟨c, hc⟩ := hD (BJ.1, k)
    (Plan.mem_gradedPlan.mpr ⟨(Plan.mem_gradedPlan.mp hBJ).1, hk0,
      hk.trans (Plan.mem_gradedPlan.mp hBJ).2.2⟩)
  apply exists_chart hq
  exact ⟨⟨c, by rw [hc]; exact ⟨Finset.Subset.refl _, hk⟩⟩, hc⟩

/-- No separate member-row assumption is needed to obtain the whole graded representation. -/
theorem exists_family (hq : RespectsSemanticsBelow sem BJ q)
    (hD : D.IsComplete) (hBJ : BJ ∈ Plan.gradedPlan D.plan) :
    Nonempty ((k : ℕ) → 0 < k → k ≤ BJ.2 → Chart sem BJ q k) :=
  ⟨fun _ hk0 hk => Classical.choice (exists_chart_of_complete hq hD hBJ hk0 hk)⟩

/-! ## Exact cap-preservation obligations -/

/-- The literal part of a cap equation; this statement also applies at cap top. -/
theorem eq_of_cap_below {a b γ : ExtOrd} (h : min a γ = min b γ) (hb : b < γ) : a = b := by
  rw [min_eq_left hb.le] at h
  have ha : a < γ := (min_lt_iff.mp (h.trans_lt hb)).resolve_right (lt_irrefl γ)
  rwa [min_eq_left ha.le] at h

theorem cap_reaches_iff {a b γ : ExtOrd} (h : min a γ = min b γ) : γ ≤ a ↔ γ ≤ b := by
  constructor
  · intro ha
    apply min_eq_right_iff.mp
    exact h.symm.trans (min_eq_right ha)
  · intro hb
    apply min_eq_right_iff.mp
    exact h.trans (min_eq_right hb)

/-- Preserving caps means keeping the strict lower part literal and the upper part above
the cap. It does not mean keeping all upper labels literal. -/
theorem cap_iff {a b γ : ExtOrd} : min a γ = min b γ ↔
    (b < γ → a = b) ∧ (γ ≤ b → γ ≤ a) := by
  constructor
  · intro h
    exact ⟨eq_of_cap_below h, (cap_reaches_iff h).mpr⟩
  · rintro ⟨hl, hu⟩
    rcases lt_or_ge b γ with hb | hb
    · rw [hl hb]
    · rw [min_eq_right hb, min_eq_right (hu hb)]

/-- Source-side cap agreement transfers through a monotone shifter once the
image of the source cap reaches the output cap. Bottom reflection is unnecessary
for this equation; no preservation of respect is asserted. -/
theorem map_cap_agreement {τ : ExtOrd → ExtOrd} (hτ : Monotone τ)
    {a b δ γ : ExtOrd} (hab : min a δ = min b δ) (hγ : γ ≤ τ δ) :
    min (τ a) γ = min (τ b) γ := by
  calc
    min (τ a) γ = min (τ (min a δ)) γ := by
      rw [hτ.map_min, min_assoc, min_eq_right hγ]
    _ = min (τ (min b δ)) γ := by rw [hab]
    _ = min (τ b) γ := by rw [hτ.map_min, min_assoc, min_eq_right hγ]

/-- A replacement shifter may grow above the source cut. Keeping the old prefix
literal suffices to preserve the output cap, even when the new output must exceed
the old shifter's global bound. This does not construct the replacement shifter. -/
theorem map_cap_agreement_of_prefix {τ υ : ExtOrd → ExtOrd}
    (hτ : Monotone τ) (hυ : Monotone υ) {a b δ γ : ExtOrd}
    (hprefix : ∀ x, x ≤ δ → υ x = τ x)
    (hab : min a δ = min b δ) (hγ : γ ≤ τ δ) :
    min (υ a) γ = min (τ b) γ := by
  have hγ' : γ ≤ υ δ := by rwa [hprefix δ le_rfl]
  calc
    min (υ a) γ = min (υ (min a δ)) γ := by
      rw [hυ.map_min, min_assoc, min_eq_right hγ']
    _ = min (τ (min a δ)) γ := by rw [hprefix _ (min_le_right _ _)]
    _ = min (τ (min b δ)) γ := by rw [hab]
    _ = min (τ b) γ := by rw [hτ.map_min, min_assoc, min_eq_right hγ]

variable {q' : D.below BJ → ExtOrd} {γ : ExtOrd}

namespace Chart

variable {k : ℕ} (C : Chart sem BJ q k)

/-- If the ambient maximum of this grade is below the external cap, every value
at this grade is frozen, not merely the chosen maximum's value. -/
theorem frozen_grade (hcap : ∀ d, min (q' d) γ = min (q d) γ)
    (hsmall : q C.owner < γ) (d : D.below BJ) (hd : D.grade d.1 = k) : q' d = q d :=
  eq_of_cap_below (hcap d) ((C.dominates d hd).trans_lt hsmall)

/-- Full-scope replacement controllers eligible at the cap are determined by the old ambient. -/
def eligible (_C : Chart sem BJ q k) (γ : ExtOrd) : Set (D.below BJ) :=
  {c | D.cell c.1 = (BJ.1, k) ∧ γ ≤ q c}

theorem eligible_preserved (C' : Chart sem BJ q' k)
    (hcap : ∀ d, min (q' d) γ = min (q d) γ) : C'.eligible γ = C.eligible γ := by
  ext d
  exact and_congr_right (fun _ => cap_reaches_iff (hcap d))

/-- The maximum value can move, but its capped value cannot. -/
theorem maximum_cap (C' : Chart sem BJ q' k)
    (hcap : ∀ d, min (q' d) γ = min (q d) γ) :
    min (q' C'.owner) γ = min (q C.owner) γ := by
  apply le_antisymm
  · rw [hcap]
    exact min_le_min_right γ (C.dominates C'.owner C'.grade)
  · rw [← hcap]
    exact min_le_min_right γ (C'.dominates C.owner C.grade)

/-- Controller switching is allowed, but not into an old cell below the cap. -/
theorem replacement_eligible (C' : Chart sem BJ q' k)
    (hcap : ∀ d, min (q' d) γ = min (q d) γ) (hactive : γ ≤ q C.owner) :
    C'.owner ∈ C.eligible γ := by
  refine ⟨C'.index, ?_⟩
  have hnew : γ ≤ q' C'.owner := (cap_reaches_iff (C.maximum_cap C' hcap)).mpr hactive
  exact (cap_reaches_iff (hcap C'.owner)).mp hnew

/-- What preserving the external cap asks of a replacement row and witness at this grade.
All sibling occurrences at this grade are included, not only proper-face probes. -/
theorem replacement_read_iff (C' : Chart sem BJ q' k) :
    (∀ d : D.below BJ, D.grade d.1 = k → min (q' d) γ = min (q d) γ) ↔
      ∀ (d : D.below BJ) (hd : D.grade d.1 = k),
        min (C'.shift (sem.E C'.owner.1 (C'.occurrence d hd.le))) γ =
          min (C.shift (sem.E C.owner.1 (C.occurrence d hd.le))) γ := by
  constructor
  · intro h d hd
    rw [C'.read_grade d hd, C.read_grade d hd]
    exact h d hd
  · intro h d hd
    have he := h d hd
    rw [C'.read_grade d hd, C.read_grade d hd] at he
    exact he

/-- When both maxima reach the cap, comparing the two witnesses at every actual
occurrence is equivalent to capped agreement on the whole lower-grade domain.
No bottom reflection or composition of the witnesses is required. -/
theorem replacement_read_below_iff (C' : Chart sem BJ q' k)
    (hactive : γ ≤ q C.owner) (hactive' : γ ≤ q' C'.owner) :
    (∀ d : D.below BJ, D.grade d.1 ≤ k → min (q' d) γ = min (q d) γ) ↔
      ∀ (d : D.below BJ) (hd : D.grade d.1 ≤ k),
        min (C'.shift (sem.E C'.owner.1 (C'.occurrence d hd))) γ =
          min (C.shift (sem.E C.owner.1 (C.occurrence d hd))) γ := by
  constructor
  · intro h d hd
    rw [C'.read_under_cap hactive' d hd, C.read_under_cap hactive d hd]
    exact h d hd
  · intro h d hd
    have he := h d hd
    rw [C'.read_under_cap hactive' d hd, C.read_under_cap hactive d hd] at he
    exact he

end Chart

end VaughtConjecture.Knight.AmbientGradeCharts
