/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LocalCapBounds
public import VaughtConjecture.Knight.MixedIndexConstraints

/-! # Row-dependent donor families on actual lower domains

Availability may choose a different admissible donor for each upper row. For a
lawful row, an admissible family covers all requests exactly when it contains
a reading-maximal donor at every nonempty index. The maximizer belongs to the
family, not merely to the unfiltered set of old cells. All occurrences remain
distinct and witnesses stay in the actual lower domain.

Grade-wise clipping retains each covering witness. For unchanged source rows,
enlarging the admissible family retains coverage. Neither fact constructs new
rows or proves that the family admits the required fresh columns.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.DonorFamily

open Transform Value ExtOrd CoherentGradeCaps

variable {ι : Type*} [DecidableEq ι] {F : Finset ι} {D : CellScheme F}
  {BJ : Finset ι × ℕ}

/-- Restricted availability with a declared admissible pool. -/
def Covers (p : D.below BJ → ExtOrd) (admissible : D.below BJ → Prop) : Prop :=
  ∀ d t : D.below BJ, D.scope d.1 ⊆ D.scope t.1 → D.grade d.1 = D.grade t.1 →
    ∃ w : D.below BJ, D.cell w.1 = D.cell t.1 ∧ admissible w ∧ p d ≤ p w

theorem Covers.mono {p : D.below BJ → ExtOrd} {a b : D.below BJ → Prop}
    (h : Covers p a) (hab : ∀ d, a d → b d) : Covers p b := by
  intro d t hs hg
  obtain ⟨w, hw, ha, hle⟩ := h d t hs hg
  exact ⟨w, hw, hab w ha, hle⟩

theorem covers_all {sem : Semantics D} {p : D.below BJ → ExtOrd}
    (hp : RespectsSemanticsBelow sem BJ p) : Covers p (fun _ => True) := by
  intro d t hs hg
  obtain ⟨w, hw, hle⟩ := hp.availability d t hs hg
  exact ⟨w, hw, trivial, hle⟩

/-- The chosen witness is unchanged, since requester and witness have equal
grade and hence are clipped by the same cap. No monotonicity of caps is needed. -/
theorem Covers.clipped {p : D.below BJ → ExtOrd} {a : D.below BJ → Prop}
    (h : Covers p a) (U : ℕ → ExtOrd) : Covers (CoherentGradeCaps.clipped U p) a := by
  intro d t hs hg
  obtain ⟨w, hw, ha, hle⟩ := h d t hs hg
  refine ⟨w, hw, ha, ?_⟩
  have he : D.grade w.1 = D.grade d.1 := (congrArg Prod.snd hw).trans hg.symm
  change min (p d) (U (D.grade d.1)) ≤ min (p w) (U (D.grade w.1))
  rw [he]
  exact min_le_min_right _ hle

/-- A maximum over all old donors exists separately for each row and index. -/
theorem exists_index_max (p : D.below BJ → ExtOrd) (t : D.below BJ) :
    ∃ w : D.below BJ, D.cell w.1 = D.cell t.1 ∧
      ∀ v : D.below BJ, D.cell v.1 = D.cell t.1 → p v ≤ p w := by
  classical
  let _ := Fintype.ofFinite (D.below BJ)
  let s := Finset.univ.filter fun w : D.below BJ => D.cell w.1 = D.cell t.1
  have ht : t ∈ s := by simp only [s, Finset.mem_filter, Finset.mem_univ, and_true]
  obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image s p ⟨t, ht⟩
  refine ⟨w, (Finset.mem_filter.mp hw).2, ?_⟩
  intro v hv
  exact hmax v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)

/-- Exact admissibility test: every index has an admissible donor that reaches
the maximum over ALL its old donors. An arbitrary admissible maximum is not enough. -/
theorem covers_iff_maxima {sem : Semantics D} {p : D.below BJ → ExtOrd}
    (hp : RespectsSemanticsBelow sem BJ p) (a : D.below BJ → Prop) :
    Covers p a ↔ ∀ t : D.below BJ, ∃ w : D.below BJ,
      D.cell w.1 = D.cell t.1 ∧ a w ∧
        ∀ v : D.below BJ, D.cell v.1 = D.cell t.1 → p v ≤ p w := by
  constructor
  · intro h t
    obtain ⟨v, hv, hmax⟩ := exists_index_max p t
    obtain ⟨w, hw, ha, hle⟩ := h v t
      (by exact (congrArg Prod.fst hv).le) (congrArg Prod.snd hv)
    exact ⟨w, hw, ha, fun u hu => (hmax u hu).trans hle⟩
  · intro h d t hs hg
    obtain ⟨v, hv, hle⟩ := hp.availability d t hs hg
    obtain ⟨w, hw, ha, hmax⟩ := h t
    exact ⟨w, hw, ha, hle.trans (hmax v hv)⟩

/-- Source-row coverage of a common pool, with row-dependent witnesses.
Only rows and occurrences in the specified actual lower domain are used. -/
def SourcesCovered (sem : Semantics D) (BJ : Finset ι × ℕ)
    (a : D.below BJ → Prop) : Prop :=
  ∀ c : D.below BJ, Covers (sem.E c.1) (fun d => a (CellScheme.below.incl c d))

theorem SourcesCovered.mono {sem : Semantics D} {a b : D.below BJ → Prop}
    (h : SourcesCovered sem BJ a) (hab : ∀ d, a d → b d) : SourcesCovered sem BJ b :=
  fun c => (h c).mono (fun d hd => hab (CellScheme.below.incl c d) hd)

theorem sourcesCovered_all {sem : Semantics D} (hc : sem.IsConsistent) :
    SourcesCovered sem BJ (fun _ => True) := fun c => covers_all (hc c.1)

/-- The exact source-family test quantifies a separate admissible maximizer
for each upper row and target index, not one maximizer for all upper rows. -/
theorem sourcesCovered_iff {sem : Semantics D} (hc : sem.IsConsistent)
    (a : D.below BJ → Prop) : SourcesCovered sem BJ a ↔
      ∀ (c : D.below BJ) (t : D.below (D.cell c.1)),
        ∃ w : D.below (D.cell c.1), D.cell w.1 = D.cell t.1 ∧
          a (CellScheme.below.incl c w) ∧
          ∀ v : D.below (D.cell c.1), D.cell v.1 = D.cell t.1 → sem.E c.1 v ≤ sem.E c.1 w := by
  constructor
  · exact fun h c => (covers_iff_maxima (hc c.1) _).mp (h c)
  · exact fun h c => (covers_iff_maxima (hc c.1) _).mpr (h c)

/-- At each old controller, some admissible coindexed donor is read at least
as high as its diagonal. The choice may depend on the controller. -/
def DiagonalCover (sem : Semantics D) (BJ : Finset ι × ℕ)
    (a : D.below BJ → Prop) : Prop :=
  ∀ c : D.below BJ, ∃ w : D.below (D.cell c.1), D.cell w.1 = D.cell c.1 ∧
    a (CellScheme.below.incl c w) ∧
      sem.E c.1 ⟨c.1, GradedLe.refl _⟩ ≤ sem.E c.1 w

/-- A finite diagonal test on the unchanged sources supplies family
availability for EVERY lawful labelling, not just for the selected display. -/
theorem covers_of_diagonal {sem : Semantics D} {p : D.below BJ → ExtOrd}
    (hp : RespectsSemanticsBelow sem BJ p) {a : D.below BJ → Prop}
    (ha : DiagonalCover sem BJ a) : Covers p a := by
  intro d t hs hg
  obtain ⟨v, hv, hdv⟩ := hp.availability d t hs hg
  obtain ⟨w, hw, haw, hrow⟩ := ha v
  refine ⟨CellScheme.below.incl v w, hw.trans hv, haw, hdv.trans ?_⟩
  have hle := hp.capped_le_of_row_le v ⟨v.1, GradedLe.refl _⟩ w hrow
    (congrArg Prod.snd hw).le
  have he : CellScheme.below.incl v (⟨v.1, GradedLe.refl _⟩ : D.below (D.cell v.1)) = v :=
    Subtype.ext rfl
  rw [he, min_self] at hle
  exact hle.trans (min_le_left _ _)

/-- Consistency reduces all source-row requests to one diagonal test per old
controller. This does not require a common maximum across different rows. -/
theorem sourcesCovered_iff_diagonal {sem : Semantics D} (hc : sem.IsConsistent)
    (a : D.below BJ → Prop) : SourcesCovered sem BJ a ↔ DiagonalCover sem BJ a := by
  constructor
  · intro h c
    exact h c ⟨c.1, GradedLe.refl _⟩ ⟨c.1, GradedLe.refl _⟩
      (Finset.Subset.refl _) rfl
  · intro h c
    apply covers_of_diagonal (hc c.1)
    intro v
    obtain ⟨w, hw, ha, hrow⟩ := h (CellScheme.below.incl c v)
    exact ⟨w, hw, ha, hrow⟩

theorem SourcesCovered.covers {sem : Semantics D} (hc : sem.IsConsistent)
    {a : D.below BJ → Prop} (h : SourcesCovered sem BJ a)
    {p : D.below BJ → ExtOrd} (hp : RespectsSemanticsBelow sem BJ p) : Covers p a :=
  covers_of_diagonal hp ((sourcesCovered_iff_diagonal hc a).mp h)

/-- Only designated indices need an admissible copy; untouched indices may
retain every old witness. This does not demand donors at mute or unused indices. -/
def Targeted (needs : (Finset ι × ℕ) → Prop) (a : D.below BJ → Prop)
    (c : D.below BJ) : Prop := needs (D.cell c.1) → a c

theorem diagonal_targeted_iff {sem : Semantics D} (needs : (Finset ι × ℕ) → Prop)
    (a : D.below BJ → Prop) : DiagonalCover sem BJ (Targeted needs a) ↔
      ∀ c : D.below BJ, needs (D.cell c.1) →
        ∃ w : D.below (D.cell c.1), D.cell w.1 = D.cell c.1 ∧
          a (CellScheme.below.incl c w) ∧
            sem.E c.1 ⟨c.1, GradedLe.refl _⟩ ≤ sem.E c.1 w := by
  constructor
  · intro h c hn
    obtain ⟨w, hw, ha, hr⟩ := h c
    exact ⟨w, hw, ha (hw.symm ▸ hn), hr⟩
  · intro h c
    classical
    by_cases hn : needs (D.cell c.1)
    · obtain ⟨w, hw, ha, hr⟩ := h c hn
      exact ⟨w, hw, fun _ => ha, hr⟩
    · exact ⟨⟨c.1, GradedLe.refl _⟩, rfl, fun hh => False.elim (hn hh), le_rfl⟩

end VaughtConjecture.Knight.DonorFamily
