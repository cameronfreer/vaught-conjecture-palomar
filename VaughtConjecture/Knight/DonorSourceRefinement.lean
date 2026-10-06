/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceBlockPadding
public import VaughtConjecture.Knight.FreeDiagonal

/-! # Refining a display by the actual donor sources

A donor's row, rather than its displayed labels, retains the distinctions that
lawful old sections may need. Padding that row gives a coded, lawful source
profile with exactly the same faithful targets. The outgoing witness is
constructed by precomposition with the replacement-commuting inverse, not by
transitivity of faithful transformations.

At a unique index, availability removes the cap on all same-grade occurrences.
At grade one this is the entire lower domain, so the padded row covers every
lawful old section literally. The original row itself witnesses every source
distinction; no separate separating-section existence hypothesis is needed.

This does not add a fresh column or construct mixed-row incidences. In
particular, a fixed fresh source still has to meet the required order, block,
and cap constraints. No bountifulness of an enlargement is claimed.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.DonorSourceRefinement

open Transform Value ExtOrd SourceBlockPadding

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {o : Cell D}

def owner (o : Cell D) : D.below (D.cell o) := ⟨o, GradedLe.refl _⟩

/-- Uniqueness is only at the donor's index, not throughout the scheme. -/
def UniqueAt (o : Cell D) : Prop :=
  ∀ w : D.below (D.cell o), D.cell w.1 = D.cell o → w.1 = o

theorem label_le_owner {p : D.below (D.cell o) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell o) p) (hu : UniqueAt o)
    (d : D.below (D.cell o)) (hg : D.grade d.1 = D.grade o) : p d ≤ p (owner o) := by
  obtain ⟨w, hw, hle⟩ := hp.availability d (owner o) d.2.1 hg
  have he : w = owner o := Subtype.ext (hu w hw)
  rwa [he] at hle

/-- Normalize the donor's actual locality once. Every threshold clause is
part of the returned witness, including the bottom clauses above its grade. -/
theorem exact_witness {p : D.below (D.cell o) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell o) p) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop (D.grade o)) τ ∧
      (∀ x, τ x ≤ p (owner o)) ∧
      ∀ d, τ (sem.E o d) = min (p d) (p (owner o)) := by
  have hl : TransformsTo (fun d : D.below (D.cell o) => D.grade d.1)
      (sem.E o) (fun d => min (p d) (p (owner o))) := hp.locality (owner o)
  exact exists_bounded_exact_capped_witness (fun d => d.2.2)
    (hp.orderly (owner o)).symm hl

/-- Padding the actual row is independent of the selected display. -/
noncomputable def refined (sem : Semantics D) (o : Cell D)
    (d : D.below (D.cell o)) : ExtOrd := pad (sem.E o d)

theorem refined_respects (hc : sem.IsConsistent) :
    RespectsSemanticsBelow sem (D.cell o) (refined sem o) :=
  pad_respects (hc o) (K := D.grade o) (fun d => d.2.2)

theorem refined_coded (hc : sem.IsCoded) (d : D.below (D.cell o)) :
    IsCodedLabel (D.grade o) (refined sem o d) := pad_coded (hc o d)

theorem refined_eq_iff (d e : D.below (D.cell o)) :
    refined sem o d = refined sem o e ↔ sem.E o d = sem.E o e := by
  constructor
  · intro h
    have hh := congrArg unpad h
    simpa only [refined, unpad_pad] using hh
  · exact congrArg pad

/-- This source change gains and loses no faithful targets, even targets
that are not respecting labellings of the old semantics. -/
theorem refined_targets_iff (q : D.below (D.cell o) → ExtOrd) :
    TransformsTo (fun d : D.below (D.cell o) => D.grade d.1) (refined sem o) q ↔
      TransformsTo (fun d : D.below (D.cell o) => D.grade d.1) (sem.E o) q :=
  transforms_padded_source_iff

theorem refined_witness {p : D.below (D.cell o) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell o) p) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop (D.grade o)) τ ∧
      (∀ x, τ x ≤ p (owner o)) ∧
      ∀ d, τ (refined sem o d) = min (p d) (p (owner o)) := by
  obtain ⟨τ, hτ, hb, hr⟩ := exact_witness hp
  refine ⟨fun x => τ (unpad x), witness_precompose_unpad hτ,
    fun x => hb (unpad x), ?_⟩
  intro d
  simpa only [refined, unpad_pad] using hr d

/-- With a unique owner, its same-grade part is decoded literally. No
injectivity of the display or nonbottom label is required. -/
theorem same_grade_readback {p : D.below (D.cell o) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell o) p) (hu : UniqueAt o) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop (D.grade o)) τ ∧
      ∀ d, D.grade d.1 = D.grade o → τ (refined sem o d) = p d := by
  obtain ⟨τ, hτ, _, hr⟩ := refined_witness hp
  exact ⟨τ, hτ, fun d hd => (hr d).trans (min_eq_left (label_le_owner hp hu d hd))⟩

/-- Grade one has no lower positive grades: the same fixed refined source
row faithfully covers every lawful old input on the entire lower domain. -/
theorem grade_one_covers {p : D.below (D.cell o) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell o) p) (hu : UniqueAt o)
    (ho : D.grade o = 1) :
    TransformsTo (fun d : D.below (D.cell o) => D.grade d.1) (refined sem o) p := by
  obtain ⟨τ, hτ, hr⟩ := same_grade_readback hp hu
  apply hτ.transformsTo
  intro d
  have hg : D.grade d.1 = D.grade o := by
    have hl : D.grade d.1 ≤ D.grade o := d.2.2
    have hpos := D.grade_pos d.1
    omega
  rw [hr d hg, gTop_of_le hg.le, min_top_right]

/-- One source-only choice supplies a fresh owner diagonal for every lawful
old grade-one section and every larger visible owner label, including top.
This is a row extension, not an independent fresh request column. -/
theorem exists_free_owner (hc : sem.IsCoded) (hu : UniqueAt o)
    (ho : D.grade o = 1) :
    ∃ n : ℕ, 0 < n ∧ ∀ p, RespectsSemanticsBelow sem (D.cell o) p →
      ∀ U, SelfVis (D.grade o) U → p (owner o) ≤ U →
        TransformsTo
          (FreeDiagonal.append (fun d : D.below (D.cell o) => D.grade d.1) (D.grade o))
          (FreeDiagonal.append (refined sem o) (FreeDiagonal.source (D.grade o) n))
          (FreeDiagonal.append p U) := by
  obtain ⟨n, hn, hcut⟩ := FreeDiagonal.exists_limit_above (refined sem o)
    (refined_coded hc)
  refine ⟨n, hn, ?_⟩
  intro p hp U hU hle
  have hun : ∀ d : D.below (D.cell o), min (p d) (p (owner o)) = p d := by
    intro d
    apply min_eq_left (label_le_owner hp hu d ?_)
    have hl : D.grade d.1 ≤ D.grade o := d.2.2
    have hpos := D.grade_pos d.1
    omega
  have hl : TransformsTo (fun d : D.below (D.cell o) => D.grade d.1)
      (refined sem o) (fun d => min (p d) (p (owner o))) :=
    transforms_padded_source (hp.locality (owner o))
  have h := FreeDiagonal.transforms_append
    (grade := fun d : D.below (D.cell o) => D.grade d.1) (c := owner o) (fun d => d.2.2)
    (hp.orderly (owner o)).symm hl hcut hU hle
  have howner : D.grade (owner o).1 = D.grade o := rfl
  simpa only [hun, howner] using h

/-- A unique donor's row gives exactly the order forced on every lawful
section of its same-grade part. The reverse direction uses the row itself. -/
theorem source_le_iff_forced (hc : sem.IsConsistent) (hu : UniqueAt o)
    (d e : D.below (D.cell o)) (hd : D.grade d.1 = D.grade o)
    (he : D.grade e.1 = D.grade o) :
    sem.E o d ≤ sem.E o e ↔
      ∀ p, RespectsSemanticsBelow sem (D.cell o) p → p d ≤ p e := by
  constructor
  · intro h p hp
    obtain ⟨τ, hτ, _, hr⟩ := exact_witness hp
    have hh := hτ.mono h
    rwa [hr d, hr e, min_eq_left (label_le_owner hp hu d hd),
      min_eq_left (label_le_owner hp hu e he)] at hh
  · intro h
    exact h (sem.E o) (hc o)

theorem source_eq_iff_forced (hc : sem.IsConsistent) (hu : UniqueAt o)
    (d e : D.below (D.cell o)) (hd : D.grade d.1 = D.grade o)
    (he : D.grade e.1 = D.grade o) :
    sem.E o d = sem.E o e ↔
      ∀ p, RespectsSemanticsBelow sem (D.cell o) p → p d = p e := by
  constructor
  · intro h p hp
    exact le_antisymm ((source_le_iff_forced hc hu d e hd he).mp h.le p hp)
      ((source_le_iff_forced hc hu e d he hd).mp h.ge p hp)
  · intro h
    exact h (sem.E o) (hc o)

/-- If a display merges distinct sources, the old row itself is a lawful
separating section. The collision is not another existence problem. -/
theorem collision_witness (hc : sem.IsConsistent)
    (p : D.below (D.cell o) → ExtOrd) (d e : D.below (D.cell o))
    (hdisplay : p d = p e) (hsource : sem.E o d ≠ sem.E o e) :
    ∃ q, RespectsSemanticsBelow sem (D.cell o) q ∧ p d = p e ∧ q d ≠ q e :=
  ⟨sem.E o, hc o, hdisplay, hsource⟩

/-- No scalar recoding of a collapsed display can cover the literal old
row. Equality of sources forces equality of targets at equal grades. -/
theorem display_recoding_misses_row (p : D.below (D.cell o) → ExtOrd)
    (d e : D.below (D.cell o)) (hg : D.grade d.1 = D.grade e.1)
    (hdisplay : p d = p e) (hsource : sem.E o d ≠ sem.E o e)
    (encode : ExtOrd → ExtOrd) :
    ¬ TransformsTo (fun d : D.below (D.cell o) => D.grade d.1)
      (fun d => encode (p d)) (sem.E o) := by
  rintro ⟨g, τ, _, _, _, _, _, hr⟩
  apply hsource
  rw [hr d, hr e]
  change min (τ (encode (p d))) (g (D.grade d.1)) =
    min (τ (encode (p e))) (g (D.grade e.1))
  rw [hdisplay, hg]

/-- The collision persists under any new controller cap dominating the old
diagonal. Non-strict domination suffices; no larger prescribed cap is needed. -/
theorem display_recoding_misses_capped_row (hc : sem.IsConsistent) (hu : UniqueAt o)
    (p : D.below (D.cell o) → ExtOrd) (d e : D.below (D.cell o))
    (hd : D.grade d.1 = D.grade o) (he : D.grade e.1 = D.grade o)
    (hdisplay : p d = p e) (hsource : sem.E o d ≠ sem.E o e)
    (encode : ExtOrd → ExtOrd) {C : ExtOrd} (hC : sem.E o (owner o) ≤ C) :
    ¬ TransformsTo (fun d : D.below (D.cell o) => D.grade d.1)
      (fun d => encode (p d)) (fun d => min (sem.E o d) C) := by
  rintro ⟨g, τ, _, _, _, _, _, hr⟩
  have hdC := (label_le_owner (hc o) hu d hd).trans hC
  have heC := (label_le_owner (hc o) hu e he).trans hC
  have hrd := hr d
  have hre := hr e
  change min (sem.E o d) C = min (τ (encode (p d))) (g (D.grade d.1)) at hrd
  change min (sem.E o e) C = min (τ (encode (p e))) (g (D.grade e.1)) at hre
  rw [min_eq_left hdC] at hrd
  rw [min_eq_left heC] at hre
  apply hsource
  rw [hrd, hre]
  rw [hdisplay, hd, he]

end VaughtConjecture.Knight.DonorSourceRefinement
