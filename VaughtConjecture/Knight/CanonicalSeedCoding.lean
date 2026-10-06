/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalCodingSupport

/-! # Coding of the actual retained canonical seed pair

Every long old row is transported literally. New values are coded because
their boundary fields and supported grid/orbit values are coded.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalSeedCoding
open Transform Value ExtOrd SourcePrefixRows SourcePrefixLayer CanonicalCodingSupport
open PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

theorem fieldLayer (sem : Semantics D) (j : ℕ) (X : Type*) [Fintype X]
    (occ : Cell D → X) (hj : 0 < j) (hA : j ≤ A.card)
    (hp : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ j)
    (hc : sem.IsCoded) : (CanonicalFieldLayer.rows sem j X occ hj hA hp hg).IsCoded := by
  apply layer D _ j hj hA (SeparatedSourceLayerCarrier.separated_of_proper D j hp)
    sem _ hc (CanonicalFieldLayer.inherited_row sem j X occ hj hA hp hg)
  intro q d
  let F := CanonicalFieldLayer.data sem j X occ hj hA hp hg
  change IsCodedLabel j (F.rows.E (CanonicalFieldLayer.controller sem j X occ hj hA q).1 d)
  rw [F.row_new (CanonicalFieldLayer.controller sem j X occ hj hA q) d]
  by_cases hd : (CanonicalFieldLayer.scheme sem j X occ hj hA).cell d.1 = (A, j)
  · rw [show d.1 = (⟨d.1, hd⟩ : Controller _ j).1 from rfl, F.profile_new]
    exact grid j _ (cut_mem (sourceGrid_bot _ _) _ _)
  · obtain ⟨x, hx⟩ := SourceLayerCarrier.old_occurrence D
      (CanonicalFieldLayer.Profile sem j X occ) j hj hA d.1 hd
    change IsCodedLabel j (CanonicalFieldLayer.source sem j X occ hj hA hp hg q d.1)
    rw [hx, CanonicalFieldLayer.source_old]
    exact field sem j occ q (occ x)

theorem cutLayer (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hA : j ≤ A.card)
    (hp : ∀ d : Cell D, D.scope d ≠ A) (hc : sem.IsCoded) :
    (CanonicalGradeCutSections.rows sem j hj hA hp).IsCoded := by
  let Q := CanonicalGradeCutSections.Profiles sem j
  have low := fieldLayer (GradeCutBoundary.rows D j sem) j (Cell D)
    (GradeCutBoundary.toCell D j) hj hA (GradeCutBoundary.proper D j hp)
    (GradeCutBoundary.grade_bound D j) (gradeCut sem j hc)
  apply layer D Q j hj hA (SeparatedSourceLayerCarrier.separated_of_proper D j hp)
    sem _ hc (CanonicalGradeCutSections.old_row sem j hj hA hp)
  intro q d
  rw [CanonicalGradeCutSections.rows, GradeCutLayerRows.rows_toCell]
  change IsCodedLabel j ((CanonicalGradeCutSections.lowerRows sem j hj hA hp).E
    (SourceLayerCarrier.toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inr q)) _)
  have he : (CanonicalGradeCutSections.lower sem j hj hA).grade
      (SourceLayerCarrier.toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inr q)) = j :=
    congrArg Prod.snd (SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inr q))
  apply at_grade he
  exact low (SourceLayerCarrier.toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inr q)) _

theorem mixed (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
    (hp : ∀ d : Cell D, D.scope d ≠ A) (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
    (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k) (hc : sem.IsCoded) :
    (CanonicalMixedGradeLayers.rows sem j hj hjA hp k hg hk hkA hjk).IsCoded := by
  apply layer (CanonicalMixedGradeLayers.lowerScheme sem j hj hjA) _ k hk hkA
    (CanonicalMixedGradeLayers.lower_separated sem j hj hjA hp k hjk)
    (CanonicalMixedGradeLayers.lowerSem sem j hj hjA hp) _
    (cutLayer sem j hj hjA hp hc)
    (CanonicalMixedGradeLayers.inherited_row sem j hj hjA hp k hg hk hkA hjk)
  intro q d
  let F := CanonicalMixedGradeLayers.data sem j hj hjA hp k hg hk hkA hjk
  change IsCodedLabel k
    (F.rows.E (CanonicalMixedGradeLayers.controller sem j hj hjA k hk hkA q).1 d)
  rw [F.row_new (CanonicalMixedGradeLayers.controller sem j hj hjA k hk hkA q) d]
  apply supported (fun _ hh => grid k _ hh) (field sem k id q)
  exact CanonicalMixedGradeLayers.source_supported sem j hj hjA hp k hg hk hkA hjk q d.1

theorem pairSplice (D : CellScheme A) (Q R : Type*) [Fintype Q] [Fintype R]
    (j k : ℕ) (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)
    (hp : ∀ d : Cell D, D.scope d ≠ A) (hjk : j ≤ k)
    (sem : Semantics D) (low : Semantics (GradeCutPairCarrier.small D Q R j k hj hjA hk hkA))
    (hc : sem.IsCoded) (hl : low.IsCoded) :
    (GradeCutPairRows.rows D Q R j k hj hjA hk hkA hp hjk sem low).IsCoded := by
  intro c d
  obtain ⟨x, rfl⟩ := (GradeCutPairCarrier.occEquiv D Q R j k hj hjA hk hkA).surjective c
  change IsCodedLabel ((GradeCutPairCarrier.enlarged D Q R j k hj hjA hk hkA).grade
    (GradeCutPairCarrier.cell D Q R j k hj hjA hk hkA x))
    ((GradeCutPairRows.rows D Q R j k hj hjA hk hkA hp hjk sem low).E
      (GradeCutPairCarrier.cell D Q R j k hj hjA hk hkA x) d)
  apply at_grade (congrArg Prod.snd
    (GradeCutPairCarrier.cell_idx D Q R j k hj hjA hk hkA x)).symm
  rw [GradeCutPairRows.rows_cell D Q R j k hj hjA hk hkA hp hjk sem low x d]
  rcases x with (c | q) | r
  · exact hc c _
  · exact at_grade (congrArg Prod.snd (GradeCutPairCarrier.cell_idx
      (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inl (.inr q)))) (hl _ _)
  · exact at_grade (congrArg Prod.snd (GradeCutPairCarrier.cell_idx
      (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inr r))) (hl _ _)

theorem pair (sem : Semantics D) (hA : 2 ≤ A.card)
    (hp : ∀ d : Cell D, D.scope d ≠ A) (hc : sem.IsCoded) :
    (CanonicalPairLocalSections.semantics sem hA hp).IsCoded := by
  apply pairSplice D _ _ 1 2 (by decide) _ (by decide) hA hp (by decide) sem _ hc
  exact mixed (GradeCutBoundary.rows D 2 sem) 1 (by decide) _
    (GradeCutBoundary.proper D 2 hp) 2 (GradeCutBoundary.grade_bound D 2)
    (by decide) hA (by decide) (gradeCut sem 2 hc)

end
end VaughtConjecture.Knight.CanonicalSeedCoding
