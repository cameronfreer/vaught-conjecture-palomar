/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutLayerCarrier

/-! # Retaining higher proper owners around two constructed lower layers

The same two controller inventories are installed over the cut boundary and
over the entire boundary. Their lower domains through the cut are identical.
No higher proper owner, lower controller, or occurrence is discarded.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GradeCutPairCarrier
open Transform Value ExtOrd SourceLayerCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q R : Type*) [Fintype Q] [Fintype R]
variable (j k : ℕ) (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)

abbrev lower := SourceLayerCarrier.scheme D Q j hj hjA
abbrev enlarged := SourceLayerCarrier.scheme (lower D Q j hj hjA) R k hk hkA
abbrev small := enlarged (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA

def occEquiv : ((Cell D ⊕ Q) ⊕ R) ≃ Cell (enlarged D Q R j k hj hjA hk hkA) :=
  (Equiv.sumCongr (enumeration D Q j hj hjA) (Equiv.refl R)).trans
    (enumeration (lower D Q j hj hjA) R k hk hkA)

def cell (x : (Cell D ⊕ Q) ⊕ R) := occEquiv D Q R j k hj hjA hk hkA x

def idx : (Cell D ⊕ Q) ⊕ R → Finset ι × ℕ
  | .inl (.inl d) => D.cell d
  | .inl (.inr _) => (A, j)
  | .inr _ => (A, k)

theorem cell_idx (x : (Cell D ⊕ Q) ⊕ R) :
    (enlarged D Q R j k hj hjA hk hkA).cell (cell D Q R j k hj hjA hk hkA x) =
      idx D Q R j k x := by
  rcases x with (d | q) | r
  · change (enlarged D Q R j k hj hjA hk hkA).cell
      (toCell _ R k hk hkA (.inl (toCell D Q j hj hjA (.inl d)))) = D.cell d
    simp only [cell_toCell, index]
  · change (enlarged D Q R j k hj hjA hk hkA).cell
      (toCell _ R k hk hkA (.inl (toCell D Q j hj hjA (.inr q)))) = (A, j)
    simp only [cell_toCell, index]
  · exact cell_toCell _ R k hk hkA (.inr r)

abbrev old (d : Cell D) := cell D Q R j k hj hjA hk hkA (.inl (.inl d))

theorem old_order : StrictMono (old D Q R j k hj hjA hk hkA) :=
  (SourceLayerCarrier.old_order (lower D Q j hj hjA) R k hk hkA).comp
    (SourceLayerCarrier.old_order D Q j hj hjA)

def embed (d : Cell (small D Q R j k hj hjA hk hkA)) :=
  cell D Q R j k hj hjA hk hkA
    (Sum.map (Sum.map (GradeCutBoundary.toCell D k) id) id
      ((occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA).symm d))

theorem embed_cell (x : (Cell (GradeCutBoundary.scheme D k) ⊕ Q) ⊕ R) :
    embed D Q R j k hj hjA hk hkA
      (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA x) =
    cell D Q R j k hj hjA hk hkA (Sum.map (Sum.map (GradeCutBoundary.toCell D k) id) id x) := by
  simp only [embed, cell, Equiv.symm_apply_apply]

theorem embed_index (d : Cell (small D Q R j k hj hjA hk hkA)) :
    (enlarged D Q R j k hj hjA hk hkA).cell (embed D Q R j k hj hjA hk hkA d) =
      (small D Q R j k hj hjA hk hkA).cell d := by
  obtain ⟨x, rfl⟩ := (occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA).surjective d
  change (enlarged D Q R j k hj hjA hk hkA).cell
    (embed D Q R j k hj hjA hk hkA (cell _ _ _ _ _ _ _ _ _ x)) =
      (small D Q R j k hj hjA hk hkA).cell (cell _ _ _ _ _ _ _ _ _ x)
  rw [embed_cell, cell_idx, cell_idx]
  rcases x with (d | q) | r <;> rfl

theorem embed_injective : Function.Injective (embed D Q R j k hj hjA hk hkA) := by
  intro d e h
  apply (occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA).symm.injective
  exact (Sum.map_injective.mpr ⟨Sum.map_injective.mpr
    ⟨(GradeCutBoundary.toCell D k).injective, Function.injective_id⟩,
      Function.injective_id⟩) ((occEquiv D Q R j k hj hjA hk hkA).injective h)

theorem exhaustive (d : Cell (enlarged D Q R j k hj hjA hk hkA))
    (hd : (enlarged D Q R j k hj hjA hk hkA).grade d ≤ k) :
    ∃ c, embed D Q R j k hj hjA hk hkA c = d := by
  obtain ⟨x, rfl⟩ := (occEquiv D Q R j k hj hjA hk hkA).surjective d
  change (enlarged D Q R j k hj hjA hk hkA).grade (cell _ _ _ _ _ _ _ _ _ x) ≤ k at hd
  rw [CellScheme.grade, cell_idx] at hd
  rcases x with (d | q) | r
  · obtain ⟨c, hc⟩ := GradeCutBoundary.exhaustive D k hd
    refine ⟨cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inl (.inl c)), ?_⟩
    rw [embed_cell]
    change cell _ _ _ _ _ _ _ _ _ (.inl (.inl (GradeCutBoundary.toCell D k c))) = _
    rw [hc]; rfl
  · exact ⟨cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inl (.inr q)),
      embed_cell D Q R j k hj hjA hk hkA _⟩
  · exact ⟨cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inr r),
      embed_cell D Q R j k hj hjA hk hkA _⟩

def belowEquiv (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ k) :
    (small D Q R j k hj hjA hk hkA).below BJ ≃
      (enlarged D Q R j k hj hjA hk hkA).below BJ :=
  Equiv.ofBijective (fun d => ⟨embed D Q R j k hj hjA hk hkA d.1, by
    simpa only [embed_index] using d.2⟩) ⟨by
      intro d e h
      exact Subtype.ext (embed_injective D Q R j k hj hjA hk hkA (congrArg Subtype.val h)), by
      intro d
      obtain ⟨c, hc⟩ := exhaustive D Q R j k hj hjA hk hkA d.1 (d.2.2.trans hBJ)
      refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
      simpa only [← embed_index D Q R j k hj hjA hk hkA c, hc] using d.2⟩

def properEquiv (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) :
    D.below BJ ≃ (enlarged D Q R j k hj hjA hk hkA).below BJ :=
  (GradeCutLayerCarrier.properEquiv D Q j hj hjA BJ hB).trans
    (GradeCutLayerCarrier.properEquiv (lower D Q j hj hjA) R k hk hkA BJ hB)

theorem properEquiv_val (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) (d : D.below BJ) :
    (properEquiv D Q R j k hj hjA hk hkA BJ hB d).1 = old D Q R j k hj hjA hk hkA d.1 := rfl

theorem small_grade (hjk : j ≤ k) (d : Cell (small D Q R j k hj hjA hk hkA)) :
    (small D Q R j k hj hjA hk hkA).grade d ≤ k := by
  obtain ⟨x, rfl⟩ := (occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA).surjective d
  change (small D Q R j k hj hjA hk hkA).grade (cell _ _ _ _ _ _ _ _ _ x) ≤ k
  rw [CellScheme.grade, cell_idx]
  rcases x with (d | q) | r
  · exact GradeCutBoundary.grade_bound D k d
  · exact hjk
  · exact le_rfl

end
end VaughtConjecture.Knight.GradeCutPairCarrier
