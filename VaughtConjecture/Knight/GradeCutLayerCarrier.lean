/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutBoundary

/-! # Admitting higher proper owners alongside a constructed lower layer

The small carrier adds full-scope grade-j controllers to the grade-j boundary
cut. The enlarged carrier retains the entire original boundary and the very
same controller inventory. Its lower domains through j are exactly the small
carrier's, while every proper old owner's lower domain is exactly the old one.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GradeCutLayerCarrier

open Transform Value ExtOrd
open SourceLayerCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q : Type*) [Fintype Q] (j : ℕ)
variable (hj : 0 < j) (hA : j ≤ A.card)

abbrev small := scheme (GradeCutBoundary.scheme D j) Q j hj hA
abbrev enlarged := scheme D Q j hj hA

def embedOcc : Cell (GradeCutBoundary.scheme D j) ⊕ Q → Cell D ⊕ Q :=
  Sum.map (GradeCutBoundary.toCell D j) id

def embed (d : Cell (small D Q j hj hA)) : Cell (enlarged D Q j hj hA) :=
  toCell D Q j hj hA (embedOcc D Q j (toOcc (GradeCutBoundary.scheme D j) Q j hj hA d))

theorem embed_toCell (x : Cell (GradeCutBoundary.scheme D j) ⊕ Q) :
    embed D Q j hj hA (toCell (GradeCutBoundary.scheme D j) Q j hj hA x) =
      toCell D Q j hj hA (embedOcc D Q j x) := by
  simp only [embed, toOcc_toCell]

theorem embed_cell (d : Cell (small D Q j hj hA)) :
    (enlarged D Q j hj hA).cell (embed D Q j hj hA d) =
      (small D Q j hj hA).cell d := by
  rw [embed, cell_toCell, cell_eq]
  cases toOcc (GradeCutBoundary.scheme D j) Q j hj hA d <;> rfl

theorem embed_injective : Function.Injective (embed D Q j hj hA) := by
  intro d e h
  apply (enumeration (GradeCutBoundary.scheme D j) Q j hj hA).symm.injective
  have he := (enumeration D Q j hj hA).injective h
  change embedOcc D Q j _ = embedOcc D Q j _ at he
  exact (Sum.map_injective.mpr
    ⟨(GradeCutBoundary.toCell D j).injective, Function.injective_id⟩) he

theorem small_grade (d : Cell (small D Q j hj hA)) :
    (small D Q j hj hA).grade d ≤ j := by
  change ((small D Q j hj hA).cell d).2 ≤ j
  rw [cell_eq]
  cases toOcc (GradeCutBoundary.scheme D j) Q j hj hA d with
  | inl c => exact GradeCutBoundary.grade_bound D j c
  | inr q => exact le_rfl

theorem exhaustive (d : Cell (enlarged D Q j hj hA))
    (hd : (enlarged D Q j hj hA).grade d ≤ j) : ∃ c, embed D Q j hj hA c = d := by
  cases he : toOcc D Q j hj hA d with
  | inl c =>
    have hc : D.grade c ≤ j := by
      simpa only [CellScheme.grade, cell_eq, he, index] using hd
    obtain ⟨a, ha⟩ := GradeCutBoundary.exhaustive D j hc
    refine ⟨toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inl a), ?_⟩
    rw [embed_toCell]
    change toCell D Q j hj hA (.inl (GradeCutBoundary.toCell D j a)) = d
    rw [ha, ← he, toCell_toOcc]
  | inr q =>
    refine ⟨toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inr q), ?_⟩
    rw [embed_toCell]
    change toCell D Q j hj hA (.inr q) = d
    rw [← he, toCell_toOcc]

def belowEquiv (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j) :
    (small D Q j hj hA).below BJ ≃ (enlarged D Q j hj hA).below BJ :=
  Equiv.ofBijective (fun d => ⟨embed D Q j hj hA d.1, by
    simpa only [embed_cell] using d.2⟩) ⟨by
      intro d e h
      exact Subtype.ext (embed_injective D Q j hj hA (congrArg Subtype.val h)), by
      intro d
      obtain ⟨c, hc⟩ := exhaustive D Q j hj hA d.1 (d.2.2.trans hBJ)
      refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
      simpa only [← embed_cell D Q j hj hA c, hc] using d.2⟩

theorem belowEquiv_val (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j)
    (d : (small D Q j hj hA).below BJ) :
    (belowEquiv D Q j hj hA BJ hBJ d).1 = embed D Q j hj hA d.1 := rfl

def wholeEquiv : Cell (small D Q j hj hA) ≃ (enlarged D Q j hj hA).below (A, j) :=
  Equiv.ofBijective (fun d => ⟨embed D Q j hj hA d, by
    rw [embed_cell]
    exact ⟨D.isPlan.subset_of_mem ((small D Q j hj hA).scope_mem_plan d),
      small_grade D Q j hj hA d⟩⟩) ⟨by
      intro d e h
      exact embed_injective D Q j hj hA (congrArg Subtype.val h), by
      intro d
      obtain ⟨c, hc⟩ := exhaustive D Q j hj hA d.1 d.2.2
      exact ⟨c, Subtype.ext hc⟩⟩

theorem wholeEquiv_val (d : Cell (small D Q j hj hA)) :
    (wholeEquiv D Q j hj hA d).1 = embed D Q j hj hA d := rfl

abbrev ownerEquiv (hp : ∀ d : Cell D, D.scope d ≠ A) (c : Cell D) :=
  SeparatedSourceLayerCarrier.ownerEquiv D Q j hj hA
    (SeparatedSourceLayerCarrier.separated_of_proper D j hp) c

def properEquiv (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) :
    D.below BJ ≃ (enlarged D Q j hj hA).below BJ :=
  Equiv.ofBijective (fun d => ⟨toCell D Q j hj hA (.inl d.1), by
    simpa only [cell_toCell, index] using d.2⟩) ⟨by
      intro d e h
      exact Subtype.ext ((old_order D Q j hj hA).injective (congrArg Subtype.val h)), by
      intro d
      cases he : toOcc D Q j hj hA d.1 with
      | inl c =>
        have hc : GradedLe (D.cell c) BJ := by
          simpa only [cell_eq, he, index] using d.2
        refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
        change toCell D Q j hj hA (.inl c) = d.1
        rw [← he, toCell_toOcc]
      | inr q =>
        have hc : A ⊆ BJ.1 := by
          simpa only [CellScheme.scope, cell_eq, he, index] using d.2.1
        exact False.elim (hB hc)⟩

end
end VaughtConjecture.Knight.GradeCutLayerCarrier
