/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutLayerCarrier

/-! # Literal row splice at a grade cut

Retain all proper boundary rows, including higher-grade and long rows. The
full-scope rows already constructed on the smaller grade cut are transported
across their exact lower domains; their source values are not renormalized.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GradeCutLayerRows

open Transform Value ExtOrd SourceLayerCarrier GradeCutLayerCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q : Type*) [Fintype Q] (j : ℕ)
variable (hj : 0 < j) (hA : j ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)
variable (sem : Semantics D) (low : Semantics (small D Q j hj hA))

include hp in
theorem proper_scope (c : Cell D) : ¬ A ⊆ D.scope c := by
  intro hc
  exact hp c (Finset.Subset.antisymm (D.isPlan.subset_of_mem (D.scope_mem_plan c)) hc)

def oldBelow (c : Cell D) := properEquiv D Q j hj hA (D.cell c) (proper_scope D hp c)

def rowAt (x : Cell D ⊕ Q) : (enlarged D Q j hj hA).below (index D Q j x) → ExtOrd :=
  match x with
  | .inl c => fun d => sem.E c ((oldBelow D Q j hj hA hp c).symm d)
  | .inr q => fun d => low.E (toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inr q))
      ⟨((belowEquiv D Q j hj hA (A, j) le_rfl).symm d).1, by
        simpa only [cell_toCell, index] using
          ((belowEquiv D Q j hj hA (A, j) le_rfl).symm d).2⟩

theorem oldBelow_cell (c : Cell D) (d : (enlarged D Q j hj hA).below (D.cell c)) :
    D.cell ((oldBelow D Q j hj hA hp c).symm d).1 =
      (enlarged D Q j hj hA).cell d.1 := by
  have he := congrArg Subtype.val ((oldBelow D Q j hj hA hp c).apply_symm_apply d)
  change toCell D Q j hj hA (.inl _) = d.1 at he
  rw [← he, cell_toCell]
  rfl

theorem lowBelow_cell (d : (enlarged D Q j hj hA).below (A, j)) :
    (small D Q j hj hA).cell ((belowEquiv D Q j hj hA (A, j) le_rfl).symm d).1 =
      (enlarged D Q j hj hA).cell d.1 := by
  have he := congrArg Subtype.val
    ((belowEquiv D Q j hj hA (A, j) le_rfl).apply_symm_apply d)
  change embed D Q j hj hA _ = d.1 at he
  rw [← he, embed_cell]

theorem rowAt_orderly (x : Cell D ⊕ Q)
    (d : (enlarged D Q j hj hA).below (index D Q j x)) :
    rowAt D Q j hj hA hp sem low x d =
      extVisibilityReplace (rowAt D Q j hj hA hp sem low x d)
        ((enlarged D Q j hj hA).grade d.1) ((enlarged D Q j hj hA).grade d.1) := by
  cases x with
  | inl a =>
    have hv := sem.orderly a ((oldBelow D Q j hj hA hp a).symm d)
    have hg := congrArg Prod.snd (oldBelow_cell D Q j hj hA hp a d)
    change D.grade _ = (enlarged D Q j hj hA).grade d.1 at hg
    exact hv.trans (congrArg (fun i => extVisibilityReplace _ i i) hg)
  | inr q =>
    have hv := low.orderly (toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inr q))
      ⟨((belowEquiv D Q j hj hA (A, j) le_rfl).symm d).1, by
        rw [cell_toCell]
        exact ((belowEquiv D Q j hj hA (A, j) le_rfl).symm d).2⟩
    have hg := congrArg Prod.snd (lowBelow_cell D Q j hj hA d)
    change (small D Q j hj hA).grade _ = (enlarged D Q j hj hA).grade d.1 at hg
    exact hv.trans (congrArg (fun i => extVisibilityReplace _ i i) hg)

def rows : Semantics (enlarged D Q j hj hA) where
  E c d := rowAt D Q j hj hA hp sem low (toOcc D Q j hj hA c)
    ⟨d.1, by simpa only [← cell_eq] using d.2⟩
  orderly c d := rowAt_orderly D Q j hj hA hp sem low _ _

theorem rowAt_congr {x y : Cell D ⊕ Q} (hxy : x = y)
    {d : (enlarged D Q j hj hA).below (index D Q j x)}
    {e : (enlarged D Q j hj hA).below (index D Q j y)} (hde : d.1 = e.1) :
    rowAt D Q j hj hA hp sem low x d = rowAt D Q j hj hA hp sem low y e := by
  subst y
  rw [Subtype.ext hde]

theorem rows_toCell (x : Cell D ⊕ Q)
    (d : (enlarged D Q j hj hA).below ((enlarged D Q j hj hA).cell
      (toCell D Q j hj hA x))) :
    (rows D Q j hj hA hp sem low).E (toCell D Q j hj hA x) d =
      rowAt D Q j hj hA hp sem low x
        ⟨d.1, by simpa only [cell_toCell] using d.2⟩ :=
  rowAt_congr D Q j hj hA hp sem low (toOcc_toCell D Q j hj hA x) rfl

theorem old_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows D Q j hj hA hp sem low).E (toCell D Q j hj hA (.inl c))
      (ownerEquiv D Q j hj hA hp c d) = sem.E c d := by
  rw [rows_toCell]
  change sem.E c ((oldBelow D Q j hj hA hp c).symm ((oldBelow D Q j hj hA hp c) d)) = _
  rw [Equiv.symm_apply_apply]

theorem controller_row (q : Q)
    (d : (small D Q j hj hA).below (A, j)) :
    (rows D Q j hj hA hp sem low).E (toCell D Q j hj hA (.inr q))
      ⟨embed D Q j hj hA d.1, by
        rw [cell_toCell, embed_cell]; exact d.2⟩ =
    low.E (toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inr q))
      ⟨d.1, by rw [cell_toCell]; exact d.2⟩ := by
  refine (rows_toCell D Q j hj hA hp sem low (.inr q) _).trans ?_
  apply low.E_congr' rfl
  exact congrArg (fun z : (small D Q j hj hA).below (A, j) => z.1)
    ((belowEquiv D Q j hj hA (A, j) le_rfl).symm_apply_apply d)

theorem old_respects_iff (c : Cell D)
    (p : (enlarged D Q j hj hA).below
      ((enlarged D Q j hj hA).cell (toCell D Q j hj hA (.inl c))) → ExtOrd) :
    RespectsSemanticsBelow (rows D Q j hj hA hp sem low) _ p ↔
      RespectsSemanticsBelow sem (D.cell c) (p ∘ ownerEquiv D Q j hj hA hp c) := by
  have ht := respects_iff_of_equiv (sem' := sem) (sem := rows D Q j hj hA hp sem low)
    (ownerEquiv D Q j hj hA hp c)
    (fun d => (congrArg Prod.snd (cell_toCell D Q j hj hA (.inl d.1))).symm)
    (fun d e => by
      change D.scope d.1 ⊆ D.scope e.1 ↔
        ((enlarged D Q j hj hA).cell (toCell D Q j hj hA (.inl d.1))).1 ⊆
        ((enlarged D Q j hj hA).cell (toCell D Q j hj hA (.inl e.1))).1
      rw [cell_toCell, cell_toCell]; rfl)
    (fun b d _ => (old_row D Q j hj hA hp sem low b.1 d).symm)
    (p ∘ ownerEquiv D Q j hj hA hp c)
  have he : (p ∘ ownerEquiv D Q j hj hA hp c) ∘
      (ownerEquiv D Q j hj hA hp c).symm = p := by
    funext d; simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [he] at ht
  exact ht.symm

variable (hmatch : ∀ (c : Cell (GradeCutBoundary.scheme D j))
  (d : (GradeCutBoundary.scheme D j).below ((GradeCutBoundary.scheme D j).cell c)),
  low.E (toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inl c))
    (ownerEquiv (GradeCutBoundary.scheme D j) Q j hj hA (GradeCutBoundary.proper D j hp) c d) =
  (GradeCutBoundary.rows D j sem).E c d)

include hmatch

theorem embedded_row (c : Cell (small D Q j hj hA))
    (d : (small D Q j hj hA).below ((small D Q j hj hA).cell c)) :
    (rows D Q j hj hA hp sem low).E (embed D Q j hj hA c)
      ⟨embed D Q j hj hA d.1, by simpa only [embed_cell] using d.2⟩ = low.E c d := by
  obtain ⟨x, rfl⟩ := (enumeration (GradeCutBoundary.scheme D j) Q j hj hA).surjective c
  cases x with
  | inl a =>
    obtain ⟨e, rfl⟩ := (ownerEquiv (GradeCutBoundary.scheme D j) Q j hj hA
      (GradeCutBoundary.proper D j hp) a).surjective d
    have he := old_row D Q j hj hA hp sem low (GradeCutBoundary.toCell D j a)
      (GradeCutBoundary.belowEquiv D j ((GradeCutBoundary.scheme D j).cell a)
        (GradeCutBoundary.grade_bound D j a) e)
    refine (Semantics.E_congr' _ (embed_toCell D Q j hj hA (.inl a)) ?_).trans
      (he.trans (hmatch a e).symm)
    exact embed_toCell D Q j hj hA (.inl e.1)
  | inr q =>
    let e : (small D Q j hj hA).below (A, j) :=
      ⟨d.1, by
        have hc := d.2
        change GradedLe ((small D Q j hj hA).cell d.1)
          ((small D Q j hj hA).cell
            (toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inr q))) at hc
        rwa [cell_toCell] at hc⟩
    exact (Semantics.E_congr' _ (embed_toCell D Q j hj hA (.inr q)) rfl).trans
      (controller_row D Q j hj hA hp sem low q e)

theorem lower_respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j)
    (p : (small D Q j hj hA).below BJ → ExtOrd) :
    RespectsSemanticsBelow low BJ p ↔
      RespectsSemanticsBelow (rows D Q j hj hA hp sem low) BJ
        (p ∘ (belowEquiv D Q j hj hA BJ hBJ).symm) :=
  respects_iff_of_equiv (belowEquiv D Q j hj hA BJ hBJ)
    (fun d => (congrArg Prod.snd (embed_cell D Q j hj hA d.1)).symm)
    (fun d e => by
      change ((small D Q j hj hA).cell d.1).1 ⊆ ((small D Q j hj hA).cell e.1).1 ↔
        ((enlarged D Q j hj hA).cell (embed D Q j hj hA d.1)).1 ⊆
        ((enlarged D Q j hj hA).cell (embed D Q j hj hA e.1)).1
      rw [embed_cell, embed_cell])
    (fun b d _ => (embedded_row D Q j hj hA hp sem low hmatch b.1 d).symm) p

omit hmatch in
theorem cast_respects {B C : Finset ι × ℕ} (h : B = C)
    {p : D.below B → ExtOrd} (hr : RespectsSemanticsBelow sem B p) :
    RespectsSemanticsBelow sem C (fun d => p ⟨d.1, h.symm ▸ d.2⟩) := by
  subst C
  exact hr

theorem consistent (hs : sem.IsConsistent) (hl : low.IsConsistent) :
    (rows D Q j hj hA hp sem low).IsConsistent := by
  intro c
  obtain ⟨x, rfl⟩ := (enumeration D Q j hj hA).surjective c
  cases x with
  | inl a =>
    apply (old_respects_iff D Q j hj hA hp sem low a _).mpr
    change RespectsSemanticsBelow sem (D.cell a) (fun d =>
      (rows D Q j hj hA hp sem low).E (toCell D Q j hj hA (.inl a))
        (ownerEquiv D Q j hj hA hp a d))
    simpa only [old_row] using hs a
  | inr q =>
    have hc := cast_respects (small D Q j hj hA) low
      (cell_toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inr q))
      (hl (toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inr q)))
    have ht := (lower_respects_iff D Q j hj hA hp sem low hmatch (A, j) le_rfl _).mp
      hc
    have hu := cast_respects (enlarged D Q j hj hA) (rows D Q j hj hA hp sem low)
      (cell_toCell D Q j hj hA (.inr q)).symm ht
    convert hu using 1 <;> try rfl
    apply heq_of_eq
    funext d
    exact rows_toCell D Q j hj hA hp sem low (.inr q) d

omit hmatch in
theorem respects_of_lower {p : Cell D → ExtOrd}
    (hr : ∀ c, RespectsSemanticsBelow sem (D.cell c) (fun d => p d.1)) :
    RespectsSemantics sem p where
  orderly c := (hr c).orderly ⟨c, GradedLe.refl _⟩
  locality c := (hr c).locality ⟨c, GradedLe.refl _⟩
  availability c t hs hg := by
    obtain ⟨w, hw, hb⟩ := (hr t).availability ⟨c, hs, hg.le⟩
      ⟨t, GradedLe.refl _⟩ hs hg
    exact ⟨w.1, hw, hb⟩

omit hmatch in
def glue (p : Cell D → ExtOrd) (r : Cell (small D Q j hj hA) → ExtOrd)
    (d : Cell (enlarged D Q j hj hA)) : ExtOrd :=
  match toOcc D Q j hj hA d with
  | .inl c => p c
  | .inr q => r (toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inr q))

omit hmatch in
theorem glue_old (p : Cell D → ExtOrd) (r : Cell (small D Q j hj hA) → ExtOrd)
    (c : Cell D) : glue D Q j hj hA p r (toCell D Q j hj hA (.inl c)) = p c := by
  simp only [glue, toOcc_toCell]

omit hmatch in
theorem glue_embed (p : Cell D → ExtOrd) (r : Cell (small D Q j hj hA) → ExtOrd)
    (hr : ∀ c, r (toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inl c)) =
      p (GradeCutBoundary.toCell D j c)) (c : Cell (small D Q j hj hA)) :
    glue D Q j hj hA p r (embed D Q j hj hA c) = r c := by
  obtain ⟨x, rfl⟩ := (enumeration (GradeCutBoundary.scheme D j) Q j hj hA).surjective c
  change glue D Q j hj hA p r (embed D Q j hj hA
    (toCell (GradeCutBoundary.scheme D j) Q j hj hA x)) = _
  rw [embed_toCell]
  cases x with
  | inl c => exact (glue_old D Q j hj hA p r _).trans (hr c).symm
  | inr q =>
    change glue D Q j hj hA p r (toCell D Q j hj hA (.inr q)) = _
    simp only [glue, toOcc_toCell]
    rfl

theorem glue_respects {p : Cell D → ExtOrd} {r : Cell (small D Q j hj hA) → ExtOrd}
    (hpr : RespectsSemantics sem p) (hr : RespectsSemantics low r)
    (hag : ∀ c, r (toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inl c)) =
      p (GradeCutBoundary.toCell D j c)) :
    RespectsSemantics (rows D Q j hj hA hp sem low) (glue D Q j hj hA p r) := by
  apply respects_of_lower
  intro c
  obtain ⟨x, rfl⟩ := (enumeration D Q j hj hA).surjective c
  cases x with
  | inl a =>
    apply (old_respects_iff D Q j hj hA hp sem low a _).mpr
    change RespectsSemanticsBelow sem (D.cell a)
      (fun d => glue D Q j hj hA p r (toCell D Q j hj hA (.inl d.1)))
    simpa only [glue_old] using hpr.toBelow (D.cell a)
  | inr q =>
    let BJ := (enlarged D Q j hj hA).cell (toCell D Q j hj hA (.inr q))
    have hBJ : BJ.2 ≤ j := by dsimp only [BJ]; rw [cell_toCell]; exact le_rfl
    have ht := (lower_respects_iff D Q j hj hA hp sem low hmatch BJ hBJ _).mp (hr.toBelow BJ)
    change RespectsSemanticsBelow (rows D Q j hj hA hp sem low) BJ _
    have heq : (fun d : (enlarged D Q j hj hA).below BJ => glue D Q j hj hA p r d.1) =
        (fun d : (small D Q j hj hA).below BJ => r d.1) ∘
          (belowEquiv D Q j hj hA BJ hBJ).symm := by
      funext d
      have he := congrArg (fun z : (enlarged D Q j hj hA).below BJ => z.1)
        ((belowEquiv D Q j hj hA BJ hBJ).apply_symm_apply d)
      exact (congrArg (glue D Q j hj hA p r) he).symm.trans
        (glue_embed D Q j hj hA p r hag _)
    exact heq.symm ▸ ht

end
end VaughtConjecture.Knight.GradeCutLayerRows
