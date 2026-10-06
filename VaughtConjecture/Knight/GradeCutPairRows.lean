/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutPairCarrier
public import VaughtConjecture.Knight.GradeCutLayerRows

/-! # Literal row splice around two lower controller layers

Higher proper owners keep their entire original rows. Both lower controller
layers keep their already constructed rows, on exactly the same lower domains.
The overlap equation concerns existing inherited rows, not future locality.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GradeCutPairRows
open Transform Value ExtOrd GradeCutPairCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q R : Type*) [Fintype Q] [Fintype R]
variable (j k : ℕ) (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A) (hjk : j ≤ k)
variable (sem : Semantics D) (low : Semantics (small D Q R j k hj hjA hk hkA))

def ownerEquiv (c : Cell D) :=
  properEquiv D Q R j k hj hjA hk hkA (D.cell c) (GradeCutLayerRows.proper_scope D hp c)

def liftedRow (c : Cell (small D Q R j k hj hjA hk hkA)) :
    (enlarged D Q R j k hj hjA hk hkA).below
      ((small D Q R j k hj hjA hk hkA).cell c) → ExtOrd :=
  low.E c ∘ (belowEquiv D Q R j k hj hjA hk hkA _
    (small_grade D Q R j k hj hjA hk hkA hjk c)).symm

theorem liftedRow_orderly (c : Cell (small D Q R j k hj hjA hk hkA))
    (d : (enlarged D Q R j k hj hjA hk hkA).below
      ((small D Q R j k hj hjA hk hkA).cell c)) :
    SelfVis ((enlarged D Q R j k hj hjA hk hkA).grade d.1)
      (liftedRow D Q R j k hj hjA hk hkA hjk low c d) := by
  let e := belowEquiv D Q R j k hj hjA hk hkA _
    (small_grade D Q R j k hj hjA hk hkA hjk c)
  have he := congrArg Subtype.val (e.apply_symm_apply d)
  change embed D Q R j k hj hjA hk hkA (e.symm d).1 = d.1 at he
  have hg := congrArg Prod.snd (embed_index D Q R j k hj hjA hk hkA (e.symm d).1)
  rw [he] at hg
  change (enlarged D Q R j k hj hjA hk hkA).grade d.1 =
    (small D Q R j k hj hjA hk hkA).grade (e.symm d).1 at hg
  rw [hg]
  exact (low.orderly c (e.symm d)).symm

def rowAt (x : (Cell D ⊕ Q) ⊕ R) :
    (enlarged D Q R j k hj hjA hk hkA).below (idx D Q R j k x) → ExtOrd :=
  match x with
  | .inl (.inl c) => sem.E c ∘ (ownerEquiv D Q R j k hj hjA hk hkA hp c).symm
  | .inl (.inr q) => fun d =>
      liftedRow D Q R j k hj hjA hk hkA hjk low
        (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inl (.inr q)))
        ⟨d.1, by simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩
  | .inr r => fun d =>
      liftedRow D Q R j k hj hjA hk hkA hjk low
        (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inr r))
        ⟨d.1, by simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩

theorem rowAt_orderly (x : (Cell D ⊕ Q) ⊕ R)
    (d : (enlarged D Q R j k hj hjA hk hkA).below (idx D Q R j k x)) :
    SelfVis ((enlarged D Q R j k hj hjA hk hkA).grade d.1)
      (rowAt D Q R j k hj hjA hk hkA hp hjk sem low x d) := by
  rcases x with (c | q) | r
  · let e := ownerEquiv D Q R j k hj hjA hk hkA hp c
    have he := congrArg Subtype.val (e.apply_symm_apply d)
    change old D Q R j k hj hjA hk hkA (e.symm d).1 = d.1 at he
    have hg := congrArg Prod.snd (cell_idx D Q R j k hj hjA hk hkA (.inl (.inl (e.symm d).1)))
    change (enlarged D Q R j k hj hjA hk hkA).grade
      (old D Q R j k hj hjA hk hkA (e.symm d).1) = D.grade (e.symm d).1 at hg
    rw [he] at hg
    rw [hg]
    exact (sem.orderly c (e.symm d)).symm
  · dsimp only [rowAt]
    exact liftedRow_orderly D Q R j k hj hjA hk hkA hjk low
      (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inl (.inr q))) _
  · dsimp only [rowAt]
    exact liftedRow_orderly D Q R j k hj hjA hk hkA hjk low
      (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inr r)) _

def rows : Semantics (enlarged D Q R j k hj hjA hk hkA) where
  E c d := rowAt D Q R j k hj hjA hk hkA hp hjk sem low
    ((occEquiv D Q R j k hj hjA hk hkA).symm c)
    ⟨d.1, by
      have he := cell_idx D Q R j k hj hjA hk hkA ((occEquiv D Q R j k hj hjA hk hkA).symm c)
      change (enlarged D Q R j k hj hjA hk hkA).cell
        ((occEquiv D Q R j k hj hjA hk hkA) ((occEquiv D Q R j k hj hjA hk hkA).symm c)) = _ at he
      rw [Equiv.apply_symm_apply] at he
      rw [← he]
      exact d.2⟩
  orderly c d := (rowAt_orderly D Q R j k hj hjA hk hkA hp hjk sem low _ _).symm

theorem rowAt_congr {x y : (Cell D ⊕ Q) ⊕ R} (hxy : x = y)
    {d : (enlarged D Q R j k hj hjA hk hkA).below (GradeCutPairCarrier.idx D Q R j k x)}
    {e : (enlarged D Q R j k hj hjA hk hkA).below (GradeCutPairCarrier.idx D Q R j k y)}
    (hde : d.1 = e.1) :
    rowAt D Q R j k hj hjA hk hkA hp hjk sem low x d =
      rowAt D Q R j k hj hjA hk hkA hp hjk sem low y e := by
  subst y
  rw [Subtype.ext hde]

theorem rows_cell (x : (Cell D ⊕ Q) ⊕ R)
    (d : (enlarged D Q R j k hj hjA hk hkA).below
      ((enlarged D Q R j k hj hjA hk hkA).cell (cell D Q R j k hj hjA hk hkA x))) :
    (rows D Q R j k hj hjA hk hkA hp hjk sem low).E (cell D Q R j k hj hjA hk hkA x) d =
      rowAt D Q R j k hj hjA hk hkA hp hjk sem low x
        ⟨d.1, by simpa only [cell_idx] using d.2⟩ :=
  rowAt_congr D Q R j k hj hjA hk hkA hp hjk sem low
    ((occEquiv D Q R j k hj hjA hk hkA).symm_apply_apply x) rfl

theorem old_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows D Q R j k hj hjA hk hkA hp hjk sem low).E
      (old D Q R j k hj hjA hk hkA c)
      ⟨(ownerEquiv D Q R j k hj hjA hk hkA hp c d).1, by
        simpa only [old, cell_idx, GradeCutPairCarrier.idx] using
          (ownerEquiv D Q R j k hj hjA hk hkA hp c d).2⟩ =
    sem.E c d := by
  exact (rows_cell D Q R j k hj hjA hk hkA hp hjk sem low (.inl (.inl c)) _).trans
    (congrArg (sem.E c) ((ownerEquiv D Q R j k hj hjA hk hkA hp c).symm_apply_apply d))

variable (hmatch : ∀ (c : Cell (GradeCutBoundary.scheme D k))
    (d : (GradeCutBoundary.scheme D k).below ((GradeCutBoundary.scheme D k).cell c)),
    low.E (old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA c)
      ⟨old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA d.1, by
        simpa only [old, cell_idx, GradeCutPairCarrier.idx] using d.2⟩ =
      (GradeCutBoundary.rows D k sem).E c d)

include hmatch in
theorem embedded_row (c : Cell (small D Q R j k hj hjA hk hkA))
    (d : (small D Q R j k hj hjA hk hkA).below
      ((small D Q R j k hj hjA hk hkA).cell c)) :
    (rows D Q R j k hj hjA hk hkA hp hjk sem low).E (embed D Q R j k hj hjA hk hkA c)
      ⟨embed D Q R j k hj hjA hk hkA d.1, by simpa only [embed_index] using d.2⟩ = low.E c d := by
  obtain ⟨x, rfl⟩ := (occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA).surjective c
  change (rows D Q R j k hj hjA hk hkA hp hjk sem low).E
    (embed D Q R j k hj hjA hk hkA (cell _ _ _ _ _ _ _ _ _ x)) _ = _
  have helper (a : Cell (small D Q R j k hj hjA hk hkA))
      (e : (small D Q R j k hj hjA hk hkA).below ((small D Q R j k hj hjA hk hkA).cell a)) :
      liftedRow D Q R j k hj hjA hk hkA hjk low a
        ⟨embed D Q R j k hj hjA hk hkA e.1, by simpa only [embed_index] using e.2⟩ = low.E a e :=
    congrArg (low.E a) ((belowEquiv D Q R j k hj hjA hk hkA _
      (small_grade D Q R j k hj hjA hk hkA hjk a)).symm_apply_apply e)
  rcases x with (c | q) | r
  · let ep := properEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA
      ((GradeCutBoundary.scheme D k).cell c)
      (GradeCutLayerRows.proper_scope D hp (GradeCutBoundary.toCell D k c))
    let d' : (small D Q R j k hj hjA hk hkA).below ((GradeCutBoundary.scheme D k).cell c) :=
      ⟨d.1, by
        have hd := d.2
        change GradedLe _ ((small D Q R j k hj hjA hk hkA).cell
          (cell _ _ _ _ _ _ _ _ _ (.inl (.inl c)))) at hd
        simpa only [cell_idx, GradeCutPairCarrier.idx] using hd⟩
    obtain ⟨e, he⟩ := ep.surjective d'
    have hev := congrArg Subtype.val he
    change old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA e.1 = d.1 at hev
    have hr := old_row D Q R j k hj hjA hk hkA hp hjk sem low
      (GradeCutBoundary.toCell D k c)
      (GradeCutBoundary.belowEquiv D k _ (GradeCutBoundary.grade_bound D k c) e)
    have hc := embed_cell D Q R j k hj hjA hk hkA (.inl (.inl c))
    refine (Semantics.E_congr' _ hc ?_).trans (hr.trans ?_)
    · exact (congrArg (embed D Q R j k hj hjA hk hkA) hev).symm.trans
        (embed_cell D Q R j k hj hjA hk hkA (.inl (.inl e.1)))
    · exact (hmatch c e).symm.trans (low.E_congr' rfl hev)
  · have hc := embed_cell D Q R j k hj hjA hk hkA (.inl (.inr q))
    refine (Semantics.E_congr' _ hc
      (d' := ⟨embed D Q R j k hj hjA hk hkA d.1, by
        rw [embed_index, cell_idx]
        have hd := d.2
        change GradedLe _ ((small D Q R j k hj hjA hk hkA).cell
          (cell _ _ _ _ _ _ _ _ _ (.inl (.inr q)))) at hd
        rw [cell_idx] at hd
        exact hd⟩) rfl).trans ?_
    exact (rows_cell D Q R j k hj hjA hk hkA hp hjk sem low (.inl (.inr q)) _).trans
      (helper _ d)
  · have hc := embed_cell D Q R j k hj hjA hk hkA (.inr r)
    refine (Semantics.E_congr' _ hc
      (d' := ⟨embed D Q R j k hj hjA hk hkA d.1, by
        rw [embed_index, cell_idx]
        have hd := d.2
        change GradedLe _ ((small D Q R j k hj hjA hk hkA).cell
          (cell _ _ _ _ _ _ _ _ _ (.inr r))) at hd
        rw [cell_idx] at hd
        exact hd⟩) rfl).trans ?_
    exact (rows_cell D Q R j k hj hjA hk hkA hp hjk sem low (.inr r) _).trans
      (helper _ d)

theorem proper_respects_iff (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1)
    (p : D.below BJ → ExtOrd) :
    RespectsSemanticsBelow sem BJ p ↔
      RespectsSemanticsBelow (rows D Q R j k hj hjA hk hkA hp hjk sem low) BJ
        (p ∘ (properEquiv D Q R j k hj hjA hk hkA BJ hB).symm) := by
  apply respects_iff_of_equiv (properEquiv D Q R j k hj hjA hk hkA BJ hB)
    (fun d => ?_) (fun d e => ?_) (fun b d _ => ?_) p
  · exact (congrArg Prod.snd (cell_idx D Q R j k hj hjA hk hkA (.inl (.inl d.1)))).symm
  · change (D.cell d.1).1 ⊆ (D.cell e.1).1 ↔
      ((enlarged D Q R j k hj hjA hk hkA).cell (old D Q R j k hj hjA hk hkA d.1)).1 ⊆
      ((enlarged D Q R j k hj hjA hk hkA).cell (old D Q R j k hj hjA hk hkA e.1)).1
    simp only [old, cell_idx, GradeCutPairCarrier.idx]
  · exact (old_row D Q R j k hj hjA hk hkA hp hjk sem low b.1 d).symm

include hmatch in
theorem lower_respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ k)
    (p : (small D Q R j k hj hjA hk hkA).below BJ → ExtOrd) :
    RespectsSemanticsBelow low BJ p ↔
      RespectsSemanticsBelow (rows D Q R j k hj hjA hk hkA hp hjk sem low) BJ
        (p ∘ (belowEquiv D Q R j k hj hjA hk hkA BJ hBJ).symm) := by
  apply respects_iff_of_equiv (belowEquiv D Q R j k hj hjA hk hkA BJ hBJ)
    (fun d => (congrArg Prod.snd (embed_index D Q R j k hj hjA hk hkA d.1)).symm)
    (fun d e => ?_)
    (fun b d _ => (embedded_row D Q R j k hj hjA hk hkA hp hjk sem low hmatch b.1 d).symm) p
  change ((small D Q R j k hj hjA hk hkA).cell d.1).1 ⊆
      ((small D Q R j k hj hjA hk hkA).cell e.1).1 ↔
    ((enlarged D Q R j k hj hjA hk hkA).cell (embed D Q R j k hj hjA hk hkA d.1)).1 ⊆
      ((enlarged D Q R j k hj hjA hk hkA).cell (embed D Q R j k hj hjA hk hkA e.1)).1
  simp only [embed_index]

include hmatch in
theorem consistent (hs : sem.IsConsistent) (hl : low.IsConsistent) :
    (rows D Q R j k hj hjA hk hkA hp hjk sem low).IsConsistent := by
  have hold (c : Cell D) :
      RespectsSemanticsBelow (rows D Q R j k hj hjA hk hkA hp hjk sem low)
        ((enlarged D Q R j k hj hjA hk hkA).cell (old D Q R j k hj hjA hk hkA c))
        ((rows D Q R j k hj hjA hk hkA hp hjk sem low).E (old D Q R j k hj hjA hk hkA c)) := by
    have ht := (proper_respects_iff D Q R j k hj hjA hk hkA hp hjk sem low (D.cell c)
      (GradeCutLayerRows.proper_scope D hp c) _).mp (hs c)
    have hu := GradeCutLayerRows.cast_respects _ _
      (cell_idx D Q R j k hj hjA hk hkA (.inl (.inl c))).symm ht
    convert hu using 1
    funext d
    let e := ownerEquiv D Q R j k hj hjA hk hkA hp c
    let d' : (enlarged D Q R j k hj hjA hk hkA).below (D.cell c) :=
      ⟨d.1, by simpa only [old, cell_idx, GradeCutPairCarrier.idx] using d.2⟩
    have he : (e (e.symm d')).1 = d.1 :=
      congrArg (fun z : (enlarged D Q R j k hj hjA hk hkA).below (D.cell c) => z.1)
        (e.apply_symm_apply d')
    exact (Semantics.E_congr' _ rfl he).symm.trans
      (old_row D Q R j k hj hjA hk hkA hp hjk sem low c (e.symm d'))
  have hlow (c : Cell (small D Q R j k hj hjA hk hkA)) :
      RespectsSemanticsBelow (rows D Q R j k hj hjA hk hkA hp hjk sem low)
        ((enlarged D Q R j k hj hjA hk hkA).cell (embed D Q R j k hj hjA hk hkA c))
        ((rows D Q R j k hj hjA hk hkA hp hjk sem low).E (embed D Q R j k hj hjA hk hkA c)) := by
    have ht := (lower_respects_iff D Q R j k hj hjA hk hkA hp hjk sem low hmatch _
      (small_grade D Q R j k hj hjA hk hkA hjk c) _).mp (hl c)
    have hu := GradeCutLayerRows.cast_respects _ _ (embed_index D Q R j k hj hjA hk hkA c).symm ht
    convert hu using 1
    funext d
    let e := belowEquiv D Q R j k hj hjA hk hkA _ (small_grade D Q R j k hj hjA hk hkA hjk c)
    let d' : (enlarged D Q R j k hj hjA hk hkA).below
        ((small D Q R j k hj hjA hk hkA).cell c) :=
      ⟨d.1, by simpa only [embed_index] using d.2⟩
    have he : (e (e.symm d')).1 = d.1 :=
      congrArg (fun z : (enlarged D Q R j k hj hjA hk hkA).below
        ((small D Q R j k hj hjA hk hkA).cell c) => z.1) (e.apply_symm_apply d')
    exact (Semantics.E_congr' _ rfl he).symm.trans
      (embedded_row D Q R j k hj hjA hk hkA hp hjk sem low hmatch c (e.symm d'))
  intro c
  obtain ⟨x, rfl⟩ := (occEquiv D Q R j k hj hjA hk hkA).surjective c
  rcases x with (d | q) | r
  · exact hold d
  · have h := hlow (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inl (.inr q)))
    exact (congrArg (fun a => RespectsSemanticsBelow
      (rows D Q R j k hj hjA hk hkA hp hjk sem low)
      ((enlarged D Q R j k hj hjA hk hkA).cell a)
      ((rows D Q R j k hj hjA hk hkA hp hjk sem low).E a))
      (embed_cell D Q R j k hj hjA hk hkA (.inl (.inr q)))).mp h
  · have h := hlow (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inr r))
    exact (congrArg (fun a => RespectsSemanticsBelow
      (rows D Q R j k hj hjA hk hkA hp hjk sem low)
      ((enlarged D Q R j k hj hjA hk hkA).cell a)
      ((rows D Q R j k hj hjA hk hkA hp hjk sem low).E a))
      (embed_cell D Q R j k hj hjA hk hkA (.inr r))).mp h

def glue (p : Cell D → ExtOrd) (r : Cell (small D Q R j k hj hjA hk hkA) → ExtOrd)
    (d : Cell (enlarged D Q R j k hj hjA hk hkA)) : ExtOrd :=
  match (occEquiv D Q R j k hj hjA hk hkA).symm d with
  | .inl (.inl a) => p a
  | .inl (.inr q) => r (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inl (.inr q)))
  | .inr q => r (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inr q))

theorem glue_old (p : Cell D → ExtOrd) (r : Cell (small D Q R j k hj hjA hk hkA) → ExtOrd)
    (d : Cell D) : glue D Q R j k hj hjA hk hkA p r (old D Q R j k hj hjA hk hkA d) = p d := by
  simp only [glue, old, cell, Equiv.symm_apply_apply]

theorem glue_embed (p : Cell D → ExtOrd) (r : Cell (small D Q R j k hj hjA hk hkA) → ExtOrd)
    (hag : ∀ c, r (old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA c) =
      p (GradeCutBoundary.toCell D k c)) (d : Cell (small D Q R j k hj hjA hk hkA)) :
    glue D Q R j k hj hjA hk hkA p r (embed D Q R j k hj hjA hk hkA d) = r d := by
  obtain ⟨x, rfl⟩ := (occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA).surjective d
  change glue D Q R j k hj hjA hk hkA p r
    (embed D Q R j k hj hjA hk hkA (cell _ _ _ _ _ _ _ _ _ x)) = _
  rw [embed_cell]
  rcases x with (d | q) | q
  · exact (glue_old D Q R j k hj hjA hk hkA p r _).trans (hag d).symm
  · simp only [Sum.map_inl, Sum.map_inr, id_eq, glue, cell, Equiv.symm_apply_apply]
  · simp only [Sum.map_inr, id_eq, glue, cell, Equiv.symm_apply_apply]

include hmatch in
theorem glue_respects {p : Cell D → ExtOrd} {r : Cell (small D Q R j k hj hjA hk hkA) → ExtOrd}
    (hpr : RespectsSemantics sem p) (hr : RespectsSemantics low r)
    (hag : ∀ c, r (old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA c) =
      p (GradeCutBoundary.toCell D k c)) :
    RespectsSemantics (rows D Q R j k hj hjA hk hkA hp hjk sem low)
      (glue D Q R j k hj hjA hk hkA p r) := by
  apply GradeCutLayerRows.respects_of_lower
  intro c
  obtain ⟨x, rfl⟩ := (occEquiv D Q R j k hj hjA hk hkA).surjective c
  change RespectsSemanticsBelow _
    ((enlarged D Q R j k hj hjA hk hkA).cell (cell D Q R j k hj hjA hk hkA x)) _
  have hlow (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ k) :
      RespectsSemanticsBelow (rows D Q R j k hj hjA hk hkA hp hjk sem low) BJ
        (fun d => glue D Q R j k hj hjA hk hkA p r d.1) := by
    have ht := (lower_respects_iff D Q R j k hj hjA hk hkA hp hjk sem low hmatch BJ hBJ _).mp
      (hr.toBelow BJ)
    convert ht using 1
    funext d
    let e := belowEquiv D Q R j k hj hjA hk hkA BJ hBJ
    exact (congrArg (glue D Q R j k hj hjA hk hkA p r)
      (congrArg Subtype.val (e.apply_symm_apply d))).symm.trans
        (glue_embed D Q R j k hj hjA hk hkA p r hag _)
  rcases x with (a | q) | q
  · have ht := (proper_respects_iff D Q R j k hj hjA hk hkA hp hjk sem low (D.cell a)
      (GradeCutLayerRows.proper_scope D hp a) _).mp (hpr.toBelow (D.cell a))
    have hu := GradeCutLayerRows.cast_respects _ _
      (cell_idx D Q R j k hj hjA hk hkA (.inl (.inl a))).symm ht
    let e := ownerEquiv D Q R j k hj hjA hk hkA hp a
    have heq : (fun d : (enlarged D Q R j k hj hjA hk hkA).below
        ((enlarged D Q R j k hj hjA hk hkA).cell (cell D Q R j k hj hjA hk hkA (.inl (.inl a)))) =>
        glue D Q R j k hj hjA hk hkA p r d.1) =
      (fun d => p (e.symm ⟨d.1, by
        simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩).1) := by
      funext d
      let d' : (enlarged D Q R j k hj hjA hk hkA).below (D.cell a) :=
        ⟨d.1, by simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩
      exact (congrArg (glue D Q R j k hj hjA hk hkA p r)
        (congrArg Subtype.val (e.apply_symm_apply d'))).symm.trans
          (glue_old D Q R j k hj hjA hk hkA p r _)
    exact heq.symm ▸ hu
  · exact hlow _ (by rw [cell_idx]; exact hjk)
  · exact hlow _ (by rw [cell_idx]; exact le_rfl)

end
end VaughtConjecture.Knight.GradeCutPairRows
