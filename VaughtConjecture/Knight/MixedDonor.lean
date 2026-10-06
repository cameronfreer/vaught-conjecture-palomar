/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.DonorRowInstall

/-! # Donor admissibility at a mixed index, and one coherent mixed incidence

The reviewer's tasks (2026-09-15): (1) grade the fresh cell by its actual grade and keep the
receiver's old labels literal in the whole labelling, the capped versions being the
controller's transformation target only; (2) classify where a smaller donor actually exists
at a mixed index, separating the top-grade case, the representative's membership in the
donor's lower domain, and the availability requirement; (3) construct one admissible mixed
incidence completely, with old-source transport, the fresh-source equation and locality at
the actual cap, checking clause 5 when the donor's grade is below `N`.

**(1) Actual grades, literal labels** (`installed_transformsTo_actual`): the donor's own exact
witness carries the installed row to the **literal** whole labelling — the receiver's labels on
old cells, the requested values on fresh cells — capped at the donor's value, with every fresh
cell graded by its actual grade `Y.grade c`.  The capped labels are the target of locality at
the controller; the labelling itself is literal.

**(2) Classification at a mixed index `(B ∪ {fresh}, j)`.**
* *Top grade.*  When `j` is the size of the whole index scope, every same-grade cell of the
  inventory with scope inside it is the index's own cell (`top_grade_only_self`): there is no
  same-grade requester, so availability toward it is satisfied by the cell itself and a mute
  reading is not excluded by availability.  In particular no old cell can serve as donor
  (`grade_le_card_of_scope_subset`: an old cell inside `B` has grade at most `|B| < j`).
* *A donor exists* at `(B, j)` exactly when `(B, j)` is a graded pair of the context's plan,
  by completeness (`exists_donor`).
* *The representative* enters the replacement formula only when it lies in the donor's lower
  domain, i.e. its scope is inside `B` and its grade at most `j` (`rep_below_iff`, the graded
  order unfolded), and the replacement reads it at the donor's grade only when its offset is
  below that grade (the hypothesis `rep_off_lt` of `MixedDonor`).

**(3) One coherent mixed incidence** (`MixedDonor`, data satisfying the classification
conditions: a donor cell with the representative below it, the representative's offset below
the donor's grade, the requested offset at most it, and the representative's label at most
the donor's).  Its row (`mixedSource`) reads every cell of the donor's lower domain as the
donor does (`mixedSource_old`, old-source transport) and reads the fresh cell as the
visibility replacement **at the donor's grade** of the donor's reading of the representative
(`mixedSource_fresh`, the fresh-source equation).  The donor's exact witness — suppressor
`gTop (grade donor)`, clause 5 unguarded up to the donor's grade — reads the fresh source back
as the requested value (`fresh_readback`: clause 5 at threshold the donor's grade, which is
exactly why the replacement is taken there and not at `N`), and carries the row to the
literal labelling capped at the donor (`mixed_transformsTo`, locality at the actual cap), the
requested value lying at or below the donor's value (`request_le_donor`).

Not here: coherence between the incidences chosen at different mixed indices, the mixed
cells' readings in the full controller's row, and any bountifulness test.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

namespace ReferenceContext

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} {C : ReferenceContext R t reqs} (F : C.FullController)
  (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block)

/-! ## (1) Actual grades and literal labels -/

section Actual

variable {Y : CellScheme (ι := Fin (n + 1)) Finset.univ}
  {Rp : Finset (Finset (Fin (C.m + 1)))} {hR : Plan.IsPlan Finset.univ Rp}
  {hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
    C.p₀.scheme.scheme.plan.image (Finset.image Fin.castSuccEmb)}
  {hRB : Plan.restrictPlan Rp (Finset.univ.image (onePointProj C.proj)) =
    Y.plan.image (Finset.image (onePointProj C.proj))}
  (hn : ∀ i : Cell C.p₀.scheme.scheme, ¬ C.p₀.scheme.scheme.scope i ⊆ Finset.univ.image C.proj)

/-- **The literal whole labelling** on the donor's carrier: the receiver's labels on old cells,
the requested values on fresh cells. -/
noncomputable def wholeLabel (readFresh : FreshReq Y → Fin reqs.length) :
    F.Old ⊕ FreshReq Y → ExtOrd :=
  Sum.elim (fun d => C.p₀.label d.1) (fun c => ofOrd reqs[(readFresh c).val].value)

/-- **Locality at the controller with actual grades and literal labels**: the donor's own exact
witness carries the installed row to the literal whole labelling capped at the donor's value,
each fresh cell graded by its actual grade. -/
theorem installed_transformsTo_actual (readFresh : FreshReq Y → Fin reqs.length)
    (mixedRead : OutsideIndex C.proj Rp → ExtOrd) (hfr : ∀ c : FreshReq Y, Y.grade c.1 ≤ C.N) :
    TransformsTo (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1)
        (fun c : FreshReq Y => Y.grade c.1))
      (Sum.elim
        (fun d => installedRow (hR := hR) (hRA := hRA) (hRB := hRB) F hblocks hn readFresh mixedRead
          (oldPart (hR := hR) (hRA := hRA) (hRB := hRB) F hn d))
        (fun c : FreshReq Y => installedRow (hR := hR) (hRA := hRA) (hRB := hRB) F hblocks hn
          readFresh mixedRead (freshPart (hR := hR) (hRA := hRA) (hRB := hRB) hn c (hfr c))))
      (fun x => min (wholeLabel F readFresh x) (C.p₀.label F.cell)) := by
  obtain ⟨τ, hτ, -, hread⟩ := F.exists_exact_witness
  apply hτ.transformsTo
  intro x
  rcases x with d | c
  · change min (C.p₀.label d.1) (C.p₀.label F.cell) =
      min (τ (installedRow (hR := hR) (hRA := hRA) (hRB := hRB) F hblocks hn readFresh mixedRead
        (oldPart (hR := hR) (hRA := hRA) (hRB := hRB) F hn d)))
        (gTop C.N (C.p₀.scheme.scheme.grade d.1))
    rw [installedRow_old, gTop_of_le (F.grade_le d), min_top_right, hread]
  · change min (ofOrd reqs[(readFresh c).val].value) (C.p₀.label F.cell) =
      min (τ (installedRow (hR := hR) (hRA := hRA) (hRB := hRB) F hblocks hn readFresh mixedRead
        (freshPart (hR := hR) (hRA := hRA) (hRB := hRB) hn c (hfr c)))) (gTop C.N (Y.grade c.1))
    rw [installedRow_fresh, gTop_of_le (hfr c), min_top_right,
      min_eq_left (request_lt_donor F (readFresh c)).le]
    exact (F.orbit_readback hblocks hτ hread (readFresh c)).symm

/-! ## (2) Classification at a mixed index -/

/-- **Top grade: no same-grade requester.**  At a remaining index whose grade is the size of
its scope, every cell of the inventory of that grade with scope inside it is the index's own
cell. -/
theorem top_grade_only_self (b : OutsideIndex C.proj Rp) (htop : b.1.2 = b.1.1.card)
    (Sig : Cell (requestInventory C.p₀.scheme.scheme Y C.proj Rp hR hRA hRB))
    (hs : (requestInventory C.p₀.scheme.scheme Y C.proj Rp hR hRA hRB).scope Sig ⊆ b.1.1)
    (hg : (requestInventory C.p₀.scheme.scheme Y C.proj Rp hR hRA hRB).grade Sig = b.1.2) :
    Sig = outsideCell b := by
  apply eq_outsideCell_of_cell_eq
  rw [cell_outsideCell]
  refine Prod.ext ?_ hg
  change (requestInventory C.p₀.scheme.scheme Y C.proj Rp hR hRA hRB).scope Sig = b.1.1
  refine Finset.eq_of_subset_of_card_le hs ?_
  rw [← htop, ← hg]
  exact (requestInventory C.p₀.scheme.scheme Y C.proj Rp hR hRA hRB).grade_le_card_scope Sig

end Actual

/-- An old cell inside a face has grade at most the face's size: no old donor at a top-grade
index. -/
theorem grade_le_card_of_scope_subset (o : Cell C.p₀.scheme.scheme) {B : Finset (Fin C.m)}
    (h : C.p₀.scheme.scheme.scope o ⊆ B) : C.p₀.scheme.scheme.grade o ≤ B.card :=
  (C.p₀.scheme.scheme.grade_le_card_scope o).trans (Finset.card_le_card h)

/-- **A donor exists** at `(B, j)` exactly when it is a graded pair of the context's plan
(completeness). -/
theorem exists_donor {B : Finset (Fin C.m)} {j : ℕ}
    (h : (B, j) ∈ Plan.gradedPlan C.p₀.scheme.scheme.plan) :
    ∃ o : Cell C.p₀.scheme.scheme, C.p₀.scheme.scheme.cell o = (B, j) :=
  C.p₀.scheme.complete _ h

/-- **The representative lies in the donor's lower domain** iff its scope is inside the donor's
and its grade at most the donor's. -/
theorem rep_below_iff (o : Cell C.p₀.scheme.scheme) (μ : Ordinal.{0}) :
    GradedLe (C.p₀.scheme.scheme.cell (C.repBase μ)) (C.p₀.scheme.scheme.cell o) ↔
      C.p₀.scheme.scheme.scope (C.repBase μ) ⊆ C.p₀.scheme.scheme.scope o ∧
        C.p₀.scheme.scheme.grade (C.repBase μ) ≤ C.p₀.scheme.scheme.grade o :=
  Iff.rfl

/-! ## (3) One coherent mixed incidence -/

variable (C) in
/-- **A mixed donor for request `i`**: an old cell with the representative in its lower domain,
the representative's offset below the donor's grade, the requested offset at most it, and the
representative's label at most the donor's. -/
structure MixedDonor (i : Fin reqs.length) where
  /-- The donor cell. -/
  cell : Cell C.p₀.scheme.scheme
  /-- The representative lies in the donor's lower domain. -/
  rep_le : GradedLe (C.p₀.scheme.scheme.cell (C.repBase reqs[i.val].block))
    (C.p₀.scheme.scheme.cell cell)
  /-- The representative's offset is below the donor's grade. -/
  rep_off_lt : C.repOff reqs[i.val].block < C.p₀.scheme.scheme.grade cell
  /-- The requested offset is at most the donor's grade. -/
  offset_le : reqs[i.val].offset ≤ C.p₀.scheme.scheme.grade cell
  /-- The representative's label is at most the donor's. -/
  rep_le_label : C.p₀.label (C.repBase reqs[i.val].block) ≤ C.p₀.label cell

namespace MixedDonor

variable {i : Fin reqs.length} (D : C.MixedDonor i)

/-- The donor's lower domain. -/
abbrev Old := C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell D.cell)

/-- The donor itself in its lower domain. -/
def owner : D.Old := ⟨D.cell, GradedLe.refl _⟩

/-- The representative in the donor's lower domain. -/
def rep : D.Old := ⟨C.repBase reqs[i.val].block, D.rep_le⟩

/-- **The mixed row**: the donor's source at its lower domain, and at the fresh cell the
visibility replacement at the donor's grade of the donor's reading of the representative. -/
noncomputable def mixedSource : D.Old ⊕ Unit → ExtOrd :=
  Sum.elim (C.p₀.scheme.rows.E D.cell)
    (fun _ => extVisibilityReplace (C.p₀.scheme.rows.E D.cell D.rep)
      (C.p₀.scheme.scheme.grade D.cell) reqs[i.val].offset)

/-- The literal labelling: the receiver's labels and the requested value. -/
noncomputable def whole : D.Old ⊕ Unit → ExtOrd :=
  Sum.elim (fun d => C.p₀.label d.1) (fun _ => ofOrd reqs[i.val].value)

/-- **Old-source transport**: the mixed row reads the donor's lower domain as the donor. -/
theorem mixedSource_old (d : D.Old) : D.mixedSource (Sum.inl d) = C.p₀.scheme.rows.E D.cell d :=
  rfl

/-- **The fresh-source equation** at the donor's grade. -/
theorem mixedSource_fresh :
    D.mixedSource (Sum.inr ()) = extVisibilityReplace (C.p₀.scheme.rows.E D.cell D.rep)
      (C.p₀.scheme.scheme.grade D.cell) reqs[i.val].offset :=
  rfl

/-- The donor's exact witness on its own lower domain. -/
theorem exists_exact_witness :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop (C.p₀.scheme.scheme.grade D.cell)) τ ∧
      (∀ x, τ x ≤ C.p₀.label D.cell) ∧
      (∀ d : D.Old, τ (C.p₀.scheme.rows.E D.cell d) =
        min (C.p₀.label d.1) (C.p₀.label D.cell)) :=
  exists_bounded_exact_capped_witness (c := D.owner) (p := fun d : D.Old => C.p₀.label d.1)
    (fun d => d.2.2) (C.p₀.respects.orderly D.cell).symm (C.p₀.respects.locality D.cell)

include hblocks in
/-- **Fresh readback at the donor's grade**: the donor's witness reads the fresh source as the
requested value.  Clause 5 is applied at threshold the donor's grade, where the suppressor is
`⊤`; at a threshold above the donor's grade it would be unavailable. -/
theorem fresh_readback {τ : ExtOrd → ExtOrd}
    (hτ : Witness (gTop (C.p₀.scheme.scheme.grade D.cell)) τ)
    (hread : ∀ d : D.Old, τ (C.p₀.scheme.rows.E D.cell d) =
      min (C.p₀.label d.1) (C.p₀.label D.cell)) :
    τ (D.mixedSource (Sum.inr ())) = ofOrd reqs[i.val].value := by
  have hr := List.getElem_mem i.isLt
  rw [mixedSource_fresh, hτ.clause5 _ (C.p₀.scheme.scheme.grade D.cell)
    (by rw [gTop_of_le le_rfl]; exact le_top) _ D.offset_le, hread]
  change extVisibilityReplace (min (C.p₀.label (C.repBase reqs[i.val].block)) (C.p₀.label D.cell))
    (C.p₀.scheme.scheme.grade D.cell) reqs[i.val].offset = _
  rw [min_eq_left D.rep_le_label, C.rep_label _ hr]
  exact extVisibilityReplace_rep (hblocks _ hr) D.rep_off_lt

include hblocks in
/-- The requested value lies at or below the donor's label: the donor is at least the
representative, so at least its block, and is self-visible at its grade, which is at least the
requested offset. -/
theorem request_le_donor : ofOrd reqs[i.val].value ≤ C.p₀.label D.cell := by
  have hr := List.getElem_mem i.isLt
  have hrep := D.rep_le_label
  rw [C.rep_label _ hr] at hrep
  have hvis := (C.p₀.respects.orderly D.cell).symm
  rcases ExtOrd.cases (C.p₀.label D.cell) with h | h | ⟨L, h⟩
  · rw [h] at hrep; exact absurd hrep (not_ofOrd_le_bot _)
  · rw [h]; exact le_top
  · rw [h] at hrep hvis ⊢
    rw [ofOrd_le_ofOrd] at hrep ⊢
    have hfp : C.p₀.scheme.scheme.grade D.cell ≤ finitePart L := selfVis_ofOrd_iff.mp hvis
    have hlp : reqs[i.val].block ≤ limitPart L := by
      have key : limitPart (reqs[i.val].block + (C.repOff reqs[i.val].block : Ordinal)) =
          reqs[i.val].block := by
        have h := limitPart_limitPart_add_nat reqs[i.val].block (C.repOff reqs[i.val].block)
        rwa [hblocks _ hr] at h
      have := limitPart_mono hrep
      rwa [key] at this
    calc reqs[i.val].value = reqs[i.val].block + (reqs[i.val].offset : Ordinal) := rfl
      _ ≤ limitPart L + (reqs[i.val].offset : Ordinal) := add_le_add_left hlp _
      _ ≤ limitPart L + (finitePart L : Ordinal) :=
          add_le_add_right (Nat.cast_le.mpr (D.offset_le.trans hfp)) _
      _ = L := decomposition L

include hblocks in
/-- **Locality at the actual cap**: the donor's own witness carries the mixed row to the
literal labelling capped at the donor's value, the fresh cell graded by any grade at most the
donor's. -/
theorem mixed_transformsTo (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell) :
    TransformsTo (Sum.elim (fun d : D.Old => C.p₀.scheme.scheme.grade d.1) (fun _ => g₀))
      D.mixedSource (fun x => min (D.whole x) (C.p₀.label D.cell)) := by
  obtain ⟨τ, hτ, -, hread⟩ := D.exists_exact_witness
  apply hτ.transformsTo
  intro x
  rcases x with d | u
  · change min (C.p₀.label d.1) (C.p₀.label D.cell) =
      min (τ (D.mixedSource (Sum.inl d))) (gTop (C.p₀.scheme.scheme.grade D.cell)
        (C.p₀.scheme.scheme.grade d.1))
    rw [mixedSource_old, gTop_of_le (show C.p₀.scheme.scheme.grade d.1 ≤
      C.p₀.scheme.scheme.grade D.cell from d.2.2), min_top_right, hread]
  · change min (ofOrd reqs[i.val].value) (C.p₀.label D.cell) =
      min (τ (D.mixedSource (Sum.inr ()))) (gTop (C.p₀.scheme.scheme.grade D.cell) g₀)
    rw [gTop_of_le hg₀, min_top_right, D.fresh_readback hblocks hτ hread,
      min_eq_left (D.request_le_donor hblocks)]

end MixedDonor

end ReferenceContext

end VaughtConjecture.Knight
