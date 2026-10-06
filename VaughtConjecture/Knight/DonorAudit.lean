/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.DonorInventory

/-! # Auditing the donor classification: fresh requesters, grade one, source-row availability

The reviewer's qualifications (2026-09-15) to the classification of `Knight/DonorInventory.lean`,
formalized before any assembly:

* **Fresh requesters.**  `DonorCovered` checks only nonbottom **old** requesters.  But the fresh
  cell is a nonbottom grade-one requester into **every** grade-one mixed index containing it:
  under any labelling satisfying availability on the inventory, the cell at such an index is
  nonbottom (`fresh_requester_forbids_mute`).  So a grade-one mixed index may never be mute,
  whether or not an old requester exists.
* **No grade-one donor.**  The mixed-donor rule replaces the representative's reading at the
  donor's grade and needs the representative's offset **below** that grade; but a proper
  representative's offset is at least its own grade, hence positive.  So every mixed donor has
  grade at least two (`two_le_grade_of_mixedDonor`): the rule cannot supply a grade-one mixed
  row, and the grade-one indices — which the fresh requester forbids to be mute — need
  **another low-row construction**.
* **Availability in source rows.**  Choosing a lower donor at `(B, j)` that dominates the
  representative's label does not make an upper donor's row read it above every requester into
  that index.  What receiver consistency gives is a witness **of the upper donor's own
  choosing**: some old cell at `(B, j)`, possibly a different one.  Fixing this under one upper
  donor is possible — choose the lower donor with the **maximal reading** under that upper
  donor's row among the cells at `(B, j)` (`exists_reading_maximal`), and then every requester is
  read at most it (`availability_of_reading_maximal`).  What is **not** supplied is one lower
  donor that is reading-maximal under **every** upper donor simultaneously; that is the
  obligation a donor selection must meet, and it is left open here.

Accordingly the earlier claim that the assembly is possible "exactly on covered contexts" is
withdrawn: coverage is one necessary condition among these, not an assembly theorem.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

/-! ## The fresh requester -/

section Fresh

variable {m n : ℕ} {X : CellScheme (ι := Fin m) Finset.univ}
  {Y : CellScheme (ι := Fin (n + 1)) Finset.univ} {e : Fin n ↪ Fin m}
  {Rp : Finset (Finset (Fin (m + 1)))} {hR : Plan.IsPlan Finset.univ Rp}
  {hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
    X.plan.image (Finset.image Fin.castSuccEmb)}
  {hRB : Plan.restrictPlan Rp (Finset.univ.image (onePointProj e)) =
    Y.plan.image (Finset.image (onePointProj e))}

/-- **A nonbottom fresh cell forbids a mute cell at every mixed index of its grade containing
it**: availability lifts it to the unique cell at that index. -/
theorem fresh_requester_forbids_mute
    {q : Cell (requestInventory X Y e Rp hR hRA hRB) → ExtOrd}
    (hav : ∀ Sig Xi₀ : Cell (requestInventory X Y e Rp hR hRA hRB),
      (requestInventory X Y e Rp hR hRA hRB).scope Sig ⊆
        (requestInventory X Y e Rp hR hRA hRB).scope Xi₀ →
      (requestInventory X Y e Rp hR hRA hRB).grade Sig =
        (requestInventory X Y e Rp hR hRA hRB).grade Xi₀ →
      ∃ Xi, (requestInventory X Y e Rp hR hRA hRB).cell Xi =
        (requestInventory X Y e Rp hR hRA hRB).cell Xi₀ ∧ q Sig ≤ q Xi)
    (c : FreshReq Y) (hc : q (freshCell c) ≠ ⊥) (b : OutsideIndex e Rp)
    (hs : (Y.scope c.1).image (onePointProj e) ⊆ b.1.1) (hg : Y.grade c.1 = b.1.2) :
    q (outsideCell b) ≠ ⊥ := by
  obtain ⟨Xi, hXi, hle⟩ := hav (freshCell c) (outsideCell b)
    (by rw [scope_freshCell, scope_outsideCell]; exact hs)
    (by rw [grade_freshCell, grade_outsideCell]; exact hg)
  rw [eq_outsideCell_of_cell_eq hXi] at hle
  exact fun h => hc (le_antisymm (h ▸ hle) bot_le)

end Fresh

namespace ReferenceContext

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} {C : ReferenceContext R t reqs} {i : Fin reqs.length}

/-! ## No grade-one mixed donor -/

/-- **Every mixed donor has grade at least two**: the representative's offset is at least its own
grade (orderliness of a proper label), hence positive, and it must lie below the donor's
grade. -/
theorem two_le_grade_of_mixedDonor (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block)
    (D : C.MixedDonor i) : 2 ≤ C.p₀.scheme.scheme.grade D.cell := by
  have hr := List.getElem_mem i.isLt
  have h1 : C.p₀.scheme.scheme.grade (C.repBase reqs[i.val].block) ≤ C.repOff reqs[i.val].block :=
    C.rep_grade_le hr (hblocks _ hr)
  have h2 := C.p₀.scheme.scheme.grade_pos (C.repBase reqs[i.val].block)
  have h3 := D.rep_off_lt
  omega

/-- The mixed-donor rule supplies no grade-one row. -/
theorem no_grade_one_mixedDonor (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block)
    (D : C.MixedDonor i) : C.p₀.scheme.scheme.grade D.cell ≠ 1 := by
  have := two_le_grade_of_mixedDonor hblocks D
  omega

/-! ## Source-row availability under one upper donor -/

open Classical in
/-- The reading of a cell in the row of `Sig`, extended by `⊥` off the lower set. -/
noncomputable def readAt (Sig d : Cell C.p₀.scheme.scheme) : ExtOrd :=
  if h : GradedLe (C.p₀.scheme.scheme.cell d) (C.p₀.scheme.scheme.cell Sig)
  then C.p₀.scheme.rows.E Sig ⟨d, h⟩ else ⊥

theorem readAt_of_le {Sig d : Cell C.p₀.scheme.scheme}
    (h : GradedLe (C.p₀.scheme.scheme.cell d) (C.p₀.scheme.scheme.cell Sig)) :
    readAt (C := C) Sig d = C.p₀.scheme.rows.E Sig ⟨d, h⟩ := by
  unfold readAt
  rw [dite_eq_left h]

/-- The cells of the context at a graded index. -/
noncomputable def cellsAt (BJ : Finset (Fin C.m) × ℕ) : Finset (Cell C.p₀.scheme.scheme) :=
  Finset.univ.filter fun d => C.p₀.scheme.scheme.cell d = BJ

theorem mem_cellsAt {BJ : Finset (Fin C.m) × ℕ} {d : Cell C.p₀.scheme.scheme} :
    d ∈ cellsAt (C := C) BJ ↔ C.p₀.scheme.scheme.cell d = BJ := by
  unfold cellsAt
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **A reading-maximal cell at an index exists** under any upper donor's row (the cells at an
index are finite; nonempty by completeness when the index is in the graded plan). -/
theorem exists_reading_maximal (Sig : Cell C.p₀.scheme.scheme) {BJ : Finset (Fin C.m) × ℕ}
    (hne : (cellsAt (C := C) BJ).Nonempty) :
    ∃ D' ∈ cellsAt (C := C) BJ, ∀ Xi ∈ cellsAt (C := C) BJ,
      readAt (C := C) Sig Xi ≤ readAt (C := C) Sig D' :=
  Finset.exists_max_image _ (readAt (C := C) Sig) hne

/-- **Availability of the upper row toward a reading-maximal lower donor**: every requester of
the index's grade with scope inside it, below the upper donor, is read at most the
reading-maximal cell at that index — by the receiver's own consistency at the upper donor,
whose witness at the index is then dominated by maximality.  Under one upper donor this is the
source-row availability the mixed row needs; across several upper donors the same lower cell
need not be maximal for each, which is the open obligation. -/
theorem availability_of_reading_maximal (Sig : Cell C.p₀.scheme.scheme)
    {BJ : Finset (Fin C.m) × ℕ} (hBJ : GradedLe BJ (C.p₀.scheme.scheme.cell Sig))
    {D' : Cell C.p₀.scheme.scheme} (hD' : D' ∈ cellsAt (C := C) BJ)
    (hmax : ∀ Xi ∈ cellsAt (C := C) BJ, readAt (C := C) Sig Xi ≤ readAt (C := C) Sig D')
    (d : Cell C.p₀.scheme.scheme)
    (hd : GradedLe (C.p₀.scheme.scheme.cell d) (C.p₀.scheme.scheme.cell Sig))
    (hs : C.p₀.scheme.scheme.scope d ⊆ BJ.1) (hg : C.p₀.scheme.scheme.grade d = BJ.2) :
    readAt (C := C) Sig d ≤ readAt (C := C) Sig D' := by
  have hD'cell := (mem_cellsAt (C := C)).mp hD'
  have hD'le : GradedLe (C.p₀.scheme.scheme.cell D') (C.p₀.scheme.scheme.cell Sig) := by
    rw [hD'cell]; exact hBJ
  obtain ⟨Xi, hXi, hle⟩ := (C.p₀.scheme.consistent Sig).availability ⟨d, hd⟩ ⟨D', hD'le⟩
    (by change C.p₀.scheme.scheme.scope d ⊆ C.p₀.scheme.scheme.scope D'
        rw [show C.p₀.scheme.scheme.scope D' = BJ.1 from congrArg Prod.fst hD'cell]
        exact hs)
    (by change C.p₀.scheme.scheme.grade d = C.p₀.scheme.scheme.grade D'
        rw [show C.p₀.scheme.scheme.grade D' = BJ.2 from congrArg Prod.snd hD'cell]
        exact hg)
  have hXimem : Xi.1 ∈ cellsAt (C := C) BJ := (mem_cellsAt (C := C)).mpr (hXi.trans hD'cell)
  calc readAt (C := C) Sig d = C.p₀.scheme.rows.E Sig ⟨d, hd⟩ := readAt_of_le hd
    _ ≤ C.p₀.scheme.rows.E Sig Xi := hle
    _ = readAt (C := C) Sig Xi.1 := (readAt_of_le Xi.2).symm
    _ ≤ readAt (C := C) Sig D' := hmax Xi.1 hXimem

end ReferenceContext

end VaughtConjecture.Knight
