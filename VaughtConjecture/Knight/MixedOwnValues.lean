/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RequestFaceIdentification
public import VaughtConjecture.Knight.CountedRecoding

/-! # The own values of the mixed cells over the actual context

The reviewer's assignment (2026-09-15, V-C item 1): construct the mixed cells' own values over
the actual reference context by a finite assignment from same-grade lower-value bounds, keeping
every prescribed context and request label fixed, with visibility and the required inequalities
checked explicitly.

**The assignment.**  On the cell inventory `requestInventory` (old cells of the context, fresh
cells of the request, one cell per remaining graded index containing the fresh point), the
**own value** of a graded index `(B, j)` is the supremum of the labels of the same-grade cells
of both faces whose pushed scope lies in `B` (`ownValue`): the context's grade-`j` cells inside
`B` and the request's grade-`j` cells inside `B`.  The **full labelling** (`fullLabel`) keeps
the context's labels on old cells and the request's labels on fresh cells literally, and gives
each remaining-index cell its own value.

**Checked.**  The own value is self-visible at its grade (`ownValue_selfVis`: a supremum of
labels self-visible at `j`), dominates every same-grade label below it on either face
(`le_ownValue_old`, `le_ownValue_req`), is monotone in the scope (`ownValue_mono`), and is one
of the existing labels or `⊥` (`ownValue_eq_or`) — so the value set is unchanged and no new
codebook is introduced.  The full labelling is orderly (`fullLabel_selfVis`), keeps the
prescribed labels (`fullLabel_castAdd`, `fullLabel_freshCell`), takes only existing values
(`fullLabel_eq_or`), and **satisfies availability on the whole inventory**
(`fullLabel_availability`): a cell of the same grade with a larger scope is dominated at that
index, on either face and at every mixed index, by the own value; the one hypothesis is that no
old cell is visible on the root face (the empty root, `no_old_on_root_of_isEmpty`).

Rows and consistency are `Knight/MixedRows.lean`'s business; bountifulness is not touched.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd
open CellScheme.restrictFace (pushGraded)

private theorem selfVis_max' {K : ℕ} {a b : ExtOrd} (ha : SelfVis K a) (hb : SelfVis K b) :
    SelfVis K (max a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha

section OwnValues

variable {m n : ℕ} {X : CellScheme (ι := Fin m) Finset.univ}
  {Y : CellScheme (ι := Fin (n + 1)) Finset.univ} {e : Fin n ↪ Fin m}
  (labX : Cell X → ExtOrd) (labY : Cell Y → ExtOrd)

/-- The old cells of grade `j` whose pushed scope lies in `B`. -/
noncomputable def oldBelowIndex (B : Finset (Fin (m + 1))) (j : ℕ) : Finset (Cell X) :=
  Finset.univ.filter fun d => X.grade d = j ∧ (X.scope d).image Fin.castSuccEmb ⊆ B

/-- The request cells of grade `j` whose pushed scope lies in `B`. -/
noncomputable def reqBelowIndex (B : Finset (Fin (m + 1))) (j : ℕ) : Finset (Cell Y) :=
  Finset.univ.filter fun c => Y.grade c = j ∧ (Y.scope c).image (onePointProj e) ⊆ B

/-- **The own value of a graded index**: the supremum of the same-grade labels below it on both
faces. -/
noncomputable def ownValue (B : Finset (Fin (m + 1))) (j : ℕ) : ExtOrd :=
  max ((oldBelowIndex (X := X) B j).sup labX) ((reqBelowIndex (Y := Y) (e := e) B j).sup labY)

theorem le_ownValue_old {B : Finset (Fin (m + 1))} {j : ℕ} {d : Cell X} (hd : X.grade d = j)
    (hs : (X.scope d).image Fin.castSuccEmb ⊆ B) :
    labX d ≤ ownValue (Y := Y) (e := e) labX labY B j :=
  (Finset.le_sup (f := labX) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, hs⟩)).trans
    (le_max_left _ _)

theorem le_ownValue_req {B : Finset (Fin (m + 1))} {j : ℕ} {c : Cell Y} (hc : Y.grade c = j)
    (hs : (Y.scope c).image (onePointProj e) ⊆ B) :
    labY c ≤ ownValue (X := X) (e := e) labX labY B j :=
  (Finset.le_sup (f := labY) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hs⟩)).trans
    (le_max_right _ _)

theorem ownValue_mono {B B' : Finset (Fin (m + 1))} (h : B ⊆ B') (j : ℕ) :
    ownValue (X := X) (Y := Y) (e := e) labX labY B j ≤
      ownValue (X := X) (Y := Y) (e := e) labX labY B' j := by
  apply max_le_max
  · apply Finset.sup_mono
    intro d hd
    unfold oldBelowIndex at hd ⊢
    rw [Finset.mem_filter] at hd ⊢
    exact ⟨hd.1, hd.2.1, hd.2.2.trans h⟩
  · apply Finset.sup_mono
    intro c hc
    unfold reqBelowIndex at hc ⊢
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, hc.2.1, hc.2.2.trans h⟩

/-- The own value is self-visible at its grade. -/
theorem ownValue_selfVis (hX : ∀ d, SelfVis (X.grade d) (labX d))
    (hY : ∀ c, SelfVis (Y.grade c) (labY c)) (B : Finset (Fin (m + 1))) (j : ℕ) :
    SelfVis j (ownValue (e := e) labX labY B j) := by
  apply selfVis_max'
  · refine Finset.sup_induction (selfVis_bot j) (fun _ ha _ hb => selfVis_max' ha hb) ?_
    intro d hd
    have := hX d
    rwa [(Finset.mem_filter.mp hd).2.1] at this
  · refine Finset.sup_induction (selfVis_bot j) (fun _ ha _ hb => selfVis_max' ha hb) ?_
    intro c hc
    have := hY c
    rwa [(Finset.mem_filter.mp hc).2.1] at this

/-- The own value is `⊥` or one of the existing labels. -/
theorem ownValue_eq_or (B : Finset (Fin (m + 1))) (j : ℕ) :
    ownValue (e := e) labX labY B j = ⊥ ∨
      (∃ d, ownValue (e := e) labX labY B j = labX d) ∨
      ∃ c, ownValue (e := e) labX labY B j = labY c := by
  unfold ownValue
  have h1 : (oldBelowIndex (X := X) B j).sup labX = ⊥ ∨
      ∃ d, (oldBelowIndex (X := X) B j).sup labX = labX d := by
    rcases (oldBelowIndex (X := X) B j).eq_empty_or_nonempty with h | h
    · exact Or.inl (by rw [h, Finset.sup_empty])
    · obtain ⟨d, -, hd⟩ := Finset.exists_mem_eq_sup _ h labX
      exact Or.inr ⟨d, hd⟩
  have h2 : (reqBelowIndex (Y := Y) (e := e) B j).sup labY = ⊥ ∨
      ∃ c, (reqBelowIndex (Y := Y) (e := e) B j).sup labY = labY c := by
    rcases (reqBelowIndex (Y := Y) (e := e) B j).eq_empty_or_nonempty with h | h
    · exact Or.inl (by rw [h, Finset.sup_empty])
    · obtain ⟨c, -, hc⟩ := Finset.exists_mem_eq_sup _ h labY
      exact Or.inr ⟨c, hc⟩
  rcases max_choice ((oldBelowIndex (X := X) B j).sup labX)
      ((reqBelowIndex (Y := Y) (e := e) B j).sup labY) with h | h <;> rw [h]
  · rcases h1 with h1 | ⟨d, hd⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨d, hd⟩)
  · rcases h2 with h2 | ⟨c, hc⟩
    · exact Or.inl h2
    · exact Or.inr (Or.inr ⟨c, hc⟩)

end OwnValues

/-! ## The full labelling of the inventory -/

section FullLabel

variable {m n : ℕ} {X : CellScheme (ι := Fin m) Finset.univ}
  {Y : CellScheme (ι := Fin (n + 1)) Finset.univ} {e : Fin n ↪ Fin m}
  {Rp : Finset (Finset (Fin (m + 1)))} {hR : Plan.IsPlan Finset.univ Rp}
  {hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
    X.plan.image (Finset.image Fin.castSuccEmb)}
  {hRB : Plan.restrictPlan Rp (Finset.univ.image (onePointProj e)) =
    Y.plan.image (Finset.image (onePointProj e))}
  (labX : Cell X → ExtOrd) (labY : Cell Y → ExtOrd)

/-- **The full labelling**: the context's labels on old cells, the request's on fresh cells,
the own value at each remaining index. -/
noncomputable def fullLabel : Cell (requestInventory X Y e Rp hR hRA hRB) → ExtOrd :=
  Fin.addCases (motive := fun _ => ExtOrd) (fun i => labX i)
    (fun j => match (Fintype.equivFin (FreshReq Y ⊕ OutsideIndex e Rp)).symm j with
      | Sum.inl c => labY c.1
      | Sum.inr b => ownValue (e := e) labX labY b.1.1 b.1.2)

theorem fullLabel_castAdd (i : Cell X) :
    fullLabel (Y := Y) (e := e) (hR := hR) (hRA := hRA) (hRB := hRB) labX labY
      (Fin.castAdd _ i) = labX i :=
  Fin.addCases_left i

theorem fullLabel_freshCell (c : FreshReq Y) :
    fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY (freshCell c) = labY c.1 := by
  unfold fullLabel freshCell
  rw [Fin.addCases_right, Equiv.symm_apply_apply]

theorem fullLabel_outsideCell (b : OutsideIndex e Rp) :
    fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY (outsideCell b) =
      ownValue (e := e) labX labY b.1.1 b.1.2 := by
  unfold fullLabel outsideCell
  rw [Fin.addCases_right, Equiv.symm_apply_apply]

theorem grade_outsideCell (b : OutsideIndex e Rp) :
    (requestInventory X Y e Rp hR hRA hRB).grade (outsideCell b) = b.1.2 :=
  congrArg Prod.snd (cell_outsideCell b)

theorem scope_outsideCell (b : OutsideIndex e Rp) :
    (requestInventory X Y e Rp hR hRA hRB).scope (outsideCell b) = b.1.1 :=
  congrArg Prod.fst (cell_outsideCell b)

theorem grade_freshCell (c : FreshReq Y) :
    (requestInventory X Y e Rp hR hRA hRB).grade (freshCell c) = Y.grade c.1 :=
  congrArg Prod.snd (cell_freshCell c)

theorem scope_freshCell (c : FreshReq Y) :
    (requestInventory X Y e Rp hR hRA hRB).scope (freshCell c) =
      (Y.scope c.1).image (onePointProj e) :=
  congrArg Prod.fst (cell_freshCell c)

/-- The full labelling is orderly. -/
theorem fullLabel_selfVis (hX : ∀ d, SelfVis (X.grade d) (labX d))
    (hY : ∀ c, SelfVis (Y.grade c) (labY c)) (d : Cell (requestInventory X Y e Rp hR hRA hRB)) :
    SelfVis ((requestInventory X Y e Rp hR hRA hRB).grade d)
      (fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY d) := by
  rcases requestInventory_cases d with ⟨i, rfl⟩ | ⟨c, rfl⟩ | ⟨b, rfl⟩
  · rw [fullLabel_castAdd, grade_castAdd]
    exact hX i
  · rw [fullLabel_freshCell, grade_freshCell]
    exact hY c.1
  · rw [fullLabel_outsideCell, grade_outsideCell]
    exact ownValue_selfVis labX labY hX hY _ _

/-- The full labelling takes only the existing labels, or `⊥`. -/
theorem fullLabel_eq_or (d : Cell (requestInventory X Y e Rp hR hRA hRB)) :
    fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY d = ⊥ ∨
      (∃ i, fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY d = labX i) ∨
      ∃ c, fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY d = labY c := by
  rcases requestInventory_cases d with ⟨i, rfl⟩ | ⟨c, rfl⟩ | ⟨b, rfl⟩
  · exact Or.inr (Or.inl ⟨i, fullLabel_castAdd labX labY i⟩)
  · exact Or.inr (Or.inr ⟨c.1, fullLabel_freshCell labX labY c⟩)
  · rw [fullLabel_outsideCell]
    exact ownValue_eq_or labX labY _ _

/-- Over the empty root no old cell is visible on the root face. -/
theorem no_old_on_root_of_isEmpty [IsEmpty (Fin n)] (i : Cell X) :
    ¬ X.scope i ⊆ Finset.univ.image e := by
  intro h
  have hpos := X.grade_le_card_scope i
  have hcard := X.grade_pos i
  have himg : (Finset.univ : Finset (Fin n)).image e = ∅ := by
    rw [Finset.univ_eq_empty, Finset.image_empty]
  have : X.scope i = ∅ := by
    rw [himg] at h
    exact Finset.subset_empty.mp h
  rw [this, Finset.card_empty] at hpos
  omega

/-- **Availability of the full labelling on the whole inventory**: a cell of the same grade
with a larger scope is dominated at its index — on the old face by the context's availability,
on the request face by the request's, and at every remaining index by the own value.  The
hypothesis is that no old cell is visible on the root face. -/
theorem fullLabel_availability
    (hn : ∀ i : Cell X, ¬ X.scope i ⊆ Finset.univ.image e)
    (hX : ∀ Sig Xi₀ : Cell X, X.scope Sig ⊆ X.scope Xi₀ → X.grade Sig = X.grade Xi₀ →
      ∃ Xi, X.cell Xi = X.cell Xi₀ ∧ labX Sig ≤ labX Xi)
    (hY : ∀ Sig Xi₀ : Cell Y, Y.scope Sig ⊆ Y.scope Xi₀ → Y.grade Sig = Y.grade Xi₀ →
      ∃ Xi, Y.cell Xi = Y.cell Xi₀ ∧ labY Sig ≤ labY Xi)
    (Sig Xi₀ : Cell (requestInventory X Y e Rp hR hRA hRB))
    (hs : (requestInventory X Y e Rp hR hRA hRB).scope Sig ⊆
      (requestInventory X Y e Rp hR hRA hRB).scope Xi₀)
    (hg : (requestInventory X Y e Rp hR hRA hRB).grade Sig =
      (requestInventory X Y e Rp hR hRA hRB).grade Xi₀) :
    ∃ Xi, (requestInventory X Y e Rp hR hRA hRB).cell Xi =
        (requestInventory X Y e Rp hR hRA hRB).cell Xi₀ ∧
      fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY Sig ≤
        fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY Xi := by
  rcases requestInventory_cases Xi₀ with ⟨i, rfl⟩ | ⟨c, rfl⟩ | ⟨b, rfl⟩
  · -- the old face
    have hold : (requestInventory X Y e Rp hR hRA hRB).scope Sig ⊆
        Finset.univ.image Fin.castSuccEmb := by
      refine hs.trans ?_
      unfold requestInventory
      rw [extendOneWith_scope_castAdd]
      exact Finset.image_subset_image (Finset.subset_univ _)
    obtain ⟨i', rfl⟩ := (extendOneWith_scope_subset_iff (newIndex_last Y e Rp) Sig).mp hold
    have hs' : X.scope i' ⊆ X.scope i := by
      have := hs
      unfold requestInventory at this
      rw [extendOneWith_scope_castAdd, extendOneWith_scope_castAdd] at this
      exact (Finset.image_subset_image_iff Fin.castSuccEmb.injective).mp this
    have hg' : X.grade i' = X.grade i := by
      rwa [grade_castAdd, grade_castAdd] at hg
    obtain ⟨Xi, hXi, hle⟩ := hX i' i hs' hg'
    refine ⟨Fin.castAdd _ Xi, ?_, ?_⟩
    · unfold requestInventory
      rw [extendOneWith_cell_castAdd, extendOneWith_cell_castAdd, hXi]
    · rw [fullLabel_castAdd, fullLabel_castAdd]
      exact hle
  · -- the request face
    have hreq : (requestInventory X Y e Rp hR hRA hRB).scope Sig ⊆
        Finset.univ.image (onePointProj e) :=
      hs.trans (scope_freshCell_subset c)
    rcases requestInventory_cases Sig with ⟨i', rfl⟩ | ⟨c', rfl⟩ | ⟨b', rfl⟩
    · exact absurd ((scope_castAdd_subset_iff i').mp hreq) (hn i')
    · have hs' : Y.scope c'.1 ⊆ Y.scope c.1 := by
        rw [scope_freshCell, scope_freshCell] at hs
        exact (Finset.image_subset_image_iff (onePointProj e).injective).mp hs
      have hg' : Y.grade c'.1 = Y.grade c.1 := by
        rwa [grade_freshCell, grade_freshCell] at hg
      obtain ⟨Xi, hXi, hle⟩ := hY c'.1 c.1 hs' hg'
      have hlast : Fin.last n ∈ Y.scope Xi := by
        change Fin.last n ∈ (Y.cell Xi).1
        rw [hXi]
        exact c.2
      refine ⟨freshCell ⟨Xi, hlast⟩, ?_, ?_⟩
      · rw [cell_freshCell, cell_freshCell, hXi]
      · rw [fullLabel_freshCell, fullLabel_freshCell]
        exact hle
    · exact absurd hreq (scope_outsideCell_not_subset b')
  · -- a remaining index: dominated by the own value
    refine ⟨outsideCell b, rfl, ?_⟩
    rw [fullLabel_outsideCell]
    rw [scope_outsideCell] at hs
    rw [grade_outsideCell] at hg
    rcases requestInventory_cases Sig with ⟨i', rfl⟩ | ⟨c', rfl⟩ | ⟨b', rfl⟩
    · rw [fullLabel_castAdd]
      rw [grade_castAdd] at hg
      refine le_ownValue_old labX labY hg ?_
      have := hs
      unfold requestInventory at this
      rwa [extendOneWith_scope_castAdd] at this
    · rw [fullLabel_freshCell]
      rw [grade_freshCell] at hg
      rw [scope_freshCell] at hs
      exact le_ownValue_req labX labY hg hs
    · rw [fullLabel_outsideCell]
      rw [grade_outsideCell] at hg
      rw [scope_outsideCell] at hs
      rw [hg]
      exact ownValue_mono labX labY hs _

end FullLabel

end VaughtConjecture.Knight
