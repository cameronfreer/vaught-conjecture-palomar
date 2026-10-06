/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RequestAttachment

/-! # The exact identification of the request face

On the cell inventory `requestInventory` over the common plan
(`Knight/RequestAttachment.lean`), the cells visible on the request face are identified with
**all** the request's cells, not only its fresh ones: a fresh request cell is its embedding
`freshCell`; a root request cell (one not containing the fresh point) is identified through
the **shared root** — the equality of the context's restriction to the root face with the
request's restriction to its initial face — and the context's own cell map `toCell`.

* `reqCell : Cell Y → Cell (requestInventory …)` is injective (`reqCell_injective`: distinct
  request cells sharing a graded index stay distinct — index equality is not cell equality),
  lands in the cells visible on the request face (`scope_reqCell_subset`), and every visible
  cell is hit (`exists_reqCell_eq`).
* **Graded-index transport** (`cell_reqCell`): the inventory's graded index of `reqCell c` is
  the request's, pushed along `onePointProj e`.
* **Lower-domain transport** (`gradedLe_reqCell_iff`, `reqBelowEquiv`): the graded order of
  the request is the graded order of the inventory on the identified cells, and the lower set
  of a request cell corresponds bijectively to the lower set of its image.  Likewise for old
  cells (`oldBelowEquiv`): the lower set of an old cell consists of old cells.
* **The rows prescribed by both faces** (`prescribedRows`): old cells carry the context's rows,
  fresh request cells the request's rows, remaining-index cells a parameter; **literal old-face
  preservation** (`prescribedRows_old`), **request-face preservation up to the explicit
  enumeration** on fresh cells (`prescribedRows_fresh`) and on root cells through the context's
  cells (`prescribedRows_root`) — the request's row there exactly when the two faces' rows agree
  on the shared root, which is `ReferenceContext.shared_root` (rows included) over the actual
  context.
* **The first mixed scope** (section `MixedScope`): a degenerate consistent row (the mute row)
  is available but mutes the cell; the diagonal row is consistent under diagonal respect of the
  lower rows (sufficient, not an equivalence); bountifulness, realization of the prescribed
  pair, and the forced reduced projection remain three separate obligations.

Two distinctions kept throughout.  The request's **rows** are prescribed literally, but its
**labels** are prescribed after reduction: a requested `⊤` is an upstairs value at least `β`,
not a literal upstairs `⊤` (`reduced_label_iff`).  And reference-row correctness remains a
sufficient construction route for readback, not a necessary interface.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme
open CellScheme.restrictFace (toCell pushGraded gradedLe_pushGraded_iff)

/-! ## Cell transport along an equality of schemes -/

section Cast

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

/-- Transport of a cell along an equality of schemes. -/
def CellScheme.castCellEq {D₁ D₂ : CellScheme A} (h : D₁ = D₂) (i : Cell D₁) : Cell D₂ :=
  Fin.cast (congrArg CellScheme.card h) i

theorem CellScheme.cell_castCellEq {D₁ D₂ : CellScheme A} (h : D₁ = D₂) (i : Cell D₁) :
    D₂.cell (castCellEq h i) = D₁.cell i := by
  subst h; rfl

theorem CellScheme.castCellEq_injective {D₁ D₂ : CellScheme A} (h : D₁ = D₂) :
    Function.Injective (castCellEq h) := by
  subst h; exact fun _ _ e => e

theorem CellScheme.castCellEq_symm_castCellEq {D₁ D₂ : CellScheme A} (h : D₁ = D₂)
    (i : Cell D₁) : castCellEq h.symm (castCellEq h i) = i := by
  subst h; rfl

theorem CellScheme.castCellEq_castCellEq_symm {D₁ D₂ : CellScheme A} (h : D₁ = D₂)
    (j : Cell D₂) : castCellEq h (castCellEq h.symm j) = j := by
  subst h; rfl

end Cast

/-! ## The identification -/

section Identification

variable {m n : ℕ} {X : CellScheme (ι := Fin m) Finset.univ}
  {Y : CellScheme (ι := Fin (n + 1)) Finset.univ} {e : Fin n ↪ Fin m}
  {Rp : Finset (Finset (Fin (m + 1)))} {hR : Plan.IsPlan Finset.univ Rp}
  {hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
    X.plan.image (Finset.image Fin.castSuccEmb)}
  {hRB : Plan.restrictPlan Rp (Finset.univ.image (onePointProj e)) =
    Y.plan.image (Finset.image (onePointProj e))}
  (hvX : Finset.univ.image e ∈ X.plan) (hvY : Finset.univ.image Fin.castSuccEmb ∈ Y.plan)
  (hroot : X.restrictFace e hvX = Y.restrictFace Fin.castSuccEmb hvY)

/-- A request cell without the fresh point lies on the request's initial face. -/
theorem scope_subset_castSucc_of_not_last {c : Cell Y} (hc : Fin.last n ∉ Y.scope c) :
    Y.scope c ⊆ Finset.univ.image Fin.castSuccEmb := by
  rw [image_castSuccEmb_univ]
  intro x hx
  exact Finset.mem_erase.mpr ⟨fun e => hc (e ▸ hx), Finset.mem_univ _⟩

/-- The context cell of a root request cell: through the shared root. -/
noncomputable def rootCell (j : Cell (Y.restrictFace Fin.castSuccEmb hvY)) : Cell X :=
  toCell X e hvX (castCellEq hroot.symm j)

theorem rootCell_injective : Function.Injective (rootCell hvX hvY hroot) := fun _ _ h =>
  castCellEq_injective hroot.symm (restrictFace.toCell_injective X e hvX h)

/-- The graded index of the context cell of a root request cell is the request's index of
that cell, pulled to the root and pushed to the context. -/
theorem cell_rootCell (j : Cell (Y.restrictFace Fin.castSuccEmb hvY)) :
    X.cell (rootCell hvX hvY hroot j) =
      pushGraded e (Y.pullCell Fin.castSuccEmb (toCell Y Fin.castSuccEmb hvY j)) := by
  unfold rootCell
  rw [← restrictFace.pushGraded_cell X e hvX, cell_castCellEq]
  rfl

theorem scope_rootCell_subset (j : Cell (Y.restrictFace Fin.castSuccEmb hvY)) :
    X.scope (rootCell hvX hvY hroot j) ⊆ Finset.univ.image e :=
  restrictFace.scope_toCell_subset X e hvX _

/-- **The identification** of all request cells with inventory cells: fresh cells by their
embedding, root cells through the shared root. -/
noncomputable def reqCell (c : Cell Y) : Cell (requestInventory X Y e Rp hR hRA hRB) :=
  if hc : Fin.last n ∈ Y.scope c then freshCell ⟨c, hc⟩
  else Fin.castAdd _ (rootCell hvX hvY hroot (Classical.choose
    (restrictFace.exists_toCell_eq Y Fin.castSuccEmb hvY (scope_subset_castSucc_of_not_last hc))))

theorem reqCell_of_last {c : Cell Y} (hc : Fin.last n ∈ Y.scope c) :
    reqCell hvX hvY hroot (hR := hR) (hRA := hRA) (hRB := hRB) c = freshCell ⟨c, hc⟩ := by
  unfold reqCell; exact dite_eq_left hc

theorem reqCell_of_not_last {c : Cell Y} (hc : Fin.last n ∉ Y.scope c) :
    reqCell hvX hvY hroot (hR := hR) (hRA := hRA) (hRB := hRB) c =
      Fin.castAdd _ (rootCell hvX hvY hroot (Classical.choose
        (restrictFace.exists_toCell_eq Y Fin.castSuccEmb hvY
          (scope_subset_castSucc_of_not_last hc)))) := by
  unfold reqCell; exact dite_eq_right hc

theorem pushGraded_pushGraded {k l p : ℕ} (f : Fin k ↪ Fin l) (g : Fin l ↪ Fin p)
    (Z : Finset (Fin k) × ℕ) : pushGraded g (pushGraded f Z) = pushGraded (f.trans g) Z := by
  unfold pushGraded
  rw [Finset.image_image]
  rfl

/-- **Graded-index transport**: the inventory's index of an identified request cell is the
request's index, pushed. -/
theorem cell_reqCell (c : Cell Y) :
    (requestInventory X Y e Rp hR hRA hRB).cell (reqCell hvX hvY hroot c) =
      pushGraded (onePointProj e) (Y.cell c) := by
  by_cases hc : Fin.last n ∈ Y.scope c
  · rw [reqCell_of_last hvX hvY hroot hc, cell_freshCell]
  · rw [reqCell_of_not_last hvX hvY hroot hc]
    unfold requestInventory
    rw [extendOneWith_cell_castAdd, cell_rootCell, pushGraded_pushGraded,
      Classical.choose_spec (restrictFace.exists_toCell_eq Y Fin.castSuccEmb hvY
        (scope_subset_castSucc_of_not_last hc)), ← castSucc_trans_onePointProj,
      ← pushGraded_pushGraded]
    congr 1
    exact Prod.ext (image_pullCell_fst Y Fin.castSuccEmb (scope_subset_castSucc_of_not_last hc))
      rfl

theorem natAdd_ne_castAdd {k l : ℕ} (j : Fin k) (i : Fin l) :
    Fin.natAdd l j ≠ Fin.castAdd k i :=
  Fin.ne_of_val_ne (by simp [Fin.castAdd, Fin.natAdd]; omega)

theorem reqCell_injective : Function.Injective (reqCell hvX hvY hroot (hR := hR) (hRA := hRA)
    (hRB := hRB)) := by
  intro c c' h
  by_cases hc : Fin.last n ∈ Y.scope c <;> by_cases hc' : Fin.last n ∈ Y.scope c'
  · rw [reqCell_of_last hvX hvY hroot hc, reqCell_of_last hvX hvY hroot hc'] at h
    exact congrArg Subtype.val (freshCell_injective h)
  · rw [reqCell_of_last hvX hvY hroot hc, reqCell_of_not_last hvX hvY hroot hc'] at h
    exact absurd h (by unfold freshCell; exact natAdd_ne_castAdd _ _)
  · rw [reqCell_of_not_last hvX hvY hroot hc, reqCell_of_last hvX hvY hroot hc'] at h
    exact absurd h.symm (by unfold freshCell; exact natAdd_ne_castAdd _ _)
  · rw [reqCell_of_not_last hvX hvY hroot hc, reqCell_of_not_last hvX hvY hroot hc'] at h
    have h1 := rootCell_injective hvX hvY hroot (Fin.castAdd_injective _ _ h)
    have s := Classical.choose_spec (restrictFace.exists_toCell_eq Y Fin.castSuccEmb hvY
      (scope_subset_castSucc_of_not_last hc))
    have s' := Classical.choose_spec (restrictFace.exists_toCell_eq Y Fin.castSuccEmb hvY
      (scope_subset_castSucc_of_not_last hc'))
    rw [← s, ← s', h1]

/-- Identified cells are visible on the request face. -/
theorem scope_reqCell_subset (c : Cell Y) :
    (requestInventory X Y e Rp hR hRA hRB).scope (reqCell hvX hvY hroot c) ⊆
      Finset.univ.image (onePointProj e) := by
  change ((requestInventory X Y e Rp hR hRA hRB).cell (reqCell hvX hvY hroot c)).1 ⊆ _
  rw [cell_reqCell]
  exact Finset.image_subset_image (Finset.subset_univ _)

/-- **Every cell visible on the request face is an identified request cell.** -/
theorem exists_reqCell_eq {d : Cell (requestInventory X Y e Rp hR hRA hRB)}
    (hd : (requestInventory X Y e Rp hR hRA hRB).scope d ⊆ Finset.univ.image (onePointProj e)) :
    ∃ c, reqCell hvX hvY hroot c = d := by
  rcases requestInventory_cases d with ⟨i, rfl⟩ | ⟨c, rfl⟩ | ⟨b, rfl⟩
  · -- an old cell visible on the root face: through the shared root
    have hi : X.scope i ⊆ Finset.univ.image e := (scope_castAdd_subset_iff i).mp hd
    obtain ⟨j', hj'⟩ := restrictFace.exists_toCell_eq X e hvX hi
    set j : Cell (Y.restrictFace Fin.castSuccEmb hvY) := castCellEq hroot j' with hj
    refine ⟨toCell Y Fin.castSuccEmb hvY j, ?_⟩
    have hnl : Fin.last n ∉ Y.scope (toCell Y Fin.castSuccEmb hvY j) := by
      intro h
      have := restrictFace.scope_toCell_subset Y Fin.castSuccEmb hvY j h
      rw [image_castSuccEmb_univ] at this
      exact (Finset.mem_erase.mp this).1 rfl
    rw [reqCell_of_not_last hvX hvY hroot hnl]
    have hch : Classical.choose (restrictFace.exists_toCell_eq Y Fin.castSuccEmb hvY
        (scope_subset_castSucc_of_not_last hnl)) = j :=
      restrictFace.toCell_injective Y Fin.castSuccEmb hvY
        (Classical.choose_spec (restrictFace.exists_toCell_eq Y Fin.castSuccEmb hvY
          (scope_subset_castSucc_of_not_last hnl)))
    rw [hch]
    unfold rootCell
    rw [hj, castCellEq_symm_castCellEq, hj']
  · exact ⟨c.1, by rw [reqCell_of_last hvX hvY hroot c.2]⟩
  · exact absurd hd (scope_outsideCell_not_subset b)

/-! ## Lower-domain transport -/

/-- **The graded order transports** along the identification. -/
theorem gradedLe_reqCell_iff (c c' : Cell Y) :
    GradedLe ((requestInventory X Y e Rp hR hRA hRB).cell (reqCell hvX hvY hroot c'))
        ((requestInventory X Y e Rp hR hRA hRB).cell (reqCell hvX hvY hroot c)) ↔
      GradedLe (Y.cell c') (Y.cell c) := by
  rw [cell_reqCell, cell_reqCell]
  exact gradedLe_pushGraded_iff (onePointProj e)

/-- The lower set of a request cell, transported into the inventory. -/
noncomputable def reqBelow (c : Cell Y) (d : Y.below (Y.cell c)) :
    (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (reqCell hvX hvY hroot c)) :=
  ⟨reqCell hvX hvY hroot d.1, (gradedLe_reqCell_iff hvX hvY hroot c d.1).mpr d.2⟩

theorem reqBelow_bijective (c : Cell Y) :
    Function.Bijective (reqBelow (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot c) := by
  constructor
  · intro d d' h
    exact Subtype.ext (reqCell_injective hvX hvY hroot (congrArg Subtype.val h))
  · intro d
    have hvis : (requestInventory X Y e Rp hR hRA hRB).scope d.1 ⊆
        Finset.univ.image (onePointProj e) :=
      d.2.1.trans (scope_reqCell_subset hvX hvY hroot c)
    obtain ⟨c', hc'⟩ := exists_reqCell_eq hvX hvY hroot hvis
    refine ⟨⟨c', ?_⟩, Subtype.ext hc'⟩
    rw [← gradedLe_reqCell_iff hvX hvY hroot, hc']
    exact d.2

/-- **Lower-domain transport**: the lower set of a request cell corresponds bijectively to the
lower set of its identified cell. -/
noncomputable def reqBelowEquiv (c : Cell Y) :
    Y.below (Y.cell c) ≃ (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (reqCell hvX hvY hroot c)) :=
  Equiv.ofBijective _ (reqBelow_bijective (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot c)

/-- The lower set of an old cell, transported into the inventory. -/
def oldBelow (i : Cell X) (d : X.below (X.cell i)) :
    (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (Fin.castAdd _ i)) :=
  ⟨Fin.castAdd _ d.1, by
    unfold requestInventory
    rw [extendOneWith_cell_castAdd, extendOneWith_cell_castAdd]
    exact (gradedLe_pushGraded_iff Fin.castSuccEmb).mpr d.2⟩

theorem oldBelow_bijective (i : Cell X) :
    Function.Bijective (oldBelow (Y := Y) (e := e) (hR := hR) (hRA := hRA) (hRB := hRB) i) := by
  constructor
  · intro d d' h
    exact Subtype.ext (Fin.castAdd_injective _ _ (congrArg Subtype.val h))
  · intro d
    have hold : (requestInventory X Y e Rp hR hRA hRB).scope d.1 ⊆
        Finset.univ.image Fin.castSuccEmb := by
      refine d.2.1.trans ?_
      unfold requestInventory
      rw [extendOneWith_cell_castAdd]
      exact Finset.image_subset_image (Finset.subset_univ _)
    obtain ⟨i', hi'⟩ := (extendOneWith_scope_subset_iff (newIndex_last Y e Rp) d.1).mp hold
    refine ⟨⟨i', ?_⟩, Subtype.ext hi'⟩
    have := d.2
    rw [← hi'] at this
    unfold requestInventory at this
    rw [extendOneWith_cell_castAdd, extendOneWith_cell_castAdd] at this
    exact (gradedLe_pushGraded_iff Fin.castSuccEmb).mp this

/-- **The lower set of an old cell consists of old cells**, bijectively. -/
noncomputable def oldBelowEquiv (i : Cell X) :
    X.below (X.cell i) ≃ (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (Fin.castAdd _ i)) :=
  Equiv.ofBijective _ (oldBelow_bijective (Y := Y) (e := e) (hR := hR) (hRA := hRA) (hRB := hRB) i)

/-! ## Root request cells, explicitly -/

/-- The context cell of a root request cell (one without the fresh point). -/
noncomputable def rootOf (c : Cell Y) (hc : Fin.last n ∉ Y.scope c) : Cell X :=
  rootCell hvX hvY hroot (Classical.choose (restrictFace.exists_toCell_eq Y Fin.castSuccEmb hvY
    (scope_subset_castSucc_of_not_last hc)))

theorem reqCell_eq_castAdd_rootOf {c : Cell Y} (hc : Fin.last n ∉ Y.scope c) :
    reqCell hvX hvY hroot (hR := hR) (hRA := hRA) (hRB := hRB) c =
      Fin.castAdd _ (rootOf hvX hvY hroot c hc) :=
  reqCell_of_not_last hvX hvY hroot hc

/-- The graded index of the context cell of a root request cell. -/
theorem cell_rootOf {c : Cell Y} (hc : Fin.last n ∉ Y.scope c) :
    X.cell (rootOf hvX hvY hroot c hc) = pushGraded e (Y.pullCell Fin.castSuccEmb c) := by
  unfold rootOf
  rw [cell_rootCell, Classical.choose_spec (restrictFace.exists_toCell_eq Y Fin.castSuccEmb hvY
    (scope_subset_castSucc_of_not_last hc))]

/-- A cell below a root request cell is a root request cell. -/
theorem not_last_of_gradedLe {c c' : Cell Y} (hc : Fin.last n ∉ Y.scope c)
    (h : GradedLe (Y.cell c') (Y.cell c)) : Fin.last n ∉ Y.scope c' := fun hl => hc (h.1 hl)

/-- The graded order of root request cells transports to their context cells. -/
theorem gradedLe_rootOf_iff {c c' : Cell Y} (hc : Fin.last n ∉ Y.scope c)
    (hc' : Fin.last n ∉ Y.scope c') :
    GradedLe (X.cell (rootOf hvX hvY hroot c' hc')) (X.cell (rootOf hvX hvY hroot c hc)) ↔
      GradedLe (Y.cell c') (Y.cell c) := by
  rw [cell_rootOf, cell_rootOf, gradedLe_pushGraded_iff,
    gradedLe_pullCell_iff Y Fin.castSuccEmb (scope_subset_castSucc_of_not_last hc')]

end Identification

/-! ## The rows prescribed by both faces -/

section Rows

variable {m n : ℕ} {X : CellScheme (ι := Fin m) Finset.univ}
  {Y : CellScheme (ι := Fin (n + 1)) Finset.univ} {e : Fin n ↪ Fin m}
  {Rp : Finset (Finset (Fin (m + 1)))} {hR : Plan.IsPlan Finset.univ Rp}
  {hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
    X.plan.image (Finset.image Fin.castSuccEmb)}
  {hRB : Plan.restrictPlan Rp (Finset.univ.image (onePointProj e)) =
    Y.plan.image (Finset.image (onePointProj e))}
  (hvX : Finset.univ.image e ∈ X.plan) (hvY : Finset.univ.image Fin.castSuccEmb ∈ Y.plan)
  (hroot : X.restrictFace e hvX = Y.restrictFace Fin.castSuccEmb hvY)
  (rowsX : Semantics X) (rowsY : Semantics Y)
  (ctrl : ∀ b : OutsideIndex e Rp, (requestInventory X Y e Rp hR hRA hRB).below
    ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)) → ExtOrd)

open Classical in
/-- The row of an old cell, as a total function: the context's row on the old cells below it. -/
noncomputable def oldRowFun (i : Cell X) (d : Cell (requestInventory X Y e Rp hR hRA hRB)) :
    ExtOrd :=
  if hd : ∃ d' : X.below (X.cell i), Fin.castAdd _ d'.1 = d then rowsX.E i (Classical.choose hd)
  else ⊥

open Classical in
/-- The row of a fresh request cell, as a total function: the request's row on the identified
cells below it. -/
noncomputable def freshRowFun (c : FreshReq Y) (d : Cell (requestInventory X Y e Rp hR hRA hRB)) :
    ExtOrd :=
  if hd : ∃ d' : Y.below (Y.cell c.1), reqCell hvX hvY hroot d'.1 = d
  then rowsY.E c.1 (Classical.choose hd) else ⊥

open Classical in
/-- The row of a remaining-index cell, as a total function. -/
noncomputable def outsideRowFun (b : OutsideIndex e Rp)
    (d : Cell (requestInventory X Y e Rp hR hRA hRB)) : ExtOrd :=
  if hd : ∃ d' : (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)), d'.1 = d
  then ctrl b (Classical.choose hd) else ⊥

/-- **The prescribed row function**: by the kind of the cell. -/
noncomputable def prescribedRowFun (Sig : Cell (requestInventory X Y e Rp hR hRA hRB)) :
    Cell (requestInventory X Y e Rp hR hRA hRB) → ExtOrd :=
  Fin.addCases (motive := fun _ => Cell (requestInventory X Y e Rp hR hRA hRB) → ExtOrd)
    (fun i => oldRowFun rowsX i)
    (fun j => match (Fintype.equivFin (FreshReq Y ⊕ OutsideIndex e Rp)).symm j with
      | Sum.inl c => freshRowFun hvX hvY hroot rowsY c
      | Sum.inr b => outsideRowFun ctrl b) Sig

theorem prescribedRowFun_castAdd (i : Cell X) :
    prescribedRowFun hvX hvY hroot rowsX rowsY ctrl (Fin.castAdd _ i) = oldRowFun rowsX i :=
  Fin.addCases_left i

theorem prescribedRowFun_freshCell (c : FreshReq Y) :
    prescribedRowFun hvX hvY hroot rowsX rowsY ctrl (freshCell c) =
      freshRowFun hvX hvY hroot rowsY c := by
  unfold prescribedRowFun freshCell
  rw [Fin.addCases_right, Equiv.symm_apply_apply]

theorem prescribedRowFun_outsideCell (b : OutsideIndex e Rp) :
    prescribedRowFun hvX hvY hroot rowsX rowsY ctrl (outsideCell b) = outsideRowFun ctrl b := by
  unfold prescribedRowFun outsideCell
  rw [Fin.addCases_right, Equiv.symm_apply_apply]

/-- **Literal old-face preservation**, cellwise. -/
theorem oldRowFun_castAdd (i : Cell X) (d' : X.below (X.cell i)) :
    oldRowFun (hR := hR) (hRA := hRA) (hRB := hRB) rowsX i
        (Fin.castAdd (Fintype.card (FreshReq Y ⊕ OutsideIndex e Rp)) d'.1) =
      rowsX.E i d' := by
  unfold oldRowFun
  have hd : ∃ d'' : X.below (X.cell i), Fin.castAdd _ d''.1 =
      Fin.castAdd (Fintype.card (FreshReq Y ⊕ OutsideIndex e Rp)) d'.1 := ⟨d', rfl⟩
  rw [dite_eq_left hd]
  congr 1
  exact Subtype.ext (Fin.castAdd_injective _ _ (Classical.choose_spec hd))

/-- **Request-face preservation on fresh cells**, cellwise along the identification. -/
theorem freshRowFun_reqCell (c : FreshReq Y) (d' : Y.below (Y.cell c.1)) :
    freshRowFun hvX hvY hroot rowsY c
        (reqCell hvX hvY hroot (hR := hR) (hRA := hRA) (hRB := hRB) d'.1) =
      rowsY.E c.1 d' := by
  unfold freshRowFun
  have hd : ∃ d'' : Y.below (Y.cell c.1),
      reqCell hvX hvY hroot (hR := hR) (hRA := hRA) (hRB := hRB) d''.1 =
        reqCell hvX hvY hroot d'.1 := ⟨d', rfl⟩
  rw [dite_eq_left hd]
  congr 1
  exact Subtype.ext (reqCell_injective hvX hvY hroot (Classical.choose_spec hd))

theorem outsideRowFun_apply (b : OutsideIndex e Rp)
    (d' : (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b))) :
    outsideRowFun ctrl b d'.1 = ctrl b d' := by
  unfold outsideRowFun
  have hd : ∃ d'' : (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)), d''.1 = d'.1 := ⟨d', rfl⟩
  rw [dite_eq_left hd]
  congr 1
  exact Subtype.ext (Classical.choose_spec hd)

/-- The grade of an identified request cell is the request's. -/
theorem grade_reqCell (c : Cell Y) :
    (requestInventory X Y e Rp hR hRA hRB).grade (reqCell hvX hvY hroot c) = Y.grade c :=
  congrArg Prod.snd (cell_reqCell hvX hvY hroot c)

/-- **The prescribed rows are orderly** on every lower set, given orderly remaining-index rows. -/
theorem grade_castAdd (i : Cell X) :
    (requestInventory X Y e Rp hR hRA hRB).grade (Fin.castAdd _ i) = X.grade i :=
  congrArg Prod.snd (extendOneWith_cell_castAdd i)

/-- **The prescribed rows are orderly** on every lower set, given orderly remaining-index rows. -/
theorem prescribedRowFun_orderly
    (hctrl : ∀ b, Transform.IsOrderly
      (fun d : (requestInventory X Y e Rp hR hRA hRB).below
        ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)) =>
        (requestInventory X Y e Rp hR hRA hRB).grade d.1) (ctrl b))
    (Sig : Cell (requestInventory X Y e Rp hR hRA hRB)) :
    Transform.IsOrderly
      (fun d : (requestInventory X Y e Rp hR hRA hRB).below
        ((requestInventory X Y e Rp hR hRA hRB).cell Sig) =>
        (requestInventory X Y e Rp hR hRA hRB).grade d.1)
      (fun d => prescribedRowFun hvX hvY hroot rowsX rowsY ctrl Sig d.1) := by
  intro d
  change prescribedRowFun hvX hvY hroot rowsX rowsY ctrl Sig d.1 =
    Value.extVisibilityReplace (prescribedRowFun hvX hvY hroot rowsX rowsY ctrl Sig d.1)
      ((requestInventory X Y e Rp hR hRA hRB).grade d.1)
      ((requestInventory X Y e Rp hR hRA hRB).grade d.1)
  rcases requestInventory_cases Sig with ⟨i, rfl⟩ | ⟨c, rfl⟩ | ⟨b, rfl⟩
  · obtain ⟨d', rfl⟩ :=
      (oldBelow_bijective (Y := Y) (e := e) (hR := hR) (hRA := hRA) (hRB := hRB) i).2 d
    change prescribedRowFun hvX hvY hroot rowsX rowsY ctrl (Fin.castAdd _ i)
        (Fin.castAdd _ d'.1) =
      Value.extVisibilityReplace (prescribedRowFun hvX hvY hroot rowsX rowsY ctrl
        (Fin.castAdd _ i) (Fin.castAdd _ d'.1))
        ((requestInventory X Y e Rp hR hRA hRB).grade (Fin.castAdd _ d'.1))
        ((requestInventory X Y e Rp hR hRA hRB).grade (Fin.castAdd _ d'.1))
    rw [prescribedRowFun_castAdd, oldRowFun_castAdd, grade_castAdd]
    exact rowsX.orderly i d'
  · have hvis : (requestInventory X Y e Rp hR hRA hRB).scope d.1 ⊆
        Finset.univ.image (onePointProj e) := d.2.1.trans (scope_freshCell_subset c)
    obtain ⟨c', hc'⟩ := exists_reqCell_eq hvX hvY hroot hvis
    have hle : GradedLe (Y.cell c') (Y.cell c.1) := by
      have this := d.2
      have e3 : freshCell c = reqCell hvX hvY hroot c.1 :=
        (reqCell_of_last (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot c.2).symm
      rw [← hc', e3] at this
      exact (gradedLe_reqCell_iff hvX hvY hroot c.1 c').mp this
    have hd : d.1 = reqCell hvX hvY hroot (⟨c', hle⟩ : Y.below (Y.cell c.1)).1 := hc'.symm
    have hv := freshRowFun_reqCell (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsY c
      ⟨c', hle⟩
    have hg := grade_reqCell (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot c'
    rw [hd, prescribedRowFun_freshCell]
    erw [hv, hg]
    exact rowsY.orderly c.1 ⟨c', hle⟩
  · rw [prescribedRowFun_outsideCell, outsideRowFun_apply]
    exact hctrl b d

/-- **The rows prescribed by both faces**, with the remaining-index rows as a parameter. -/
noncomputable def prescribedRows
    (hctrl : ∀ b, Transform.IsOrderly
      (fun d : (requestInventory X Y e Rp hR hRA hRB).below
        ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)) =>
        (requestInventory X Y e Rp hR hRA hRB).grade d.1) (ctrl b)) :
    Semantics (requestInventory X Y e Rp hR hRA hRB) where
  E Sig d := prescribedRowFun hvX hvY hroot rowsX rowsY ctrl Sig d.1
  orderly := prescribedRowFun_orderly hvX hvY hroot rowsX rowsY ctrl hctrl

variable {ctrl}
variable (hctrl : ∀ b, Transform.IsOrderly
      (fun d : (requestInventory X Y e Rp hR hRA hRB).below
        ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)) =>
        (requestInventory X Y e Rp hR hRA hRB).grade d.1) (ctrl b))

/-- **Literal old-face preservation**: the row of an old cell at an old cell is the context's. -/
theorem prescribedRows_old (i : Cell X) (d' : X.below (X.cell i)) (h) :
    (prescribedRows hvX hvY hroot rowsX rowsY ctrl hctrl).E (Fin.castAdd _ i)
        ⟨Fin.castAdd _ d'.1, h⟩ =
      rowsX.E i d' := by
  change prescribedRowFun hvX hvY hroot rowsX rowsY ctrl (Fin.castAdd _ i)
    (Fin.castAdd _ d'.1) = _
  rw [prescribedRowFun_castAdd, oldRowFun_castAdd]

/-- **Request-face preservation on fresh cells**: the row of a fresh request cell at an
identified request cell is the request's. -/
theorem prescribedRows_fresh (c : FreshReq Y) (d' : Y.below (Y.cell c.1)) (h) :
    (prescribedRows hvX hvY hroot rowsX rowsY ctrl hctrl).E (freshCell c)
        ⟨reqCell hvX hvY hroot d'.1, h⟩ =
      rowsY.E c.1 d' := by
  change prescribedRowFun hvX hvY hroot rowsX rowsY ctrl (freshCell c)
    (reqCell hvX hvY hroot d'.1) = _
  rw [prescribedRowFun_freshCell, freshRowFun_reqCell]

/-- **Request-face preservation on root cells, up to the shared root**: the row of a root
request cell at an identified root cell is the context's row at the corresponding context
cells; it is the request's row exactly when the two faces' rows agree on the shared root. -/
theorem prescribedRows_root (c : Cell Y) (hc : Fin.last n ∉ Y.scope c) (d' : Y.below (Y.cell c))
    (h) (h') :
    (prescribedRows hvX hvY hroot rowsX rowsY ctrl hctrl).E (reqCell hvX hvY hroot c)
        ⟨reqCell hvX hvY hroot d'.1, h⟩ =
      rowsX.E (rootOf hvX hvY hroot c hc)
        ⟨rootOf hvX hvY hroot d'.1 (not_last_of_gradedLe hc d'.2), h'⟩ := by
  have e1 := reqCell_eq_castAdd_rootOf hvX hvY hroot (hR := hR) (hRA := hRA) (hRB := hRB) hc
  have e2 := reqCell_eq_castAdd_rootOf hvX hvY hroot (hR := hR) (hRA := hRA) (hRB := hRB)
    (not_last_of_gradedLe hc d'.2)
  change prescribedRowFun hvX hvY hroot rowsX rowsY ctrl (reqCell hvX hvY hroot c)
    (reqCell hvX hvY hroot d'.1) = _
  rw [e1, e2, prescribedRowFun_castAdd]
  exact oldRowFun_castAdd rowsX (rootOf hvX hvY hroot c hc)
    ⟨rootOf hvX hvY hroot d'.1 (not_last_of_gradedLe hc d'.2), h'⟩

/-- **The remaining-index rows are the parameter**, literally. -/
theorem prescribedRows_outside (b : OutsideIndex e Rp) (d') :
    (prescribedRows hvX hvY hroot rowsX rowsY ctrl hctrl).E (outsideCell b) d' = ctrl b d' := by
  change prescribedRowFun hvX hvY hroot rowsX rowsY ctrl (outsideCell b) d'.1 = _
  rw [prescribedRowFun_outsideCell, outsideRowFun_apply]

end Rows

/-! ## The first mixed scope: a degenerate consistent row is available; adequacy is separate

At a remaining-index cell `M` (the first mixed scope: its lower set carries old cells with the
context's rows, fresh request cells with the request's rows, and lower remaining-index cells),
two candidate rows are compiled with their witnesses.

* **The mute row** (`⊥` everywhere below `M`) is a **degenerate consistent row**, available
  unconditionally: every row transforms onto constant `⊥` (`TransformsTo.to_bot`, shifter
  constantly `⊥`), availability is trivial (`respects_bot_row`).  It is semantically inadequate:
  every labelling respecting the rows reads `⊥` at `M` (`label_eq_bot_of_bot_row`, the mute
  obstruction of `Knight/Domain.lean` at one cell), and availability then pins lower same-grade
  cells whenever `M` is the only cell at its index.  Useful nonmute rows still require their
  own consistency proofs.
* **The diagonal row** (each lower cell read at its own diagonal, a dominating orderly top at
  `M`) is consistent **under** diagonal respect of the lower rows — a sufficient condition, not
  an equivalence: each lower row transforms onto the capped diagonals of its own lower set, and
  the diagonals are available (`respects_diagonal_row`, with the identity witness at `M`).
  Diagonal respect is a condition on the input rows that coding and consistency do not imply:
  a row reading `⊥` at a lower cell whose own diagonal is not `⊥` cannot transform onto the
  capped diagonals when the capping diagonal is also not `⊥` (a shifter fixes `⊥`, and the cap
  would have to be `⊥` for the target to be); both relevant diagonals must be nonbottom for
  this bottom-source obstruction — a nonbottom lower diagonal alone is not enough.

Three obligations stay separate, as the legal-glue counterexample of the coupled construction
already showed they are: **bountifulness** of the rows (respecting extensions of every
permitted labelling of the two faces), **realization of the prescribed pair**, and the
**forced reduced projection** (reduced projected correctness), to which reference-row
correctness remains a sufficient route.  None of the three is settled by either candidate row;
additional cells at an outside index (several rows at one index) are the room availability
leaves.  The slack-cut pasting theorem (#346) takes two labellings already respecting the rows
on the common lower set and pastes them at a cap self-visible one grade above the scheme, with
availability reduced to an overlap condition on their high controllers; it can simplify the
subsequent paste at slack caps, but it does not produce the first section and it does not
discharge boundary caps. -/

section MixedScope

open Transform Value

/-- Every labelling transforms onto the constant bottom: the shifter constantly `⊥`. -/
theorem TransformsTo.to_bot {E : Type*} {grade : E → ℕ} (p : E → ExtOrd) :
    TransformsTo grade p (fun _ => ⊥) :=
  ⟨fun _ => ⊤, fun _ => ⊥, fun _ _ _ => le_rfl, fun _ => rfl, rfl, monotone_const,
    fun _ _ _ _ _ => (extVisibilityReplace_bot _ _).symm,
    fun _ => (min_eq_left bot_le).symm⟩

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} (sem : Semantics D)

/-- **The mute row at one cell is consistent**, unconditionally. -/
theorem respects_bot_row (M : Cell D) (hM : ∀ d, sem.E M d = ⊥) :
    RespectsSemanticsBelow sem (D.cell M) (sem.E M) where
  orderly d := by rw [hM]; exact (extVisibilityReplace_bot _ _).symm
  locality Sig := by
    have : (fun d => min (sem.E M (CellScheme.below.incl Sig d)) (sem.E M Sig)) =
        fun _ => (⊥ : ExtOrd) := funext fun d => by rw [hM, hM, min_self]
    rw [this]
    exact TransformsTo.to_bot _
  availability Sig Xi₀ _ _ := ⟨Xi₀, rfl, by rw [hM, hM]⟩

/-- **The mute obstruction at one cell**: a labelling respecting rows with a mute row at `M`
reads `⊥` at `M`. -/
theorem label_eq_bot_of_bot_row {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    (h : RespectsSemanticsBelow sem BJ r) (M : D.below BJ) (hM : ∀ d, sem.E M.1 d = ⊥) :
    r M = ⊥ := by
  obtain ⟨g, σ, -, -, hσ, -, -, heq⟩ := h.locality M
  have key := heq ⟨M.1, GradedLe.refl _⟩
  have hincl : CellScheme.below.incl M ⟨M.1, GradedLe.refl _⟩ = M := Subtype.ext rfl
  dsimp only at key
  have hMM : sem.E M.1 ⟨M.1, GradedLe.refl _⟩ = ⊥ := hM _
  rw [hincl, min_self, hMM, hσ] at key
  exact le_bot_iff.mp (key ▸ min_le_left _ _)

/-- The diagonal labelling: what each cell reads at itself. -/
def Semantics.diagonal (d : Cell D) : ExtOrd := sem.E d ⟨d, GradedLe.refl _⟩

/-- **The diagonal row at one cell is consistent under diagonal respect of the lower rows** (a
sufficient condition): if `M`'s row reads every lower cell at its own diagonal, is dominated by
its orderly top, every lower row transforms onto the capped diagonals of its own lower set, and
the diagonals are available below `M`. -/
theorem respects_diagonal_row (M : Cell D)
    (hM : ∀ d : D.below (D.cell M), sem.E M d = sem.diagonal d.1)
    (htop : ∀ d : D.below (D.cell M), sem.E M d ≤ sem.E M ⟨M, GradedLe.refl _⟩)
    (hord : sem.E M ⟨M, GradedLe.refl _⟩ =
      extVisibilityReplace (sem.E M ⟨M, GradedLe.refl _⟩) (D.grade M) (D.grade M))
    (hloc : ∀ Sig : D.below (D.cell M), Sig.1 ≠ M →
      TransformsTo (fun d : D.below (D.cell Sig.1) => D.grade d.1) (sem.E Sig.1)
        (fun d => min (sem.diagonal d.1) (sem.diagonal Sig.1)))
    (havail : ∀ Sig Xi₀ : D.below (D.cell M), Xi₀.1 ≠ M → D.scope Sig.1 ⊆ D.scope Xi₀.1 →
      D.grade Sig.1 = D.grade Xi₀.1 →
      ∃ Xi : D.below (D.cell M), D.cell Xi.1 = D.cell Xi₀.1 ∧
        sem.diagonal Sig.1 ≤ sem.diagonal Xi.1) :
    RespectsSemanticsBelow sem (D.cell M) (sem.E M) where
  orderly d := by
    by_cases hd : d.1 = M
    · have : d = ⟨M, GradedLe.refl _⟩ := Subtype.ext hd
      rw [this]; exact hord
    · rw [hM]
      exact sem.orderly d.1 ⟨d.1, GradedLe.refl _⟩
  locality Sig := by
    have htarget : (fun d => min (sem.E M (CellScheme.below.incl Sig d)) (sem.E M Sig)) =
        fun d : D.below (D.cell Sig.1) => min (sem.diagonal d.1) (sem.diagonal Sig.1) :=
      funext fun d => by rw [hM, hM]; rfl
    rw [htarget]
    by_cases hS : Sig.1 = M
    · -- at `M` itself: the target is the row (the top dominates), the identity witness
      have hrow : (fun d : D.below (D.cell Sig.1) => min (sem.diagonal d.1)
          (sem.diagonal Sig.1)) = sem.E Sig.1 := by
        funext d
        have e : Sig = ⟨M, GradedLe.refl _⟩ := Subtype.ext hS
        subst e
        change min (sem.diagonal d.1) (sem.diagonal M) = sem.E M d
        rw [← hM d]
        exact min_eq_left (htop d)
      rw [hrow]
      exact TransformsTo.refl _
    · exact hloc Sig hS
  availability Sig Xi₀ hsub hgr := by
    by_cases hX : Xi₀.1 = M
    · refine ⟨⟨M, GradedLe.refl _⟩, by rw [hX], htop Sig⟩
    · obtain ⟨Xi, hXi, hle⟩ := havail Sig Xi₀ hX hsub hgr
      exact ⟨Xi, hXi, by rw [hM, hM]; exact hle⟩

end MixedScope

end VaughtConjecture.Knight
