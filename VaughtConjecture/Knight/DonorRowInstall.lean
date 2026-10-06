/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReferenceOrbitRow
public import VaughtConjecture.Knight.CollisionAtController

/-! # Installing the donor row on the actual request inventory

The reviewer's assignment (2026-09-15): reuse the actual full-controller reference-orbit
construction (`Knight/ReferenceOrbitRow.lean`, ported with attribution) and install its unary
fresh reading on the actual request inventory at the unchanged threshold `N`; prove the exact
old-source, fresh-source, lower-domain and availability equations; identify the selected
section's controller-cap compatibility explicitly; then test bottom-cap sections and
positive-cap lifting; stop at the first concrete failed obligation.

**The donor.**  `C.FullController` (`exists_fullController`) is an actual old cell `F.cell`
of the context at `(univ, N)` dominating the cap, chosen by completeness and availability.
Its lower domain `F.Old` — the old cells of grade `≤ N` — is **literally the old part of the
inventory controller's lower set** (`oldPart`, `oldPart_surjective`: the lower-domain
equation).  The new controller is the remaining-index cell at `(univ, N)` of the inventory
(`controllerIndex`, threshold unchanged).

**The installed row** (`installedRow`): at an old cell the donor's own source, literally
(`installedRow_old`, the old-source equation); at a fresh request cell the donor's orbit source
for the request it answers — the visibility replacement of the donor's reading of the actual
representative (`installedRow_fresh`, the fresh-source equation); at a remaining-index cell of
the lower set, a reading `mixedRead` that this module does **not** construct.

**The selected section** (`selectedSection`): the context's labels capped at the donor's
value on old cells, the requested values at fresh cells, the donor's value at the new
controller.  Its **controller-cap compatibility** is explicit: the donor's value is
self-visible at `N` (`donor_selfVis`), every requested value lies strictly below it
(`request_lt_donor`: cap dominance and the donor's domination of the cap), and the faithful
witness carrying the installed row to the section capped at the donor is **the donor's own
exact witness** — one shifter with the step suppressor `gTop N` and unguarded clause 5
(`installed_transformsTo`, from `FullController.transformsTo`; no composition).  Availability
of the section **among the old cells** is the context's own (`section_old_respects`, from
`target_old_respects`).

**The first concrete obligation, where this stops.**  The lower set of the new controller
also contains the remaining-index cells of grade `≤ N` — the mixed indices `(B ∪ {last}, j)`.
The installed row needs readings there (`mixedRead`), the section needs values there, and
availability of a fresh cell toward every mixed index of its grade must be met by those
values; and each mixed cell needs its own row with restrictions coherent with the installed
row.  None of this is supplied by the donor row (its carrier is `F.Old ⊕ requests`), and the
readings cannot be mute (a mute reading forces the mixed cell to `⊥` under the controller,
contradicting availability from a nonbottom old or fresh cell of its grade).  This is the
reviewer's qualification 3, met here as the stop: **the mixed-cell readings and rows coherent
with the donor row**.  The bottom-cap section tests and the positive-cap lifting test are not
reached.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd
open CellScheme.restrictFace (pushGraded)

namespace ReferenceContext

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} {C : ReferenceContext R t reqs} (F : C.FullController)
  (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block)
  {Y : CellScheme (ι := Fin (n + 1)) Finset.univ}
  {Rp : Finset (Finset (Fin (C.m + 1)))} {hR : Plan.IsPlan Finset.univ Rp}
  {hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
    C.p₀.scheme.scheme.plan.image (Finset.image Fin.castSuccEmb)}
  {hRB : Plan.restrictPlan Rp (Finset.univ.image (onePointProj C.proj)) =
    Y.plan.image (Finset.image (onePointProj C.proj))}
  (hn : ∀ i : Cell C.p₀.scheme.scheme, ¬ C.p₀.scheme.scheme.scope i ⊆ Finset.univ.image C.proj)

local notation "Inv" => requestInventory C.p₀.scheme.scheme Y C.proj Rp hR hRA hRB

/-- The new controller: the remaining-index cell at `(univ, N)`. -/
noncomputable def newController : OutsideIndex C.proj Rp :=
  controllerIndex (hR := hR) C.capBase hn

theorem newController_grade : (newController (hR := hR) hn).1.2 = C.N := C.cap_grade

/-! ## The lower-domain equation -/

/-- An old cell of the donor's lower domain, as a cell of the new controller's lower set. -/
def oldPart (d : F.Old) : (Inv).below ((Inv).cell (outsideCell (newController (hR := hR) hn))) :=
  ⟨Fin.castAdd _ d.1, by
    rw [cell_outsideCell]
    refine ⟨Finset.subset_univ _, ?_⟩
    change (Inv).grade (Fin.castAdd _ d.1) ≤ C.p₀.scheme.scheme.grade C.capBase
    rw [grade_castAdd, C.cap_grade]
    exact F.grade_le d⟩

theorem oldPart_val (d : F.Old) :
    (oldPart (hR := hR) (hRA := hRA) (hRB := hRB) F hn d).1 = Fin.castAdd _ d.1 := rfl

/-- **The lower-domain equation**: every old cell of the new controller's lower set is an old
cell of the donor's lower domain. -/
theorem oldPart_surjective
    (x : (Inv).below ((Inv).cell (outsideCell (newController (hR := hR) hn))))
    (i : Cell C.p₀.scheme.scheme) (hx : x.1 = Fin.castAdd _ i) :
    ∃ d : F.Old, oldPart (hR := hR) (hRA := hRA) (hRB := hRB) F hn d = x := by
  have hg : C.p₀.scheme.scheme.grade i ≤ C.N := by
    have h := x.2.2
    rw [hx, cell_outsideCell] at h
    change (Inv).grade (Fin.castAdd _ i) ≤ C.p₀.scheme.scheme.grade C.capBase at h
    rwa [grade_castAdd, C.cap_grade] at h
  refine ⟨⟨i, ?_⟩, Subtype.ext hx.symm⟩
  rw [F.index]
  exact ⟨Finset.subset_univ _, hg⟩

/-- A fresh request cell of grade `≤ N`, as a cell of the new controller's lower set. -/
noncomputable def freshPart (c : FreshReq Y) (hc : Y.grade c.1 ≤ C.N) :
    (Inv).below ((Inv).cell (outsideCell (newController (hR := hR) hn))) :=
  ⟨freshCell c, by
    rw [cell_outsideCell]
    refine ⟨Finset.subset_univ _, ?_⟩
    change (Inv).grade (freshCell c) ≤ C.p₀.scheme.scheme.grade C.capBase
    rw [grade_freshCell, C.cap_grade]
    exact hc⟩

/-! ## The installed row -/

open Classical in
/-- **The donor row installed on the new controller's lower set**: the donor's source at old
cells, its orbit source at fresh cells (for the request each answers), and a reading
`mixedRead` at the remaining-index cells — the latter not constructed here. -/
noncomputable def installedRow (readFresh : FreshReq Y → Fin reqs.length)
    (mixedRead : OutsideIndex C.proj Rp → ExtOrd)
    (x : (Inv).below ((Inv).cell (outsideCell (newController (hR := hR) hn)))) : ExtOrd :=
  Fin.addCases (motive := fun _ => ExtOrd)
    (fun i => if h : C.p₀.scheme.scheme.grade i ≤ C.N then
      F.source hblocks (Sum.inl ⟨i, by
        rw [F.index]; exact ⟨Finset.subset_univ _, h⟩⟩) else ⊥)
    (fun j => match (Fintype.equivFin (FreshReq Y ⊕ OutsideIndex C.proj Rp)).symm j with
      | Sum.inl c => F.orbitSource hblocks (readFresh c)
      | Sum.inr b => mixedRead b) x.1

/-- **The old-source equation**: the installed row reads every old cell as the donor does. -/
theorem installedRow_old (readFresh : FreshReq Y → Fin reqs.length)
    (mixedRead : OutsideIndex C.proj Rp → ExtOrd) (d : F.Old) :
    installedRow (hR := hR) (hRA := hRA) (hRB := hRB) F hblocks hn readFresh mixedRead
      (oldPart (hR := hR) (hRA := hRA) (hRB := hRB) F hn d) =
      C.p₀.scheme.rows.E F.cell d := by
  unfold installedRow
  rw [oldPart_val, Fin.addCases_left, dite_eq_left (F.grade_le d)]
  rfl

/-- **The fresh-source equation**: the installed row reads a fresh cell as the donor's orbit
source for the request it answers — the visibility replacement, at `N` and the requested
offset, of the donor's reading of the actual representative. -/
theorem installedRow_fresh (readFresh : FreshReq Y → Fin reqs.length)
    (mixedRead : OutsideIndex C.proj Rp → ExtOrd) (c : FreshReq Y) (hc : Y.grade c.1 ≤ C.N) :
    installedRow (hR := hR) (hRA := hRA) (hRB := hRB) F hblocks hn readFresh mixedRead
      (freshPart (hR := hR) (hRA := hRA) (hRB := hRB) hn c hc) =
      extVisibilityReplace (C.p₀.scheme.rows.E F.cell (F.reference hblocks (readFresh c))) C.N
        reqs[(readFresh c).val].offset := by
  unfold installedRow freshPart freshCell
  rw [Fin.addCases_right, Equiv.symm_apply_apply]
  rfl

/-! ## The selected section and its controller-cap compatibility -/

/-- **The selected section** on the donor's carrier: old labels capped at the donor, requested
values at fresh cells (`FullController.target`). -/
noncomputable def selectedSection : F.Old ⊕ Fin reqs.length → ExtOrd := F.target

/-- The donor's value is self-visible at `N`: the cap of the section. -/
theorem donor_selfVis : SelfVis C.N (C.p₀.label F.cell) := by
  have h := (C.p₀.respects.orderly F.cell).symm
  rwa [F.grade_eq] at h

/-- Every requested value lies strictly below the donor's value: cap dominance and the donor's
domination of the cap. -/
theorem request_lt_donor (i : Fin reqs.length) :
    ofOrd reqs[i.val].value < C.p₀.label F.cell :=
  (C.cap_dom _ (List.getElem_mem i.isLt)).trans_le F.dominates

/-- The section at the donor's owner is the donor's value: the cap is literal there. -/
theorem selectedSection_owner : selectedSection F (Sum.inl F.owner) = C.p₀.label F.cell := by
  change min (C.p₀.label F.cell) (C.p₀.label F.cell) = _
  exact min_self _

/-- **The faithful witness at the controller cap**: the donor's own exact witness carries the
installed row (old sources and fresh orbit sources) to the selected section — with the step
suppressor `gTop N` and unguarded clause 5, no composition (`FullController.transformsTo`). -/
theorem installed_transformsTo (readFresh : FreshReq Y → Fin reqs.length)
    (mixedRead : OutsideIndex C.proj Rp → ExtOrd) (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ C.N) (hfr : ∀ c, Y.grade c.1 ≤ C.N) :
    TransformsTo
      (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) (fun c => newGrade (readFresh c)))
      (Sum.elim
        (fun d => installedRow (hR := hR) (hRA := hRA) (hRB := hRB) F hblocks hn readFresh mixedRead
          (oldPart (hR := hR) (hRA := hRA) (hRB := hRB) F hn d))
        (fun c : FreshReq Y => installedRow (hR := hR) (hRA := hRA) (hRB := hRB) F hblocks hn
          readFresh mixedRead (freshPart (hR := hR) (hRA := hRA) (hRB := hRB) hn c (hfr c))))
      (Sum.elim (fun d => selectedSection F (Sum.inl d))
        (fun c => selectedSection F (Sum.inr (readFresh c)))) := by
  have key := (F.transformsTo hblocks newGrade hgrade).reindex (Sum.map id readFresh)
  refine transformsTo_congr ?_ ?_ ?_ key
  · funext x
    rcases x with d | c <;> rfl
  · funext x
    rcases x with d | c
    · exact (installedRow_old (hR := hR) (hRA := hRA) (hRB := hRB) F hblocks hn readFresh
        mixedRead d).symm
    · exact (installedRow_fresh (hR := hR) (hRA := hRA) (hRB := hRB) F hblocks hn readFresh
        mixedRead c (hfr c)).symm
  · funext x
    rcases x with d | c <;> rfl

/-- **Availability among the old cells** of the selected section: the context's own, capped
(`FullController.target_old_respects`). -/
theorem section_old_respects :
    RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell F.cell)
      (fun d => selectedSection F (Sum.inl d)) :=
  F.target_old_respects

end ReferenceContext

end VaughtConjecture.Knight
