/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReducedProjectionRequest
public import VaughtConjecture.AmalgamationPlan.PlanAttachment
public import VaughtConjecture.Knight.ExtendOneWith

/-! # The common plan of the actual context and one requested one-point extension

`IsPlan.attach_one_over_face` (`AmalgamationPlan/PlanAttachment.lean`) attaches a prescribed
one-point plan over a visible face of a plan, retaining both plans literally.  This module
instantiates it on the actual model-produced reference context `C` and a requested reduced
one-point type `P` over the root:

* the **context plan** is embedded on the old coordinates (`Fin.castSuccEmb`);
* the **request plan** is embedded on the root coordinates plus the fresh point
  (`onePointProj C.proj`), its domain being the root face plus `last`
  (`univ_image_onePointProj`);
* their **agreement on the shared root face** is derived from the request's root compatibility
  (`typeMap castSucc P = some (reduce p)`) and the context's exact consistency
  (`typeMap C.proj C.p₀ = some p`): both restrict to the root's own plan, pushed
  (`plan_of_typeMap_eq_some`, `restrictPlan_image`);
* the result (`exists_common_plan`) is a support plan on all `C.m + 1` points in which the old
  face and the request face are visible and carry the context's and the request's plans
  **exactly** (`restrictPlan` equalities); in the form the explicit one-point extension of cell
  schemes consumes, `common_plan_hface`.

The pivot lemma (`exists_pivot_outside_root`) remains a necessary-condition check on any such
plan; it is not a hypothesis here — the attachment theorem supplies the geometry from the two
plans and their agreement.  For a whole finite candidate envelope rather than one fresh point,
`IsPlan.amalgamate` (#344) attaches two support plans agreeing on a common visible overlap on
their literal union; the one-point form is what one requested projection needs.

**The cell inventory** (`requestInventory`, over the common plan, by the explicit one-point
extension `CellScheme.extendOneWith`): the old cells, the request's **fresh cells** (those
containing the fresh point, pushed along `onePointProj e`), and one cell per **remaining graded
index** — in the plan, containing the fresh point, not inside the request face.  It is complete
(`requestInventory_complete`, from the context's and the request's completeness), its old face
is literally the context's domain (`requestInventory_old_face`), its request face is visible
and carries the request's plan (`requestInventory_request_face`), each fresh request cell sits
at its pushed graded index (`cell_freshCell`, injectively), and every cell is an old cell, a
fresh request cell, or a remaining-index cell (`requestInventory_cases`); the fresh request
cells are visible on the request face, the remaining-index cells are not, and an old cell is
visible on the request face exactly when it is visible on the root face of the context
(`scope_castAdd_subset_iff`).  Over the actual context and request:
`ReferenceContext.exists_requestInventory`, and the **shared root with rows**
(`ReferenceContext.shared_root`): the context's domain restricted to the root face and the
request's domain restricted to its initial face are both the root's domain, rows included, so
the rows the two faces prescribe agree on the shared root.

## Where this stops: the first genuinely new mixed-semantic obligation

The rows of the old cells and of the request's fresh cells are prescribed by the two faces (the
old face literally; the request face through the fresh-cell embedding and the shared root), and
they agree where both apply.  Not prescribed by anything are the rows of the **remaining-index
cells**: the full-scope controllers `(univ, k)` and every new mixed proper scope containing the
fresh point outside the request face.  Their rows must be consistent with the context's rows
and with the request's rows at once (mixed locality across the two faces), correct for the
reference data (equality on the exact requests, inequality on the lower-bound requests), and
bountiful for **every** permitted labelling of the two faces.  Two qualifications are part of
the obligation, not resolved by the inventory: one cell per remaining index is index
completeness, not semantic adequacy — owned witnesses or availability may require several cells
at one index — and the mixed proper scopes need the same work as the full-scope controllers.
`ReducedDeterminingProbe` (#343) is a template for a small determining set of probes; its proof
uses the fixed repaired scheme and does not transfer to this inventory.  No supply record is
added; nothing replaces the context by the fixed coupled example.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization AmalgamationPlan Value ExtOrd

universe w

/-! ## Plans of faces -/

section PlanImage

/-- Restriction commutes with the image along an injection. -/
theorem restrictPlan_image {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (g : ι ↪ κ)
    (S : Finset (Finset ι)) (T : Finset ι) :
    Plan.restrictPlan (S.image (Finset.image g)) (T.image g) =
      (Plan.restrictPlan S T).image (Finset.image g) := by
  ext U
  simp only [Plan.restrictPlan, Finset.mem_inter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨⟨V, hV, rfl⟩, hsub⟩
    exact ⟨V, ⟨hV, (Finset.image_subset_image_iff g.injective).mp hsub⟩, rfl⟩
  · rintro ⟨V, ⟨hV, hVT⟩, rfl⟩
    exact ⟨⟨V, hV, rfl⟩, Finset.image_subset_image hVT⟩

variable {k m : ℕ}

/-- The image of a restricted scheme's plan is the restriction of the plan to the face. -/
theorem image_restrictFace_plan (D : CellScheme (ι := Fin m) Finset.univ) (f : Fin k ↪ Fin m)
    (hr : Finset.univ.image f ∈ D.plan) :
    (D.restrictFace f hr).plan.image (Finset.image f) =
      Plan.restrictPlan D.plan (Finset.univ.image f) := by
  ext S
  simp only [Finset.mem_image, CellScheme.mem_restrictFace_plan D f hr, Plan.restrictPlan,
    Finset.mem_inter, Finset.mem_powerset]
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact ⟨hT, Finset.image_subset_image (Finset.subset_univ T)⟩
  · rintro ⟨hS, hsub⟩
    obtain ⟨T, -, rfl⟩ := Finset.subset_image_iff.mp hsub
    exact ⟨T, hS, rfl⟩

/-- **The plan of a projection**: if `q` projects along `f` to `P`, then `P`'s plan, pushed
along `f`, is the restriction of `q`'s plan to the face. -/
theorem plan_of_typeMap_eq_some {γ : Ordinal.{0}} (f : Fin k ↪ Fin m) {q : S γ m} {P : S γ k}
    (h : typeMap f q = some P) :
    P.scheme.scheme.plan.image (Finset.image f) =
      Plan.restrictPlan q.scheme.scheme.plan (Finset.univ.image f) := by
  obtain ⟨hv, hs⟩ := face_of_typeMap_eq_some f h
  rw [← image_restrictFace_plan q.scheme.scheme f hv]
  have : (q.scheme.restrictFace f hv).scheme.plan = P.scheme.scheme.plan :=
    congrArg (fun X : SemScheme k => X.scheme.plan) hs
  rw [← this]
  rfl

theorem univ_image_onePointProj (e : Fin k ↪ Fin m) :
    (Finset.univ : Finset (Fin (k + 1))).image (onePointProj e) =
      Finset.univ.image (e.trans Fin.castSuccEmb) ∪ {Fin.last m} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => exact Or.inr (onePointProj_last e)
    | cast i => exact Or.inl ⟨i, (onePointProj_castSucc e i).symm⟩
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨Fin.castSucc i, onePointProj_castSucc e i⟩
    · exact ⟨Fin.last k, onePointProj_last e⟩

theorem image_castSuccEmb_union_last :
    (Finset.univ : Finset (Fin m)).image Fin.castSuccEmb ∪ {Fin.last m} = Finset.univ := by
  rw [image_castSuccEmb_univ, Finset.union_comm, ← Finset.insert_eq,
    Finset.insert_erase (Finset.mem_univ _)]

end PlanImage

/-! ## The common plan over the actual context -/

section Attach

variable {M : Type w} {α β : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} (C : ReferenceContext R t reqs) (hβ : β ≤ α)

/-- **The root face is visible in the context** (exact consistency of the model). -/
theorem ReferenceContext.typeMap_proj (hM : R.IsModel) {p : S α.1 n} (hp : R.eval t = some p) :
    typeMap C.proj C.p₀ = some p := by
  have h := hM.consistent C.ctx C.p₀ C.proj C.eval_ctx
  rw [C.proj_ctx, hp] at h
  exact h.symm

/-- **The common plan**: a support plan on the context's points plus the fresh point in which
the old face carries the context's plan and the request face carries the request's plan,
both exactly.  From `IsPlan.attach_one_over_face`, with the agreement on the shared root face
derived from the request's root compatibility and the context's exact consistency. -/
theorem ReferenceContext.exists_common_plan (hM : R.IsModel) {p : S α.1 n}
    (hp : R.eval t = some p) {P : S β.1 (n + 1)}
    (hroot : typeMap Fin.castSuccEmb P = some (reduceType β.2 hβ p)) :
    ∃ Rp : Finset (Finset (Fin (C.m + 1))), Plan.IsPlan Finset.univ Rp ∧
      Finset.univ.image Fin.castSuccEmb ∈ Rp ∧
      Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
        C.p₀.scheme.scheme.plan.image (Finset.image Fin.castSuccEmb) ∧
      Finset.univ.image (onePointProj C.proj) ∈ Rp ∧
      Plan.restrictPlan Rp (Finset.univ.image (onePointProj C.proj)) =
        P.scheme.scheme.plan.image (Finset.image (onePointProj C.proj)) := by
  classical
  -- the context plan on the old coordinates
  have hP : Plan.IsPlan (Finset.univ.image Fin.castSuccEmb)
      (C.p₀.scheme.scheme.plan.image (Finset.image Fin.castSuccEmb)) :=
    Plan.isPlan_image _ C.p₀.scheme.scheme.isPlan
  have hpt := C.typeMap_proj hM hp
  obtain ⟨hvroot, -⟩ := face_of_typeMap_eq_some C.proj hpt
  -- the root face, on the old coordinates
  have hcomp : ((Finset.univ : Finset (Fin n)).image C.proj).image Fin.castSuccEmb =
      Finset.univ.image (C.proj.trans Fin.castSuccEmb) := by
    rw [Finset.image_image]; rfl
  have hB : Finset.univ.image (C.proj.trans Fin.castSuccEmb) ∈
      C.p₀.scheme.scheme.plan.image (Finset.image Fin.castSuccEmb) :=
    Finset.mem_image.mpr ⟨Finset.univ.image C.proj, hvroot, hcomp⟩
  have hx : Fin.last C.m ∉ (Finset.univ : Finset (Fin C.m)).image Fin.castSuccEmb := by
    rw [image_castSuccEmb_univ]; exact Finset.notMem_erase _ _
  -- the request plan on the root coordinates plus the fresh point
  have hQ : Plan.IsPlan (Finset.univ.image (C.proj.trans Fin.castSuccEmb) ∪ {Fin.last C.m})
      (P.scheme.scheme.plan.image (Finset.image (onePointProj C.proj))) := by
    rw [← univ_image_onePointProj]
    exact Plan.isPlan_image _ P.scheme.scheme.isPlan
  obtain ⟨hvP, -⟩ := face_of_typeMap_eq_some Fin.castSuccEmb hroot
  have hcomp' : ((Finset.univ : Finset (Fin n)).image Fin.castSuccEmb).image (onePointProj C.proj)
      = Finset.univ.image (C.proj.trans Fin.castSuccEmb) := by
    rw [Finset.image_image]
    congr 1
    funext i
    exact onePointProj_castSucc C.proj i
  have hBQ : Finset.univ.image (C.proj.trans Fin.castSuccEmb) ∈
      P.scheme.scheme.plan.image (Finset.image (onePointProj C.proj)) :=
    Finset.mem_image.mpr ⟨Finset.univ.image Fin.castSuccEmb, hvP, hcomp'⟩
  -- agreement on the shared root face: both restrict to the root's plan, pushed
  have hL : Plan.restrictPlan (P.scheme.scheme.plan.image (Finset.image (onePointProj C.proj)))
        (Finset.univ.image (C.proj.trans Fin.castSuccEmb)) =
      p.scheme.scheme.plan.image (Finset.image (C.proj.trans Fin.castSuccEmb)) := by
    rw [← hcomp', restrictPlan_image, ← plan_of_typeMap_eq_some Fin.castSuccEmb hroot,
      Finset.image_image]
    change p.scheme.scheme.plan.image
      (Finset.image (onePointProj C.proj) ∘ Finset.image Fin.castSuccEmb) = _
    congr 1
    funext V
    change (V.image Fin.castSuccEmb).image (onePointProj C.proj) = _
    rw [Finset.image_image]
    congr 1
    funext i
    exact onePointProj_castSucc C.proj i
  have hR' : Plan.restrictPlan (C.p₀.scheme.scheme.plan.image (Finset.image Fin.castSuccEmb))
        (Finset.univ.image (C.proj.trans Fin.castSuccEmb)) =
      p.scheme.scheme.plan.image (Finset.image (C.proj.trans Fin.castSuccEmb)) := by
    rw [← hcomp, restrictPlan_image, ← plan_of_typeMap_eq_some C.proj hpt, Finset.image_image]
    congr 1
    funext V
    change (V.image C.proj).image Fin.castSuccEmb = _
    rw [Finset.image_image]
    rfl
  have hres := hL.trans hR'.symm
  obtain ⟨Rp, hR, hAR, hRA, hBR, hRB⟩ := hP.attach_one_over_face hB hx hQ hBQ hres
  rw [image_castSuccEmb_union_last] at hR
  rw [← univ_image_onePointProj] at hBR hRB
  exact ⟨Rp, hR, hAR, hRA, hBR, hRB⟩

/-- The retained old face, in the form the explicit one-point extension of cell schemes
consumes: a face of the context's points is visible in the common plan exactly when it is
visible in the context's plan. -/
theorem common_plan_hface {m : ℕ} {Rp : Finset (Finset (Fin (m + 1)))}
    {P₀ : Finset (Finset (Fin m))}
    (hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
      P₀.image (Finset.image Fin.castSuccEmb)) :
    ∀ B : Finset (Fin m), B.image Fin.castSuccEmb ∈ Rp ↔ B ∈ P₀ := by
  intro B
  have hsub : B.image Fin.castSuccEmb ⊆ Finset.univ.image Fin.castSuccEmb :=
    Finset.image_subset_image (Finset.subset_univ B)
  constructor
  · intro h
    have : B.image Fin.castSuccEmb ∈ Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) :=
      Finset.mem_inter.mpr ⟨h, Finset.mem_powerset.mpr hsub⟩
    rw [hRA, Finset.mem_image] at this
    obtain ⟨B', hB', e⟩ := this
    rwa [(Finset.image_injective Fin.castSuccEmb.injective) e] at hB'
  · intro h
    have : B.image Fin.castSuccEmb ∈ Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) := by
      rw [hRA]; exact Finset.mem_image_of_mem _ h
    exact (Finset.mem_inter.mp this).1

end Attach

/-! ## The cell inventory: old cells, the request's fresh cells, one cell per remaining index

`requestInventory` is the explicit one-point extension (`CellScheme.extendOneWith`) of the
context scheme `X` along the common plan, with two kinds of new cells: the request's **fresh
cells** (those containing the fresh point, pushed along `onePointProj e`) and one cell per
remaining graded index of the plan that contains the fresh point but is **not** inside the
request face (`OutsideIndex`).  Index completeness is by construction; the old face is literal;
the request face carries the request's plan and each fresh request cell sits at its pushed
graded index.  What this does **not** decide is semantic adequacy at the outside indices:
whether one cell per index suffices, and which rows those cells carry. -/

section Inventory

open CellScheme
open CellScheme.restrictFace (pushGraded)

variable {m n : ℕ} (X : CellScheme (ι := Fin m) Finset.univ)
  (Y : CellScheme (ι := Fin (n + 1)) Finset.univ) (e : Fin n ↪ Fin m)
  (Rp : Finset (Finset (Fin (m + 1)))) (hR : Plan.IsPlan Finset.univ Rp)
  (hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
    X.plan.image (Finset.image Fin.castSuccEmb))
  (hRB : Plan.restrictPlan Rp (Finset.univ.image (onePointProj e)) =
    Y.plan.image (Finset.image (onePointProj e)))

/-- The request's fresh cells: those whose scope contains the fresh point. -/
abbrev FreshReq : Type := {c : Cell Y // Fin.last n ∈ Y.scope c}

/-- The remaining graded indices: in the common plan, containing the fresh point, not inside the
request face. -/
abbrev OutsideIndex : Type :=
  {BJ : Finset (Fin (m + 1)) × ℕ // BJ ∈ (Plan.gradedPlan Rp).filter
    (fun BJ => Fin.last m ∈ BJ.1 ∧ ¬ BJ.1 ⊆ Finset.univ.image (onePointProj e))}

/-- The new cells' graded indices. -/
def newIndex : FreshReq Y ⊕ OutsideIndex e Rp → Finset (Fin (m + 1)) × ℕ
  | Sum.inl c => pushGraded (onePointProj e) (Y.cell c.1)
  | Sum.inr BJ => BJ.1

include hRB in
theorem newIndex_mem (x : FreshReq Y ⊕ OutsideIndex e Rp) :
    newIndex Y e Rp x ∈ Plan.gradedPlan Rp := by
  classical
  rcases x with c | BJ
  · have hmem : (Y.scope c.1).image (onePointProj e) ∈ Rp := by
      have : (Y.scope c.1).image (onePointProj e) ∈
          Plan.restrictPlan Rp (Finset.univ.image (onePointProj e)) := by
        rw [hRB]; exact Finset.mem_image_of_mem _ (Y.scope_mem_plan c.1)
      exact (Finset.mem_inter.mp this).1
    have h := Plan.mem_gradedPlan.mp (Y.cell_mem c.1)
    refine Plan.mem_gradedPlan.mpr ⟨hmem, h.2.1, ?_⟩
    change (Y.cell c.1).2 ≤ ((Y.cell c.1).1.image (onePointProj e)).card
    rw [Finset.card_image_of_injective _ (onePointProj e).injective]
    exact h.2.2
  · exact (Finset.mem_filter.mp BJ.2).1

theorem newIndex_last (x : FreshReq Y ⊕ OutsideIndex e Rp) :
    Fin.last m ∈ (newIndex Y e Rp x).1 := by
  rcases x with c | BJ
  · exact Finset.mem_image.mpr ⟨Fin.last n, c.2, onePointProj_last e⟩
  · exact (Finset.mem_filter.mp BJ.2).2.1

/-- **The cell inventory** over the common plan. -/
noncomputable def requestInventory : CellScheme (ι := Fin (m + 1)) Finset.univ :=
  extendOneWith X Rp hR (common_plan_hface hRA) (newIndex Y e Rp) (newIndex_mem Y e Rp hRB)

variable {X Y e Rp hR hRA hRB}

theorem requestInventory_plan : (requestInventory X Y e Rp hR hRA hRB).plan = Rp := rfl

/-- The fresh point of the request face comes only from the request's fresh point. -/
theorem last_mem_of_mem_image {S : Finset (Fin (n + 1))}
    (h : Fin.last m ∈ S.image (onePointProj e)) : Fin.last n ∈ S := by
  obtain ⟨i, hi, hgi⟩ := Finset.mem_image.mp h
  induction i using Fin.lastCases with
  | last => exact hi
  | cast i =>
    rw [onePointProj_castSucc] at hgi
    exact absurd hgi (Fin.castSucc_ne_last _)

/-- **Index completeness**, from the context's and the request's. -/
theorem requestInventory_complete (hX : X.IsComplete) (hY : Y.IsComplete) :
    (requestInventory X Y e Rp hR hRA hRB).IsComplete := by
  classical
  refine IsComplete.extendOneWith hX fun BJ hBJ hlast => ?_
  by_cases hF : BJ.1 ⊆ Finset.univ.image (onePointProj e)
  · -- inside the request face: a fresh request cell at that index
    have h := Plan.mem_gradedPlan.mp hBJ
    have hmem : BJ.1 ∈ Y.plan.image (Finset.image (onePointProj e)) := by
      rw [← hRB]
      exact Finset.mem_inter.mpr ⟨h.1, Finset.mem_powerset.mpr hF⟩
    obtain ⟨S, hS, hSB⟩ := Finset.mem_image.mp hmem
    obtain ⟨c, hc⟩ := hY (S, BJ.2) (Plan.mem_gradedPlan.mpr ⟨hS, h.2.1, by
      have := h.2.2
      rwa [← hSB, Finset.card_image_of_injective _ (onePointProj e).injective] at this⟩)
    refine ⟨Sum.inl ⟨c, ?_⟩, ?_⟩
    · change Fin.last n ∈ (Y.cell c).1
      rw [hc]
      exact last_mem_of_mem_image (hSB.symm ▸ hlast)
    · change pushGraded (onePointProj e) (Y.cell c) = BJ
      rw [hc]
      exact Prod.ext hSB rfl
  · exact ⟨Sum.inr ⟨BJ, Finset.mem_filter.mpr ⟨hBJ, hlast, hF⟩⟩, rfl⟩

/-- **The old face is literal.** -/
theorem requestInventory_old_face :
    (requestInventory X Y e Rp hR hRA hRB).restrictFace Fin.castSuccEmb extendOneWith_visible
      = X :=
  restrictFace_extendOneWith (newIndex_last Y e Rp)

/-- **The request face is visible and carries the request's plan.** -/
theorem requestInventory_request_face :
    Finset.univ.image (onePointProj e) ∈ (requestInventory X Y e Rp hR hRA hRB).plan ∧
      Plan.restrictPlan (requestInventory X Y e Rp hR hRA hRB).plan
        (Finset.univ.image (onePointProj e)) = Y.plan.image (Finset.image (onePointProj e)) := by
  refine ⟨?_, hRB⟩
  have : Finset.univ.image (onePointProj e) ∈
      Plan.restrictPlan Rp (Finset.univ.image (onePointProj e)) := by
    rw [hRB]
    exact Finset.mem_image_of_mem _ Y.isPlan.domain_mem
  exact (Finset.mem_inter.mp this).1

/-- The request's fresh cells, as cells of the inventory. -/
noncomputable def freshCell (c : FreshReq Y) : Cell (requestInventory X Y e Rp hR hRA hRB) :=
  Fin.natAdd X.card (Fintype.equivFin (FreshReq Y ⊕ OutsideIndex e Rp) (Sum.inl c))

/-- The remaining-index cells. -/
noncomputable def outsideCell (b : OutsideIndex e Rp) :
    Cell (requestInventory X Y e Rp hR hRA hRB) :=
  Fin.natAdd X.card (Fintype.equivFin (FreshReq Y ⊕ OutsideIndex e Rp) (Sum.inr b))

/-- **Each fresh request cell sits at its pushed graded index.** -/
theorem cell_freshCell (c : FreshReq Y) :
    (requestInventory X Y e Rp hR hRA hRB).cell (freshCell c) =
      pushGraded (onePointProj e) (Y.cell c.1) := by
  unfold freshCell requestInventory
  rw [extendOneWith_cell_natAdd, Equiv.symm_apply_apply]
  rfl

theorem cell_outsideCell (b : OutsideIndex e Rp) :
    (requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b) = b.1 := by
  unfold outsideCell requestInventory
  rw [extendOneWith_cell_natAdd, Equiv.symm_apply_apply]
  rfl

theorem freshCell_injective :
    Function.Injective (freshCell (hR := hR) (hRA := hRA) (hRB := hRB) :
      FreshReq Y → Cell (requestInventory X Y e Rp hR hRA hRB)) := by
  intro c c' h
  unfold freshCell at h
  have := Fin.natAdd_injective _ _ h
  exact Sum.inl_injective ((Fintype.equivFin _).injective this)

/-- **Every cell** is an old cell, a fresh request cell, or a remaining-index cell. -/
theorem requestInventory_cases (d : Cell (requestInventory X Y e Rp hR hRA hRB)) :
    (∃ i : Cell X, d = Fin.castAdd _ i) ∨ (∃ c, d = freshCell c) ∨ ∃ b, d = outsideCell b := by
  induction d using Fin.addCases with
  | left i => exact Or.inl ⟨i, rfl⟩
  | right j =>
    rcases hx : (Fintype.equivFin (FreshReq Y ⊕ OutsideIndex e Rp)).symm j with c | b
    · refine Or.inr (Or.inl ⟨c, ?_⟩)
      unfold freshCell
      rw [← hx, Equiv.apply_symm_apply]
    · refine Or.inr (Or.inr ⟨b, ?_⟩)
      unfold outsideCell
      rw [← hx, Equiv.apply_symm_apply]

/-- A fresh request cell is visible on the request face. -/
theorem scope_freshCell_subset (c : FreshReq Y) :
    (requestInventory X Y e Rp hR hRA hRB).scope (freshCell c) ⊆
      Finset.univ.image (onePointProj e) := by
  change ((requestInventory X Y e Rp hR hRA hRB).cell (freshCell c)).1 ⊆ _
  rw [cell_freshCell]
  exact Finset.image_subset_image (Finset.subset_univ _)

/-- A remaining-index cell is **not** visible on the request face. -/
theorem scope_outsideCell_not_subset (b : OutsideIndex e Rp) :
    ¬ (requestInventory X Y e Rp hR hRA hRB).scope (outsideCell b) ⊆
      Finset.univ.image (onePointProj e) := by
  change ¬ ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)).1 ⊆ _
  rw [cell_outsideCell]
  exact (Finset.mem_filter.mp b.2).2.2

/-- An old cell is visible on the request face exactly when it is visible on the root face of
the context. -/
theorem scope_castAdd_subset_iff (i : Cell X) :
    (requestInventory X Y e Rp hR hRA hRB).scope (Fin.castAdd _ i) ⊆
        Finset.univ.image (onePointProj e) ↔
      X.scope i ⊆ Finset.univ.image e := by
  unfold requestInventory
  rw [extendOneWith_scope_castAdd]
  constructor
  · intro h x hx
    have hmem := h (Finset.mem_image_of_mem _ hx)
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hmem
    induction y using Fin.lastCases with
    | last =>
      rw [onePointProj_last] at hy
      exact absurd hy.symm (Fin.castSucc_ne_last x)
    | cast y =>
      rw [onePointProj_castSucc] at hy
      have hyx : e y = x := Fin.castSucc_injective _ (hy.trans (Fin.castSuccEmb_apply x))
      exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, hyx⟩
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp (h hy)
    exact Finset.mem_image.mpr ⟨Fin.castSucc z, Finset.mem_univ _, onePointProj_castSucc e z⟩

end Inventory

/-! ## Over the actual context -/

section Actual

open CellScheme
open CellScheme.restrictFace (pushGraded)

variable {M : Type w} {α β : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} (C : ReferenceContext R t reqs) (hβ : β ≤ α)

/-- **The shared root, with rows**: the context's domain restricted to the root face and the
request's domain restricted to its initial face are both the root's domain — as domains with
semantics, rows included.  So the rows prescribed by the two faces agree on the shared root. -/
theorem ReferenceContext.shared_root (hM : R.IsModel) {p : S α.1 n} (hp : R.eval t = some p)
    {P : S β.1 (n + 1)} (hroot : typeMap Fin.castSuccEmb P = some (reduceType β.2 hβ p)) :
    (∃ hv, C.p₀.scheme.restrictFace C.proj hv = p.scheme) ∧
      ∃ hv', P.scheme.restrictFace Fin.castSuccEmb hv' = p.scheme :=
  ⟨face_of_typeMap_eq_some C.proj (C.typeMap_proj hM hp),
    face_of_typeMap_eq_some Fin.castSuccEmb hroot⟩

/-- **The inventory over the actual context and request**: a complete cell scheme on the
context's points plus the fresh point, whose old face is literally the context's domain, whose
request face is visible and carries the request's plan, and in which every fresh request cell
sits at its pushed graded index. -/
theorem ReferenceContext.exists_requestInventory (hM : R.IsModel) {p : S α.1 n}
    (hp : R.eval t = some p) {P : S β.1 (n + 1)}
    (hroot : typeMap Fin.castSuccEmb P = some (reduceType β.2 hβ p)) :
    ∃ (D : CellScheme (ι := Fin (C.m + 1)) Finset.univ)
      (hv : Finset.univ.image Fin.castSuccEmb ∈ D.plan), D.IsComplete ∧
      D.restrictFace Fin.castSuccEmb hv = C.p₀.scheme.scheme ∧
      Finset.univ.image (onePointProj C.proj) ∈ D.plan ∧
      Plan.restrictPlan D.plan (Finset.univ.image (onePointProj C.proj)) =
        P.scheme.scheme.plan.image (Finset.image (onePointProj C.proj)) ∧
      ∃ fresh : FreshReq P.scheme.scheme → Cell D, Function.Injective fresh ∧
        ∀ c, D.cell (fresh c) = pushGraded (onePointProj C.proj) (P.scheme.scheme.cell c.1) := by
  obtain ⟨Rp, hR, -, hRA, -, hRB⟩ := C.exists_common_plan hβ hM hp hroot
  refine ⟨requestInventory C.p₀.scheme.scheme P.scheme.scheme C.proj Rp hR hRA hRB,
    extendOneWith_visible, requestInventory_complete C.p₀.scheme.complete P.scheme.complete,
    requestInventory_old_face, (requestInventory_request_face).1,
    (requestInventory_request_face).2, freshCell (hR := hR) (hRA := hRA) (hRB := hRB),
    freshCell_injective, fun c => cell_freshCell c⟩

end Actual

end VaughtConjecture.Knight
