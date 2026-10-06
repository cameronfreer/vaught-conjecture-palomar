/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.MixedRows
public import VaughtConjecture.Knight.ContextSourceRow

/-! # The collision obstruction on the actual reference context

The reviewer's assignment (2026-09-15, V-C item 1): instantiate the collision obstruction of
`Knight/MixedRows.lean` on the actual receiver reference context and request domain — exhibit
the lawful separating prescription and the exact failed graded pair, or prove why that
hypothesis cannot occur there; keep the actual threshold.

**The exact pair.**  The full-scope controller of the actual threshold `N` is the remaining
cell at `(univ, N)` (`controllerIndex`, an index of the inventory as soon as the cap has grade
`N` and no old cell is visible on the root face).  The failed bountifulness instance is
**the cap's own pair below the controller's**: `(scope cap, N) ≺ (univ, N)`, with the bottom
cap and the `⊥` ambient (`not_bountiful_of_old_separating`).  Its lower set consists of old
cells only, so the lawful prescription is a section of the **receiver's own rows** on the
cap's lower set (`p`, transported by `respectsBelow_of_face_section`): one separating two
same-grade old cells that the context's actual labels identify, strictly below its value at
the cap.  On the actual context this is `ReferenceContext.not_bountiful_of_old_separating`,
with `C.capBase` and `C.N`.

**Why only old-face collisions are live.**  Inside any lower set below a remaining cell, the
identifications the recoded rows impose between a remaining cell and a same-grade cell of
equal full label below it are **tied** by the remaining cell's own locality together with
availability (`tied_of_fullLabel_eq_remaining`: the two labels are equal under every
respecting labelling), so no section separates them.  The own value of a remaining index is
attained at a cell of one face (`ownValue_eq_or`), which is exactly such an identification.
Hence the only identification a lawful section can break is between two cells of one face
with equal actual labels and untied rows — for a one-cell request, two **old** cells.

**What the reference-context construction decides.**  Nothing about the rows beyond the cap
and representative labels: `exists_referenceContext` produces the context from the model
clauses (Uniformity and High-Grade Dominance steps) and carries no information on whether the
receiver's rows tie two equal-labelled cells.  So the obstruction is neither guaranteed nor
excluded by the construction: it **occurs** exactly when the receiver's scheme admits an
old-face separating section under the cap, and its hypothesis is **unavailable** when, for
instance, the context's labels are injective on each grade below the cap.  The first is a
property of the receiver model; deciding it for a given model is not a construction step here.
Neither direction of bountifulness is claimed beyond the refutation.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd
open CellScheme.restrictFace (pushGraded)

section Collision

variable {m n : ℕ} {X : CellScheme (ι := Fin m) Finset.univ}
  {Y : CellScheme (ι := Fin (n + 1)) Finset.univ} {e : Fin n ↪ Fin m}
  {Rp : Finset (Finset (Fin (m + 1)))} {hR : Plan.IsPlan Finset.univ Rp}
  {hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
    X.plan.image (Finset.image Fin.castSuccEmb)}
  {hRB : Plan.restrictPlan Rp (Finset.univ.image (onePointProj e)) =
    Y.plan.image (Finset.image (onePointProj e))}
  (hvX : Finset.univ.image e ∈ X.plan) (hvY : Finset.univ.image Fin.castSuccEmb ∈ Y.plan)
  (hroot : X.restrictFace e hvX = Y.restrictFace Fin.castSuccEmb hvY)
  (rowsX : Semantics X) (rowsY : Semantics Y) (labX : Cell X → ExtOrd) (labY : Cell Y → ExtOrd)
  (hX : ∀ d, SelfVis (X.grade d) (labX d)) (hY : ∀ c, SelfVis (Y.grade c) (labY c))

/-! ## The full-scope controller of the actual threshold -/

/-- Over the empty root the whole scope is not inside the request face: a point of an old
cell's scope is not in it. -/
theorem univ_not_subset_request_face (cap : Cell X)
    (hn : ∀ i : Cell X, ¬ X.scope i ⊆ Finset.univ.image e) :
    ¬ (Finset.univ : Finset (Fin (m + 1))) ⊆ Finset.univ.image (onePointProj e) := by
  intro h
  apply hn cap
  intro x hx
  have hmem := h (Finset.mem_univ (Fin.castSucc x))
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hmem
  induction y using Fin.lastCases with
  | last =>
    rw [onePointProj_last] at hy
    exact absurd hy (Fin.castSucc_ne_last x).symm
  | cast y =>
    rw [onePointProj_castSucc] at hy
    have hyx : e y = x := Fin.castSucc_injective _ hy
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, hyx⟩

include hR in
/-- **The full-scope index at the cap's grade** is a remaining index: visible (the whole
plan), containing the fresh point, not inside the request face. -/
theorem controllerIndex_mem (cap : Cell X) (hn : ∀ i : Cell X, ¬ X.scope i ⊆ Finset.univ.image e) :
    ((Finset.univ : Finset (Fin (m + 1))), X.grade cap) ∈ (Plan.gradedPlan Rp).filter
      (fun BJ => Fin.last m ∈ BJ.1 ∧ ¬ BJ.1 ⊆ Finset.univ.image (onePointProj e)) := by
  refine Finset.mem_filter.mpr ⟨?_, Finset.mem_univ _, univ_not_subset_request_face cap hn⟩
  refine Plan.mem_gradedPlan.mpr ⟨hR.domain_mem, X.grade_pos cap, ?_⟩
  change X.grade cap ≤ (Finset.univ : Finset (Fin (m + 1))).card
  calc X.grade cap ≤ (X.scope cap).card := X.grade_le_card_scope cap
    _ ≤ Fintype.card (Fin m) := Finset.card_le_univ _
    _ ≤ (Finset.univ : Finset (Fin (m + 1))).card := by
        rw [Finset.card_univ, Fintype.card_fin, Fintype.card_fin]; exact Nat.le_succ m

include hR in
/-- The full-scope controller at the cap's grade, as a remaining index. -/
noncomputable def controllerIndex (cap : Cell X)
    (hn : ∀ i : Cell X, ¬ X.scope i ⊆ Finset.univ.image e) : OutsideIndex e Rp :=
  ⟨((Finset.univ : Finset (Fin (m + 1))), X.grade cap), controllerIndex_mem (hR := hR) cap hn⟩

/-! ## Identifications with a remaining cell are tied -/

include hX hY in
/-- **A remaining cell and a same-grade cell of equal full label below it are tied**: under
every respecting labelling of the remaining cell's lower set they carry the same label — the
cell's own locality caps the other at it, availability lifts the other to it. -/
theorem tied_of_fullLabel_eq_remaining (b : OutsideIndex e Rp)
    {q' : (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)) → ExtOrd}
    (hq : RespectsSemanticsBelow (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot
      rowsX rowsY labX labY hX hY) ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b))
      q')
    (x : (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)))
    (hF : fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY x.1 =
      fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY (outsideCell b))
    (hgr : (requestInventory X Y e Rp hR hRA hRB).grade x.1 =
      (requestInventory X Y e Rp hR hRA hRB).grade (outsideCell b)) :
    q' x = q' ⟨outsideCell b, GradedLe.refl _⟩ := by
  have hcap := capped_eq_of_fullLabel_eq hvX hvY hroot rowsX rowsY labX labY hX hY b hq x
    ⟨outsideCell b, GradedLe.refl _⟩ hF hgr
  rw [min_self] at hcap
  obtain ⟨Xi, hXi, hle⟩ := hq.availability x ⟨outsideCell b, GradedLe.refl _⟩ x.2.1 hgr
  have hXi' : Xi = ⟨outsideCell b, GradedLe.refl _⟩ := Subtype.ext (eq_outsideCell_of_cell_eq hXi)
  rw [hXi'] at hle
  exact le_antisymm hle (by rw [← hcap]; exact min_le_left _ _)

/-! ## The obstruction at the cap's pair below the controller -/

include hX hY in
/-- **Bottom-cap completion from the cap's pair into the controller's fails for an old-face
separating section**: if a labelling of the cap's lower set respecting the **receiver's own
rows** separates two same-grade old cells that the actual labels identify, strictly below its
value at the cap, then the mixed rows are not bountiful — the failed pair is
`(scope cap, N) ≺ (univ, N)`. -/
theorem not_bountiful_of_old_separating (cap : Cell X)
    (hn : ∀ i : Cell X, ¬ X.scope i ⊆ Finset.univ.image e)
    {p : X.below (X.cell cap) → ExtOrd} (hp : RespectsSemanticsBelow rowsX (X.cell cap) p)
    (d₁ d₂ : X.below (X.cell cap)) (hlab : labX d₁.1 = labX d₂.1)
    (hgr : X.grade d₁.1 = X.grade d₂.1) (h12 : p d₁ < p d₂)
    (hcap : p d₁ < p ⟨cap, GradedLe.refl _⟩) :
    ¬ (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY hX
      hY).IsBountiful := by
  set b : OutsideIndex e Rp := controllerIndex (hR := hR) cap hn with hb
  have hp' := respectsBelow_of_face_section (hR := hR) (hRA := hRA) (hRB := hRB) rowsX
    (mixedRows hvX hvY hroot rowsX rowsY labX labY hX hY) (Fin.castAdd _) oldBelowEquiv
    (fun _ _ => rfl) grade_castAdd scope_castAdd_subset_iff'
    (fun i d => mixedRows_old (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY
      labX labY hX hY i d _) cap hp
  refine not_bountiful_of_separating hvX hvY hroot rowsX rowsY labX labY hX hY b
    ((requestInventory X Y e Rp hR hRA hRB).cell_mem (Fin.castAdd _ cap)) ?_ ?_ hp'
    (oldBelowEquiv cap d₁) (oldBelowEquiv cap d₂) (oldBelowEquiv cap ⟨cap, GradedLe.refl _⟩)
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- the cap's pair lies below the controller's
    rw [cell_outsideCell]
    refine ⟨Finset.subset_univ _, ?_⟩
    change (requestInventory X Y e Rp hR hRA hRB).grade (Fin.castAdd _ cap) ≤ X.grade cap
    rw [grade_castAdd]
  · -- and is not the controller's: the fresh point is not in the cap's pushed scope
    intro h
    rw [cell_outsideCell] at h
    have hs : (requestInventory X Y e Rp hR hRA hRB).scope (Fin.castAdd _ cap) = Finset.univ :=
      congrArg Prod.fst h
    unfold requestInventory at hs
    rw [extendOneWith_scope_castAdd] at hs
    have := Finset.mem_univ (Fin.last m)
    rw [← hs] at this
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp this
    exact Fin.castSucc_ne_last x hx
  · change fullLabel labX labY (Fin.castAdd _ d₁.1) = fullLabel labX labY (Fin.castAdd _ d₂.1)
    rw [fullLabel_castAdd, fullLabel_castAdd]
    exact hlab
  · change (requestInventory X Y e Rp hR hRA hRB).grade (Fin.castAdd _ d₁.1) =
      (requestInventory X Y e Rp hR hRA hRB).grade (Fin.castAdd _ d₂.1)
    rw [grade_castAdd, grade_castAdd]
    exact hgr
  · simp only [Equiv.symm_apply_apply]
    exact h12
  · have e1 := (oldBelowEquiv (Y := Y) (e := e) (hR := hR) (hRA := hRA) (hRB := hRB)
      cap).symm_apply_apply d₁
    have e2 := (oldBelowEquiv (Y := Y) (e := e) (hR := hR) (hRA := hRA) (hRB := hRB)
      cap).symm_apply_apply ⟨cap, GradedLe.refl _⟩
    exact ((congrArg p e1).symm ▸ hcap).trans_eq (congrArg p e2).symm
  · rw [scope_outsideCell]
    exact Finset.subset_univ _
  · change (requestInventory X Y e Rp hR hRA hRB).grade (Fin.castAdd _ cap) = _
    rw [grade_castAdd, grade_outsideCell]
    rfl

end Collision

/-! ## On the actual reference context -/

namespace ReferenceContext

universe w

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} (C : ReferenceContext R t reqs)

/-- **The collision obstruction on the actual reference context**, at the actual threshold
`C.N`: over any inventory of the context's domain with a request domain `Y`, if a labelling of
the cap's lower set respecting the context's own rows separates two same-grade cells that the
context's actual labels identify, strictly below its value at the cap, then the mixed rows are
not bountiful; the failed pair is `(scope C.capBase, C.N) ≺ (univ, C.N)`. -/
theorem not_bountiful_of_old_separating {Y : CellScheme (ι := Fin (n + 1)) Finset.univ}
    {Rp : Finset (Finset (Fin (C.m + 1)))} {hR : Plan.IsPlan Finset.univ Rp}
    {hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
      C.p₀.scheme.scheme.plan.image (Finset.image Fin.castSuccEmb)}
    {hRB : Plan.restrictPlan Rp (Finset.univ.image (onePointProj C.proj)) =
      Y.plan.image (Finset.image (onePointProj C.proj))}
    (hvX : Finset.univ.image C.proj ∈ C.p₀.scheme.scheme.plan)
    (hvY : Finset.univ.image Fin.castSuccEmb ∈ Y.plan)
    (hroot : C.p₀.scheme.scheme.restrictFace C.proj hvX = Y.restrictFace Fin.castSuccEmb hvY)
    (rowsY : Semantics Y) (labY : Cell Y → ExtOrd) (hY : ∀ c, SelfVis (Y.grade c) (labY c))
    (hn : ∀ i : Cell C.p₀.scheme.scheme, ¬ C.p₀.scheme.scheme.scope i ⊆ Finset.univ.image C.proj)
    {p : C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell C.capBase) → ExtOrd}
    (hp : RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell C.capBase) p)
    (d₁ d₂ : C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell C.capBase))
    (hlab : C.p₀.label d₁.1 = C.p₀.label d₂.1)
    (hgr : C.p₀.scheme.scheme.grade d₁.1 = C.p₀.scheme.scheme.grade d₂.1) (h12 : p d₁ < p d₂)
    (hcap : p d₁ < p ⟨C.capBase, GradedLe.refl _⟩) :
    ¬ (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot C.p₀.scheme.rows rowsY
      C.p₀.label labY (fun d => (C.p₀.respects.orderly d).symm) hY).IsBountiful :=
  VaughtConjecture.Knight.not_bountiful_of_old_separating hvX hvY hroot C.p₀.scheme.rows rowsY
    C.p₀.label labY (fun d => (C.p₀.respects.orderly d).symm) hY C.capBase hn hp d₁ d₂ hlab hgr
    h12 hcap

end ReferenceContext

end VaughtConjecture.Knight
