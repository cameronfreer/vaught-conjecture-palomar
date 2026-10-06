/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RequestFaceIdentification
public import VaughtConjecture.Knight.CoupledRepair

/-! # Uniform request-row preservation, and the collision obstruction at a mixed index

**Uniform request-row preservation** (`prescribedRows_req`): one theorem covers every request
cell, fresh or root — the prescribed row of an identified request cell, read at an identified
request cell below it, is the request's row.  On fresh cells this is
`prescribedRows_fresh`; on root cells it is `prescribedRows_root` composed with the **shared-root
semantic equality**: the context's rows restricted to the root face and the request's rows
restricted to its initial face agree (`SharedRootRows`), which is what an equality of the two
restricted domains with their semantics yields (`sharedRootRows_of_eq`, from
`SemScheme.rows_E_castCellEq`) — over the actual context, `ReferenceContext.sharedRootRows`,
from the two face equations of `ReferenceContext.shared_root`.

**One genuinely mixed index, working backwards from a section.**  Fix a remaining-index cell
`M` and a candidate row for it in advance (the diagonal candidate of
`RequestFaceIdentification`, or any row); ask whether every relevant prescribed face labelling
has a respecting extension through `M`.  The first explicit obstruction is to **mixed
locality**, and it is a *collision*: locality at `M` reads every lower cell through one shifter
applied to the row's value, so two lower cells of the same grade at which the row reads the
same value receive the same label below the cap `r M` under every respecting `r`
(`RespectsSemanticsBelow.probe_eq_of_row_eq`, restated as `capped_eq_of_row_eq`).  For the
diagonal candidate this is `diagonal_row_identifies`: cells with equal diagonals and grades
cannot be separated below the cap.  So a prescribed pair of face labellings that separates two
equal-diagonal same-grade cells below `M` — up to the cap — has **no** respecting extension with
that row at `M`; the row must be chosen to separate whatever the permitted labellings separate.

**The concrete instance** (`diagonal_H₀old_eq_H₀new`, `no_realization_of_equal_H₀_rows`): in the
repaired coupled semantics the diagonals of `H₀old` and `H₀new` coincide (both cells retract to
the same cell of the three-cell family), while the prescribed pair labels them `γ₀ < γ₁`; hence
no semantics on the glued scheme whose full-scope controllers read equal values at the two
cells — the diagonal candidate in particular — admits a respecting labelling realizing the pair.
This is the collision at the smallest mixed index, and it is exactly why the coupled
construction needed separating controllers (`separating_controllers_of_realizes`).  No row is
chosen after seeing the universally quantified input; the obstruction is stated against the
fixed candidate family.  Additional controllers at an outside index are the room availability
leaves; their usefulness is not assumed here.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value
open CellScheme.restrictFace (toCell belowMap pushGraded)

/-! ## Rows along an equality of domains with semantics -/

section RowsCast

variable {n : ℕ}

/-- The rows of equal domains agree along cell transport. -/
theorem SemScheme.rows_E_castCellEq {D₁ D₂ : SemScheme n} (h : D₁ = D₂) (Sig : Cell D₁.scheme)
    (d : D₁.scheme.below (D₁.scheme.cell Sig)) :
    D₂.rows.E (castCellEq (congrArg SemScheme.scheme h) Sig)
        ⟨castCellEq (congrArg SemScheme.scheme h) d.1, by
          rw [cell_castCellEq, cell_castCellEq]; exact d.2⟩ =
      D₁.rows.E Sig d := by
  subst h; rfl

end RowsCast

/-! ## Uniform request-row preservation -/

section Uniform

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

/-- A cell below a transported cell of the root, transported. -/
noncomputable def rootBelowCast (j : Cell (Y.restrictFace Fin.castSuccEmb hvY))
    (d : (X.restrictFace e hvX).below
      ((X.restrictFace e hvX).cell (castCellEq hroot.symm j))) :
    (Y.restrictFace Fin.castSuccEmb hvY).below ((Y.restrictFace Fin.castSuccEmb hvY).cell j) :=
  ⟨castCellEq hroot d.1, by
    rw [cell_castCellEq, ← cell_castCellEq hroot.symm j]
    exact d.2⟩

/-- **Shared-root agreement of rows**: the context's rows at the context cells of the root agree
with the request's rows at the request cells of the root, read at corresponding cells. -/
def SharedRootRows : Prop :=
  ∀ (j : Cell (Y.restrictFace Fin.castSuccEmb hvY))
    (d : (X.restrictFace e hvX).below
      ((X.restrictFace e hvX).cell (castCellEq hroot.symm j))),
    rowsX.E (rootCell hvX hvY hroot j) (belowMap X e hvX _ d) =
      rowsY.E (toCell Y Fin.castSuccEmb hvY j)
        (belowMap Y Fin.castSuccEmb hvY j (rootBelowCast hvX hvY hroot j d))

/-- Shared-root agreement of rows follows from an equality of the two restricted domains with
their semantics. -/
theorem sharedRootRows_of_eq {X' Y' : SemScheme _} (hX' : X'.scheme = X) (hY' : Y'.scheme = Y)
    (hvX' : Finset.univ.image e ∈ X'.scheme.plan)
    (hvY' : Finset.univ.image Fin.castSuccEmb ∈ Y'.scheme.plan)
    (hSR : X'.restrictFace e hvX' = Y'.restrictFace Fin.castSuccEmb hvY')
    (hrX : HEq X'.rows rowsX) (hrY : HEq Y'.rows rowsY) :
    SharedRootRows hvX hvY hroot rowsX rowsY := by
  subst hX' hY'
  obtain rfl := eq_of_heq hrX
  obtain rfl := eq_of_heq hrY
  intro j d
  have key := SemScheme.rows_E_castCellEq hSR (castCellEq hroot.symm j) d
  refine (key.symm.trans ?_)
  exact Semantics.E_congr Y'.rows
    (congrArg (toCell Y'.scheme Fin.castSuccEmb hvY') (castCellEq_castCellEq_symm hroot j)) rfl

variable {ctrl : ∀ b : OutsideIndex e Rp, (requestInventory X Y e Rp hR hRA hRB).below
    ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)) → ExtOrd}
  (hctrl : ∀ b, Transform.IsOrderly
    (fun d : (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)) =>
      (requestInventory X Y e Rp hR hRA hRB).grade d.1) (ctrl b))

/-- Request-face preservation on a cell equal to a fresh cell. -/
theorem prescribedRows_fresh_of_eq (c : FreshReq Y)
    {Sig : Cell (requestInventory X Y e Rp hR hRA hRB)} (hS : Sig = freshCell c)
    (d' : Y.below (Y.cell c.1)) (h) :
    (prescribedRows hvX hvY hroot rowsX rowsY ctrl hctrl).E Sig
        ⟨reqCell hvX hvY hroot d'.1, h⟩ = rowsY.E c.1 d' := by
  subst hS
  exact prescribedRows_fresh hvX hvY hroot rowsX rowsY hctrl c d' h

/-- **Uniform request-row preservation**: for every request cell, fresh or root, the prescribed
row of its identified cell, read at an identified request cell below it, is the request's row —
given the shared-root agreement of rows. -/
theorem prescribedRows_req (hrows : SharedRootRows hvX hvY hroot rowsX rowsY) (c : Cell Y)
    (d' : Y.below (Y.cell c)) (h) :
    (prescribedRows hvX hvY hroot rowsX rowsY ctrl hctrl).E (reqCell hvX hvY hroot c)
        ⟨reqCell hvX hvY hroot d'.1, h⟩ = rowsY.E c d' := by
  by_cases hc : Fin.last n ∈ Y.scope c
  · exact prescribedRows_fresh_of_eq hvX hvY hroot rowsX rowsY hctrl ⟨c, hc⟩
      (reqCell_of_last hvX hvY hroot hc) d' h
  · have hd : Fin.last n ∉ Y.scope d'.1 := not_last_of_gradedLe hc d'.2
    have h' : GradedLe (X.cell (rootOf hvX hvY hroot d'.1 hd))
        (X.cell (rootOf hvX hvY hroot c hc)) :=
      (gradedLe_rootOf_iff hvX hvY hroot hc hd).mpr d'.2
    rw [prescribedRows_root hvX hvY hroot rowsX rowsY hctrl c hc d' h h']
    -- the two chosen root cells
    set j := Classical.choose (restrictFace.exists_toCell_eq Y Fin.castSuccEmb hvY
      (scope_subset_castSucc_of_not_last hc)) with hjdef
    have hj : toCell Y Fin.castSuccEmb hvY j = c := Classical.choose_spec
      (restrictFace.exists_toCell_eq Y Fin.castSuccEmb hvY (scope_subset_castSucc_of_not_last hc))
    set j₂ := Classical.choose (restrictFace.exists_toCell_eq Y Fin.castSuccEmb hvY
      (scope_subset_castSucc_of_not_last hd)) with hj₂def
    have hj₂ : toCell Y Fin.castSuccEmb hvY j₂ = d'.1 := Classical.choose_spec
      (restrictFace.exists_toCell_eq Y Fin.castSuccEmb hvY (scope_subset_castSucc_of_not_last hd))
    have mem : GradedLe ((X.restrictFace e hvX).cell (castCellEq hroot.symm j₂))
        ((X.restrictFace e hvX).cell (castCellEq hroot.symm j)) := by
      rw [cell_castCellEq, cell_castCellEq]
      exact (restrictFace.gradedLe_restrictFace_iff Y Fin.castSuccEmb hvY).mpr
        (by rw [hj, hj₂]; exact d'.2)
    have key := hrows j ⟨castCellEq hroot.symm j₂, mem⟩
    refine key.trans ?_
    exact Semantics.E_congr rowsY hj (by
      change toCell Y Fin.castSuccEmb hvY (castCellEq hroot (castCellEq hroot.symm j₂)) = d'.1
      rw [castCellEq_castCellEq_symm, hj₂])

end Uniform

/-! ## Over the actual context -/

section Actual

open TypeTower StageType KnightRealization

universe w

variable {M : Type w} {α β : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} (C : ReferenceContext R t reqs) (hβ : β ≤ α)

/-- **Shared-root agreement of rows over the actual context**: from the two face equations of
`ReferenceContext.shared_root`, the context's rows and the request's rows agree on the shared
root — the hypothesis of the uniform request-row preservation. -/
theorem ReferenceContext.sharedRootRows (hM : R.IsModel) {p : S α.1 n} (hp : R.eval t = some p)
    {P : S β.1 (n + 1)} (hroot : typeMap Fin.castSuccEmb P = some (reduceType β.2 hβ p))
    (hvX : Finset.univ.image C.proj ∈ C.p₀.scheme.scheme.plan)
    (hvY : Finset.univ.image Fin.castSuccEmb ∈ P.scheme.scheme.plan)
    (hroot' : C.p₀.scheme.scheme.restrictFace C.proj hvX =
      P.scheme.scheme.restrictFace Fin.castSuccEmb hvY) :
    SharedRootRows hvX hvY hroot' C.p₀.scheme.rows P.scheme.rows := by
  obtain ⟨hv1, h1⟩ := face_of_typeMap_eq_some C.proj (C.typeMap_proj hM hp)
  obtain ⟨hv2, h2⟩ := face_of_typeMap_eq_some Fin.castSuccEmb hroot
  have hSR : C.p₀.scheme.restrictFace C.proj hvX = P.scheme.restrictFace Fin.castSuccEmb hvY :=
    h1.trans h2.symm
  exact sharedRootRows_of_eq hvX hvY hroot' _ _ rfl rfl hvX hvY hSR HEq.rfl HEq.rfl

end Actual

/-! ## The collision obstruction at a mixed index -/

section Collision

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- **Locality identifies what the row identifies**: under any respecting labelling, two lower
cells of the same grade at which the row of `Sig` reads the same value carry the same label
below the cap `r Sig`. -/
theorem RespectsSemanticsBelow.capped_eq_of_row_eq {sem : Semantics D} {BJ : Finset ι × ℕ}
    {r : D.below BJ → ExtOrd} (h : RespectsSemanticsBelow sem BJ r) (Sig : D.below BJ)
    (d₁ d₂ : D.below (D.cell Sig.1)) (hrow : sem.E Sig.1 d₁ = sem.E Sig.1 d₂)
    (hgr : D.grade d₁.1 = D.grade d₂.1) :
    min (r (CellScheme.below.incl Sig d₁)) (r Sig) =
      min (r (CellScheme.below.incl Sig d₂)) (r Sig) :=
  h.probe_eq_of_row_eq Sig d₁ d₂ hrow hgr

/-- **The diagonal candidate identifies equal diagonals**: with the diagonal row at `M`, every
respecting labelling of the lower set of `M` agrees below the cap `r M` at two lower cells of
the same grade whose diagonals coincide.  A prescribed pair of face labellings separating such
cells (up to the cap) has no respecting extension with that row at `M`. -/
theorem diagonal_row_identifies {sem : Semantics D} (M : Cell D)
    (hM : ∀ d : D.below (D.cell M), sem.E M d = sem.diagonal d.1)
    {r : D.below (D.cell M) → ExtOrd} (hr : RespectsSemanticsBelow sem (D.cell M) r)
    (d₁ d₂ : D.below (D.cell M)) (hdiag : sem.diagonal d₁.1 = sem.diagonal d₂.1)
    (hgr : D.grade d₁.1 = D.grade d₂.1) :
    min (r d₁) (r ⟨M, GradedLe.refl _⟩) = min (r d₂) (r ⟨M, GradedLe.refl _⟩) := by
  have := hr.capped_eq_of_row_eq ⟨M, GradedLe.refl _⟩ d₁ d₂ (by rw [hM, hM, hdiag]) hgr
  exact this

end Collision

/-! ## The instance on the coupled construction -/

section Instance

/-- The diagonals of `H₀old` and `H₀new` coincide in the repaired semantics: both cells retract
to the same cell of the three-cell family. -/
theorem diagonal_H₀old_eq_H₀new : rowsR.diagonal H₀old = rowsR.diagonal H₀new := by
  have hA : AFace H₀old := aFace_castAdd _
  have hB : BFace H₀new := copyB_mem _
  have h1 : rowsR.diagonal H₀old = family₂.rowX H₀X H₀X := by
    unfold Semantics.diagonal
    rw [rowsR_E_of_A hA ⟨H₀old, GradedLe.refl _⟩,
      rows₂_E_eq_pull not_mute_H₀old ⟨H₀old, GradedLe.refl _⟩,
      pull_of_not_mute _ not_mute_H₀old, ret₂_H₀old, Equiv.symm_apply_apply]
  have h2 : rowsR.diagonal H₀new = family₂.rowX H₀X H₀X := by
    unfold Semantics.diagonal
    rw [rowsR_E_of_B hB ⟨H₀new, GradedLe.refl _⟩,
      rows₂_E_eq_pull not_mute_H₀new ⟨H₀new, GradedLe.refl _⟩,
      pull_of_not_mute _ not_mute_H₀new, ret₂_H₀new, Equiv.symm_apply_apply]
  exact h1.trans h2.symm

/-- **No realization of the prescribed pair from equal `H₀` readings**: a semantics on the glued
scheme whose full-scope controllers read the same value at `H₀old` and at `H₀new` — the
diagonal candidate in particular — admits no respecting labelling of `(univ, 3)` realizing the
prescribed pair.  The collision at the smallest mixed index. -/
theorem no_realization_of_equal_H₀_rows (sem : Semantics D₂)
    (hrows : ∀ (U : Cell D₂) (hA : GradedLe (D₂.cell H₀old) (D₂.cell U))
      (hB : GradedLe (D₂.cell H₀new) (D₂.cell U)), sem.E U ⟨H₀old, hA⟩ = sem.E U ⟨H₀new, hB⟩)
    {q : D₂.below (Finset.univ, 3) → ExtOrd}
    (hq : RespectsSemanticsBelow sem (Finset.univ, 3) q) : ¬ RealizesPair q := by
  intro hpair
  obtain ⟨U, hA, hB, -, -, hlt⟩ := separating_controllers_of_realizes hq hpair 1 (by decide)
  exact absurd (hrows U.1 hA hB) (ne_of_lt hlt)

/-- The diagonal candidate on the glued scheme reads equal values at the two `H₀` cells. -/
theorem diagonal_candidate_equal_H₀ (sem : Semantics D₂)
    (hdiag : ∀ (U : Cell D₂) (d : D₂.below (D₂.cell U)), sem.E U d = rowsR.diagonal d.1)
    (U : Cell D₂) (hA : GradedLe (D₂.cell H₀old) (D₂.cell U))
    (hB : GradedLe (D₂.cell H₀new) (D₂.cell U)) :
    sem.E U ⟨H₀old, hA⟩ = sem.E U ⟨H₀new, hB⟩ := by
  rw [hdiag U ⟨H₀old, hA⟩, hdiag U ⟨H₀new, hB⟩]
  exact diagonal_H₀old_eq_H₀new

end Instance

end VaughtConjecture.Knight
