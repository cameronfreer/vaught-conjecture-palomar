/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Domain

/-! # One-point extension of a cell scheme with an explicit plan and explicit new cells

`CellScheme.extendOne` (`Knight/Domain.lean`) chooses the extended plan (`Plan.extendOnePlan`) and
takes one new cell per new graded pair.  A comparison context needs both to be **explicit**: the
plan is prescribed (the two-copy plan on `Fin 4` in `Knight/FourPointDuplication.lean`), and the new
cells are prescribed data (the copies of the old cells).  `CellScheme.extendOneWith` is the same
construction with the plan `Q` and the finite type of new cells `N` as parameters; the face equation
(`restrictFace_extendOneWith`) and completeness (`IsComplete.extendOneWith`) are the repository
proofs with the two chosen facts replaced by the hypotheses `hface` (the plan's face equation) and
`hnew` (every new graded pair has a new cell).  Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

namespace CellScheme

variable {n : ℕ} (C : CellScheme (ι := Fin n) Finset.univ)
  (Q : Finset (Finset (Fin (n + 1)))) (hQ : Plan.IsPlan Finset.univ Q)
  (hface : ∀ B : Finset (Fin n), B.image Fin.castSuccEmb ∈ Q ↔ B ∈ C.plan)
  {N : Type*} [Fintype N] (newCell : N → Finset (Fin (n + 1)) × ℕ)
  (hnew_mem : ∀ x, newCell x ∈ Plan.gradedPlan Q)
  (hnew_last : ∀ x, Fin.last n ∈ (newCell x).1)

/-- **One-point extension with an explicit plan and explicit new cells**: the old cells with
their scopes pushed along `castSucc` (indices `Fin.castAdd`), then the new cells (indices
`Fin.natAdd`, enumerated by `Fintype.equivFin`). -/
noncomputable def extendOneWith : CellScheme (ι := Fin (n + 1)) Finset.univ where
  plan := Q
  isPlan := hQ
  card := C.card + Fintype.card N
  cell := Fin.append (fun i => pushGraded Fin.castSuccEmb (C.cell i))
    (fun j => newCell ((Fintype.equivFin N).symm j))
  cell_mem i := by
    induction i using Fin.addCases with
    | left i =>
      rw [Fin.append_left]
      have h := Plan.mem_gradedPlan.mp (C.cell_mem i)
      refine Plan.mem_gradedPlan.mpr ⟨?_, h.2.1, ?_⟩
      · exact (hface _).mpr h.1
      · change (C.cell i).2 ≤ ((C.cell i).1.image Fin.castSuccEmb).card
        rw [Finset.card_image_of_injective _ Fin.castSuccEmb.injective]
        exact h.2.2
    | right j =>
      rw [Fin.append_right]
      exact hnew_mem _

variable {C Q hQ hface newCell hnew_mem}

section Lemmas

theorem extendOneWith_plan : (extendOneWith C Q hQ hface newCell hnew_mem).plan = Q := rfl

theorem extendOneWith_card :
    (extendOneWith C Q hQ hface newCell hnew_mem).card = C.card + Fintype.card N := rfl

/-- The initial segment is a visible face. -/
theorem extendOneWith_visible :
    Finset.univ.image Fin.castSuccEmb ∈ (extendOneWith C Q hQ hface newCell hnew_mem).plan :=
  (hface _).mpr C.isPlan.domain_mem

@[simp] theorem extendOneWith_cell_castAdd (i : Cell C) :
    (extendOneWith C Q hQ hface newCell hnew_mem).cell (Fin.castAdd (Fintype.card N) i) =
      pushGraded Fin.castSuccEmb (C.cell i) :=
  Fin.append_left (fun i => pushGraded Fin.castSuccEmb (C.cell i))
    (fun j => newCell ((Fintype.equivFin N).symm j)) i

@[simp] theorem extendOneWith_scope_castAdd (i : Cell C) :
    (extendOneWith C Q hQ hface newCell hnew_mem).scope (Fin.castAdd (Fintype.card N) i) =
      (C.scope i).image Fin.castSuccEmb :=
  congrArg Prod.fst (extendOneWith_cell_castAdd i)

@[simp] theorem extendOneWith_grade_castAdd (i : Cell C) :
    (extendOneWith C Q hQ hface newCell hnew_mem).grade (Fin.castAdd (Fintype.card N) i) =
      C.grade i :=
  congrArg Prod.snd (extendOneWith_cell_castAdd i)

@[simp] theorem extendOneWith_cell_natAdd (j : Fin (Fintype.card N)) :
    (extendOneWith C Q hQ hface newCell hnew_mem).cell (Fin.natAdd C.card j) =
      newCell ((Fintype.equivFin N).symm j) :=
  Fin.append_right (fun i => pushGraded Fin.castSuccEmb (C.cell i))
    (fun j => newCell ((Fintype.equivFin N).symm j)) j

/-- Every new cell sees the new point. -/
theorem last_mem_extendOneWith_scope_natAdd (hnew_last : ∀ x, Fin.last n ∈ (newCell x).1)
    (j : Fin (Fintype.card N)) :
    Fin.last n ∈ (extendOneWith C Q hQ hface newCell hnew_mem).scope (Fin.natAdd C.card j) := by
  change Fin.last n ∈ ((extendOneWith C Q hQ hface newCell hnew_mem).cell (Fin.natAdd C.card j)).1
  rw [extendOneWith_cell_natAdd]
  exact hnew_last _

/-- The cells visible through the initial face are exactly the old cells. -/
theorem extendOneWith_scope_subset_iff (hnew_last : ∀ x, Fin.last n ∈ (newCell x).1)
    (d : Cell (extendOneWith C Q hQ hface newCell hnew_mem)) :
    (extendOneWith C Q hQ hface newCell hnew_mem).scope d ⊆ Finset.univ.image Fin.castSuccEmb ↔
      ∃ i, Fin.castAdd (Fintype.card N) i = d := by
  induction d using Fin.addCases with
  | left i =>
    refine ⟨fun _ => ⟨i, rfl⟩, fun _ => ?_⟩
    rw [extendOneWith_scope_castAdd]
    exact Finset.image_subset_image (Finset.subset_univ _)
  | right j =>
    refine ⟨fun h => ?_, fun ⟨i, hi⟩ => ?_⟩
    · have := h (last_mem_extendOneWith_scope_natAdd hnew_last j)
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Fin.coe_castSuccEmb] at this
      obtain ⟨i, hi⟩ := this
      exact absurd hi (Fin.castSucc_ne_last i)
    · exact absurd hi (Fin.ne_of_val_ne (by simp [Fin.castAdd, Fin.natAdd]; omega))

/-- Pulling an old cell back along the initial face recovers its graded index. -/
theorem pullCell_extendOneWith_castAdd (i : Cell C) :
    (extendOneWith C Q hQ hface newCell hnew_mem).pullCell Fin.castSuccEmb
      (Fin.castAdd (Fintype.card N) i) = C.cell i := by
  unfold pullCell
  refine Prod.ext ?_ (extendOneWith_grade_castAdd i)
  ext x
  simp [extendOneWith_scope_castAdd]

/-- **The face equation**: the face restriction along the initial segment is `C`. -/
theorem restrictFace_extendOneWith (hnew_last : ∀ x, Fin.last n ∈ (newCell x).1) :
    (extendOneWith C Q hQ hface newCell hnew_mem).restrictFace Fin.castSuccEmb
      extendOneWith_visible = C := by
  set E := extendOneWith C Q hQ hface newCell hnew_mem with hE
  have hvis : ∀ c, E.scope (Fin.castAdd (Fintype.card N) c) ⊆ Finset.univ.image Fin.castSuccEmb :=
    fun c => (extendOneWith_scope_subset_iff hnew_last _).mpr ⟨c, rfl⟩
  have hsurj : ∀ d, E.scope d ⊆ Finset.univ.image Fin.castSuccEmb →
      ∃ c, Fin.castAdd (Fintype.card N) c = d :=
    fun d hd => (extendOneWith_scope_subset_iff hnew_last d).mp hd
  have hcard : (E.restrictFace Fin.castSuccEmb extendOneWith_visible).card = C.card :=
    restrictFace.card_restrictFace_of_emb _ _ _ (Fin.strictMono_castAdd _) hvis hsurj
  refine ext_of_components ?_ hcard fun i => ?_
  · ext B
    simp only [restrictFace_plan, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
      true_and, extendOneWith_plan, hface]
  · rw [restrictFace.cell_eq, restrictFace.toCell_cast_eq_of_emb E Fin.castSuccEmb
      extendOneWith_visible (e := Fin.castAdd (Fintype.card N)) (Fin.strictMono_castAdd _) hvis
      hcard, pullCell_extendOneWith_castAdd]

/-- **Completeness** of the extension, given a new cell at every new graded pair. -/
theorem IsComplete.extendOneWith (hC : C.IsComplete)
    (hnew : ∀ BJ ∈ Plan.gradedPlan Q, Fin.last n ∈ BJ.1 → ∃ x, newCell x = BJ) :
    (extendOneWith C Q hQ hface newCell hnew_mem).IsComplete := by
  intro BJ hBJ
  by_cases hlast : Fin.last n ∈ BJ.1
  · obtain ⟨x, hx⟩ := hnew BJ hBJ hlast
    refine ⟨Fin.natAdd C.card (Fintype.equivFin N x), ?_⟩
    rw [extendOneWith_cell_natAdd, Equiv.symm_apply_apply, hx]
  · set C₀ : Finset (Fin n) := Finset.univ.filter (fun x => Fin.castSucc x ∈ BJ.1) with hC₀
    have himg : C₀.image Fin.castSuccEmb = BJ.1 := by
      ext y
      simp only [Finset.mem_image, hC₀, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.coe_castSuccEmb]
      refine ⟨fun ⟨x, hx, hxy⟩ => hxy ▸ hx, fun hy => ?_⟩
      rcases Fin.eq_castSucc_or_eq_last y with ⟨x, rfl⟩ | rfl
      · exact ⟨x, hy, rfl⟩
      · exact absurd hy hlast
    have h := Plan.mem_gradedPlan.mp hBJ
    have hmem : (C₀, BJ.2) ∈ Plan.gradedPlan C.plan := by
      refine Plan.mem_gradedPlan.mpr ⟨?_, h.2.1, ?_⟩
      · exact (hface C₀).mp (by rw [himg]; exact h.1)
      · change BJ.2 ≤ C₀.card
        rw [← Finset.card_image_of_injective C₀ Fin.castSuccEmb.injective, himg]
        exact h.2.2
    obtain ⟨d, hd⟩ := hC _ hmem
    refine ⟨Fin.castAdd (Fintype.card N) d, ?_⟩
    rw [extendOneWith_cell_castAdd, hd]
    exact Prod.ext himg rfl

end Lemmas

end CellScheme

end VaughtConjecture.Knight
