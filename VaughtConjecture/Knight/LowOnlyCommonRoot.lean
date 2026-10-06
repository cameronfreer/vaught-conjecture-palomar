/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyCompleteFields
public import VaughtConjecture.Knight.PartialSections

/-! # Literal common-root transport for the gate-free LOW family

The input records occurrence and row identities, not a supplied repair or a
lawfulness-transport conclusion. The latter and opposite-face installation are
derived from those identities and the two original schemes' bountifulness.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd AmalgamationPlan CappedDonor

variable {n : ℕ} {P C : SemScheme n}

/-- The complete common root, with exact original source rows. -/
structure CommonRoot (P C : SemScheme n) where
  A : Finset (Fin n)
  B : Finset (Fin n)
  A_mem : A ∈ P.scheme.plan
  B_mem : B ∈ C.scheme.plan
  card : A.card = B.card
  face : P.scheme.below (A, A.card) ≃ C.scheme.below (B, B.card)
  grade : ∀ a, P.scheme.grade a.1 = C.scheme.grade (face a).1
  scope : ∀ a b, P.scheme.scope a.1 ⊆ P.scheme.scope b.1 ↔
    C.scheme.scope (face a).1 ⊆ C.scheme.scope (face b).1
  row : ∀ (a : P.scheme.below (A, A.card))
    (d : P.scheme.below (P.scheme.cell a.1))
    (hd : GradedLe (C.scheme.cell (face ⟨d.1, d.2.trans a.2⟩).1)
      (C.scheme.cell (face a).1)),
    P.rows.E a.1 d = C.rows.E (face a).1 ⟨(face ⟨d.1, d.2.trans a.2⟩).1, hd⟩

namespace CommonRoot

variable (R : CommonRoot P C)

def fullP {j : ℕ} (a : P.scheme.below (faceIndex R.A j)) :
    P.scheme.below (R.A, R.A.card) :=
  ⟨a.1, a.2.1, a.2.2.trans (min_le_left _ _)⟩

def fullC {j : ℕ} (a : C.scheme.below (faceIndex R.B j)) :
    C.scheme.below (R.B, R.B.card) :=
  ⟨a.1, a.2.1, a.2.2.trans (min_le_left _ _)⟩

def faceAt (j : ℕ) : P.scheme.below (faceIndex R.A j) ≃
    C.scheme.below (faceIndex R.B j) where
  toFun a := ⟨(R.face (R.fullP a)).1, (R.face (R.fullP a)).2.1,
    le_min (R.face (R.fullP a)).2.2
      ((R.grade (R.fullP a)).symm.trans_le (a.2.2.trans (min_le_right _ _)))⟩
  invFun a := ⟨(R.face.symm (R.fullC a)).1, (R.face.symm (R.fullC a)).2.1,
    le_min (R.face.symm (R.fullC a)).2.2 (by
      have hg := R.grade (R.face.symm (R.fullC a))
      rw [Equiv.apply_symm_apply] at hg
      exact hg.trans_le (a.2.2.trans (min_le_right _ _)))⟩
  left_inv a := by
    apply Subtype.ext
    change (R.face.symm (R.face (R.fullP a))).1 = a.1
    exact congrArg Subtype.val (R.face.symm_apply_apply (R.fullP a))
  right_inv a := by
    apply Subtype.ext
    change (R.face (R.face.symm (R.fullC a))).1 = a.1
    exact congrArg Subtype.val (R.face.apply_symm_apply (R.fullC a))

theorem at_grade {j : ℕ} (a : P.scheme.below (faceIndex R.A j)) :
    P.scheme.grade a.1 = C.scheme.grade (R.faceAt j a).1 := R.grade (R.fullP a)

/-- Lawfulness transport is proved from every actual row identity. -/
theorem respects_iff {j : ℕ} (v : C.scheme.below (faceIndex R.B j) → ExtOrd) :
    RespectsSemanticsBelow C.rows (faceIndex R.B j) v ↔
      RespectsSemanticsBelow P.rows (faceIndex R.A j) (fun a => v (R.faceAt j a)) := by
  have h := respects_iff_of_equiv (sem' := P.rows) (sem := C.rows) (R.faceAt j)
    R.at_grade (fun a b => R.scope (R.fullP a) (R.fullP b))
    (fun a d hd => R.row (R.fullP a) d hd) (fun a => v (R.faceAt j a))
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h.symm

def Shared (u : Cell P.scheme → ExtOrd) (v : Cell C.scheme → ExtOrd) : Prop :=
  ∀ a, u a.1 = v (R.face a).1

theorem shared_at {u : Cell P.scheme → ExtOrd} {v : Cell C.scheme → ExtOrd}
    (h : R.Shared u v) {j : ℕ} (a : P.scheme.below (faceIndex R.A j)) :
    u a.1 = v (R.faceAt j a).1 := h (R.fullP a)

/-- Installing the present vector keeps the entire common root, including its future part. -/
theorem shared_complete {j : ℕ} {u : Cell P.scheme → ExtOrd} {v : Cell C.scheme → ExtOrd}
    (h : R.Shared u v) (u' : P.scheme.below (effC n j) → ExtOrd)
    (v' : C.scheme.below (effC n j) → ExtOrd)
    (hface : ∀ a : P.scheme.below (faceIndex R.A j),
      u' (CellScheme.below.mono (faceIndex_le R.A j) a) =
        v' (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a))) :
    R.Shared (completeAt u u') (completeAt v v') := by
  intro a
  by_cases hj : P.scheme.grade a.1 ≤ j
  · let a' : P.scheme.below (faceIndex R.A j) := ⟨a.1, a.2.1, le_min a.2.2 hj⟩
    exact (completeAt_present u u' (CellScheme.below.mono (faceIndex_le R.A j) a')).trans
      ((hface a').trans
        (completeAt_present v v' (CellScheme.below.mono (faceIndex_le R.B j)
          (R.faceAt j a'))).symm)
  · rw [completeAt_future u u' a.1 (not_le.mp hj),
      completeAt_future v v' (R.face a).1 (by rw [← R.grade]; exact not_le.mp hj)]
    exact h a

/-- Prescribe the private root in the original donor, preserving all donor caps.
Empty roots and nominal grade zero need no bountifulness call. -/
theorem installP {j : ℕ} {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v)
    {γ : ExtOrd} (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ a : P.scheme.below (faceIndex R.A j),
      min (u (CellScheme.below.mono (faceIndex_le R.A j) a)) γ =
        min (v (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a))) γ) :
    ∃ u', RespectsSemanticsBelow P.rows (effC n j) u' ∧
      (∀ d, min (u' d) γ = min (u d) γ) ∧
      ∀ a : P.scheme.below (faceIndex R.A j),
        u' (CellScheme.below.mono (faceIndex_le R.A j) a) =
          v (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a)) := by
  by_cases hk : 0 < min R.A.card j
  · exact P.bountiful.extend (faceIndex_mem R.A_mem hk)
      (effC_mem (hk.trans_le (min_le_right _ _))
        ((hk.trans_le (min_le_left _ _)).trans_le (by simpa using Finset.card_le_univ R.A)))
      (faceIndex_le R.A j) ((R.respects_iff _).mp (hv.mono (faceIndex_le R.B j)))
      hu hγ hag
  · exact ⟨u, hu, fun _ => rfl, fun a => (faceIndex_absent hk a).elim⟩

/-- The reverse original-face installation uses the inverse actual root map. -/
theorem installC {j : ℕ} {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v)
    {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u)
    {γ : ExtOrd} (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ a : P.scheme.below (faceIndex R.A j),
      min (v (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a))) γ =
        min (u (CellScheme.below.mono (faceIndex_le R.A j) a)) γ) :
    ∃ v', RespectsSemanticsBelow C.rows (effC n j) v' ∧
      (∀ d, min (v' d) γ = min (v d) γ) ∧
      ∀ a : P.scheme.below (faceIndex R.A j),
        v' (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a)) =
          u (CellScheme.below.mono (faceIndex_le R.A j) a) := by
  by_cases hk : 0 < min R.B.card j
  · have hlaw : RespectsSemanticsBelow C.rows (faceIndex R.B j)
        (fun a => u (CellScheme.below.mono (faceIndex_le R.A j) ((R.faceAt j).symm a))) := by
      apply (R.respects_iff _).mpr
      simpa only [Equiv.symm_apply_apply] using hu.mono (faceIndex_le R.A j)
    obtain ⟨v', hv', hcap, hface⟩ := C.bountiful.extend (faceIndex_mem R.B_mem hk)
      (effC_mem (hk.trans_le (min_le_right _ _))
        ((hk.trans_le (min_le_left _ _)).trans_le (by simpa using Finset.card_le_univ R.B)))
      (faceIndex_le R.B j) hlaw hv hγ (fun a => by
        simpa only [Equiv.apply_symm_apply] using hag ((R.faceAt j).symm a))
    exact ⟨v', hv', hcap, fun a => by simpa using hface (R.faceAt j a)⟩
  · exact ⟨v, hv, fun _ => rfl, fun a => (faceIndex_absent hk (R.faceAt j a)).elim⟩

end CommonRoot
end VaughtConjecture.Knight.LowOnly
