/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedProjection

/-! # Replicated growth occurrences and their capped readings

Common occurrence maps, grade bounds and projection identities, before either
positive-cap correctness or the top-cap readback specialization. Names and
proofs remain in the historical namespace for compatibility.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GrowthReplicatedReadback

open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources GrowthHigherMixed
open GrowthPaddedContract GrowthPaddedIteration

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (t : ℕ) (ht : t + 2 ≤ A.card)

local notation "P" => GrowthHigherMixed.tower I X T hA hB hC t ht
local notation "D" => GrowthHigherMixed.carrier I X T hA hB hC t ht
local notation "Rows" => GrowthHigherMixed.rows I X T hA hB hC t ht

/-! ## Original occurrences inside the observed section -/

/-- The boundary index of a placed private cell. -/
theorem private_cell (d : Cell I.right.scheme) :
    I.boundary.cell (I.rightFace.map d) =
      ((I.right.scheme.scope d).image I.placeRight, I.right.scheme.grade d) :=
  I.rightFace.index d

/-- The boundary index of a placed donor cell. -/
theorem donor_cell (d : Cell I.left.scheme) :
    I.boundary.cell (I.leftFace.map d) =
      ((I.left.scheme.scope d).image I.placeLeft, I.left.scheme.grade d) :=
  I.leftFace.index d

theorem private_scope_le (d : Cell I.right.scheme) :
    (I.right.scheme.scope d).image I.placeRight ⊆ C := by
  exact (Finset.image_subset_image (Finset.subset_univ _)).trans (Finset.subset_of_eq I.imageRight)

theorem donor_scope_le (d : Cell I.left.scheme) :
    (I.left.scheme.scope d).image I.placeLeft ⊆ B := by
  exact (Finset.image_subset_image (Finset.subset_univ _)).trans (Finset.subset_of_eq I.imageLeft)

variable (U : Finset ι) (j : ℕ)

/-- An original boundary cell as an occurrence of the observed section: the inherited cell
of the replicated carrier, not a copy. -/
def originalAt (d : Cell I.boundary) (hd : GradedLe (I.boundary.cell d) (U, j)) :
    CellScheme.below (carrier I X T hA hB hC t ht) (U, j) :=
  ScopeReplicationCarrier.oldBelow (P).carrier B C (U, j)
    ⟨original I X T hA hB hC t ht d, by rw [original_index]; exact hd⟩

theorem erase_originalAt (d : Cell I.boundary) (hd : GradedLe (I.boundary.cell d) (U, j)) :
    erase I X T hA hB hC t ht (originalAt I X T hA hB hC t ht U j d hd).1 =
      original I X T hA hB hC t ht d :=
  ScopeReplicationCarrier.erase_old (P).carrier B C _

variable (hBU : B ⊆ U) (hCU : C ⊆ U)

/-- The occurrence of a private original of grade at most `j`. -/
def privateAt (d : Cell I.right.scheme) (hd : I.right.scheme.grade d ≤ j) :
    CellScheme.below (carrier I X T hA hB hC t ht) (U, j) :=
  originalAt I X T hA hB hC t ht U j (I.rightFace.map d)
    (by rw [private_cell]; exact ⟨(private_scope_le I d).trans hCU, hd⟩)

/-- The occurrence of a donor original of grade at most `j`. -/
def donorAt (d : Cell I.left.scheme) (hd : I.left.scheme.grade d ≤ j) :
    CellScheme.below (carrier I X T hA hB hC t ht) (U, j) :=
  originalAt I X T hA hB hC t ht U j (I.leftFace.map d)
    (by rw [donor_cell]; exact ⟨(donor_scope_le I d).trans hBU, hd⟩)

/-! ## Readback through the whole-boundary projection -/

variable (hU : U ∈ R) (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (hj : j ≤ U.card) (hj0 : 1 ≤ j) (hjt : j ≤ t + 2)
  {p : CellScheme.below (carrier I X T hA hB hC t ht) (U, j) → ExtOrd}

include hjt in
/-- A private original reads its complete field capped at the height of its own grade. -/
theorem private_readback (hp : RespectsSemanticsBelow Rows (U, j) p)
    (d : Cell I.right.scheme) (hd : I.right.scheme.grade d ≤ j) :
    p (privateAt I X T hA hB hC t ht U j hCU d hd) =
      min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p
        (GrowthOrderedBase.field I (I.rightFace.map d)))
        (height I X T hA hB hC t ht U j p (I.right.scheme.grade d)) := by
  have h := projection_readback I X T hA hB hC t ht U hU hm j hj hj0 hp hjt
    (privateAt I X T hA hB hC t ht U j hCU d hd) (I.rightFace.map d)
    (erase_originalAt I X T hA hB hC t ht U j _ _)
  rwa [show I.boundary.grade (I.rightFace.map d) = I.right.scheme.grade d from
    congrArg Prod.snd (private_cell I d)] at h

include hjt in
/-- A donor original reads its complete field capped at the height of its own grade. -/
theorem donor_readback_height (hp : RespectsSemanticsBelow Rows (U, j) p)
    (d : Cell I.left.scheme) (hd : I.left.scheme.grade d ≤ j) :
    p (donorAt I X T hA hB hC t ht U j hBU d hd) =
      min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p
        (GrowthOrderedBase.field I (I.leftFace.map d)))
        (height I X T hA hB hC t ht U j p (I.left.scheme.grade d)) := by
  have h := projection_readback I X T hA hB hC t ht U hU hm j hj hj0 hp hjt
    (donorAt I X T hA hB hC t ht U j hBU d hd) (I.leftFace.map d)
    (erase_originalAt I X T hA hB hC t ht U j _ _)
  rwa [show I.boundary.grade (I.leftFace.map d) = I.left.scheme.grade d from
    congrArg Prod.snd (donor_cell I d)] at h

variable (hN : X.req.N ≤ j)

include hN in
/-- The private cap's grade is the activation grade, so its occurrence is observed. -/
theorem cap_grade_le : I.right.scheme.grade X.req.C ≤ j := X.grade_C.trans_le hN

/-- Every donor cell has grade at most the activation grade. -/
theorem donor_grade_le (d : Cell I.left.scheme) : I.left.scheme.grade d ≤ X.req.N :=
  (X.below_top d).2.trans X.top_le_N

/-- The grade bound of a private cell below the cap. -/
theorem grade_le_of_below_cap (d : I.right.scheme.below (I.right.scheme.cell X.req.C)) :
    I.right.scheme.grade d.1 ≤ X.req.N :=
  d.2.2.trans_eq X.grade_C

include I X T hA hB hC t ht in
theorem A_mem : A ∈ R := by
  have h := GrowthMixedGradeOne.A_mem_plan I X T hA hB hC (P)
  rwa [GrowthPaddedIteration.build_plan] at h

include hC in
/-- The activation grade is the actual cap's grade, bounded by the private arity. -/
theorem threshold_le_card : X.req.N ≤ A.card := by
  have hg := I.right.scheme.grade_le_card_scope X.req.C
  rw [X.grade_C] at hg
  have h1 := Finset.card_le_card (Finset.subset_univ (I.right.scheme.scope X.req.C))
  have h2 : (Finset.univ : Finset (Fin J)).card = C.card := by
    rw [← I.imageRight, Finset.card_image_of_injective _ I.placeRight.injective]
  have h3 := Finset.card_le_card (Finset.ssubset_iff_subset_ne.mp hC).1
  omega

/-- The installed private occurrence map is the inherited original occurrence. -/
theorem privateFace_map (d : Cell I.right.scheme) (hd : I.right.scheme.grade d ≤ A.card) :
    (GrowthReplicatedRows.privateFace I X T hA hB hC t ht).map d =
      (privateAt I X T hA hB hC t ht A A.card (Finset.ssubset_iff_subset_ne.mp hC).1 d hd).1 := by
  exact congrArg (ScopeReplicationCarrier.old (P).carrier B C)
    (GrowthPaddedInstallation.face_map I X T hA hB hC I.rightFace hC.not_ge t ht d)

/-- The installed donor occurrence map is the inherited original occurrence. -/
theorem donorFace_map (d : Cell I.left.scheme) (hd : I.left.scheme.grade d ≤ A.card) :
    (GrowthReplicatedRows.donorFace I X T hA hB hC t ht).map d =
      (donorAt I X T hA hB hC t ht A A.card (Finset.ssubset_iff_subset_ne.mp hB).1 d hd).1 := by
  exact congrArg (ScopeReplicationCarrier.old (P).carrier B C)
    (GrowthPaddedInstallation.face_map I X T hA hB hC I.leftFace hB.not_ge t ht d)

end
end VaughtConjecture.Knight.GrowthReplicatedReadback
