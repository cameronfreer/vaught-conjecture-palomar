/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthScalarLedger
public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.RelativeLadderRankRendering

/-! # The growth catalogue on the actual ordered padded boundary

The donor and private arities may differ. Only grade-one original occurrences
are read by the new rows; all future fields remain in the anchor's complete
rank table. Boundary lawfulness is derived from the literal root attachment.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthOrderedBase
open Transform Value ExtOrd AmalgamationPlan Growth RelativeLadderLayer
noncomputable section

private theorem faceMap_eq {m n : ℕ} (D : SemScheme n) (F : SemScheme m)
    (f : Fin m ↪ Fin n) (hv : Finset.univ.image f ∈ D.scheme.plan)
    (hf : D.restrictFace f hv = F) (d : Cell F.scheme) :
    SemSchemeBoundaryInput.faceMap D F f hv hf d =
      CellScheme.restrictFace.toCell D.scheme f hv (SemScheme.castCell hf.symm d) := by
  subst F
  rfl

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)

def field (d : Cell I.boundary) : Field I.right.scheme I.left.scheme :=
  match (OrderedFaceBoundary.enumeration I.leftScheme I.rightScheme I.shared).symm d with
  | .inl c => .inr c
  | .inr c => .inl c.1

theorem field_read (S : State I.right.scheme I.left.scheme) (d : Cell I.boundary) :
    S.profile (field I d) = I.paste S.donorValues S.privateValues d := by
  unfold field WholeDonorBoundary.Input.paste OrderedFaceBoundarySemantics.paste
  change S.profile (match (OrderedFaceBoundary.enumeration
      I.leftScheme I.rightScheme I.shared).symm d with
    | .inl c => .inr c | .inr c => .inl c.1) =
    ProfileFaceUnion.paste I.shared.g S.donorValues S.privateValues
      ((OrderedFaceBoundary.enumeration I.leftScheme I.rightScheme I.shared).symm d)
  cases (OrderedFaceBoundary.enumeration I.leftScheme I.rightScheme I.shared).symm d <;> rfl

include T in
theorem shared {j : ℕ} {S : State I.right.scheme I.left.scheme} (hs : Admitted X j S)
    (d : Cell I.common.scheme) :
    S.donorValues (I.shared.f d) = S.privateValues (I.shared.g d) := by
  let d' : I.common.scheme.below (Finset.univ, m) :=
    ⟨d, Finset.subset_univ _, by
      have hd := I.common.scheme.grade_le_card_scope d
      have hc := Finset.card_le_univ (I.common.scheme.scope d)
      have hc' : (I.common.scheme.scope d).card ≤ m := by simpa using hc
      exact hd.trans hc'⟩
  let a : I.left.scheme.below (Finset.univ.image I.commonLeft, m) :=
    CappedDonor.bP I.commonLeft I.visibleLeft m
      (CappedDonor.castBelow I.faceLeft.symm (Finset.univ, m) d')
  have ha : a.1 = I.shared.f d := by
    change CellScheme.restrictFace.toCell _ _ _
      (CappedDonor.castBelow I.faceLeft.symm (Finset.univ, m) _).1 = _
    erw [CappedDonor.castBelow_val]
    exact (faceMap_eq _ _ _ _ _ d).symm
  have hb : (rootMap I.common I.commonLeft I.visibleLeft I.faceLeft
      I.commonRight I.visibleRight I.faceRight m a).1 = I.shared.g d := by
    erw [CappedDonor.commonFace_apply]
    have he : (CappedDonor.bP I.commonLeft I.visibleLeft m).symm a =
        CappedDonor.castBelow I.faceLeft.symm (Finset.univ, m) d' :=
      Equiv.symm_apply_apply _ _
    rw [he, CappedDonor.castBelow_castBelow_symm]
    change CellScheme.restrictFace.toCell _ _ _
      (CappedDonor.castBelow I.faceRight.symm (Finset.univ, m) _).1 = _
    erw [CappedDonor.castBelow_val]
    exact (faceMap_eq _ _ _ _ _ d).symm
  have he := hs.shared (T.full a)
  change S.donorValues a.1 = S.privateValues (X.κ (T.full a)).1 at he
  rw [← T.at_occurrence a, ha, hb] at he
  exact he

theorem field_donor (S : State I.right.scheme I.left.scheme) (d : Cell I.left.scheme) :
    S.profile (field I (I.leftFace.map d)) = S.donorValues d :=
  (field_read I S _).trans (I.paste_left _ _ d)

include T in
theorem field_private {j : ℕ} {S : State I.right.scheme I.left.scheme}
    (hs : Admitted X j S) (d : Cell I.right.scheme) :
    S.profile (field I (I.rightFace.map d)) = S.privateValues d :=
  (field_read I S _).trans (I.paste_right _ _ (shared I X T hs) d)

theorem proper (hB : B ⊂ A) (hC : C ⊂ A) (d : Cell I.boundary) :
    I.boundary.scope d ≠ A := by
  rcases OrderedFaceBoundaryRows.covered I.leftScheme I.rightScheme I.shared R I.isPlan
      I.leftPlan_le I.rightPlan_le d with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · have hs := I.leftScheme.isPlan.subset_of_mem (I.leftScheme.scope_mem_plan d)
    change I.boundary.scope (I.leftFace.map d) ≠ A
    rw [show I.boundary.scope (I.leftFace.map d) = I.leftScheme.scope d from
      congrArg Prod.fst (I.leftFace.index d)]
    exact fun he => hB.not_ge (he ▸ hs)
  · have hs := I.rightScheme.isPlan.subset_of_mem (I.rightScheme.scope_mem_plan d)
    change I.boundary.scope (I.rightFace.map d) ≠ A
    rw [show I.boundary.scope (I.rightFace.map d) = I.rightScheme.scope d from
      congrArg Prod.fst (I.rightFace.index d)]
    exact fun he => hC.not_ge (he ▸ hs)

include T in
theorem boundary_lawful {S : State I.right.scheme I.left.scheme} (hs : Admitted X 1 S) :
    RespectsSemanticsBelow I.rows (A, 1) (fun d => S.profile (field I d.1)) := by
  let u := CellScheme.zeroAbove (fun d : I.left.scheme.below (Finset.univ, 1) => S.donorValues d.1)
  let v := CellScheme.zeroAbove
    (fun d : I.right.scheme.below (Finset.univ, 1) => S.privateValues d.1)
  have hshared (i : Cell I.common.scheme) : u (I.shared.f i) = v (I.shared.g i) := by
    have hg : I.left.scheme.grade (I.shared.f i) = I.right.scheme.grade (I.shared.g i) :=
      congrArg (fun x : Finset ι × ℕ => x.2) (I.shared.shared i)
    by_cases hd : I.left.scheme.grade (I.shared.f i) ≤ 1
    · have he : I.right.scheme.grade (I.shared.g i) ≤ 1 := hg ▸ hd
      rw [show u (I.shared.f i) = S.donorValues (I.shared.f i) from
        CellScheme.zeroAbove_low _ ⟨_, Finset.subset_univ _, hd⟩,
        show v (I.shared.g i) = S.privateValues (I.shared.g i) from
        CellScheme.zeroAbove_low _ ⟨_, Finset.subset_univ _, he⟩]
      exact shared I X T hs i
    · exact (CellScheme.zeroAbove_high _ hd).trans
        (CellScheme.zeroAbove_high _ (hg ▸ hd)).symm
  have hl := (I.paste_respects hs.donor_lawful.zeroAbove
    hs.private_lawful.zeroAbove hshared).toBelow (A, 1)
  have he : (fun d : I.boundary.below (A, 1) => S.profile (field I d.1)) =
      (fun d => I.paste u v d.1) := by
    funext d
    rw [field_read]
    rcases OrderedFaceBoundaryRows.covered I.leftScheme I.rightScheme I.shared R I.isPlan
        I.leftPlan_le I.rightPlan_le d.1 with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hg : I.left.scheme.grade c ≤ 1 := by
        have hi := d.2.2
        rw [← hc] at hi
        exact (congrArg Prod.snd (I.leftFace.index c)).ge.trans hi
      rw [← hc]
      exact (I.paste_left _ _ c).trans
        ((CellScheme.zeroAbove_low
          (fun d : I.left.scheme.below (Finset.univ, 1) => S.donorValues d.1)
          ⟨c, Finset.subset_univ _, hg⟩).symm.trans
          (I.paste_left u v c).symm)
    · have hg : I.right.scheme.grade c ≤ 1 := by
        have hi := d.2.2
        rw [← hc] at hi
        exact (congrArg Prod.snd (I.rightFace.index c)).ge.trans hi
      rw [← hc]
      exact (I.paste_right _ _ (shared I X T hs) c).trans
        ((CellScheme.zeroAbove_low
          (fun d : I.right.scheme.below (Finset.univ, 1) => S.privateValues d.1)
          ⟨c, Finset.subset_univ _, hg⟩).symm.trans
          (I.paste_right u v hshared c).symm)
  exact he ▸ hl

instance : Fintype (Catalogue X 1) := Fintype.ofFinite _
abbrev fields (a : Catalogue X 1) := a.val

include T in
theorem anchor_lawful (a : Catalogue X 1) :
    RespectsSemanticsBelow I.rows (A, 1) (fun d => a.val (field I d.1)) := by
  obtain ⟨S, hs, he⟩ := a.property.2
  rw [← he]
  exact boundary_lawful I X T hs

include T in
theorem consistent (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A) :
    (rows I.boundary I.rows hA (field I) (fields I X) (proper I hB hC)).IsConsistent :=
  RelativeLadderLayer.consistent _ _ _ _ _ _ I.consistent (anchor_lawful I X T)

theorem coded (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A) :
    (rows I.boundary I.rows hA (field I) (fields I X) (proper I hB hC)).IsCoded :=
  RelativeLadderLayer.coded _ _ _ _ _ _ I.coded

end
end VaughtConjecture.Knight.GrowthOrderedBase
