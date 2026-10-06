/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedCharts
public import VaughtConjecture.Knight.GrowthMixedGradeOne

/-! # Complete-field admission from arbitrary higher mixed sections

The lawful grade-one restriction provides finite bottom reflection for each
higher owner's actual chart. Each positive grade maximum therefore produces
an admitted capped complete vector; a zero maximum uses the independent zero
state. Neither admission nor a whole-section extension is an input.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthHigherMixed
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration SupportLadderRows LadderScalarRendering
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (t : ℕ) (ht : t + 2 ≤ A.card)
local notation "P" => tower I X T hA hB hC t ht
local notation "D" => carrier I X T hA hB hC t ht
local notation "Rows" => rows I X T hA hB hC t ht
local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)
local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)
local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (j : ℕ) (hj : j ≤ U.card) (hj0 : 1 ≤ j)
  {p : CellScheme.below (carrier I X T hA hB hC t ht) (U, j) → ExtOrd}

theorem ladder_lawful (hp : RespectsSemanticsBelow Rows (U, j) p) :
    SupportLadderRows.Lawful ranks₁
      (fun v => p (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 v)) := by
  exact GrowthMixedGradeOne.ladder_lawful I X T hA hB hC P U
    (by rw [GrowthPaddedIteration.build_plan]; exact hU) hm
    (hp.mono (show GradedLe (U, 1) (U, j) from ⟨le_rfl, hj0⟩))

section Owner
variable (c : Cell (tower I X T hA hB hC t ht).carrier)
  (hc : (tower I X T hA hB hC t ht).carrier.scope c = A)
  (hg : (tower I X T hA hB hC t ht).carrier.grade c ≤ j)
  (O : GrowthPaddedOwnerProvenance.Origin I X T hA hB hC t ht c)
  {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop ((tower I X T hA hB hC t ht).carrier.grade c)) τ)
  (hread : ∀ (z : CellScheme.below (carrier I X T hA hB hC t ht) (U, j))
      (hz : (carrier I X T hA hB hC t ht).grade z.1 ≤
        (tower I X T hA hB hC t ht).carrier.grade c),
    τ ((tower I X T hA hB hC t ht).rows.E c
      (nativeArgument I X T hA hB hC t ht U j c hc z hz)) =
        min (p z) (p (place I X T hA hB hC t ht U hU hm j hj c hc hg)))

include hread in
theorem owner_ladder_read (v : Pt) :
    τ (SupportLadderRows.image ranks₁
      (GrowthPaddedNativeRows.anchor I X T hA hB hC O.birth O.height O.member)
      (LadderScalarRendering.level (values (fields X (O.birth + 2) O.member))
        (GrowthPaddedNativeRows.ceiling I O.birth)) v) =
      min (p (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 v))
        (p (place I X T hA hB hC t ht U hU hm j hj c hc hg)) := by
  have hz : (D).grade (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 v).1 ≤
      (P).carrier.grade c :=
    (congrArg Prod.snd (ladderAt_index I X T hA hB hC t ht U hU hm j hj hj0 v)).le.trans
      ((P).carrier.grade_pos c)
  have he : (P).rows.E c (nativeArgument I X T hA hB hC t ht U j c hc
      (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 v) hz) =
      (P).rows.E c (O.ladderArgument v) :=
    (P).rows.E_congr rfl (erase_ladderAt I X T hA hB hC t ht U hU hm j hj hj0 v)
  exact (congrArg τ (he.trans (O.row_ladder v)).symm).trans (hread _ hz)

include hj0 hτ hread in
/-- Reflection on every complete field, including hidden and future fields.
No global bottom-reflection property of the chart is asserted. -/
theorem owner_bottom_reflection (hp : RespectsSemanticsBelow Rows (U, j) p)
    (hne : p (place I X T hA hB hC t ht U hU hm j hj c hc hg) ≠ ⊥) (f : Fld) :
    τ (fields X (O.birth + 2) O.member f) = ⊥ → fields X (O.birth + 2) O.member f = ⊥ := by
  let a := GrowthPaddedNativeRows.anchor I X T hA hB hC O.birth O.height O.member
  let H := GrowthPaddedNativeRows.ceiling I O.birth
  have hceil := owner_ceiling I X T hA hB hC t ht U hU hm j hj c hc hg O hread
  have hHne : H ≠ ⊥ := fun hz => hne (hceil.symm.trans ((congrArg τ hz).trans hτ.bot))
  have : Nonempty (Catalogue X 1) := ⟨GrowthLeafRecognition.zeroMember I X 1 le_rfl⟩
  have h0 : LadderScalarRendering.level (values (fields X (O.birth + 2) O.member)) H 0 = ⊥ :=
    level_zero _ _
  have hf : ∀ i, 0 < i → i ≤ rungs →
      LadderScalarRendering.level (values (fields X (O.birth + 2) O.member)) H i ≠ ⊥ :=
    fun i hi _ => level_pos (bot_not_values _) (values_bound (anchor_bound X O.member)) hHne hi
  have hspare : τ (LadderScalarRendering.level (values (fields X (O.birth + 2) O.member)) H rungs) =
      p (place I X T hA hB hC t ht U hU hm j hj c hc hg) := by
    have he := O.row_ladder (SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I) a)
    rw [O.row_spare] at he
    rw [SupportLadderRows.image, SupportLadderRows.index_leaf,
      FiniteProfileControllers.cut_refl] at he
    exact (congrArg τ he.symm).trans hceil
  have hr := owner_ladder_read I X T hA hB hC t ht U hU hm j hj hj0 c hc hg O hread
  have hrefl := SupportLadderRows.bottom_reflection_image (GrowthLeafRecognition.rank_le_rungs I X)
    (GrowthLeafRecognition.rungs_pos I) (ladder_lawful I X T hA hB hC t ht U hU hm j hj hj0 hp)
    a h0 hf hne hr hspare (shadow a f)
  rw [SupportLadderRows.image, GrowthLeafRecognition.index_shadow_self,
    GrowthPaddedNativeRows.anchor_ranks, field_readback] at hrefl
  exact hrefl.mp

end Owner

/-- Admission of each grade-capped complete shadow vector is constructed from
the actual maximal owner's chart. There is no upward-admission step. -/
theorem exists_admitted_at (hp : RespectsSemanticsBelow Rows (U, j) p)
    (k : ℕ) (hk : 2 ≤ k) (hkj : k ≤ j) (hkt : k ≤ t + 2) :
    ∃ S : State I.right.scheme I.left.scheme, Admitted X k S ∧
      ∀ f, S.profile f = min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p f)
        (gradeMax I X T hA hB hC t ht U j p k) := by
  by_cases hz : gradeMax I X T hA hB hC t ht U j p k = ⊥
  · exact ⟨zero, zero_admitted X k, fun f => by rw [hz, min_bot_right]; cases f <;> rfl⟩
  obtain ⟨c, hc, hg, hmax⟩ := exists_maximal_owner I X T hA hB hC t ht U hU hm j hj hp
    k (by omega) hkj hkt
  let O := GrowthPaddedOwnerProvenance.origin I X T hA hB hC t ht c hc (hk.trans_eq hg.symm)
  obtain ⟨τ, hτ, hr⟩ := exists_owner_chart I X T hA hB hC t ht U hU hm j hj hp
    c hc (hg.le.trans hkj)
  have hb : O.birth + 2 = k := (congrArg Prod.snd O.owner_index).symm.trans hg
  have hτ' : Witness (gTop (O.birth + 2)) τ := hb.symm ▸ (hg ▸ hτ)
  refine ⟨(state X O.member).map τ, hb ▸ ?_, fun f => ?_⟩
  · refine Admitted.map_on_profile X (state_admitted X O.member) hτ' (by omega) fun f hf => ?_
    rw [state_profile] at hf ⊢
    exact owner_bottom_reflection I X T hA hB hC t ht U hU hm j hj hj0 c hc
      (hg.le.trans hkj) O hτ hr hp (fun he => hz (hmax.symm.trans he)) f hf
  · rw [State.profile_map, state_profile, ← hmax]
    exact owner_recognition I X T hA hB hC t ht U hU hm j hj hj0 c hc (hg.le.trans hkj) O hτ hr f

/-- Lawfulness on the entire original boundary, including originals absent
from the prescribed mixed scope, follows from the constructed admitted state. -/
theorem boundary_capped_lawful (hp : RespectsSemanticsBelow Rows (U, j) p)
    (k : ℕ) (hk : 2 ≤ k) (hkj : k ≤ j) (hkt : k ≤ t + 2) :
    RespectsSemanticsBelow I.rows (A, k) (fun d =>
      min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d.1))
        (gradeMax I X T hA hB hC t ht U j p k)) := by
  obtain ⟨S, hS, he⟩ := exists_admitted_at I X T hA hB hC t ht U hU hm j hj hj0 hp k hk hkj hkt
  have hl := boundary_lawful_at I X T hS
  simpa only [he] using hl

end
end VaughtConjecture.Knight.GrowthHigherMixed
