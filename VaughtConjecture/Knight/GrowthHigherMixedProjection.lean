/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedRecognition

/-! # One lawful original projection at every installed mixed cutoff

Grade one is uncapped. At every higher grade the original projection uses
that grade's actual maximum. All capped prefixes are lawful on the whole
ordered boundary, so decreasing heights splice them lawfully without requiring
one uncapped higher-grade state or identifying different chart anchors.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthHigherMixed
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration SupportLadderRows LadderScalarRendering
open SharpWitnessComposition
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
local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)
local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (j : ℕ) (hj : j ≤ U.card) (hj0 : 1 ≤ j)
  {p : CellScheme.below (carrier I X T hA hB hC t ht) (U, j) → ExtOrd}

theorem original_readback_one (hp : RespectsSemanticsBelow Rows (U, j) p)
    (z : (D).below (U, j)) (d : Cell I.boundary)
    (hz : erase I X T hA hB hC t ht z.1 = original I X T hA hB hC t ht d)
    (hg : (D).grade z.1 = 1) :
    p z = shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d) := by
  exact GrowthMixedGradeOne.original_readback_one I X T hA hB hC P U
    (by rw [GrowthPaddedIteration.build_plan]; exact hU) hm
    (hp.mono (show GradedLe (U, 1) (U, j) from ⟨le_rfl, hj0⟩))
    ⟨z.1, z.2.1, hg.le⟩ d hz

theorem boundary_one (hp : RespectsSemanticsBelow Rows (U, j) p) :
    RespectsSemanticsBelow I.rows (A, 1)
      (fun d => shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p
        (GrowthOrderedBase.field I d.1)) := by
  have hplan : U ∈ (P).carrier.plan := by rw [GrowthPaddedIteration.build_plan]; exact hU
  let q : (D).below (U, 1) → ExtOrd := fun d => p (CellScheme.below.mono
    (show GradedLe (U, 1) (U, j) from ⟨le_rfl, hj0⟩) d)
  have hq : RespectsSemanticsBelow Rows (U, 1) q :=
    hp.mono (show GradedLe (U, 1) (U, j) from ⟨le_rfl, hj0⟩)
  obtain ⟨a, τ, hτ, hmax, hb, hread, -⟩ :=
    GrowthMixedGradeOne.exists_spare_chart I X T hA hB hC P U hplan hm hq
  have hl := RelativeLadderLayer.rank_respects I.boundary I.rows (GrowthOrderedBase.field I)
    (fields X 1) a (GrowthHigherSources.anchor_lawful_at I X T a) rungs
  have he : (fun d : I.boundary.below (A, 1) =>
      shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d.1)) =
      fun d => τ (SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field I d.1))) :=
    funext fun d => GrowthMixedGradeOne.shadowSup_eq_spare I X T hA hB hC P U hplan hm hτ hread _
  rw [he]
  by_cases hz : GrowthMixedGradeOne.spareSup I X T hA hB hC P U hplan hm q = ⊥
  · have htau : ∀ x, τ x = ⊥ := fun x => le_bot_iff.mp ((hb x).trans_eq hz)
    simp only [htau]
    exact respectsBelow_bot I.rows (A, 1)
  · apply map_respects_of_bottom_reflection hl (fun d => d.2.2) (boundedMap_of_witness hτ)
    intro d
    have hr := GrowthMixedGradeOne.spare_bottom_reflection I X T hA hB hC P U hplan hm
      hτ hread hq hmax hz (shadow a (GrowthOrderedBase.field I d.1))
    rwa [GrowthSpareRecognition.row_spare, GrowthLeafRecognition.index_shadow_self] at hr

/-- Heights outside the observed range are bottom only to give a globally
antitone function; no occurrence of that range is projected. -/
def height (p : (D).below (U, j) → ExtOrd) (k : ℕ) : ExtOrd :=
  if k ≤ 1 then ⊤ else if k ≤ j then gradeMax I X T hA hB hC t ht U j p k else ⊥

include hU hm hj in
theorem height_antitone (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2) :
    Antitone (height I X T hA hB hC t ht U j p) := by
  intro a b hab
  by_cases hb : b ≤ 1
  · simp only [height, ite_eq_left hb, ite_eq_left (hab.trans hb), le_refl]
  by_cases ha : a ≤ 1
  · rw [height, height, ite_eq_left ha]
    exact le_top
  by_cases hbj : b ≤ j
  · simp only [height, ite_eq_right hb, ite_eq_right ha,
      ite_eq_left hbj, ite_eq_left (hab.trans hbj)]
    exact gradeMax_antitone I X T hA hB hC t ht U hU hm j hj hp a b
      (by omega) (by omega) hab hbj (hbj.trans hjt)
  · simp only [height, ite_eq_right hb, ite_eq_right hbj, bot_le]

/-- One lawful vector on the entire original boundary, including hidden
owners, preserving lower values above later grade maxima. -/
theorem boundary_projection (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2) :
    RespectsSemanticsBelow I.rows (A, j) (fun d =>
      min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d.1))
        (height I X T hA hB hC t ht U j p (I.boundary.grade d.1))) := by
  apply GradePrefixProjection.respectsBelow (sem := I.rows) (BJ := (A, j))
    (ρ := fun d => shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d))
    (height_antitone I X T hA hB hC t ht U hU hm j hj hp hjt)
  intro k hkj
  by_cases hk0 : k = 0
  · subst k
    exact GrowthSpareRecognition.respectsBelow_zero I.rows _
  by_cases hk1 : k = 1
  · subst k
    simpa only [height, ite_eq_left (le_refl (1 : ℕ)), min_top_right] using
      boundary_one I X T hA hB hC t ht U hU hm j hj hj0 hp
  · simpa only [height, ite_eq_right (by omega : ¬ k ≤ 1), ite_eq_left hkj] using
      boundary_capped_lawful I X T hA hB hC t ht U hU hm j hj hj0 hp k
        (by omega) hkj (hkj.trans hjt)

theorem projection_readback (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2)
    (z : (D).below (U, j)) (d : Cell I.boundary)
    (hz : erase I X T hA hB hC t ht z.1 = original I X T hA hB hC t ht d) :
    p z = min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d))
      (height I X T hA hB hC t ht U j p (I.boundary.grade d)) := by
  have hg : I.boundary.grade d = (D).grade z.1 :=
    (congrArg Prod.snd (original_index I X T hA hB hC t ht d)).symm.trans
      ((congrArg (P).carrier.grade hz).symm.trans (ScopeReplicationCarrier.erase_grade _ B C z.1))
  have hpos := (D).grade_pos z.1
  have hle : (D).grade z.1 ≤ j := z.2.2
  rw [height, hg]
  by_cases h1 : (D).grade z.1 ≤ 1
  · rw [ite_eq_left h1, min_top_right]
    exact original_readback_one I X T hA hB hC t ht U hU hm j hj hj0 hp z d hz (by omega)
  · rw [ite_eq_right h1, ite_eq_left hle]
    exact original_readback I X T hA hB hC t ht U hU hm j hj hj0 hp z d hz
      (by omega) (hle.trans hjt)

end
end VaughtConjecture.Knight.GrowthHigherMixed
