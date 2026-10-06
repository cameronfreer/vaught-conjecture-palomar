/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedRestriction

/-! # Concrete mixed extension values on a fixed final growth carrier

Originals use the lawful grade-dependent boundary projection. Every relevant
auxiliary uses its own actual prescribed copy; no auxiliary is reconstructed
from complete-field readouts. Values above the observed cutoff are irrelevant.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthHigherMixed
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
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
local notation "P" => tower I X T hA hB hC t ht
local notation "D" => carrier I X T hA hB hC t ht
local notation "Rows" => rows I X T hA hB hC t ht
local notation "Pt" => RelativeLadderLayer.Point
  (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)

theorem original_injective : Function.Injective (original I X T hA hB hC t ht) :=
  ((P).base_mono.comp
    (SourceLayerCarrier.old_order I.boundary Pt 1 Nat.one_pos (by omega))).injective

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (j : ℕ) (hj : j ≤ U.card) (hj0 : 1 ≤ j)
  (p : CellScheme.below (carrier I X T hA hB hC t ht) (U, j) → ExtOrd)

def boundaryValue (d : Cell I.boundary) : ExtOrd :=
  min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d))
    (height I X T hA hB hC t ht U j p (I.boundary.grade d))

def nativeValue (c : Cell (P).carrier) : ExtOrd := by
  classical
  exact if ho : ∃ d, c = original I X T hA hB hC t ht d then
    boundaryValue I X T hA hB hC t ht U hU hm j hj hj0 p ho.choose
  else if ha : (P).carrier.scope c = A ∧ (P).carrier.grade c ≤ j then
    p (place I X T hA hB hC t ht U hU hm j hj c ha.1 ha.2)
  else ⊥

theorem native_original (d : Cell I.boundary) :
    nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p (original I X T hA hB hC t ht d) =
      boundaryValue I X T hA hB hC t ht U hU hm j hj hj0 p d := by
  classical
  unfold nativeValue
  split_ifs with ho
  · exact congrArg (boundaryValue I X T hA hB hC t ht U hU hm j hj hj0 p)
      (original_injective I X T hA hB hC t ht ho.choose_spec.symm)
  all_goals exact (ho ⟨d, rfl⟩).elim

theorem native_full (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ j) :
    nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p c =
      p (place I X T hA hB hC t ht U hU hm j hj c hc hg) := by
  classical
  unfold nativeValue
  split_ifs with ho ha
  · obtain ⟨d, rfl⟩ := ho
    exact (GrowthOrderedBase.proper I hB hC d
      ((congrArg Prod.fst (original_index I X T hA hB hC t ht d)).symm.trans hc)).elim
  · rfl
  · exact (ha ⟨hc, hg⟩).elim

def value {V : Finset ι} (z : (D).below (V, j)) : ExtOrd :=
  nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p (erase I X T hA hB hC t ht z.1)

theorem literal (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2)
    {V : Finset ι} (hUV : U ⊆ V) (z : (D).below (U, j)) :
    value I X T hA hB hC t ht U hU hm j hj hj0 p
      (CellScheme.below.mono (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) z) = p z := by
  change nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p
    (erase I X T hA hB hC t ht z.1) = p z
  rcases original_or_full I X T hA hB hC t ht (erase I X T hA hB hC t ht z.1) with
      ⟨d, hd⟩ | hz
  · rw [hd, native_original]
    exact (projection_readback I X T hA hB hC t ht U hU hm j hj hj0 hp hjt z d hd).symm
  · rw [native_full I X T hA hB hC t ht U hU hm j hj hj0 p _ hz
      ((ScopeReplicationCarrier.erase_grade (P).carrier B C z.1).le.trans z.2.2)]
    exact (GrowthReplicatedRows.copy_eq P hp z _
      (z.2.1.trans (congrArg Prod.fst
        (place_index I X T hA hB hC t ht U hU hm j hj _ _ _)).symm.le)
      (erase_place I X T hA hB hC t ht U hU hm j hj _ _ _).symm).symm

end
end VaughtConjecture.Knight.GrowthHigherMixed
