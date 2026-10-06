/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedOwnerProvenance
public import VaughtConjecture.Knight.GrowthReplicatedRows
public import VaughtConjecture.Knight.ScopeReplicationCharts
public import VaughtConjecture.Knight.GrowthLeafRecognition

/-! # Higher-owner columns on the actual replicated growth carrier

The final build and observation cutoff are independent. Every inherited higher
owner has its own birth provenance, and the entire padded base has named copies
at the observed mixed scope. No lawful extension is used to obtain these rows.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthHigherMixed
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration SupportLadderRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (t : ℕ) (ht : t + 2 ≤ A.card)

abbrev tower := build I X T hA hB hC t ht
abbrev carrier := GrowthReplicatedRows.carrier (tower I X T hA hB hC t ht)
abbrev rows := GrowthReplicatedRows.rows (tower I X T hA hB hC t ht)
abbrev erase := GrowthReplicatedRows.erase (tower I X T hA hB hC t ht)

local notation "P" => tower I X T hA hB hC t ht
local notation "D" => carrier I X T hA hB hC t ht
local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)

def original (d : Cell I.boundary) : Cell (P).carrier :=
  (P).baseMap (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)

theorem original_index (d : Cell I.boundary) : (P).carrier.cell
    (original I X T hA hB hC t ht d) = I.boundary.cell d :=
  ((P).base_index _).trans (RelativeLadderLayer.old_index _ _ d)

abbrev ladder (v : Pt) : Cell (P).carrier :=
  GrowthPaddedNativeRows.ladder I X T hA hB hC t ht v

theorem ladder_index (v : Pt) : (P).carrier.cell
    (ladder I X T hA hB hC t ht v) = (A, 1) :=
  GrowthPaddedNativeRows.ladder_index I X T hA hB hC t ht v

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (j : ℕ) (hj : j ≤ U.card)

def place (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ j) : (D).below (U, j) :=
  ⟨ScopeReplicationCarrier.atScope (P).carrier B C U
      (by rw [GrowthPaddedIteration.build_plan]; exact hU) hm c hc (hg.trans hj),
    by rw [ScopeReplicationCarrier.atScope_index]; exact ⟨le_rfl, hg⟩⟩

theorem place_index (c) (hc) (hg) : (D).cell
    (place I X T hA hB hC t ht U hU hm j hj c hc hg).1 = (U, (P).carrier.grade c) :=
  ScopeReplicationCarrier.atScope_index (P).carrier B C U _ hm c hc (hg.trans hj)

theorem erase_place (c) (hc) (hg) : erase I X T hA hB hC t ht
    (place I X T hA hB hC t ht U hU hm j hj c hc hg).1 = c :=
  ScopeReplicationCarrier.erase_atScope (P).carrier B C U _ hm c hc (hg.trans hj)

variable (hj0 : 1 ≤ j)

def ladderAt (v : Pt) : (D).below (U, j) :=
  place I X T hA hB hC t ht U hU hm j hj (ladder I X T hA hB hC t ht v)
    (congrArg Prod.fst (ladder_index I X T hA hB hC t ht v))
    ((congrArg Prod.snd (ladder_index I X T hA hB hC t ht v)).le.trans hj0)

theorem ladderAt_index (v : Pt) : (D).cell
    (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 v).1 = (U, 1) :=
  (place_index I X T hA hB hC t ht U hU hm j hj _ _ _).trans
    (congrArg (fun k => (U, k)) (congrArg Prod.snd (ladder_index I X T hA hB hC t ht v)))

theorem erase_ladderAt (v : Pt) : erase I X T hA hB hC t ht
    (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 v).1 =
      ladder I X T hA hB hC t ht v :=
  erase_place I X T hA hB hC t ht U hU hm j hj _ _ _

def shadowSup (p : (D).below (U, j) → ExtOrd) (f : Fld) : ExtOrd :=
  Finset.univ.sup fun a : Catalogue X 1 =>
    p (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 (shadow a f))

end
end VaughtConjecture.Knight.GrowthHigherMixed
