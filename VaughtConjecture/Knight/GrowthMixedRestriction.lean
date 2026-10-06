/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthMixedSpareRecognition
public import VaughtConjecture.Knight.ScopeReplicationRestriction

/-! # Injective restriction on the actual mixed grade-two growth carrier

Individual auxiliary copies determine the shadow and leaf maxima. Exact
original readback then determines every original coordinate. Thus two lawful
sections equal on a smaller eligible mixed scope are equal on the target.
Lawful capping yields every permitted-cap version without a new repair.
This does not assert existence of a lawful extension.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthMixedRestriction
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
open GrowthMixedLeafRecognition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "Native" => GrowthPaddedSuccessor.carrier I X T hA hB hC
local notation "Carrier" => carrier I X T hA hB hC
local notation "Rows" => rows I X T hA hB hC

theorem original_or_full (c : Cell Native) :
    (∃ d : Cell I.boundary, c = GrowthPaddedSuccessor.original I X T hA hB hC d) ∨
      CellScheme.scope Native c = A := by
  rcases GrowthPaddedSuccessor.cell_cases I X T hA hB hC c with ⟨d, rfl⟩ | ⟨a, rfl⟩
  · rcases RelativeLadderLayer.cell_cases I.boundary (GrowthLeafRecognition.card_pos hA) d with
      ⟨e, rfl⟩ | ⟨v, rfl⟩
    · exact Or.inl ⟨e, rfl⟩
    · exact Or.inr (congrArg Prod.fst (GrowthLeafRecognition.cell_added I X T hA hB hC v))
  · exact Or.inr (congrArg Prod.fst (GrowthPaddedSuccessor.leaf_index I X T hA hB hC a))

variable (U V : Finset ι) (hU : U ∈ R) (hV : V ∈ R)
  (hmU : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V)
  (hu : 2 ≤ U.card) (hv : 2 ≤ V.card) (hUV : U ⊆ V)
  {p q : CellScheme.below (carrier I X T hA hB hC) (V, 2) → ExtOrd}

include hU hV hmU hmV hu hv

/-- Equality on the whole prescribed lower domain, not merely field readouts,
determines a lawful target section. No extension premise occurs. -/
theorem eq_of_restriction (hp : RespectsSemanticsBelow Rows (V, 2) p)
    (hq : RespectsSemanticsBelow Rows (V, 2) q)
    (hag : ∀ d : CellScheme.below Carrier (U, 2),
      p (CellScheme.below.mono (show GradedLe (U, 2) (V, 2) from ⟨hUV, le_rfl⟩) d) =
      q (CellScheme.below.mono (show GradedLe (U, 2) (V, 2) from ⟨hUV, le_rfl⟩) d)) : p = q := by
  have haux (z : CellScheme.below Carrier (V, 2))
      (hz : CellScheme.scope Native (erase I X T hA hB hC z.1) = A) : p z = q z :=
    ScopeReplicationRestriction.auxiliary_eq Native B C
      (GrowthReplicatedRows.proper_covered (layer I X T hA hB hC))
      (GrowthPaddedSuccessor.rows I X T hA hB hC) hU hmU hu hV hmV hv hUV hp hq hag z hz
  have hshadow (f : Field I.right.scheme I.left.scheme) :
      shadowSup I X T hA hB hC V hV hmV hv p f =
        shadowSup I X T hA hB hC V hV hmV hv q f := by
    apply Finset.sup_congr rfl
    intro a _
    apply haux
    rw [erase_ladder]
    exact congrArg Prod.fst (GrowthLeafRecognition.cell_ladderAt I X T hA hB hC _)
  have hleaf : leafSup I X T hA hB hC V hV hmV hv p =
      leafSup I X T hA hB hC V hV hmV hv q := by
    apply Finset.sup_congr rfl
    intro a _
    apply haux
    rw [erase_leaf]
    exact congrArg Prod.fst (GrowthPaddedSuccessor.leaf_index I X T hA hB hC a)
  funext z
  rcases original_or_full I X T hA hB hC (erase I X T hA hB hC z.1) with ⟨d, hd⟩ | hz
  · rw [GrowthMixedSpareRecognition.original_readback I X T hA hB hC V hV hmV hv hp z d hd,
      GrowthMixedSpareRecognition.original_readback I X T hA hB hC V hV hmV hv hq z d hd,
      hshadow, GrowthMixedSpareRecognition.height, GrowthMixedSpareRecognition.height, hleaf]
  · exact haux z hz

/-- Capping preserves lawfulness, so restriction injectivity supplies all
permitted physical cap equations, bottom and literal top included. -/
theorem cap_eq_of_restriction (hp : RespectsSemanticsBelow Rows (V, 2) p)
    (hq : RespectsSemanticsBelow Rows (V, 2) q) {γ : ExtOrd} (hγ : SelfVis 2 γ)
    (hag : ∀ d : CellScheme.below Carrier (U, 2),
      min (p (CellScheme.below.mono (show GradedLe (U, 2) (V, 2) from ⟨hUV, le_rfl⟩) d)) γ =
      min (q (CellScheme.below.mono (show GradedLe (U, 2) (V, 2) from ⟨hUV, le_rfl⟩) d)) γ) :
    ∀ z, min (p z) γ = min (q z) γ :=
  congrFun (eq_of_restriction I X T hA hB hC U V hU hV hmU hmV hu hv hUV
    (hp.cap hγ) (hq.cap hγ) hag)

end
end VaughtConjecture.Knight.GrowthMixedRestriction
