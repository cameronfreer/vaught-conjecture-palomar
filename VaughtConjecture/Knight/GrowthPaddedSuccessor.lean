/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherSources
public import VaughtConjecture.Knight.LadderWeightedSuccessor

/-! # The installed second growth layer over the checked padded base

Specialize the existing weighted installer to ceiling leaves indexed by the
complete grade-two growth catalogue. Downward normalization supplies the
birth anchor, while the numerical source remains the original grade-two
vector. Original-owner lawfulness and whole-coordinate agreement are derived
from the actual boundary and rank renderer.

The construction follows the checked LOW initializer, without changing LOW,
the growth relation, or the padded base. This is consistency and selected
source lawfulness at one scope, not bountifulness or mixed-scope iteration.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedSuccessor
open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources
open SourcePrefixRows PairedSlotComparison
noncomputable section

section Anchors
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

def baseAnchor (a : Catalogue X 2) : Catalogue X 1 :=
  normalized X (by decide) (by decide : 1 ≤ 2)
    (state X a) (state_admitted X a) (state_proper X a)

theorem baseAnchor_fields (a : Catalogue X 2) :
    fields X 1 (baseAnchor X a) = PairedSlotEncoding.normalize 1 (fields X 2 a) := by
  rw [baseAnchor, normalized_fields, state_profile]

theorem baseAnchor_ranks (a : Catalogue X 2) (d : Field DA DQ) :
    RelativeLadderLayer.ranks (fields X 1) (baseAnchor X a) d =
      LadderScalarRendering.fieldRank (fields X 2 a) d := by
  change LadderScalarRendering.fieldRank (fields X 1 (baseAnchor X a)) d = _
  rw [baseAnchor_fields]
  exact ReceivingCatalogueRanks.fieldRank_normalize 1 a.val a.property.1.2 d

end Anchors

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

def input : LadderWeightedSuccessor.Input
    (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1) (U := Catalogue X 2) (V := Empty)
    I.boundary where
  sem := I.rows
  proper := proper I hB hC
  height := hA
  field := field I
  fields := fields X 1
  birth := GrowthOrderedBase.anchor_lawful I X T
  anchor := baseAnchor X
  upper := fields X 2
  rank_match := baseAnchor_ranks X
  incoming := anchor_lawful_at I X T
  visible := anchor_visible_one X
  grid := RecursiveRungRendering.grid (Field I.right.scheme I.left.scheme) 2
  bot_mem := sourceGrid_bot _ _
  ceiling := RecursiveRungRendering.ceiling (Field I.right.scheme I.left.scheme) 2
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hz := CanonicalFieldLayer.grid_bound _ _ hz
  grid_visible _ hz := sourceGrid_visible hz
  bounded := anchor_bound X
  nodeField v := Empty.elim v
  node_visible _ v := Empty.elim v

abbrev carrier := (input I X T hA hB hC).carrier
abbrev rows := (input I X T hA hB hC).rows
abbrev source := (input I X T hA hB hC).source
abbrev old := (input I X T hA hB hC).old
abbrev leaf (a : Catalogue X 2) := (input I X T hA hB hC).added (a, none)
abbrev original (d : Cell I.boundary) := old I X T hA hB hC
  (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)

/-- The entire checked padded semantics is the literal predecessor. -/
theorem lower_rows_literal : (input I X T hA hB hC).lowerRows =
    RelativeLadderLayer.rows I.boundary I.rows (by omega : 0 < A.card)
      (field I) (fields X 1) (proper I hB hC) := rfl

/-- The predecessor is KVC's checked growth base, not an equivalent new carrier. -/
theorem lower_eq_checked_base : (input I X T hA hB hC).lower =
    GrowthOrderedBase.scheme I X (by omega : 0 < A.card) := rfl

theorem lower_rows_eq_checked_base : (input I X T hA hB hC).lowerRows =
    GrowthOrderedBase.semantics I X (by omega : 0 < A.card) hB hC := rfl

/-- Every new occurrence is a ceiling leaf, not a weighted node. -/
theorem cell_cases (d : Cell (carrier I X T hA hB hC)) :
    (∃ x, d = old I X T hA hB hC x) ∨
      ∃ a, d = leaf I X T hA hB hC a := by
  let J := input I X T hA hB hC
  obtain ⟨x, hx⟩ := (SourceLayerCarrier.enumeration J.lower
    (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty))
    2 (by decide) hA).surjective d
  change SourceLayerCarrier.toCell _ _ _ _ _ x = d at hx
  rcases x with x | ⟨a, v⟩
  · exact Or.inl ⟨x, hx.symm⟩
  · cases v with
    | none => exact Or.inr ⟨a, hx.symm⟩
    | some v => exact Empty.elim v

theorem leaf_index (a : Catalogue X 2) :
    (carrier I X T hA hB hC).cell (leaf I X T hA hB hC a) = (A, 2) :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _

theorem original_index (d : Cell I.boundary) :
    (carrier I X T hA hB hC).cell (original I X T hA hB hC d) =
      I.boundary.cell d := by
  rw [SourceLayerCarrier.cell_toCell]
  exact RelativeLadderLayer.old_index _ _ d

theorem consistent : (rows I X T hA hB hC).IsConsistent :=
  (input I X T hA hB hC).consistent I.consistent

theorem source_lawful (a : Catalogue X 2) :
    RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2)
      (fun d => source I X T hA hB hC a d.1) :=
  (input I X T hA hB hC).source_lawful a

/-- Every retained rung, shadow, and proper original owner keeps its own row. -/
theorem inherited_row (c : Cell (input I X T hA hB hC).lower)
    (d : (input I X T hA hB hC).lower.below
      ((input I X T hA hB hC).lower.cell c)) :
    (rows I X T hA hB hC).E (old I X T hA hB hC c)
      (SeparatedSourceLayerCarrier.ownerEquiv (input I X T hA hB hC).lower
        (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty))
        2 (by decide) hA (input I X T hA hB hC).separation c d) =
      (input I X T hA hB hC).lowerRows.E c d :=
  (input I X T hA hB hC).inherited_row c d

theorem original_readback (a : Catalogue X 2) (d : Cell I.boundary) :
    source I X T hA hB hC a (original I X T hA hB hC d) =
      fields X 2 a (field I d) :=
  (input I X T hA hB hC).source_original a d

theorem source_ceiling (a : Catalogue X 2) :
    source I X T hA hB hC a (leaf I X T hA hB hC a) =
      RecursiveRungRendering.ceiling (Field I.right.scheme I.left.scheme) 2 :=
  (input I X T hA hB hC).source_parent a

theorem source_prefix (a b : Catalogue X 2) {h : ExtOrd}
    (hh : h ∈ RecursiveRungRendering.grid (Field I.right.scheme I.left.scheme) 2)
    (hab : Agree (fields X 2 a) (fields X 2 b) h)
    (d : Cell (carrier I X T hA hB hC)) :
    min (source I X T hA hB hC a d) h = min (source I X T hA hB hC b d) h :=
  (input I X T hA hB hC).source_prefix_all a b hh hab d

theorem source_supported (a : Catalogue X 2) (d : Cell (carrier I X T hA hB hC)) :
    OrbitPrefixSupport.Supported 2
      (RecursiveRungRendering.grid (Field I.right.scheme I.left.scheme) 2 : Set ExtOrd)
      (fields X 2 a) (source I X T hA hB hC a d) :=
  (input I X T hA hB hC).source_supported_all a d

theorem source_bound (a : Catalogue X 2) (d : Cell (carrier I X T hA hB hC)) :
    source I X T hA hB hC a d ≤
      RecursiveRungRendering.ceiling (Field I.right.scheme I.left.scheme) 2 :=
  (input I X T hA hB hC).source_bound_all a d

/-- Each new row is the full selected source, with no residual weight cap. -/
theorem leaf_row (a : Catalogue X 2)
    (d : (carrier I X T hA hB hC).below
      ((carrier I X T hA hB hC).cell (leaf I X T hA hB hC a))) :
    (rows I X T hA hB hC).E (leaf I X T hA hB hC a) d =
      source I X T hA hB hC a d.1 := by
  let J := input I X T hA hB hC
  have he := WeightedSourcePrefixLayer.row_new J.data J.weight J.weight_visible
    (J.controller (a, none)) d
  have hw : J.weight (J.controller (a, none)) = J.ceiling := by
    simp only [LadderWeightedSuccessor.Input.weight,
      LadderWeightedSuccessor.Input.member_controller,
      LadderWeightedSuccessor.Input.nodeWeight]
  exact he.trans ((congrArg (min (J.source a d.1)) hw).trans
    (min_eq_left (J.source_bound_all a d.1)))

theorem source_leaf (a b : Catalogue X 2) :
    source I X T hA hB hC a (leaf I X T hA hB hC b) =
      cut (RecursiveRungRendering.grid (Field I.right.scheme I.left.scheme) 2)
        (fields X 2 a) (fields X 2 b) := by
  let J := input I X T hA hB hC
  change WeightedSourcePrefixLayer.master J.data J.weight
    (J.controller (a, none)) (J.controller (b, none)).1 = _
  rw [WeightedSourcePrefixLayer.master_new]
  simp only [LadderWeightedSuccessor.Input.data,
    LadderWeightedSuccessor.Input.member_controller,
    LadderWeightedSuccessor.Input.weight, LadderWeightedSuccessor.Input.nodeWeight]
  exact min_eq_left (cut_le J.grid_bound _ _)

end
end VaughtConjecture.Knight.GrowthPaddedSuccessor
