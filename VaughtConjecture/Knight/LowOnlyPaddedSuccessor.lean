/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyOrderedSources
public import VaughtConjecture.Knight.LadderWeightedSuccessor

/-! # The first LOW successor on the unchanged padded base

The birth catalogue is the existing grade-one LOW catalogue. The new layer
has exactly one ceiling leaf per grade-two admitted canonical profile: the
weighted installer is specialized to an empty weighted-node type. The actual
predecessor sections, lawfulness, and agreement are constructed from the
ordered original boundary and downward normalization, not assumed.

This is one installed higher layer with consistent rows. Neither iteration
nor unrestricted bountifulness of the output is claimed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedSuccessor
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open SourcePrefixRows PairedSlotComparison
noncomputable section

section Anchors
variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

/-- Downward normalization chooses an existing birth anchor; numerical source
values are not identified with that anchor's normalized values. -/
def baseAnchor (a : F.Anchor 2) : F.Anchor 1 := by
  refine ⟨PairedSlotEncoding.normalize 1 a.val, ?_⟩
  obtain ⟨S, hS, he⟩ := a.property.2
  have hp : ∀ d, S.profile d ≠ ⊤ := by rw [he]; exact a.property.1.2
  have h := (LowOnlyRecursiveCoverage.normalizedAnchor F (by decide : 1 ≤ 1)
    (by decide : 1 ≤ 2) hS hp).property
  change F.fields 1 (LowOnlyRecursiveCoverage.normalizedAnchor F
    (by decide : 1 ≤ 1) (by decide : 1 ≤ 2) hS hp) ∈ F.catalogue 1 at h
  rw [LowOnlyRecursiveCoverage.normalizedAnchor_fields] at h
  simpa only [he] using h

theorem baseAnchor_ranks (a : F.Anchor 2) (d : Field P C) :
    RelativeLadderLayer.ranks (F.fields 1) (baseAnchor F a) d =
      LadderScalarRendering.fieldRank (F.fields 2 a) d :=
  ReceivingCatalogueRanks.fieldRank_normalize 1 a.val a.property.1.2 d

end Anchors

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

def input : LadderWeightedSuccessor.Input
    (X := Field I.left I.right) (Q := F.Anchor 1) (U := F.Anchor 2) (V := Empty)
    I.boundary where
  sem := I.rows
  proper := proper I hB hC
  height := hA
  field := field I
  fields := F.fields 1
  birth := LowOnlyOrderedSources.anchor_lawful I F hroot 1
  anchor := baseAnchor F
  upper := F.fields 2
  rank_match := baseAnchor_ranks F
  incoming := LowOnlyOrderedSources.anchor_lawful I F hroot 2
  visible := LowOnlyRecursiveCharts.anchor_visible_one F (by decide)
  grid := RecursiveRungRendering.grid (Field I.left I.right) 2
  bot_mem := sourceGrid_bot _ _
  ceiling := RecursiveRungRendering.ceiling (Field I.left I.right) 2
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hz := CanonicalFieldLayer.grid_bound _ _ hz
  grid_visible _ hz := sourceGrid_visible hz
  bounded := LowOnlyRecursiveCharts.anchor_bound F
  nodeField v := Empty.elim v
  node_visible _ v := Empty.elim v

abbrev carrier := (input I F hroot hA hB hC).carrier
abbrev rows := (input I F hroot hA hB hC).rows
abbrev source := (input I F hroot hA hB hC).source
abbrev old := (input I F hroot hA hB hC).old
abbrev leaf (a : F.Anchor 2) := (input I F hroot hA hB hC).added (a, none)
abbrev original (d : Cell I.boundary) := old I F hroot hA hB hC
  (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)

/-- The entire checked padded semantics is the literal predecessor. -/
theorem lower_rows_literal : (input I F hroot hA hB hC).lowerRows =
    RelativeLadderLayer.rows I.boundary I.rows (by omega : 0 < A.card)
      (field I) (F.fields 1) (proper I hB hC) := rfl

/-- Every new occurrence is a ceiling leaf, not a weighted node. -/
theorem cell_cases (d : Cell (carrier I F hroot hA hB hC)) :
    (∃ x, d = old I F hroot hA hB hC x) ∨
      ∃ a, d = leaf I F hroot hA hB hC a := by
  let J := input I F hroot hA hB hC
  obtain ⟨x, hx⟩ := (SourceLayerCarrier.enumeration J.lower
    (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty))
    2 (by decide) hA).surjective d
  change SourceLayerCarrier.toCell _ _ _ _ _ x = d at hx
  rcases x with x | ⟨a, v⟩
  · exact Or.inl ⟨x, hx.symm⟩
  · cases v with
    | none => exact Or.inr ⟨a, hx.symm⟩
    | some v => exact Empty.elim v

theorem leaf_index (a : F.Anchor 2) :
    (carrier I F hroot hA hB hC).cell (leaf I F hroot hA hB hC a) = (A, 2) :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _

theorem original_index (d : Cell I.boundary) :
    (carrier I F hroot hA hB hC).cell (original I F hroot hA hB hC d) =
      I.boundary.cell d := by
  rw [SourceLayerCarrier.cell_toCell]
  exact RelativeLadderLayer.old_index _ _ d

theorem consistent : (rows I F hroot hA hB hC).IsConsistent :=
  (input I F hroot hA hB hC).consistent I.consistent

theorem source_lawful (a : F.Anchor 2) :
    RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2)
      (fun d => source I F hroot hA hB hC a d.1) :=
  (input I F hroot hA hB hC).source_lawful a

/-- Every retained rung, shadow, and proper original owner keeps its own row. -/
theorem inherited_row (c : Cell (input I F hroot hA hB hC).lower)
    (d : (input I F hroot hA hB hC).lower.below
      ((input I F hroot hA hB hC).lower.cell c)) :
    (rows I F hroot hA hB hC).E (old I F hroot hA hB hC c)
      (SeparatedSourceLayerCarrier.ownerEquiv (input I F hroot hA hB hC).lower
        (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty))
        2 (by decide) hA (input I F hroot hA hB hC).separation c d) =
      (input I F hroot hA hB hC).lowerRows.E c d :=
  (input I F hroot hA hB hC).inherited_row c d

theorem original_readback (a : F.Anchor 2) (d : Cell I.boundary) :
    source I F hroot hA hB hC a (original I F hroot hA hB hC d) =
      F.fields 2 a (field I d) :=
  (input I F hroot hA hB hC).source_original a d

theorem source_ceiling (a : F.Anchor 2) :
    source I F hroot hA hB hC a (leaf I F hroot hA hB hC a) =
      RecursiveRungRendering.ceiling (Field I.left I.right) 2 :=
  (input I F hroot hA hB hC).source_parent a

theorem source_prefix (a b : F.Anchor 2) {h : ExtOrd}
    (hh : h ∈ RecursiveRungRendering.grid (Field I.left I.right) 2)
    (hab : Agree (F.fields 2 a) (F.fields 2 b) h)
    (d : Cell (carrier I F hroot hA hB hC)) :
    min (source I F hroot hA hB hC a d) h = min (source I F hroot hA hB hC b d) h :=
  (input I F hroot hA hB hC).source_prefix_all a b hh hab d

theorem source_supported (a : F.Anchor 2) (d : Cell (carrier I F hroot hA hB hC)) :
    OrbitPrefixSupport.Supported 2
      (RecursiveRungRendering.grid (Field I.left I.right) 2 : Set ExtOrd)
      (F.fields 2 a) (source I F hroot hA hB hC a d) :=
  (input I F hroot hA hB hC).source_supported_all a d

theorem source_bound (a : F.Anchor 2) (d : Cell (carrier I F hroot hA hB hC)) :
    source I F hroot hA hB hC a d ≤
      RecursiveRungRendering.ceiling (Field I.left I.right) 2 :=
  (input I F hroot hA hB hC).source_bound_all a d

/-- Each new row is the full selected source, with no residual weight cap. -/
theorem leaf_row (a : F.Anchor 2)
    (d : (carrier I F hroot hA hB hC).below
      ((carrier I F hroot hA hB hC).cell (leaf I F hroot hA hB hC a))) :
    (rows I F hroot hA hB hC).E (leaf I F hroot hA hB hC a) d =
      source I F hroot hA hB hC a d.1 := by
  let J := input I F hroot hA hB hC
  have he := WeightedSourcePrefixLayer.row_new J.data J.weight J.weight_visible
    (J.controller (a, none)) d
  have hw : J.weight (J.controller (a, none)) = J.ceiling := by
    simp only [LadderWeightedSuccessor.Input.weight,
      LadderWeightedSuccessor.Input.member_controller,
      LadderWeightedSuccessor.Input.nodeWeight]
  exact he.trans ((congrArg (min (J.source a d.1)) hw).trans
    (min_eq_left (J.source_bound_all a d.1)))

theorem source_leaf (a b : F.Anchor 2) :
    source I F hroot hA hB hC a (leaf I F hroot hA hB hC b) =
      cut (RecursiveRungRendering.grid (Field I.left I.right) 2)
        (F.fields 2 a) (F.fields 2 b) := by
  let J := input I F hroot hA hB hC
  change WeightedSourcePrefixLayer.master J.data J.weight
    (J.controller (a, none)) (J.controller (b, none)).1 = _
  rw [WeightedSourcePrefixLayer.master_new]
  simp only [LadderWeightedSuccessor.Input.data,
    LadderWeightedSuccessor.Input.member_controller,
    LadderWeightedSuccessor.Input.weight, LadderWeightedSuccessor.Input.nodeWeight]
  exact min_eq_left (cut_le J.grid_bound _ _)

end
end VaughtConjecture.Knight.LowOnlyPaddedSuccessor
