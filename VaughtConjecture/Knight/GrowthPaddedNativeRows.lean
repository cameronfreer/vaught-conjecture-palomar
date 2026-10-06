/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedCutTransport

/-! # Native higher-owner columns on the installed growth tower

The catalogue member at the owner's birth determines its entire padded table.
These are native row identities, not recognition assumptions or equalities
between independently selected renderings. The shadow maximum calculation
follows the grade-two calculation in V-C's GrowthLeafRecognition.
-/
@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedNativeRows
open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

/-- An actual leaf in its native build. -/
def owner : (t : ℕ) → (ht : t + 2 ≤ A.card) → Catalogue X (t + 2) →
    Cell (build I X T hA hB hC t ht).carrier
  | 0, _, a => GrowthPaddedSuccessor.leaf I X T hA hB hC a
  | t + 1, _, a => (GrowthPaddedStepRows.controller
      (build I X T hA hB hC t (by omega)) (by omega) a).1

def source : (t : ℕ) → (ht : t + 2 ≤ A.card) → Catalogue X (t + 2) →
    Cell (build I X T hA hB hC t ht).carrier → ExtOrd
  | 0, _, a => GrowthPaddedSuccessor.source I X T hA hB hC a
  | t + 1, _, a => GrowthPaddedStepRows.source
      (build I X T hA hB hC t (by omega)) (by omega) (by omega) a

def anchor : (t : ℕ) → (ht : t + 2 ≤ A.card) → Catalogue X (t + 2) → Catalogue X 1
  | 0, _, a => GrowthPaddedSuccessor.baseAnchor X a
  | t + 1, _, a => GrowthPaddedStepSupply.birth
      (build I X T hA hB hC t (by omega)) a

def ceiling (t : ℕ) : ExtOrd := CanonicalFieldLayer.ceiling (t + 2)
  (Field I.right.scheme I.left.scheme)

theorem owner_index (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2)) :
    (build I X T hA hB hC t ht).carrier.cell (owner I X T hA hB hC t ht a) =
      (A, t + 2) := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.leaf_index I X T hA hB hC a
  | succ t => exact (GrowthPaddedStepRows.controller _ _ a).2

theorem owner_row (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (d : (build I X T hA hB hC t ht).carrier.below
      ((build I X T hA hB hC t ht).carrier.cell (owner I X T hA hB hC t ht a))) :
    (build I X T hA hB hC t ht).rows.E (owner I X T hA hB hC t ht a) d =
      source I X T hA hB hC t ht a d.1 := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.leaf_row I X T hA hB hC a d
  | succ t => exact ScopedSourcePrefixLayer.Data.row_new _ _ d

theorem anchor_ranks (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (f : Field I.right.scheme I.left.scheme) :
    RelativeLadderLayer.ranks (fields X 1) (anchor I X T hA hB hC t ht a) f =
      LadderScalarRendering.fieldRank (fields X (t + 2) a) f := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.baseAnchor_ranks X a f
  | succ t => exact GrowthPaddedStepSupply.birth_ranks _ a f

/-- The complete table, including unused ranks and every foreign shadow. -/
theorem source_base (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (d : Cell (base I X T hA hB hC)) :
    source I X T hA hB hC t ht a ((build I X T hA hB hC t ht).baseMap d) =
      RelativeLadderLayer.renderWith I.boundary (by omega : 0 < A.card)
        (field I) (fields X 1) (anchor I X T hA hB hC t ht a)
        (fields X (t + 2) a) (ceiling I t) d := by
  cases t with
  | zero => exact LadderWeightedSuccessor.Input.source_old _ a d
  | succ t => exact GrowthPaddedStepSupply.source_base _ _ _ a d

theorem source_bound (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (d : Cell (build I X T hA hB hC t ht).carrier) :
    source I X T hA hB hC t ht a d ≤ ceiling I t := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.source_bound I X T hA hB hC a d
  | succ t => exact GrowthPaddedStepRows.source_bound _ _ _ a d

theorem source_diagonal (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2)) :
    source I X T hA hB hC t ht a (owner I X T hA hB hC t ht a) =
      ceiling I t := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.source_ceiling I X T hA hB hC a
  | succ t => exact ScopedSourcePrefixLayer.Data.profile_diagonal _ _

theorem source_lawful (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2)) :
    RespectsSemanticsBelow (build I X T hA hB hC t ht).rows (A, t + 2)
      (fun d => source I X T hA hB hC t ht a d.1) := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.source_lawful I X T hA hB hC a
  | succ t => exact GrowthPaddedStepRows.source_lawful _ _ _ a

theorem source_original (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (d : Cell I.boundary) :
    source I X T hA hB hC t ht a ((build I X T hA hB hC t ht).baseMap
      (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)) =
        fields X (t + 2) a (field I d) := by
  rw [source_base]
  exact RelativeLadderLayer.renderWith_old _ _ _ _ _ _ _ (anchor_ranks I X T hA hB hC t ht a) d

abbrev ladder (t : ℕ) (ht : t + 2 ≤ A.card)
    (v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1)) :=
  (build I X T hA hB hC t ht).baseMap
    (RelativeLadderLayer.added I.boundary (by omega : 0 < A.card) v)

theorem ladder_index (t : ℕ) (ht : t + 2 ≤ A.card)
    (v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1)) :
    (build I X T hA hB hC t ht).carrier.cell (ladder I X T hA hB hC t ht v) = (A, 1) := by
  rw [ladder, Layer.base_index, RelativeLadderLayer.added_index]

theorem source_ladder (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1)) :
    source I X T hA hB hC t ht a (ladder I X T hA hB hC t ht v) =
      SupportLadderRows.image (RelativeLadderLayer.ranks (fields X 1))
        (anchor I X T hA hB hC t ht a)
        (LadderScalarRendering.level (LadderScalarRendering.values (fields X (t + 2) a))
          (ceiling I t)) v := by
  rw [ladder, source_base]
  change RelativeLadderLayer.image _ _ _ _ _ _ (RelativeLadderLayer.added _ _ v) = _
  rw [RelativeLadderLayer.image, RelativeLadderLayer.rankIndex_added]
  rfl

theorem source_shadow_birth (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (f : Field I.right.scheme I.left.scheme) :
    source I X T hA hB hC t ht a (ladder I X T hA hB hC t ht
      (SupportLadderRows.shadow (anchor I X T hA hB hC t ht a) f)) =
        fields X (t + 2) a f := by
  rw [source_ladder, SupportLadderRows.image]
  have he : SupportLadderRows.index (H := RelativeLadderLayer.rungs
      (X := Field I.right.scheme I.left.scheme)) (RelativeLadderLayer.ranks (fields X 1))
      (anchor I X T hA hB hC t ht a)
      (SupportLadderRows.shadow (anchor I X T hA hB hC t ht a) f) =
        RelativeLadderLayer.ranks (fields X 1) (anchor I X T hA hB hC t ht a) f := by
    change min (FiniteProfileControllers.cut _
      (RelativeLadderLayer.ranks (fields X 1) (anchor I X T hA hB hC t ht a))
      (RelativeLadderLayer.ranks (fields X 1) (anchor I X T hA hB hC t ht a))) _ = _
    rw [FiniteProfileControllers.cut_refl]
    exact min_eq_right (le_of_lt (RelativeLadderLayer.rank_bound _ _ _))
  unfold ceiling
  rw [he, anchor_ranks, LadderScalarRendering.field_readback]

/-- Complete fields, including hidden/future fields, are actual shadow maxima. -/
theorem source_shadow_sup (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (f : Field I.right.scheme I.left.scheme) :
    (Finset.univ : Finset (Catalogue X 1)).sup (fun b =>
      source I X T hA hB hC t ht a
        (ladder I X T hA hB hC t ht (SupportLadderRows.shadow b f))) =
          fields X (t + 2) a f := by
  classical
  have he := SupportLadderRows.readout_image
    (H := RelativeLadderLayer.rungs (X := Field I.right.scheme I.left.scheme))
    (fun b f => le_of_lt (RelativeLadderLayer.rank_bound (fields X 1) b f))
    (anchor I X T hA hB hC t ht a)
    (LadderScalarRendering.level_mono (LadderScalarRendering.values_bound (anchor_bound X a))) f
  simp only [SupportLadderRows.readout] at he
  rw [show Fintype.ofFinite (Catalogue X 1) = (inferInstance : Fintype (Catalogue X 1))
    from Subsingleton.elim _ _] at he
  simp only [source_ladder]
  unfold ceiling
  rw [he, anchor_ranks, LadderScalarRendering.field_readback]

theorem source_spare (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2)) :
    source I X T hA hB hC t ht a (ladder I X T hA hB hC t ht
      (SupportLadderRows.leaf (by exact Nat.succ_pos _) (anchor I X T hA hB hC t ht a))) =
        ceiling I t := by
  rw [source_ladder, SupportLadderRows.image]
  have he := SupportLadderRows.index_leaf (profile := RelativeLadderLayer.ranks (fields X 1))
    (show 0 < RelativeLadderLayer.rungs (X := Field I.right.scheme I.left.scheme)
      from Nat.succ_pos _) (anchor I X T hA hB hC t ht a) (anchor I X T hA hB hC t ht a)
  rw [FiniteProfileControllers.cut_refl] at he
  exact (congrArg (LadderScalarRendering.level
    (LadderScalarRendering.values (fields X (t + 2) a)) (ceiling I t)) he).trans (by
    rw [LadderScalarRendering.level]
    apply ite_eq_left
    exact lt_of_le_of_lt (LadderScalarRendering.values_card_le (fields X (t + 2) a))
      (Nat.lt_succ_self _))

/-- Every earlier grade has a real ceiling occurrence in this native row.
The lower renderer is invoked with this row's fixed outer grid and ceiling. -/
theorem source_ceiling_at (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (i : ℕ) (hi : 1 ≤ i) (hit : i ≤ t + 2) :
    ∃ c : Cell (build I X T hA hB hC t ht).carrier,
      (build I X T hA hB hC t ht).carrier.cell c = (A, i) ∧
        source I X T hA hB hC t ht a c = ceiling I t := by
  by_cases he : i = t + 2
  · subst i
    exact ⟨_, owner_index I X T hA hB hC t ht a, source_diagonal I X T hA hB hC t ht a⟩
  cases t with
  | zero =>
    have hie : i = 1 := by omega
    subst i
    exact ⟨_, ladder_index I X T hA hB hC 0 ht _, source_spare I X T hA hB hC 0 ht a⟩
  | succ t =>
    let P := build I X T hA hB hC t (by omega)
    obtain ⟨c, hc, hv⟩ := P.ceiling_at (Nat.le_succ (t + 2))
      (state X a) (state_admitted X a) (state_proper X a)
      (G := GrowthPaddedStepRows.grid P) (H := GrowthPaddedStepRows.ceiling P)
      (fun _ hz => (PairedSlotComparison.sourceGrid_visible hz).mono (Nat.le_succ _))
      ((PairedSlotComparison.sourceGrid_visible
        (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.le_succ _))
      (fun f => by rw [state_profile]; exact anchor_bound X a f) i hi (by omega)
    refine ⟨GrowthPaddedStepRows.old P (by omega) c,
      (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans hc, ?_⟩
    change GrowthPaddedStepRows.source P _ _ a (GrowthPaddedStepRows.old P _ c) = _
    rw [GrowthPaddedStepRows.source_old]
    exact hv

end
end VaughtConjecture.Knight.GrowthPaddedNativeRows
