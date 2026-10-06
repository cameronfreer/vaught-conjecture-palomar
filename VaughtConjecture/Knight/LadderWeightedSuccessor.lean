/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLadderRankRendering
public import VaughtConjecture.Knight.WeightedSourcePrefixLayer

/-! # A weighted grade-two successor of the installed ladder

The scalar input distinguishes retained birth-grade anchors from upper sources.
Only an upper source must have a lawful grade-two original restriction. Physical
predecessor lawfulness, bounds and prefix equations are constructed from the
grade-one renderer, including all unused rungs and shadows. Every weighted node
has a separately installed ceiling parent, including nodes of weight bottom.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LadderWeightedSuccessor
open Transform Value ExtOrd SourcePrefixRows SourcePrefixLayer
noncomputable section
variable {ι X Q U V : Type*} [DecidableEq ι]
  [Fintype X] [Fintype Q] [Fintype U] [Fintype V] {A : Finset ι}

/-- Only original scalar conditions are supplied. None of the physical
predecessor receipts consumed by the weighted installer is a field. -/
structure Input (D : CellScheme A) where
  sem : Semantics D
  proper : ∀ d : Cell D, D.scope d ≠ A
  height : 2 ≤ A.card
  field : Cell D → X
  fields : Q → X → ExtOrd
  birth : ∀ a, RespectsSemanticsBelow sem (A, 1) (fun d => fields a (field d.1))
  anchor : U → Q
  upper : U → X → ExtOrd
  rank_match : ∀ u x, RelativeLadderLayer.ranks fields (anchor u) x =
    LadderScalarRendering.fieldRank (upper u) x
  incoming : ∀ u, RespectsSemanticsBelow sem (A, 2) (fun d => upper u (field d.1))
  visible : ∀ u x, SelfVis 1 (upper u x)
  grid : Finset ExtOrd
  bot_mem : ⊥ ∈ grid
  ceiling : ExtOrd
  ceiling_mem : ceiling ∈ grid
  grid_bound : ∀ h ∈ grid, h ≤ ceiling
  grid_visible : ∀ h ∈ grid, SelfVis 2 h
  bounded : ∀ u x, upper u x ≤ ceiling
  nodeField : V → X
  node_visible : ∀ u v, SelfVis 2 (upper u (nodeField v))

namespace Input
variable {D : CellScheme A} (I : Input (X := X) (Q := Q) (U := U) (V := V) D)

abbrev one : 0 < A.card := lt_of_lt_of_le (by decide : 0 < 2) I.height
abbrev lower := RelativeLadderLayer.carrier D I.one (X := X) (Q := Q)
abbrev lowerRows := RelativeLadderLayer.rows D I.sem I.one I.field I.fields I.proper
abbrev Node := U × Option V
abbrev carrier := SourceLayerCarrier.scheme I.lower (Node (U := U) (V := V)) 2
  (by decide) I.height
abbrev old (d : Cell I.lower) : Cell I.carrier :=
  SourceLayerCarrier.toCell I.lower (Node (U := U) (V := V)) 2 (by decide) I.height (.inl d)
abbrev added (v : Node (U := U) (V := V)) : Cell I.carrier :=
  SourceLayerCarrier.toCell I.lower (Node (U := U) (V := V)) 2 (by decide) I.height (.inr v)

omit [Fintype U] [Fintype V] in
theorem separation (d : Cell I.lower) : ¬ GradedLe (A, 2) (I.lower.cell d) := by
  rcases RelativeLadderLayer.cell_cases D I.one d with ⟨x, rfl⟩ | ⟨v, rfl⟩
  · rw [RelativeLadderLayer.old_index]
    exact SeparatedSourceLayerCarrier.separated_of_proper D 2 I.proper x
  · rw [RelativeLadderLayer.added_index]
    exact fun h => (by omega : ¬ 2 ≤ 1) h.2

abbrev controller := SeparatedSourceLayerCarrier.controller I.lower (Node (U := U) (V := V))
  2 (by decide) I.height
abbrev member := (SeparatedSourceLayerCarrier.controllerEquiv I.lower (Node (U := U) (V := V))
  2 (by decide) I.height I.separation).symm
@[simp] theorem member_controller (v : Node (U := U) (V := V)) :
    I.member (I.controller v) = v := Equiv.symm_apply_apply _ v

def predecessor (u : U) : Cell I.lower → ExtOrd :=
  RelativeLadderLayer.renderWith D I.one I.field I.fields (I.anchor u) (I.upper u) I.ceiling

omit [Fintype U] [Fintype V] in
theorem predecessor_lawful (u : U) : RespectsSemanticsBelow I.lowerRows (A, 2)
    (fun d => I.predecessor u d.1) :=
  RelativeLadderLayer.renderWith_respects D I.sem I.one I.field I.fields I.proper _ _
    (I.rank_match u) (I.bounded u) (I.visible u)
    ((I.grid_visible _ I.ceiling_mem).mono (by decide)) (I.incoming u)

omit [Fintype U] [Fintype V] in
theorem predecessor_bound (u : U) (d : Cell I.lower) : I.predecessor u d ≤ I.ceiling :=
  RelativeLadderLayer.renderWith_bound D I.one I.field I.fields _ _ (I.bounded u) d

omit [Fintype U] [Fintype V] in
theorem predecessor_prefix (u v : U) {h : ExtOrd} (hh : h ≤ I.ceiling)
    (hag : Agree (I.upper u) (I.upper v) h) (d : Cell I.lower) :
    min (I.predecessor u d) h = min (I.predecessor v d) h :=
  RelativeLadderLayer.renderWith_agreement D I.one I.field I.fields
    (I.rank_match u) (I.rank_match v) (I.bounded u) (I.bounded v) hh hag d

def lowerVector (u : U) (d : Cell I.carrier) : ExtOrd :=
  match SourceLayerCarrier.toOcc I.lower (Node (U := U) (V := V)) 2 (by decide) I.height d with
  | .inl x => I.predecessor u x
  | .inr _ => ⊥

theorem lowerVector_old (u : U) (d : Cell I.lower) :
    I.lowerVector u (I.old d) = I.predecessor u d := by
  simp only [lowerVector, old, SourceLayerCarrier.toOcc_toCell]

def data : ScopedSourcePrefixLayer.Data I.carrier 2 X where
  base := SeparatedSourceLayerCarrier.base I.lower (Node (U := U) (V := V)) 2
    (by decide) I.height I.separation I.lowerRows
  separated c hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower (Node (U := U) (V := V))
      2 (by decide) I.height c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact I.separation x
  grid := I.grid
  bot_mem := I.bot_mem
  ceiling := I.ceiling
  ceiling_mem := I.ceiling_mem
  grid_bound := I.grid_bound
  grid_visible := I.grid_visible
  boundary q := I.upper (I.member q).1
  lower q := I.lowerVector (I.member q).1
  lower_bound q d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower (Node (U := U) (V := V))
      2 (by decide) I.height d hd
    rw [lowerVector_old]
    exact I.predecessor_bound _ x
  lower_lawful q c hg hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower (Node (U := U) (V := V))
      2 (by decide) I.height c hc
    apply (SeparatedSourceLayerCarrier.base_respects_iff I.lower (Node (U := U) (V := V))
      2 (by decide) I.height I.separation I.lowerRows x _).mpr
    change RespectsSemanticsBelow I.lowerRows _ (fun d => I.lowerVector _ (I.old d.1))
    have hx : GradedLe (I.lower.cell x) (A, 2) :=
      ⟨I.lower.isPlan.subset_of_mem (I.lower.scope_mem_plan x), by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell,
          SourceLayerCarrier.index] using hg⟩
    simpa only [lowerVector_old, CellScheme.below.mono] using (I.predecessor_lawful _).mono hx
  grid_agreement p q h hh hag d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower (Node (U := U) (V := V))
      2 (by decide) I.height d hd
    simpa only [lowerVector_old] using I.predecessor_prefix _ _ (I.grid_bound h hh) hag x

def nodeWeight (v : Node (U := U) (V := V)) : ExtOrd :=
  match v.2 with
  | none => I.ceiling
  | some x => I.upper v.1 (I.nodeField x)
def weight (q : Controller I.carrier 2) : ExtOrd := I.nodeWeight (I.member q)

theorem weight_visible (q : Controller I.carrier 2) : SelfVis 2 (I.weight q) := by
  unfold weight nodeWeight
  split
  · exact I.grid_visible _ I.ceiling_mem
  · exact I.node_visible _ _

theorem weight_bound (q : Controller I.carrier 2) : I.weight q ≤ I.ceiling := by
  unfold weight nodeWeight
  split
  · exact le_rfl
  · exact I.bounded _ _

theorem parent (q : Controller I.carrier 2) :
    ∃ p, I.data.boundary p = I.data.boundary q ∧ I.weight p = I.data.ceiling := by
  refine ⟨I.controller ((I.member q).1, none), ?_, ?_⟩
  · change I.upper (I.member (I.controller _)).1 = _
    rw [member_controller]; rfl
  · simp only [weight, member_controller, nodeWeight]; rfl

abbrev rows := WeightedSourcePrefixLayer.rows I.data I.weight I.weight_visible
abbrev source (u : U) := WeightedSourcePrefixLayer.master I.data I.weight (I.controller (u, none))

theorem source_lawful (u : U) : RespectsSemanticsBelow I.rows (A, 2)
    (fun d => I.source u d.1) :=
  WeightedSourcePrefixLayer.master_respects I.data I.weight I.weight_visible I.parent _

theorem inherited_row (c : Cell I.lower) (d : I.lower.below (I.lower.cell c)) :
    I.rows.E (I.old c) (SeparatedSourceLayerCarrier.ownerEquiv I.lower (Node (U := U) (V := V))
      2 (by decide) I.height I.separation c d) = I.lowerRows.E c d := by
  rw [WeightedSourcePrefixLayer.row_old _ _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ I.separation c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ I.separation _ c d

theorem consistent (hs : I.sem.IsConsistent) : I.rows.IsConsistent := by
  apply WeightedSourcePrefixLayer.consistent I.data I.weight I.weight_visible I.parent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower (Node (U := U) (V := V))
    2 (by decide) I.height c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff I.lower (Node (U := U) (V := V))
    2 (by decide) I.height I.separation I.lowerRows x _).mpr
  simpa only [Function.comp_def, data, SeparatedSourceLayerCarrier.base_old] using
    RelativeLadderLayer.consistent D I.sem I.one I.field I.fields I.proper hs I.birth x

theorem source_old (u : U) (d : Cell I.lower) : I.source u (I.old d) = I.predecessor u d := by
  rw [source, WeightedSourcePrefixLayer.master_old _ _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ I.separation d)]
  change I.lowerVector (I.member (I.controller (u, none))).1 (I.old d) = _
  rw [member_controller, lowerVector_old]

theorem source_original (u : U) (d : Cell D) :
    I.source u (I.old (RelativeLadderLayer.old D I.one d)) = I.upper u (I.field d) := by
  rw [source_old]
  exact RelativeLadderLayer.renderWith_old D I.one I.field I.fields _ _ _ (I.rank_match u) d

theorem source_prefix (u v : U) {h : ExtOrd} (hh : h ∈ I.grid)
    (hag : Agree (I.upper u) (I.upper v) h)
    (d : I.carrier.below (A, 2)) : min (I.source u d.1) h = min (I.source v d.1) h := by
  apply WeightedSourcePrefixLayer.master_prefix I.data I.weight hh (q := I.controller (v, none))
    (p := I.controller (u, none)) ?_ d
  change Agree (I.upper (I.member (I.controller _)).1)
    (I.upper (I.member (I.controller _)).1) h
  simpa only [member_controller] using hag

/-- Higher proper original owners retain their own lawful domains. No grade
bound on the entire inherited carrier is used. -/
theorem source_below_lawful {j : ℕ} (u : U)
    (hj : RespectsSemanticsBelow I.sem (A, j)
      (fun d => I.upper u (I.field d.1))) :
    RespectsSemanticsBelow I.rows (A, j) (fun d => I.source u d.1) := by
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  by_cases hc : I.carrier.cell c.1 = (A, 2)
  · exact GradeCutLayerRows.cast_respects I.carrier I.rows hc.symm (I.source_lawful u)
  · obtain ⟨x, hx⟩ := SourceLayerCarrier.old_occurrence I.lower (Node (U := U) (V := V))
      2 (by decide) I.height c.1 hc
    have hxc : GradedLe (I.lower.cell x) (A, j) := by
      simpa only [hx, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using c.2
    rw [hx]
    apply (WeightedSourcePrefixLayer.old_respects_iff I.data I.weight I.weight_visible
      (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ I.separation x)).mpr
    apply (SeparatedSourceLayerCarrier.base_respects_iff I.lower (Node (U := U) (V := V))
      2 (by decide) I.height I.separation I.lowerRows x _).mpr
    have h := (RelativeLadderLayer.renderWith_respects D I.sem I.one I.field I.fields I.proper
      (I.anchor u) (I.upper u) (I.rank_match u) (I.bounded u) (I.visible u)
      ((I.grid_visible _ I.ceiling_mem).mono (by decide : 1 ≤ 2)) hj).mono hxc
    simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
      source_old, predecessor, CellScheme.below.mono] using h

theorem source_bound (u : U) (d : Cell I.carrier) (hd : I.carrier.grade d ≤ 2) :
    I.source u d ≤ I.ceiling :=
  WeightedSourcePrefixLayer.master_bound I.data I.weight _ d hd

theorem node_diagonal (v : Node (U := U) (V := V)) :
    I.rows.E (I.added v) ⟨I.added v, GradedLe.refl _⟩ = I.nodeWeight v := by
  have h := WeightedSourcePrefixLayer.diagonal I.data I.weight I.weight_visible I.weight_bound
    (I.controller v)
  change I.rows.E (I.controller v).1 ⟨(I.controller v).1, GradedLe.refl _⟩ = _
  exact h.trans (congrArg I.nodeWeight (I.member_controller v))

theorem source_parent (u : U) : I.source u (I.added (u, none)) = I.ceiling := by
  change WeightedSourcePrefixLayer.master I.data I.weight (I.controller (u, none))
    (I.controller (u, none)).1 = _
  rw [WeightedSourcePrefixLayer.master_new]
  change min (cut I.grid _ _) (I.weight (I.controller (u, none))) = _
  simp only [data, member_controller, weight, nodeWeight]
  rw [cut_refl I.ceiling_mem I.grid_bound, min_self]

theorem weight_kind (q : Controller I.carrier 2) :
    I.weight q = I.data.ceiling ∨ ∃ x, I.weight q = I.data.boundary q x := by
  unfold weight nodeWeight
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨I.nodeField _, rfl⟩

omit [Fintype U] [Fintype V] in
theorem predecessor_supported (u : U) (d : Cell I.lower) :
    OrbitPrefixSupport.Supported 2 (I.grid : Set ExtOrd) (I.upper u)
      (I.predecessor u d) := by
  rcases RelativeLadderLayer.renderWith_supported D I.one I.field I.fields
      (I.anchor u) (I.upper u) I.ceiling d with hz | ⟨x, hx⟩ | hc
  · exact Or.inl hz
  · rw [show I.predecessor u d = I.upper u x from hx]
    rcases ExtOrd.cases (I.upper u x) with hb | ht | ⟨v, hv⟩
    · exact Or.inl hb
    · exact Or.inr (Or.inr ⟨x, 2, le_rfl, by rw [ht, extVisibilityReplace_top]⟩)
    · by_cases hi : finitePart v < 2
      · exact Or.inr (Or.inr ⟨x, finitePart v, hi.le, by
          rw [hv, extVisibilityReplace_of_finitePart_lt hi, limitPart_add_finitePart]⟩)
      · exact Or.inr (Or.inr ⟨x, 2, le_rfl, by
          rw [hv, extVisibilityReplace_of_le_finitePart (not_lt.mp hi)]⟩)
  · apply Or.inr; apply Or.inl
    change RelativeLadderLayer.renderWith D I.one I.field I.fields _ _ _ _ ∈ I.grid
    rw [hc]; exact I.ceiling_mem

theorem source_supported (u : U) (d : Cell I.carrier) (hd : I.carrier.grade d ≤ 2) :
    OrbitPrefixSupport.Supported 2 (I.grid : Set ExtOrd)
      (I.upper u) (I.source u d) := by
  have h := WeightedSourcePrefixLayer.master_supported I.data I.weight I.weight_visible
    I.weight_kind (fun q d _ hn => ?_) (I.controller (u, none)) d hd
  · simpa only [source, data, member_controller] using h
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower (Node (U := U) (V := V))
      2 (by decide) I.height d hn
    change OrbitPrefixSupport.Supported 2 (I.grid : Set ExtOrd)
      (I.upper (I.member q).1) (I.lowerVector _ (I.old x))
    rw [lowerVector_old]
    exact I.predecessor_supported (I.member q).1 x

theorem source_prefix_all (u v : U) {h : ExtOrd} (hh : h ∈ I.grid)
    (hag : Agree (I.upper u) (I.upper v) h) (d : Cell I.carrier) :
    min (I.source u d) h = min (I.source v d) h := by
  by_cases hd : I.carrier.cell d = (A, 2)
  · exact I.source_prefix u v hh hag ⟨d, hd.symm ▸ GradedLe.refl _⟩
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower (Node (U := U) (V := V))
      2 (by decide) I.height d hd
    rw [source_old, source_old]
    exact I.predecessor_prefix u v (I.grid_bound h hh) hag x

theorem source_supported_all (u : U) (d : Cell I.carrier) :
    OrbitPrefixSupport.Supported 2 (I.grid : Set ExtOrd)
      (I.upper u) (I.source u d) := by
  by_cases hd : I.carrier.cell d = (A, 2)
  · exact I.source_supported u d (by simp only [CellScheme.grade, hd, le_refl])
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower (Node (U := U) (V := V))
      2 (by decide) I.height d hd
    rw [source_old]
    exact I.predecessor_supported u x

theorem source_bound_all (u : U) (d : Cell I.carrier) : I.source u d ≤ I.ceiling := by
  by_cases hd : I.carrier.cell d = (A, 2)
  · exact I.source_bound u d (by simp only [CellScheme.grade, hd, le_refl])
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower (Node (U := U) (V := V))
      2 (by decide) I.height d hd
    rw [source_old]
    exact I.predecessor_bound u x

/-- Literal original rows survive both layers, on the composed actual domains. -/
theorem original_row (c : Cell D) (d : D.below (D.cell c)) :
    I.rows.E (I.old (RelativeLadderLayer.old D I.one c))
      (SeparatedSourceLayerCarrier.ownerEquiv I.lower (Node (U := U) (V := V))
        2 (by decide) I.height I.separation _
        (RelativeLadderLayer.ownerEquiv D I.one I.proper c d)) = I.sem.E c d := by
  rw [I.inherited_row]
  exact RelativeLadderLayer.inherited_row D I.sem I.one I.field I.fields I.proper c d

end Input
end
end VaughtConjecture.Knight.LadderWeightedSuccessor
