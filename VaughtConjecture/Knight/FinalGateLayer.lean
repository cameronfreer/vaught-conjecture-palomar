/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WeightedSourcePrefixLayer
public import VaughtConjecture.Knight.SeparatedSourceLayerCarrier

/-! # A physical final-grade gate layer

Install two distinct full-scope occurrences per source: a ceiling leaf and a
marked node weighted by the source's gate field. The gate field participates in
the comparison cut. Its value must be visible at the installed grade, not merely
at grade one. The parent exists even when the marked weight is bottom.

This is the weighted final layer of new31 / `uniform_upper_receiving`, built on
the actual ordered source-layer carrier using KVC's weighted installer. Lawful
predecessor sources and their common-grid agreement are inputs; this file does
not construct the ordinary scope recursion, an admitted catalogue, or lifting.
No shortness condition is imposed on inherited rows.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.FinalGateLayer
open Transform Value ExtOrd SourcePrefixRows SourcePrefixLayer
noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]
variable {A : Finset ι} {D : CellScheme A} {N : ℕ}

/-- The predecessor data consumed by the actual weighted installation. -/
structure Input (D : CellScheme A) (N : ℕ) (X Q : Type*) where
  sem : Semantics D
  positive : 0 < N
  height : N ≤ A.card
  separated : ∀ d : Cell D, ¬ GradedLe (A, N) (D.cell d)
  fields : Q → X → ExtOrd
  gate : X
  grid : Finset ExtOrd
  bot_mem : ⊥ ∈ grid
  ceiling : ExtOrd
  ceiling_mem : ceiling ∈ grid
  grid_bound : ∀ h ∈ grid, h ≤ ceiling
  grid_visible : ∀ h ∈ grid, SelfVis N h
  lower : Q → Cell D → ExtOrd
  lower_lawful : ∀ a, RespectsSemanticsBelow sem (A, N) (fun d => lower a d.1)
  lower_bound : ∀ a d, D.grade d ≤ N → lower a d ≤ ceiling
  lower_prefix : ∀ a b h, h ∈ grid → Agree (fields a) (fields b) h →
    ∀ d, D.grade d ≤ N → min (lower a d) h = min (lower b d) h
  gate_visible : ∀ a, SelfVis N (fields a gate)
  gate_bound : ∀ a, fields a gate ≤ ceiling

namespace Input
variable (I : Input D N X Q)

abbrev Node := Q × Bool
abbrev carrier := SourceLayerCarrier.scheme D (Node (Q := Q)) N I.positive I.height
abbrev old (d : Cell D) : Cell I.carrier :=
  SourceLayerCarrier.toCell D (Node (Q := Q)) N I.positive I.height (.inl d)
abbrev added (a : Q) (marked : Bool) : Cell I.carrier :=
  SourceLayerCarrier.toCell D (Node (Q := Q)) N I.positive I.height (.inr (a, marked))
abbrev controller := SeparatedSourceLayerCarrier.controller D (Node (Q := Q))
  N I.positive I.height
abbrev member := (SeparatedSourceLayerCarrier.controllerEquiv D (Node (Q := Q))
  N I.positive I.height I.separated).symm

@[simp] theorem member_controller (a : Q) (marked : Bool) :
    I.member (I.controller (a, marked)) = (a, marked) := Equiv.symm_apply_apply _ _

@[simp] theorem old_index (d : Cell D) : I.carrier.cell (I.old d) = D.cell d :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _

@[simp] theorem added_index (a : Q) (marked : Bool) :
    I.carrier.cell (I.added a marked) = (A, N) :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _

theorem added_ne_old (a : Q) (marked : Bool) (d : Cell D) :
    I.added a marked ≠ I.old d := by
  intro he
  have hi := congrArg I.carrier.cell he
  rw [added_index, old_index] at hi
  exact I.separated d (hi ▸ GradedLe.refl (A, N))

theorem leaf_ne_marked (a : Q) : I.added a false ≠ I.added a true := by
  intro he
  have h := (SourceLayerCarrier.enumeration D (Node (Q := Q)) N I.positive I.height).injective he
  exact Bool.false_ne_true (congrArg Prod.snd (Sum.inr.inj h))

/-- Moving the physical gate to the full scope excludes it from every proper
face prescription, independently of that prescription's grade. -/
theorem added_not_below {S : Finset ι} {k : ℕ} (hS : S ⊆ A) (hne : S ≠ A)
    (a : Q) (marked : Bool) : ¬ GradedLe (I.carrier.cell (I.added a marked)) (S, k) := by
  rw [I.added_index]
  exact fun h => hne (Finset.Subset.antisymm hS h.1)

theorem old_strictMono : StrictMono I.old :=
  SourceLayerCarrier.old_order D (Node (Q := Q)) N I.positive I.height

/-- The old occurrence inventory is exhaustive on every proper scope. -/
theorem proper_occurrence {S : Finset ι} {k : ℕ} (hS : S ⊆ A) (hne : S ≠ A)
    (d : I.carrier.below (S, k)) :
    ∃ x : D.below (S, k), d.1 = I.old x.1 := by
  have hn : I.carrier.cell d.1 ≠ (A, N) := by
    intro he
    exact hne (Finset.Subset.antisymm hS (he ▸ d.2).1)
  obtain ⟨x, hx⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N
    I.positive I.height d.1 hn
  refine ⟨⟨x, ?_⟩, hx⟩
  simpa only [hx, I.old_index] using d.2

def lowerVector (a : Q) (d : Cell I.carrier) : ExtOrd :=
  match SourceLayerCarrier.toOcc D (Node (Q := Q)) N I.positive I.height d with
  | .inl x => I.lower a x
  | .inr _ => ⊥

theorem lowerVector_old (a : Q) (d : Cell D) :
    I.lowerVector a (I.old d) = I.lower a d := by
  simp only [lowerVector, old, SourceLayerCarrier.toOcc_toCell]

def data : ScopedSourcePrefixLayer.Data I.carrier N X where
  base := SeparatedSourceLayerCarrier.base D (Node (Q := Q)) N
    I.positive I.height I.separated I.sem
  separated c hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N
      I.positive I.height c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact I.separated x
  grid := I.grid
  bot_mem := I.bot_mem
  ceiling := I.ceiling
  ceiling_mem := I.ceiling_mem
  grid_bound := I.grid_bound
  grid_visible := I.grid_visible
  boundary q := I.fields (I.member q).1
  lower q := I.lowerVector (I.member q).1
  lower_bound q d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N
      I.positive I.height d hd
    rw [lowerVector_old]
    exact I.lower_bound _ x (by simpa only [CellScheme.grade, old_index] using hg)
  lower_lawful q c hg hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N
      I.positive I.height c hc
    apply (SeparatedSourceLayerCarrier.base_respects_iff D (Node (Q := Q)) N
      I.positive I.height I.separated I.sem x _).mpr
    have hx : GradedLe (D.cell x) (A, N) :=
      ⟨D.isPlan.subset_of_mem (D.scope_mem_plan x), by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell,
          SourceLayerCarrier.index] using hg⟩
    simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
      lowerVector_old, CellScheme.below.mono] using (I.lower_lawful _).mono hx
  grid_agreement p q h hh hag d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N
      I.positive I.height d hd
    simpa only [lowerVector_old] using I.lower_prefix _ _ h hh hag x
      (by simpa only [CellScheme.grade, old_index] using hg)

def nodeWeight (v : Node (Q := Q)) : ExtOrd :=
  if v.2 then I.fields v.1 I.gate else I.ceiling
def weight (q : Controller I.carrier N) : ExtOrd := I.nodeWeight (I.member q)

theorem weight_visible (q : Controller I.carrier N) : SelfVis N (I.weight q) := by
  unfold weight nodeWeight
  split
  · exact I.gate_visible _
  · exact I.grid_visible _ I.ceiling_mem

theorem weight_bound (q : Controller I.carrier N) : I.weight q ≤ I.ceiling := by
  unfold weight nodeWeight
  split
  · exact I.gate_bound _
  · exact le_rfl

theorem weight_kind (q : Controller I.carrier N) :
    I.weight q = I.data.ceiling ∨ ∃ x, I.weight q = I.data.boundary q x := by
  unfold weight nodeWeight
  split
  · exact Or.inr ⟨I.gate, rfl⟩
  · exact Or.inl rfl

theorem parent (q : Controller I.carrier N) :
    ∃ p, I.data.boundary p = I.data.boundary q ∧ I.weight p = I.data.ceiling := by
  refine ⟨I.controller ((I.member q).1, false), ?_, ?_⟩
  · change I.fields (I.member (I.controller _)).1 = _
    rw [member_controller]
    rfl
  · simp only [weight, member_controller, nodeWeight, Bool.false_eq_true, ↓reduceIte]
    rfl

abbrev rows := WeightedSourcePrefixLayer.rows I.data I.weight I.weight_visible
abbrev source (a : Q) :=
  WeightedSourcePrefixLayer.master I.data I.weight (I.controller (a, false))

theorem source_lawful (a : Q) : RespectsSemanticsBelow I.rows (A, N)
    (fun d => I.source a d.1) :=
  WeightedSourcePrefixLayer.master_respects I.data I.weight I.weight_visible I.parent _

theorem source_old (a : Q) (d : Cell D) : I.source a (I.old d) = I.lower a d := by
  rw [source, WeightedSourcePrefixLayer.master_old _ _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ I.separated d)]
  change I.lowerVector (I.member (I.controller (a, false))).1 (I.old d) = _
  rw [member_controller, lowerVector_old]

theorem source_added (a b : Q) (marked : Bool) :
    I.source a (I.added b marked) =
      min (cut I.grid (I.fields a) (I.fields b)) (I.nodeWeight (b, marked)) := by
  rw [source, show I.added b marked = (I.controller (b, marked)).1 from rfl,
    WeightedSourcePrefixLayer.master_new]
  simp only [data, weight, member_controller]

theorem source_marked (a b : Q) : I.source a (I.added b true) =
    min (I.fields a I.gate) (cut I.grid (I.fields a) (I.fields b)) := by
  rw [source_added]
  change min (cut I.grid (I.fields a) (I.fields b)) (I.fields b I.gate) = _
  rw [min_comm]
  exact (agree_cut I.bot_mem _ _ I.gate).symm

theorem source_marked_le (a b : Q) : I.source a (I.added b true) ≤ I.fields a I.gate := by
  rw [source_marked]
  exact min_le_left _ _

theorem source_own_marked (a : Q) : I.source a (I.added a true) = I.fields a I.gate := by
  rw [source_marked, cut_refl I.ceiling_mem I.grid_bound, min_eq_left (I.gate_bound a)]

theorem source_own_leaf (a : Q) : I.source a (I.added a false) = I.ceiling := by
  rw [source_added, cut_refl I.ceiling_mem I.grid_bound]
  exact min_self _

theorem source_bound (a : Q) (d : Cell I.carrier) (hd : I.carrier.grade d ≤ N) :
    I.source a d ≤ I.ceiling :=
  WeightedSourcePrefixLayer.master_bound I.data I.weight _ d hd

theorem leaf_row (a : Q) (d : I.carrier.below (I.carrier.cell (I.added a false))) :
    I.rows.E (I.added a false) d = I.source a d.1 := by
  have hw : I.weight (I.controller (a, false)) = I.ceiling := by
    simp only [weight, member_controller, nodeWeight, Bool.false_eq_true, ↓reduceIte]
  exact (WeightedSourcePrefixLayer.row_new I.data I.weight I.weight_visible
    (I.controller (a, false)) d).trans (by
      rw [hw, min_eq_left]
      exact I.source_bound a d.1
        (by simpa only [CellScheme.grade, added_index] using d.2.2))

/-- Neither a zero weight nor equality of weights identifies the two cells. -/
theorem node_diagonal (a : Q) (marked : Bool) :
    I.rows.E (I.added a marked) ⟨I.added a marked, GradedLe.refl _⟩ =
      I.nodeWeight (a, marked) := by
  have h := WeightedSourcePrefixLayer.diagonal I.data I.weight I.weight_visible I.weight_bound
    (I.controller (a, marked))
  exact h.trans (congrArg I.nodeWeight (I.member_controller a marked))

theorem source_supported
    (hlower : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd) (I.fields a) (I.lower a d))
    (a : Q) (d : Cell I.carrier) (hd : I.carrier.grade d ≤ N) :
    OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd) (I.fields a) (I.source a d) := by
  have h := WeightedSourcePrefixLayer.master_supported I.data I.weight I.weight_visible
    I.weight_kind (fun q d hg hn => ?_) (I.controller (a, false)) d hd
  · simpa only [source, data, member_controller] using h
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N
      I.positive I.height d hn
    change OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd)
      (I.fields (I.member q).1) (I.lowerVector _ (I.old x))
    rw [lowerVector_old]
    exact hlower _ x (by simpa only [CellScheme.grade, old_index] using hg)

theorem source_prefix (a b : Q) {h : ExtOrd} (hh : h ∈ I.grid)
    (hag : Agree (I.fields a) (I.fields b) h) :
    Agree (fun d : I.carrier.below (A, N) => I.source a d.1)
      (fun d => I.source b d.1) h := by
  apply WeightedSourcePrefixLayer.master_prefix I.data I.weight hh
  simpa only [data, member_controller] using hag

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    I.rows.E (I.old c) (SeparatedSourceLayerCarrier.ownerEquiv D (Node (Q := Q))
      N I.positive I.height I.separated c d) = I.sem.E c d := by
  rw [WeightedSourcePrefixLayer.row_old _ _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ I.separated c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ I.separated _ c d

theorem consistent (hs : I.sem.IsConsistent) : I.rows.IsConsistent := by
  apply WeightedSourcePrefixLayer.consistent I.data I.weight I.weight_visible I.parent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N
    I.positive I.height c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff D (Node (Q := Q)) N
    I.positive I.height I.separated I.sem x _).mpr
  simpa only [Function.comp_def, data, SeparatedSourceLayerCarrier.base_old] using hs x

end Input
end
end VaughtConjecture.Knight.FinalGateLayer
