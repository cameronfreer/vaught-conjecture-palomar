/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingCatalogueIncidences

/-! # Actual mixed-index availability witnesses

The spare terminal rung reaches the reserved ceiling. Parent leaves therefore
dominate every coordinate of a weighted upper row. The witnesses below are
actual occurrences inside the requested lower domain, at either mixed scope.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingCatalogueAvailability
open Transform Value ExtOrd CappedDonor CappedDonor.Ref ReceivingLadderCarrier
open ReceivingCatalogueSources
noncomputable section

variable {I : Type*} [Fintype I] {nP K : ℕ} {P : SemScheme (nP + 1)}
  {C : SemScheme 2} {R : Ref I nP 2 2 P C} (L : R.LowRef K)
  (hC : C.scheme.plan = privatePlan) (request : Cell P.scheme)

local notation "D" => carrier L hC
local notation "H" => ReceivingCatalogueSources.ceiling (P := P) (C := C)
local notation "G" => grid (P := P) (C := C)
local notation "T" => SupportLadderRows.Point (rungs (P := P) (C := C))
  (TField P C) (Controller L)

abbrev upperRow (a : Controller L) (node : Bool) : Cell D → ExtOrd :=
  ReceivingLadderUpperRows.row C.scheme hC privateField (.field (.req request))
    (high (R := R)) (ranks L) (fields L) id G H a node

def terminal (a : Controller L) : T :=
  SupportLadderRows.leaf (show 0 < rungs (P := P) (C := C) from Nat.succ_pos _) a

theorem terminal_source (a : Controller L) (b : Bool) :
    source L hC request a (added C.scheme hC (.ladder b (terminal L a))) = H := by
  simp only [source, ReceivingLadderSources.source_ladder, LadderScalarRendering.render,
    SupportLadderRows.image, id_eq, terminal]
  rw [SupportLadderRows.index_leaf, FiniteProfileControllers.cut_refl]
  apply ite_eq_left
  exact Nat.lt_succ_of_le (LadderScalarRendering.values_card_le (fields L a))

theorem upper_terminal (a : Controller L) (node b : Bool) :
    upperRow L hC request a node (added C.scheme hC (.ladder b (terminal L a))) =
      ReceivingLadderUpperRows.weight (high (R := R)) (fields L) H a node := by
  change min (source L hC request a _) _ = _
  rw [terminal_source]
  exact min_eq_right (ReceivingLadderUpperRows.weight_le (high (R := R)) (fields L) H
    (fields_bound L) a node)

theorem upper_parent (a : Controller L) (node b : Bool) :
    upperRow L hC request a node (added C.scheme hC (.upper b a false)) =
      ReceivingLadderUpperRows.weight (high (R := R)) (fields L) H a node :=
  ReceivingLadderUpperRows.parent_read C.scheme hC privateField (.field (.req request))
    (high (R := R)) (ranks L) (fields L) id G H ceiling_mem (fun _ => grid_bound)
    (fields_bound L) a node b

/-- Grade-one mixed availability for a weighted upper row, with the spare
rung as the explicit witness in the actual owner domain. -/
theorem upper_available_one (a : Controller L) (node full b : Bool)
    (hs : scope b ⊆ scope full)
    (d : (D).below ((D).cell (added C.scheme hC (.upper full a node)))) :
    ∃ e : (D).below ((D).cell (added C.scheme hC (.upper full a node))),
      (D).cell e.1 = (scope b, 1) ∧
      upperRow L hC request a node d.1 ≤ upperRow L hC request a node e.1 := by
  refine ⟨⟨added C.scheme hC (.ladder b (terminal L a)), ?_⟩, added_index _ _ _, ?_⟩
  · rw [added_index, added_index]
    exact ⟨hs, by change 1 ≤ 2; omega⟩
  · rw [upper_terminal]
    exact min_le_right _ _

/-- Grade-two mixed availability, with the same profile's leaf, not an
assumed active controller and not a maximum of numerical readouts. -/
theorem upper_available_two (a : Controller L) (node full b : Bool)
    (hs : scope b ⊆ scope full)
    (d : (D).below ((D).cell (added C.scheme hC (.upper full a node)))) :
    ∃ e : (D).below ((D).cell (added C.scheme hC (.upper full a node))),
      (D).cell e.1 = (scope b, 2) ∧
      upperRow L hC request a node d.1 ≤ upperRow L hC request a node e.1 := by
  refine ⟨⟨added C.scheme hC (.upper b a false), ?_⟩, added_index _ _ _, ?_⟩
  · rw [added_index, added_index]
    exact ⟨hs, le_rfl⟩
  · rw [upper_parent]
    exact min_le_right _ _

theorem ladder_terminal (v : T) (b : Bool) :
    ladderRow (U := Controller L) C.scheme hC privateField (.field (.req request))
      (ranks L) v (added C.scheme hC (.ladder b (terminal L (SupportLadderRows.parent v)))) =
      SupportLadderRows.source (SupportLadderRows.ceiling (ranks L) v)
        (rungs (P := P) (C := C)) := by
  rw [ladderRow_ladder]
  simp only [SupportLadderRows.row, terminal]
  rw [SupportLadderRows.index_leaf, FiniteProfileControllers.cut_refl]

/-- Every lower row has its own parent terminal rung in each permitted
mixed lower domain, including shadows of rank zero. -/
theorem ladder_available (v : T) (full b : Bool) (hs : scope b ⊆ scope full)
    (d : (D).below ((D).cell (added C.scheme hC (.ladder full v)))) :
    ∃ e : (D).below ((D).cell (added C.scheme hC (.ladder full v))),
      (D).cell e.1 = (scope b, 1) ∧
      ladderRow C.scheme hC privateField (.field (.req request)) (ranks L) v d.1 ≤
        ladderRow C.scheme hC privateField (.field (.req request)) (ranks L) v e.1 := by
  refine ⟨⟨added C.scheme hC (.ladder b (terminal L (SupportLadderRows.parent v))), ?_⟩,
    added_index _ _ _, ?_⟩
  · rw [added_index, added_index]
    exact ⟨hs, le_rfl⟩
  · rw [ladder_terminal]
    apply (SupportLadderRows.source_le_iff _ _ _).mpr
    have ht := SupportLadderRows.ceiling_le (fun a f => (rank_bound L a f).le) v
    rw [min_eq_right ht]
    exact min_le_right _ _

/-- Availability at inherited indices is supplied by the admitted private
section, and the witness remains in the actual upper owner's lower domain. -/
theorem upper_available_old (a : Controller L) (node full : Bool)
    (d e : Cell C.scheme) (hs : C.scheme.scope d ⊆ C.scheme.scope e)
    (hg : C.scheme.grade d = C.scheme.grade e)
    (he : GradedLe ((D).cell (old C.scheme hC e))
      ((D).cell (added C.scheme hC (.upper full a node)))) :
    ∃ w : (D).below ((D).cell (added C.scheme hC (.upper full a node))),
      (D).cell w.1 = (D).cell (old C.scheme hC e) ∧
      upperRow L hC request a node (old C.scheme hC d) ≤
        upperRow L hC request a node w.1 := by
  obtain ⟨c, hc, hle⟩ := (private_lawful L a).availability d e hs hg
  have hi : (D).cell (old C.scheme hC c) = (D).cell (old C.scheme hC e) := by
    simp only [old_index, CellScheme.scope, CellScheme.grade, hc]
  refine ⟨⟨old C.scheme hC c, hi.symm ▸ he⟩, hi, ?_⟩
  simpa only [upperRow, ReceivingLadderUpperRows.row, ReceivingLadderSources.source_old] using
    min_le_min_right (ReceivingLadderUpperRows.weight (high (R := R)) (fields L) H a node) hle

/-- The same original availability witness survives rank compression, with
no requirement that different original readings be identified. -/
theorem ladder_available_old (v : T) (full : Bool)
    (d e : Cell C.scheme) (hs : C.scheme.scope d ⊆ C.scheme.scope e)
    (hg : C.scheme.grade d = C.scheme.grade e)
    (he : GradedLe ((D).cell (old C.scheme hC e))
      ((D).cell (added C.scheme hC (.ladder full v)))) :
    ∃ w : (D).below ((D).cell (added C.scheme hC (.ladder full v))),
      (D).cell w.1 = (D).cell (old C.scheme hC e) ∧
      ladderRow (U := Controller L) C.scheme hC privateField (.field (.req request)) (ranks L) v
        (old C.scheme hC d) ≤
      ladderRow C.scheme hC privateField (.field (.req request)) (ranks L) v w.1 := by
  obtain ⟨c, hc, hle⟩ := (private_lawful L (SupportLadderRows.parent v)).availability d e hs hg
  have hi : (D).cell (old C.scheme hC c) = (D).cell (old C.scheme hC e) := by
    simp only [old_index, CellScheme.scope, CellScheme.grade, hc]
  refine ⟨⟨old C.scheme hC c, hi.symm ▸ he⟩, hi, ?_⟩
  simp only [ladderRow_old]
  exact (SupportLadderRows.source_mono _)
    (LadderScalarRendering.rank_mono
      (LadderScalarRendering.values (fields L (SupportLadderRows.parent v))) hle)

end
end VaughtConjecture.Knight.ReceivingCatalogueAvailability
