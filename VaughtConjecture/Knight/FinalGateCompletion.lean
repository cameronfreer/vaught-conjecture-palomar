/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FinalGateLayer
public import VaughtConjecture.Knight.CanonicalCodingSupport
public import VaughtConjecture.Knight.OrdinaryFinalCatalogue

/-! # Coding and completeness of the actual final gate layer

New weighted rows are coded because every master reading is supported by the
coded original field vector and grid. Old rows remain literal. Completeness
through the final active grade only needs the predecessor's missing-index
ledger, and does not assume that the predecessor is already complete there.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.FinalGateLayer.Input
open Transform Value ExtOrd AmalgamationPlan
noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]
variable {A : Finset ι} {D : CellScheme A} {N : ℕ} (F : Input D N X Q)

theorem node_row (a : Q) (marked : Bool)
    (d : F.carrier.below (F.carrier.cell (F.added a marked))) :
    F.rows.E (F.added a marked) d = min (F.source a d.1) (F.nodeWeight (a, marked)) := by
  have hm : WeightedSourcePrefixLayer.master F.data F.weight (F.controller (a, marked)) d.1 =
      F.source a d.1 := by
    simp only [source, WeightedSourcePrefixLayer.master, ScopedSourcePrefixLayer.Data.profile,
      data, member_controller]
  exact (WeightedSourcePrefixLayer.row_new F.data F.weight F.weight_visible
    (F.controller (a, marked)) d).trans (by
      rw [hm]
      simp only [weight, member_controller])

theorem grade_bound (hD : ∀ d : Cell D, D.grade d ≤ N) :
    ∀ d : Cell F.carrier, F.carrier.grade d ≤ N := by
  intro d
  obtain ⟨x, rfl⟩ := (SourceLayerCarrier.enumeration D (Node (Q := Q)) N
    F.positive F.height).surjective d
  change (F.carrier.cell (SourceLayerCarrier.toCell D (Node (Q := Q)) N
    F.positive F.height x)).2 ≤ N
  rw [SourceLayerCarrier.cell_toCell]
  cases x with
  | inl c => exact hD c
  | inr a => exact le_rfl

theorem coded (hc : F.sem.IsCoded)
    (hfields : ∀ a f, IsCodedLabel N (F.fields a f))
    (hgrid : ∀ z ∈ F.grid, IsCodedLabel N z)
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d)) :
    F.rows.IsCoded := by
  apply CanonicalCodingSupport.layer D (Node (Q := Q)) N F.positive F.height F.separated
    F.sem F.rows hc F.inherited_row
  rintro ⟨a, marked⟩ d
  rw [F.node_row]
  have hs : IsCodedLabel N (F.source a d.1) := CanonicalCodingSupport.supported
    hgrid (hfields a) (F.source_supported hsupport a d.1 (by
      simpa only [CellScheme.grade, F.added_index] using d.2.2))
  have hw : IsCodedLabel N (F.nodeWeight (a, marked)) := by
    unfold nodeWeight
    split
    · exact hfields a F.gate
    · exact hgrid _ F.ceiling_mem
  rcases le_total (F.source a d.1) (F.nodeWeight (a, marked)) with he | he
  · rwa [min_eq_left he]
  · rwa [min_eq_right he]

/-- Fill the unique missing full active index by an actual ceiling leaf. -/
theorem complete_through (seed : Q)
    (hc : ∀ J ∈ Plan.gradedPlan D.plan, J.2 ≤ N → J ≠ (A, N) → ∃ d, D.cell d = J) :
    ∀ J ∈ Plan.gradedPlan F.carrier.plan, J.2 ≤ N → ∃ d, F.carrier.cell d = J := by
  intro J hJ hJN
  by_cases he : J = (A, N)
  · exact ⟨F.added seed false, (F.added_index seed false).trans he.symm⟩
  · obtain ⟨d, hd⟩ := hc J hJ hJN he
    exact ⟨F.old d, (F.old_index d).trans hd⟩

end
end VaughtConjecture.Knight.FinalGateLayer.Input

namespace VaughtConjecture.Knight.OrdinaryFinalCatalogue
open Transform Value ExtOrd CappedDonor CappedDonor.Ref PairedSlotComparison
noncomputable section
variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)

theorem member_coded (a : Member R) (f : Field P C) : IsCodedLabel N (a.val f) := by
  rcases mem_codedAlphabet_iff.mp
    (CanonicalPairedProfiles.inventory_coded (Field P C) N a.property.1 f)
    with hb | ⟨b, i, _, hi, he⟩
  · exact Or.inl hb
  · exact Or.inr ⟨b, i, hi, he⟩

end
end VaughtConjecture.Knight.OrdinaryFinalCatalogue
