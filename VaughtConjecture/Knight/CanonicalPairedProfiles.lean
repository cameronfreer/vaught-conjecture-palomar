/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalPairedPrefix

/-! # Canonical inventories on the complete field vector

This is a separate inventory, not a change to the refuted all-short family.
The finite type `X` counts every field normalized together, including auxiliary
fields. No boundary-cardinality estimate is substituted for its cardinality.

The inventory supplies canonical representatives and relative capped agreement.
It does not yet supply a prefix-fixing inverse or coupled semantic sections.
The ordinary exact decoder below is deliberately not claimed to fix unused grids.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalPairedProfiles
open Transform Value ExtOrd PairedSlotEncoding PairedSlotProfiles SharpWitnessComposition
noncomputable section

section Inventory
variable (X : Type*) [Fintype X] (j : ℕ)

/-- Proper canonical fixed points on the complete inventory. -/
def inventory : Set (X → ExtOrd) :=
  {p | PairedSlotEncoding.normalize j p = p ∧ ∀ d, p d ≠ ⊤}

theorem inventory_coded {p : X → ExtOrd} (hp : p ∈ inventory X j) (d : X) :
    p d ∈ ExtOrd.codedAlphabet (2 * Fintype.card X) j := by
  rw [← congrFun hp.1 d]
  exact normalize_mem j p d (hp.2 d)

theorem inventory_finite : (inventory X j).Finite :=
  (ExtOrd.codedLabellings_finite X (2 * Fintype.card X) j).subset
    (fun _ hp => inventory_coded X j hp)

theorem inventory_short {p : X → ExtOrd} (hp : p ∈ inventory X j) (d : X) :
    Short j (p d) := by
  rw [← congrFun hp.1 d]
  exact normalize_short j p d

theorem inventory_bound {p : X → ExtOrd} (hp : p ∈ inventory X j) (d : X) :
    p d ≤ sourceCeiling j X := by
  rw [← congrFun hp.1 d]
  exact normalize_le_ceiling hp.2 d

theorem normalize_mem_inventory {p : X → ExtOrd} (hp : ∀ d, p d ≠ ⊤) :
    PairedSlotEncoding.normalize j p ∈ inventory X j := by
  refine ⟨CanonicalPairedEncoding.normalize_idempotent j p, ?_⟩
  intro d
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simpa only [PairedSlotEncoding.normalize, hb] using
      (show (⊥ : ExtOrd) ≠ ⊤ from hb ▸ hp d)
  · exact (hp d ht).elim
  · rw [normalize_ofOrd ha]
    exact ofOrd_ne_top _

/-- The relative prefix theorem applies coordinatewise to the full field vector,
including auxiliary fields, and uses the original grid cut. -/
theorem normalize_cap {a p : X → ExtOrd} {B : ℕ}
    (ha : a ∈ inventory X j)
    (hag : ∀ d, min (a d) (ofOrd (Ordinal.omega0 * B + j)) =
      min (p d) (ofOrd (Ordinal.omega0 * B + j))) (d : X) :
    min (PairedSlotEncoding.normalize j p d) (ofOrd (Ordinal.omega0 * B + j)) =
      min (a d) (ofOrd (Ordinal.omega0 * B + j)) :=
  CanonicalPairedPrefix.normalize_cap ha.1 ha.2 hag d

/-- All fields, not merely the old boundary, contribute to the slot budget. -/
theorem complete_field_count {O A : Type*} [Fintype O] [Fintype A] :
    2 * Fintype.card (O ⊕ A) = 2 * (Fintype.card O + Fintype.card A) := by
  rw [Fintype.card_sum]

end Inventory

section Scheme
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (BJ : Finset ι × ℕ) [Fintype (D.below BJ)] (j : ℕ)

/-- Lawful canonical profiles; membership includes no completion assumption. -/
def family : Set (D.below BJ → ExtOrd) :=
  {p | RespectsSemanticsBelow sem BJ p ∧ p ∈ inventory (D.below BJ) j}

theorem family_finite : (family sem BJ j).Finite :=
  (inventory_finite (D.below BJ) j).subset (fun _ hp => hp.2)

theorem normalize_mem_family {p : D.below BJ → ExtOrd}
    (hp : RespectsSemanticsBelow sem BJ p) (ht : ∀ d, p d ≠ ⊤)
    (hg : ∀ d : D.below BJ, D.grade d.1 ≤ j) :
    PairedSlotEncoding.normalize j p ∈ family sem BJ j :=
  ⟨PairedSlotIncoming.normalize_respects hp hg,
    normalize_mem_inventory (D.below BJ) j ht⟩

/-- Canonical representatives have constructed incoming lawfulness and exact
ordinary decoding. This is not yet the supported prefix-fixing inverse. -/
theorem family_covers {p : D.below BJ → ExtOrd}
    (hp : RespectsSemanticsBelow sem BJ p) (ht : ∀ d, p d ≠ ⊤)
    (hg : ∀ d : D.below BJ, D.grade d.1 ≤ j)
    {G : Finset ExtOrd} {C : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) :
    ∃ q ∈ family sem BJ j, ∃ ν : ExtOrd → ExtOrd,
      Witness (gTop j) ν ∧ (∀ d, ν (q d) = p d) ∧
      (∀ d, q d = ⊥ ↔ p d = ⊥) ∧
      (∀ d, q d ≤ sourceCeiling j (D.below BJ)) := by
  refine ⟨PairedSlotEncoding.normalize j p, normalize_mem_family sem BJ j hp ht hg,
    PairedSlotDecoder.decode j (values p) G C, PairedSlotDecoder.decode_witness hG hC,
    PairedSlotDecoder.decode_normalize hG hC ht, normalize_bot_iff j p,
    normalize_le_ceiling ht⟩

end Scheme
end
end VaughtConjecture.Knight.CanonicalPairedProfiles
