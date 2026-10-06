/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlySupportedRepair
public import VaughtConjecture.Knight.RelativeLadderDecodedPrefix

/-! # LOW repairs retain the entire padded ladder prefix

The fixed index set is the full canonical admitted catalogue at the chosen birth
grade. Replacement membership is constructed by the existing LOW fibres and the
protected inverse. The installed rank rows are not changed or filtered by a
lifting request. All coordinates, including unused and foreign rungs, use the
same external ceiling before and after repair.

This proves physical source receipts, not extraction from an arbitrary ambient
or unrestricted lifting on a higher LOW tower. It does not promote birth-grade
profiles to higher-grade admission.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnly.Family
open Transform Value ExtOrd AmalgamationPlan CappedDonor CanonicalPairedInverse
open RelativeLadderLayer
noncomputable section
variable {n K j B : ℕ} {P C : SemScheme n} (F : Family P C K)

def catalogue (j : ℕ) : Set (Field P C → ExtOrd) :=
  {a | a ∈ CanonicalPairedProfiles.inventory (Field P C) j ∧
    ∃ S : State P C, F.Admissible j S ∧ S.profile = a}

theorem catalogue_finite (j : ℕ) : (F.catalogue j).Finite :=
  (CanonicalPairedProfiles.inventory_finite (Field P C) j).subset (fun _ h => h.1)

abbrev Anchor (j : ℕ) := {a // a ∈ F.catalogue j}

instance (j : ℕ) : Fintype (F.Anchor j) := (F.catalogue_finite j).fintype

def fields (j : ℕ) (a : F.Anchor j) : Field P C → ExtOrd := a.val

/-- The same ceiling is used by both physical renderings, even at unused ranks. -/
def ladderCeiling (j B : ℕ) : ExtOrd :=
  max (grid j B) (PairedSlotProfiles.sourceCeiling j (Field P C))

theorem anchor_bound (a : F.Anchor j) (d : Field P C) :
    F.fields j a d ≤ ladderCeiling (P := P) (C := C) j B :=
  (CanonicalPairedProfiles.inventory_bound _ _ a.property.1 d).trans (le_max_right _ _)

variable {F}

def ProtectedRepair.anchor {a : Field P C → ExtOrd} {S : State P C}
    (r : F.ProtectedRepair a S j B) : F.Anchor j :=
  ⟨r.encoded.profile, r.canonical, r.encoded, r.admitted, rfl⟩

section Physical
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (hA : 0 < A.card) (field : Cell D → Field P C)

/-- Actual original occurrences decode literally, including top. -/
theorem ProtectedRepair.ladder_readback {a : Field P C → ExtOrd} {S : State P C}
    (r : F.ProtectedRepair a S j B) (d : Cell D) :
    r.decoder (selected D hA field (F.fields j) r.anchor
      (ladderCeiling (P := P) (C := C) j B) (old D hA d)) = S.profile (field d) := by
  rw [selected_old]
  exact r.readback _

/-- No caller-supplied physical support or physical agreement: both are derived
from the full rank table on the unchanged carrier. -/
theorem ProtectedRepair.ladder_caps {a : F.Anchor j} {S : State P C}
    (r : F.ProtectedRepair a.val S j B)
    (d : Cell (carrier D hA (X := Field P C) (Q := F.Anchor j))) :
    min (r.decoder (selected D hA field (F.fields j) r.anchor
      (ladderCeiling (P := P) (C := C) j B) d)) (grid j B) =
    min (selected D hA field (F.fields j) a
      (ladderCeiling (P := P) (C := C) j B) d) (grid j B) := by
  exact renderWith_decoded_agreement D hA field (F.fields j)
    (a := a) (b := r.anchor) (fun _ => rfl) (fun _ => rfl)
    (F.anchor_bound a) (F.anchor_bound r.anchor) (le_max_left _ _)
    (fun x => (r.prefix_eq x).symm) r.witness.mono r.witness.bot r.reaches r.boundary_fixed d

/-- Private repair constructs the member of the fixed catalogue and all physical
prefix receipts. Only the lawful original prescription and its scalar cap
compatibility are inputs; the future vector is retained by the fibre. -/
theorem private_ladder_repair (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v)
    (hag : ∀ d, min (v d) (grid j B) = min (S.lowerC j d) (grid j B)) :
    ∃ S' : State P C, F.Admissible j S' ∧ S'.lowerC j = v ∧ S.FutureEq j S' ∧
      ∃ r : F.ProtectedRepair S.profile S' j B,
        ∀ d : Cell (carrier D hA (X := Field P C) (Q := F.Anchor j)),
          min (r.decoder (selected D hA field (F.fields j) r.anchor
            (ladderCeiling (P := P) (C := C) j B) d)) (grid j B) =
          min (selected D hA field (F.fields j) ⟨S.profile, hc, S, hS, rfl⟩
            (ladderCeiling (P := P) (C := C) j B) d) (grid j B) := by
  obtain ⟨S', hS', hv', _, hf, ⟨r⟩⟩ := F.private_protected_repair hj hS hc hv hag
  exact ⟨S', hS', hv', hf, r, ProtectedRepair.ladder_caps D hA field
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r⟩

/-- The other direction consumes donor release, with identical physical receipts. -/
theorem donor_ladder_repair (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j)
    {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u)
    (hag : ∀ d, min (u d) (grid j B) = min (S.lowerP j d) (grid j B)) :
    ∃ S' : State P C, F.Admissible j S' ∧ S'.lowerP j = u ∧ S.FutureEq j S' ∧
      ∃ r : F.ProtectedRepair S.profile S' j B,
        ∀ d : Cell (carrier D hA (X := Field P C) (Q := F.Anchor j)),
          min (r.decoder (selected D hA field (F.fields j) r.anchor
            (ladderCeiling (P := P) (C := C) j B) d)) (grid j B) =
          min (selected D hA field (F.fields j) ⟨S.profile, hc, S, hS, rfl⟩
            (ladderCeiling (P := P) (C := C) j B) d) (grid j B) := by
  obtain ⟨S', hS', hu', _, hf, ⟨r⟩⟩ := F.donor_protected_repair hj hS hc hu hag
  exact ⟨S', hS', hu', hf, r, ProtectedRepair.ladder_caps D hA field
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r⟩

end Physical
end
end VaughtConjecture.Knight.LowOnly.Family
