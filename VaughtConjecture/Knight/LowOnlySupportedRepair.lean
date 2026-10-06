/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyTerminal
public import VaughtConjecture.Knight.CanonicalPairedInverse

/-! # Protected terminal decoding for the gate-free LOW family

This specializes the supported-terminal construction of `ReceivingSupportedRepair`
to the already-proved gate-free fibres. The complete vector includes future fields
and the cutoff. Whole-block collapse is above the protected cut, so even unused
grid endpoints below that cut survive. No physical prefix hypothesis is hidden in
this source-level result; its ladder application is in `LowOnlyLadderRepair`.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnly
open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref
open CanonicalPairedInverse
noncomputable section
variable {n K j B : ℕ} {P C : SemScheme n}

namespace Family
variable (F : Family P C K)

/-- Constructed source repair, including protected unused grid endpoints. -/
structure ProtectedRepair (a : Field P C → ExtOrd) (S : State P C) (j B : ℕ) where
  encoded : State P C
  admitted : F.Admissible j encoded
  canonical : encoded.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j
  prefix_eq : ∀ d, min (encoded.profile d) (grid j B) = min (a d) (grid j B)
  decoder : ExtOrd → ExtOrd
  witness : Witness (gTop j) decoder
  readback : ∀ d, decoder (encoded.profile d) = S.profile d
  grid_fixed : ∀ b < B, decoder (grid j b) = grid j b
  reaches : grid j B ≤ decoder (grid j B)
  boundary_fixed : ∀ d, a d < grid j B → decoder (a d) = a d

/-- Properize above the cut, use the supported inverse, then collapse the whole
terminal block. Literal top does not sacrifice any protected grid point. -/
theorem exists_protected_repair (hj : 1 ≤ j) {a : Field P C → ExtOrd}
    (ha : a ∈ CanonicalPairedProfiles.inventory (Field P C) j)
    {S : State P C} (hS : F.Admissible j S)
    (hag : ∀ d, min (a d) (grid j B) = min (S.profile d) (grid j B)) :
    Nonempty (F.ProtectedRepair a S j B) := by
  let h : Ordinal.{0} := Ordinal.omega0 * B + j
  let l := S.freshFloor h
  let β : ExtOrd := ofOrd (l + j)
  have hlim : limitPart l = l := S.freshFloor_limit h
  have hh : grid j B < ofOrd l :=
    ofOrd_lt_ofOrd.mpr (S.lt_freshFloor h (Finset.mem_insert_self _ _))
  have hβ : SelfVis j β := by
    apply selfVis_ofOrd_iff.mpr
    have he := finitePart_limitPart_add_nat l j
    rw [hlim] at he
    exact he.ge
  have hlβ : ofOrd l ≤ β := ofOrd_le_ofOrd.mpr le_self_add
  have hcutβ : grid j B ≤ β := hh.le.trans hlβ
  let V := S.map (fun x => min x β)
  have hV : F.Admissible j V :=
    hS.map F (capWitness hβ (ofOrd_ne_bot _)) hj
      (capWitness_reflects_bottom (ofOrd_ne_bot _))
  have hproper : ∀ d, V.profile d ≠ ⊤ := by
    intro d
    rw [State.profile_map]
    exact fun ht => ofOrd_ne_top _ (min_eq_top.mp ht).2
  have hagV : ∀ d, min (a d) (grid j B) = min (V.profile d) (grid j B) := by
    intro d
    rw [State.profile_map, min_assoc, min_eq_right hcutβ]
    exact hag d
  obtain ⟨κ, hw, hread, hfix, hreach, _⟩ := exists_supported_inverse ha hproper hagV
  let Q := V.normalize j
  have hprefix : ∀ d, min (Q.profile d) (grid j B) = min (a d) (grid j B) := by
    intro d
    rw [State.profile_normalize]
    exact CanonicalPairedProfiles.normalize_cap (Field P C) j ha hagV d
  let δ := collapseBlock l ∘ κ
  have hδ : Witness (gTop j) δ :=
    Witness.comp_of_bottom_reflecting hw (collapseBlock_witness j hlim) le_rfl
      (collapseBlock_reflects_bottom l)
  have hδread (d) : δ (Q.profile d) = S.profile d := by
    dsimp only [δ, Function.comp_apply]
    rw [State.profile_normalize, hread, State.profile_map]
    exact collapseBlock_min hlβ (S.profile_lt_freshFloor h d)
  refine ⟨{
    encoded := Q
    admitted := F.normalize_admissible hj hV
    canonical := normalize_inventory j hproper
    prefix_eq := hprefix
    decoder := δ
    witness := hδ
    readback := hδread
    grid_fixed := ?_
    reaches := ?_
    boundary_fixed := ?_
  }⟩
  · intro b hb
    dsimp only [δ, Function.comp_apply]
    rw [hfix b hb]
    apply collapseBlock_of_lt
    apply lt_of_le_of_lt _ hh
    exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl)
  · calc
      grid j B = collapseBlock l (grid j B) := (collapseBlock_of_lt hh).symm
      _ ≤ collapseBlock l (κ (grid j B)) := (collapseBlock_witness j hlim).mono hreach
  · intro d hd
    have hqa := PairedSlotEncoding.eq_of_cap_eq_lt (hprefix d).symm hd
    have hpa := PairedSlotEncoding.eq_of_cap_eq_lt (hag d) hd
    exact (congrArg δ hqa).trans ((hδread d).trans hpa.symm)

/-- Fixation extends to every represented replacement orbit, not to arbitrary
unhosted invisible values. -/
theorem ProtectedRepair.orbit_fixed {a : Field P C → ExtOrd} {S : State P C}
    (r : F.ProtectedRepair a S j B) (d : Field P C) (hd : a d < grid j B)
    {k i : ℕ} (hk : k ≤ j) (hi : i ≤ k) :
    r.decoder (extVisibilityReplace (a d) k i) = extVisibilityReplace (a d) k i := by
  rw [r.witness.clause5 _ k (by rw [gTop_of_le hk]; exact le_top) i hi,
    r.boundary_fixed d hd]

/-- The private fibre constructs admission and agreement before normalization. -/
theorem private_protected_repair (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S)
    (hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v)
    (hag : ∀ d, min (v d) (grid j B) = min (S.lowerC j d) (grid j B)) :
    ∃ S', F.Admissible j S' ∧ S'.lowerC j = v ∧
      S.CapEq (grid j B) S' ∧ S.FutureEq j S' ∧
      Nonempty (F.ProtectedRepair S.profile S' j B) := by
  obtain ⟨S', hS', hv', hcap, hfuture⟩ :=
    F.private_lift hS hv ((grid_visible j B).mono (min_le_left _ _)) hag
  exact ⟨S', hS', hv', hcap, hfuture, F.exists_protected_repair hj hcanon hS'
    (fun d => (State.capEq_iff_profile.mp hcap d).symm)⟩

/-- Donor prescription uses the checked release fibre, not a face exchange. -/
theorem donor_protected_repair (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S)
    (hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j)
    {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u)
    (hag : ∀ d, min (u d) (grid j B) = min (S.lowerP j d) (grid j B)) :
    ∃ S', F.Admissible j S' ∧ S'.lowerP j = u ∧
      S.CapEq (grid j B) S' ∧ S.FutureEq j S' ∧
      Nonempty (F.ProtectedRepair S.profile S' j B) := by
  obtain ⟨S', hS', hu', hcap, hfuture⟩ :=
    F.donor_lift hS hu ((grid_visible j B).mono (min_le_left _ _)) hag
  exact ⟨S', hS', hu', hcap, hfuture, F.exists_protected_repair hj hcanon hS'
    (fun d => (State.capEq_iff_profile.mp hcap d).symm)⟩

end Family
end
end VaughtConjecture.Knight.LowOnly
