/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalPairedProfiles

/-! # Supported inverse with fixed unused grid endpoints

Occupied rays read the original observations. At every unhosted block through
the retained cut, an added constant step fixes that block's grid endpoint.
Hosted blocks retain their affine rays instead: a constant patch there would
destroy the invisible observations. This is separate from right-filled decoding.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalPairedInverse
open Transform Value ExtOrd PairedSlotEncoding
noncomputable section

def grid (j b : ℕ) : ExtOrd := ofOrd (Ordinal.omega0 * b + j)

def freeBlocks (j : ℕ) (S : Finset Ordinal.{0}) (B : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (B + 1)).filter
    (fun b => ¬ ∃ a ∈ S, Orbit j S a ∧ block j S a = b)

def patch (j : ℕ) (S : Finset Ordinal.{0}) (B : ℕ) (x : ExtOrd) : ExtOrd :=
  (freeBlocks j S B).sup (fun b => stepShifter b ⊥ (grid j b) x)

def inverse (j : ℕ) (S : Finset Ordinal.{0}) (B : ℕ) (x : ExtOrd) : ExtOrd :=
  max (PairedSlotDecoder.occupied j S x) (patch j S B x)

theorem grid_visible (j b : ℕ) : SelfVis j (grid j b) := by
  apply selfVis_ofOrd_iff.mpr
  simp only [finitePart_mul_add, le_refl]

theorem inverse_witness (j : ℕ) (S : Finset Ordinal.{0}) (B : ℕ) :
    Witness (gTop j) (inverse j S B) :=
  (PairedSlotDecoder.occupied_witness j S).max
    (Witness.finset_sup (MixedGradeInterpolation.zero_witness j) (freeBlocks j S B)
      (fun b _ => Witness.stepLimit j b bot_le (selfVis_bot j) (grid_visible j b)))

section Relative
variable {j B : ℕ} {S : Finset Ordinal.{0}}
  (hc : ∀ a ∈ S, min (encode j S a) (grid j B) = min (ofOrd a) (grid j B))
include hc

theorem encoded_low {a : Ordinal.{0}} (ha : a ∈ S) (hl : encode j S a < grid j B) :
    encode j S a = ofOrd a := eq_of_cap_eq_lt (hc a ha) hl

theorem original_reaches {a : Ordinal.{0}} (ha : a ∈ S) {b : ℕ}
    (hb : b ≤ B) (he : grid j b ≤ encode j S a) : grid j b ≤ ofOrd a := by
  have hcut : grid j b ≤ grid j B := ofOrd_le_ofOrd.mpr (by
    apply add_le_add
    · gcongr
    · exact le_rfl)
  exact (le_min he hcut).trans ((hc a ha) ▸ min_le_left (ofOrd a) (grid j B))

theorem patch_encode_le {a : Ordinal.{0}} (ha : a ∈ S) :
    patch j S B (encode j S a) ≤ ofOrd a := by
  classical
  apply Finset.sup_le
  intro b hb
  obtain ⟨hbB, hbfree⟩ := Finset.mem_filter.mp hb
  have hbB : b ≤ B := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hbB
  by_cases hba : b ≤ block j S a
  · apply (PairedSlotDecoder.step_zero_le _ _ _).trans
    apply original_reaches hc ha hbB
    rcases lt_or_eq_of_le hba with hlt | heq
    · exact ofOrd_le_ofOrd.mpr ((code_add_lt_mul (Nat.cast_lt.mpr hlt) j).le.trans
        le_self_add)
    · have ho : ¬ Orbit j S a := fun ho => hbfree ⟨a, ha, ho, heq.symm⟩
      simp only [encode, offset, ite_eq_right ho, grid, heq, le_refl]
  · rw [encode, stepShifter_of_lt (ofOrd_ne_bot _)
      (ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (not_le.mp hba)) _))]
    exact bot_le

theorem inverse_encode {a : Ordinal.{0}} (ha : a ∈ S) :
    inverse j S B (encode j S a) = ofOrd a := by
  rw [inverse, PairedSlotDecoder.occupied_encode ha, max_eq_left (patch_encode_le hc ha)]

theorem occupied_grid_le {b : ℕ} (hb : b < B) :
    PairedSlotDecoder.occupied j S (grid j b) ≤ grid j b := by
  classical
  apply Finset.sup_le
  intro a ha
  by_cases hab : block j S a ≤ b
  · have hes : encode j S a ≤ grid j b := ofOrd_le_ofOrd.mpr
      (add_le_add (by gcongr) (Nat.cast_le.mpr (offset_le j S a)))
    have hgrid : grid j b < grid j B := ofOrd_lt_ofOrd.mpr
      ((code_add_lt_mul (Nat.cast_lt.mpr hb) j).trans_le le_self_add)
    have hea : encode j S a = ofOrd a := encoded_low hc ha (hes.trans_lt hgrid)
    apply (PairedSlotDecoder.piece_le j S a _).trans
    rw [PairedSlotDecoder.ceiling_eq_replace ha, ← hea]
    exact (evr_mono hes le_rfl).trans_eq (grid_visible j b)
  · have hlt : grid j b < ofOrd (Ordinal.omega0 * block j S a) :=
      ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (not_le.mp hab)) j)
    unfold PairedSlotDecoder.piece
    split_ifs
    · rw [grid, FiniteOrbitEmbedding.ray_ofOrd, limitPart_mul_add,
        ite_eq_left (by simpa only [Nat.cast_zero, add_zero] using
          code_add_lt_mul (Nat.cast_lt.mpr (not_le.mp hab)) 0)]
      exact bot_le
    · change stepShifter (block j S a) ⊥ (ofOrd a)
        (ofOrd (Ordinal.omega0 * b + j)) ≤ grid j b
      rw [stepShifter_of_lt (ofOrd_ne_bot _) hlt]
      exact bot_le

omit hc in
theorem patch_grid_le (b : ℕ) : patch j S B (grid j b) ≤ grid j b := by
  classical
  apply Finset.sup_le
  intro n _
  by_cases hn : n ≤ b
  · apply (PairedSlotDecoder.step_zero_le _ _ _).trans
    exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl)
  · change stepShifter n ⊥ (grid j n) (ofOrd (Ordinal.omega0 * b + j)) ≤ grid j b
    rw [stepShifter_of_lt (ofOrd_ne_bot _)
      (ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (not_le.mp hn)) j))]
    exact bot_le

/-- Every retained grid point is reached. A hosted block is supplied by its
actual invisible anchor, not by a constant patch over that anchor. -/
theorem grid_reaches {b : ℕ} (hb : b ≤ B) : grid j b ≤ inverse j S B (grid j b) := by
  classical
  by_cases hh : ∃ a ∈ S, Orbit j S a ∧ block j S a = b
  · obtain ⟨a, ha, ho, hab⟩ := hh
    obtain ⟨v, hv, hvj, hva⟩ := ho.2
    have hov : Orbit j S v := orbit_of_invisible hv hvj
    have hkv : key j S v = key j S a := by
      simp only [key, ite_eq_left hov, ite_eq_left ho, hva]
    have hvb : block j S v = b := (block_eq_of_key_eq hv ha hkv).trans hab
    have he : encode j S v < grid j B := by
      simp only [encode, offset, ite_eq_left hov, hvb, grid]
      exact ofOrd_lt_ofOrd.mpr (lt_of_lt_of_le
        ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hvj))
        (add_le_add (by gcongr) le_rfl))
    have hfix := encoded_low hc hv he
    have hread := inverse_encode hc hv
    have hw := inverse_witness j S B
    have hsrc : extVisibilityReplace (encode j S v) j j = grid j b := by
      simp only [encode, offset, ite_eq_left hov, hvb,
        extVisibilityReplace_ofOrd, visibilityReplace, finitePart_mul_add,
        ite_eq_left hvj, ordinalReplace, limitPart_mul_add, grid]
    have hcomm := hw.clause5 (encode j S v) j (by rw [gTop_of_le le_rfl]; exact le_top)
      j le_rfl
    rw [hsrc, hread, ← hfix, hsrc] at hcomm
    exact hcomm.ge
  · have hm : b ∈ freeBlocks j S B :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hh⟩
    have hs : stepShifter b ⊥ (grid j b) (grid j b) = grid j b :=
      stepShifter_of_ge (ofOrd_le_ofOrd.mpr le_self_add)
    calc
      grid j b = stepShifter b ⊥ (grid j b) (grid j b) := hs.symm
      _ ≤ patch j S B (grid j b) := Finset.le_sup (f := fun n =>
        stepShifter n ⊥ (grid j n) (grid j b)) hm
      _ ≤ inverse j S B (grid j b) := le_max_right _ _

theorem inverse_grid {b : ℕ} (hb : b < B) : inverse j S B (grid j b) = grid j b :=
  le_antisymm (max_le (occupied_grid_le hc hb) (patch_grid_le b)) (grid_reaches hc hb.le)

end Relative

section Profile
variable {X : Type*} [Fintype X] {j B : ℕ} {a p : X → ExtOrd}

theorem encoded_cap
    (ha : a ∈ CanonicalPairedProfiles.inventory X j)
    (hag : ∀ d, min (a d) (grid j B) = min (p d) (grid j B)) :
    ∀ v ∈ values p, min (encode j (values p) v) (grid j B) =
      min (ofOrd v) (grid j B) := by
  intro v hv
  obtain ⟨d, hd⟩ := mem_values.mp hv
  have he := CanonicalPairedProfiles.normalize_cap X j ha hag d
  rw [normalize_ofOrd hd] at he
  exact he.trans (by simpa only [hd, grid] using hag d)

theorem inverse_normalize
    (ha : a ∈ CanonicalPairedProfiles.inventory X j) (hp : ∀ d, p d ≠ ⊤)
    (hag : ∀ d, min (a d) (grid j B) = min (p d) (grid j B)) (d : X) :
    inverse j (values p) B (PairedSlotEncoding.normalize j p d) = p d := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨v, hv⟩
  · simp only [PairedSlotEncoding.normalize, hb, (inverse_witness j (values p) B).bot]
  · exact (hp d ht).elim
  · rw [normalize_ofOrd hv, inverse_encode (encoded_cap ha hag) (mem_values.mpr ⟨d, hv⟩), hv]

/-- Only represented low anchors and their replacement orbits are fixed.
There is deliberately no identity assertion for unhosted invisible sources. -/
theorem inverse_supported
    (ha : a ∈ CanonicalPairedProfiles.inventory X j) (hp : ∀ d, p d ≠ ⊤)
    (hag : ∀ d, min (a d) (grid j B) = min (p d) (grid j B))
    (d : X) (hd : a d < grid j B) {k i : ℕ} (hk : k ≤ j) (hi : i ≤ k) :
    inverse j (values p) B (extVisibilityReplace (a d) k i) =
      extVisibilityReplace (a d) k i := by
  have he : a d = p d := eq_of_cap_eq_lt (hag d) hd
  have hn : PairedSlotEncoding.normalize j p d = a d := by
    rw [← normalize_prefix (by simp only [finitePart_mul_add, le_refl]) hag d hd, ha.1]
  have hr : inverse j (values p) B (a d) = a d := by
    calc
      inverse j (values p) B (a d) =
          inverse j (values p) B (PairedSlotEncoding.normalize j p d) := congrArg _ hn.symm
      _ = p d := inverse_normalize ha hp hag d
      _ = a d := he.symm
  rw [(inverse_witness j (values p) B).clause5 _ k
    (by rw [gTop_of_le hk]; exact le_top) i hi, hr]

/-- A constructed supported inverse, with no supplied scalar map or alignment.
The canonical source and the proper repaired field vector agree at the same
original grid cut. The whole field inventory determines the normalizer. -/
theorem exists_supported_inverse
    (ha : a ∈ CanonicalPairedProfiles.inventory X j) (hp : ∀ d, p d ≠ ⊤)
    (hag : ∀ d, min (a d) (grid j B) = min (p d) (grid j B)) :
    ∃ κ : ExtOrd → ExtOrd,
      Witness (gTop j) κ ∧
      (∀ d, κ (PairedSlotEncoding.normalize j p d) = p d) ∧
      (∀ b < B, κ (grid j b) = grid j b) ∧
      grid j B ≤ κ (grid j B) ∧
      (∀ d, a d < grid j B → ∀ k ≤ j, ∀ i ≤ k,
        κ (extVisibilityReplace (a d) k i) = extVisibilityReplace (a d) k i) := by
  refine ⟨inverse j (values p) B, inverse_witness j (values p) B,
    inverse_normalize ha hp hag, ?_, grid_reaches (encoded_cap ha hag) le_rfl, ?_⟩
  · exact fun b hb => inverse_grid (encoded_cap ha hag) hb
  · exact fun d hd k hk i hi => inverse_supported ha hp hag d hd hk hi

end Profile
end
end VaughtConjecture.Knight.CanonicalPairedInverse
