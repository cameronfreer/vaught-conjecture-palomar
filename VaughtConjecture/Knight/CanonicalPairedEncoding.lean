/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PairedSlotProfiles

/-! # Canonical paired normalization

The canonical inventory uses fixed points of paired normalization, not all short
coded profiles. These scalar facts retain the complete finite field inventory.
They do not change the refuted `PairedMixedGradeLayers` construction.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalPairedEncoding
open Transform Value ExtOrd PairedSlotEncoding
noncomputable section

def codeOrd (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.omega0 * block j S a + offset j S a

def codedValues (j : ℕ) (S : Finset Ordinal.{0}) : Finset Ordinal.{0} :=
  S.image (codeOrd j S)

theorem codeOrd_finitePart (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) :
    finitePart (codeOrd j S a) = offset j S a := by
  exact finitePart_mul_add _ _

theorem codeOrd_limitPart (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) :
    limitPart (codeOrd j S a) = Ordinal.omega0 * block j S a := by
  exact limitPart_mul_add _ _

theorem orbit_codeOrd_iff {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : Orbit j (codedValues j S) (codeOrd j S a) ↔ Orbit j S a := by
  classical
  constructor
  · rintro ⟨_, b, hb, hbj, hba⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb
    rw [codeOrd_finitePart] at hbj
    have hob : Orbit j S b := by
      by_contra hn
      simp only [offset, ite_eq_right hn, lt_self_iff_false] at hbj
    have he : block j S b = block j S a := by
      simp only [codeOrd_limitPart] at hba
      have h := congrArg blockIdx hba
      have hz (n : ℕ) : blockIdx (Ordinal.omega0 * n) = (n : Ordinal.{0}) := by
        simpa only [Nat.cast_zero, add_zero] using blockIdx_mul_add n 0
      simpa only [hz, Nat.cast_inj] using h
    by_contra hoa
    simp only [block, ite_eq_left hob, ite_eq_right hoa] at he
    omega
  · intro hoa
    obtain ⟨b, hb, hbj, hk⟩ := orbit_witness_key hoa
    have hob := orbit_of_invisible hb hbj
    refine ⟨by rw [codeOrd_finitePart]; exact offset_le _ _ _,
      codeOrd j S b, Finset.mem_image_of_mem _ hb, ?_, ?_⟩
    · simpa only [codeOrd_finitePart, offset, ite_eq_left hob] using hbj
    · simp only [codeOrd_limitPart, block_eq_of_key_eq hb ha hk]

theorem key_codeOrd_eq_of_key_eq {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hb : b ∈ S) (hk : key j S a = key j S b) :
    key j (codedValues j S) (codeOrd j S a) =
      key j (codedValues j S) (codeOrd j S b) := by
  classical
  have he := block_eq_of_key_eq ha hb hk
  by_cases hoa : Orbit j S a
  · have hob := (orbit_iff_of_key_eq ha hb hk).mp hoa
    simp only [key, ite_eq_left ((orbit_codeOrd_iff ha).mpr hoa),
      ite_eq_left ((orbit_codeOrd_iff hb).mpr hob), codeOrd_limitPart, he]
  · have hob : ¬ Orbit j S b := fun h => hoa ((orbit_iff_of_key_eq ha hb hk).mpr h)
    have hab : a = b := by simpa only [key, ite_eq_right hoa, ite_eq_right hob] using hk
    rw [hab]

theorem key_codeOrd_lt_of_key_lt {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hk : key j S a < key j S b) :
    key j (codedValues j S) (codeOrd j S a) <
      key j (codedValues j S) (codeOrd j S b) := by
  have he := block_lt_of_key_lt ha hk
  have hlt : codeOrd j S a < limitPart (codeOrd j S b) := by
    rw [codeOrd_limitPart]
    exact code_add_lt_mul (Nat.cast_lt.mpr he) _
  apply (key_le _ _ _).trans_lt
  apply hlt.trans_le
  unfold key
  split_ifs
  · exact le_rfl
  · exact limitPart_le _

theorem key_codeOrd_lt_iff {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hb : b ∈ S) :
    key j (codedValues j S) (codeOrd j S a) <
      key j (codedValues j S) (codeOrd j S b) ↔ key j S a < key j S b := by
  constructor
  · intro h
    rcases lt_trichotomy (key j S a) (key j S b) with hlt | he | hgt
    · exact hlt
    · exact (h.ne (key_codeOrd_eq_of_key_eq ha hb he)).elim
    · exact (lt_asymm h (key_codeOrd_lt_of_key_lt hb hgt)).elim
  · exact key_codeOrd_lt_of_key_lt ha

theorem key_codeOrd_eq_iff {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hb : b ∈ S) :
    key j (codedValues j S) (codeOrd j S a) =
      key j (codedValues j S) (codeOrd j S b) ↔ key j S a = key j S b := by
  constructor
  · intro h
    rcases lt_trichotomy (key j S a) (key j S b) with hlt | he | hgt
    · exact ((key_codeOrd_lt_of_key_lt ha hlt).ne h).elim
    · exact he
    · exact ((key_codeOrd_lt_of_key_lt hb hgt).ne h.symm).elim
  · exact key_codeOrd_eq_of_key_eq ha hb

theorem rank_codeOrd {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : rank j (codedValues j S) (codeOrd j S a) = rank j S a := by
  classical
  let rep (x : Ordinal.{0}) (hx : x ∈ PairedSlotEncoding.keys j S) : Ordinal.{0} :=
    Classical.choose (Finset.mem_image.mp hx)
  have rep_spec (x : Ordinal.{0}) (hx : x ∈ PairedSlotEncoding.keys j S) :
      rep x hx ∈ S ∧ key j S (rep x hx) = x :=
    Classical.choose_spec (Finset.mem_image.mp hx)
  unfold PairedSlotEncoding.rank
  symm
  apply Finset.card_bij (fun x hx =>
    key j (codedValues j S) (codeOrd j S (rep x (Finset.mem_filter.mp hx).1)))
  · intro x hx
    obtain ⟨hm, hl⟩ := Finset.mem_filter.mp hx
    obtain ⟨hr, he⟩ := rep_spec x hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _
      (Finset.mem_image_of_mem _ hr),
      key_codeOrd_lt_of_key_lt hr (lt_of_eq_of_lt he hl)⟩
  · intro x hx y hy he
    obtain ⟨hr, hx'⟩ := rep_spec x (Finset.mem_filter.mp hx).1
    obtain ⟨hs, hy'⟩ := rep_spec y (Finset.mem_filter.mp hy).1
    exact hx'.symm.trans (((key_codeOrd_eq_iff hr hs).mp he).trans hy')
  · intro y hy
    obtain ⟨hy, hlt⟩ := Finset.mem_filter.mp hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hw
    subst w
    have hk : key j S b ∈ PairedSlotEncoding.keys j S := Finset.mem_image_of_mem _ hb
    have hm : key j S b ∈ (PairedSlotEncoding.keys j S).filter (fun x => x < key j S a) :=
      Finset.mem_filter.mpr ⟨hk, (key_codeOrd_lt_iff hb ha).mp hlt⟩
    refine ⟨key j S b, hm, ?_⟩
    exact key_codeOrd_eq_of_key_eq (rep_spec _ hk).1 hb (rep_spec _ hk).2

theorem encode_codeOrd {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : encode j (codedValues j S) (codeOrd j S a) = encode j S a := by
  classical
  have hr := rank_codeOrd (j := j) ha
  by_cases ho : Orbit j S a
  · have hc := (orbit_codeOrd_iff ha).mpr ho
    simp only [encode, block, offset, ite_eq_left ho, ite_eq_left hc, hr,
      codeOrd_finitePart]
  · have hc : ¬ Orbit j (codedValues j S) (codeOrd j S a) :=
      fun h => ho ((orbit_codeOrd_iff ha).mp h)
    simp only [encode, block, offset, ite_eq_right ho, ite_eq_right hc, hr]

section Profile
variable {X : Type*} [Fintype X]

theorem values_normalize (j : ℕ) (p : X → ExtOrd) :
    values (normalize j p) = codedValues j (values p) := by
  classical
  ext a
  rw [mem_values, codedValues, Finset.mem_image]
  constructor
  · rintro ⟨d, hd⟩
    rcases ExtOrd.cases (p d) with hb | ht | ⟨b, hb⟩
    · simp only [PairedSlotEncoding.normalize, hb] at hd
      exact (ofOrd_ne_bot _ hd.symm).elim
    · simp only [PairedSlotEncoding.normalize, ht] at hd
      exact (ofOrd_ne_top _ hd.symm).elim
    · exact ⟨b, mem_values.mpr ⟨d, hb⟩, ofOrd_inj.mp ((normalize_ofOrd hb).symm.trans hd)⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨d, hd⟩ := mem_values.mp hb
    exact ⟨d, normalize_ofOrd hd⟩

/-- Paired normalization is a retraction, with no bound on the original ordinals.
Literal top stays top; membership of the finite proper catalogue is separate. -/
theorem normalize_idempotent (j : ℕ) (p : X → ExtOrd) :
    normalize j (normalize j p) = normalize j p := by
  funext d
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simp only [PairedSlotEncoding.normalize, hb]
  · simp only [PairedSlotEncoding.normalize, ht]
  · rw [normalize_ofOrd (normalize_ofOrd ha), values_normalize, normalize_ofOrd ha]
    exact encode_codeOrd (mem_values.mpr ⟨d, ha⟩)

end Profile
end
end VaughtConjecture.Knight.CanonicalPairedEncoding
