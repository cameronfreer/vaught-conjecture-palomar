/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PairedSlotIncoming

/-! # Finite lawful paired-slot profiles

On a fixed finite lower domain, every lawful labelling without literal top has
a lawful sharp representative in a fixed finite family. The representative
has a constructed incoming encoder and an exact outgoing decoder. The family
does not assume a lawful completion of any face, common-cut compatibility of
decoders, or a new-controller consistency theorem.

Literal top is supported by incoming normalization, but is excluded here because
the family's finite coded alphabet contains only bottom and proper ordinals.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.PairedSlotProfiles
open Transform Value ExtOrd PairedSlotEncoding SharpWitnessComposition
noncomputable section

section Profile
variable {X : Type*} [Fintype X]

theorem normalize_short (j : ℕ) (p : X → ExtOrd) (d : X) :
    Short j (PairedSlotEncoding.normalize j p d) := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · exact Or.inl (by simp only [PairedSlotEncoding.normalize, hb])
  · exact Or.inr (Or.inl (by simp only [PairedSlotEncoding.normalize, ht]))
  · rw [normalize_ofOrd ha]
    exact Or.inr (Or.inr ⟨_, rfl, by
      rw [finitePart_mul_add]
      exact offset_le j (values p) a⟩)

/-- A single visible proper source ceiling bounds every finite normalized profile
on the same carrier, regardless of the ordinal size of its original labels. -/
def sourceCeiling (j : ℕ) (X : Type*) [Fintype X] : ExtOrd :=
  ofOrd (Ordinal.omega0 * (2 * Fintype.card X : ℕ) + j)

theorem sourceCeiling_visible (j : ℕ) (X : Type*) [Fintype X] :
    SelfVis j (sourceCeiling j X) := by
  apply selfVis_ofOrd_iff.mpr
  simp only [finitePart_mul_add, le_refl]

theorem normalize_le_ceiling {j : ℕ} {p : X → ExtOrd}
    (hp : ∀ d, p d ≠ ⊤) (d : X) :
    PairedSlotEncoding.normalize j p d ≤ sourceCeiling j X := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simp only [PairedSlotEncoding.normalize, hb, bot_le]
  · exact (hp d ht).elim
  · have hr := rank_lt_card (j := j) (mem_values.mpr ⟨d, ha⟩)
    have hn := values_card_le p
    have hblock : block j (values p) a ≤ 2 * Fintype.card X := by
      unfold block
      split_ifs <;> omega
    rw [normalize_ofOrd ha]
    apply ofOrd_le_ofOrd.mpr
    apply add_le_add
    · gcongr
    · exact Nat.cast_le.mpr (offset_le j (values p) a)

/-- The other decoder reads every replacement of the unchanged boundary prefix
literally. This includes invisible auxiliary values hosted by that prefix. -/
theorem decode_other_orbit_prefix {j k i : ℕ} {p q : X → ExtOrd}
    {G : Finset ExtOrd} {C : ExtOrd} {h : Ordinal.{0}}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) (hq : ∀ d, q d ≠ ⊤)
    (hh : j ≤ finitePart h)
    (hpq : ∀ d, min (p d) (ofOrd h) = min (q d) (ofOrd h))
    (hk : k ≤ j) (hi : i ≤ k) (d : X) (hd : p d < ofOrd h) :
    PairedSlotDecoder.decode j (values q) G C
        (extVisibilityReplace (PairedSlotEncoding.normalize j p d) k i) =
      extVisibilityReplace (p d) k i := by
  rw [(PairedSlotDecoder.decode_witness hG hC).clause5 _ k
    (by rw [gTop_of_le hk]; exact le_top) i hi,
    PairedSlotDecoder.decode_other_prefix hG hC hq hh hpq d hd]

/-- The two constructed decoders coincide on all replacement-orbit sources
anchored in the proper boundary prefix, even with different terminal ceilings.
This does not identify their values on unused source-grid points. -/
theorem decoders_agree_on_prefix_orbit {j k i : ℕ} {p q : X → ExtOrd}
    {G : Finset ExtOrd} {C C' : ExtOrd} {h : Ordinal.{0}}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) (hC' : SelfVis j C')
    (hp : ∀ d, p d ≠ ⊤) (hq : ∀ d, q d ≠ ⊤) (hh : j ≤ finitePart h)
    (hpq : ∀ d, min (p d) (ofOrd h) = min (q d) (ofOrd h))
    (hk : k ≤ j) (hi : i ≤ k) (d : X) (hd : p d < ofOrd h) :
    PairedSlotDecoder.decode j (values p) G C
        (extVisibilityReplace (PairedSlotEncoding.normalize j p d) k i) =
      PairedSlotDecoder.decode j (values q) G C'
        (extVisibilityReplace (PairedSlotEncoding.normalize j p d) k i) := by
  rw [decode_other_orbit_prefix hG hC hp hh (fun _ => rfl) hk hi d hd,
    decode_other_orbit_prefix hG hC' hq hh hpq hk hi d hd]

end Profile

section Scheme
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (BJ : Finset ι × ℕ) [Fintype (D.below BJ)] (j : ℕ)

/-- All lawful short rows in the fixed finite paired-slot alphabet. -/
def family : Set (D.below BJ → ExtOrd) :=
  {q | RespectsSemanticsBelow sem BJ q ∧
    (∀ d, q d ∈ ExtOrd.codedAlphabet (2 * Fintype.card (D.below BJ)) j) ∧
    ∀ d, Short j (q d)}

theorem family_finite : (family sem BJ j).Finite :=
  (ExtOrd.codedLabellings_finite (D.below BJ) (2 * Fintype.card (D.below BJ)) j).subset
    (fun _ h => h.2.1)

theorem normalize_mem_family {p : D.below BJ → ExtOrd}
    (hp : RespectsSemanticsBelow sem BJ p) (ht : ∀ d, p d ≠ ⊤)
    (hg : ∀ d : D.below BJ, D.grade d.1 ≤ j) :
    PairedSlotEncoding.normalize j p ∈ family sem BJ j :=
  ⟨PairedSlotIncoming.normalize_respects hp hg,
    fun d => normalize_mem j p d (ht d), normalize_short j p⟩

/-- A fixed finite family covers every lawful proper-valued profile by an
explicit faithful decoder, with no pre-existing output transformation assumed. -/
theorem family_covers {p : D.below BJ → ExtOrd}
    (hp : RespectsSemanticsBelow sem BJ p) (ht : ∀ d, p d ≠ ⊤)
    (hg : ∀ d : D.below BJ, D.grade d.1 ≤ j)
    {G : Finset ExtOrd} {C : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) :
    ∃ q ∈ family sem BJ j, ∃ ν : ExtOrd → ExtOrd,
      Witness (gTop j) ν ∧ (∀ d, ν (q d) = p d) ∧
      (∀ d, q d = ⊥ ↔ p d = ⊥) ∧ (∀ d, q d ≤ sourceCeiling j (D.below BJ)) := by
  refine ⟨PairedSlotEncoding.normalize j p, normalize_mem_family sem BJ j hp ht hg,
    PairedSlotDecoder.decode j (values p) G C, PairedSlotDecoder.decode_witness hG hC,
    PairedSlotDecoder.decode_normalize hG hC ht, normalize_bot_iff j p,
    normalize_le_ceiling ht⟩

end Scheme
end
end VaughtConjecture.Knight.PairedSlotProfiles
