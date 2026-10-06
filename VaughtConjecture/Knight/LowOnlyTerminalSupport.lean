/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyTerminal
public import VaughtConjecture.Knight.CappedDonorDecoderStage

/-! # Supported literal-top insertion for the LOW catalogue

The terminal cap is included in the decoder grid. Consequently every decoded
value, not just represented fields, is supported by the original complete
vector with bottom and top allowed. This adapts the ordinary receiver's
supported terminal insertion without changing LOW or the existing API.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnly.Family
open Transform Value ExtOrd CappedDonor CappedDonor.Ref
noncomputable section
variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

/-- Literal-top insertion with all-output support, including unused decoder
arguments. The fresh terminal block need not lie below the final model stage. -/
theorem terminal_insertion_supported {j : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) (h : Ordinal.{0}) :
    ∃ S₀ Q : State P C, F.Admissible j S₀ ∧ (∀ d, S₀.profile d ≠ ⊤) ∧
      S.CapEq (ofOrd h) S₀ ∧ Q = S₀.normalize j ∧ F.Admissible j Q ∧
      Q.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j ∧
      ∃ δ : ExtOrd → ExtOrd, Witness (gTop j) δ ∧
        (∀ d, δ (Q.profile d) = S.profile d) ∧
        ∀ x, OrbitPrefixSupport.Supported j ({⊤} : Set ExtOrd) S.profile (δ x) := by
  let l := S.freshFloor h
  have hlim : limitPart l = l := S.freshFloor_limit h
  let β : ExtOrd := ofOrd (l + j)
  have hβvis : SelfVis j β := by
    change SelfVis j (ofOrd (l + j))
    rw [selfVis_ofOrd_iff]
    have he := finitePart_limitPart_add_nat l j
    rw [hlim] at he
    exact he.ge
  have hβbot : β ≠ ⊥ := ofOrd_ne_bot _
  have hlβ : ofOrd l ≤ β := ofOrd_le_ofOrd.mpr le_self_add
  let S₀ := S.map (fun x => min x β)
  have hS₀ : F.Admissible j S₀ :=
    hS.map F (capWitness hβvis hβbot) hj (capWitness_reflects_bottom hβbot)
  have hproper : ∀ d, S₀.profile d ≠ ⊤ := by
    intro d
    rw [State.profile_map]
    exact fun ht => ofOrd_ne_top _ ((min_eq_top.mp ht).2)
  have hprefix : S.CapEq (ofOrd h) S₀ := by
    apply State.capEq_iff_profile.mpr
    intro d
    rw [State.profile_map, min_assoc, min_eq_right
      ((ofOrd_le_ofOrd.mpr (S.lt_freshFloor h (Finset.mem_insert_self _ _)).le).trans hlβ)]
  refine ⟨S₀, S₀.normalize j, hS₀, hproper, hprefix, rfl,
    F.normalize_admissible hj hS₀, normalize_inventory j hproper, ?_⟩
  have hG : ∀ z ∈ ({β} : Finset ExtOrd), SelfVis j z := fun z hz => by
    rw [Finset.mem_singleton.mp hz]
    exact hβvis
  refine ⟨collapseBlock l ∘ PairedSlotDecoder.decode j
    (PairedSlotEncoding.values S₀.profile) {β} β,
    Witness.comp_of_bottom_reflecting (PairedSlotDecoder.decode_witness hG hβvis)
      (collapseBlock_witness j hlim) le_rfl (collapseBlock_reflects_bottom l), ?_, ?_⟩
  · intro d
    rw [Function.comp_apply, State.profile_normalize,
      PairedSlotDecoder.decode_normalize hG hβvis hproper d, State.profile_map]
    exact collapseBlock_min hlβ (S.profile_lt_freshFloor h d)
  · intro x
    rw [Function.comp_apply]
    rcases PairedSlotDecoder.decode_supported (j := j) (K := j) (p := S₀.profile)
        le_rfl (Finset.mem_singleton_self β) x with hz | hβ | ⟨d, i, hi, he⟩
    · rw [hz]
      exact Or.inl (collapseBlock_witness j hlim).bot
    · rw [Finset.mem_singleton.mp (Finset.mem_coe.mp hβ), collapseBlock_of_le hlβ]
      exact Or.inr (Or.inl (Set.mem_singleton _))
    · rw [he, State.profile_map]
      rcases S.profile_lt_freshFloor h d with hlt | ht
      · rw [min_eq_left (hlt.le.trans hlβ),
          collapseBlock_of_lt (evr_lt_of_lt_limit hlim hlt j i)]
        exact Or.inr (Or.inr ⟨d, i, hi, rfl⟩)
      · rw [ht, min_top_left, evr_eq_self_of_selfVis hβvis i, collapseBlock_of_le hlβ]
        exact Or.inr (Or.inl (Set.mem_singleton _))

/-- A catalogue member and exact decoder with the finite bottom reflection
needed by the long padded rows, and support on every decoder argument. -/
theorem exists_supported_decoder {j : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) :
    ∃ Q : State P C, F.Admissible j Q ∧
      Q.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j ∧
      ∃ δ : ExtOrd → ExtOrd, Witness (gTop j) δ ∧
        (∀ d, δ (Q.profile d) = S.profile d) ∧
        (∀ d, δ (Q.profile d) = ⊥ → Q.profile d = ⊥) ∧
        ∀ x, OrbitPrefixSupport.Supported j ({⊤} : Set ExtOrd) S.profile (δ x) := by
  obtain ⟨S₀, Q, _, _, hcap, hQeq, hQ, hcanon, δ, hδ, hread, hsupp⟩ :=
    F.terminal_insertion_supported hj hS 0
  refine ⟨Q, hQ, hcanon, δ, hδ, hread, ?_, hsupp⟩
  intro d hd
  have hSd : S.profile d = ⊥ := (hread d).symm.trans hd
  have he := State.capEq_iff_profile.mp hcap d
  rw [hSd, min_bot_left] at he
  have hS₀ : S₀.profile d = ⊥ := (min_eq_bot.mp he).resolve_right (ofOrd_ne_bot 0)
  rw [hQeq, State.profile_normalize]
  exact (PairedSlotEncoding.normalize_bot_iff j S₀.profile d).mpr hS₀

end
end VaughtConjecture.Knight.LowOnly.Family
