/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyNormalization
public import VaughtConjecture.Knight.CappedDonorLowHighNormalization

/-! # Literal-top insertion in the gate-free canonical catalogue

Attribution: the fresh terminal block and scalar whole-block collapse are the
construction in `CappedDonorLowHighNormalization`. Only those scalar tools are
reused here; no `Ref`, LOW/HIGH state, or gate is constructed. Exact decoding is
on the complete original-field inventory, not on uninstalled physical rows.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref

noncomputable section

variable {n K : ℕ} {P C : SemScheme n}

namespace State

def freshFloor (S : State P C) (h : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.omega0 * ((insert h (PairedSlotEncoding.values S.profile)).sup id + 1)

theorem freshFloor_limit (S : State P C) (h : Ordinal.{0}) :
    limitPart (S.freshFloor h) = S.freshFloor h := limitPart_omega0_mul _

theorem lt_freshFloor (S : State P C) (h : Ordinal.{0}) {a : Ordinal.{0}}
    (ha : a ∈ insert h (PairedSlotEncoding.values S.profile)) : a < S.freshFloor h := by
  unfold freshFloor
  set m := (insert h (PairedSlotEncoding.values S.profile)).sup id
  exact (Order.lt_add_one_iff.mpr (Finset.le_sup (f := id) ha)).trans_le
    (Ordinal.le_mul_right (m + 1) Ordinal.omega0_pos)

theorem profile_lt_freshFloor (S : State P C) (h : Ordinal.{0}) (d : Field P C) :
    S.profile d < ofOrd (S.freshFloor h) ∨ S.profile d = ⊤ := by
  rcases ExtOrd.cases (S.profile d) with hb | ht | ⟨a, ha⟩
  · exact Or.inl (hb ▸ bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _))
  · exact Or.inr ht
  · refine Or.inl ?_
    rw [ha, ofOrd_lt_ofOrd]
    exact S.lt_freshFloor h (Finset.mem_insert_of_mem
      (PairedSlotEncoding.mem_values.mpr ⟨d, ha⟩))

end State

namespace Family

variable (F : Family P C K)

/-- Every admitted complete vector, including literal top, has an admitted proper
canonical representative and an exact outgoing decoder. Properization preserves
the prescribed raw prefix; no unused physical-grid fixation is claimed. -/
theorem terminal_insertion {j : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) (h : Ordinal.{0}) :
    ∃ S₀ Q : State P C, F.Admissible j S₀ ∧ (∀ d, S₀.profile d ≠ ⊤) ∧
      S.CapEq (ofOrd h) S₀ ∧ Q = S₀.normalize j ∧ F.Admissible j Q ∧
      Q.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j ∧
      ∃ δ : ExtOrd → ExtOrd, Witness (gTop j) δ ∧ ∀ d, δ (Q.profile d) = S.profile d := by
  let l := S.freshFloor h
  have hlim : limitPart l = l := S.freshFloor_limit h
  let β : ExtOrd := ofOrd (l + j)
  have hβvis : SelfVis j β := by
    change SelfVis j (ofOrd (l + j))
    rw [selfVis_ofOrd_iff]
    have h := finitePart_limitPart_add_nat l j
    rw [hlim] at h
    exact h.ge
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
  have hG : ∀ z ∈ (∅ : Finset ExtOrd), SelfVis j z :=
    fun z hz => absurd hz (Finset.notMem_empty z)
  refine ⟨collapseBlock l ∘ PairedSlotDecoder.decode j
    (PairedSlotEncoding.values S₀.profile) ∅ β,
    Witness.comp_of_bottom_reflecting (PairedSlotDecoder.decode_witness hG hβvis)
      (collapseBlock_witness j hlim) le_rfl (collapseBlock_reflects_bottom l), ?_⟩
  intro d
  rw [Function.comp_apply, State.profile_normalize,
    PairedSlotDecoder.decode_normalize hG hβvis hproper d, State.profile_map]
  exact collapseBlock_min hlβ (S.profile_lt_freshFloor h d)

/-- Both stages of the private repair, with no supplied admitted replacement.
The raw repair retains the prescription and all caps; the canonical member
decodes to that entire raw vector, cutoff and future coordinates included. -/
theorem private_catalogue_repair {j : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (v d) γ = min (S.lowerC j d) γ) :
    ∃ S' Q : State P C, F.Admissible j S' ∧ S'.lowerC j = v ∧
      S.CapEq γ S' ∧ S.FutureEq j S' ∧ F.Admissible j Q ∧
      Q.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j ∧
      ∃ δ : ExtOrd → ExtOrd, Witness (gTop j) δ ∧ ∀ d, δ (Q.profile d) = S'.profile d := by
  obtain ⟨S', hS', hv', hcap, hfuture⟩ := F.private_lift hS hv hγ hag
  obtain ⟨_, Q, _, _, _, _, hQ, hcanon, hdecode⟩ := F.terminal_insertion hj hS' 0
  exact ⟨S', Q, hS', hv', hcap, hfuture, hQ, hcanon, hdecode⟩

/-- The donor-prescribed catalogue fibre uses private release, not an exchange
of the asymmetric LOW relation. -/
theorem donor_catalogue_repair {j : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (u d) γ = min (S.lowerP j d) γ) :
    ∃ S' Q : State P C, F.Admissible j S' ∧ S'.lowerP j = u ∧
      S.CapEq γ S' ∧ S.FutureEq j S' ∧ F.Admissible j Q ∧
      Q.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j ∧
      ∃ δ : ExtOrd → ExtOrd, Witness (gTop j) δ ∧ ∀ d, δ (Q.profile d) = S'.profile d := by
  obtain ⟨S', hS', hu', hcap, hfuture⟩ := F.donor_lift hS hu hγ hag
  obtain ⟨_, Q, _, _, _, _, hQ, hcanon, hdecode⟩ := F.terminal_insertion hj hS' 0
  exact ⟨S', Q, hS', hu', hcap, hfuture, hQ, hcanon, hdecode⟩

end Family
end
end VaughtConjecture.Knight.LowOnly
