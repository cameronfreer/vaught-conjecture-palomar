/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyLadderRepair
public import VaughtConjecture.Knight.ReceivingRankLift

/-! # From an actual grade-one chart to an admitted LOW replacement

The separator and lawful encoding are constructed, not alignment hypotheses.
The complete LOW fibre supplies the replacement, and bounded decoding orders
the literal prescription. The physical lift consuming this producer is separate.
The rank-table and bounded interpolation proofs are reused from the checked
fixed receiving construction, without importing its LOW/HIGH family.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnly.Family
open Transform Value ExtOrd CappedDonor CanonicalPairedInverse
open LadderScalarRendering SharpWitnessComposition
noncomputable section
variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

theorem Admissible.profile_visible_one {S : State P C} (hS : F.Admissible 1 S)
    (d : Field P C) : SelfVis 1 (S.profile d) := by
  rcases d with d | d | d
  · by_cases hd : 1 < P.scheme.grade d
    · exact hS.futureP d hd
    · have hg : P.scheme.grade d = 1 := le_antisymm (not_lt.mp hd) (P.scheme.grade_pos d)
      exact hg ▸ (hS.lawfulP.orderly
        ⟨d, Finset.subset_univ _, by
          have := F.gap.K_pos; have := F.gap.K_le
          change P.scheme.grade d ≤ min 1 n
          omega⟩).symm
  · by_cases hd : 1 < C.scheme.grade d
    · exact hS.futureC d hd
    · have hg : C.scheme.grade d = 1 := le_antisymm (not_lt.mp hd) (C.scheme.grade_pos d)
      exact hg ▸ (hS.lawfulC.orderly
        ⟨d, Finset.subset_univ _, by
          have := F.gap.K_pos; have := F.gap.K_le
          change C.scheme.grade d ≤ min 1 n
          omega⟩).symm
  · simpa only [State.profile, min_eq_left (Nat.succ_le_of_lt F.gap.K_pos)] using hS.cutoff

theorem anchor_visible_one (a : F.Anchor 1) (d : Field P C) :
    SelfVis 1 (F.fields 1 a d) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  change SelfVis 1 (a.val d)
  rw [← he]
  exact hS.profile_visible_one F d

/-- A positive visible canonical grade-one field is an actual grid endpoint. -/
theorem anchor_grid_one (a : F.Anchor 1) (d : Field P C)
    (hd : F.fields 1 a d ≠ ⊥) : ∃ B, grid 1 B = F.fields 1 a d := by
  rcases (ExtOrd.mem_codedAlphabet_iff.mp
    (CanonicalPairedProfiles.inventory_coded _ _ a.property.1 d)) with hz | ⟨b, i, _, _, he⟩
  · exact (hd hz).elim
  have hvis := F.anchor_visible_one a d
  have hs := CanonicalPairedProfiles.inventory_short _ _ a.property.1 d
  change SelfVis 1 (a.val d) at hvis
  rw [he, selfVis_ofOrd_iff] at hvis
  rw [he] at hs
  simp only [Short, ofOrd_ne_bot, ofOrd_ne_top, false_or, ofOrd_inj] at hs
  obtain ⟨_, rfl, hs⟩ := hs
  have hf : finitePart (Ordinal.omega0 * b + i) = i := by
    simpa only [limitPart_omega0_mul] using
      finitePart_limitPart_add_nat (Ordinal.omega0 * b) i
  rw [hf] at hvis hs
  have hi : i = 1 := le_antisymm hs hvis
  subst i
  exact ⟨b, he.symm⟩

local instance : Fintype (C.scheme.below (effC n 1)) := Fintype.ofFinite _

/-- The chart, prescription and original cap determine a lawful encoded private
source and an actual member of the unchanged birth-grade catalogue. -/
theorem exists_private_rank_repair (a : F.Anchor 1) {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop 1) σ)
    {p : C.scheme.below (effC n 1) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC n 1) p)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (σ (SupportLadderRows.source (RelativeLadderLayer.rungs
        (X := Field P C)) (fieldRank a.val (.inr (.inl d.1))))) γ = min (p d) γ)
    (c : C.scheme.below (effC n 1)) (hactive : γ < p c) :
    ∃ b : F.Anchor 1, ∃ ν : ExtOrd → ExtOrd, ∃ B : ℕ,
      BoundedMap 1 ν ∧
      (∀ f, a.val f < grid 1 B ↔
        σ (SupportLadderRows.source (RelativeLadderLayer.rungs (X := Field P C))
          (fieldRank a.val f)) < γ) ∧
      (∀ d, ν (b.val (.inr (.inl d.1))) = p d) ∧
      ∀ f, min (a.val f) (grid 1 B) = min (b.val f) (grid 1 B) := by
  classical
  let H := RelativeLadderLayer.rungs (X := Field P C)
  let v : Field P C → ExtOrd := fun f => σ (SupportLadderRows.source H (fieldRank a.val f))
  let high := Finset.univ.filter (fun f => γ ≤ v f)
  have hact : γ ≤ v (.inr (.inl c.1)) :=
    min_eq_right_iff.mp ((hag c).trans (min_eq_right hactive.le))
  obtain ⟨f, hf, hmin⟩ := Finset.exists_min_image high a.val
    ⟨.inr (.inl c.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact⟩⟩
  have hfg : γ ≤ v f := (Finset.mem_filter.mp hf).2
  have hbot (x) (hx : a.val x = ⊥) : v x = ⊥ := by
    simp only [v, fieldRank, hx, rank_bot (bot_not_values _), SupportLadderRows.source_zero,
      hσ.bot]
  have hfb : a.val f ≠ ⊥ := fun hz => hpos.not_ge (hfg.trans_eq (hbot f hz))
  obtain ⟨B, hB⟩ := F.anchor_grid_one a f hfb
  have hcut (d) : a.val d < grid 1 B ↔ v d < γ := by
    rw [hB]
    constructor
    · intro hd
      by_contra hn
      exact hd.not_ge (hmin d (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hn⟩))
    · intro hd
      by_contra hn
      exact hd.not_ge (hfg.trans (hσ.mono (SupportLadderRows.source_mono H
        (rank_mono (values a.val) (not_lt.mp hn)))))
  let s : C.scheme.below (effC n 1) → ExtOrd := fun d => a.val (.inr (.inl d.1))
  have halign (d) (hd : γ < p d) : grid 1 B ≤ s d := by
    apply not_lt.mp
    intro hl
    have hh := (hcut (.inr (.inl d.1))).mp hl
    have he := hag d
    rw [min_eq_left hh.le, min_eq_right hd.le] at he
    exact hh.ne he
  have hroom : grid 1 B < ofOrd (Ordinal.omega0 * (↑(B + 1) : Ordinal)) :=
    ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (Nat.lt_succ_self B)) 1)
  obtain ⟨S, hS, heS⟩ := a.property.2
  have hs : RespectsSemanticsBelow C.rows (effC n 1) s := by
    have he : s = S.lowerC 1 := funext (fun d => (congrFun heS (.inr (.inl d.1))).symm)
    exact he ▸ hS.lawfulC
  let p' := AlignedCutEncoding.encode s p 1 (B + 1) (grid 1 B) γ
  have hp' : RespectsSemanticsBelow C.rows (effC n 1) p' :=
    AlignedCutEncoding.encode_respects hs hp (fun d => d.2.2.trans (min_le_left _ _))
      (grid_visible 1 B) (ofOrd_ne_bot _) hγ hroom halign
  have hp'cap (d) : min (p' d) (grid 1 B) = min (S.lowerC 1 d) (grid 1 B) := by
    rw [show S.lowerC 1 d = s d from congrFun heS (.inr (.inl d.1))]
    exact AlignedCutEncoding.encode_cap s p hroom halign d
  have hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field P C) 1 :=
    heS.symm ▸ a.property.1
  obtain ⟨T, _, hT, _, _, ⟨r⟩⟩ := F.private_protected_repair (by decide) hS hcanon hp' hp'cap
  obtain ⟨τ, hτ, hτcut, hτread⟩ := ReceivingCutDecoder.exists_chart
    (F.anchor_visible_one a)
    (fun f => CappedDonor.Ref.selfVis_map hσ le_rfl (SupportLadderRows.source_visible _ _))
    (grid_visible 1 B) (ofOrd_ne_bot _) hγ
    (fun f g h => hσ.mono (SupportLadderRows.source_mono H (rank_mono (values a.val) h)))
    hbot hcut
  let μ := PaddedSourceDecoder.extend (RelativePrefixEncoding.inventory p γ) 1 (B + 1) τ γ
  have hμ : BoundedMap 1 μ := ReceivingCutDecoder.extend_bounded _ hτ hγ
  have hμread (d) : μ (p' d) = p d := by
    apply AlignedCutEncoding.decode_encode s p hτ.mono hroom hτcut.ge
    intro e
    have hh := hτread (.inr (.inl e.1))
    change τ (s e) = min (v (.inr (.inl e.1))) γ at hh
    rw [hh, min_assoc, min_self]
    exact hag e
  let ν := μ ∘ r.decoder
  have hν : BoundedMap 1 ν := by
    refine ⟨by dsimp only [ν, Function.comp_apply]; rw [r.witness.bot, hμ.bot],
      hμ.mono.comp r.witness.mono, ?_⟩
    intro x k i hk hi
    dsimp only [ν, Function.comp_apply]
    rw [r.witness.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi,
      hμ.comm _ k i hk hi]
  refine ⟨r.anchor, ν, B, hν, hcut, ?_, ?_⟩
  · intro d
    change μ (r.decoder (r.encoded.profile (.inr (.inl d.1)))) = p d
    rw [r.readback]
    exact (congrArg μ (congrFun hT d)).trans (hμread d)
  · intro f
    exact (congrArg (fun z => min (z f) (grid 1 B)) heS).symm.trans (r.prefix_eq f).symm

end
end VaughtConjecture.Knight.LowOnly.Family
