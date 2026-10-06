/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyGradeOneSource

/-! # Donor-side source repair from an actual grade-one chart

The first-reaching represented cut and rank decoding follow
`LowOnlyGradeOneSource.exists_private_rank_repair`. The lawfulness input is the
actual donor restriction, and the asymmetric step consumes
`donor_protected_repair`. The LOW family and its two face roles are never swapped.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnly.Family
open Transform Value ExtOrd CappedDonor CanonicalPairedInverse
open LadderScalarRendering SharpWitnessComposition
noncomputable section
variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

local instance donorSourceFintype : Fintype (P.scheme.below (effC n 1)) := Fintype.ofFinite _

/-- The chart, prescription and original cap determine a lawful encoded donor
source and an actual member of the unchanged birth-grade catalogue. -/
theorem exists_donor_rank_repair (a : F.Anchor 1) {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop 1) σ)
    {p : P.scheme.below (effC n 1) → ExtOrd}
    (hp : RespectsSemanticsBelow P.rows (effC n 1) p)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (σ (SupportLadderRows.source (RelativeLadderLayer.rungs
        (X := Field P C)) (fieldRank a.val (.inl d.1)))) γ = min (p d) γ)
    (c : P.scheme.below (effC n 1)) (hactive : γ < p c) :
    ∃ b : F.Anchor 1, ∃ ν : ExtOrd → ExtOrd, ∃ B : ℕ,
      BoundedMap 1 ν ∧
      (∀ f, a.val f < grid 1 B ↔
        σ (SupportLadderRows.source (RelativeLadderLayer.rungs (X := Field P C))
          (fieldRank a.val f)) < γ) ∧
      (∀ d, ν (b.val (.inl d.1)) = p d) ∧
      ∀ f, min (a.val f) (grid 1 B) = min (b.val f) (grid 1 B) := by
  classical
  let H := RelativeLadderLayer.rungs (X := Field P C)
  let v : Field P C → ExtOrd := fun f => σ (SupportLadderRows.source H (fieldRank a.val f))
  let high := Finset.univ.filter (fun f => γ ≤ v f)
  have hact : γ ≤ v (.inl c.1) :=
    min_eq_right_iff.mp ((hag c).trans (min_eq_right hactive.le))
  obtain ⟨f, hf, hmin⟩ := Finset.exists_min_image high a.val
    ⟨.inl c.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact⟩⟩
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
  let s : P.scheme.below (effC n 1) → ExtOrd := fun d => a.val (.inl d.1)
  have halign (d) (hd : γ < p d) : grid 1 B ≤ s d := by
    apply not_lt.mp
    intro hl
    have hh := (hcut (.inl d.1)).mp hl
    have he := hag d
    rw [min_eq_left hh.le, min_eq_right hd.le] at he
    exact hh.ne he
  have hroom : grid 1 B < ofOrd (Ordinal.omega0 * (↑(B + 1) : Ordinal)) :=
    ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (Nat.lt_succ_self B)) 1)
  obtain ⟨S, hS, heS⟩ := a.property.2
  have hs : RespectsSemanticsBelow P.rows (effC n 1) s := by
    have he : s = S.lowerP 1 := funext (fun d => (congrFun heS (.inl d.1)).symm)
    exact he ▸ hS.lawfulP
  let p' := AlignedCutEncoding.encode s p 1 (B + 1) (grid 1 B) γ
  have hp' : RespectsSemanticsBelow P.rows (effC n 1) p' :=
    AlignedCutEncoding.encode_respects hs hp (fun d => d.2.2.trans (min_le_left _ _))
      (grid_visible 1 B) (ofOrd_ne_bot _) hγ hroom halign
  have hp'cap (d) : min (p' d) (grid 1 B) = min (S.lowerP 1 d) (grid 1 B) := by
    rw [show S.lowerP 1 d = s d from congrFun heS (.inl d.1)]
    exact AlignedCutEncoding.encode_cap s p hroom halign d
  have hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field P C) 1 :=
    heS.symm ▸ a.property.1
  obtain ⟨T, _, hT, _, _, ⟨r⟩⟩ := F.donor_protected_repair (by decide) hS hcanon hp' hp'cap
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
    have hh := hτread (.inl e.1)
    change τ (s e) = min (v (.inl e.1)) γ at hh
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
    change μ (r.decoder (r.encoded.profile (.inl d.1))) = p d
    rw [r.readback]
    exact (congrArg μ (congrFun hT d)).trans (hμread d)
  · intro f
    exact (congrArg (fun z => min (z f) (grid 1 B)) heS).symm.trans (r.prefix_eq f).symm

end
end VaughtConjecture.Knight.LowOnly.Family
