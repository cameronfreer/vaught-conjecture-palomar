/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthScalarLedger
public import VaughtConjecture.Knight.ReceivingRankLift
public import VaughtConjecture.Knight.RelativeLadderLayer

/-! # Actual chart to admitted growth source

The first-reaching separator and lawful source prescription are constructed.
The proof adapts the rank encoding of `LowOnlyGradeOneSource`, but consumes
the growth private fibre and the distinct pre-activation donor fibre.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.Growth
open Transform Value ExtOrd CappedDonor CanonicalPairedInverse
open LadderScalarRendering SharpWitnessComposition
noncomputable section
variable {n J r : ℕ} {P : SemScheme (n + 1)} {C : SemScheme J}
  {F : SemScheme r} {fP : Fin r ↪ Fin (n + 1)}
  {hvP : Finset.univ.image fP ∈ P.scheme.plan} {hP : P.restrictFace fP hvP = F}
  {fC : Fin r ↪ Fin J} {hvC : Finset.univ.image fC ∈ C.scheme.plan}
  {hC : C.restrictFace fC hvC = F}
  (X : RelativeData C.scheme C.rows P.scheme P.rows)
  (R : RootAttachment F fP hvP hP fC hvC hC X)

theorem anchor_visible_one (a : Catalogue X 1) (d : Field C.scheme P.scheme) :
    SelfVis 1 (a.val d) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  rw [← he]
  exact hS.visible d

/-- A positive visible canonical grade-one field is an actual grid endpoint. -/
theorem anchor_grid_one (a : Catalogue X 1) (d : Field C.scheme P.scheme)
    (hd : a.val d ≠ ⊥) : ∃ B, grid 1 B = a.val d := by
  rcases (ExtOrd.mem_codedAlphabet_iff.mp
    (CanonicalPairedProfiles.inventory_coded _ _ a.property.1 d)) with hz | ⟨b, i, _, _, he⟩
  · exact (hd hz).elim
  have hvis := anchor_visible_one X a d
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


local instance : Fintype (C.scheme.below (Finset.univ, 1)) := Fintype.ofFinite _

include R in
/-- The chart, prescription and original cap determine a lawful encoded private
source and an actual member of the unchanged birth-grade catalogue. -/
theorem exists_private_rank_repair (a : Catalogue X 1) {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop 1) σ)
    {p : C.scheme.below (Finset.univ, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (Finset.univ, 1) p)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (σ (SupportLadderRows.source (RelativeLadderLayer.rungs
        (X := Field C.scheme P.scheme)) (fieldRank a.val (.inl d.1)))) γ = min (p d) γ)
    (c : C.scheme.below (Finset.univ, 1)) (hactive : γ < p c) :
    ∃ b : Catalogue X 1, ∃ ν : ExtOrd → ExtOrd, ∃ B : ℕ,
      BoundedMap 1 ν ∧
      (∀ f, a.val f < grid 1 B ↔
        σ (SupportLadderRows.source (RelativeLadderLayer.rungs (X := Field C.scheme P.scheme))
          (fieldRank a.val f)) < γ) ∧
      (∀ d, ν (b.val (.inl d.1)) = p d) ∧
      ∀ f, min (a.val f) (grid 1 B) = min (b.val f) (grid 1 B) := by
  classical
  let H := RelativeLadderLayer.rungs (X := Field C.scheme P.scheme)
  let v : Field C.scheme P.scheme → ExtOrd :=
    fun f => σ (SupportLadderRows.source H (fieldRank a.val f))
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
  obtain ⟨B, hB⟩ := anchor_grid_one X a f hfb
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
  let s : C.scheme.below (Finset.univ, 1) → ExtOrd := fun d => a.val (.inl d.1)
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
  have hs : RespectsSemanticsBelow C.rows (Finset.univ, 1) s := by
    have he : s = (fun d : C.scheme.below (Finset.univ, 1) => S.privateValues d.1) :=
      funext (fun d => (congrFun heS (.inl d.1)).symm)
    exact he ▸ hS.private_lawful
  let p' := AlignedCutEncoding.encode s p 1 (B + 1) (grid 1 B) γ
  have hp' : RespectsSemanticsBelow C.rows (Finset.univ, 1) p' :=
    AlignedCutEncoding.encode_respects hs hp (fun d => d.2.2)
      (grid_visible 1 B) (ofOrd_ne_bot _) hγ hroom halign
  have hp'cap (d) : min (p' d) (grid 1 B) = min (S.privateValues d.1) (grid 1 B) := by
    rw [show S.privateValues d.1 = s d from congrFun heS (.inl d.1)]
    exact AlignedCutEncoding.encode_cap s p hroom halign d
  have hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field C.scheme P.scheme) 1 :=
    heS.symm ▸ a.property.1
  obtain ⟨U, _, hU, _, _, _, ⟨r⟩⟩ := R.private_protected_all (by decide) hS hcanon hp' hp'cap
  obtain ⟨τ, hτ, hτcut, hτread⟩ := ReceivingCutDecoder.exists_chart
    (anchor_visible_one X a)
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
  refine ⟨⟨r.encoded.profile, r.canonical, r.encoded, r.admitted, rfl⟩, ν, B, hν, hcut, ?_, ?_⟩
  · intro d
    change μ (r.decoder (r.encoded.profile (.inl d.1))) = p d
    rw [r.readback]
    exact (congrArg μ (hU d)).trans (hμread d)
  · intro f
    exact (congrArg (fun z => min (z f) (grid 1 B)) heS).symm.trans (r.prefix_eq f).symm

local instance : Fintype (P.scheme.below (Finset.univ, 1)) := Fintype.ofFinite _

include R in
/-- The chart, prescription and original cap determine a lawful encoded donor
source and an actual member of the unchanged birth-grade catalogue. -/
theorem exists_donor_rank_repair (hN : 1 < X.req.N) (a : Catalogue X 1) {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop 1) σ)
    {p : P.scheme.below (Finset.univ, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow P.rows (Finset.univ, 1) p)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (σ (SupportLadderRows.source (RelativeLadderLayer.rungs
        (X := Field C.scheme P.scheme)) (fieldRank a.val (.inr d.1)))) γ = min (p d) γ)
    (c : P.scheme.below (Finset.univ, 1)) (hactive : γ < p c) :
    ∃ b : Catalogue X 1, ∃ ν : ExtOrd → ExtOrd, ∃ B : ℕ,
      BoundedMap 1 ν ∧
      (∀ f, a.val f < grid 1 B ↔
        σ (SupportLadderRows.source (RelativeLadderLayer.rungs (X := Field C.scheme P.scheme))
          (fieldRank a.val f)) < γ) ∧
      (∀ d, ν (b.val (.inr d.1)) = p d) ∧
      ∀ f, min (a.val f) (grid 1 B) = min (b.val f) (grid 1 B) := by
  classical
  let H := RelativeLadderLayer.rungs (X := Field C.scheme P.scheme)
  let v : Field C.scheme P.scheme → ExtOrd :=
    fun f => σ (SupportLadderRows.source H (fieldRank a.val f))
  let high := Finset.univ.filter (fun f => γ ≤ v f)
  have hact : γ ≤ v (.inr c.1) :=
    min_eq_right_iff.mp ((hag c).trans (min_eq_right hactive.le))
  obtain ⟨f, hf, hmin⟩ := Finset.exists_min_image high a.val
    ⟨.inr c.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact⟩⟩
  have hfg : γ ≤ v f := (Finset.mem_filter.mp hf).2
  have hbot (x) (hx : a.val x = ⊥) : v x = ⊥ := by
    simp only [v, fieldRank, hx, rank_bot (bot_not_values _), SupportLadderRows.source_zero,
      hσ.bot]
  have hfb : a.val f ≠ ⊥ := fun hz => hpos.not_ge (hfg.trans_eq (hbot f hz))
  obtain ⟨B, hB⟩ := anchor_grid_one X a f hfb
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
  let s : P.scheme.below (Finset.univ, 1) → ExtOrd := fun d => a.val (.inr d.1)
  have halign (d) (hd : γ < p d) : grid 1 B ≤ s d := by
    apply not_lt.mp
    intro hl
    have hh := (hcut (.inr d.1)).mp hl
    have he := hag d
    rw [min_eq_left hh.le, min_eq_right hd.le] at he
    exact hh.ne he
  have hroom : grid 1 B < ofOrd (Ordinal.omega0 * (↑(B + 1) : Ordinal)) :=
    ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (Nat.lt_succ_self B)) 1)
  obtain ⟨S, hS, heS⟩ := a.property.2
  have hs : RespectsSemanticsBelow P.rows (Finset.univ, 1) s := by
    have he : s = (fun d : P.scheme.below (Finset.univ, 1) => S.donorValues d.1) :=
      funext (fun d => (congrFun heS (.inr d.1)).symm)
    exact he ▸ hS.donor_lawful
  let p' := AlignedCutEncoding.encode s p 1 (B + 1) (grid 1 B) γ
  have hp' : RespectsSemanticsBelow P.rows (Finset.univ, 1) p' :=
    AlignedCutEncoding.encode_respects hs hp (fun d => d.2.2)
      (grid_visible 1 B) (ofOrd_ne_bot _) hγ hroom halign
  have hp'cap (d) : min (p' d) (grid 1 B) = min (S.donorValues d.1) (grid 1 B) := by
    rw [show S.donorValues d.1 = s d from congrFun heS (.inr d.1)]
    exact AlignedCutEncoding.encode_cap s p hroom halign d
  have hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field C.scheme P.scheme) 1 :=
    heS.symm ▸ a.property.1
  obtain ⟨U, _, hU, _, _, _, ⟨r⟩⟩ := R.donor_protected_before (by decide) hN hS hcanon hp' hp'cap
  obtain ⟨τ, hτ, hτcut, hτread⟩ := ReceivingCutDecoder.exists_chart
    (anchor_visible_one X a)
    (fun f => CappedDonor.Ref.selfVis_map hσ le_rfl (SupportLadderRows.source_visible _ _))
    (grid_visible 1 B) (ofOrd_ne_bot _) hγ
    (fun f g h => hσ.mono (SupportLadderRows.source_mono H (rank_mono (values a.val) h)))
    hbot hcut
  let μ := PaddedSourceDecoder.extend (RelativePrefixEncoding.inventory p γ) 1 (B + 1) τ γ
  have hμ : BoundedMap 1 μ := ReceivingCutDecoder.extend_bounded _ hτ hγ
  have hμread (d) : μ (p' d) = p d := by
    apply AlignedCutEncoding.decode_encode s p hτ.mono hroom hτcut.ge
    intro e
    have hh := hτread (.inr e.1)
    change τ (s e) = min (v (.inr e.1)) γ at hh
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
  refine ⟨⟨r.encoded.profile, r.canonical, r.encoded, r.admitted, rfl⟩, ν, B, hν, hcut, ?_, ?_⟩
  · intro d
    change μ (r.decoder (r.encoded.profile (.inr d.1))) = p d
    rw [r.readback]
    exact (congrArg μ (hU d)).trans (hμread d)
  · intro f
    exact (congrArg (fun z => min (z f) (grid 1 B)) heS).symm.trans (r.prefix_eq f).symm

end
end VaughtConjecture.Knight.Growth
