/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingGradeOneSourceCut

/-! # Outgoing decoding at the constructed lower source cut

Interpolate only the tracked fields and the cut. This produces a bounded
replacement-commuting map, not an unjustified globally faithful composition.
The tail decoder then restores the entire private prescription literally.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingCutDecoder
open Transform Value ExtOrd SharpWitnessComposition FullRowLifting
noncomputable section

/-- A finite visible ordered table plus its actual separating cut constructs
the clipped chart. No prescribed values are required at unused source points. -/
theorem exists_chart {X : Type*} [Finite X] {s v : X → ExtOrd} {δ γ : ExtOrd}
    (hs : ∀ f, SelfVis 1 (s f)) (hv : ∀ f, SelfVis 1 (v f))
    (hδ : SelfVis 1 δ) (hδb : δ ≠ ⊥) (hγ : SelfVis 1 γ)
    (hord : ∀ f g, s f ≤ s g → v f ≤ v g)
    (hbot : ∀ f, s f = ⊥ → v f = ⊥)
    (hcut : ∀ f, s f < δ ↔ v f < γ) :
    ∃ τ, BoundedMap 1 τ ∧ τ δ = γ ∧ ∀ f, τ (s f) = min (v f) γ := by
  let : Fintype X := Fintype.ofFinite X
  let E : Option X → ExtOrd := fun d => d.elim δ s
  let t : Option X → ExtOrd := fun d => d.elim γ (fun f => min (v f) γ)
  have hE : ∀ d, SelfVis 1 (E d) := by
    intro d
    cases d with
    | none => exact hδ
    | some f => exact hs f
  have ht : ∀ d, SelfVis 1 (t d) := by
    intro d
    cases d with
    | none => exact hγ
    | some f => exact selfVis_min (hv f) hγ
  have horder : ∀ d e, E d ≤ E e → t d ≤ t e := by
    intro d e h
    cases d with
    | none =>
      cases e with
      | none => exact le_rfl
      | some f =>
        have hhi : γ ≤ v f := not_lt.mp (fun hf => ((hcut f).mpr hf).not_ge h)
        exact le_min hhi le_rfl
    | some f =>
      cases e with
      | none => exact min_le_right _ _
      | some g => exact min_le_min_right _ (hord f g h)
  have hzero : ∀ d, E d = ⊥ → t d = ⊥ := by
    intro d hd
    cases d with
    | none => exact (hδb hd).elim
    | some f => exact (congrArg (fun x => min x γ) (hbot f hd)).trans (min_bot_left _)
  refine ⟨orderInterpolate E t, orderInterpolate_bounded hE ht,
    orderInterpolate_read horder hzero none, fun f => orderInterpolate_read horder hzero (some f)⟩

/-- Extending the clipped chart only needs bounded commutation. This does
not claim the literal function composite is a faithful witness. -/
theorem extend_bounded (S : Finset Ordinal.{0}) {b : ℕ} {τ : ExtOrd → ExtOrd}
    {γ : ExtOrd} (hτ : BoundedMap 1 τ) (hγ : SelfVis 1 γ) :
    BoundedMap 1 (PaddedSourceDecoder.extend S 1 b τ γ) := by
  apply PairedSlotIncoming.bounded_max
  · refine ⟨by rw [hτ.bot, min_bot_left], fun _ _ h => min_le_min_right _ (hτ.mono h), ?_⟩
    intro x k i hk hi
    rw [hτ.comm x k i hk hi, evr_min_of_selfVis hγ hk hi]
  · exact boundedMap_of_witness (PaddedSourceDecoder.witness_release
      (isStepShifter_canonicalDecoder (S := S) (K := 1)).normalizedWitness b)

open CappedDonor CappedDonor.Ref ReceivingLadderCarrier ReceivingCatalogueSources
variable {I : Type*} [Fintype I] {nP K : ℕ} {P : SemScheme (nP + 1)}
  {C : SemScheme 2} {R : Ref I nP 2 2 P C} (L : R.LowRef K)

local instance : Fintype (C.scheme.below (effC 2 1)) := Fintype.ofFinite _
local notation "ℓ" => rungs (P := P) (C := C)

/-- Construct outgoing readback from the derived source-cut classification.
This helper exposes that classification; the physical producer supplies it. -/
theorem exists_decoder (a : Controller L) {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop 1) σ) {B b : ℕ} {γ : ExtOrd} (hγ : SelfVis 1 γ)
    (hcut : ∀ f, fields L a f < CanonicalPairedInverse.grid 2 B ↔
      σ (SupportLadderRows.source ℓ (ranks L a f)) < γ)
    (hroom : CanonicalPairedInverse.grid 2 B < ofOrd (Ordinal.omega0 * b))
    {p : C.scheme.below (effC 2 1) → ExtOrd}
    (hread : ∀ d, min (σ (SupportLadderRows.source ℓ (ranks L a (privateField d.1)))) γ =
      min (p d) γ) :
    ∃ μ, BoundedMap 1 μ ∧ μ (CanonicalPairedInverse.grid 2 B) = γ ∧
      (∀ f, min (μ (fields L a f)) γ =
        min (σ (SupportLadderRows.source ℓ (ranks L a f))) γ) ∧
      ∀ d, μ (AlignedCutEncoding.encode (fun d => fields L a (privateField d.1)) p 1 b
        (CanonicalPairedInverse.grid 2 B) γ d) = p d := by
  let v := fun f => σ (SupportLadderRows.source ℓ (ranks L a f))
  have hv : ∀ f, SelfVis 1 (v f) := by
    intro f
    exact CappedDonor.Ref.selfVis_map hσ le_rfl (SupportLadderRows.source_visible _ _)
  have ho : ∀ f g, fields L a f ≤ fields L a g → v f ≤ v g := by
    intro f g h
    exact hσ.mono (SupportLadderRows.source_mono ℓ
      (LadderScalarRendering.rank_mono (LadderScalarRendering.values (fields L a)) h))
  have hz : ∀ f, fields L a f = ⊥ → v f = ⊥ := by
    intro f hf
    have hr : ranks L a f = 0 := by
      change LadderScalarRendering.rank (LadderScalarRendering.values (fields L a)) _ = 0
      rw [hf]
      exact LadderScalarRendering.rank_bot (Finset.notMem_erase _ _)
    simp only [v, hr, SupportLadderRows.source_zero, hσ.bot]
  obtain ⟨τ, hτ, hτcut, hτread⟩ := exists_chart (fields_visible L a) hv
    (selfVis_mono (CanonicalPairedInverse.grid_visible 2 B) (by decide))
    (ofOrd_ne_bot _) hγ ho hz hcut
  let S := RelativePrefixEncoding.inventory p γ
  let μ := PaddedSourceDecoder.extend S 1 b τ γ
  have hμ := extend_bounded (b := b) S hτ hγ
  have hμcut : μ (CanonicalPairedInverse.grid 2 B) = γ := by
    dsimp only [μ]
    rw [PaddedSourceDecoder.extend_before S hroom, hτcut, min_self]
  refine ⟨μ, hμ, hμcut, ?_, ?_⟩
  · intro f
    by_cases hf : fields L a f < CanonicalPairedInverse.grid 2 B
    · dsimp only [μ]
      rw [PaddedSourceDecoder.extend_before S (hf.trans hroom), hτread, min_assoc, min_self]
      exact min_assoc _ _ _ |>.trans (congrArg (min (v f)) (min_self γ))
    · have hg : γ ≤ v f := not_lt.mp (fun h => hf ((hcut f).mpr h))
      rw [min_eq_right (hμcut.ge.trans (hμ.mono (not_lt.mp hf))), min_eq_right hg]
  · intro d
    apply AlignedCutEncoding.decode_encode _ _ hτ.mono hroom hτcut.ge _ d
    intro e
    rw [hτread, min_assoc, min_self]
    exact hread e

variable (hC : C.scheme.plan = privatePlan) (request : Cell P.scheme)
local notation "D" => carrier L hC
local notation "E" => semantics L hC request

/-- Physical inputs produce an installed replacement and ordered literal
private readback. Admission, source-cut compatibility and decoding are outputs.
The final rank-table rendering remains distinct from this raw-field decoder. -/
theorem exists_installed_repair
    {p : C.scheme.below (effC 2 1) → ExtOrd}
    {q : (D).below (Finset.univ, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC 2 1) p)
    (hq : RespectsSemanticsBelow E (Finset.univ, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (q (ReceivingGradeOnePhysicalChart.privateAt L hC d)) γ = min (p d) γ)
    (c : C.scheme.below (effC 2 1)) (hactive : γ < p c) :
    ∃ a b : Controller L, ∃ σ ν B k, Witness (gTop 1) σ ∧ BoundedMap 1 ν ∧
      (∀ d, σ (ReceivingGradeOnePhysicalChart.lowerSource L hC request a d.1) = q d) ∧
      (∀ f, fields L a f < CanonicalPairedInverse.grid 2 B ↔
        σ (SupportLadderRows.source ℓ (ranks L a f)) < γ) ∧
      (∀ d, ν (fields L b (privateField d.1)) = p d) ∧
      (∀ f, min (ν (fields L b f)) γ =
        min (σ (SupportLadderRows.source ℓ (ranks L a f))) γ) ∧
      k = LadderScalarRendering.next (LadderScalarRendering.values (fields L a))
        (CanonicalPairedInverse.grid 2 B) ∧
      0 < k ∧ k ≤ ℓ ∧ FiniteProfileControllers.Agree (ranks L a) (ranks L b) k := by
  obtain ⟨a, σ, B, t, hσ, hread, hcut, hroom, hv, hv_cap⟩ :=
    ReceivingGradeOneSourceCut.exists_encoded_prescription L hC request hp hq hγ hpos hag c hactive
  obtain ⟨μ, hμ, hμcut, hμcap, hμread⟩ := exists_decoder L a (p := p) hσ hγ hcut hroom (by
    intro d
    have hh := hread (ReceivingGradeOnePhysicalChart.privateAt L hC d)
    rw [ReceivingGradeOnePhysicalChart.lowerSource_private] at hh
    exact (congrArg (fun x => min x γ) hh).trans (hag d))
  obtain ⟨T, _, _, hlow, _, ⟨r⟩⟩ :=
    ReceivingLowerCatalogueInsertion.exists_repair L a B hv hv_cap
  let b : Controller L := ⟨r.encoded.profile, r.catalogue⟩
  let ν := μ ∘ r.decoder
  have hν : BoundedMap 1 ν := by
    refine ⟨by dsimp only [ν, Function.comp_apply]; rw [r.witness.bot, hμ.bot],
      hμ.mono.comp r.witness.mono, ?_⟩
    intro x j i hj hi
    dsimp only [ν, Function.comp_apply]
    rw [r.witness.clause5 x j (by rw [gTop_of_le (hj.trans (by decide : 1 ≤ 2))]; exact le_top)
      i hi, hμ.comm _ j i hj hi]
  let δ := CanonicalPairedInverse.grid 2 B
  let k := LadderScalarRendering.next (LadderScalarRendering.values (fields L a)) δ
  have hδ : ⊥ < δ := bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)
  have hpref (f) : min (fields L a f) δ = min (fields L b f) δ := (r.prefix_eq f).symm
  refine ⟨a, b, σ, ν, B, k, hσ, hν, hread, hcut, ?_, ?_, rfl, Nat.succ_pos _,
    (LadderScalarRendering.next_le _ _).trans
      (Nat.add_le_add_right (LadderScalarRendering.values_card_le _) 1),
    LadderScalarRendering.fieldRank_agreement hδ hpref⟩
  · intro d
    change μ (r.decoder (r.encoded.profile (privateField d.1))) = p d
    exact (congrArg μ ((r.readback (privateField d.1)).trans
      ((PrivateCatalogueRepair.profile_private T
        (ReceivingLowerCatalogueInsertion.privateUp d)).trans (hlow d)))).trans (hμread d)
  · intro f
    by_cases hf : fields L a f < δ
    · have he : fields L b f = fields L a f :=
        (PairedSlotEncoding.eq_of_cap_eq_lt (hpref f) hf).symm
      change min (μ (r.decoder (fields L b f))) γ = _
      rw [he, r.boundary_fixed f hf]
      exact hμcap f
    · have hb : δ ≤ fields L b f := by
        apply min_eq_right_iff.mp
        exact (hpref f).symm.trans (min_eq_right (not_lt.mp hf))
      have hreach : γ ≤ μ (r.decoder (fields L b f)) :=
        hμcut.ge.trans (hμ.mono (r.reaches.trans (r.witness.mono hb)))
      have hhigh : γ ≤ σ (SupportLadderRows.source ℓ (ranks L a f)) :=
        not_lt.mp (fun h => hf ((hcut f).mpr h))
      exact (min_eq_right hreach).trans (min_eq_right hhigh).symm

end
end VaughtConjecture.Knight.ReceivingCutDecoder
