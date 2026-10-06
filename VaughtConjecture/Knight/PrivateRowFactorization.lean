/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OwnerLocalAlignment
public import VaughtConjecture.Knight.CanonicalPairedProfiles

/-! # Private-row factorization with frozen source receipts

This adapter concerns an actual original owner's lower domain. It constructs
the lawful replacement section and its bounded outgoing witness from the old
source and actual prescribed lawfulness. It does not install a receiving
catalogue or assume that arbitrary physical sections are source states.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.PrivateRowFactorization
open Transform Value ExtOrd SharpWitnessComposition OwnerLocalEndpoint
noncomputable section

theorem coded_proper {m j : ℕ} {x : ExtOrd} (hx : x ∈ ExtOrd.codedAlphabet m j) :
    x ≠ ⊤ := by
  rcases ExtOrd.mem_codedAlphabet_iff.mp hx with rfl | ⟨b, i, _, _, rfl⟩
  · exact bot_ne_top
  · exact ofOrd_ne_top _

theorem code_spec {m j : ℕ} {x : ExtOrd}
    (hc : x ∈ ExtOrd.codedAlphabet m j) (hs : Short j x) :
    x = ⊥ ∨ ∃ b i : ℕ, b ≤ m ∧ i ≤ j ∧ x = ofOrd (Ordinal.omega0 * b + i) := by
  rcases ExtOrd.mem_codedAlphabet_iff.mp hc with hb | ⟨b, i, hb, _, he⟩
  · exact Or.inl hb
  · refine Or.inr ⟨b, i, hb, ?_, he⟩
    rcases hs with hz | ht | ⟨u, hu, hj⟩
    · exact (ofOrd_ne_bot _ (he.symm.trans hz)).elim
    · exact (ofOrd_ne_top _ (he.symm.trans ht)).elim
    have heq := ofOrd_inj.mp (he.symm.trans hu)
    simpa only [← heq, finitePart_mul_add] using hj

theorem code_bound {m j : ℕ} {x : ExtOrd}
    (hc : x ∈ ExtOrd.codedAlphabet m j) (hs : Short j x) :
    x ≤ ofOrd (Ordinal.omega0 * m + j) := by
  rcases code_spec hc hs with rfl | ⟨b, i, hb, hi, rfl⟩
  · exact bot_le
  · apply ofOrd_le_ofOrd.mpr
    apply add_le_add
    · gcongr
    · exact Nat.cast_le.mpr hi

theorem endpoint_grid {m j : ℕ} {x : ExtOrd}
    (hc : x ∈ ExtOrd.codedAlphabet (2 * m) j) (hs : Short j x) :
    endpoint j x ∈ PairedSlotComparison.sourceGrid j m := by
  rcases code_spec hc hs with rfl | ⟨b, i, hb, hi, rfl⟩
  · exact PairedSlotComparison.sourceGrid_bot j m
  · have he : endpoint j (ofOrd (Ordinal.omega0 * b + i)) =
        ofOrd (Ordinal.omega0 * b + j) := by
      by_cases hij : i < j
      · rw [endpoint, extVisibilityReplace_of_finitePart_lt (by
          rw [finitePart_mul_add]; exact hij), limitPart_mul_add]
      · have hi' : i = j := by omega
        subst i
        apply endpoint_of_selfVis
        apply selfVis_ofOrd_iff.mpr
        rw [finitePart_mul_add]
    rw [he]
    exact PairedSlotComparison.sourceGrid_endpoint (hb.trans (Nat.le_succ _))

theorem short_replace {j k i : ℕ} {x : ExtOrd} (hx : Short j x)
    (hk : k ≤ j) (hi : i ≤ k) : Short j (extVisibilityReplace x k i) := by
  rcases hx with rfl | rfl | ⟨u, rfl, hu⟩
  · exact Or.inl (extVisibilityReplace_bot _ _)
  · exact Or.inr (Or.inl (extVisibilityReplace_top _ _))
  · by_cases hut : finitePart u < k
    · rw [extVisibilityReplace_of_finitePart_lt hut]
      exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_limitPart_add_nat]; exact hi.trans hk⟩)
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hut)]
      exact Or.inr (Or.inr ⟨u, rfl, hu⟩)

theorem encoded_proper {X : Type*} [Fintype X] {s p : X → ExtOrd}
    {j b : ℕ} {h δ : ExtOrd} (hs : ∀ d, s d ≠ ⊤)
    (hroom : h < ofOrd (Ordinal.omega0 * b)) (d : X) :
    AlignedCutEncoding.encode s p j b h δ d ≠ ⊤ := by
  by_cases hd : p d ≤ δ
  · rw [AlignedCutEncoding.encode_of_le s p j b h δ d hd]
    intro ht
    exact hs d (top_le_iff.mp (ht ▸ min_le_left (s d) h))
  · rw [AlignedCutEncoding.encode_of_gt s p hroom d (not_le.mp hd)]
    exact coded_proper (PaddedSourceDecoder.encode_mem _ j b _)

/-- Retuning and tail decoding retain the external cap on every short source,
not only represented fields. The final owner clip allows literal-top targets. -/
theorem outgoing_cap {j b : ℕ} {σ ρ : ExtOrd → ExtOrd} {h δ γ M : ExtOrd}
    (S : Finset Ordinal.{0}) (hσ : Monotone σ)
    (hρ : Witness (gTop j) ρ) (hδ : SelfVis j δ) (hM : SelfVis j M)
    (hroom : h < ofOrd (Ordinal.omega0 * b)) (hread : ρ h = δ)
    (hγδ : γ ≤ δ) (hδM : δ ≤ M) (hreach : γ ≤ σ h)
    (hcap : ∀ x, Short j x → min (ρ x) γ = min (σ x) γ)
    {x : ExtOrd} (hx : Short j x) :
    min (min (PaddedSourceDecoder.extend S j b ρ δ x) M) γ = min (σ x) γ := by
  by_cases hlow : x < ofOrd (Ordinal.omega0 * b)
  · rw [PaddedSourceDecoder.extend_before S hlow, min_assoc, min_eq_right (hγδ.trans hδM),
      min_assoc, min_eq_right hγδ]
    exact hcap x hx
  · have hhx : h ≤ x := hroom.le.trans (not_lt.mp hlow)
    have hν := FreeDiagonal.clip_witness (PaddedSourceDecoder.extend_witness (b := b) S hρ hδ) hM
    have hat : min (PaddedSourceDecoder.extend S j b ρ δ h) M = δ := by
      rw [PaddedSourceDecoder.extend_before S hroom, hread, min_self, min_eq_left hδM]
    have hνx : γ ≤ min (PaddedSourceDecoder.extend S j b ρ δ x) M :=
      hγδ.trans (hat.ge.trans (hν.mono hhx))
    rw [min_eq_right hνx, min_eq_right (hreach.trans (hσ hhx))]

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable {sem : Semantics D}

/-- Output receipts, all constructed by `at_first_cut` below. The source is
proper but need not be normalized: it is the input to the scalar fibre and
supported inverse, not a new row added to the frozen catalogue. -/
structure Factorization (c : Cell D) (s p : D.below (D.cell c) → ExtOrd)
    (σ : ExtOrd → ExtOrd) (γ δ : ExtOrd) where
  source : D.below (D.cell c) → ExtOrd
  outgoing : ExtOrd → ExtOrd
  lawful : RespectsSemanticsBelow sem (D.cell c) source
  proper : ∀ d, source d ≠ ⊤
  witness : Witness (gTop (D.grade c)) outgoing
  bounded : ∀ x, outgoing x ≤ p ⟨c, GradedLe.refl _⟩
  readback : ∀ d, outgoing (source d) = min (p d) (p ⟨c, GradedLe.refl _⟩)
  prefix_eq : ∀ d, min (source d) δ = min (s d) δ
  reaches : γ ≤ outgoing δ
  caps : ∀ x, Short (D.grade c) x → min (outgoing x) γ = min (σ x) γ

/-- Arbitrary lawful original rows, with no chain/private-shape restriction.
The fixed first grid cut is not identified with the owner-local endpoint.
The latter may be larger; its stronger preserved prefix implies the required
original prefix. Alignment, repaired lawfulness and the outgoing map are outputs. -/
theorem at_first_cut (c : Cell D)
    {s p : D.below (D.cell c) → ExtOrd} (m : ℕ)
    (hs : RespectsSemanticsBelow sem (D.cell c) s)
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    (hcoded : ∀ e, s e ∈ ExtOrd.codedAlphabet (2 * m) (D.grade c))
    (hshort : ∀ e, Short (D.grade c) (s e))
    {σ : ExtOrd → ExtOrd} {γ δ : ExtOrd}
    (hσ : Witness (gTop (D.grade c)) σ) (hγ : SelfVis (D.grade c) γ)
    (hpos : ⊥ < γ) (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    (hface : ∀ e, min (σ (s e)) γ = min (p e) γ)
    (hδ : δ ∈ PairedSlotComparison.sourceGrid (D.grade c) m) (hreach : γ ≤ σ δ)
    (hfirst : ∀ z ∈ PairedSlotComparison.sourceGrid (D.grade c) m, z < δ → σ z < γ) :
    Nonempty (Factorization (sem := sem) c s p σ γ δ) := by
  classical
  let := Fintype.ofFinite (D.below (D.cell c))
  let self : D.below (D.cell c) := ⟨c, GradedLe.refl _⟩
  let M := p self
  let τ := fun x => min (σ x) γ
  have hτ : Witness (gTop (D.grade c)) τ := FreeDiagonal.clip_witness hσ hγ
  have hτbound : ∀ x, τ x ≤ γ := fun _ => min_le_right _ _
  have htface : ∀ e, τ (s e) = min (p e) γ := hface
  have hproper : ∀ e, s e ≠ ⊤ := fun e => coded_proper (hcoded e)
  have hbudget := code_bound (hcoded self) (hshort self)
  obtain ⟨η, ρ, β, f, H, _, _, _, hroom, hρ, hγβ, hβM, hβvis, hρη,
      hf, hfprefix, hfdef, hfread, _, hρcap⟩ :=
    OwnerLocalAlignment.exists_coded_face c hs hp hproper hshort m hbudget
      hτ hγ hpos hτbound htface hpc
  have sat : Saturation (D.grade c) s p self τ γ :=
    Saturation.of_witness hτ hτbound hpos hpc htface hproper (hs.orderly self).symm
  have hηreach : γ ≤ σ η := (H.reach sat).ge.trans (min_le_left _ _)
  have hηgrid : η ∈ PairedSlotComparison.sourceGrid (D.grade c) m := by
    obtain ⟨e, _, he⟩ := H.exists_witness
    rw [← he]
    exact endpoint_grid (hcoded e) (hshort e)
  have hδη : δ ≤ η := by
    by_contra hn
    exact (not_lt_of_ge hηreach) (hfirst η hηgrid (not_le.mp hn))
  let S := RelativePrefixEncoding.inventory (fun e => min (p e) M) β
  let ν := fun x => min (PaddedSourceDecoder.extend S (D.grade c) (2 * m + 1) ρ β x) M
  have hMvis : SelfVis (D.grade c) M := (hp.orderly self).symm
  have hν : Witness (gTop (D.grade c)) ν :=
    FreeDiagonal.clip_witness (PaddedSourceDecoder.extend_witness S hρ hβvis) hMvis
  have hcaps : ∀ x, Short (D.grade c) x → min (ν x) γ = min (σ x) γ := by
    intro x hx
    apply outgoing_cap S hσ.mono hρ hβvis hMvis hroom hρη hγβ hβM hηreach
      (fun z hz => ?_) hx
    simpa only [τ, min_assoc, min_self] using hρcap z hz
  refine ⟨{
    source := f
    outgoing := ν
    lawful := hf
    proper := ?_
    witness := hν
    bounded := fun _ => min_le_right _ _
    readback := ?_
    prefix_eq := ?_
    reaches := ?_
    caps := hcaps }⟩
  · intro e
    rw [hfdef]
    exact encoded_proper hproper hroom e
  · intro e
    change min (PaddedSourceDecoder.extend S (D.grade c) (2 * m + 1) ρ β (f e)) M = _
    rw [hfread e, min_assoc, min_self]
  · intro e
    have he := congrArg (fun x => min x δ) (hfprefix e)
    simpa only [min_assoc, min_eq_right hδη] using he
  · have hδshort : Short (D.grade c) δ := by
      rcases Finset.mem_insert.mp hδ with rfl | he
      · exact Or.inl rfl
      · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he
        exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)
    have he := hcaps δ hδshort
    rw [min_eq_right hreach] at he
    exact he.ge.trans (min_le_left _ _)

namespace Factorization
variable {c : Cell D} {s p : D.below (D.cell c) → ExtOrd}
variable {σ : ExtOrd → ExtOrd} {γ δ : ExtOrd}
variable (F : Factorization (sem := sem) c s p σ γ δ)

/-- Every low grid reading is literal once first-cut minimality supplies its
strict output inequality. No claim is made that every smaller invisible source
has such an inequality. -/
theorem low_read {x : ExtOrd} (hx : Short (D.grade c) x) (hl : σ x < γ) :
    F.outgoing x = σ x :=
  AmbientGradeCharts.eq_of_cap_below (F.caps x hx) hl

theorem high_read {x : ExtOrd} (hx : δ ≤ x) : γ ≤ F.outgoing x :=
  F.reaches.trans (F.witness.mono hx)

/-- Frozen finite-part receipts cover unused orbit points as well as original
observations. Only capped output is fixed on a saturated invisible plateau. -/
theorem orbit_caps {x : ExtOrd} (hx : Short (D.grade c) x) {k i : ℕ}
    (hk : k ≤ D.grade c) (hi : i ≤ k) :
    min (F.outgoing (extVisibilityReplace x k i)) γ =
      min (σ (extVisibilityReplace x k i)) γ :=
  F.caps _ (short_replace hx hk hi)

end Factorization

/-- The reaching cut is constructed in the fixed complete-field grid.
The input supplies the old source, actual chart, and lawful prescription;
no replacement source, alignment, retuning or coded completion is assumed. -/
theorem exists_factorization (c : Cell D) {s p : D.below (D.cell c) → ExtOrd} (m : ℕ)
    (hs : RespectsSemanticsBelow sem (D.cell c) s)
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    (hcoded : ∀ e, s e ∈ ExtOrd.codedAlphabet (2 * m) (D.grade c))
    (hshort : ∀ e, Short (D.grade c) (s e))
    {σ : ExtOrd → ExtOrd} {γ : ExtOrd}
    (hσ : Witness (gTop (D.grade c)) σ) (hγ : SelfVis (D.grade c) γ)
    (hpos : ⊥ < γ) (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    (hface : ∀ e, min (σ (s e)) γ = min (p e) γ) :
    ∃ δ ∈ PairedSlotComparison.sourceGrid (D.grade c) m, ⊥ < δ ∧ γ ≤ σ δ ∧
      (∀ z ∈ PairedSlotComparison.sourceGrid (D.grade c) m, z < δ → σ z < γ) ∧
      Nonempty (Factorization (sem := sem) c s p σ γ δ) := by
  classical
  let self : D.below (D.cell c) := ⟨c, GradedLe.refl _⟩
  let G := PairedSlotComparison.sourceGrid (D.grade c) m
  let R := G.filter (fun z => γ ≤ σ z)
  have howner : s self ∈ G := by
    have he := endpoint_grid (hcoded self) (hshort self)
    rwa [endpoint_of_selfVis (hs.orderly self).symm] at he
  have hownerread : γ ≤ σ (s self) := by
    have he := hface self
    rw [min_eq_right hpc.le] at he
    exact he.ge.trans (min_le_left _ _)
  have hn : R.Nonempty := ⟨s self, Finset.mem_filter.mpr ⟨howner, hownerread⟩⟩
  let δ := R.min' hn
  have hd := Finset.mem_filter.mp (Finset.min'_mem R hn)
  have hfirst : ∀ z ∈ G, z < δ → σ z < γ := by
    intro z hz hzd
    by_contra hl
    have hm : z ∈ R := Finset.mem_filter.mpr ⟨hz, not_lt.mp hl⟩
    exact (not_le_of_gt hzd) (Finset.min'_le R z hm)
  have hδpos : ⊥ < δ := by
    apply bot_lt_iff_ne_bot.mpr
    intro hbot
    have hreach := hd.2
    change γ ≤ σ δ at hreach
    rw [hbot, hσ.bot] at hreach
    exact not_le_of_gt hpos hreach
  exact ⟨δ, hd.1, hδpos, hd.2, hfirst,
    at_first_cut c m hs hp hcoded hshort hσ hγ hpos hpc hface hd.1 hd.2 hfirst⟩

/-- The source alphabet is counted on the complete field inventory, not the
owner's lower domain. Actual occurrence maps may repeat fields. Canonicality
supplies the code and shortness hypotheses; old source lawfulness is still the
original scheme's actual semantic condition. -/
theorem of_canonical_fields {X : Type*} [Fintype X] (c : Cell D)
    (occ : D.below (D.cell c) → X) {a : X → ExtOrd}
    (ha : a ∈ CanonicalPairedProfiles.inventory X (D.grade c))
    {p : D.below (D.cell c) → ExtOrd}
    (hs : RespectsSemanticsBelow sem (D.cell c) (a ∘ occ))
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {σ : ExtOrd → ExtOrd} {γ : ExtOrd}
    (hσ : Witness (gTop (D.grade c)) σ) (hγ : SelfVis (D.grade c) γ)
    (hpos : ⊥ < γ) (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    (hface : ∀ e, min (σ (a (occ e))) γ = min (p e) γ) :
    ∃ δ ∈ PairedSlotComparison.sourceGrid (D.grade c) (Fintype.card X),
      ⊥ < δ ∧ γ ≤ σ δ ∧
      (∀ z ∈ PairedSlotComparison.sourceGrid (D.grade c) (Fintype.card X),
        z < δ → σ z < γ) ∧
      Nonempty (Factorization (sem := sem) c (a ∘ occ) p σ γ δ) :=
  exists_factorization c (Fintype.card X) hs hp
    (fun e => CanonicalPairedProfiles.inventory_coded X (D.grade c) ha (occ e))
    (fun e => CanonicalPairedProfiles.inventory_short X (D.grade c) ha (occ e))
    hσ hγ hpos hpc hface

end
end VaughtConjecture.Knight.PrivateRowFactorization
