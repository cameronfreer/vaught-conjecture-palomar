/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedSourceDecoder

/-! # Encoding a prescribed face without moving its low prefix

Keep labels at or below a visible cap literally, and put the remaining labels in
a canonically encoded tail above reserved source blocks. This is a faithful,
bottom-reflecting map, not a pointwise patch of unrelated lawful labellings.
Only the new high labels enter the inventory. Its size and the required source
alphabet are explicit; room in an already fixed tower is not automatic.

The decoder-tail construction recovers the original prescribed labels when its
old shifter fixes this prefix. That hypothesis is a genuine restriction, not a
normal form for arbitrary ambient witnesses. The encoder itself constructs no
extension; the final transport lemma consumes a lawful coded lift.
-/

@[expose] public section

namespace VaughtConjecture.Knight.RelativePrefixEncoding

open Transform Value ExtOrd SharpWitnessComposition SourceBlockPadding

private theorem tail_witness (S : Finset Ordinal.{0}) (K b : ℕ) :
    Witness (gTop K) (PaddedSourceDecoder.encode S K b) := by
  induction b with
  | zero => exact (isStepShifter_canonicalNormalizer (S := S) (K := K)).normalizedWitness
  | succ b ih =>
    exact ih.comp_of_bottom_reflecting (pad_step K).normalizedWitness le_rfl
      pad_reflects_bottom

private theorem tail_reflects_bottom {S : Finset Ordinal.{0}} {K b : ℕ}
    (h0 : (0 : Ordinal.{0}) ∈ S) (y : ExtOrd)
    (hy : PaddedSourceDecoder.encode S K b y = ⊥) : y = ⊥ := by
  have h := congrArg (PaddedSourceDecoder.release b) hy
  rw [PaddedSourceDecoder.encode, PaddedSourceDecoder.release_reserve,
    PaddedSourceDecoder.release_bot] at h
  exact canonicalNormalizer_reflects_bottom_of_zero_mem h0 y h

private theorem tail_ge_floor {S : Finset Ordinal.{0}} {K b : ℕ}
    (h0 : (0 : Ordinal.{0}) ∈ S) {y : ExtOrd} (hy : y ≠ ⊥) :
    ofOrd (Ordinal.omega0 * b) ≤ PaddedSourceDecoder.encode S K b y := by
  by_contra hn
  have h := PaddedSourceDecoder.release_eq_bot_of_lt (not_le.mp hn)
  rw [PaddedSourceDecoder.encode, PaddedSourceDecoder.release_reserve] at h
  exact hy (canonicalNormalizer_reflects_bottom_of_zero_mem h0 y h)

/-- The closed low prefix is literal; only values strictly above the cap are coded. -/
noncomputable def encode (S : Finset Ordinal.{0}) (K b : ℕ) (γ : ExtOrd) :
    ExtOrd → ExtOrd := prefixSplice γ id (PaddedSourceDecoder.encode S K b)

theorem encode_of_le {S : Finset Ordinal.{0}} {K b : ℕ} {γ y : ExtOrd}
    (hy : y ≤ γ) : encode S K b γ y = y := prefixSplice_of_le hy

theorem encode_of_gt {S : Finset Ordinal.{0}} {K b : ℕ} {γ y : ExtOrd}
    (hy : γ < y) : encode S K b γ y = PaddedSourceDecoder.encode S K b y :=
  prefixSplice_of_gt hy

@[simp] theorem encode_bot (S : Finset Ordinal.{0}) (K b : ℕ) (γ : ExtOrd) :
    encode S K b γ ⊥ = ⊥ := encode_of_le bot_le

/-- Inserting zero prevents the tail encoder from killing a nonbottom label. -/
theorem encode_reflects_bottom {S : Finset Ordinal.{0}} {K b : ℕ} {γ : ExtOrd}
    (h0 : (0 : Ordinal.{0}) ∈ S) (y : ExtOrd) (hy : encode S K b γ y = ⊥) : y = ⊥ := by
  by_cases h : y ≤ γ
  · rwa [encode_of_le h] at hy
  · rw [encode_of_gt (not_le.mp h)] at hy
    exact tail_reflects_bottom h0 y hy

/-- The jump to the tail is lawful because the cut is visible and the tail lies
strictly above it. Above the grade bound, bottom reflection discharges clause 5. -/
theorem encode_witness {S : Finset Ordinal.{0}} {K b : ℕ} {γ : ExtOrd}
    (h0 : (0 : Ordinal.{0}) ∈ S) (hγ : SelfVis K γ)
    (hroom : γ < ofOrd (Ordinal.omega0 * b)) :
    Witness (gTop K) (encode S K b γ) where
  anti := (witness_id K).anti
  vis := (witness_id K).vis
  bot := encode_bot S K b γ
  mono := by
    intro x y hxy
    by_cases hx : x ≤ γ <;> by_cases hy : y ≤ γ
    · rw [encode_of_le hx, encode_of_le hy]; exact hxy
    · rw [encode_of_le hx, encode_of_gt (not_le.mp hy)]
      exact hx.trans (hroom.le.trans (tail_ge_floor h0
        (ne_of_gt (bot_le.trans_lt (not_le.mp hy)))))
    · exact False.elim (hx (hxy.trans hy))
    · rw [encode_of_gt (not_le.mp hx), encode_of_gt (not_le.mp hy)]
      exact (tail_witness S K b).mono hxy
  clause5 := by
    intro x k hact i hi
    by_cases hk : k ≤ K
    · by_cases hx : x ≤ γ
      · rw [encode_of_le hx,
          encode_of_le ((replace_le_visible_cut_iff hγ hk hi).mpr hx)]
      · rw [encode_of_gt (not_le.mp hx),
          encode_of_gt (replace_gt_visible_cut hγ hk (not_le.mp hx))]
        exact (tail_witness S K b).clause5 x k
          (by rw [gTop_of_le hk]; exact le_top) i hi
    · have hz : encode S K b γ x = ⊥ := by
        rwa [gTop_of_gt (not_le.mp hk), le_bot_iff] at hact
      rw [encode_reflects_bottom h0 x hz, extVisibilityReplace_bot,
        encode_bot, extVisibilityReplace_bot]

/-- Every old cap equation survives, including bottom and a value equal to the cut. -/
theorem encode_cap {S : Finset Ordinal.{0}} {K b : ℕ} {γ y : ExtOrd}
    (h0 : (0 : Ordinal.{0}) ∈ S) (hroom : γ < ofOrd (Ordinal.omega0 * b)) :
    min (encode S K b γ y) γ = min y γ := by
  by_cases hy : y ≤ γ
  · rw [encode_of_le hy]
  · have hgt := not_le.mp hy
    rw [encode_of_gt hgt, min_eq_right hgt.le,
      min_eq_right (hroom.le.trans (tail_ge_floor h0 (ne_of_gt (bot_le.trans_lt hgt))))]

/-- The original rows remain fixed; the new prescribed labelling is actually lawful. -/
theorem encode_respects
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} {p : D.below BJ → ExtOrd}
    {S : Finset Ordinal.{0}} {K b : ℕ} {γ : ExtOrd}
    (hp : RespectsSemanticsBelow sem BJ p)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (h0 : (0 : Ordinal.{0}) ∈ S) (hγ : SelfVis K γ)
    (hroom : γ < ofOrd (Ordinal.omega0 * b)) :
    RespectsSemanticsBelow sem BJ (fun d => encode S K b γ (p d)) := by
  apply (map_respects_iff_rowBlockBottom hp hK
    (boundedMap_of_witness (encode_witness h0 hγ hroom))).mpr
  apply rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects hp)
  intro d
  exact ⟨encode_reflects_bottom h0 _, fun h => by rw [h, encode_bot]⟩

/-- Only an identity low prefix is assumed here; a general ambient shifter need
not admit this form. Above the cap, decoding is exact even at literal top. -/
theorem decode_encode {S : Finset Ordinal.{0}} {K b : ℕ} {σ : ExtOrd → ExtOrd}
    {γ y : ExtOrd} (hroom : γ < ofOrd (Ordinal.omega0 * b))
    (hprefix : ∀ x, x ≤ γ → σ x = x)
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) :
    PaddedSourceDecoder.extend S K b σ γ (encode S K b γ y) = y := by
  by_cases h : y ≤ γ
  · rw [encode_of_le h, PaddedSourceDecoder.extend_before S (h.trans_lt hroom),
      hprefix y h, min_eq_left h]
  · rw [encode_of_gt (not_le.mp h)]
    exact PaddedSourceDecoder.extend_encode S hy (not_le.mp h).le

section FiniteInventory

variable {X : Type*} [Fintype X]

open Classical in
/-- High occurrences are retained individually when counting the budget. -/
noncomputable def highCells (p : X → ExtOrd) (γ : ExtOrd) : Finset X :=
  Finset.univ.filter (fun d => γ < p d)

open Classical in
/-- Only high proper values need tracking; zero guarantees bottom reflection. -/
noncomputable def inventory (p : X → ExtOrd) (γ : ExtOrd) : Finset Ordinal.{0} :=
  insert 0 ((highCells p γ).image (fun d => ordOf (p d)))

theorem zero_mem_inventory (p : X → ExtOrd) (γ : ExtOrd) :
    (0 : Ordinal.{0}) ∈ inventory p γ := by
  classical
  exact Finset.mem_insert_self _ _

/-- This bound counts occurrences, not distinct source indices. Duplicate values
can save room, but are never needed for the bound. -/
theorem inventory_card_le (p : X → ExtOrd) (γ : ExtOrd) :
    (inventory p γ).card ≤ (highCells p γ).card + 1 := by
  classical
  exact (Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right (Finset.card_image_le) 1)

theorem tracked_high (p : X → ExtOrd) (γ : ExtOrd) (d : X) (hd : γ < p d) :
    p d = ⊥ ∨ p d = ⊤ ∨ ∃ α ∈ inventory p γ, p d = ofOrd α := by
  classical
  rcases ExtOrd.cases (p d) with h | h | ⟨α, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨α, Finset.mem_insert_of_mem ?_, h⟩)
    exact Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩,
      by rw [h, ordOf_ofOrd]⟩

/-- The complete face decodes, although its low ordinal values were not put in
the new inventory. -/
theorem decode_face (p : X → ExtOrd) {K b : ℕ} {γ : ExtOrd}
    {σ : ExtOrd → ExtOrd} (hroom : γ < ofOrd (Ordinal.omega0 * b))
    (hprefix : ∀ x, x ≤ γ → σ x = x) (d : X) :
    PaddedSourceDecoder.extend (inventory p γ) K b σ γ
      (encode (inventory p γ) K b γ (p d)) = p d := by
  by_cases hd : p d ≤ γ
  · rw [encode_of_le hd, PaddedSourceDecoder.extend_before _ (hd.trans_lt hroom),
      hprefix _ hd, min_eq_left hd]
  · exact decode_encode hroom hprefix (tracked_high p γ d (not_le.mp hd))

/-- A fixed alphabet suffices only under the displayed room bound and coded-low
input condition. This does not resize a previously fixed tower. -/
theorem encode_face_mem (p : X → ExtOrd) {K b t : ℕ} {γ : ExtOrd}
    (hlow : ∀ d, p d ≤ γ → p d ∈ ExtOrd.codedAlphabet t K)
    (hbudget : (highCells p γ).card + 1 + b ≤ t) (d : X) :
    encode (inventory p γ) K b γ (p d) ∈ ExtOrd.codedAlphabet t K := by
  by_cases hd : p d ≤ γ
  · rw [encode_of_le hd]; exact hlow d hd
  · rw [encode_of_gt (not_le.mp hd)]
    rcases mem_codedAlphabet_iff.mp (PaddedSourceDecoder.encode_mem (inventory p γ) K b
      (p d)) with hb | ⟨u, j, hu, hj, he⟩
    · exact mem_codedAlphabet_iff.mpr (Or.inl hb)
    · exact mem_codedAlphabet_iff.mpr (Or.inr ⟨u, j,
        hu.trans ((Nat.add_le_add_right (inventory_card_le p γ) b).trans hbudget), hj, he⟩)

/-- Decode a lawful coded lift produced independently. Every ambient cap is
preserved by construction, so the positive-cap transport proves lawfulness of
the decoded lift. A coded lift is still an input to this generic lemma. -/
theorem decode_lift
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} {r q : D.below BJ → ExtOrd}
    (p : X → ExtOrd) (incl : X → D.below BJ) {K b : ℕ} {γ : ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) (hq : RespectsSemanticsBelow sem BJ q)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hγ : SelfVis K γ) (hγb : γ ≠ ⊥) (hroom : γ < ofOrd (Ordinal.omega0 * b))
    (hcap : ∀ d, min (r d) γ = min (q d) γ)
    (hlit : ∀ d, r (incl d) = encode (inventory p γ) K b γ (p d)) :
    ∃ q' : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ q' ∧
      (∀ d, q' (incl d) = p d) ∧ ∀ d, min (q' d) γ = min (q d) γ := by
  let τ := PaddedSourceDecoder.extend (inventory p γ) K b id γ
  have hτ : Witness (gTop K) τ :=
    PaddedSourceDecoder.extend_witness _ (witness_id K) hγ
  have hag d : min (τ (r d)) γ = min (q d) γ :=
    (PaddedSourceDecoder.extend_cap_agreement _ (witness_id K) hγ hroom le_rfl
      (show min (r d) γ = min (q d) γ from hcap d))
  refine ⟨fun d => τ (r d),
    map_respects_of_positive_cap_agreement hr hq hK (boundedMap_of_witness hτ) hγb hag,
    ?_, hag⟩
  intro d
  change PaddedSourceDecoder.extend (inventory p γ) K b id γ (r (incl d)) = p d
  rw [hlit d]
  exact decode_face p hroom (fun _ _ => rfl) d

end FiniteInventory

end VaughtConjecture.Knight.RelativePrefixEncoding
