/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CapFirstScalar
public import VaughtConjecture.Knight.SourceBlockPadding

/-! # A finite decoder tail above a preserved capped prefix

Reserve finitely many source blocks, decode a new finite inventory beyond them,
and take the maximum with the old shifter clipped at the output cap. The result
is an actual faithful witness, literal on the clipped prefix and exact on all
tracked new targets above the output cap, including literal top. The source
alphabet bound is explicit. This constructs a scalar map and codes, not a lawful
replacement member, available controller, or uniform source enlargement.
-/

@[expose] public section

namespace VaughtConjecture.Knight.PaddedSourceDecoder

open Transform Value ExtOrd SharpWitnessComposition SourceBlockPadding

/-- Move nonbottom sources by `b` whole blocks. -/
noncomputable def reserve : ℕ → ExtOrd → ExtOrd
  | 0, x => x
  | b + 1, x => pad (reserve b x)

/-- Erase the reserved blocks; every erased block is killed in its entirety. -/
noncomputable def release : ℕ → ExtOrd → ExtOrd
  | 0, x => x
  | b + 1, x => release b (unpad x)

@[simp] theorem reserve_bot (b : ℕ) : reserve b ⊥ = ⊥ := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [reserve, ih, pad_bot]

@[simp] theorem release_bot (b : ℕ) : release b ⊥ = ⊥ := by
  induction b with
  | zero => rfl
  | succ b ih => simpa only [release, unpad_bot] using ih

/-- The inverse is literal at every padded source, including bottom and top. -/
theorem release_reserve (b : ℕ) (x : ExtOrd) : release b (reserve b x) = x := by
  induction b with
  | zero => rfl
  | succ b ih => simpa only [reserve, release, unpad_pad] using ih

/-- Repeated source padding preserves the finite part exactly. -/
theorem reserve_code (b u j : ℕ) : reserve b (ofOrd (Ordinal.omega0 * u + j)) =
    ofOrd (Ordinal.omega0 * (u + b : ℕ) + j) := by
  induction b with
  | zero => simp only [reserve, Nat.add_zero]
  | succ b ih => rw [reserve, ih, pad_code, Nat.add_assoc]

/-- Precomposition is justified by exact replacement commutation, not transitivity. -/
theorem witness_release {g : ℕ → ExtOrd} {τ : ExtOrd → ExtOrd}
    (hτ : Witness g τ) (b : ℕ) : Witness g (fun x => τ (release b x)) := by
  induction b with
  | zero => exact hτ
  | succ b ih => exact witness_precompose_unpad ih

private theorem unpad_lt_floor {b : ℕ} {x : ExtOrd}
    (hx : x < ofOrd (Ordinal.omega0 * (b + 1 : ℕ))) :
    unpad x < ofOrd (Ordinal.omega0 * b) := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [unpad_bot]; exact bot_lt_ofOrd _
  · exact False.elim (not_lt_of_ge le_top hx)
  · by_cases hα : Ordinal.omega0 ≤ α
    · have he : pad (unpad (ofOrd α)) = ofOrd α := by
        rw [unpad_ofOrd, ite_eq_left hα, pad_ofOrd, Ordinal.add_sub_cancel_of_le hα]
      have hp : pad (ofOrd (Ordinal.omega0 * b)) =
          ofOrd (Ordinal.omega0 * (b + 1 : ℕ)) := by
        simpa only [Nat.cast_zero, add_zero] using pad_code b 0
      by_contra hn
      have hle := pad_mono (not_lt.mp hn)
      rw [he, hp] at hle
      exact not_lt_of_ge hle hx
    · rw [unpad_ofOrd, ite_eq_right hα]
      exact bot_lt_ofOrd _

/-- The decoder sees bottom on the entire reserved prefix, not just listed sources. -/
theorem release_eq_bot_of_lt {b : ℕ} {x : ExtOrd}
    (hx : x < ofOrd (Ordinal.omega0 * b)) : release b x = ⊥ := by
  induction b generalizing x with
  | zero =>
    change x = ⊥
    rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
    · rfl
    · exact False.elim (not_lt_of_ge le_top hx)
    · have hα := ofOrd_lt_ofOrd.mp hx
      simp only [Nat.cast_zero, mul_zero, not_lt_zero] at hα
  | succ b ih => exact ih (unpad_lt_floor hx)

/-- An alphabet of block bound `t` moves to block bound `t + b`. -/
theorem reserve_mem_codedAlphabet {t K : ℕ} {x : ExtOrd}
    (hx : x ∈ ExtOrd.codedAlphabet t K) (b : ℕ) :
    reserve b x ∈ ExtOrd.codedAlphabet (t + b) K := by
  rcases mem_codedAlphabet_iff.mp hx with rfl | ⟨u, j, hu, hj, rfl⟩
  · exact mem_codedAlphabet_iff.mpr (Or.inl (reserve_bot b))
  · exact mem_codedAlphabet_iff.mpr
      (Or.inr ⟨u + b, j, Nat.add_le_add_right hu b, hj, reserve_code b u j⟩)

/-- The actual finite tail code. Original literal top is represented by a proper code. -/
noncomputable def encode (S : Finset Ordinal.{0}) (K b : ℕ) (y : ExtOrd) : ExtOrd :=
  reserve b (canonicalNormalizer S K y)

/-- Exact alphabet accounting: no availability of this much room in a tower is assumed. -/
theorem encode_mem (S : Finset Ordinal.{0}) (K b : ℕ) (y : ExtOrd) :
    encode S K b y ∈ ExtOrd.codedAlphabet (S.card + b) K :=
  reserve_mem_codedAlphabet (canonicalNormalizer_mem_codedAlphabet le_rfl y) b

/-- Exact readback before taking any maximum with the old witness. -/
theorem decode_encode (S : Finset Ordinal.{0}) {K b : ℕ} {y : ExtOrd}
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) :
    canonicalDecoder S K (release b (encode S K b y)) = y := by
  rw [encode, release_reserve, canonicalDecoder_canonicalNormalizer hy]

/-- Distinct tracked targets remain distinct even when their old capped values coincide. -/
theorem encode_eq_iff (S : Finset Ordinal.{0}) {K b : ℕ} {x y : ExtOrd}
    (hx : x = ⊥ ∨ x = ⊤ ∨ ∃ α ∈ S, x = ofOrd α)
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) :
    encode S K b x = encode S K b y ↔ x = y := by
  constructor
  · intro he
    have := congrArg (fun z => canonicalDecoder S K (release b z)) he
    simpa only [decode_encode S hx, decode_encode S hy] using this
  · exact congrArg (encode S K b)

/-- Every nonbottom tracked target really is placed beyond the reserved blocks. -/
theorem encode_ge_floor (S : Finset Ordinal.{0}) {K b : ℕ} {y : ExtOrd}
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) (hyb : y ≠ ⊥) :
    ofOrd (Ordinal.omega0 * b) ≤ encode S K b y := by
  by_contra hn
  have he := decode_encode (K := K) (b := b) S hy
  rw [release_eq_bot_of_lt (not_le.mp hn), canonicalDecoder_bot] at he
  exact hyb he.symm

/-- Even the code for literal top is a proper ordinal, not the top source. -/
theorem encode_top_proper (S : Finset Ordinal.{0}) (K b : ℕ) :
    ∃ u j : ℕ, u ≤ S.card + b ∧ j ≤ K + 1 ∧
      encode S K b ⊤ = ofOrd (Ordinal.omega0 * u + j) := by
  rcases mem_codedAlphabet_iff.mp (encode_mem S K b ⊤) with he | he
  · have hb := encode_ge_floor (K := K) (b := b) S (Or.inr (Or.inl rfl)) top_ne_bot
    rw [he] at hb
    exact False.elim (not_ofOrd_le_bot _ hb)
  · exact he

/-- Join a clipped old witness to the new decoder. The join uses existing normalized
witness closure; its decoder is precomposed only with the exact source inverse. -/
noncomputable def extend (S : Finset Ordinal.{0}) (K b : ℕ)
    (σ : ExtOrd → ExtOrd) (γ : ExtOrd) (x : ExtOrd) : ExtOrd :=
  max (min (σ x) γ) (canonicalDecoder S K (release b x))

/-- The extension is globally faithful, including the higher-threshold bottom clauses. -/
theorem extend_witness (S : Finset Ordinal.{0}) {K b : ℕ}
    {σ : ExtOrd → ExtOrd} {γ : ExtOrd}
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ) :
    Witness (gTop K) (extend S K b σ γ) :=
  (FreeDiagonal.clip_witness hσ hγ).max
    (witness_release (isStepShifter_canonicalDecoder (S := S) (K := K)).normalizedWitness b)

/-- Every value before the tail remains exactly the old value capped at `γ`. -/
theorem extend_before (S : Finset Ordinal.{0}) {K b : ℕ}
    {σ : ExtOrd → ExtOrd} {γ x : ExtOrd} (hx : x < ofOrd (Ordinal.omega0 * b)) :
    extend S K b σ γ x = min (σ x) γ := by
  rw [extend, release_eq_bot_of_lt hx, canonicalDecoder_bot, max_bot_right]

/-- New high targets are read literally, with no restriction on their finite part.
Bottom is allowed when the cap is bottom; top is handled by its proper code. -/
theorem extend_encode (S : Finset Ordinal.{0}) {K b : ℕ}
    {σ : ExtOrd → ExtOrd} {γ y : ExtOrd}
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) (hγy : γ ≤ y) :
    extend S K b σ γ (encode S K b y) = y := by
  rw [extend, encode, release_reserve, canonicalDecoder_canonicalNormalizer hy]
  exact max_eq_right ((min_le_right _ _).trans hγy)

/-- The proposed new source map preserves output caps on every pair of sources
agreeing below an interior source cut. Nothing requires the old map to attain `γ`. -/
theorem extend_cap_agreement (S : Finset Ordinal.{0}) {K b : ℕ}
    {σ : ExtOrd → ExtOrd} {γ a x y : ExtOrd}
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ)
    (ha : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hxy : min x a = min y a) :
    min (extend S K b σ γ x) γ = min (σ y) γ :=
  CapFirstScalar.map_cap_agreement_of_clipped_prefix hσ.mono
    (extend_witness S hσ hγ).mono
    (fun _ hz => extend_before S (hz.trans_lt ha)) hxy hactive

/-- Finite interpolation with a capped infinite prefix. The construction supplies
both the shifter and its new finite codes, with an explicit alphabet bound. The
inventory need track only the new targets, not the old witness's range. -/
theorem finite_tail (S : Finset Ordinal.{0}) {K b : ℕ}
    {σ : ExtOrd → ExtOrd} {γ a : ExtOrd}
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ)
    (ha : a < ofOrd (Ordinal.omega0 * b)) :
    ∃ τ code : ExtOrd → ExtOrd, Witness (gTop K) τ ∧
      (∀ x, x ≤ a → τ x = min (σ x) γ) ∧
      (∀ y, code y ∈ ExtOrd.codedAlphabet (S.card + b) K) ∧
      (∀ y, (y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) →
        γ ≤ y → τ (code y) = y) :=
  ⟨extend S K b σ γ, encode S K b, extend_witness S hσ hγ,
    fun _ hx => extend_before S (hx.trans_lt ha), encode_mem S K b,
    fun _ hy hγy => extend_encode S hy hγy⟩

/-- Direct consumer for a proposed replacement labelling. The decoder-tail map
preserves every ambient cap and gives actual respect. The protected set may mix
old-prefix reads with the newly encoded high targets. No locality, availability,
or equality of caps is hidden in the boundary condition. -/
theorem lift_of_source_agreement
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ}
    {r s q p : D.below BJ → ExtOrd} {K b : ℕ} {σ : ExtOrd → ExtOrd} {γ a : ExtOrd}
    (S : Finset Ordinal.{0}) (fixedCells : Set (D.below BJ))
    (hr : RespectsSemanticsBelow sem BJ r) (hq : RespectsSemanticsBelow sem BJ q)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ) (hγb : γ ≠ ⊥)
    (ha : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hsource : ∀ d, min (r d) a = min (s d) a)
    (hread : ∀ d, min (σ (s d)) γ = min (q d) γ)
    (hfixed : ∀ d ∈ fixedCells,
      (r d < ofOrd (Ordinal.omega0 * b) ∧ p d = min (σ (r d)) γ) ∨
      (r d = encode S K b (p d) ∧ γ ≤ p d ∧
        (p d = ⊥ ∨ p d = ⊤ ∨ ∃ α ∈ S, p d = ofOrd α))) :
    ∃ q' : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ q' ∧
      (∀ d ∈ fixedCells, q' d = p d) ∧
      (∀ d, min (q' d) γ = min (q d) γ) := by
  let τ := extend S K b σ γ
  have hτ : Witness (gTop K) τ := extend_witness S hσ hγ
  have hag d : min (τ (r d)) γ = min (q d) γ :=
    (extend_cap_agreement S hσ hγ ha hactive (hsource d)).trans (hread d)
  refine ⟨fun d => τ (r d),
    map_respects_of_positive_cap_agreement hr hq hK (boundedMap_of_witness hτ) hγb hag,
    ?_, hag⟩
  intro d hd
  rcases hfixed d hd with ⟨hbefore, hp⟩ | ⟨hrcode, hp, htracked⟩
  · exact (extend_before S hbefore).trans hp.symm
  · change extend S K b σ γ (r d) = p d
    rw [hrcode]
    exact extend_encode S htracked hp

end VaughtConjecture.Knight.PaddedSourceDecoder
