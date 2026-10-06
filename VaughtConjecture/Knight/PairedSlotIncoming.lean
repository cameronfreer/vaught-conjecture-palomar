/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PairedSlotDecoder
public import VaughtConjecture.Knight.SourceBlockLocalityTransport

/-! # Incoming lawfulness for paired point/orbit normalization

The finite paired encoding is extended to a monotone scalar map commuting with
replacement through the encoding grade. Affine rays handle low offsets; steps
strictly above a visible predecessor handle the remaining isolated points. A
nonbottom baseline makes the whole map bottom-reflecting, although an individual
point step need not have a block-closed bottom fibre.

The new map is constructed independently of the outgoing decoder. No inverse
transformation or transitivity of faithful transformations is used.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.PairedSlotIncoming
open Transform Value ExtOrd PairedSlotEncoding SharpWitnessComposition
noncomputable section

def after (a c x : ExtOrd) : ExtOrd := if a < x then c else ⊥

theorem after_bounded {j : ℕ} {a c : ExtOrd}
    (ha : SelfVis j a) (hc : SelfVis j c) : BoundedMap j (after a c) where
  bot := by simp [after]
  mono := by
    intro x y hxy
    by_cases hx : a < x
    · simp only [after, ite_eq_left hx, ite_eq_left (hx.trans_le hxy), le_refl]
    · simp only [after, ite_eq_right hx, bot_le]
  comm := by
    intro x k i hk hi
    have he : a < extVisibilityReplace x k i ↔ a < x := by
      simpa only [not_le] using not_congr (replace_le_visible_cut_iff ha hk hi)
    by_cases hx : a < x
    · simp only [after, ite_eq_left hx, ite_eq_left (he.mpr hx)]
      exact (evr_eq_self_of_selfVis (selfVis_mono hc hk) i).symm
    · simp only [after, ite_eq_right hx, ite_eq_right (fun h => hx (he.mp h)),
        extVisibilityReplace_bot]

theorem bounded_max {j : ℕ} {f g : ExtOrd → ExtOrd}
    (hf : BoundedMap j f) (hg : BoundedMap j g) :
    BoundedMap j (fun x => max (f x) (g x)) where
  bot := by rw [hf.bot, hg.bot, max_self]
  mono := fun _ _ h => max_le_max (hf.mono h) (hg.mono h)
  comm := by
    intro x k i hk hi
    rw [hf.comm x k i hk hi, hg.comm x k i hk hi, extVisibilityReplace_max _ _ hi]

theorem bounded_sup {I : Type*} {j : ℕ} (s : Finset I) (f : I → ExtOrd → ExtOrd)
    (hf : ∀ a ∈ s, BoundedMap j (f a)) : BoundedMap j (fun x => s.sup (fun a => f a x)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sup_empty] using
        (boundedMap_of_witness (MixedGradeInterpolation.zero_witness j))
  | @insert a s ha ih =>
      simpa only [Finset.sup_insert] using
        bounded_max (hf a (Finset.mem_insert_self a s))
          (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

def predecessor (a : Ordinal.{0}) : Ordinal.{0} := limitPart a + (finitePart a - 1 : ℕ)

theorem predecessor_lt {a : Ordinal.{0}} (ha : 0 < finitePart a) : predecessor a < a := by
  conv_rhs => rw [← limitPart_add_finitePart a]
  exact (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr (by omega))

theorem le_predecessor_of_lt {a b : Ordinal.{0}} (ha : 0 < finitePart a)
    (hb : b < a) : b ≤ predecessor a := by
  rcases lt_or_eq_of_le (limitPart_mono hb.le) with hl | hl
  · exact (lt_limitPart_of_limitPart_lt hl).le.trans le_self_add
  · have hf : finitePart b < finitePart a := by
      by_contra hn
      exact hb.not_ge (le_of_finitePart_le hl.symm (not_lt.mp hn))
    rw [← limitPart_add_finitePart b, predecessor, hl]
    exact add_le_add_right (Nat.cast_le.mpr (by omega)) _

def piece (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : ExtOrd → ExtOrd :=
  if finitePart a ≤ j then
    FiniteOrbitEmbedding.ray j (limitPart a) (Ordinal.omega0 * block j S a)
  else after (ofOrd (predecessor a)) (encode j S a)

theorem piece_bounded (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) :
    BoundedMap j (piece j S a) := by
  unfold piece
  split_ifs with ha
  · exact boundedMap_of_witness
      (FiniteOrbitEmbedding.ray_step j (limitPart_mul_nat _)).normalizedWitness
  · apply after_bounded
    · apply selfVis_ofOrd_iff.mpr
      rw [predecessor, finitePart_limitPart_add_nat]
      omega
    · exact encode_visible le_rfl (not_le.mp ha).le

theorem offset_eq_min {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : offset j S a = min (finitePart a) j := by
  by_cases h : finitePart a < j
  · simp only [offset, ite_eq_left (orbit_of_invisible ha h), min_eq_left h.le]
  · unfold offset
    split_ifs with ho
    · have he : finitePart a = j := le_antisymm ho.1 (not_lt.mp h)
      simp only [he, min_self]
    · exact (min_eq_right (not_lt.mp h)).symm

theorem piece_at {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hb : b ∈ S) (hk : key j S a = key j S b) :
    piece j S a (ofOrd b) = encode j S b := by
  have hblock := block_eq_of_key_eq ha hb hk
  by_cases ho : Orbit j S a
  · have hob := (orbit_iff_of_key_eq ha hb hk).mp ho
    have hl : limitPart a = limitPart b := by
      simpa only [key, ite_eq_left ho, ite_eq_left hob] using hk
    rw [piece, ite_eq_left ho.1, encode, offset, ite_eq_left hob, hblock, hl]
    simpa only [limitPart_add_finitePart] using
      (FiniteOrbitEmbedding.ray_at j (ν := Ordinal.omega0 * block j S b)
        (limitPart_idem b) hob.1)
  · have hob : ¬ Orbit j S b := fun h => ho ((orbit_iff_of_key_eq ha hb hk).mpr h)
    have hab : a = b := by simpa only [key, ite_eq_right ho, ite_eq_right hob] using hk
    subst b
    by_cases hf : finitePart a ≤ j
    · rw [piece, ite_eq_left hf, encode, offset_eq_min ha, min_eq_left hf]
      simpa only [limitPart_add_finitePart] using
        (FiniteOrbitEmbedding.ray_at j (ν := Ordinal.omega0 * block j S a)
          (limitPart_idem a) hf)
    · rw [piece, ite_eq_right hf, after, ite_eq_left
        (ofOrd_lt_ofOrd.mpr (predecessor_lt (by omega : 0 < finitePart a)))]

theorem piece_le (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) (x : ExtOrd) :
    piece j S a x ≤ ofOrd (Ordinal.omega0 * block j S a + j) := by
  unfold piece
  split_ifs
  · exact FiniteOrbitEmbedding.ray_le _ _ _ _
  · unfold after
    split_ifs
    · exact ofOrd_le_ofOrd.mpr
        (add_le_add_right (Nat.cast_le.mpr (offset_le j S a)) _)
    · exact bot_le

theorem piece_before {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (hb : b ∈ S) (hk : key j S b < key j S a) : piece j S a (ofOrd b) = ⊥ := by
  have hba : b < a := by
    by_contra hn
    exact hk.not_ge (key_mono j S (not_lt.mp hn))
  unfold piece
  split_ifs with ha
  · have hl : limitPart b < limitPart a := by
      apply lt_of_le_of_ne (limitPart_mono hba.le)
      intro he
      have hf : finitePart b < finitePart a := by
        by_contra hn
        exact hba.not_ge (le_of_finitePart_le he.symm (not_lt.mp hn))
      have hob := orbit_of_invisible hb (hf.trans_le ha)
      have hoa : Orbit j S a := ⟨ha, b, hb, hf.trans_le ha, he⟩
      simp only [key, ite_eq_left hoa, ite_eq_left hob, he, lt_self_iff_false] at hk
    rw [FiniteOrbitEmbedding.ray_ofOrd, ite_eq_left hl]
  · exact ite_eq_right (not_lt.mpr
      (ofOrd_le_ofOrd.mpr (le_predecessor_of_lt (by omega) hba)))

/-- A scalar encoder on every input, not only on the represented finite values. -/
def incoming (j : ℕ) (S : Finset Ordinal.{0}) (x : ExtOrd) : ExtOrd :=
  max (FiniteOrbitEmbedding.ray j 0 0 x) (S.sup (fun a => piece j S a x))

theorem incoming_bounded (j : ℕ) (S : Finset Ordinal.{0}) :
    BoundedMap j (incoming j S) :=
  bounded_max (boundedMap_of_witness (FiniteOrbitEmbedding.ray_step j
    (by simpa only [Nat.cast_zero] using limitPart_natCast 0)).normalizedWitness)
    (bounded_sup S _ (fun a _ => piece_bounded j S a))

theorem incoming_reflects_bottom (j : ℕ) (S : Finset Ordinal.{0}) (x : ExtOrd)
    (hx : incoming j S x = ⊥) : x = ⊥ :=
  FiniteOrbitEmbedding.baseline_reflects_bottom j x
    (le_bot_iff.mp ((le_max_left _ _).trans_eq hx))

theorem incoming_at {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}} (ha : a ∈ S) :
    incoming j S (ofOrd a) = encode j S a := by
  apply le_antisymm
  · apply max_le
    · apply (FiniteOrbitEmbedding.ray_le j 0 0 _).trans
      apply ofOrd_le_ofOrd.mpr
      rw [zero_add]
      have hblock : ((0 : ℕ) : Ordinal.{0}) < block j S a :=
        Nat.cast_lt.mpr (block_pos j S a)
      have hlow : (j : Ordinal.{0}) ≤ Ordinal.omega0 * block j S a := by
        simpa only [Nat.cast_zero, mul_zero, zero_add] using (code_add_lt_mul hblock j).le
      exact hlow.trans le_self_add
    · apply Finset.sup_le
      intro b hb
      rcases lt_trichotomy (key j S b) (key j S a) with hk | hk | hk
      · apply (piece_le j S b _).trans
        exact ofOrd_le_ofOrd.mpr ((code_add_lt_mul
          (Nat.cast_lt.mpr (block_lt_of_key_lt hb hk)) j).le.trans le_self_add)
      · exact (piece_at hb ha hk).le
      · rw [piece_before ha hk]
        exact bot_le
  · calc encode j S a = piece j S a (ofOrd a) := (piece_at ha ha rfl).symm
         _ ≤ S.sup (fun b => piece j S b (ofOrd a)) :=
           Finset.le_sup (f := fun b => piece j S b (ofOrd a)) ha
         _ ≤ incoming j S (ofOrd a) := le_max_right _ _

/-! ## Literal top and semantic transport -/

/-- Preserve literal top as well as all the finite represented values. -/
def encoder (j : ℕ) (S : Finset Ordinal.{0}) (x : ExtOrd) : ExtOrd :=
  if x = ⊤ then ⊤ else incoming j S x

theorem encoder_bounded (j : ℕ) (S : Finset Ordinal.{0}) :
    BoundedMap j (encoder j S) where
  bot := by simpa only [encoder, bot_ne_top, ite_false] using (incoming_bounded j S).bot
  mono := by
    intro x y hxy
    by_cases hy : y = ⊤
    · simp only [encoder, hy, ite_true, le_top]
    · have hx : x ≠ ⊤ := fun hx => hy (top_le_iff.mp (hx ▸ hxy))
      simpa only [encoder, ite_eq_right hx, ite_eq_right hy] using
        (incoming_bounded j S).mono hxy
  comm := by
    intro x k i hk hi
    rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
    · simp only [encoder, extVisibilityReplace_bot, bot_ne_top, ite_false,
        (incoming_bounded j S).bot]
    · simp only [encoder, extVisibilityReplace_top, ite_true]
    · simpa only [encoder, extVisibilityReplace_ofOrd, ofOrd_ne_top, ite_false] using
        (incoming_bounded j S).comm (ofOrd a) k i hk hi

theorem encoder_reflects_bottom (j : ℕ) (S : Finset Ordinal.{0}) (x : ExtOrd)
    (hx : encoder j S x = ⊥) : x = ⊥ := by
  unfold encoder at hx
  split_ifs at hx with ht
  · exact (top_ne_bot hx).elim
  · exact incoming_reflects_bottom j S x hx

/-- Bottom reflection supplies the clause-5 tail above the bounded commutation range. -/
theorem witness_of_bounded_reflecting {j : ℕ} {f : ExtOrd → ExtOrd}
    (hf : BoundedMap j f) (hbot : ∀ x, f x = ⊥ → x = ⊥) : Witness (gTop j) f where
  anti := (witness_id j).anti
  vis := (witness_id j).vis
  bot := hf.bot
  mono := hf.mono
  clause5 := by
    intro x k hact i hi
    by_cases hk : k ≤ j
    · exact hf.comm x k i hk hi
    · have hz : f x = ⊥ := by rwa [gTop_of_gt (not_le.mp hk), le_bot_iff] at hact
      rw [hbot x hz, extVisibilityReplace_bot, hf.bot, extVisibilityReplace_bot]

theorem encoder_witness (j : ℕ) (S : Finset Ordinal.{0}) :
    Witness (gTop j) (encoder j S) :=
  witness_of_bounded_reflecting (encoder_bounded j S) (encoder_reflects_bottom j S)

theorem encoder_at {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}} (ha : a ∈ S) :
    encoder j S (ofOrd a) = encode j S a := by
  simpa only [encoder, ofOrd_ne_top, ite_false] using incoming_at ha

section Profile
variable {X : Type*} [Fintype X]

theorem encoder_profile (j : ℕ) (p : X → ExtOrd) (d : X) :
    encoder j (values p) (p d) = PairedSlotEncoding.normalize j p d := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simpa only [PairedSlotEncoding.normalize, hb] using (encoder_bounded j (values p)).bot
  · simp only [encoder, ht, ite_true, PairedSlotEncoding.normalize]
  · rw [normalize_ofOrd ha, ha]
    exact encoder_at (mem_values.mpr ⟨d, ha⟩)

/-- The incoming transformation is constructed; it is not the inverse of a decoder. -/
theorem transforms_normalized {j : ℕ} (p : X → ExtOrd)
    (grade : X → ℕ) (hgrade : ∀ d, grade d ≤ j) :
    TransformsTo grade p (PairedSlotEncoding.normalize j p) := by
  apply (encoder_witness j (values p)).transformsTo
  intro d
  rw [encoder_profile, gTop_of_le (hgrade d), min_top_right]

end Profile

/-- Every incoming locality and availability survives paired-slot normalization.
The semantic rows may have long sources; no source-shortness hypothesis is used. -/
theorem normalize_respects
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} [Fintype (D.below BJ)]
    {p : D.below BJ → ExtOrd} {j : ℕ}
    (hp : RespectsSemanticsBelow sem BJ p)
    (hgrade : ∀ d : D.below BJ, D.grade d.1 ≤ j) :
    RespectsSemanticsBelow sem BJ (PairedSlotEncoding.normalize j p) := by
  have he : (fun d => encoder j (values p) (p d)) = PairedSlotEncoding.normalize j p :=
    funext (encoder_profile j p)
  rw [← he]
  exact FiniteOrbitEmbedding.map_respects hp hgrade (encoder_witness j (values p))
    (encoder_reflects_bottom j (values p))

end
end VaughtConjecture.Knight.PairedSlotIncoming
