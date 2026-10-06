/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PairedSlotEncoding
public import VaughtConjecture.Knight.FiniteOrbitEmbedding
public import VaughtConjecture.Knight.RightFilledGap

/-! # Constructed right-filled decoder for the paired slots

One affine ray serves each hosted orbit and one constant step serves each point.
Their finite maximum reads the occupied slots literally. Before each next group,
a step beginning just past every preceding occupied block raises unused strips
to the greatest grid value below the next group's floor. A final step supplies
the chosen ceiling after the last group. These are genuine faithful witnesses:
clause 5 holds at every threshold, including the bottom-suppressor tail.

The resulting decoder is exact, bounded by any visible ceiling of the inventory,
and orbit-supported over the original boundary when that ceiling belongs to the
grid. It constructs the outgoing transformation of a normalized finite profile.
Bottom reflection is neither needed nor claimed. The initial-gap control shows
where right-filling improves on the occupied rays alone.

Still open: a bottom-reflecting incoming normalization witness, the decoder
comparison at the largest common source-grid cut, normalization idempotence,
and the coupled lawful-section producer. Thus this is not source-prefix
extension, semantic amalgamation, or a bountifulness theorem.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.PairedSlotDecoder
open Transform Value ExtOrd PairedSlotEncoding
noncomputable section

def piece (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : ExtOrd → ExtOrd := by
  classical
  exact if Orbit j S a then
    FiniteOrbitEmbedding.ray j (Ordinal.omega0 * block j S a) (limitPart a)
  else stepShifter (block j S a) ⊥ (ofOrd a)

theorem piece_witness {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : Witness (gTop j) (piece j S a) := by
  unfold piece
  split_ifs with ho
  · exact (FiniteOrbitEmbedding.ray_step j (limitPart_idem a)).normalizedWitness
  · exact Witness.stepLimit j _ bot_le (selfVis_bot j)
      (selfVis_ofOrd_iff.mpr (by
        by_contra hn
        exact ho (orbit_of_invisible ha (not_le.mp hn))))

theorem piece_le (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) (x : ExtOrd) :
    piece j S a x ≤ ofOrd (ceiling j S a) := by
  unfold piece ceiling
  split_ifs with ho
  · exact FiniteOrbitEmbedding.ray_le _ _ _ _
  · rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
    · exact bot_le
    · exact le_rfl
    · change (if _ then _ else _) ≤ _
      split_ifs <;> simp

theorem piece_at {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hb : b ∈ S) (hk : key j S a = key j S b) :
    piece j S a (encode j S b) = ofOrd b := by
  have hblock := block_eq_of_key_eq ha hb hk
  have ho := orbit_iff_of_key_eq ha hb hk
  by_cases hoa : Orbit j S a
  · have hob := ho.mp hoa
    have hl : limitPart a = limitPart b := by
      simpa only [key, ite_eq_left hoa, ite_eq_left hob] using hk
    simp only [piece, ite_eq_left hoa, encode, offset, ite_eq_left hob, hblock]
    rw [FiniteOrbitEmbedding.ray_at j (limitPart_mul_nat _) hob.1, hl,
      limitPart_add_finitePart]
  · have hob : ¬ Orbit j S b := fun h => hoa (ho.mpr h)
    have hab : a = b := by
      simpa only [key, ite_eq_right hoa, ite_eq_right hob] using hk
    simp only [piece, ite_eq_right hoa, hab]
    apply stepShifter_of_ge
    exact ofOrd_le_ofOrd.mpr le_self_add

theorem piece_before {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hk : key j S a < key j S b) :
    piece j S b (encode j S a) = ⊥ := by
  have hb := block_lt_of_key_lt ha hk
  have hbo : (block j S a : Ordinal.{0}) < block j S b := Nat.cast_lt.mpr hb
  unfold piece
  split_ifs
  · rw [encode, FiniteOrbitEmbedding.ray_ofOrd, limitPart_mul_add,
      ite_eq_left (by simpa only [Nat.cast_zero, add_zero] using code_add_lt_mul hbo 0)]
  · exact stepShifter_of_lt (ofOrd_ne_bot _)
      (ofOrd_lt_ofOrd.mpr (code_add_lt_mul hbo _))

def occupied (j : ℕ) (S : Finset Ordinal.{0}) (x : ExtOrd) : ExtOrd :=
  S.sup (fun a => piece j S a x)

theorem occupied_witness (j : ℕ) (S : Finset Ordinal.{0}) :
    Witness (gTop j) (occupied j S) :=
  Witness.finset_sup (MixedGradeInterpolation.zero_witness j) S (fun _ ha => piece_witness ha)

theorem occupied_encode {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : occupied j S (encode j S a) = ofOrd a := by
  apply le_antisymm
  · apply Finset.sup_le
    intro b hb
    rcases lt_trichotomy (key j S b) (key j S a) with hk | hk | hk
    · exact (piece_le j S b _).trans (ofOrd_le_ofOrd.mpr (ceiling_le_of_key_lt hk))
    · exact (piece_at hb ha hk).le
    · rw [piece_before ha hk]
      exact bot_le
  · rw [← piece_at ha ha rfl]
    exact Finset.le_sup (f := fun b => piece j S b (encode j S a)) ha
/-- The first source block not occupied by an earlier group. -/
def gapStart (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : ℕ :=
  S.sup (fun b => if key j S b < key j S a then block j S b + 1 else 0)

theorem gapStart_le (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) :
    gapStart j S a ≤ block j S a := by
  apply Finset.sup_le
  intro b hb
  split_ifs with hk
  · exact block_lt_of_key_lt hb hk
  · exact Nat.zero_le _

theorem block_lt_gapStart {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hk : key j S a < key j S b) :
    block j S a < gapStart j S b := by
  change block j S a + 1 ≤ gapStart j S b
  unfold gapStart
  apply Finset.le_sup_of_le ha
  simp only [ite_eq_left hk, le_refl]

def gap (j : ℕ) (S : Finset Ordinal.{0}) (G : Finset ExtOrd)
    (a : Ordinal.{0}) : ExtOrd → ExtOrd :=
  stepShifter (gapStart j S a) ⊥ (RightFilledGap.floor G (ofOrd (key j S a)))

theorem step_zero_le (n : ℕ) (c x : ExtOrd) : stepShifter n ⊥ c x ≤ c := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
  · exact bot_le
  · exact le_rfl
  · change (if _ then _ else _) ≤ _
    split_ifs <;> simp

theorem gap_witness {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (a : Ordinal.{0}) :
    Witness (gTop j) (gap j S G a) := by
  apply Witness.stepLimit j _ bot_le (selfVis_bot j)
  rcases RightFilledGap.floor_eq_bot_or_mem G (ofOrd (key j S a)) with hb | hm
  · rw [hb]; exact selfVis_bot j
  · exact hG _ hm

theorem gap_encode_le {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd}
    {a b : Ordinal.{0}} (ha : a ∈ S) :
    gap j S G b (encode j S a) ≤ ofOrd a := by
  by_cases hk : key j S b ≤ key j S a
  · exact (step_zero_le _ _ _).trans ((RightFilledGap.floor_le _ _).trans
      (ofOrd_le_ofOrd.mpr (hk.trans (key_le j S a))))
  · have hblock := block_lt_gapStart ha (not_le.mp hk)
    have he : gap j S G b (encode j S a) = ⊥ :=
      stepShifter_of_lt (ofOrd_ne_bot _)
        (ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr hblock) _))
    rw [he]
    exact bot_le

def tailStart (j : ℕ) (S : Finset Ordinal.{0}) : ℕ := S.sup (block j S) + 1

/-- Occupied pieces, right-filled gaps, and the terminal ceiling. -/
def decode (j : ℕ) (S : Finset Ordinal.{0}) (G : Finset ExtOrd)
    (C x : ExtOrd) : ExtOrd :=
  max (occupied j S x)
    (max (S.sup (fun a => gap j S G a x)) (stepShifter (tailStart j S) ⊥ C x))

theorem decode_witness {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd} {C : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) :
    Witness (gTop j) (decode j S G C) :=
  (occupied_witness j S).max
    ((Witness.finset_sup (MixedGradeInterpolation.zero_witness j) S
      (fun a _ => gap_witness hG a)).max
      (Witness.stepLimit j _ bot_le (selfVis_bot j) hC))

theorem decode_encode {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd} {C : ExtOrd}
    {a : Ordinal.{0}} (ha : a ∈ S) : decode j S G C (encode j S a) = ofOrd a := by
  have htail : stepShifter (tailStart j S) ⊥ C (encode j S a) = ⊥ := by
    apply stepShifter_of_lt (ofOrd_ne_bot _)
    apply ofOrd_lt_ofOrd.mpr
    apply code_add_lt_mul
    exact Nat.cast_lt.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := block j S) ha))
  rw [decode, occupied_encode ha, htail, max_eq_left bot_le]
  apply max_eq_left
  apply Finset.sup_le
  intro b _
  exact gap_encode_le ha

theorem decode_gap_reaches {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd}
    {C x h : ExtOrd} {a : Ordinal.{0}}
    (ha : a ∈ S) (hh : h ∈ G) (hfloor : h ≤ ofOrd (key j S a))
    (hx : ofOrd (Ordinal.omega0 * gapStart j S a) ≤ x) :
    h ≤ decode j S G C x := by
  have hg : gap j S G a x = RightFilledGap.floor G (ofOrd (key j S a)) :=
    stepShifter_of_ge hx
  calc h ≤ gap j S G a x := hg ▸ RightFilledGap.le_floor hh hfloor
    _ ≤ S.sup (fun b => gap j S G b x) := Finset.le_sup (f := fun b => gap j S G b x) ha
    _ ≤ decode j S G C x := (le_max_left _ _).trans (le_max_right _ _)

theorem decode_tail {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd}
    {C x : ExtOrd} (hx : ofOrd (Ordinal.omega0 * tailStart j S) ≤ x) :
    C ≤ decode j S G C x := by
  have he := stepShifter_of_ge (c₀ := (⊥ : ExtOrd)) (c₁ := C) hx
  rw [decode, he]
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem ceiling_eq_replace {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : ofOrd (ceiling j S a) = extVisibilityReplace (ofOrd a) j j := by
  by_cases hf : finitePart a < j
  · simp only [ceiling, ite_eq_left (orbit_of_invisible ha hf),
      extVisibilityReplace_of_finitePart_lt hf]
  · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hf)]
    unfold ceiling
    split_ifs with ho
    · have he : finitePart a = j := le_antisymm ho.1 (not_lt.mp hf)
      rw [← he, limitPart_add_finitePart]
    · rfl

theorem decode_le {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd} {C : ExtOrd}
    (hC : SelfVis j C) (hS : ∀ a ∈ S, ofOrd a ≤ C) (x : ExtOrd) :
    decode j S G C x ≤ C := by
  apply max_le
  · apply Finset.sup_le
    intro a ha
    apply (piece_le j S a x).trans
    rw [ceiling_eq_replace ha]
    exact extVisibilityReplace_le_of_le_selfVis le_rfl hC (hS a ha)
  · apply max_le
    · apply Finset.sup_le
      intro a ha
      exact (step_zero_le _ _ _).trans ((RightFilledGap.floor_le _ _).trans
        ((ofOrd_le_ofOrd.mpr (key_le j S a)).trans (hS a ha)))
    · exact step_zero_le _ _ _

theorem decode_top {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd} {C : ExtOrd}
    (hC : SelfVis j C) (hS : ∀ a ∈ S, ofOrd a ≤ C) : decode j S G C ⊤ = C :=
  le_antisymm (decode_le hC hS _) (decode_tail le_top)

theorem initial_gap_reaches {j : ℕ} {a : Ordinal.{0}} {G : Finset ExtOrd}
    {C h : ExtOrd} (ha : finitePart a < j) (hh : h ∈ G)
    (hfloor : h ≤ ofOrd (limitPart a)) :
    h ≤ decode j {a} G C (ofOrd j) := by
  apply decode_gap_reaches (Finset.mem_singleton_self a) hh
  · simpa only [key, ite_eq_left (orbit_of_invisible (Finset.mem_singleton_self a) ha)]
      using hfloor
  · have hg : gapStart j {a} a = 0 := by simp [gapStart]
    rw [hg]
    apply ofOrd_le_ofOrd.mpr
    simp

theorem occupied_initial_gap {j : ℕ} {a : Ordinal.{0}} (ha : finitePart a < j) :
    occupied j {a} (ofOrd j) = ⊥ := by
  have ho := orbit_of_invisible (Finset.mem_singleton_self a) ha
  have hr : PairedSlotEncoding.rank j {a} a = 0 := by
    simp [PairedSlotEncoding.rank, PairedSlotEncoding.keys]
  have hb : block j {a} a = 2 := by simp [block, hr, ho]
  simp only [occupied, Finset.sup_singleton, piece, ite_eq_left ho, hb,
    FiniteOrbitEmbedding.ray_ofOrd, limitPart_natCast]
  have hpos : (0 : Ordinal.{0}) < ((2 : ℕ) : Ordinal.{0}) := by norm_num
  rw [ite_eq_left (mul_pos Ordinal.omega0_pos hpos)]

section Profile
variable {X : Type*} [Fintype X]

theorem decode_normalize {j : ℕ} {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C)
    (hp : ∀ d, p d ≠ ⊤) (d : X) :
    decode j (values p) G C (PairedSlotEncoding.normalize j p d) = p d := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simp only [PairedSlotEncoding.normalize, hb]
    exact (decode_witness hG hC).bot
  · exact (hp d ht).elim
  · rw [normalize_ofOrd ha, ha]
    exact decode_encode (mem_values.mpr ⟨d, ha⟩)

/-- An actual outgoing witness, with no pre-existing transformation assumed. -/
theorem normalized_transforms {j : ℕ} {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (grade : X → ℕ) (hgrade : ∀ d, grade d ≤ j)
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) (hp : ∀ d, p d ≠ ⊤) :
    TransformsTo grade (PairedSlotEncoding.normalize j p) p := by
  apply (decode_witness (S := values p) hG hC).transformsTo
  intro d
  rw [decode_normalize hG hC hp d, gTop_of_le (hgrade d), min_top_right]

omit [Fintype X] in
private theorem supported_max {K : ℕ} {G : Set ExtOrd} {p : X → ExtOrd} {a b : ExtOrd}
    (ha : OrbitPrefixSupport.Supported K G p a)
    (hb : OrbitPrefixSupport.Supported K G p b) :
    OrbitPrefixSupport.Supported K G p (max a b) := by
  rcases le_total a b with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

omit [Fintype X] in
private theorem supported_sup {I : Type*} (s : Finset I) {K : ℕ} {G : Set ExtOrd}
    {p : X → ExtOrd} {f : I → ExtOrd}
    (hf : ∀ a ∈ s, OrbitPrefixSupport.Supported K G p (f a)) :
    OrbitPrefixSupport.Supported K G p (s.sup f) := by
  classical
  apply Finset.sup_induction (p := OrbitPrefixSupport.Supported K G p)
  · exact Or.inl rfl
  · intro a ha b hb
    exact supported_max ha hb
  · exact hf

omit [Fintype X] in
private theorem supported_boundary {K : ℕ} {G : Set ExtOrd} {p : X → ExtOrd} (d : X) :
    OrbitPrefixSupport.Supported K G p (p d) := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inr ⟨d, K, le_rfl, by rw [ht, extVisibilityReplace_top]⟩)
  · by_cases hk : finitePart a < K
    · exact Or.inr (Or.inr ⟨d, finitePart a, hk.le, by
        rw [ha, extVisibilityReplace_of_finitePart_lt hk, limitPart_add_finitePart]⟩)
    · exact Or.inr (Or.inr ⟨d, K, le_rfl, by
        rw [ha, extVisibilityReplace_of_le_finitePart (not_lt.mp hk)]⟩)

theorem piece_supported {j K : ℕ} {p : X → ExtOrd} {G : Set ExtOrd}
    (hj : j ≤ K) {a : Ordinal.{0}} (ha : a ∈ values p) (x : ExtOrd) :
    OrbitPrefixSupport.Supported K G p (piece j (values p) a x) := by
  unfold piece
  split_ifs with ho
  · obtain ⟨b, hb, hbj, hba⟩ := ho.2
    obtain ⟨d, hd⟩ := mem_values.mp hb
    have hs (i : ℕ) (hi : i ≤ j) :
        OrbitPrefixSupport.Supported K G p (ofOrd (limitPart a + i)) :=
      Or.inr (Or.inr ⟨d, i, hi.trans hj, by
        rw [hd, extVisibilityReplace_of_finitePart_lt (hbj.trans_le hj), hba]⟩)
    rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
    · exact Or.inl rfl
    · exact hs j le_rfl
    · rw [FiniteOrbitEmbedding.ray_ofOrd]
      split_ifs
      · exact Or.inl rfl
      · exact hs _ (min_le_right _ _)
      · exact hs j le_rfl
  · obtain ⟨d, hd⟩ := mem_values.mp ha
    have hs : OrbitPrefixSupport.Supported K G p (ofOrd a) := hd ▸ supported_boundary d
    rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
    · exact Or.inl rfl
    · exact hs
    · change OrbitPrefixSupport.Supported K G p (if _ then _ else _)
      split_ifs <;> first | exact Or.inl rfl | exact hs

/-- Every output, not only the represented boundary values, has orbit support. -/
theorem decode_supported {j K : ℕ} {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hj : j ≤ K) (hC : C ∈ G) (x : ExtOrd) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (decode j (values p) G C x) := by
  apply supported_max
  · exact supported_sup _ (fun a ha => piece_supported hj ha x)
  · apply supported_max
    · apply supported_sup
      intro a _
      have hs : OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
          (RightFilledGap.floor G (ofOrd (key j (values p) a))) := by
        rcases RightFilledGap.floor_eq_bot_or_mem G _ with hb | hm
        · exact Or.inl hb
        · exact Or.inr (Or.inl hm)
      rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
      · exact Or.inl rfl
      · exact hs
      · change OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (if _ then _ else _)
        split_ifs <;> first | exact Or.inl rfl | exact hs
    · rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hC)
      · change OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (if _ then _ else _)
        split_ifs <;> first | exact Or.inl rfl | exact Or.inr (Or.inl hC)
theorem decode_other_prefix {j : ℕ} {p q : X → ExtOrd} {G : Finset ExtOrd}
    {C : ExtOrd} {h : Ordinal.{0}}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) (hq : ∀ d, q d ≠ ⊤)
    (hh : j ≤ finitePart h)
    (hpq : ∀ d, min (p d) (ofOrd h) = min (q d) (ofOrd h))
    (d : X) (hd : p d < ofOrd h) :
    decode j (values q) G C (PairedSlotEncoding.normalize j p d) = p d := by
  rw [normalize_prefix hh hpq d hd, decode_normalize hG hC hq d]
  exact (eq_of_cap_eq_lt (hpq d) hd).symm

end Profile

end
end VaughtConjecture.Knight.PairedSlotDecoder
