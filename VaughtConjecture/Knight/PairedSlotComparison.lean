/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PairedSlotProfiles

/-! # Constructed common cuts and whole paired-decoder comparison

For bottom/proper boundary profiles agreeing under a visible target grid cut,
the actual paired decoders agree under that cut at every source value. The
proof compares whole low pieces and their gaps, then reaches the cut through
the first upper gap or a shared orbit endpoint. A constructed visible common
source cut also supplies the required bounds at the largest agreement-grid cut.

The source grid reserves one block past every occupied slot, so its final
endpoint decodes to the chosen ceiling even for an empty boundary. The target
grid is shared and contains the external cut; both ceilings reach that cut.
External bottom and top caps are included. Literal-top boundary profiles are
not included. No coupled section operator or amalgamation is asserted.

The old encoder and decoder are unchanged. Matching a group means matching its
whole affine ray or point step, not just its represented boundary readings.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.PairedSlotComparison
open Transform Value ExtOrd PairedSlotEncoding PairedSlotDecoder
noncomputable section

theorem block_congr_below {j : ℕ} {S T : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) (ha : a < h) :
    block j S a = block j T a := by
  have hr := rank_congr_below hh heq ha
  have ho := orbit_congr_below hh heq ((limitPart_le a).trans_lt ha)
  classical
  simp only [block, hr, ho]

theorem piece_eq_of_key_eq {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hb : b ∈ S) (hk : key j S a = key j S b) :
    piece j S a = piece j S b := by
  have hblock := block_eq_of_key_eq ha hb hk
  have ho := orbit_iff_of_key_eq ha hb hk
  classical
  by_cases hoa : Orbit j S a
  · have hob := ho.mp hoa
    have hl : limitPart a = limitPart b := by
      simpa only [key, ite_eq_left hoa, ite_eq_left hob] using hk
    simp only [piece, ite_eq_left hoa, ite_eq_left hob, hblock, hl]
  · have hob : ¬ Orbit j S b := fun h => hoa (ho.mpr h)
    have hab : a = b := by
      simpa only [key, ite_eq_right hoa, ite_eq_right hob] using hk
    rw [hab]

theorem piece_congr_below {j : ℕ} {S T : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) (ha : a < h) :
    piece j S a = piece j T a := by
  have hb := block_congr_below hh heq ha
  have ho := orbit_congr_below hh heq ((limitPart_le a).trans_lt ha)
  classical
  simp only [piece, hb, ho]

/-- Every low key, even one represented only by an optional orbit endpoint,
has the same full decoding piece in the other inventory. -/
theorem low_group_transfer {j : ℕ} {S T : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T))
    (ha : a ∈ S) (hk : key j S a < h) :
    ∃ b ∈ T, b < h ∧ key j S a = key j T b ∧
      block j S a = block j T b ∧ piece j S a = piece j T b := by
  obtain ⟨b, hb, hbh, hba⟩ := exists_low_key hh ha hk
  exact ⟨b, (heq b hbh).mp hb, hbh,
    hba.symm.trans (key_congr_below hh heq hbh),
    (block_eq_of_key_eq ha hb hba.symm).trans (block_congr_below hh heq hbh),
    (piece_eq_of_key_eq ha hb hba.symm).trans (piece_congr_below hh heq hbh)⟩

/-- The source gap before corresponding low groups is literally identical. -/
theorem gapStart_congr {j : ℕ} {S T : Finset Ordinal.{0}} {a b h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (heq : ∀ c, c < h → (c ∈ S ↔ c ∈ T))
    (hk : key j S a = key j T b) (ha : key j S a < h) :
    gapStart j S a = gapStart j T b := by
  classical
  have one (S T : Finset Ordinal.{0}) (a b : Ordinal.{0})
      (heq : ∀ c, c < h → (c ∈ S ↔ c ∈ T))
      (hk : key j S a = key j T b) (ha : key j S a < h) :
      gapStart j S a ≤ gapStart j T b := by
    apply Finset.sup_le
    intro c hc
    split_ifs with hca
    · obtain ⟨d, hd, _, hkd, hbd, _⟩ := low_group_transfer hh heq hc (hca.trans ha)
      have hdb : key j T d < key j T b := by rwa [← hkd, ← hk]
      rw [hbd]
      exact block_lt_gapStart hd hdb
    · exact Nat.zero_le _
  exact le_antisymm (one S T a b heq hk ha)
    (one T S b a (fun c hc => (heq c hc).symm) hk.symm (hk ▸ ha))

theorem gap_congr {j : ℕ} {S T : Finset Ordinal.{0}} {a b h : Ordinal.{0}}
    (G : Finset ExtOrd) (hh : j ≤ finitePart h)
    (heq : ∀ c, c < h → (c ∈ S ↔ c ∈ T))
    (hk : key j S a = key j T b) (ha : key j S a < h) :
    gap j S G a = gap j T G b := by
  unfold gap
  rw [gapStart_congr hh heq hk ha, hk]

/-- First block after all groups with key strictly below the target cut.
With an empty prefix it is block zero, so the initial gap is retained. -/
def prefixEnd (j : ℕ) (S : Finset Ordinal.{0}) (h : Ordinal.{0}) : ℕ := by
  classical
  exact S.sup (fun a => if key j S a < h then block j S a + 1 else 0)

theorem block_lt_prefixEnd {j : ℕ} {S : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (ha : a ∈ S) (hk : key j S a < h) : block j S a < prefixEnd j S h := by
  classical
  change block j S a + 1 ≤ _
  apply Finset.le_sup_of_le ha
  simp only [ite_eq_left hk, le_refl]

theorem prefixEnd_congr {j : ℕ} {S T : Finset Ordinal.{0}} {h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) :
    prefixEnd j S h = prefixEnd j T h := by
  classical
  have one (S T : Finset Ordinal.{0})
      (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) :
      prefixEnd j S h ≤ prefixEnd j T h := by
    apply Finset.sup_le
    intro a ha
    split_ifs with hk
    · obtain ⟨b, hb, _, hkb, hbb, _⟩ := low_group_transfer hh heq ha hk
      rw [hbb]
      exact block_lt_prefixEnd hb (hkb ▸ hk)
    · exact Nat.zero_le _
  exact le_antisymm (one S T heq) (one T S (fun b hb => (heq b hb).symm))

theorem prefixEnd_le_gapStart {j : ℕ} {S : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (ha : h ≤ key j S a) : prefixEnd j S h ≤ gapStart j S a := by
  classical
  apply Finset.sup_le
  intro b hb
  split_ifs with hbh
  · exact block_lt_gapStart hb (hbh.trans_le ha)
  · exact Nat.zero_le _

theorem prefixEnd_le_tailStart (j : ℕ) (S : Finset Ordinal.{0}) (h : Ordinal.{0}) :
    prefixEnd j S h ≤ tailStart j S := by
  classical
  apply Finset.sup_le
  intro a ha
  split_ifs
  · exact Nat.succ_le_succ (Finset.le_sup (f := block j S) ha)
  · exact Nat.zero_le _

theorem piece_of_lt_block {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    {x : ExtOrd} (hx : x < ofOrd (Ordinal.omega0 * block j S a)) :
    piece j S a x = ⊥ := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
  · unfold piece
    split_ifs <;> rfl
  · exact (not_lt_of_ge le_top hx).elim
  · unfold piece
    split_ifs
    · rw [FiniteOrbitEmbedding.ray_ofOrd,
        ite_eq_left ((limitPart_le b).trans_lt (ofOrd_lt_ofOrd.mp hx))]
    · exact stepShifter_of_lt (ofOrd_ne_bot _) hx

theorem step_of_lt_prefix {n k : ℕ} {C x : ExtOrd}
    (hn : n ≤ k) (hx : x < ofOrd (Ordinal.omega0 * n)) :
    stepShifter k ⊥ C x = ⊥ := by
  by_cases hb : x = ⊥
  · rw [hb]; rfl
  · apply stepShifter_of_lt hb
    exact hx.trans_le (ofOrd_le_ofOrd.mpr (by gcongr))

/-- Before the common prefix ends, every decoding contribution transports.
No restriction to short or represented source values is needed. -/
theorem decode_eq_before_prefix {j : ℕ} {S T : Finset Ordinal.{0}} {h : Ordinal.{0}}
    (G : Finset ExtOrd) (C C' : ExtOrd)
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T))
    {x : ExtOrd} (hx : x < ofOrd (Ordinal.omega0 * prefixEnd j S h)) :
    decode j S G C x = decode j T G C' x := by
  classical
  have one (S T : Finset Ordinal.{0}) (C C' : ExtOrd)
      (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T))
      (hx : x < ofOrd (Ordinal.omega0 * prefixEnd j S h)) :
      decode j S G C x ≤ decode j T G C' x := by
    apply max_le
    · apply Finset.sup_le
      intro a ha
      by_cases hk : key j S a < h
      · obtain ⟨b, hb, _, _, _, hp⟩ := low_group_transfer hh heq ha hk
        rw [hp]
        exact (Finset.le_sup (f := fun b => piece j T b x) hb).trans (le_max_left _ _)
      · have hn := (prefixEnd_le_gapStart (le_of_not_gt hk)).trans (gapStart_le j S a)
        rw [piece_of_lt_block (hx.trans_le (ofOrd_le_ofOrd.mpr (by gcongr)))]
        exact bot_le
    · apply max_le
      · apply Finset.sup_le
        intro a ha
        by_cases hk : key j S a < h
        · obtain ⟨b, hb, _, hkb, _, _⟩ := low_group_transfer hh heq ha hk
          rw [gap_congr G hh heq hkb hk]
          exact (Finset.le_sup (f := fun b => gap j T G b x) hb).trans
            ((le_max_left _ _).trans (le_max_right _ _))
        · rw [gap, step_of_lt_prefix (prefixEnd_le_gapStart (le_of_not_gt hk)) hx]
          exact bot_le
      · rw [step_of_lt_prefix (prefixEnd_le_tailStart j S h) hx]
        exact bot_le
  exact le_antisymm (one S T C C' heq hx)
    (one T S C' C (fun b hb => (heq b hb).symm)
      (by rwa [prefixEnd_congr hh (fun b hb => (heq b hb).symm)]))

/-- The gap preceding the first upper group starts immediately after the
unchanged prefix, even when that upper group is an orbit rather than a point. -/
theorem gapStart_first_upper {j : ℕ} {S : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (ha : h ≤ key j S a)
    (hfirst : ∀ b ∈ S, key j S b < key j S a → key j S b < h) :
    gapStart j S a = prefixEnd j S h := by
  classical
  apply le_antisymm _ (prefixEnd_le_gapStart ha)
  apply Finset.sup_le
  intro b hb
  split_ifs with hba
  · exact block_lt_prefixEnd hb (hfirst b hb hba)
  · exact Nat.zero_le _

theorem decode_prefix_reaches_of_first_upper
    {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd} {C : ExtOrd}
    {a h : Ordinal.{0}} (ha : a ∈ S) (hhG : ofOrd h ∈ G)
    (hh : h ≤ key j S a)
    (hfirst : ∀ b ∈ S, key j S b < key j S a → key j S b < h) :
    ofOrd h ≤ decode j S G C (ofOrd (Ordinal.omega0 * prefixEnd j S h)) := by
  apply decode_gap_reaches ha hhG (ofOrd_le_ofOrd.mpr hh)
  rw [gapStart_first_upper hh hfirst]

/-- An upper boundary value guarantees that the decoder reaches the cut at
the end of its low-key prefix. A shared orbit endpoint is included. -/
theorem decode_prefix_reaches
    {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd} {C : ExtOrd}
    {h : Ordinal.{0}} (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C)
    (hhG : ofOrd h ∈ G) (hupper : ∃ a ∈ S, h ≤ a) :
    ofOrd h ≤ decode j S G C (ofOrd (Ordinal.omega0 * prefixEnd j S h)) := by
  classical
  obtain ⟨a, ha, hha⟩ := hupper
  by_cases hk : key j S a < h
  · have hcode : encode j S a ≤ ofOrd (Ordinal.omega0 * prefixEnd j S h) :=
      (ofOrd_lt_ofOrd.mpr (code_add_lt_mul
        (Nat.cast_lt.mpr (block_lt_prefixEnd ha hk)) _)).le
    calc ofOrd h ≤ ofOrd a := ofOrd_le_ofOrd.mpr hha
      _ = decode j S G C (encode j S a) := (decode_encode ha).symm
      _ ≤ _ := (decode_witness hG hC).mono hcode
  · let U := S.filter (fun b => h ≤ key j S b)
    have hU : U.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, le_of_not_gt hk⟩⟩
    obtain ⟨b, hb, hmin⟩ := U.exists_min_image (key j S) hU
    apply decode_prefix_reaches_of_first_upper (Finset.mem_filter.mp hb).1 hhG
      (Finset.mem_filter.mp hb).2
    intro c hc hcb
    by_contra hn
    exact not_lt_of_ge (hmin c (Finset.mem_filter.mpr ⟨hc, le_of_not_gt hn⟩)) hcb

theorem decode_cap_ceiling {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd}
    {C C' h : ExtOrd} (hC : min C h = min C' h) (x : ExtOrd) :
    min (decode j S G C x) h = min (decode j S G C' x) h := by
  have hs : min (stepShifter (tailStart j S) ⊥ C x) h =
      min (stepShifter (tailStart j S) ⊥ C' x) h := by
    classical
    rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
    · rfl
    · exact hC
    · change min (if _ then _ else _) h = min (if _ then _ else _) h
      split_ifs <;> first | rfl | exact hC
  simp only [decode, min_max_distrib_right, hs]

/-- The decoder comparison includes every source value, not only short
ones: below the prefix end the functions agree literally, and above it
both reach the external grid cut. -/
theorem decode_cap_agree_of_upper
    {j : ℕ} {S T : Finset Ordinal.{0}} {G : Finset ExtOrd} {C C' : ExtOrd}
    {h : Ordinal.{0}} (hG : ∀ z ∈ G, SelfVis j z)
    (hC : SelfVis j C) (hC' : SelfVis j C') (hhG : ofOrd h ∈ G)
    (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T))
    (hS : ∃ a ∈ S, h ≤ a) (hT : ∃ a ∈ T, h ≤ a) (x : ExtOrd) :
    min (decode j S G C x) (ofOrd h) = min (decode j T G C' x) (ofOrd h) := by
  have hh : j ≤ finitePart h := selfVis_ofOrd_iff.mp (hG _ hhG)
  by_cases hx : x < ofOrd (Ordinal.omega0 * prefixEnd j S h)
  · rw [decode_eq_before_prefix G C C' hh heq hx]
  · have hp := decode_prefix_reaches hG hC hhG hS
    have hq := decode_prefix_reaches hG hC' hhG hT
    rw [← prefixEnd_congr hh heq] at hq
    rw [min_eq_right (hp.trans ((decode_witness hG hC).mono (le_of_not_gt hx))),
      min_eq_right (hq.trans ((decode_witness hG hC').mono (le_of_not_gt hx)))]

theorem block_le_twice_card {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : block j S a ≤ 2 * S.card := by
  have hr := rank_lt_card (j := j) ha
  classical
  unfold block
  split_ifs <;> omega

/-- The unused odd slot before an orbit is genuine room for a visible cut. -/
theorem gapStart_lt_orbit_block {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : Orbit j S a) : gapStart j S a < block j S a := by
  classical
  have hg : gapStart j S a ≤ 2 * rank j S a + 1 := by
    apply Finset.sup_le
    intro b hb
    split_ifs with hk
    · have hr := rank_lt_of_key_lt hb hk
      unfold block
      split_ifs <;> omega
    · omega
  simp only [block, ite_eq_left ha]
  omega

/-- Each profile has a visible grid cut reaching the external cut and lying
below every upper boundary source. The spare terminal block handles profiles
whose entire boundary is below the external cut, including an empty boundary. -/
theorem exists_source_cut {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd}
    {C : ExtOrd} {h : Ordinal.{0}}
    (hG : ∀ z ∈ G, SelfVis j z) (_hC : SelfVis j C)
    (hhG : ofOrd h ∈ G) (hhC : ofOrd h ≤ C) :
    ∃ b ≤ 2 * S.card + 1,
      ofOrd h ≤ decode j S G C (ofOrd (Ordinal.omega0 * b + j)) ∧
      ∀ a ∈ S, h ≤ a → ofOrd (Ordinal.omega0 * b + j) ≤ encode j S a := by
  classical
  let U := S.filter (fun a => h ≤ a)
  by_cases hU : U.Nonempty
  · obtain ⟨a, haU, hmin⟩ := U.exists_min_image id hU
    have ha := (Finset.mem_filter.mp haU).1
    have hha := (Finset.mem_filter.mp haU).2
    have hmincode (b : Ordinal.{0}) (hb : b ∈ S) (hhb : h ≤ b) :
        encode j S a ≤ encode j S b :=
      (encode_strictMonoOn j S).monotoneOn ha hb
        (hmin b (Finset.mem_filter.mpr ⟨hb, hhb⟩))
    by_cases hv : j ≤ finitePart a
    · have hoff : offset j S a = j := by
        unfold offset
        split_ifs with ho
        · exact le_antisymm ho.1 hv
        · rfl
      have he : encode j S a = ofOrd (Ordinal.omega0 * block j S a + j) := by
        rw [encode, hoff]
      refine ⟨block j S a, (block_le_twice_card ha).trans (Nat.le_succ _), ?_, ?_⟩
      · rw [← he, decode_encode ha]
        exact ofOrd_le_ofOrd.mpr hha
      · intro b hb hhb
        rw [← he]
        exact hmincode b hb hhb
    · have ho := orbit_of_invisible ha (lt_of_not_ge hv)
      have hfloor : h ≤ key j S a := by
        simp only [key, ite_eq_left ho]
        apply le_of_not_gt
        intro hl
        exact not_lt_of_ge hha
          (invisible_lt_cut (lt_of_not_ge hv) (selfVis_ofOrd_iff.mp (hG _ hhG)) hl)
      refine ⟨gapStart j S a,
        ((gapStart_le j S a).trans (block_le_twice_card ha)).trans (Nat.le_succ _),
        ?_, ?_⟩
      · apply decode_gap_reaches ha hhG (ofOrd_le_ofOrd.mpr hfloor)
        exact ofOrd_le_ofOrd.mpr le_self_add
      · intro b hb hhb
        apply le_trans _ (hmincode b hb hhb)
        apply ofOrd_le_ofOrd.mpr
        exact (code_add_lt_mul (Nat.cast_lt.mpr (gapStart_lt_orbit_block ho)) _).le.trans
          le_self_add
  · have ht : tailStart j S ≤ 2 * S.card + 1 := by
      apply Nat.succ_le_succ
      exact Finset.sup_le (fun a ha => block_le_twice_card ha)
    refine ⟨tailStart j S, ht, hhC.trans (decode_tail (ofOrd_le_ofOrd.mpr le_self_add)), ?_⟩
    intro a ha hha
    exact (hU ⟨a, Finset.mem_filter.mpr ⟨ha, hha⟩⟩).elim

section Profile
variable {X : Type*} [Fintype X]

/-- Whole-function capped agreement for decoders of boundary profiles.
The grid must contain the external cut and both terminal ceilings must
reach it. No unsupported-grid-point comparison is left as a hypothesis. -/
theorem decode_cap_agree {j : ℕ} {p q : X → ExtOrd}
    {G : Finset ExtOrd} {C C' : ExtOrd} {h : Ordinal.{0}}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) (hC' : SelfVis j C')
    (hhG : ofOrd h ∈ G) (hhC : ofOrd h ≤ C) (hhC' : ofOrd h ≤ C')
    (hp : ∀ d, p d ≠ ⊤) (hq : ∀ d, q d ≠ ⊤)
    (hpq : ∀ d, min (p d) (ofOrd h) = min (q d) (ofOrd h)) (x : ExtOrd) :
    min (decode j (values p) G C x) (ofOrd h) =
      min (decode j (values q) G C' x) (ofOrd h) := by
  classical
  by_cases hhigh : ∃ d, ofOrd h ≤ p d
  · obtain ⟨d, hd⟩ := hhigh
    have hqd : ofOrd h ≤ q d := by
      have he := hpq d
      rw [min_eq_right hd] at he
      exact he.trans_le (min_le_left _ _)
    have upper (v : X → ExtOrd) (hv : ∀ d, v d ≠ ⊤) (hd : ofOrd h ≤ v d) :
        ∃ a ∈ values v, h ≤ a := by
      rcases ExtOrd.cases (v d) with hb | ht | ⟨a, ha⟩
      · exact (not_ofOrd_le_bot h (hb ▸ hd)).elim
      · exact (hv d ht).elim
      · exact ⟨a, mem_values.mpr ⟨d, ha⟩, ofOrd_le_ofOrd.mp (ha ▸ hd)⟩
    apply decode_cap_agree_of_upper hG hC hC' hhG _ (upper p hp hd) (upper q hq hqd)
    intro b hb
    constructor
    · rintro hbS
      obtain ⟨e, he⟩ := mem_values.mp hbS
      have hlt : p e < ofOrd h := he ▸ ofOrd_lt_ofOrd.mpr hb
      exact mem_values.mpr ⟨e, (eq_of_cap_eq_lt (hpq e) hlt).symm.trans he⟩
    · rintro hbT
      obtain ⟨e, he⟩ := mem_values.mp hbT
      have hlt : q e < ofOrd h := he ▸ ofOrd_lt_ofOrd.mpr hb
      exact mem_values.mpr ⟨e, (eq_of_cap_eq_lt (hpq e).symm hlt).symm.trans he⟩
  · have he : p = q := funext fun d =>
      eq_of_cap_eq_lt (hpq d) (lt_of_not_ge (fun hd => hhigh ⟨d, hd⟩))
    rw [he]
    exact decode_cap_ceiling (by rw [min_eq_right hhC, min_eq_right hhC']) x

/-- A constructed common source-grid cut with all three scalar properties
needed by coupled source-prefix decoding. It covers unused gaps as well as
hosted orbits, and has a uniform finite source-grid bound. -/
theorem exists_common_source_cut {j : ℕ} {p q : X → ExtOrd}
    {G : Finset ExtOrd} {C C' : ExtOrd} {h : Ordinal.{0}}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) (hC' : SelfVis j C')
    (hhG : ofOrd h ∈ G) (hhC : ofOrd h ≤ C) (hhC' : ofOrd h ≤ C')
    (hp : ∀ d, p d ≠ ⊤) (hq : ∀ d, q d ≠ ⊤)
    (hpq : ∀ d, min (p d) (ofOrd h) = min (q d) (ofOrd h)) :
    ∃ b ≤ 2 * Fintype.card X + 1,
      let e := ofOrd (Ordinal.omega0 * b + j)
      SelfVis j e ∧
      (∀ d, min (PairedSlotEncoding.normalize j p d) e =
        min (PairedSlotEncoding.normalize j q d) e) ∧
      ofOrd h ≤ decode j (values p) G C e ∧
      ofOrd h ≤ decode j (values q) G C' e ∧
      (∀ x, min (decode j (values p) G C x) (ofOrd h) =
        min (decode j (values q) G C' x) (ofOrd h)) := by
  obtain ⟨b, hb, hread, hupper⟩ := exists_source_cut (S := values p) hG hC hhG hhC
  obtain ⟨c, hc, hread', hupper'⟩ := exists_source_cut (S := values q) hG hC' hhG hhC'
  have hcompare := decode_cap_agree hG hC hC' hhG hhC hhC' hp hq hpq
  let e := ofOrd (Ordinal.omega0 * min b c + j)
  have hbound : min b c ≤ 2 * Fintype.card X + 1 := by
    have hn := values_card_le p
    omega
  have he₁ : e ≤ ofOrd (Ordinal.omega0 * b + j) := by
    apply ofOrd_le_ofOrd.mpr
    gcongr
    exact min_le_left b c
  have he₂ : e ≤ ofOrd (Ordinal.omega0 * c + j) := by
    apply ofOrd_le_ofOrd.mpr
    gcongr
    exact min_le_right b c
  have both : ofOrd h ≤ decode j (values p) G C e ∧
      ofOrd h ≤ decode j (values q) G C' e := by
    have he := hcompare e
    rcases le_total b c with hbc | hcb
    · have hpread : ofOrd h ≤ decode j (values p) G C e := by
        simpa only [e, min_eq_left hbc] using hread
      rw [min_eq_right hpread] at he
      exact ⟨hpread, he.trans_le (min_le_left _ _)⟩
    · have hqread : ofOrd h ≤ decode j (values q) G C' e := by
        simpa only [e, min_eq_right hcb] using hread'
      rw [min_eq_right hqread] at he
      exact ⟨he.symm.trans_le (min_le_left _ _), hqread⟩
  refine ⟨min b c, hbound, ?_, ?_, both.1, both.2, hcompare⟩
  · apply selfVis_ofOrd_iff.mpr
    simp only [finitePart_mul_add, le_refl]
  · intro d
    change min (PairedSlotEncoding.normalize j p d) e =
      min (PairedSlotEncoding.normalize j q d) e
    by_cases hd : p d < ofOrd h
    · rw [normalize_prefix (selfVis_ofOrd_iff.mp (hG _ hhG)) hpq d hd]
    · have hpd : ofOrd h ≤ p d := le_of_not_gt hd
      have hqd : ofOrd h ≤ q d := by
        have he := hpq d
        rw [min_eq_right hpd] at he
        exact he.trans_le (min_le_left _ _)
      have upper (v : X → ExtOrd) (hv : ∀ d, v d ≠ ⊤) (k : ℕ)
          (hk : e ≤ ofOrd (Ordinal.omega0 * k + j))
          (hu : ∀ a ∈ values v, h ≤ a →
            ofOrd (Ordinal.omega0 * k + j) ≤ encode j (values v) a)
          (hd : ofOrd h ≤ v d) : e ≤ PairedSlotEncoding.normalize j v d := by
        rcases ExtOrd.cases (v d) with hb | ht | ⟨a, ha⟩
        · exact (not_ofOrd_le_bot h (hb ▸ hd)).elim
        · exact (hv d ht).elim
        · rw [normalize_ofOrd ha]
          exact hk.trans (hu a (mem_values.mpr ⟨d, ha⟩) (ofOrd_le_ofOrd.mp (ha ▸ hd)))
      rw [min_eq_right (upper p hp b he₁ hupper hpd),
        min_eq_right (upper q hq c he₂ hupper' hqd)]

end Profile

/-- The common source grid has one reserved block beyond every occupied
paired slot. It includes bottom and every visible endpoint up to that block. -/
def sourceGrid (j n : ℕ) : Finset ExtOrd := by
  classical
  exact insert ⊥ ((Finset.range (2 * n + 2)).image
    (fun b : ℕ => ofOrd (Ordinal.omega0 * b + j)))

theorem sourceGrid_bot (j n : ℕ) : ⊥ ∈ sourceGrid j n := by
  classical
  exact Finset.mem_insert_self _ _

theorem sourceGrid_endpoint {j n b : ℕ} (hb : b ≤ 2 * n + 1) :
    ofOrd (Ordinal.omega0 * b + j) ∈ sourceGrid j n := by
  classical
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨b, Finset.mem_range.mpr (by omega), rfl⟩)

theorem sourceGrid_visible {j n : ℕ} {e : ExtOrd} (he : e ∈ sourceGrid j n) :
    SelfVis j e := by
  classical
  rcases Finset.mem_insert.mp he with rfl | he
  · exact selfVis_bot j
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he
    apply selfVis_ofOrd_iff.mpr
    simp only [finitePart_mul_add, le_refl]

section Profile
variable {X : Type*} [Fintype X]

/-- The reserved terminal endpoint reads the chosen ceiling exactly. This
is separate from the bound on occupied alphabet values. -/
theorem decode_reserved_ceiling {j : ℕ} {p : X → ExtOrd} {G : Finset ExtOrd}
    {C : ExtOrd} (hC : SelfVis j C) (hpC : ∀ d, p d ≤ C) :
    decode j (values p) G C
      (ofOrd (Ordinal.omega0 * (2 * Fintype.card X + 1 : ℕ) + j)) = C := by
  have ht : tailStart j (values p) ≤ 2 * Fintype.card X + 1 := by
    apply Nat.succ_le_succ
    apply Finset.sup_le
    intro a ha
    have hn := values_card_le p
    have hb := block_le_twice_card (j := j) ha
    omega
  apply le_antisymm
  · apply decode_le hC
    intro a ha
    obtain ⟨d, hd⟩ := mem_values.mp ha
    simpa only [hd] using hpC d
  · apply decode_tail
    apply ofOrd_le_ofOrd.mpr
    exact (by gcongr : Ordinal.omega0 * tailStart j (values p) ≤
      Ordinal.omega0 * (2 * Fintype.card X + 1 : ℕ)).trans le_self_add

/-- All external cuts, including bottom and literal top. The returned cut
belongs to a fixed finite source grid independent of the target ordinals. -/
theorem exists_common_cut {j : ℕ} {p q : X → ExtOrd}
    {G : Finset ExtOrd} {C C' h : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) (hC' : SelfVis j C')
    (hhG : h ∈ G) (hhC : h ≤ C) (hhC' : h ≤ C')
    (hp : ∀ d, p d ≠ ⊤) (hq : ∀ d, q d ≠ ⊤)
    (hpq : ∀ d, min (p d) h = min (q d) h) :
    ∃ e ∈ sourceGrid j (Fintype.card X),
      (∀ d, min (PairedSlotEncoding.normalize j p d) e =
        min (PairedSlotEncoding.normalize j q d) e) ∧
      h ≤ decode j (values p) G C e ∧ h ≤ decode j (values q) G C' e ∧
      (∀ x, min (decode j (values p) G C x) h = min (decode j (values q) G C' x) h) := by
  rcases ExtOrd.cases h with rfl | rfl | ⟨a, rfl⟩
  · exact ⟨⊥, sourceGrid_bot _ _, fun _ => by simp, bot_le, bot_le, fun _ => by simp⟩
  · have he : p = q := funext fun d => by simpa only [min_top_right] using hpq d
    have hc : C = ⊤ := top_le_iff.mp hhC
    have hc' : C' = ⊤ := top_le_iff.mp hhC'
    subst q
    subst C
    subst C'
    refine ⟨ofOrd (Ordinal.omega0 * (2 * Fintype.card X + 1 : ℕ) + j),
      sourceGrid_endpoint le_rfl, fun _ => rfl, ?_, ?_, fun _ => rfl⟩ <;>
      rw [decode_reserved_ceiling (show SelfVis j ⊤ from rfl) (fun _ => le_top)]
  · obtain ⟨b, hb, _, hagree, hread, hread', hcompare⟩ :=
      exists_common_source_cut hG hC hC' hhG hhC hhC' hp hq hpq
    exact ⟨_, sourceGrid_endpoint hb, hagree, hread, hread', hcompare⟩

/-- The same largest-agreement-grid formula used by the source-row layer,
specialized to the paired normalization and its fixed endpoint grid. -/
def largestCommonCut (j : ℕ) (p q : X → ExtOrd) : ExtOrd := by
  classical
  exact ((sourceGrid j (Fintype.card X)).filter (fun e =>
    ∀ d, min (PairedSlotEncoding.normalize j p d) e =
      min (PairedSlotEncoding.normalize j q d) e)).sup id

/-- The coupled constructor may use its largest common grid cut, rather
than the smaller witness selected by the existence proof. -/
theorem largestCommonCut_spec {j : ℕ} {p q : X → ExtOrd}
    {G : Finset ExtOrd} {C C' h : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) (hC' : SelfVis j C')
    (hhG : h ∈ G) (hhC : h ≤ C) (hhC' : h ≤ C')
    (hp : ∀ d, p d ≠ ⊤) (hq : ∀ d, q d ≠ ⊤)
    (hpq : ∀ d, min (p d) h = min (q d) h) :
    let e := largestCommonCut j p q
    e ∈ sourceGrid j (Fintype.card X) ∧ SelfVis j e ∧
      (∀ d, min (PairedSlotEncoding.normalize j p d) e =
        min (PairedSlotEncoding.normalize j q d) e) ∧
      h ≤ decode j (values p) G C e ∧ h ≤ decode j (values q) G C' e ∧
      (∀ x, min (decode j (values p) G C x) h = min (decode j (values q) G C' x) h) := by
  classical
  let A := (sourceGrid j (Fintype.card X)).filter (fun e =>
    ∀ d, min (PairedSlotEncoding.normalize j p d) e =
      min (PairedSlotEncoding.normalize j q d) e)
  have hA : A.Nonempty :=
    ⟨⊥, Finset.mem_filter.mpr ⟨sourceGrid_bot _ _, fun _ => by simp⟩⟩
  obtain ⟨e, heA, he⟩ := Finset.sup_mem_of_nonempty (f := id) hA
  change e = largestCommonCut j p q at he
  have heG : largestCommonCut j p q ∈ sourceGrid j (Fintype.card X) :=
    he ▸ (Finset.mem_filter.mp heA).1
  have hagree : ∀ d, min (PairedSlotEncoding.normalize j p d) (largestCommonCut j p q) =
      min (PairedSlotEncoding.normalize j q d) (largestCommonCut j p q) :=
    he ▸ (Finset.mem_filter.mp heA).2
  obtain ⟨c, hcG, hc, hread, hread', hcompare⟩ :=
    exists_common_cut hG hC hC' hhG hhC hhC' hp hq hpq
  have hce : c ≤ largestCommonCut j p q :=
    Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hcG, hc⟩)
  exact ⟨heG, sourceGrid_visible heG, hagree,
    hread.trans ((decode_witness hG hC).mono hce),
    hread'.trans ((decode_witness hG hC').mono hce), hcompare⟩

end Profile

end
end VaughtConjecture.Knight.PairedSlotComparison
