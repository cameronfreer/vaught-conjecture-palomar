/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CountedRecoding

/-! # The `3 → 2 → 1` coherence triangle of the counted recoding

**Canonicality of construction-time sharp coding under iteration.**  Coding a row's grade-one
values directly at grade one, or first coding its grade-`≤ 2` values at grade two and then coding
the resulting witness's grade-one values at grade one, gives **literally the same grade-one
witness row** (`witness_comp_eq`), the same cap code (`capCode_comp_eq`), and decoders that agree
on the generated range, the cap, bottom, and every capped transformation image
(`decode_comp_eq`, `decode_comp_cap`, `decode_comp_bot`, `capped_row_eq`).  Beyond that, the two
decoders are equal on **all** of `ExtOrd` (`compShift_eq_shift`): this global equality is
load-bearing once cross-level locality is required at arbitrary level-one meet values, which
range over the whole grade-one alphabet below the cap.

This is a regression theorem for the recoding algebra of `Knight/CountedRecoding.lean`, not a
load-bearing interface: it certifies that iterated recoding introduces no path dependence, so a
triangular recursive construction may recode each lower level from whichever adjacent level it
likes. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## The triangle

**Acceptance test** (reviewer, 2026-09-05): (1) direct and composite grade-one codes
agree on the generated value set; (2) the composite decoder equals the direct decoder on the
generated range, at the cap, and at `⊥`; (3) the transformation conclusions agree after capping;
(4) equality on the whole alphabet only as a bonus.

**Setting.**  A level-three row `F` on proper cells (values `⊥` or ordinals, self-visible at
each cell's grade, grades positive).  Write `S l` for its nonbottom values at cells of grade
`≤ l` and `φ := code 2 (S 2)` for the level-two coding of a value.

* **Direct route**: the grade-one witness of `F` codes each grade-one value `v ∈ S 1` as
  `code 1 (S 1) v`, decoded by `shift 1 (S 1) γ`.
* **Composite route**: the level-two witness `w₂` codes each value `u ∈ S 2` as `φ u`; its own
  grade-one values are `φ '' S 1` (`valuesAt_witness`), and its grade-one witness codes
  `φ v` as `code 1 (φ '' S 1) (φ v)`, decoded by `shift 1 (φ '' S 1) γ₂` (cap `γ₂ := capCode 2`)
  and then by `shift 2 (S 2) γ`.

**The key lemma** (`key_code_eq_psi`, `psi_strictMonoOn`): the grade-one key of `φ u` is the
image of the grade-one key of `u` under a map `ψ` that is strictly monotone on the grade-one keys
of `S 1` — because `φ` preserves finite parts up to `2`, hence the grade-one key partition (same
`ω`-block for finite part `1`, atomic for finite part `≥ 2`) and its order.  Therefore the key
counts agree (`blockOf_code_eq`) and so do the codes (`code_comp_eq`, acceptance 1): **the
composite grade-one witness is literally the direct one**.

(2) `decode_comp_eq` (generated range), `decode_comp_cap` (the cap), `decode_comp_bot`;
(3) `capped_row_eq`: the capped transformation images of the (common) witness row agree.
No independently chosen enumeration enters: every code is a count over a key set.

Construction-private (not root-exported).  Reviewer scout (2026-09-06), graduated as a
canonicality/regression theorem; the load-bearing interface is `Knight/CountedRecoding.lean`. -/

section Triangle

variable {P : Type*} [Fintype P] [DecidableEq P] (gradeP : P → ℕ)

/-- The ordinal under a nonbottom, non-top extended value (`0` otherwise). -/
def toOrd : ExtOrd → Ordinal.{0}
  | some (some α) => α
  | _ => 0

@[simp] theorem toOrd_ofOrd (α : Ordinal.{0}) : toOrd (ofOrd α) = α := rfl

/-- The nonbottom values of a row at cells of grade `≤ l`, as ordinals. -/
noncomputable def valuesAt (F : P → ExtOrd) (l : ℕ) : Finset Ordinal.{0} :=
  (((Finset.univ.filter fun c => gradeP c ≤ l).image F).filter fun x => x ≠ ⊥ ∧ x ≠ ⊤).image toOrd

theorem mem_valuesAt {F : P → ExtOrd} {l : ℕ} {v : Ordinal.{0}} :
    v ∈ valuesAt gradeP F l ↔ ∃ c, gradeP c ≤ l ∧ F c = ofOrd v := by
  unfold valuesAt
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hx1, hx2, hx3⟩ := Finset.mem_filter.mp hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx1
    refine ⟨c, (Finset.mem_filter.mp hc).2, ?_⟩
    rcases ExtOrd.cases (F c) with h | h | ⟨α, h⟩
    · exact absurd h hx2
    · exact absurd h hx3
    · rw [h]; exact (congrArg ofOrd (toOrd_ofOrd α)).symm
  · rintro ⟨c, hc, hF⟩
    refine Finset.mem_image.mpr ⟨ofOrd v, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, hF⟩, ofOrd_ne_bot v, ofOrd_ne_top v⟩, rfl⟩

/-- The grade-`l` witness row of `F` over a value set `S`: the code at cells of grade `≤ l` with
a nonbottom value, `⊥` elsewhere. -/
noncomputable def witnessRow (F : P → ExtOrd) (l : ℕ) (S : Finset Ordinal.{0}) (c : P) : ExtOrd :=
  if gradeP c ≤ l then
    (match F c with
      | some (some α) => ofOrd (code l S α)
      | _ => ⊥)
  else ⊥

theorem witnessRow_ofOrd {F : P → ExtOrd} {l : ℕ} {S : Finset Ordinal.{0}} {c : P}
    (hc : gradeP c ≤ l) {α : Ordinal.{0}} (hF : F c = ofOrd α) :
    witnessRow gradeP F l S c = ofOrd (code l S α) := by
  unfold witnessRow; rw [if_pos hc, hF]; rfl

theorem witnessRow_bot {F : P → ExtOrd} {l : ℕ} {S : Finset Ordinal.{0}} {c : P}
    (hc : gradeP c ≤ l) (hF : F c = ⊥) : witnessRow gradeP F l S c = ⊥ := by
  unfold witnessRow; rw [if_pos hc, hF]

/-- A row whose values are self-visible at their cells' grades, with positive grades and no `⊤`. -/
structure OrderlyRow (F : P → ExtOrd) : Prop where
  pos : ∀ c, 1 ≤ gradeP c
  vis : ∀ c, SelfVis (gradeP c) (F c)
  ne_top : ∀ c, F c ≠ ⊤

variable {gradeP}

/-- The values of `F` at grade-one cells have finite part `≥ 1`. -/
theorem finitePart_pos_of_mem {F : P → ExtOrd} (hF : OrderlyRow gradeP F) {v : Ordinal.{0}}
    (hv : v ∈ valuesAt gradeP F 1) : 1 ≤ finitePart v := by
  obtain ⟨c, hc, hFc⟩ := (mem_valuesAt gradeP).mp hv
  have h := hF.vis c
  rw [hFc, selfVis_ofOrd_iff] at h
  exact (hF.pos c).trans h

theorem valuesAt_mono {F : P → ExtOrd} {l l' : ℕ} (h : l ≤ l') :
    valuesAt gradeP F l ⊆ valuesAt gradeP F l' := by
  intro v hv
  obtain ⟨c, hc, hFc⟩ := (mem_valuesAt gradeP).mp hv
  exact (mem_valuesAt gradeP).mpr ⟨c, hc.trans h, hFc⟩

/-- **The grade-one values of the level-two witness are the level-two codes of the grade-one
values of `F`.** -/
theorem valuesAt_witness (F : P → ExtOrd) :
    valuesAt gradeP (witnessRow gradeP F 2 (valuesAt gradeP F 2)) 1 =
      (valuesAt gradeP F 1).image (code 2 (valuesAt gradeP F 2)) := by
  ext u
  rw [mem_valuesAt, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, hw⟩
    unfold witnessRow at hw
    rw [if_pos (by omega)] at hw
    rcases hF : F c with _ | _ | α
    · rw [hF] at hw
      change (⊥ : ExtOrd) = ofOrd u at hw
      exact absurd hw.symm (ofOrd_ne_bot u)
    · rw [hF] at hw
      change (⊥ : ExtOrd) = ofOrd u at hw
      exact absurd hw.symm (ofOrd_ne_bot u)
    · rw [hF] at hw
      have : ofOrd (code 2 (valuesAt gradeP F 2) α) = ofOrd u := hw
      rw [ofOrd_inj] at this
      exact ⟨α, (mem_valuesAt gradeP).mpr ⟨c, hc, hF⟩, this⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨c, hc, hFc⟩ := (mem_valuesAt gradeP).mp hv
    exact ⟨c, hc, witnessRow_ofOrd gradeP (by omega) hFc⟩

/-! ### The key lemma: level-two coding preserves the grade-one key structure -/

section KeyLemma

variable (S₂ : Finset Ordinal.{0})

/-- The image of a grade-one key under level-two coding. -/
noncomputable def psi (κ : Ordinal.{0}) : Ordinal.{0} :=
  if finitePart κ = 0 then Ordinal.omega0 * (blockOfKey 2 S₂ κ : ℕ)
  else Ordinal.omega0 * (blockOfKey 2 S₂ (keyOrd 2 κ) : ℕ) + 2

/-- `keyOrd 2 u` for a value with finite part `≤ 2` is its `ω`-block. -/
theorem keyOrd_two_of_le {u : Ordinal.{0}} (h : finitePart u ≤ 2) : keyOrd 2 u = limitPart u := by
  unfold keyOrd; rw [if_pos h]

theorem keyOrd_two_of_gt {u : Ordinal.{0}} (h : 2 < finitePart u) : keyOrd 2 u = u := by
  unfold keyOrd; rw [if_neg (by omega)]

theorem keyOrd_one_of_eq_one {u : Ordinal.{0}} (h : finitePart u = 1) : keyOrd 1 u = limitPart u := by
  unfold keyOrd; rw [if_pos (by omega)]

theorem keyOrd_one_of_ge_two {u : Ordinal.{0}} (h : 2 ≤ finitePart u) : keyOrd 1 u = u := by
  unfold keyOrd; rw [if_neg (by omega)]

/-- **The grade-one key of `φ u` is `ψ` of the grade-one key of `u`** (for `fp u ≥ 1`). -/
theorem key_code_eq_psi {u : Ordinal.{0}} (hu : 1 ≤ finitePart u) :
    keyOrd 1 (code 2 S₂ u) = psi S₂ (keyOrd 1 u) := by
  unfold code
  rcases Nat.lt_or_ge (finitePart u) 2 with h1 | h2
  · have hfp : finitePart u = 1 := by omega
    rw [keyOrd_one_of_eq_one hfp]
    have hmin : min (finitePart u) 2 = 1 := by rw [hfp]; rfl
    rw [hmin]
    unfold psi
    rw [if_pos (finitePart_limitPart u)]
    unfold blockOf
    rw [keyOrd_two_of_le (by omega)]
    rw [keyOrd_one_of_eq_one (by rw [finitePart_mul_add])]
    rw [limitPart_mul_add]
  · rw [keyOrd_one_of_ge_two h2]
    have hmin : min (finitePart u) 2 = 2 := min_eq_right h2
    rw [hmin]
    unfold psi
    rw [if_neg (by omega)]
    unfold blockOf
    rw [keyOrd_one_of_ge_two (by rw [finitePart_mul_add])]
    norm_cast

theorem keyOrd_two_le_of_le {u u' : Ordinal.{0}} (h : u ≤ u') : keyOrd 2 u ≤ keyOrd 2 u' := by
  unfold keyOrd
  split_ifs with h1 h2 h2
  · exact limitPart_mono h
  · exact (limitPart_le u).trans h
  · -- `fp u > 2 ≥ fp u'`, so `u < lp u'`
    rcases lt_or_ge (limitPart u) (limitPart u') with hlt | hge
    · rw [← limitPart_add_finitePart u]
      exact limitPart_add_nat_le_of_lt hlt _
    · have heq : limitPart u = limitPart u' := le_antisymm (limitPart_mono h) hge
      have := finitePart_le_of_le_of_limitPart_eq h heq
      omega
  · exact h

theorem psi_of_fp_one {u : Ordinal.{0}} (h : finitePart u = 1) :
    psi S₂ (keyOrd 1 u) = Ordinal.omega0 * (blockOfKey 2 S₂ (keyOrd 2 u) : ℕ) := by
  rw [keyOrd_one_of_eq_one h]
  unfold psi
  rw [if_pos (finitePart_limitPart u), keyOrd_two_of_le (by omega)]

theorem psi_of_fp_ge_two {u : Ordinal.{0}} (h : 2 ≤ finitePart u) :
    psi S₂ (keyOrd 1 u) = Ordinal.omega0 * (blockOfKey 2 S₂ (keyOrd 2 u) : ℕ) + 2 := by
  rw [keyOrd_one_of_ge_two h]
  unfold psi
  rw [if_neg (by omega)]

/-- Strict order of grade-one keys reflects to the values (for finite parts `≥ 1`). -/
theorem lt_of_keyOrd_one_lt {u u' : Ordinal.{0}} (hu : 1 ≤ finitePart u) (hu' : 1 ≤ finitePart u')
    (h : keyOrd 1 u < keyOrd 1 u') : u < u' := by
  have hne : u ≠ u' := by rintro rfl; exact lt_irrefl _ h
  rcases Nat.lt_or_ge (finitePart u) 2 with h1 | h2
  · have hfp : finitePart u = 1 := by omega
    rw [keyOrd_one_of_eq_one hfp] at h
    rcases Nat.lt_or_ge (finitePart u') 2 with h1' | h2'
    · have hfp' : finitePart u' = 1 := by omega
      rw [keyOrd_one_of_eq_one hfp'] at h
      have h1le := limitPart_add_nat_le_of_lt h 1
      have hu'eq : limitPart u' + ((1 : ℕ) : Ordinal) = u' := by
        have := limitPart_add_finitePart u'; rwa [hfp'] at this
      calc u = limitPart u + (finitePart u : ℕ) := (limitPart_add_finitePart u).symm
        _ = limitPart u + ((1 : ℕ) : Ordinal) := by rw [hfp]
        _ ≤ limitPart u' := h1le
        _ < limitPart u' + ((1 : ℕ) : Ordinal) := by
          rw [Nat.cast_one]; exact Order.lt_add_one_iff.mpr le_rfl
        _ = u' := hu'eq
    · rw [keyOrd_one_of_ge_two h2'] at h
      -- `lp u < u'`, `u = lp u + 1`, `u ≠ u'`
      rcases lt_or_ge (limitPart u) (limitPart u') with hlt | hge
      · refine lt_of_le_of_ne ?_ hne
        calc u = limitPart u + (finitePart u : ℕ) := (limitPart_add_finitePart u).symm
          _ ≤ limitPart u' := limitPart_add_nat_le_of_lt hlt _
          _ ≤ u' := limitPart_le u'
      · have hle : limitPart u ≤ limitPart u' := by
          have := limitPart_mono h.le
          rwa [limitPart_idem] at this
        have heq : limitPart u = limitPart u' := le_antisymm hle hge
        exact lt_of_le_of_ne (le_of_finitePart_le heq (by omega)) hne
  · rw [keyOrd_one_of_ge_two h2] at h
    rcases Nat.lt_or_ge (finitePart u') 2 with h1' | h2'
    · have hfp' : finitePart u' = 1 := by omega
      rw [keyOrd_one_of_eq_one hfp'] at h
      exact h.trans_le (limitPart_le u')
    · rw [keyOrd_one_of_ge_two h2'] at h
      exact h

/-- **`ψ` is strictly monotone on the grade-one keys of values of `S₂` with finite part `≥ 1`.** -/
theorem psi_lt_psi {u u' : Ordinal.{0}} (hu : 1 ≤ finitePart u) (hu' : 1 ≤ finitePart u')
    (hu₂ : u ∈ S₂) (hu'₂ : u' ∈ S₂) (h : keyOrd 1 u < keyOrd 1 u') :
    psi S₂ (keyOrd 1 u) < psi S₂ (keyOrd 1 u') := by
  have huu' : u < u' := lt_of_keyOrd_one_lt hu hu' h
  have hk2 : keyOrd 2 u ≤ keyOrd 2 u' := keyOrd_two_le_of_le huu'.le
  have hb : blockOfKey 2 S₂ (keyOrd 2 u) ≤ blockOfKey 2 S₂ (keyOrd 2 u') := blockOfKey_mono 2 S₂ hk2
  rcases Nat.lt_or_ge (blockOfKey 2 S₂ (keyOrd 2 u)) (blockOfKey 2 S₂ (keyOrd 2 u')) with hlt | hge
  · -- different level-two blocks: `ω·b + 2 < ω·(b + 1) ≤ ω·b'`
    have hupper : psi S₂ (keyOrd 1 u) ≤ Ordinal.omega0 * (blockOfKey 2 S₂ (keyOrd 2 u) : ℕ) + 2 := by
      rcases Nat.lt_or_ge (finitePart u) 2 with h1 | h2
      · rw [psi_of_fp_one S₂ (by omega)]; exact le_self_add
      · rw [psi_of_fp_ge_two S₂ h2]
    have hlower : Ordinal.omega0 * (blockOfKey 2 S₂ (keyOrd 2 u') : ℕ) ≤ psi S₂ (keyOrd 1 u') := by
      rcases Nat.lt_or_ge (finitePart u') 2 with h1 | h2
      · rw [psi_of_fp_one S₂ (by omega)]
      · rw [psi_of_fp_ge_two S₂ h2]; exact le_self_add
    refine hupper.trans_lt (lt_of_lt_of_le ?_ hlower)
    calc Ordinal.omega0 * (blockOfKey 2 S₂ (keyOrd 2 u) : ℕ) + 2
        < Ordinal.omega0 * (blockOfKey 2 S₂ (keyOrd 2 u) : ℕ) + Ordinal.omega0 := by
          exact (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 2)
      _ = Ordinal.omega0 * ((blockOfKey 2 S₂ (keyOrd 2 u) + 1 : ℕ) : Ordinal) := by
          rw [Nat.cast_succ, mul_add, mul_one]
      _ ≤ Ordinal.omega0 * (blockOfKey 2 S₂ (keyOrd 2 u') : ℕ) := by
          gcongr; exact_mod_cast hlt
  · -- same level-two block: same level-two key, so `fp u = 1`, `fp u' = 2`, same `ω`-block
    have hbe : blockOfKey 2 S₂ (keyOrd 2 u) = blockOfKey 2 S₂ (keyOrd 2 u') := le_antisymm hb hge
    have hke : keyOrd 2 u = keyOrd 2 u' :=
      blockOfKey_injOn 2 S₂ (keyOrd_mem_keys 2 S₂ hu₂) (keyOrd_mem_keys 2 S₂ hu'₂) hbe
    have hfu : finitePart u ≤ 2 := by
      by_contra hgt
      rw [keyOrd_two_of_gt (by omega)] at hke
      rcases Nat.lt_or_ge (finitePart u') 3 with h3 | h3
      · rw [keyOrd_two_of_le (by omega)] at hke
        have := congrArg finitePart hke
        rw [finitePart_limitPart] at this
        omega
      · rw [keyOrd_two_of_gt (by omega)] at hke
        exact absurd hke (ne_of_lt huu')
    have hfu' : finitePart u' ≤ 2 := by
      by_contra hgt
      rw [keyOrd_two_of_le hfu, keyOrd_two_of_gt (by omega)] at hke
      have := congrArg finitePart hke
      rw [finitePart_limitPart] at this
      omega
    rw [keyOrd_two_of_le hfu, keyOrd_two_of_le hfu'] at hke
    have hfpl := finitePart_le_of_le_of_limitPart_eq huu'.le hke
    have hne : finitePart u ≠ finitePart u' := by
      intro heq
      exact absurd (le_antisymm huu'.le (le_of_finitePart_le hke.symm heq.symm.le)) (ne_of_lt huu')
    have hfu1 : finitePart u = 1 := by omega
    have hfu2 : finitePart u' = 2 := by omega
    rw [psi_of_fp_one S₂ hfu1, psi_of_fp_ge_two S₂ (by omega), keyOrd_two_of_le hfu,
      keyOrd_two_of_le hfu', hke]
    exact lt_add_of_pos_right _ (by exact_mod_cast (Nat.succ_pos 1))

end KeyLemma

/-! ### Composition: the composite grade-one witness is the direct one -/

section Composition

variable {F : P → ExtOrd}

theorem keys_image (hF : OrderlyRow gradeP F) :
    keys 1 ((valuesAt gradeP F 1).image (code 2 (valuesAt gradeP F 2))) =
      (keys 1 (valuesAt gradeP F 1)).image (psi (valuesAt gradeP F 2)) := by
  unfold keys
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro v hv
  exact key_code_eq_psi _ (finitePart_pos_of_mem hF (Finset.mem_coe.mp hv))

theorem psi_strictMonoOn (hF : OrderlyRow gradeP F) :
    StrictMonoOn (psi (valuesAt gradeP F 2)) (keys 1 (valuesAt gradeP F 1)) := by
  intro κ hκ κ' hκ' hlt
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hκ)
  obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hκ')
  exact psi_lt_psi _ (finitePart_pos_of_mem hF hu) (finitePart_pos_of_mem hF hu')
    (valuesAt_mono (by omega) hu) (valuesAt_mono (by omega) hu') hlt

/-- **The key counts agree**: the block of `ψ κ` in the composite key set is the block of `κ` in
the direct one. -/
theorem blockOfKey_psi (hF : OrderlyRow gradeP F) {κ : Ordinal.{0}}
    (hκ : κ ∈ keys 1 (valuesAt gradeP F 1)) :
    blockOfKey 1 ((valuesAt gradeP F 1).image (code 2 (valuesAt gradeP F 2)))
        (psi (valuesAt gradeP F 2) κ) =
      blockOfKey 1 (valuesAt gradeP F 1) κ := by
  unfold blockOfKey
  rw [keys_image hF]
  have hmono := psi_strictMonoOn hF
  have hfilt : ((keys 1 (valuesAt gradeP F 1)).image (psi (valuesAt gradeP F 2))).filter
      (fun κ' => κ' ≤ psi (valuesAt gradeP F 2) κ) =
      ((keys 1 (valuesAt gradeP F 1)).filter fun κ'' => κ'' ≤ κ).image (psi (valuesAt gradeP F 2)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨κ'', hκ'', rfl⟩, hle⟩
      exact ⟨κ'', ⟨hκ'', (hmono.le_iff_le (Finset.mem_coe.mpr hκ'') (Finset.mem_coe.mpr hκ)).mp hle⟩,
        rfl⟩
    · rintro ⟨κ'', ⟨hκ'', hle⟩, rfl⟩
      exact ⟨⟨κ'', hκ'', rfl⟩,
        hmono.monotoneOn (Finset.mem_coe.mpr hκ'') (Finset.mem_coe.mpr hκ) hle⟩
  rw [hfilt, Finset.card_image_of_injOn
    (hmono.injOn.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]

/-- **Acceptance (1): the composite grade-one code of a grade-one value is the direct one.** -/
theorem code_comp_eq (hF : OrderlyRow gradeP F) {v : Ordinal.{0}} (hv : v ∈ valuesAt gradeP F 1) :
    code 1 ((valuesAt gradeP F 1).image (code 2 (valuesAt gradeP F 2)))
        (code 2 (valuesAt gradeP F 2) v) =
      code 1 (valuesAt gradeP F 1) v := by
  have hfp := finitePart_pos_of_mem hF hv
  have h1 : blockOf 1 ((valuesAt gradeP F 1).image (code 2 (valuesAt gradeP F 2)))
      (code 2 (valuesAt gradeP F 2) v) = blockOf 1 (valuesAt gradeP F 1) v := by
    unfold blockOf
    rw [key_code_eq_psi _ hfp, blockOfKey_psi hF (keyOrd_mem_keys 1 _ hv)]
  have h2 : finitePart (code 2 (valuesAt gradeP F 2) v) = min (finitePart v) 2 := by
    unfold code; rw [finitePart_mul_add]
  calc code 1 ((valuesAt gradeP F 1).image (code 2 (valuesAt gradeP F 2)))
        (code 2 (valuesAt gradeP F 2) v)
      = Ordinal.omega0 * (blockOf 1 ((valuesAt gradeP F 1).image (code 2 (valuesAt gradeP F 2)))
          (code 2 (valuesAt gradeP F 2) v) : ℕ) +
          (min (finitePart (code 2 (valuesAt gradeP F 2) v)) 1 : ℕ) := rfl
    _ = Ordinal.omega0 * (blockOf 1 (valuesAt gradeP F 1) v : ℕ) + (min (finitePart v) 1 : ℕ) := by
        rw [h1, h2]
        congr 1
        exact Nat.cast_inj.mpr (by omega)
    _ = code 1 (valuesAt gradeP F 1) v := rfl

/-- The composite value set has the same number of keys, hence the same cap code. -/
theorem card_keys_comp (hF : OrderlyRow gradeP F) :
    (keys 1 ((valuesAt gradeP F 1).image (code 2 (valuesAt gradeP F 2)))).card =
      (keys 1 (valuesAt gradeP F 1)).card := by
  rw [keys_image hF, Finset.card_image_of_injOn (psi_strictMonoOn hF).injOn]

theorem capCode_comp_eq (hF : OrderlyRow gradeP F) :
    capCode 1 ((valuesAt gradeP F 1).image (code 2 (valuesAt gradeP F 2))) =
      capCode 1 (valuesAt gradeP F 1) := by
  unfold capCode; rw [card_keys_comp hF]

/-- **The composite grade-one witness row is literally the direct one.** -/
theorem witness_comp_eq (hF : OrderlyRow gradeP F) :
    witnessRow gradeP (witnessRow gradeP F 2 (valuesAt gradeP F 2)) 1
        (valuesAt gradeP (witnessRow gradeP F 2 (valuesAt gradeP F 2)) 1) =
      witnessRow gradeP F 1 (valuesAt gradeP F 1) := by
  funext c
  rw [valuesAt_witness]
  by_cases hc : gradeP c ≤ 1
  · rcases hFc : F c with _ | _ | α
    · rw [witnessRow_bot gradeP hc hFc, witnessRow_bot gradeP hc (witnessRow_bot gradeP (by omega) hFc)]
    · exact absurd hFc (hF.ne_top c)
    · have hα : F c = ofOrd α := hFc
      rw [witnessRow_ofOrd gradeP hc hα,
        witnessRow_ofOrd gradeP hc (witnessRow_ofOrd gradeP (by omega) hα),
        code_comp_eq hF ((mem_valuesAt gradeP).mpr ⟨c, hc, hα⟩)]
  · unfold witnessRow; rw [if_neg hc, if_neg hc]

/-! ### Decoder agreement on the generated range, the cap, and bottom -/

variable (γ : ExtOrd)

/-- The composite decoder: level-one codes to level-two codes (cap `capCode 2`), then to values. -/
noncomputable def compShift : ExtOrd → ExtOrd :=
  fun x => shift 2 (valuesAt gradeP F 2) γ
    (shift 1 ((valuesAt gradeP F 1).image (code 2 (valuesAt gradeP F 2)))
      (ofOrd (capCode 2 (valuesAt gradeP F 2))) x)

/-- **Acceptance (2), generated range.** -/
theorem decode_comp_eq (hF : OrderlyRow gradeP F) {v : Ordinal.{0}} (hv : v ∈ valuesAt gradeP F 1) :
    compShift (gradeP := gradeP) (F := F) γ (ofOrd (code 1 (valuesAt gradeP F 1) v)) = ofOrd v ∧
    shift 1 (valuesAt gradeP F 1) γ (ofOrd (code 1 (valuesAt gradeP F 1) v)) = ofOrd v := by
  refine ⟨?_, shift_code 1 _ γ hv⟩
  unfold compShift
  rw [← code_comp_eq hF hv, shift_code 1 _ _ (Finset.mem_image_of_mem _ hv),
    shift_code 2 _ γ (valuesAt_mono (by omega) hv)]

/-- **Acceptance (2), the cap.** -/
theorem decode_comp_cap (hF : OrderlyRow gradeP F) :
    compShift (gradeP := gradeP) (F := F) γ (ofOrd (capCode 1 (valuesAt gradeP F 1))) = γ ∧
    shift 1 (valuesAt gradeP F 1) γ (ofOrd (capCode 1 (valuesAt gradeP F 1))) = γ := by
  refine ⟨?_, shift_capCode 1 _ γ⟩
  unfold compShift
  rw [← capCode_comp_eq hF, shift_capCode 1, shift_capCode 2]

/-- **Acceptance (2), bottom.** -/
theorem decode_comp_bot :
    compShift (gradeP := gradeP) (F := F) γ ⊥ = ⊥ ∧ shift 1 (valuesAt gradeP F 1) γ ⊥ = ⊥ :=
  ⟨by unfold compShift; rw [shift_bot, shift_bot], shift_bot 1 _ γ⟩

/-- **Acceptance (3): the two decoders agree on the whole witness row**, hence on every capped
transformation image of it. -/
theorem decode_comp_witness (hF : OrderlyRow gradeP F) (c : P) :
    compShift (gradeP := gradeP) (F := F) γ (witnessRow gradeP F 1 (valuesAt gradeP F 1) c) =
      shift 1 (valuesAt gradeP F 1) γ (witnessRow gradeP F 1 (valuesAt gradeP F 1) c) := by
  by_cases hc : gradeP c ≤ 1
  · rcases hFc : F c with _ | _ | α
    · rw [witnessRow_bot gradeP hc hFc, (decode_comp_bot γ).1, (decode_comp_bot γ).2]
    · exact absurd hFc (hF.ne_top c)
    · have hα : F c = ofOrd α := hFc
      have hv := (mem_valuesAt gradeP).mpr ⟨c, hc, hα⟩
      rw [witnessRow_ofOrd gradeP hc hα, (decode_comp_eq γ hF hv).1, (decode_comp_eq γ hF hv).2]
  · have hb : witnessRow gradeP F 1 (valuesAt gradeP F 1) c = ⊥ := by
      unfold witnessRow; rw [if_neg hc]
    rw [hb, (decode_comp_bot γ).1, (decode_comp_bot γ).2]

theorem capped_row_eq (hF : OrderlyRow gradeP F) (g : ℕ → ExtOrd) (c : P) :
    min (compShift (gradeP := gradeP) (F := F) γ (witnessRow gradeP F 1 (valuesAt gradeP F 1) c))
        (g (gradeP c)) =
      min (shift 1 (valuesAt gradeP F 1) γ (witnessRow gradeP F 1 (valuesAt gradeP F 1) c))
        (g (gradeP c)) := by
  rw [decode_comp_witness γ hF c]

end Composition

/-! ### Global decoder equality

Load-bearing once locality is required at arbitrary level-one meet values (the mixed square of
`Knight/ThreeLevelFragment.lean`): the composite decoder equals the direct decoder on **all** of
`ExtOrd`, block by block through the key correspondence. -/

section Global

variable {F : P → ExtOrd}

theorem decodeIn_of_fp_zero (l : ℕ) {κ : Ordinal.{0}} (h : finitePart κ = 0) (j : ℕ) :
    decodeIn l κ j = κ + (min j l : ℕ) := by
  unfold decodeIn; rw [if_pos h]

theorem decodeIn_of_fp_ne (l : ℕ) {κ : Ordinal.{0}} (h : finitePart κ ≠ 0) (j : ℕ) :
    decodeIn l κ j = κ := by
  unfold decodeIn; rw [if_neg h]

/-- On the block of a grade-one key, composite decoding agrees with direct decoding. -/
theorem shift_two_decodeIn_psi (hF : OrderlyRow gradeP F) {κ : Ordinal.{0}}
    (hκ : κ ∈ keys 1 (valuesAt gradeP F 1)) (γ : ExtOrd) (j : ℕ) :
    shift 2 (valuesAt gradeP F 2) γ (ofOrd (decodeIn 1 (psi (valuesAt gradeP F 2) κ) j)) =
      ofOrd (decodeIn 1 κ j) := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hκ
  have hfp := finitePart_pos_of_mem hF hv
  have hv₂ : v ∈ valuesAt gradeP F 2 := valuesAt_mono (by omega) hv
  rcases Nat.lt_or_ge (finitePart v) 2 with h1 | h2
  · -- `fp v = 1`: an `ω`-block key
    have hfp1 : finitePart v = 1 := by omega
    rw [psi_of_fp_one _ hfp1, keyOrd_two_of_le (by omega), keyOrd_one_of_eq_one hfp1]
    have hk2 : limitPart v ∈ keys 2 (valuesAt gradeP F 2) := by
      have := keyOrd_mem_keys 2 (valuesAt gradeP F 2) hv₂
      rwa [keyOrd_two_of_le (by omega)] at this
    set b := blockOfKey 2 (valuesAt gradeP F 2) (limitPart v) with hb
    rw [decodeIn_of_fp_zero 1 (finitePart_mul _), shift_ofOrd, blockIdx_mul_add]
    have hble : b ≤ (keys 2 (valuesAt gradeP F 2)).card := blockOfKey_le _ _ _
    rw [if_neg (fun h => absurd (by exact_mod_cast h : (keys 2 (valuesAt gradeP F 2)).card + 1 ≤ b)
      (by omega))]
    rw [keyAt_eq_of_mem 2 _ hk2]
    simp only
    rw [finitePart_mul_add, decodeIn_of_fp_zero 2 (finitePart_limitPart v),
      decodeIn_of_fp_zero 1 (finitePart_limitPart v)]
    congr 2
    exact Nat.cast_inj.mpr (by omega)
  · -- `fp v ≥ 2`: an atomic grade-one key
    rw [psi_of_fp_ge_two _ h2, keyOrd_one_of_ge_two h2]
    set b := blockOfKey 2 (valuesAt gradeP F 2) (keyOrd 2 v) with hb
    have hfp2 : finitePart (Ordinal.omega0 * (b : ℕ) + 2) = 2 := by
      have := finitePart_mul_add b 2; rwa [Nat.cast_ofNat] at this
    have hbi : blockIdx (Ordinal.omega0 * (b : ℕ) + 2) = b := by
      have := blockIdx_mul_add b 2; rwa [Nat.cast_ofNat] at this
    rw [decodeIn_of_fp_ne 1 (by rw [hfp2]; omega), shift_ofOrd, hbi]
    have hble : b ≤ (keys 2 (valuesAt gradeP F 2)).card := blockOfKey_le _ _ _
    rw [if_neg (fun h => absurd (by exact_mod_cast h : (keys 2 (valuesAt gradeP F 2)).card + 1 ≤ b)
      (by omega))]
    rw [keyAt_eq_of_mem 2 _ (keyOrd_mem_keys 2 _ hv₂)]
    simp only
    rw [hfp2, decodeIn_of_fp_ne 1 (by omega)]
    rcases Nat.lt_or_ge (finitePart v) 3 with h3 | h3
    · have hfp2' : finitePart v = 2 := by omega
      rw [keyOrd_two_of_le (by omega), decodeIn_of_fp_zero 2 (finitePart_limitPart v)]
      congr 1
      conv_rhs => rw [← limitPart_add_finitePart v]
      rw [hfp2']
      rfl
    · rw [keyOrd_two_of_gt (by omega), decodeIn_of_fp_ne 2 (by omega)]

/-- **Global decoder equality**: the composite decoder is the direct one on all of `ExtOrd`. -/
theorem compShift_eq_shift (hF : OrderlyRow gradeP F) (γ : ExtOrd) (x : ExtOrd) :
    compShift (gradeP := gradeP) (F := F) γ x = shift 1 (valuesAt gradeP F 1) γ x := by
  unfold compShift
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [shift_bot, shift_bot, shift_bot]
  · rw [shift_top, shift_top, shift_capCode]
  · have hK := card_keys_comp hF
    rw [shift_ofOrd 1 _ _ α]
    rw [shift_ofOrd 1 (valuesAt gradeP F 1) γ α]
    rw [hK]
    split_ifs with h
    · exact shift_capCode 2 _ γ
    · obtain ⟨n, hn, hnle⟩ := exists_nat_of_lt_card 1 (valuesAt gradeP F 1) (not_le.mp h)
      rw [hn]
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · rw [Nat.cast_zero, keyAt_zero, keyAt_zero]
        exact shift_bot 2 _ γ
      · obtain ⟨κ, hκ, hk, hbκ⟩ := keyAt_nat_eq_some 1 (valuesAt gradeP F 1) hpos hnle
        have hψ : keyAt 1 ((valuesAt gradeP F 1).image (code 2 (valuesAt gradeP F 2))) n =
            some (psi (valuesAt gradeP F 2) κ) := by
          have hmem : psi (valuesAt gradeP F 2) κ ∈
              keys 1 ((valuesAt gradeP F 1).image (code 2 (valuesAt gradeP F 2))) := by
            rw [keys_image hF]; exact Finset.mem_image_of_mem _ hκ
          have := keyAt_eq_of_mem 1 _ hmem
          rw [blockOfKey_psi hF hκ, hbκ] at this
          exact this
        rw [hk, hψ]
        simp only
        exact shift_two_decodeIn_psi hF hκ γ (finitePart α)

end Global



end Triangle

end VaughtConjecture.Knight
