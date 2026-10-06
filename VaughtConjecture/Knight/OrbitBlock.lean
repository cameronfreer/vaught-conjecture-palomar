/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelabelWitness

/-! # The orbit-block witness

A `gTop 2`-witness that reproduces the grade-two replacement orbit of one value `a` on one block:
`⊥` below the block floor `ω·b`, the orbit `R₂ⁱ a` at the point `ω·b + i` of the block (with
`i` clipped at `2`), and the orbit's top `R₂² a` from the next block floor on
(`orbitBlock a b`, `witness_orbitBlock`; `a` self-visible at grade one).  This is the shape a
witness table must have at a source block carrying two labels that clause 5 couples — the proper
label `ω + 1` and a request `ω + 2` — so it is the generic piece of every level-two table of the
lift.  Constants are spliced above it at limit cuts (`witness_spliceAt`).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-- The block floor `ω·b`. -/
noncomputable abbrev bfloor (b : ℕ) : Ordinal.{0} := Ordinal.omega0 * (b : Ordinal)

theorem bfloor_succ (b : ℕ) : bfloor (b + 1) = bfloor b + Ordinal.omega0 := by
  unfold bfloor; rw [Nat.cast_succ, mul_add_one]

theorem limitPart_bfloor (b : ℕ) : limitPart (bfloor b) = bfloor b :=
  limitPart_mul_nat b

/-- The limit part of a point of the block `[ω·b, ω·(b+1))` is the floor. -/
theorem limitPart_of_mem_block {b : ℕ} {α : Ordinal.{0}} (h1 : bfloor b ≤ α)
    (h2 : α < bfloor (b + 1)) : limitPart α = bfloor b := by
  have := limitPart_eq_of_mem_block (x := bfloor b) (q := α)
    (by rw [limitPart_bfloor]; exact h1) (by rw [limitPart_bfloor, ← bfloor_succ]; exact h2)
  rwa [limitPart_bfloor] at this

theorem mem_block_add {b i : ℕ} :
    bfloor b ≤ bfloor b + (i : Ordinal) ∧ bfloor b + (i : Ordinal) < bfloor (b + 1) := by
  refine ⟨le_self_add, ?_⟩
  rw [bfloor_succ]
  exact add_lt_add_right (Ordinal.natCast_lt_omega0 i) _

/-! ## Replacement orbits of a grade-one self-visible value -/

/-- The orbit is monotone in the offset. -/
theorem evr_mono_offset {a : ExtOrd} (ha : SelfVis 1 a) {i j : ℕ} (hij : i ≤ j) :
    extVisibilityReplace a 2 i ≤ extVisibilityReplace a 2 j := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · rw [extVisibilityReplace_bot, extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top, extVisibilityReplace_top]
  · by_cases h : finitePart α < 2
    · rw [extVisibilityReplace_of_finitePart_lt h, extVisibilityReplace_of_finitePart_lt h,
        ofOrd_le_ofOrd]
      exact add_le_add_right (Nat.cast_le.mpr hij) _
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp h),
        extVisibilityReplace_of_le_finitePart (not_lt.mp h)]

/-- Replacing the orbit point `R₂ʲ a` at a threshold `k ≤ 2` above `j` gives the orbit point. -/
theorem evr_evr_of_lt {a : ExtOrd} {k i j : ℕ} (hk : k ≤ 2) (hj : j < k) :
    extVisibilityReplace (extVisibilityReplace a 2 j) k i = extVisibilityReplace a 2 i := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · rw [extVisibilityReplace_bot, extVisibilityReplace_bot, extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top, extVisibilityReplace_top, extVisibilityReplace_top]
  · by_cases h : finitePart α < 2
    · rw [extVisibilityReplace_of_finitePart_lt h, extVisibilityReplace_of_finitePart_lt h,
        extVisibilityReplace_of_finitePart_lt (by rw [finitePart_limitPart_add_nat]; exact hj),
        limitPart_limitPart_add_nat]
    · have h' := not_lt.mp h
      rw [extVisibilityReplace_of_le_finitePart h', extVisibilityReplace_of_le_finitePart h',
        extVisibilityReplace_of_le_finitePart (hk.trans h')]

/-- The orbit point `R₂ᵐ a` is fixed by replacement at thresholds `k ≤ m`, `k ≤ 2`. -/
theorem evr_evr_of_le {a : ExtOrd} {k i m : ℕ} (hk : k ≤ 2) (hkm : k ≤ m) :
    extVisibilityReplace (extVisibilityReplace a 2 m) k i = extVisibilityReplace a 2 m := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · rw [extVisibilityReplace_bot, extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top, extVisibilityReplace_top]
  · by_cases h : finitePart α < 2
    · rw [extVisibilityReplace_of_finitePart_lt h,
        extVisibilityReplace_of_le_finitePart (by rw [finitePart_limitPart_add_nat]; exact hkm)]
    · have h' := not_lt.mp h
      rw [extVisibilityReplace_of_le_finitePart h',
        extVisibilityReplace_of_le_finitePart (hk.trans h')]

theorem evr_eq_bot_iff {a : ExtOrd} (k i : ℕ) : extVisibilityReplace a k i = ⊥ ↔ a = ⊥ := by
  constructor
  · intro h; by_contra ha; exact extVisibilityReplace_ne_bot ha k i h
  · rintro rfl; exact extVisibilityReplace_bot _ _

/-! ## The orbit-block map -/

/-- **The orbit block**: `⊥` below `ω·b`, the orbit of `a` on the block, its top above. -/
noncomputable def orbitBlock (a : ExtOrd) (b : ℕ) : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => extVisibilityReplace a 2 2
  | some (some α) =>
      if α < bfloor b then ⊥
      else if α < bfloor (b + 1) then extVisibilityReplace a 2 (min (finitePart α) 2)
      else extVisibilityReplace a 2 2

theorem orbitBlock_bot (a : ExtOrd) (b : ℕ) : orbitBlock a b ⊥ = ⊥ := rfl

theorem orbitBlock_top (a : ExtOrd) (b : ℕ) : orbitBlock a b ⊤ = extVisibilityReplace a 2 2 := rfl

theorem orbitBlock_of_lt (a : ExtOrd) {b : ℕ} {α : Ordinal.{0}} (h : α < bfloor b) :
    orbitBlock a b (ofOrd α) = ⊥ := by
  change (if α < bfloor b then ⊥ else _) = ⊥
  rw [ite_eq_left h]

theorem orbitBlock_of_mem (a : ExtOrd) {b : ℕ} {α : Ordinal.{0}} (h1 : bfloor b ≤ α)
    (h2 : α < bfloor (b + 1)) :
    orbitBlock a b (ofOrd α) = extVisibilityReplace a 2 (min (finitePart α) 2) := by
  change (if α < bfloor b then ⊥ else if α < bfloor (b + 1) then _ else _) = _
  rw [ite_eq_right (not_lt.mpr h1), ite_eq_left h2]

theorem orbitBlock_of_ge (a : ExtOrd) {b : ℕ} {α : Ordinal.{0}} (h : bfloor (b + 1) ≤ α) :
    orbitBlock a b (ofOrd α) = extVisibilityReplace a 2 2 := by
  have h1 : ¬ α < bfloor b := not_lt.mpr ((le_self_add.trans (bfloor_succ b).symm.le).trans h)
  change (if α < bfloor b then ⊥ else if α < bfloor (b + 1) then _ else _) = _
  rw [ite_eq_right h1, ite_eq_right (not_lt.mpr h)]

theorem orbitBlock_le_top {a : ExtOrd} (ha : SelfVis 1 a) (b : ℕ) (x : ExtOrd) :
    orbitBlock a b x ≤ extVisibilityReplace a 2 2 := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [orbitBlock_bot]; exact bot_le
  · rw [orbitBlock_top]
  · by_cases h1 : α < bfloor b
    · rw [orbitBlock_of_lt a h1]; exact bot_le
    · by_cases h2 : α < bfloor (b + 1)
      · rw [orbitBlock_of_mem a (not_lt.mp h1) h2]
        exact evr_mono_offset ha (min_le_right _ _)
      · rw [orbitBlock_of_ge a (not_lt.mp h2)]

/-- The orbit's top is self-visible at grade two. -/
theorem evr_two_two_selfVis {a : ExtOrd} (ha : SelfVis 1 a) :
    SelfVis 2 (extVisibilityReplace a 2 2) := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · rw [extVisibilityReplace_bot]; exact selfVis_bot _
  · rw [extVisibilityReplace_top]; exact extVisibilityReplace_top _ _
  · by_cases h : finitePart α < 2
    · rw [extVisibilityReplace_of_finitePart_lt h, selfVis_ofOrd_iff, finitePart_limitPart_add_nat]
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp h), selfVis_ofOrd_iff]
      exact not_lt.mp h

/-- **The orbit block is a `gTop 2`-witness** for `a` self-visible at grade one. -/
theorem witness_orbitBlock {a : ExtOrd} (ha : SelfVis 1 a) (b : ℕ) :
    Witness (gTop 2) (orbitBlock a b) where
  anti := (witness_id 2).anti
  vis := (witness_id 2).vis
  bot := orbitBlock_bot a b
  mono := by
    intro x y hxy
    rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
    · rw [orbitBlock_bot]; exact bot_le
    · rw [top_le_iff.mp hxy]
    · rcases ExtOrd.cases y with rfl | rfl | ⟨β, rfl⟩
      · exact absurd hxy (not_ofOrd_le_bot _)
      · rw [orbitBlock_top]; exact orbitBlock_le_top ha b _
      · have hαβ : α ≤ β := ofOrd_le_ofOrd.mp hxy
        by_cases h1 : α < bfloor b
        · rw [orbitBlock_of_lt a h1]; exact bot_le
        · have h1' := not_lt.mp h1
          by_cases h2 : α < bfloor (b + 1)
          · rw [orbitBlock_of_mem a h1' h2]
            by_cases h3 : β < bfloor (b + 1)
            · rw [orbitBlock_of_mem a (h1'.trans hαβ) h3]
              refine evr_mono_offset ha (min_le_min_right _ ?_)
              have eα := limitPart_add_finitePart α
              have eβ := limitPart_add_finitePart β
              rw [limitPart_of_mem_block h1' h2] at eα
              rw [limitPart_of_mem_block (h1'.trans hαβ) h3] at eβ
              have : bfloor b + (finitePart α : Ordinal) ≤ bfloor b + (finitePart β : Ordinal) := by
                rw [eα, eβ]; exact hαβ
              exact Nat.cast_le.mp ((add_le_add_iff_left _).mp this)
            · rw [orbitBlock_of_ge a (not_lt.mp h3)]
              exact evr_mono_offset ha (min_le_right _ _)
          · rw [orbitBlock_of_ge a (not_lt.mp h2), orbitBlock_of_ge a ((not_lt.mp h2).trans hαβ)]
  clause5 := by
    intro x k hx i hi
    by_cases hk : k ≤ 2
    · rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
      · rw [extVisibilityReplace_bot, orbitBlock_bot, extVisibilityReplace_bot]
      · rw [extVisibilityReplace_top, orbitBlock_top, evr_evr_of_le hk hk]
      · by_cases h1 : α < bfloor b
        · rw [orbitBlock_of_lt a h1, extVisibilityReplace_bot]
          have := extVisibilityReplace_lt_floor (limitPart_bfloor b) (ofOrd_lt_ofOrd.mpr h1) k i
          rcases ExtOrd.cases (extVisibilityReplace (ofOrd α) k i) with h | h | ⟨β, h⟩
          · rw [h, orbitBlock_bot]
          · rw [h] at this; exact absurd this not_top_lt
          · rw [h] at this ⊢; exact orbitBlock_of_lt a (ofOrd_lt_ofOrd.mp this)
        · have h1' := not_lt.mp h1
          by_cases h2 : α < bfloor (b + 1)
          · rw [orbitBlock_of_mem a h1' h2]
            by_cases hfp : finitePart α < k
            · have hmin : min (finitePart α) 2 = finitePart α := min_eq_left (by omega)
              rw [extVisibilityReplace_of_finitePart_lt hfp, limitPart_of_mem_block h1' h2,
                orbitBlock_of_mem a mem_block_add.1 mem_block_add.2, finitePart_mul_add, hmin,
                min_eq_left (by omega), evr_evr_of_lt hk hfp]
            · have hfp' := not_lt.mp hfp
              rw [extVisibilityReplace_of_le_finitePart hfp', orbitBlock_of_mem a h1' h2,
                evr_evr_of_le hk (by omega)]
          · have h2' := not_lt.mp h2
            rw [orbitBlock_of_ge a h2', evr_evr_of_le hk hk]
            have := floor_le_extVisibilityReplace (limitPart_bfloor (b + 1))
              (ofOrd_le_ofOrd.mpr h2') k i
            rcases ExtOrd.cases (extVisibilityReplace (ofOrd α) k i) with h | h | ⟨β, h⟩
            · rw [h] at this; exact absurd this (not_ofOrd_le_bot _)
            · rw [h, orbitBlock_top]
            · rw [h] at this ⊢; exact orbitBlock_of_ge a (ofOrd_le_ofOrd.mp this)
    · rw [gTop_of_gt (not_le.mp hk)] at hx
      have h0 := le_bot_iff.mp hx
      rw [h0, extVisibilityReplace_bot]
      rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
      · rw [extVisibilityReplace_bot, orbitBlock_bot]
      · rw [orbitBlock_top, evr_eq_bot_iff] at h0
        subst h0
        rw [extVisibilityReplace_top, orbitBlock_top, extVisibilityReplace_bot]
      · by_cases h1 : α < bfloor b
        · have := extVisibilityReplace_lt_floor (limitPart_bfloor b) (ofOrd_lt_ofOrd.mpr h1) k i
          rcases ExtOrd.cases (extVisibilityReplace (ofOrd α) k i) with h | h | ⟨β, h⟩
          · rw [h, orbitBlock_bot]
          · rw [h] at this; exact absurd this not_top_lt
          · rw [h] at this ⊢; exact orbitBlock_of_lt a (ofOrd_lt_ofOrd.mp this)
        · have ha0 : a = ⊥ := by
            have h1' := not_lt.mp h1
            by_cases h2 : α < bfloor (b + 1)
            · rw [orbitBlock_of_mem a h1' h2, evr_eq_bot_iff] at h0; exact h0
            · rw [orbitBlock_of_ge a (not_lt.mp h2), evr_eq_bot_iff] at h0; exact h0
          subst ha0
          rcases ExtOrd.cases (extVisibilityReplace (ofOrd α) k i) with h | h | ⟨β, h⟩
          · rw [h, orbitBlock_bot]
          · rw [h, orbitBlock_top, extVisibilityReplace_bot]
          · rw [h]
            by_cases hb1 : β < bfloor b
            · exact orbitBlock_of_lt _ hb1
            · by_cases hb2 : β < bfloor (b + 1)
              · rw [orbitBlock_of_mem _ (not_lt.mp hb1) hb2, extVisibilityReplace_bot]
              · rw [orbitBlock_of_ge _ (not_lt.mp hb2), extVisibilityReplace_bot]

end VaughtConjecture.Knight
