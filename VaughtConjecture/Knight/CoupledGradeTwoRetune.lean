/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledGradeTwoConstraints

/-! # The grade-two retuning: the visibility closure, the strip witness, and the three rules

**The visibility closure** `closeH H t = max t (min H (R₂ t))`, where `R₂` is grade-two
visibility replacement: the least upward repair of `t` whose minimum with `H` is grade-two
self-visible.  Its algebra: inflationary (`le_closeH`), bounded by `max t H` (`closeH_le`),
`min (closeH H t) H = R₂ (min t H)` (`min_closeH`), hence grade-two self-visible
(`selfVis_min_closeH`); bottom-reflecting (`closeH_eq_bot_iff`); grade-one self-visibility is
preserved (`closeH_selfVis₁`); **capped agreement** `min (closeH H t) γ = closeH (min H γ)
(min t γ)` (`min_closeH_cap`) and **legal values are fixed** (`closeH_min_eq_of_visible`).
The closure is what repairs the grade-one clamp: a grade-one label chosen by the grade-one rule
may fail to be grade-two self-visible below `H`.

**The strip witness** (`Witness.strip`): the single-block orbit shifter — `⊥` below `ω`, the
`ω`-block orbit `extVisibilityReplace m 2 (min (fp a) 2)` of a grade-one self-visible `m` on
`[ω, ω·2)`, and the constant grade-two self-visible `c` from `ω·2` on — is a faithful witness at
**every** threshold, with suppressor `gTop 2`.  The orbit strip is essential: a grade-one output
(finite part one) is not grade-two self-visible, so a constant step at threshold two would fail
clause 5; the orbit calculus `orbit_eq` is the commutation that makes clause 5 hold for all
thresholds `≤ 2`, and above grade two only bottom outputs activate the clause (the bottom fibre
is constant on each ordinal block, and replacement never crosses a limit).

**The cells of `(univ, 2)`** (`two_cases`): the six named cells and the proper cells of grades one
and two, with the rows read at each (`rows₃_E_proper_two`, `rows₃_E_s₀old`, `rows₃_E_s₀new`,
`rowX_s₀_of_proper`, `vS_of_proper'`), the face facts (`s₀old_le_H₀old_of_respects`,
`s₀new_le_H₀new_of_respects`, `proper_two_eq_bot'`), and the lower-set cases
(`below_s₀old_cases`, `below_s₀new_cases₂`).

**The three retuning rules** (`Retuned` bundles the eleven required properties: order, bottom
coupling, visibility at grades one and two, `H ≤ x₁`, grade-two visibility of `min x₀ H`, and
capped agreement in all three parameters):
* only the proper value protected (`rule_two_v`): `H' = Hq`, `x₀' = closeH Hq (max x₀q vP)`,
  `x₁' = max x₁q x₀'`;
* the old face protected (`rule_two_old`): `x₀' = x_p`, and `H' = h_p` when `h_p < x_p` (forced),
  `H' = max h_p Hq` when `h_p = x_p`, with the bottom branch when `x_p = ⊥`; the old high label
  `min x₀' H' = h_p` is preserved literally;
* the copy face protected (`rule_two_copy`): `x₁' = x_p`, `H' = h_p`,
  `x₀' = closeH h_p (max vP (min x₀q x_p))`, with the bottom fallback `x₀' = x_p`.

**The retuned labelling** `retune₂` and its values at the six cells (`retune₂_in`,
`retune₂_H₀old`, …, `retune₂_proper`).

Not done: the cash-out — `ProperToFull₃Low` at `j = 2` (the respect proof for `retune₂` over all
cells, with the strip witnesses at the three grade-two rows).  Grade three is out of scope: its
duplicate graded indices break the uniqueness argument.  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## The visibility closure below a grade-two label -/

section Closure

/-- Grade-two visibility replacement. -/
noncomputable abbrev R₂ (t : ExtOrd) : ExtOrd := extVisibilityReplace t 2 2

theorem R₂_mono : Monotone R₂ := fun _ _ h => evr_mono h le_rfl
theorem R₂_min (a b : ExtOrd) : R₂ (min a b) = min (R₂ a) (R₂ b) := R₂_mono.map_min
theorem le_R₂ (t : ExtOrd) : t ≤ R₂ t := le_extVisibilityReplace_self t 2
theorem R₂_of_selfVis {t : ExtOrd} (h : SelfVis 2 t) : R₂ t = t := h

theorem R₂_selfVis (t : ExtOrd) : SelfVis 2 (R₂ t) := by
  rcases ExtOrd.cases t with rfl | rfl | ⟨α, rfl⟩
  · exact selfVis_bot 2
  · change extVisibilityReplace (extVisibilityReplace ⊤ 2 2) 2 2 = extVisibilityReplace ⊤ 2 2
    rw [extVisibilityReplace_top, extVisibilityReplace_top]
  · change SelfVis 2 (extVisibilityReplace (ofOrd α) 2 2)
    rw [extVisibilityReplace_ofOrd, selfVis_ofOrd_iff, finitePart_visibilityReplace]
    split_ifs with h <;> omega

theorem R₂_bot : R₂ ⊥ = ⊥ := extVisibilityReplace_bot _ _

/-- **The closure**: the least upward repair of `t` whose minimum with `H` is grade-two
self-visible. -/
noncomputable def closeH (H t : ExtOrd) : ExtOrd := max t (min H (R₂ t))

theorem le_closeH (H t : ExtOrd) : t ≤ closeH H t := le_max_left _ _
theorem closeH_le (H t : ExtOrd) : closeH H t ≤ max t H :=
  max_le (le_max_left _ _) ((min_le_left _ _).trans (le_max_right _ _))

theorem min_closeH {H : ExtOrd} (hH : SelfVis 2 H) (t : ExtOrd) :
    min (closeH H t) H = R₂ (min t H) := by
  unfold closeH
  rw [min_max_distrib_right, R₂_min, R₂_of_selfVis hH, min_eq_left (min_le_left H (R₂ t)),
    min_comm H (R₂ t)]
  exact max_eq_right (min_le_min (le_R₂ t) le_rfl)

theorem selfVis_min_closeH {H : ExtOrd} (hH : SelfVis 2 H) (t : ExtOrd) :
    SelfVis 2 (min (closeH H t) H) := by
  rw [min_closeH hH]; exact R₂_selfVis _

theorem closeH_eq_bot_iff (H t : ExtOrd) : closeH H t = ⊥ ↔ t = ⊥ := by
  constructor
  · intro h; exact le_bot_iff.mp (h ▸ le_closeH H t)
  · rintro rfl; unfold closeH; rw [R₂_bot, min_eq_right bot_le, max_self]

theorem closeH_selfVis₁ {H t : ExtOrd} (ht : SelfVis 1 t) (hH : SelfVis 1 H) :
    SelfVis 1 (closeH H t) :=
  selfVis_max ht (selfVis_min' hH ((R₂_selfVis t).mono (by omega)))

/-- **Capped agreement**: the closure commutes with a grade-two self-visible cap. -/
theorem min_closeH_cap {H γ : ExtOrd} (hγ : SelfVis 2 γ) (t : ExtOrd) :
    min (closeH H t) γ = closeH (min H γ) (min t γ) := by
  unfold closeH
  rw [min_max_distrib_right, R₂_min, R₂_of_selfVis hγ]
  congr 1
  rw [min_min_min_comm, min_self]

/-- **Legal values are fixed**: when `min a H` is grade-two self-visible, the closure below the
capped `H` fixes the capped `a`. -/
theorem closeH_min_eq_of_visible {a H γ : ExtOrd} (hvis : SelfVis 2 (min a H))
    (hγ : SelfVis 2 γ) : closeH (min H γ) (min a γ) = min a γ := by
  unfold closeH
  apply max_eq_left
  rcases le_total a H with hle | hle
  · rw [min_eq_left hle] at hvis
    rw [R₂_min, R₂_of_selfVis hvis, R₂_of_selfVis hγ]; exact min_le_right _ _
  · exact (min_le_left _ _).trans (min_le_min hle le_rfl)

end Closure

/-! ## The single-block orbit shifter at threshold two -/

section Strip

/-- The finite part of a label (`0` at `⊥` and `⊤`). -/
noncomputable def fpE : ExtOrd → ℕ
  | some (some α) => finitePart α
  | _ => 0

theorem fpE_ofOrd (α : Ordinal.{0}) : fpE (ofOrd α) = finitePart α := rfl

abbrev ωn (n : ℕ) : Ordinal.{0} := Ordinal.omega0 * ((n : ℕ) : Ordinal)


/-- **The orbit calculus**: replacing the finite part of the block-`ω` value commutes with the
threshold-`k` replacement, for `k ≤ 2`. -/
theorem orbit_eq {m : ExtOrd} (hm : SelfVis 1 m) {j k i : ℕ} (hk : k ≤ 2) (hi : i ≤ k) :
    extVisibilityReplace (extVisibilityReplace m 2 (min j 2)) k i =
      extVisibilityReplace m 2 (min (if j < k then i else j) 2) := by
  rcases ExtOrd.cases m with rfl | rfl | ⟨μ, rfl⟩
  · rw [extVisibilityReplace_bot, extVisibilityReplace_bot, extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top, extVisibilityReplace_top, extVisibilityReplace_top]
  · have h1 : 1 ≤ finitePart μ := selfVis_ofOrd_iff.mp hm
    rw [extVisibilityReplace_ofOrd, extVisibilityReplace_ofOrd, extVisibilityReplace_ofOrd,
      ofOrd_inj, visReplace_eq (visibilityReplace μ 2 (min j 2)), limitPart_visibilityReplace,
      finitePart_visibilityReplace, visReplace_eq μ 2]
    congr 1
    norm_cast
    split_ifs <;> omega

theorem evr_two_one_of_selfVis₁ {m : ExtOrd} (hm : SelfVis 1 m) :
    extVisibilityReplace m 2 1 = m := by
  rcases ExtOrd.cases m with rfl | rfl | ⟨μ, rfl⟩
  · exact extVisibilityReplace_bot _ _
  · exact extVisibilityReplace_top _ _
  · have h1 : 1 ≤ finitePart μ := selfVis_ofOrd_iff.mp hm
    rw [extVisibilityReplace_ofOrd, ofOrd_inj, visReplace_eq]
    split_ifs with h
    · have : finitePart μ = 1 := by omega
      rw [← this]; exact decomposition μ
    · exact decomposition μ

theorem evr_arg_mono (m : ExtOrd) {s s' : ℕ} (h : s ≤ s') :
    extVisibilityReplace m 2 s ≤ extVisibilityReplace m 2 s' := by
  rcases ExtOrd.cases m with rfl | rfl | ⟨μ, rfl⟩
  · rw [extVisibilityReplace_bot, extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top, extVisibilityReplace_top]
  · rw [extVisibilityReplace_ofOrd, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd, visReplace_eq,
      visReplace_eq]
    split_ifs
    · exact add_le_add_right (Nat.cast_le.mpr h) _
    · exact le_rfl

open Classical in
/-- **The strip shifter**: `⊥` below `ω`, the block-`ω` orbit of `m` on `[ω, ω·2)`, the
constant `c` from `ω·2` on. -/
noncomputable def stripShifter (m c : ExtOrd) : ExtOrd → ExtOrd := fun a =>
  if a = ⊥ then ⊥ else if a < ofOrd (ωn 1) then ⊥
  else if a < ofOrd (ωn 2) then extVisibilityReplace m 2 (min (fpE a) 2) else c

theorem strip_bot (m c : ExtOrd) : stripShifter m c ⊥ = ⊥ := by
  classical
  unfold stripShifter; rw [ite_eq_left rfl]
theorem strip_of_lt_one {m c a : ExtOrd} (ha : a ≠ ⊥) (h : a < ofOrd (ωn 1)) :
    stripShifter m c a = ⊥ := by
  classical
  unfold stripShifter; rw [ite_eq_right ha, ite_eq_left h]
theorem strip_of_block {m c a : ExtOrd} (h1 : ofOrd (ωn 1) ≤ a) (h2 : a < ofOrd (ωn 2)) :
    stripShifter m c a = extVisibilityReplace m 2 (min (fpE a) 2) := by
  classical
  unfold stripShifter
  rw [ite_eq_right (fun hb => not_ofOrd_le_bot _ (hb ▸ h1)), ite_eq_right (not_lt.mpr h1),
    ite_eq_left h2]
theorem strip_of_ge {m c a : ExtOrd} (h : ofOrd (ωn 2) ≤ a) : stripShifter m c a = c := by
  classical
  unfold stripShifter
  have h1 : ofOrd (ωn 1) ≤ a := (ofOrd_le_ofOrd.mpr (by
    change Ordinal.omega0 * ((1 : ℕ) : Ordinal) ≤ Ordinal.omega0 * ((2 : ℕ) : Ordinal)
    exact mul_le_mul_right (Nat.cast_le.mpr (by decide)) _)).trans h
  rw [ite_eq_right (fun hb => not_ofOrd_le_bot _ (hb ▸ h1)), ite_eq_right (not_lt.mpr h1),
    ite_eq_right (not_lt.mpr h)]

theorem ωn_one_le_two : ofOrd (ωn 1) ≤ ofOrd (ωn 2) := ofOrd_le_ofOrd.mpr
  (mul_le_mul_right (Nat.cast_le.mpr (by decide)) _)

theorem blockIdx_eq_one {α : Ordinal.{0}} (h1 : ωn 1 ≤ α) (h2 : α < ωn 2) :
    blockIdx α = ((1 : ℕ) : Ordinal) := by
  have hb1 : ((1 : ℕ) : Ordinal) ≤ blockIdx α := by
    have := blockIdx_mono h1
    rwa [show ωn 1 = Ordinal.omega0 * ((1 : ℕ) : Ordinal) + ((0 : ℕ) : Ordinal) by
      rw [Nat.cast_zero, add_zero], blockIdx_mul_add] at this
  have hb2 : blockIdx α < ((2 : ℕ) : Ordinal) := by
    by_contra h
    rw [not_lt] at h
    have : ωn 2 ≤ limitPart α := by
      rw [limitPart_eq_mul_blockIdx]; exact mul_le_mul_right h _
    exact absurd h2 (not_lt.mpr (this.trans (limitPart_le α)))
  have hb2' : blockIdx α < ((1 : ℕ) : Ordinal) + 1 := by rw [← Nat.cast_add_one]; exact hb2
  exact le_antisymm (Order.lt_add_one_iff.mp hb2') hb1

theorem limitPart_of_block {α : Ordinal.{0}} (h1 : ωn 1 ≤ α) (h2 : α < ωn 2) :
    limitPart α = ωn 1 := by
  rw [limitPart_eq_mul_blockIdx, blockIdx_eq_one h1 h2]

theorem fp_le_of_block {α β : Ordinal.{0}} (hα1 : ωn 1 ≤ α) (hα2 : α < ωn 2) (hβ1 : ωn 1 ≤ β)
    (hβ2 : β < ωn 2) (h : α ≤ β) : finitePart α ≤ finitePart β := by
  have eα := decomposition α
  have eβ := decomposition β
  rw [limitPart_of_block hα1 hα2] at eα
  rw [limitPart_of_block hβ1 hβ2] at eβ
  rw [← eα, ← eβ] at h
  exact Nat.cast_le.mp ((add_le_add_iff_left _).mp h)

theorem strip_val_le {m c : ExtOrd} (hc : SelfVis 2 c) (hmc : m ≤ c) (j : ℕ) :
    extVisibilityReplace m 2 (min j 2) ≤ c :=
  (evr_arg_mono m (min_le_right j 2)).trans ((R₂_mono hmc).trans (R₂_of_selfVis hc).le)

theorem ofOrd_of_block {a : ExtOrd} (h1 : ofOrd (ωn 1) ≤ a) (h2 : a < ofOrd (ωn 2)) :
    ∃ α : Ordinal.{0}, a = ofOrd α ∧ ωn 1 ≤ α ∧ α < ωn 2 := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · exact absurd h1 (not_ofOrd_le_bot _)
  · exact absurd h2 (not_lt.mpr le_top)
  · exact ⟨α, rfl, ofOrd_le_ofOrd.mp h1, ofOrd_lt_ofOrd.mp h2⟩

/-- **The strip witness at threshold two**, for every threshold: `m` self-visible at one,
`c` self-visible at two, `m ≤ c`. -/
theorem Witness.strip {m c : ExtOrd} (hm : SelfVis 1 m) (hc : SelfVis 2 c) (hmc : m ≤ c) :
    Witness (gTop 2) (stripShifter m c) where
  anti := (witness_id 2).anti
  vis := (witness_id 2).vis
  bot := strip_bot m c
  mono := by
    intro a b hab
    by_cases ha : a = ⊥
    · rw [ha, strip_bot]; exact bot_le
    have hb : b ≠ ⊥ := fun hb => ha (le_bot_iff.mp (hb ▸ hab))
    by_cases ha1 : a < ofOrd (ωn 1)
    · rw [strip_of_lt_one ha ha1]; exact bot_le
    have ha1' : ofOrd (ωn 1) ≤ a := not_lt.mp ha1
    have hb1' : ofOrd (ωn 1) ≤ b := ha1'.trans hab
    by_cases ha2 : a < ofOrd (ωn 2)
    · rw [strip_of_block ha1' ha2]
      by_cases hb2 : b < ofOrd (ωn 2)
      · rw [strip_of_block hb1' hb2]
        obtain ⟨α, rfl, hα1, hα2⟩ := ofOrd_of_block ha1' ha2
        obtain ⟨β, rfl, hβ1, hβ2⟩ := ofOrd_of_block hb1' hb2
        rw [fpE_ofOrd, fpE_ofOrd]
        exact evr_arg_mono m (min_le_min (fp_le_of_block hα1 hα2 hβ1 hβ2 (ofOrd_le_ofOrd.mp hab))
          le_rfl)
      · rw [strip_of_ge (not_lt.mp hb2)]; exact strip_val_le hc hmc _
    · have ha2' : ofOrd (ωn 2) ≤ a := not_lt.mp ha2
      rw [strip_of_ge ha2', strip_of_ge (ha2'.trans hab)]
  clause5 := by
    intro α k hk i hi
    by_cases hα : α = ⊥
    · rw [hα, strip_bot, extVisibilityReplace_bot, strip_bot]
    have hα' : extVisibilityReplace α k i ≠ ⊥ := extVisibilityReplace_ne_bot hα k i
    by_cases hkK : k ≤ 2
    · by_cases h1 : α < ofOrd (ωn 1)
      · rw [strip_of_lt_one hα h1, strip_of_lt_one hα' (evr_lt_limit h1 k i),
          extVisibilityReplace_bot]
      have h1' : ofOrd (ωn 1) ≤ α := not_lt.mp h1
      by_cases h2 : α < ofOrd (ωn 2)
      · obtain ⟨a, rfl, ha1, ha2⟩ := ofOrd_of_block h1' h2
        rw [strip_of_block h1' h2, strip_of_block (evr_ge_limit h1' k i) (evr_lt_limit h2 k i),
          fpE_ofOrd, extVisibilityReplace_ofOrd, fpE_ofOrd, finitePart_visibilityReplace]
        exact (orbit_eq hm hkK hi).symm
      · have h2' : ofOrd (ωn 2) ≤ α := not_lt.mp h2
        rw [strip_of_ge h2', strip_of_ge (evr_ge_limit h2' k i),
          evr_eq_self_of_selfVis (hc.mono hkK)]
    · rw [gTop_of_gt (by omega)] at hk
      have hσ := le_bot_iff.mp hk
      by_cases h1 : α < ofOrd (ωn 1)
      · have e1 : stripShifter m c (extVisibilityReplace α k i) = ⊥ :=
          strip_of_lt_one hα' (evr_lt_limit h1 k i)
        rw [e1, strip_of_lt_one hα h1, extVisibilityReplace_bot]
      have h1' : ofOrd (ωn 1) ≤ α := not_lt.mp h1
      by_cases h2 : α < ofOrd (ωn 2)
      · rw [strip_of_block h1' h2] at hσ
        have hm0 : m = ⊥ := by
          by_contra hne
          exact extVisibilityReplace_ne_bot hne 2 _ hσ
        have e1 : stripShifter m c (extVisibilityReplace α k i) =
            extVisibilityReplace m 2 (min (fpE (extVisibilityReplace α k i)) 2) :=
          strip_of_block (evr_ge_limit h1' k i) (evr_lt_limit h2 k i)
        rw [e1, strip_of_block h1' h2, hm0]
        simp only [extVisibilityReplace_bot]
      · have h2' : ofOrd (ωn 2) ≤ α := not_lt.mp h2
        rw [strip_of_ge h2'] at hσ
        have e1 : stripShifter m c (extVisibilityReplace α k i) = c :=
          strip_of_ge (evr_ge_limit h2' k i)
        rw [e1, strip_of_ge h2', hσ, extVisibilityReplace_bot]

/-! ### The strip at the sources -/

theorem strip_v₀ {m c : ExtOrd} (hm : SelfVis 1 m) : stripShifter m c v₀ = m := by
  rw [v₀_num, strip_of_block (ofOrd_le_ofOrd.mpr le_self_add)
    (ofOrd_lt_ofOrd.mpr (lt_of_lt_of_eq (ω1j_lt_ω2 1 0) ω2_zero)), fpE_ofOrd, fp_ω1j]
  exact evr_two_one_of_selfVis₁ hm
theorem strip_ω2 {m c : ExtOrd} (j : ℕ) : stripShifter m c (ofOrd (ω2 j)) = c :=
  strip_of_ge (ofOrd_le_ofOrd.mpr le_self_add)

end Strip


/-! ## Stage B: the cells of `(univ, 2)`, the rows, the inputs -/

section Cells

theorem two_cases {d : Cell D₂} (hd : ¬ mute₂ d) (hg : D₂.grade d ≤ 2) :
    d = H₀old ∨ d = H₀new ∨ d = U_H ∨ d = s₀old ∨ d = s₀new ∨ d = U_S ∨
    (IsProper d ∧ D₂.grade d = 1) ∨ (IsProper d ∧ D₂.grade d = 2) := by
  rcases vS_cases d hd hg with h | h | ⟨h1, h2⟩ | ⟨c, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases h1 with h1 | h1
    · rcases ret_H₀_cases hd h1 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · rcases ret_s₀_cases hd h1 with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · have hg1 := D₂.grade_pos d
    have hg2 : D₂.grade d = c.gradeP := (gradeP_le_of_proper hd hc).symm
    have := c.gradeP_le_two
    by_cases h1 : D₂.grade d = 1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨c, hc⟩, h1⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨c, hc⟩, by omega⟩))))))

theorem scope_s₀old : D₂.scope s₀old = {0, 1, 2} := by
  change (D₂.cell s₀old).1 = _; unfold s₀old; rw [cell_castAdd_X]; decide
theorem zero_mem_scope_s₀old : (0 : Fin 4) ∈ D₂.scope s₀old := by rw [scope_s₀old]; decide
theorem three_not_mem_scope_s₀old : (3 : Fin 4) ∉ D₂.scope s₀old := by rw [scope_s₀old]; decide
theorem three_not_mem_scope_H₀old' : (3 : Fin 4) ∉ D₂.scope H₀old := three_not_mem_scope_castAdd _
theorem three_mem_scope_H₀new : (3 : Fin 4) ∈ D₂.scope H₀new := by rw [scope_H₀new]; decide
theorem three_mem_scope_s₀new : (3 : Fin 4) ∈ D₂.scope s₀new := by rw [scope_s₀new]; decide
theorem three_mem_scope_U_H : (3 : Fin 4) ∈ D₂.scope U_H := by
  change (3 : Fin 4) ∈ (D₂.cell U_H).1; rw [cell_U_H]; exact Finset.mem_univ _
theorem three_mem_scope_U_S : (3 : Fin 4) ∈ D₂.scope U_S := by
  change (3 : Fin 4) ∈ (D₂.cell U_S).1; rw [cell_U_S]; exact Finset.mem_univ _
theorem zero_mem_scope_U_H : (0 : Fin 4) ∈ D₂.scope U_H := by
  change (0 : Fin 4) ∈ (D₂.cell U_H).1; rw [cell_U_H]; exact Finset.mem_univ _
theorem zero_mem_scope_U_S : (0 : Fin 4) ∈ D₂.scope U_S := by
  change (0 : Fin 4) ∈ (D₂.cell U_S).1; rw [cell_U_S]; exact Finset.mem_univ _
theorem zero_not_mem_scope_s₀new : (0 : Fin 4) ∉ D₂.scope s₀new := by rw [scope_s₀new]; decide

/-- Below the old level-two witness: the two old witnesses or a proper cell. -/
theorem below_s₀old_cases (d : D₂.below (D₂.cell s₀old)) :
    d.1 = H₀old ∨ d.1 = s₀old ∨ IsProper d.1 := by
  have hd : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_s₀old d.2
  have hsub : D₂.scope d.1 ⊆ D₂.scope s₀old := d.2.1
  rcases two_cases hd (d.2.2.trans grade_s₀old.le) with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact absurd (hsub (h ▸ three_mem_scope_H₀new)) three_not_mem_scope_s₀old
  · exact absurd (hsub (h ▸ three_mem_scope_U_H)) three_not_mem_scope_s₀old
  · exact Or.inr (Or.inl h)
  · exact absurd (hsub (h ▸ three_mem_scope_s₀new)) three_not_mem_scope_s₀old
  · exact absurd (hsub (h ▸ three_mem_scope_U_S)) three_not_mem_scope_s₀old
  · exact Or.inr (Or.inr h.1)
  · exact Or.inr (Or.inr h.1)

/-- Below the copy of the level-two witness: the two copies or a proper cell. -/
theorem below_s₀new_cases₂ (d : D₂.below (D₂.cell s₀new)) :
    d.1 = H₀new ∨ d.1 = s₀new ∨ IsProper d.1 := by
  rcases below_s₀new_cases d with h | h | ⟨c, hc⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨c, hc⟩)

theorem not_mute_of_two (d : D₂.below (Finset.univ, 2)) : ¬ mute₂ d.1 :=
  not_mute₂_of_low (by decide) d

/-! ### The rows at the grade-two cells -/

theorem rows₃_E_proper_two {Sig : Cell D₂} (hSig : IsProper Sig) (hg : D₂.grade Sig = 2)
    (d : D₂.below (D₂.cell Sig)) : rows₃.E Sig d = ⊥ := by
  obtain ⟨c, hc⟩ := hSig
  have hnm : ¬ mute₂ Sig := fun hm => by
    change D₂.cell Sig = _ at hm; have := congrArg Prod.snd hm; change D₂.grade Sig = 4 at this
    omega
  refine (E₃_of_proper hc _).trans ((rows₂_E_eq_pull hnm _).trans ?_)
  rw [hc]
  rw [pull_of_not_mute _ (hmute_below₂ Sig d.1 hnm d.2)]
  change (if c.gradeP ≤ 1 then family₂.v else ⊥) = ⊥
  rw [ite_eq_right (by rw [gradeP_le_of_proper hnm hc, hg]; decide)]

/-- The pulled-back level-two row at a proper cell. -/
theorem rowX_s₀_proper {c : Prop3} :
    family₂.rowX s₀X (.inl c) = if c.gradeP ≤ 1 then v₀ else ⊥ := by
  rw [rowX_s₀_inl]
  by_cases hc : c.gradeP ≤ 1
  · rw [ite_eq_left hc]; exact s₀c_F_v₀ hc
  · rw [ite_eq_right hc]; exact s₀c_F_bot (by have := c.gradeP_le_two; omega)

theorem rows₃_E_s₀old (d : D₂.below (D₂.cell s₀old)) :
    rows₃.E s₀old d = family₂.rowX s₀X (family₂.e.symm (ret₂ d.1)) := by
  have hA : AFace s₀old := aFace_castAdd _
  rw [E₃_of_A hA, rows₂_E_eq_pull not_mute_s₀old, ret₂_s₀old, Equiv.symm_apply_apply,
    pull_of_not_mute _ (hmute_below₂ _ d.1 not_mute_s₀old d.2)]
theorem not_mute_s₀new : ¬ mute₂ s₀new := not_mute_copyB _
theorem rows₃_E_s₀new (d : D₂.below (D₂.cell s₀new)) :
    rows₃.E s₀new d = family₂.rowX s₀X (family₂.e.symm (ret₂ d.1)) := by
  rw [E₃_of_B bFace_s₀new, rows₂_E_eq_pull not_mute_s₀new, ret₂_s₀new, Equiv.symm_apply_apply,
    pull_of_not_mute _ (hmute_below₂ _ d.1 not_mute_s₀new d.2)]

/-- A proper cell's row value in a pulled-back level-two row, by its grade. -/
theorem rowX_s₀_of_proper {d : Cell D₂} (hd : ¬ mute₂ d) (hp : IsProper d) :
    family₂.rowX s₀X (family₂.e.symm (ret₂ d)) = if D₂.grade d ≤ 1 then v₀ else ⊥ := by
  obtain ⟨c, hc⟩ := hp
  rw [hc, rowX_s₀_proper, gradeP_le_of_proper hd hc]

theorem rowX_H₀_of_proper {d : Cell D₂} (hd : ¬ mute₂ d) (hp : IsProper d)
    (hg : D₂.grade d ≤ 1) : family₂.rowX H₀X (family₂.e.symm (ret₂ d)) = v₀ := by
  obtain ⟨c, hc⟩ := hp
  have hc1 : c.gradeP ≤ 1 := by rw [gradeP_le_of_proper hd hc]; exact hg
  rw [hc, family₂.rowX_H_inl _ c hc1]; exact H₀c_G_v₀ hc1

theorem vS_of_proper' {d : Cell D₂} (hd : ¬ mute₂ d) (hp : IsProper d) :
    vS d = if D₂.grade d ≤ 1 then v₀ else ⊥ := by
  obtain ⟨c, hc⟩ := hp
  rw [vS_of_proper hd hc]
  by_cases h1 : c.gradeP ≤ 1
  · rw [s₀c_F_v₀ h1, ite_eq_left (by rw [← gradeP_le_of_proper hd hc]; exact h1)]
  · rw [s₀c_F_bot (by have := c.gradeP_le_two; omega),
      ite_eq_right (by rw [← gradeP_le_of_proper hd hc]; exact h1)]

end Cells

/-! ### Facts about respecting labellings at grade two -/

section Inputs

theorem h₁₂ : GradedLe ((Finset.univ : Finset (Fin 4)), 1) (Finset.univ, 2) :=
  ⟨Finset.Subset.refl _, by decide⟩

/-- Grade-two proper cells are labelled `⊥` under any respecting labelling. -/
theorem proper_two_eq_bot' {BJ : Finset (Fin 4) × ℕ} {r : D₂.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow rows₃ BJ r) (d : D₂.below BJ) (hd : IsProper d.1)
    (hg : D₂.grade d.1 = 2) : r d = ⊥ := by
  obtain ⟨g, σ, hw, heq⟩ := TransformsTo.witness (hr.locality d)
  have h := heq ⟨d.1, GradedLe.refl _⟩
  have e : CellScheme.below.incl d ⟨d.1, GradedLe.refl _⟩ = d := Subtype.ext rfl
  rw [e, min_self, rows₃_E_proper_two hd hg ⟨d.1, GradedLe.refl _⟩, hw.bot] at h
  rw [h]; exact min_eq_left bot_le

/-- The old level-two witness of a protected old face is at most its level-one witness. -/
theorem s₀old_le_H₀old_of_respects {BJ : Finset (Fin 4) × ℕ} {r : D₂.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow rows₃ BJ r) (hs : GradedLe (D₂.cell s₀old) BJ)
    (hH : GradedLe (D₂.cell H₀old) BJ) : r ⟨s₀old, hs⟩ ≤ r ⟨H₀old, hH⟩ := by
  have hHs : GradedLe (D₂.cell H₀old) (D₂.cell s₀old) :=
    ⟨by change D₂.scope H₀old ⊆ D₂.scope s₀old; rw [scope_s₀old]; exact scope_castAdd_sub _,
     by change D₂.grade H₀old ≤ D₂.grade s₀old; rw [grade_H₀old, grade_s₀old]; decide⟩
  have h := hr.probe_ge_of_row_eq ⟨s₀old, hs⟩ ⟨H₀old, hHs⟩ ⟨s₀old, GradedLe.refl _⟩ (by
      change rows₃.E s₀old ⟨H₀old, hHs⟩ = rows₃.E s₀old ⟨s₀old, GradedLe.refl _⟩
      rw [rows₃_E_s₀old ⟨H₀old, hHs⟩, rows₃_E_s₀old ⟨s₀old, GradedLe.refl _⟩]
      change family₂.rowX s₀X (family₂.e.symm (ret₂ H₀old)) =
        family₂.rowX s₀X (family₂.e.symm (ret₂ s₀old))
      rw [ret₂_H₀old, ret₂_s₀old, Equiv.symm_apply_apply, Equiv.symm_apply_apply, rowX_s₀_H,
        rowX_s₀_s])
    (by rw [grade_H₀old, grade_s₀old]; decide)
  have e1 : CellScheme.below.incl ⟨s₀old, hs⟩ ⟨H₀old, hHs⟩ = ⟨H₀old, hH⟩ := Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨s₀old, hs⟩ ⟨s₀old, GradedLe.refl _⟩ = ⟨s₀old, hs⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.trans (min_le_left _ _)

theorem s₀new_le_H₀new_of_respects {BJ : Finset (Fin 4) × ℕ} {r : D₂.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow rows₃ BJ r) (hs : GradedLe (D₂.cell s₀new) BJ)
    (hH : GradedLe (D₂.cell H₀new) BJ) : r ⟨s₀new, hs⟩ ≤ r ⟨H₀new, hH⟩ := by
  have hHs : GradedLe (D₂.cell H₀new) (D₂.cell s₀new) :=
    ⟨by change D₂.scope H₀new ⊆ D₂.scope s₀new; rw [scope_H₀new, scope_s₀new],
     by change D₂.grade H₀new ≤ D₂.grade s₀new; rw [grade_H₀new, grade_s₀new]; decide⟩
  have h := hr.probe_ge_of_row_eq ⟨s₀new, hs⟩ ⟨H₀new, hHs⟩ ⟨s₀new, GradedLe.refl _⟩ (by
      change rows₃.E s₀new ⟨H₀new, hHs⟩ = rows₃.E s₀new ⟨s₀new, GradedLe.refl _⟩
      rw [rows₃_E_s₀new ⟨H₀new, hHs⟩, rows₃_E_s₀new ⟨s₀new, GradedLe.refl _⟩]
      change family₂.rowX s₀X (family₂.e.symm (ret₂ H₀new)) =
        family₂.rowX s₀X (family₂.e.symm (ret₂ s₀new))
      rw [ret₂_H₀new, ret₂_s₀new, Equiv.symm_apply_apply, Equiv.symm_apply_apply, rowX_s₀_H,
        rowX_s₀_s])
    (by rw [grade_H₀new, grade_s₀new]; decide)
  have e1 : CellScheme.below.incl ⟨s₀new, hs⟩ ⟨H₀new, hHs⟩ = ⟨H₀new, hH⟩ := Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨s₀new, hs⟩ ⟨s₀new, GradedLe.refl _⟩ = ⟨s₀new, hs⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.trans (min_le_left _ _)

end Inputs


/-! ## Stage C1: the three retuning rules -/

section Rules

/-- The properties a retuned grade-two parameter set must have. -/
structure Retuned (vP x₀q x₁q Hq γ : ExtOrd) (x₀' x₁' H' : ExtOrd) : Prop where
  vle : vP ≤ x₀'
  le01 : x₀' ≤ x₁'
  coup : x₀' = ⊥ → x₁' = ⊥
  vis0 : SelfVis 1 x₀'
  vis1 : SelfVis 1 x₁'
  visH : SelfVis 2 H'
  Hle : H' ≤ x₁'
  vismin : SelfVis 2 (min x₀' H')
  ag0 : min x₀' γ = min x₀q γ
  ag1 : min x₁' γ = min x₁q γ
  agH : min H' γ = min Hq γ

theorem Retuned.min_bot {vP x₀q x₁q Hq γ x₀' x₁' H' : ExtOrd}
    (R : Retuned vP x₀q x₁q Hq γ x₀' x₁' H') (h : min x₀' H' = ⊥) : H' = ⊥ := by
  rcases min_eq_bot.mp h with h0 | h0
  · exact le_bot_iff.mp (R.Hle.trans (R.coup h0).le)
  · exact h0

theorem min_min_cap (a b γ : ExtOrd) : min (min a b) γ = min (min a γ) (min b γ) := by
  rw [← min_min_min_comm, min_self]

theorem Retuned.agmin {vP x₀q x₁q Hq γ x₀' x₁' H' : ExtOrd}
    (R : Retuned vP x₀q x₁q Hq γ x₀' x₁' H') :
    min (min x₀' H') γ = min (min x₀q Hq) γ := by
  rw [min_min_cap, R.ag0, R.agH, ← min_min_cap]

/-- **Only the proper value protected.** -/
theorem rule_two_v {vP vq x₀q x₁q Hq γ : ExtOrd} (hvP : SelfVis 1 vP) (hx₀ : SelfVis 1 x₀q)
    (hx₁ : SelfVis 1 x₁q) (hH : SelfVis 2 Hq) (hvq0 : vq ≤ x₀q) (h01 : x₀q ≤ x₁q)
    (hcoup : x₀q = ⊥ → x₁q = ⊥) (hHle : Hq ≤ x₁q) (hmin : SelfVis 2 (min x₀q Hq))
    (hγ : SelfVis 2 γ) (hag : min vq γ = min vP γ) :
    ∃ x₀' x₁' H' : ExtOrd, Retuned vP x₀q x₁q Hq γ x₀' x₁' H' := by
  refine ⟨closeH Hq (max x₀q vP), max x₁q (closeH Hq (max x₀q vP)), Hq, ?_⟩
  have hu : SelfVis 1 (max x₀q vP) := selfVis_max hx₀ hvP
  have hagu : min (max x₀q vP) γ = min x₀q γ := by
    rw [min_max_distrib_right, ← hag, max_eq_left (min_le_min hvq0 le_rfl)]
  refine ⟨(le_max_right _ _).trans (le_closeH _ _), le_max_right _ _, ?_,
    closeH_selfVis₁ hu (hH.mono (by omega)),
    selfVis_max hx₁ (closeH_selfVis₁ hu (hH.mono (by omega))), hH,
    hHle.trans (le_max_left _ _), selfVis_min_closeH hH _, ?_, ?_, rfl⟩
  · intro h0
    have h1 := (closeH_eq_bot_iff _ _).mp h0
    have h2 : x₀q = ⊥ := le_bot_iff.mp (h1 ▸ le_max_left x₀q vP)
    rw [hcoup h2, h0, max_self]
  · rw [min_closeH_cap hγ, hagu, closeH_min_eq_of_visible hmin hγ]
  · rw [min_max_distrib_right, min_closeH_cap hγ, hagu, closeH_min_eq_of_visible hmin hγ,
      max_eq_left (min_le_min h01 le_rfl)]

/-- **The old face protected.** -/
theorem rule_two_old {vP x₀q x₁q Hq γ x_p h_p : ExtOrd} (hx₁ : SelfVis 1 x₁q)
    (hH : SelfVis 2 Hq) (h01 : x₀q ≤ x₁q) (hcoup : x₀q = ⊥ → x₁q = ⊥) (hHle : Hq ≤ x₁q)
    (hHbot : min x₀q Hq = ⊥ → Hq = ⊥) (hxp : SelfVis 1 x_p) (hhp : SelfVis 2 h_p)
    (hvxp : vP ≤ x_p) (hhx : h_p ≤ x_p) (hagx : min x₀q γ = min x_p γ)
    (hagh : min (min x₀q Hq) γ = min h_p γ) :
    ∃ x₀' x₁' H' : ExtOrd, Retuned vP x₀q x₁q Hq γ x₀' x₁' H' ∧ x₀' = x_p ∧ min x₀' H' = h_p := by
  by_cases hb : x_p = ⊥
  · have hhb : h_p = ⊥ := le_bot_iff.mp (hb ▸ hhx)
    have hx0 : min x₀q γ = ⊥ := by rw [hagx, hb, min_eq_left bot_le]
    refine ⟨⊥, ⊥, ⊥, ⟨hb ▸ hvxp, le_rfl, fun _ => rfl, selfVis_bot 1, selfVis_bot 1,
      selfVis_bot 2, le_rfl, by rw [min_self]; exact selfVis_bot 2, ?_, ?_, ?_⟩, hb.symm,
      by rw [min_self, hhb]⟩
    · rw [min_eq_left bot_le, hx0]
    · rw [min_eq_left bot_le]
      rcases min_eq_bot.mp hx0 with h0 | h0
      · rw [hcoup h0, min_eq_left bot_le]
      · rw [h0, min_eq_right bot_le]
    · rw [min_eq_left bot_le]
      rcases min_eq_bot.mp hx0 with h0 | h0
      · rw [hHbot (by rw [h0, min_eq_left bot_le]), min_eq_left bot_le]
      · rw [h0, min_eq_right bot_le]
  · have hag1 : min (max x₁q x_p) γ = min x₁q γ := by
      rw [min_max_distrib_right, ← hagx, max_eq_left (min_le_min h01 le_rfl)]
    by_cases hlt : h_p < x_p
    · -- the strict branch: `H' = h_p` is forced
      refine ⟨x_p, max x₁q x_p, h_p, ⟨hvxp, le_max_right _ _, fun h => absurd h hb, hxp,
        selfVis_max hx₁ hxp, hhp, hhx.trans (le_max_right _ _), by rw [min_eq_right hhx]; exact hhp,
        hagx.symm, hag1, ?_⟩, rfl, min_eq_right hhx⟩
      -- min h_p γ = min Hq γ
      have hagh' : min (min x₀q γ) (min Hq γ) = min h_p γ := by rw [← min_min_cap]; exact hagh
      rcases le_total (min Hq γ) (min x₀q γ) with hBA | hAB
      · rw [min_eq_right hBA] at hagh'
        exact hagh'.symm
      · rw [min_eq_left hAB] at hagh'
        -- `min x₀q γ = min h_p γ` with `h_p < x_p` forces `γ ≤ h_p`
        rcases lt_or_ge h_p γ with hhγ | hγh
        · exfalso
          rw [min_eq_left hhγ.le, hagx] at hagh'
          exact absurd hagh' (ne_of_gt (lt_min hlt hhγ))
        · rw [min_eq_right hγh]
          apply le_antisymm
          · calc γ = min h_p γ := (min_eq_right hγh).symm
              _ = min x₀q γ := hagh'.symm
              _ ≤ min Hq γ := hAB
          · exact min_le_right _ _
    · have hxe : h_p = x_p := le_antisymm hhx (not_lt.mp hlt)
      have hagh' : min (min x₀q γ) (min Hq γ) = min h_p γ := by rw [← min_min_cap]; exact hagh
      have hAB : min x₀q γ ≤ min Hq γ := by
        rw [← min_eq_left_iff, hagh', hxe, ← hagx]
      refine ⟨x_p, max x₁q x_p, max h_p Hq, ⟨hvxp, le_max_right _ _, fun h => absurd h hb, hxp,
        selfVis_max hx₁ hxp, selfVis_max hhp hH, max_le (hhx.trans (le_max_right _ _))
          (hHle.trans (le_max_left _ _)), ?_, hagx.symm, hag1, ?_⟩, rfl, ?_⟩
      · rw [min_eq_left (hxe ▸ le_max_left h_p Hq)]; exact hxe ▸ hhp
      · rw [min_max_distrib_right, hxe, ← hagx, max_eq_right hAB]
      · rw [min_eq_left (hxe ▸ le_max_left h_p Hq)]; exact hxe.symm

/-- **The copy face protected.** -/
theorem rule_two_copy {vP vq x₀q x₁q Hq γ x_p h_p : ExtOrd} (hvP : SelfVis 1 vP)
    (hx₀ : SelfVis 1 x₀q) (hvq0 : vq ≤ x₀q) (h01 : x₀q ≤ x₁q)
    (hcoup : x₀q = ⊥ → x₁q = ⊥) (hmin : SelfVis 2 (min x₀q Hq)) (hγ : SelfVis 2 γ)
    (hag : min vq γ = min vP γ) (hxp : SelfVis 1 x_p) (hhp : SelfVis 2 h_p)
    (hvxp : vP ≤ x_p) (hhx : h_p ≤ x_p) (hagx : min x₁q γ = min x_p γ)
    (hagh : min Hq γ = min h_p γ) :
    ∃ x₀' x₁' H' : ExtOrd, Retuned vP x₀q x₁q Hq γ x₀' x₁' H' ∧ x₁' = x_p ∧ H' = h_p := by
  set t := max vP (min x₀q x_p) with ht
  have htle : t ≤ x_p := max_le hvxp (min_le_right _ _)
  have htvis : SelfVis 1 t := selfVis_max hvP (selfVis_min' hx₀ hxp)
  have hagt : min t γ = min x₀q γ := by
    rw [ht, min_max_distrib_right, ← hag, min_assoc, ← hagx, ← min_assoc, min_eq_left h01,
      max_eq_right (min_le_min hvq0 le_rfl)]
  by_cases hb : t = ⊥
  · -- the bottom fallback
    have hvb : vP = ⊥ := le_bot_iff.mp (hb ▸ le_max_left vP (min x₀q x_p))
    have hagx0 : min x_p γ = min x₀q γ := by
      have h1 : min x₀q x_p = ⊥ := le_bot_iff.mp (hb ▸ le_max_right vP (min x₀q x_p))
      rcases min_eq_bot.mp h1 with h0 | h0
      · have h2 : min x₁q γ = ⊥ := by rw [hcoup h0, min_eq_left bot_le]
        rw [hagx] at h2
        rw [h2, h0, min_eq_left bot_le]
      · rw [h0, min_eq_left bot_le]
        exact ((min_le_min h01 le_rfl).trans (by rw [hagx, h0, min_eq_left bot_le])
          |> le_bot_iff.mp).symm
    refine ⟨x_p, x_p, h_p, ⟨hvxp, le_rfl, fun h => h, hxp, hxp, hhp, hhx,
      by rw [min_eq_right hhx]; exact hhp, hagx0, hagx.symm, hagh.symm⟩, rfl, rfl⟩
  · refine ⟨closeH h_p t, x_p, h_p, ⟨(le_max_left _ _).trans (le_closeH _ _),
      (closeH_le _ _).trans (max_le htle hhx), fun h => absurd ((closeH_eq_bot_iff _ _).mp h) hb,
      closeH_selfVis₁ htvis (hhp.mono (by omega)), hxp, hhp, hhx, selfVis_min_closeH hhp _, ?_,
      hagx.symm, hagh.symm⟩, rfl, rfl⟩
    rw [min_closeH_cap hγ, hagt, ← hagh, closeH_min_eq_of_visible hmin hγ]

end Rules


/-! ## Stage C2: the retuned labelling and the grade-two obligation -/

section RetuneTwo

open Classical in
/-- **The retuned labelling at grade two.** -/
noncomputable def retune₂ (C : Finset (Fin 4)) (p : D₂.below (C, 2) → ExtOrd)
    (x₀' x₁' H' vP : ExtOrd) (d : D₂.below (Finset.univ, 2)) : ExtOrd :=
  if hd : GradedLe (D₂.cell d.1) (C, 2) then p ⟨d.1, hd⟩
  else if d.1 = H₀old then x₀' else if d.1 = H₀new ∨ d.1 = U_H then x₁'
  else if d.1 = s₀old then min x₀' H' else if d.1 = s₀new ∨ d.1 = U_S then H'
  else if D₂.grade d.1 = 2 then ⊥ else vP

variable {C : Finset (Fin 4)} {p : D₂.below (C, 2) → ExtOrd} {x₀' x₁' H' vP : ExtOrd}

theorem retune₂_in (d : D₂.below (Finset.univ, 2)) (hd : GradedLe (D₂.cell d.1) (C, 2)) :
    retune₂ C p x₀' x₁' H' vP d = p ⟨d.1, hd⟩ := by
  classical
  unfold retune₂; rw [dite_of_pos hd]
theorem retune₂_H₀old (hA : ¬ GradedLe (D₂.cell H₀old) (C, 2)) :
    retune₂ C p x₀' x₁' H' vP ⟨H₀old, memH₀old₂⟩ = x₀' := by
  classical
  unfold retune₂; rw [dite_of_neg hA, ite_eq_left rfl]
theorem retune₂_H₀new (hB : ¬ GradedLe (D₂.cell H₀new) (C, 2)) :
    retune₂ C p x₀' x₁' H' vP ⟨H₀new, memH₀new₂⟩ = x₁' := by
  classical
  unfold retune₂; rw [dite_of_neg hB, ite_eq_right H₀old_ne_H₀new.symm, ite_eq_left (Or.inl rfl)]
theorem retune₂_U_H (hU : ¬ GradedLe (D₂.cell U_H) (C, 2)) :
    retune₂ C p x₀' x₁' H' vP ⟨U_H, memU_H₂⟩ = x₁' := by
  classical
  unfold retune₂; rw [dite_of_neg hU, ite_eq_right H₀old_ne_U_H.symm, ite_eq_left (Or.inr rfl)]
theorem s₀old_ne_U_H : s₀old ≠ U_H := castAdd_ne_fullCell _ H₀X rfl
theorem s₀new_ne_H₀old : s₀new ≠ H₀old := fun h => H₀old_ne_s₀new h.symm
theorem s₀new_ne_H₀new : s₀new ≠ H₀new :=
  ne_of_ret_ne (by rw [ret₂_s₀new, ret₂_H₀new]; exact ret_s₀_ne_H₀)
theorem s₀new_ne_U_H : s₀new ≠ U_H :=
  ne_of_ret_ne (by rw [ret₂_s₀new, ret₂_U_H]; exact ret_s₀_ne_H₀)
theorem s₀new_ne_s₀old : s₀new ≠ s₀old := fun h => s₀old_ne_s₀new h.symm
theorem U_S_ne_H₀old : U_S ≠ H₀old := fun h => H₀old_ne_U_S h.symm
theorem U_S_ne_H₀new : U_S ≠ H₀new :=
  ne_of_ret_ne (by rw [ret₂_U_S, ret₂_H₀new]; exact ret_s₀_ne_H₀)
theorem U_S_ne_s₀old : U_S ≠ s₀old := fun h => s₀old_ne_U_S h.symm
theorem s₀old_ne_H₀new : s₀old ≠ H₀new := fun h =>
  three_not_mem_scope_s₀old (h ▸ three_mem_scope_H₀new)

theorem retune₂_s₀old (hs : ¬ GradedLe (D₂.cell s₀old) (C, 2)) :
    retune₂ C p x₀' x₁' H' vP ⟨s₀old, mems₀old₂⟩ = min x₀' H' := by
  classical
  have h2 : ¬ (s₀old = H₀new ∨ s₀old = U_H) := by
    rintro (h | h)
    · exact s₀old_ne_H₀new h
    · exact s₀old_ne_U_H h
  unfold retune₂
  rw [dite_of_neg hs, ite_eq_right s₀old_ne_H₀old, ite_eq_right h2, ite_eq_left rfl]
theorem retune₂_s₀new (hs : ¬ GradedLe (D₂.cell s₀new) (C, 2)) :
    retune₂ C p x₀' x₁' H' vP ⟨s₀new, mems₀new₂⟩ = H' := by
  classical
  have h2 : ¬ (s₀new = H₀new ∨ s₀new = U_H) := by
    rintro (h | h)
    · exact s₀new_ne_H₀new h
    · exact s₀new_ne_U_H h
  unfold retune₂
  rw [dite_of_neg hs, ite_eq_right s₀new_ne_H₀old, ite_eq_right h2,
    ite_eq_right s₀new_ne_s₀old, ite_eq_left (Or.inl rfl)]
theorem retune₂_U_S (hU : ¬ GradedLe (D₂.cell U_S) (C, 2)) :
    retune₂ C p x₀' x₁' H' vP ⟨U_S, memU₂⟩ = H' := by
  classical
  have h2 : ¬ (U_S = H₀new ∨ U_S = U_H) := by
    rintro (h | h)
    · exact U_S_ne_H₀new h
    · exact U_S_ne_U_H h
  unfold retune₂
  rw [dite_of_neg hU, ite_eq_right U_S_ne_H₀old, ite_eq_right h2, ite_eq_right U_S_ne_s₀old,
    ite_eq_left (Or.inr rfl)]
theorem retune₂_proper (d : D₂.below (Finset.univ, 2)) (hd : IsProper d.1)
    (hdC : ¬ GradedLe (D₂.cell d.1) (C, 2)) :
    retune₂ C p x₀' x₁' H' vP d = if D₂.grade d.1 = 2 then ⊥ else vP := by
  classical
  have h1 : ¬ d.1 = H₀old := fun e => not_isProper_of_ret rfl ret₂_H₀old (e ▸ hd)
  have h2 : ¬ (d.1 = H₀new ∨ d.1 = U_H) := by
    rintro (e | e)
    · exact not_isProper_of_ret rfl ret₂_H₀new (e ▸ hd)
    · exact not_isProper_of_ret rfl ret₂_U_H (e ▸ hd)
  have h3 : ¬ d.1 = s₀old := fun e => not_isProper_of_ret rfl ret₂_s₀old (e ▸ hd)
  have h4 : ¬ (d.1 = s₀new ∨ d.1 = U_S) := by
    rintro (e | e)
    · exact not_isProper_of_ret rfl ret₂_s₀new (e ▸ hd)
    · exact not_isProper_of_ret rfl ret₂_U_S (e ▸ hd)
  unfold retune₂
  rw [dite_of_neg hdC, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]

end RetuneTwo


end VaughtConjecture.Knight
