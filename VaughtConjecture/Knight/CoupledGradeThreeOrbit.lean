/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledGradeThreeConstraints

/-! # Grade three: the moving source orbit, and the audit of the source orbits

**The generic law** (`orbit_bounds_probe`, after the research scout `orbit_bounds_controller`):
in a row transformed onto the probes `min (value e) (value c)` of a controller `c`, if the
source at `e` is the replacement `(grade c, grade c)` of the source at `d` (`grade d ≤ grade c`),
then `min (value e) (value c) ≤ R (value d)` with `R` that replacement.  When `value d < value c`
the row equation at `d` is uncapped, `σ (source d) = value d ≤ g (grade c)` (`shifter_eq_of_lt`),
so clause 5 is active at the controller's grade; otherwise inflationarity of replacement gives
the bound outright.  The same activation fixes the label at `d` under every index-`i` replacement
that fixes its source (`orbit_fixes_label`).

**The actual orbit** (`A₁c_le_R₃_of_respects`, the research scout's `actual_A₁c_bound`): the
proper source `ω+1` is replaced by `a₁`'s controller's diagonal `ω+3` at threshold three
(`v₀_orbit_three`), so `z₁ = q A₁c ≤ R₃ v` for every proper grade-one label `v` — a constraint
coupling `z₁` to the proper label that order and visibility do not give (`v = 2`, all upper labels
`ω+3` passes every constraint of `CoupledGradeThreeConstraints` and fails this one, `R₃ 2 = 3`).
The same orbit in `b₁`'s controller's row bounds the same label (`A₁c_le_R₃_of_respects'`), and
in `a₂`'s controller's row likewise.  **The sharp form** (`A₁c_eq_R₃_of_lt`, through the index-one
replacement `v₀_orbit_three_one` and the ordinal law `eq_R₃_of_orbit`): if `v < z₁` then
`z₁ = R₃ v` exactly, and `v` has finite part one.  So either `z₁ ≤ v`, or `v = ω·b+1` and
`z₁ = ω·b+3`.

**The audit of the source orbits** (the clause-5 pairs `(α, k, i)`, `α` a row value, `k` the
controller's grade, `i ≤ k`, with the row values of the frozen rows).  Grade-three rows read
`⊥`, `ω+1`, `ω+3`, `ω+4`, `ω·2+3`; at threshold three, `ω+3`, `ω+4`, `ω·2+3` and `⊥` are fixed,
`ω+1 ↦ ω+3` at index three is the orbit above, `ω+1 ↦ ω+1` at index one is the fixing law, and
`ω+1 ↦ ω, ω+2` at indices zero and two land on non-sources (they constrain the shifter off the
row only).  At thresholds one and two every row value is fixed or lands on a non-source
(`ω+1 ↦ ω+2`).  At threshold four (above the controller's grade) the clause is active only where
`σ α ≤ g 4`, and `g 4` is bounded below by no label of `(univ, 3)`; what it forces
unconditionally is the bottom coupling `A₂c_eq_bot_of_A₁c` (`ω+3 ↦ ω+4`).  The copy `b₁new`'s
row reads only `⊥`, `ω+1`, `ω·2+3`: no orbit lands on a source.  At grades one and two the only
moving orbits landing on sources are `ω·2+1 ↦ ω·2+2` (threshold two, above the grade-one
controller) and `ω·2+2 ↦ ω·2+3` (threshold three, above the grade-two controller), whose
unconditional content is the bottom couplings already extracted (`U_H_eq_bot_of_H₀old`,
`U_S_eq_bot_of_s₀old`); `ω+1 ↦ ω+2` at threshold two lands on a non-source.  So the moving
orbit `ω+1 ↦ ω+3` is the one source orbit at the controllers' own grades, and it is compiled
here.

Necessary constraints only; the augmented list is not claimed sufficient.  Not done: the
grade-three retuning.  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## Generic: a moving source orbit bounds the probes -/

section Generic

variable {D : Type*} (grade : D → ℕ) (source value : D → ExtOrd) {c d : D}
  (hd : grade d ≤ grade c)
  (h : TransformsTo grade source (fun e => min (value e) (value c)))

include hd in
/-- **The shifter is uncapped at a cell labelled strictly below the controller**: with
`value d < value c`, the row equation at `d` reads `value d = σ (source d)`, and that value is
below the suppressor at the controller's grade. -/
theorem shifter_eq_of_lt {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd}
    (hg : ∀ n m, n < m → g m ≤ g n)
    (he : ∀ e, min (value e) (value c) = min (σ (source e)) (g (grade e)))
    (hlt : value d < value c) : σ (source d) = value d ∧ σ (source d) ≤ g (grade c) := by
  have hc := he c
  rw [min_self] at hc
  have hcg : value c ≤ g (grade c) := hc.le.trans (min_le_right _ _)
  have hgd : g (grade c) ≤ g (grade d) := by
    rcases eq_or_lt_of_le hd with hh | hh
    · rw [hh]
    · exact hg _ _ hh
  have he' := he d
  rw [min_eq_left hlt.le] at he'
  have hσ : σ (source d) = value d := by
    rcases le_total (σ (source d)) (g (grade d)) with hh | hh
    · rw [min_eq_left hh] at he'; exact he'.symm
    · rw [min_eq_right hh] at he'
      exact absurd he' (ne_of_lt (hlt.trans_le (hcg.trans hgd)))
  exact ⟨hσ, hσ ▸ hlt.le.trans hcg⟩

include hd h in
/-- **A moving orbit bounds the probe** (after the research scout `orbit_bounds_controller`):
if the source at `e` is the replacement of the source at `d` at the controller's grade, the probe
at `e` is at most the replacement of the label at `d`. -/
theorem orbit_bounds_probe {e : D}
    (horbit : source e = extVisibilityReplace (source d) (grade c) (grade c)) :
    min (value e) (value c) ≤ extVisibilityReplace (value d) (grade c) (grade c) := by
  obtain ⟨g, σ, hg, -, -, -, h5, he⟩ := h
  by_cases hlt : value d < value c
  · obtain ⟨hσ, hactive⟩ := shifter_eq_of_lt grade source value hd hg he hlt
    have hcomm := h5 (source d) (grade c) hactive (grade c) le_rfl
    have hee : min (value e) (value c) = min (σ (source e)) (g (grade e)) := he e
    rw [hee, horbit, hcomm, hσ]
    exact min_le_left _ _
  · exact (min_le_right _ _).trans ((not_lt.mp hlt).trans (le_extVisibilityReplace_self _ _))

include hd h in
/-- **A source fixed by a replacement fixes its label**: with `value d < value c` and the source
at `d` fixed by the replacement `(grade c, i)`, the label at `d` is fixed by it too (clause 5 at
index `i`). -/
theorem orbit_fixes_label (hlt : value d < value c) {i : ℕ} (hi : i ≤ grade c)
    (hfix : extVisibilityReplace (source d) (grade c) i = source d) :
    extVisibilityReplace (value d) (grade c) i = value d := by
  obtain ⟨g, σ, hg, -, -, -, h5, he⟩ := h
  obtain ⟨hσ, hactive⟩ := shifter_eq_of_lt grade source value hd hg he hlt
  have hcomm := h5 (source d) (grade c) hactive i hi
  rw [hfix, hσ] at hcomm
  exact hcomm.symm

end Generic

/-! ## The sharp ordinal consequence -/

section Sharp

/-- **The sharp orbit law**: `a < b`, `b` self-visible at three, `b ≤ R₃ a`, and `a` fixed by
the index-one replacement force `b = R₃ a` (and `a` has finite part one). -/
theorem eq_R₃_of_orbit {a b : ExtOrd} (hlt : a < b) (hb : SelfVis 3 b)
    (hle : b ≤ extVisibilityReplace a 3 3) (hfix : extVisibilityReplace a 3 1 = a) :
    b = extVisibilityReplace a 3 3 := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨μ, rfl⟩
  · rw [extVisibilityReplace_bot] at hle
    exact absurd hlt (not_lt.mpr hle)
  · exact absurd hlt (not_lt.mpr le_top)
  rcases ExtOrd.cases b with rfl | rfl | ⟨ζ, rfl⟩
  · exact absurd hlt (not_lt.mpr bot_le)
  · rw [extVisibilityReplace_ofOrd] at hle; exact absurd hle (not_top_le_ofOrd _)
  rw [extVisibilityReplace_ofOrd, ofOrd_inj, visReplace_eq] at hfix ⊢
  rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd, visReplace_eq] at hle
  rw [selfVis_ofOrd_iff] at hb
  rw [ofOrd_lt_ofOrd] at hlt
  by_cases h3 : finitePart μ < 3
  · rw [ite_eq_left h3] at hfix hle ⊢
    -- the finite part of `μ` is one
    have hfp : finitePart μ = 1 := by
      have := hfix.trans (decomposition μ).symm
      have h' := (add_le_add_iff_left (limitPart μ)).mp this.ge
      have h'' := (add_le_add_iff_left (limitPart μ)).mp this.le
      exact le_antisymm (Nat.cast_le.mp h') (Nat.cast_le.mp h'')
    -- the limit parts agree
    have hlim : limitPart ζ = limitPart μ := by
      apply le_antisymm
      · have := limitPart_mono hle
        rwa [limitPart_limitPart_add_nat] at this
      · exact limitPart_mono hlt.le
    -- the finite part of `ζ` is three
    have hfζ : finitePart ζ = 3 := by
      have e := decomposition ζ
      rw [hlim] at e
      rw [← e] at hle
      have := Nat.cast_le.mp ((add_le_add_iff_left (limitPart μ)).mp hle)
      omega
    calc ζ = limitPart ζ + (finitePart ζ : Ordinal) := (decomposition ζ).symm
      _ = limitPart μ + ((3 : ℕ) : Ordinal) := by rw [hlim, hfζ]
  · rw [ite_eq_right h3] at hle
    rw [decomposition μ] at hle
    exact absurd hlt (not_lt.mpr hle)

theorem limitPart_add_nat_self (α : Ordinal.{0}) (m : ℕ) :
    limitPart (limitPart α + (m : Ordinal)) = limitPart α := limitPart_limitPart_add_nat α m

end Sharp

/-! ## The actual orbit at grade three -/

section Actual

theorem v₀_orbit_three : extVisibilityReplace v₀ 3 3 = η₁ := by
  rw [v₀_num, η₁_num, extVisibilityReplace_ofOrd]
  unfold visibilityReplace
  rw [ite_eq_left (by rw [fp_ω1j]; omega)]
  unfold ordinalReplace
  rw [limitPart_mul_add]

theorem v₀_orbit_three_one : extVisibilityReplace v₀ 3 1 = v₀ := by
  rw [v₀_num, extVisibilityReplace_ofOrd]
  unfold visibilityReplace
  rw [ite_eq_left (by rw [fp_ω1j]; omega)]
  unfold ordinalReplace
  rw [limitPart_mul_add]

/-- The rows of the three controllers read `ω+1` at every proper grade-one cell. -/
theorem rows₃_A₁c_proper (d : D₂.below (D₂.cell A₁c)) (hp : IsProper d.1)
    (hg : D₂.grade d.1 = 1) : rows₃.E A₁c d = v₀ := by
  have hnm : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_A₁c d.2
  obtain ⟨c, hc⟩ := hp
  have hgp : c.gradeP ≤ 1 := by rw [gradeP_le_of_proper hnm hc, hg]
  rw [E₃_A₁c d, pull_of_not_mute _ hnm, hc, rowX_a₁_inl, t₀_F_v₀ hgp]
theorem rows₃_A₂c_proper (d : D₂.below (D₂.cell A₂c)) (hp : IsProper d.1)
    (hg : D₂.grade d.1 = 1) : rows₃.E A₂c d = v₀ := by
  have hnm : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_A₂c d.2
  obtain ⟨c, hc⟩ := hp
  have hgp : c.gradeP ≤ 1 := by rw [gradeP_le_of_proper hnm hc, hg]
  rw [E₃_A₂c d, pull_of_not_mute _ hnm, hc, rowX_a₂_inl, t₀_F_v₀ hgp]
theorem rows₃_ub₁_proper (d : D₂.below (D₂.cell ub₁)) (hp : IsProper d.1)
    (hg : D₂.grade d.1 = 1) : rows₃.E ub₁ d = v₀ := by
  have hnm : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_ub₁ d.2
  obtain ⟨c, hc⟩ := hp
  have hgp : c.gradeP ≤ 1 := by rw [gradeP_le_of_proper hnm hc, hg]
  rw [rows₃_E, E₃_ub₁ d, qL_of_proper hnm hc, t₀_F_v₀ hgp]

theorem proper_below_A₁c (d : D₂.below (Finset.univ, 3)) :
    GradedLe (D₂.cell d.1) (D₂.cell A₁c) := by
  rw [cell_A₁c]; exact d.2
theorem proper_below_ub₁ (d : D₂.below (Finset.univ, 3)) :
    GradedLe (D₂.cell d.1) (D₂.cell ub₁) := by
  rw [cell_ub₁]; exact d.2

variable {q : D₂.below (Finset.univ, 3) → ExtOrd}
  (hq : RespectsSemanticsBelow rows₃ (Finset.univ, 3) q)
include hq

/-- **The moving-orbit bound** (the research scout's `actual_A₁c_bound`): `a₁`'s controller is
at most `R₃` of every proper grade-one label — the proper source `ω+1` is replaced by the
controller's diagonal `ω+3` at threshold three. -/
theorem A₁c_le_R₃_of_respects (d : D₂.below (Finset.univ, 3)) (hp : IsProper d.1)
    (hg : D₂.grade d.1 = 1) :
    q ⟨A₁c, memA₁c₃⟩ ≤ extVisibilityReplace (q d) 3 3 := by
  have h := orbit_bounds_probe (fun e : D₂.below (D₂.cell A₁c) => D₂.grade e.1) (rows₃.E A₁c)
    (fun e => q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ e)) (c := ⟨A₁c, refl_A₁c⟩)
    (d := ⟨d.1, proper_below_A₁c d⟩)
    (by change D₂.grade d.1 ≤ D₂.grade A₁c; rw [hg, grade_A₁c]; decide)
    (hq.locality ⟨A₁c, memA₁c₃⟩) (e := ⟨A₁c, refl_A₁c⟩) (by
      change rows₃.E A₁c ⟨A₁c, refl_A₁c⟩ =
        extVisibilityReplace (rows₃.E A₁c ⟨d.1, proper_below_A₁c d⟩) (D₂.grade A₁c) (D₂.grade A₁c)
      rw [rows₃_A₁c_self, rows₃_A₁c_proper ⟨d.1, proper_below_A₁c d⟩ hp hg, grade_A₁c,
        v₀_orbit_three])
  have e1 : CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₁c, refl_A₁c⟩ = ⟨A₁c, memA₁c₃⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨d.1, proper_below_A₁c d⟩ = d :=
    Subtype.ext rfl
  change min (q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₁c, refl_A₁c⟩))
    (q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₁c, refl_A₁c⟩)) ≤
    extVisibilityReplace (q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨d.1, proper_below_A₁c d⟩))
      (D₂.grade A₁c) (D₂.grade A₁c) at h
  rwa [e1, e2, min_self, grade_A₁c] at h

/-- **The same orbit in `b₁`'s controller's row** bounds the same label: `b₁`'s row reads `ω+1`
at the proper grade-one cells and `ω+3` at `a₁`'s controller, whose probe against `w` is `z₁`. -/
theorem A₁c_le_R₃_of_respects' (d : D₂.below (Finset.univ, 3)) (hp : IsProper d.1)
    (hg : D₂.grade d.1 = 1) :
    q ⟨A₁c, memA₁c₃⟩ ≤ extVisibilityReplace (q d) 3 3 := by
  have hA₁ : GradedLe (D₂.cell A₁c) (D₂.cell ub₁) := by rw [cell_ub₁]; exact memA₁c₃
  have h := orbit_bounds_probe (fun e : D₂.below (D₂.cell ub₁) => D₂.grade e.1) (rows₃.E ub₁)
    (fun e => q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ e)) (c := ⟨ub₁, refl_ub₁⟩)
    (d := ⟨d.1, proper_below_ub₁ d⟩)
    (by change D₂.grade d.1 ≤ D₂.grade ub₁; rw [hg, grade_ub₁]; decide)
    (hq.locality ⟨ub₁, memub₁₃⟩) (e := ⟨A₁c, hA₁⟩) (by
      change rows₃.E ub₁ ⟨A₁c, hA₁⟩ =
        extVisibilityReplace (rows₃.E ub₁ ⟨d.1, proper_below_ub₁ d⟩) (D₂.grade ub₁) (D₂.grade ub₁)
      rw [rows₃_ub₁_proper ⟨d.1, proper_below_ub₁ d⟩ hp hg, grade_ub₁, v₀_orbit_three]
      exact (rows₃_E _ _).trans ((E₃_ub₁ _).trans qL_A₁c))
  have e1 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨A₁c, hA₁⟩ = ⟨A₁c, memA₁c₃⟩ := Subtype.ext rfl
  have e0 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨ub₁, refl_ub₁⟩ = ⟨ub₁, memub₁₃⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨d.1, proper_below_ub₁ d⟩ = d :=
    Subtype.ext rfl
  change min (q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨A₁c, hA₁⟩))
    (q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨ub₁, refl_ub₁⟩)) ≤
    extVisibilityReplace (q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨d.1, proper_below_ub₁ d⟩))
      (D₂.grade ub₁) (D₂.grade ub₁) at h
  rw [e1, e0, e2, grade_ub₁,
    min_eq_left ((A₁c_le_A₂c_of_respects hq).trans (A₂c_le_ub₁_of_respects hq))] at h
  exact h

/-- **The index-one orbit**: a proper grade-one label strictly below `a₁`'s controller is fixed by
the replacement `(3, 1)` — its finite part is one, or at least three. -/
theorem proper_fix_of_lt_A₁c (d : D₂.below (Finset.univ, 3)) (hp : IsProper d.1)
    (hg : D₂.grade d.1 = 1) (hlt : q d < q ⟨A₁c, memA₁c₃⟩) :
    extVisibilityReplace (q d) 3 1 = q d := by
  have e1 : CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₁c, refl_A₁c⟩ = ⟨A₁c, memA₁c₃⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨d.1, proper_below_A₁c d⟩ = d :=
    Subtype.ext rfl
  have h := orbit_fixes_label (fun e : D₂.below (D₂.cell A₁c) => D₂.grade e.1) (rows₃.E A₁c)
    (fun e => q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ e)) (c := ⟨A₁c, refl_A₁c⟩)
    (d := ⟨d.1, proper_below_A₁c d⟩)
    (by change D₂.grade d.1 ≤ D₂.grade A₁c; rw [hg, grade_A₁c]; decide)
    (hq.locality ⟨A₁c, memA₁c₃⟩) (by
      change q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨d.1, proper_below_A₁c d⟩) <
        q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨A₁c, refl_A₁c⟩)
      rw [e1, e2]; exact hlt)
    (i := 1) (by change 1 ≤ D₂.grade A₁c; rw [grade_A₁c]; decide) (by
      change extVisibilityReplace (rows₃.E A₁c ⟨d.1, proper_below_A₁c d⟩) (D₂.grade A₁c) 1 =
        rows₃.E A₁c ⟨d.1, proper_below_A₁c d⟩
      rw [rows₃_A₁c_proper ⟨d.1, proper_below_A₁c d⟩ hp hg, grade_A₁c, v₀_orbit_three_one])
  change extVisibilityReplace (q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨d.1, proper_below_A₁c d⟩))
    (D₂.grade A₁c) 1 = q (CellScheme.below.incl ⟨A₁c, memA₁c₃⟩ ⟨d.1, proper_below_A₁c d⟩) at h
  rwa [e2, grade_A₁c] at h

/-- **The sharp orbit constraint at grade three**: a proper grade-one label `v` strictly below
`a₁`'s controller forces the controller's label to be exactly `R₃ v` (and `v` to have finite
part one).  Order and visibility alone do not give this. -/
theorem A₁c_eq_R₃_of_lt (d : D₂.below (Finset.univ, 3)) (hp : IsProper d.1)
    (hg : D₂.grade d.1 = 1) (hlt : q d < q ⟨A₁c, memA₁c₃⟩) :
    q ⟨A₁c, memA₁c₃⟩ = extVisibilityReplace (q d) 3 3 :=
  eq_R₃_of_orbit hlt (selfVis_A₁c_of_respects hq) (A₁c_le_R₃_of_respects hq d hp hg)
    (proper_fix_of_lt_A₁c hq d hp hg hlt)

end Actual

end VaughtConjecture.Knight
