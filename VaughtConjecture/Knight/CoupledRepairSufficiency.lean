/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledRepair

/-! # The repaired semantics at grade three: exact probes, the admissible parameters, and the
two face sections

**The exact capped-probe laws** (`probe_orbit`, `probe_ordered`, `probe_fixed`,
`probe_bottom_orbit`, `label_of_probe_orbit`; after the research scout `CappedProbeLaws.lean`,
draft #319): in a row transformed onto the probes `min (p d) (p c)` of a controller `c` of
maximal grade with `p c` self-visible there, a source orbit `E e = replace (E d) k i` is an
**exact equation** on the capped probes for every `i ≤ k ≤ grade c`, sources order the probes,
fixed sources give self-visible probes, and bottom propagates along orbits at *every* threshold
(so the threshold-four obligation at a grade-three controller is never vacuous).  All from the
existing controller-capped witness `exists_cappedWitness`.

**Instantiated on the repaired rows** (`q` respecting `rowsR` on `(univ, 3)`): at `b₁`'s
controller, `z₁ = R₃ (min v w)` exactly (`A₁c_eq_R₃_min_of_respectsR`, the source `ω+1` reaching
the `a₁` cells' `ω+3`), `min v w` is fixed by the replacement `(3, 1)`
(`min_proper_ub₁_fixed_of_respectsR`, kept separately), and `min x₀ w` is grade-three
self-visible (`selfVis_min_H₀old_ub₁_of_respectsR`, the old witnesses' new source `ω·2+3` is).

**The admissible parameters** (`Legal₃`): legal grade-two parameters plus `z₁ ≤ z₂ ≤ x₀`,
`z₂ ≤ w ≤ H`, grade-three visibility of `z₁, z₂, w, min x₀ w`, the exact orbit, the fixing law,
and the two bottom couplings `z₁ = ⊥ → z₂ = ⊥`, `min x₀ w = ⊥ → w = ⊥`.  **The value shape**
(`Shape₃`): the seven parameters at the twelve named cells (the old level-two witness at
`min x₀ H`, the duplicates on their controllers), `⊥` at proper grade-two cells, `v` at proper
grade-one cells.

**Sufficiency** (`respects_of_shape₃`): admissible parameters in the value shape respect `rowsR`
on `(univ, 3)`.  Grades one and two are the grade-two sufficiency lemma; every grade-three row is
witnessed by one new shape, **the two-block strip** (`Witness.twoStrip`: `⊥` below `ω`; on the
block at `ω` the threshold-three orbit of `t` up to finite part three and a constant from four; on
the block at `ω·2` a constant up to three and another from four; the last constant beyond) — with
`t = min v z₁`, `min v z₂`, `min v w` at the `a₁`, `a₂`, `b₁` rows respectively, the orbit values
computed by the threshold-`K` orbit calculus `orbit_eq_K` and the block arithmetic at every block
(`blockIdx_eq`, `limitPart_of_block'`, `fp_le_of_block'`).  The one algebraic fact behind the
three instantiations: for any cap `a` between `z₁` and `w`, `R₃ (min v a) = z₁`
(`Legal₃.R₃_min_eq`; if `z₁ < v` then `z₁ = w`).  **No further condition appeared.**

**Necessity** (`shape_legal_of_respectsR`): every respecting labelling has the value shape with
admissible parameters — the characterization is an iff.

**The two face sections** (`faceA_extendsR`, `faceB_extendsR`): every labelling respecting
`rowsR` on the old face `({0,1,2}, 3)`, resp. the copy face `({1,2,3}, 3)`, extends to one
respecting it on `(univ, 3)`, by the explicit sections `(v, x, x, y, a, b, b)` (`sectA`) and
`(v, x, x, y, r, r, b)` with `r = R₃ (min v b)` (`sectB`), no block-specific constants; the face
constraints are read off the faces' own rows (`a₁old_le_a₂old'`, `a₂old_le_H₀old'`,
`a₂old_le_s₀old'`, `a₁old_eq_R₃_min'`, `fix_min_a₂old'`, `a₂old_eq_bot_of_a₁old'`,
`b₁new_le_H₀new'`, `b₁new_le_s₀new'`, `fix_min_b₁new'`).  These are the cap-`⊥` instances of the
two grade-three face obligations of `ProperToFullRLow`.

Not done: the capped lift (a nonbottom comparison cap `γ` and a second labelling `q`) — the
relative pasting rule of the research handoff — and hence the two face obligations in full and
bountifulness.  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## The exact capped-probe laws (after the research scout `CappedProbeLaws.lean`) -/

section ProbeLaws

variable {D : Type*} {grade : D → ℕ} {E p : D → ExtOrd} {c : D}
  (hmax : ∀ d, grade d ≤ grade c) (hvis : SelfVis (grade c) (p c))
  (hloc : TransformsTo grade E (fun d => min (p d) (p c)))

include hmax hvis hloc

/-- **A source orbit is an exact equation on the capped probes**, at every threshold up to the
controller's grade. -/
theorem probe_orbit {d e : D} {k i : ℕ} (hk : k ≤ grade c) (hi : i ≤ k)
    (he : E e = extVisibilityReplace (E d) k i) :
    min (p e) (p c) = extVisibilityReplace (min (p d) (p c)) k i := by
  by_cases hb : p c = ⊥
  · rw [hb, min_eq_right bot_le, min_eq_right bot_le, extVisibilityReplace_bot]
  · obtain ⟨_, τ, _, _, _, _, _, _, _, hsrc, hcomm, _⟩ :=
      exists_cappedWitness grade E p c hmax hvis hb hloc
    rw [← hsrc e, he, hcomm _ k i hk hi, hsrc d]

/-- Capped probes are ordered like their sources. -/
theorem probe_ordered {d e : D} (he : E d ≤ E e) : min (p d) (p c) ≤ min (p e) (p c) := by
  by_cases hb : p c = ⊥
  · rw [hb, min_eq_right bot_le, min_eq_right bot_le]
  · obtain ⟨_, τ, _, _, _, hm, _, _, _, hsrc, _, _⟩ :=
      exists_cappedWitness grade E p c hmax hvis hb hloc
    rw [← hsrc d, ← hsrc e]
    exact hm he

/-- A fixed source gives a self-visible capped probe. -/
theorem probe_fixed {d : D} {k : ℕ} (hk : k ≤ grade c) (hd : SelfVis k (E d)) :
    SelfVis k (min (p d) (p c)) :=
  (probe_orbit hmax hvis hloc hk le_rfl hd.symm).symm

/-- **Bottom propagates along orbits at every threshold**, above the controller's grade too. -/
theorem probe_bottom_orbit {d e : D} {k i : ℕ} (hi : i ≤ k)
    (he : E e = extVisibilityReplace (E d) k i) (hd : min (p d) (p c) = ⊥) :
    min (p e) (p c) = ⊥ := by
  by_cases hb : p c = ⊥
  · rw [hb, min_eq_right bot_le]
  · obtain ⟨_, τ, _, _, _, _, _, _, _, hsrc, _, hprop⟩ :=
      exists_cappedWitness grade E p c hmax hvis hb hloc
    rw [← hsrc e, he]
    exact hprop _ ((hsrc d).trans hd) k i hi

/-- An orbit determines a label already below the cap. -/
theorem label_of_probe_orbit {d e : D} {k i : ℕ} (hk : k ≤ grade c) (hi : i ≤ k)
    (he : E e = extVisibilityReplace (E d) k i) (hle : p e ≤ p c) :
    p e = extVisibilityReplace (min (p d) (p c)) k i := by
  have h := probe_orbit hmax hvis hloc hk hi he
  rwa [min_eq_left hle] at h

end ProbeLaws

/-! ## Instantiation on the repaired rows -/

section Instances

theorem incl_ub₁_eq (d : D₂.below (Finset.univ, 3)) :
    CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨d.1, proper_below_ub₁ d⟩ = d := Subtype.ext rfl
theorem incl_ub₁_self :
    CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨ub₁, refl_ub₁⟩ = ⟨ub₁, memub₁₃⟩ := Subtype.ext rfl
theorem grade_le_grade_ub₁ (e : D₂.below (D₂.cell ub₁)) : D₂.grade e.1 ≤ D₂.grade ub₁ := by
  rw [grade_ub₁]; exact grade_le_below_ub₁ e

variable {q : D₂.below (Finset.univ, 3) → ExtOrd}
  (hq : RespectsSemanticsBelow rowsR (Finset.univ, 3) q)
include hq

theorem selfVis_ub₁_of_respectsR : SelfVis 3 (q ⟨ub₁, memub₁₃⟩) := by
  have := (hq.orderly ⟨ub₁, memub₁₃⟩).symm
  change SelfVis (D₂.grade ub₁) _ at this
  rwa [grade_ub₁] at this

theorem selfVis_incl_ub₁ :
    SelfVis (D₂.grade ub₁) (q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨ub₁, refl_ub₁⟩)) := by
  rw [grade_ub₁, incl_ub₁_self]; exact selfVis_ub₁_of_respectsR hq

/-- **The exact orbit at the repaired row**: `z₁ = R₃ (min v w)`. -/
theorem A₁c_eq_R₃_min_of_respectsR (d : D₂.below (Finset.univ, 3)) (hp : IsProper d.1)
    (hg : D₂.grade d.1 = 1) :
    q ⟨A₁c, memA₁c₃⟩ = extVisibilityReplace (min (q d) (q ⟨ub₁, memub₁₃⟩)) 3 3 := by
  have h := label_of_probe_orbit (grade := fun e : D₂.below (D₂.cell ub₁) => D₂.grade e.1)
    (E := rowsR.E ub₁) (p := fun e => q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ e))
    (c := ⟨ub₁, refl_ub₁⟩) grade_le_grade_ub₁ (selfVis_incl_ub₁ hq)
    (hq.locality ⟨ub₁, memub₁₃⟩) (d := ⟨d.1, proper_below_ub₁ d⟩) (e := ⟨A₁c, A₁c_below_ub₁⟩)
    (k := 3) (i := 3) (by change 3 ≤ D₂.grade ub₁; rw [grade_ub₁]) le_rfl
    (by rw [rowsR_ub₁_A₁c, rowsR_E_ub₁ ⟨d.1, proper_below_ub₁ d⟩,
          qM_proper_one (not_mute₂_of_low le_rfl d) hp hg.le, v₀_orbit_three])
    (by change q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨A₁c, A₁c_below_ub₁⟩) ≤
          q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨ub₁, refl_ub₁⟩)
        rw [show CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨A₁c, A₁c_below_ub₁⟩ = ⟨A₁c, memA₁c₃⟩ from
          Subtype.ext rfl, incl_ub₁_self]
        exact (A₁c_le_A₂c_of_respectsR hq).trans (A₂c_le_ub₁_of_respectsR hq))
  change q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨A₁c, A₁c_below_ub₁⟩) =
    extVisibilityReplace (min (q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨d.1, proper_below_ub₁ d⟩))
      (q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨ub₁, refl_ub₁⟩))) 3 3 at h
  rwa [show CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨A₁c, A₁c_below_ub₁⟩ = ⟨A₁c, memA₁c₃⟩ from
    Subtype.ext rfl, incl_ub₁_eq, incl_ub₁_self] at h

/-- **The fixing law at the repaired row**: `min v w` is fixed by the replacement `(3, 1)`. -/
theorem min_proper_ub₁_fixed_of_respectsR (d : D₂.below (Finset.univ, 3)) (hp : IsProper d.1)
    (hg : D₂.grade d.1 = 1) :
    extVisibilityReplace (min (q d) (q ⟨ub₁, memub₁₃⟩)) 3 1 = min (q d) (q ⟨ub₁, memub₁₃⟩) := by
  have h := probe_orbit (grade := fun e : D₂.below (D₂.cell ub₁) => D₂.grade e.1)
    (E := rowsR.E ub₁) (p := fun e => q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ e))
    (c := ⟨ub₁, refl_ub₁⟩) grade_le_grade_ub₁ (selfVis_incl_ub₁ hq)
    (hq.locality ⟨ub₁, memub₁₃⟩) (d := ⟨d.1, proper_below_ub₁ d⟩) (e := ⟨d.1, proper_below_ub₁ d⟩)
    (k := 3) (i := 1) (by change 3 ≤ D₂.grade ub₁; rw [grade_ub₁]) (by decide)
    (by rw [rowsR_E_ub₁ ⟨d.1, proper_below_ub₁ d⟩,
          qM_proper_one (not_mute₂_of_low le_rfl d) hp hg.le, v₀_orbit_three_one])
  change min (q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨d.1, proper_below_ub₁ d⟩))
      (q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨ub₁, refl_ub₁⟩)) =
    extVisibilityReplace (min (q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨d.1, proper_below_ub₁ d⟩))
      (q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨ub₁, refl_ub₁⟩))) 3 1 at h
  rw [incl_ub₁_eq, incl_ub₁_self] at h
  exact h.symm

/-- **The old witnesses' capped probe is grade-three self-visible** (their new source `ω·2+3`
is). -/
theorem selfVis_min_H₀old_ub₁_of_respectsR :
    SelfVis 3 (min (q ⟨H₀old, memH₀old₃⟩) (q ⟨ub₁, memub₁₃⟩)) := by
  have h := probe_fixed (grade := fun e : D₂.below (D₂.cell ub₁) => D₂.grade e.1)
    (E := rowsR.E ub₁) (p := fun e => q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ e))
    (c := ⟨ub₁, refl_ub₁⟩) grade_le_grade_ub₁ (selfVis_incl_ub₁ hq)
    (hq.locality ⟨ub₁, memub₁₃⟩) (d := ⟨H₀old, H₀old_below_ub₁⟩) (k := 3)
    (by change 3 ≤ D₂.grade ub₁; rw [grade_ub₁])
    (by rw [rowsR_ub₁_H₀old]; exact selfVis_ω2 3 3 le_rfl)
  change SelfVis 3 (min (q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨H₀old, H₀old_below_ub₁⟩))
    (q (CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨ub₁, refl_ub₁⟩))) at h
  rwa [show CellScheme.below.incl ⟨ub₁, memub₁₃⟩ ⟨H₀old, H₀old_below_ub₁⟩ = ⟨H₀old, memH₀old₃⟩
    from Subtype.ext rfl, incl_ub₁_self] at h

end Instances

/-! ## Block arithmetic at every block, and the threshold-`K` orbit calculus -/

section Blocks

theorem blockIdx_eq (n : ℕ) {α : Ordinal.{0}} (h1 : ωn n ≤ α) (h2 : α < ωn (n + 1)) :
    blockIdx α = ((n : ℕ) : Ordinal) := by
  have hb1 : ((n : ℕ) : Ordinal) ≤ blockIdx α := by
    have := blockIdx_mono h1
    rwa [show ωn n = Ordinal.omega0 * ((n : ℕ) : Ordinal) + ((0 : ℕ) : Ordinal) by
      rw [Nat.cast_zero, add_zero], blockIdx_mul_add] at this
  have hb2 : blockIdx α < ((n + 1 : ℕ) : Ordinal) := by
    by_contra h
    rw [not_lt] at h
    have : ωn (n + 1) ≤ limitPart α := by
      rw [limitPart_eq_mul_blockIdx]; exact mul_le_mul_right h _
    exact absurd h2 (not_lt.mpr (this.trans (limitPart_le α)))
  have hb2' : blockIdx α < ((n : ℕ) : Ordinal) + 1 := by rw [← Nat.cast_add_one]; exact hb2
  exact le_antisymm (Order.lt_add_one_iff.mp hb2') hb1

theorem limitPart_of_block' (n : ℕ) {α : Ordinal.{0}} (h1 : ωn n ≤ α) (h2 : α < ωn (n + 1)) :
    limitPart α = ωn n := by
  rw [limitPart_eq_mul_blockIdx, blockIdx_eq n h1 h2]

theorem fp_le_of_block' (n : ℕ) {α β : Ordinal.{0}} (hα1 : ωn n ≤ α) (hα2 : α < ωn (n + 1))
    (hβ1 : ωn n ≤ β) (hβ2 : β < ωn (n + 1)) (h : α ≤ β) : finitePart α ≤ finitePart β := by
  have eα := decomposition α
  have eβ := decomposition β
  rw [limitPart_of_block' n hα1 hα2] at eα
  rw [limitPart_of_block' n hβ1 hβ2] at eβ
  rw [← eα, ← eβ] at h
  exact Nat.cast_le.mp ((add_le_add_iff_left _).mp h)

theorem ofOrd_of_block' (n : ℕ) {a : ExtOrd} (h1 : ofOrd (ωn n) ≤ a) (h2 : a < ofOrd (ωn (n + 1))) :
    ∃ α : Ordinal.{0}, a = ofOrd α ∧ ωn n ≤ α ∧ α < ωn (n + 1) := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · exact absurd h1 (not_ofOrd_le_bot _)
  · exact absurd h2 (not_lt.mpr le_top)
  · exact ⟨α, rfl, ofOrd_le_ofOrd.mp h1, ofOrd_lt_ofOrd.mp h2⟩

theorem ωn_succ (n : ℕ) : ωn (n + 1) = ωn n + Ordinal.omega0 := by
  change Ordinal.omega0 * ((n + 1 : ℕ) : Ordinal) = Ordinal.omega0 * ((n : ℕ) : Ordinal) + _
  rw [Nat.cast_add_one, mul_add_one]

theorem block_add_nat (n j : ℕ) : ωn n ≤ ωn n + (j : Ordinal) ∧ ωn n + (j : Ordinal) < ωn (n + 1) :=
  ⟨le_self_add, by rw [ωn_succ]; exact add_lt_add_right (Ordinal.natCast_lt_omega0 j) _⟩

theorem ωn_le_succ (n : ℕ) : ωn n ≤ ωn (n + 1) :=
  mul_le_mul_right (Nat.cast_le.mpr (Nat.le_succ n)) _

/-- Replacement inside a block stays in the block, with the expected finite part. -/
theorem visReplace_of_block' (n : ℕ) {α : Ordinal.{0}} (h1 : ωn n ≤ α) (h2 : α < ωn (n + 1))
    (k i : ℕ) :
    visibilityReplace α k i =
      ωn n + ((if finitePart α < k then i else finitePart α : ℕ) : Ordinal) := by
  rw [visReplace_eq, limitPart_of_block' n h1 h2]

theorem fp_ωn_add (n j : ℕ) : finitePart (ωn n + (j : Ordinal)) = j := finitePart_mul_add n j

/-- The orbit calculus at threshold `K`: for `k ≤ K`, `i ≤ k`. -/
theorem orbit_eq_K (K : ℕ) {m : ExtOrd} (hm : SelfVis 1 m) {j k i : ℕ} (hk : k ≤ K) (hi : i ≤ k) :
    extVisibilityReplace (extVisibilityReplace m K (min j K)) k i =
      extVisibilityReplace m K (min (if j < k then i else j) K) := by
  rcases ExtOrd.cases m with rfl | rfl | ⟨μ, rfl⟩
  · rw [extVisibilityReplace_bot, extVisibilityReplace_bot, extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top, extVisibilityReplace_top, extVisibilityReplace_top]
  · have h1 : 1 ≤ finitePart μ := selfVis_ofOrd_iff.mp hm
    rw [extVisibilityReplace_ofOrd, extVisibilityReplace_ofOrd, extVisibilityReplace_ofOrd,
      ofOrd_inj, visReplace_eq (visibilityReplace μ K (min j K)), limitPart_visibilityReplace,
      finitePart_visibilityReplace, visReplace_eq μ K]
    congr 1
    norm_cast
    split_ifs <;> omega

theorem evr_arg_mono_K (K : ℕ) (m : ExtOrd) {s s' : ℕ} (h : s ≤ s') :
    extVisibilityReplace m K s ≤ extVisibilityReplace m K s' := by
  rcases ExtOrd.cases m with rfl | rfl | ⟨μ, rfl⟩
  · rw [extVisibilityReplace_bot, extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top, extVisibilityReplace_top]
  · rw [extVisibilityReplace_ofOrd, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd, visReplace_eq,
      visReplace_eq]
    split_ifs
    · exact add_le_add_right (Nat.cast_le.mpr h) _
    · exact le_rfl

theorem evr_fixed_of_ge {a : ExtOrd} {α : Ordinal.{0}} (ha : a = ofOrd α) {k i : ℕ}
    (h : k ≤ finitePart α) : extVisibilityReplace a k i = a := by
  rw [ha, extVisibilityReplace_ofOrd, ofOrd_inj, visReplace_eq, ite_eq_right (not_lt.mpr h),
    decomposition]

theorem R₃_eq_bot_iff (t : ExtOrd) : extVisibilityReplace t 3 3 = ⊥ ↔ t = ⊥ := by
  constructor
  · intro h; by_contra hne; exact extVisibilityReplace_ne_bot hne 3 3 h
  · rintro rfl; exact extVisibilityReplace_bot _ _

theorem fix₃₁_of_selfVis₃ {a : ExtOrd} (h : SelfVis 3 a) : extVisibilityReplace a 3 1 = a :=
  evr_eq_self_of_selfVis h 1

end Blocks

/-! ## The two-block strip witness at threshold three -/

section TwoStrip

open Classical in
/-- **The two-block strip**: `⊥` below `ω`; on the block at `ω`, the threshold-three orbit of `t`
up to finite part three and the constant `c₂` from finite part four; on the block at `ω·2`, the
constant `c₃` up to finite part three and `c₄` from four; `c₄` from `ω·3` on. -/
noncomputable def twoStripShifter (t c₂ c₃ c₄ : ExtOrd) : ExtOrd → ExtOrd := fun a =>
  if a = ⊥ then ⊥ else if a < ofOrd (ωn 1) then ⊥
  else if a < ofOrd (ωn 2) then (if fpE a ≤ 3 then extVisibilityReplace t 3 (fpE a) else c₂)
  else if a < ofOrd (ωn 3) then (if fpE a ≤ 3 then c₃ else c₄) else c₄

variable {t c₂ c₃ c₄ : ExtOrd}

theorem ts_bot : twoStripShifter t c₂ c₃ c₄ ⊥ = ⊥ := by
  classical
  unfold twoStripShifter; rw [ite_eq_left rfl]
theorem ts_of_lt_one {a : ExtOrd} (ha : a ≠ ⊥) (h : a < ofOrd (ωn 1)) :
    twoStripShifter t c₂ c₃ c₄ a = ⊥ := by
  classical
  unfold twoStripShifter; rw [ite_eq_right ha, ite_eq_left h]
theorem ts_of_block₁ {a : ExtOrd} (h1 : ofOrd (ωn 1) ≤ a) (h2 : a < ofOrd (ωn 2)) :
    twoStripShifter t c₂ c₃ c₄ a =
      if fpE a ≤ 3 then extVisibilityReplace t 3 (fpE a) else c₂ := by
  classical
  unfold twoStripShifter
  rw [ite_eq_right (fun hb => not_ofOrd_le_bot _ (hb ▸ h1)), ite_eq_right (not_lt.mpr h1),
    ite_eq_left h2]
theorem ts_of_block₂ {a : ExtOrd} (h1 : ofOrd (ωn 2) ≤ a) (h2 : a < ofOrd (ωn 3)) :
    twoStripShifter t c₂ c₃ c₄ a = if fpE a ≤ 3 then c₃ else c₄ := by
  classical
  unfold twoStripShifter
  have h1' : ofOrd (ωn 1) ≤ a := (ofOrd_le_ofOrd.mpr (ωn_le_succ 1)).trans h1
  rw [ite_eq_right (fun hb => not_ofOrd_le_bot _ (hb ▸ h1)), ite_eq_right (not_lt.mpr h1'),
    ite_eq_right (not_lt.mpr h1), ite_eq_left h2]
theorem ts_of_ge_three {a : ExtOrd} (h : ofOrd (ωn 3) ≤ a) : twoStripShifter t c₂ c₃ c₄ a = c₄ := by
  classical
  unfold twoStripShifter
  have h2 : ofOrd (ωn 2) ≤ a := (ofOrd_le_ofOrd.mpr (ωn_le_succ 2)).trans h
  have h1 : ofOrd (ωn 1) ≤ a := (ofOrd_le_ofOrd.mpr (ωn_le_succ 1)).trans h2
  rw [ite_eq_right (fun hb => not_ofOrd_le_bot _ (hb ▸ h1)), ite_eq_right (not_lt.mpr h1),
    ite_eq_right (not_lt.mpr h2), ite_eq_right (not_lt.mpr h)]

/-- The values at the ordinals `ω+j` and `ω·2+j`. -/
theorem ts_ω1 (j : ℕ) (hj : j ≤ 3) :
    twoStripShifter t c₂ c₃ c₄ (ofOrd (ωn 1 + j)) = extVisibilityReplace t 3 j := by
  rw [ts_of_block₁ (ofOrd_le_ofOrd.mpr (block_add_nat 1 j).1)
    (ofOrd_lt_ofOrd.mpr (block_add_nat 1 j).2), fpE_ofOrd, fp_ωn_add, ite_eq_left hj]
theorem ts_ω1_hi (j : ℕ) (hj : 4 ≤ j) : twoStripShifter t c₂ c₃ c₄ (ofOrd (ωn 1 + j)) = c₂ := by
  rw [ts_of_block₁ (ofOrd_le_ofOrd.mpr (block_add_nat 1 j).1)
    (ofOrd_lt_ofOrd.mpr (block_add_nat 1 j).2), fpE_ofOrd, fp_ωn_add, ite_eq_right (by omega)]
theorem ts_ω2 (j : ℕ) (hj : j ≤ 3) : twoStripShifter t c₂ c₃ c₄ (ofOrd (ωn 2 + j)) = c₃ := by
  rw [ts_of_block₂ (ofOrd_le_ofOrd.mpr (block_add_nat 2 j).1)
    (ofOrd_lt_ofOrd.mpr (block_add_nat 2 j).2), fpE_ofOrd, fp_ωn_add, ite_eq_left hj]
theorem ts_ω2_hi (j : ℕ) (hj : 4 ≤ j) : twoStripShifter t c₂ c₃ c₄ (ofOrd (ωn 2 + j)) = c₄ := by
  rw [ts_of_block₂ (ofOrd_le_ofOrd.mpr (block_add_nat 2 j).1)
    (ofOrd_lt_ofOrd.mpr (block_add_nat 2 j).2), fpE_ofOrd, fp_ωn_add, ite_eq_right (by omega)]

/-- The block-`ω` part is all `⊥` once `t = ⊥` and `c₂ = ⊥`. -/
theorem ts_block₁_bot (ht : t = ⊥) (hc₂ : c₂ = ⊥) {a : ExtOrd} (h1 : ofOrd (ωn 1) ≤ a)
    (h2 : a < ofOrd (ωn 2)) : twoStripShifter t c₂ c₃ c₄ a = ⊥ := by
  rw [ts_of_block₁ h1 h2, ht, hc₂, extVisibilityReplace_bot]
  split_ifs <;> rfl
theorem ts_block₂_bot (hc₃ : c₃ = ⊥) (hc₄ : c₄ = ⊥) {a : ExtOrd} (h1 : ofOrd (ωn 2) ≤ a)
    (h2 : a < ofOrd (ωn 3)) : twoStripShifter t c₂ c₃ c₄ a = ⊥ := by
  rw [ts_of_block₂ h1 h2, hc₃, hc₄]
  split_ifs <;> rfl

theorem ts_le_R₃ (a : ExtOrd) (h1 : ofOrd (ωn 1) ≤ a) (h2 : a < ofOrd (ωn 2)) (hlo : fpE a ≤ 3) :
    twoStripShifter t c₂ c₃ c₄ a ≤ extVisibilityReplace t 3 3 := by
  rw [ts_of_block₁ h1 h2, ite_eq_left hlo]; exact evr_arg_mono_K 3 t hlo

/-- **The two-block strip is a witness at threshold three.** -/
theorem Witness.twoStrip (ht : SelfVis 1 t) (hc₂ : SelfVis 3 c₂) (hc₃ : SelfVis 3 c₃)
    (hc₄ : SelfVis 3 c₄) (h12 : extVisibilityReplace t 3 3 ≤ c₂) (h23 : c₂ ≤ c₃) (h34 : c₃ ≤ c₄)
    (hb₁ : t = ⊥ → c₂ = ⊥) (hb₂ : c₃ = ⊥ → c₄ = ⊥) :
    Witness (gTop 3) (twoStripShifter t c₂ c₃ c₄) where
  anti := (witness_id 3).anti
  vis := (witness_id 3).vis
  bot := ts_bot
  mono := by
    intro a b hab
    by_cases ha : a = ⊥
    · rw [ha, ts_bot]; exact bot_le
    have hb : b ≠ ⊥ := fun hb => ha (le_bot_iff.mp (hb ▸ hab))
    by_cases ha1 : a < ofOrd (ωn 1)
    · rw [ts_of_lt_one ha ha1]; exact bot_le
    have ha1' : ofOrd (ωn 1) ≤ a := not_lt.mp ha1
    have hb1' : ofOrd (ωn 1) ≤ b := ha1'.trans hab
    -- the value at `b` bounds `c₄`, at `a` in a lower region is below every later value
    have hbound : ∀ x, ofOrd (ωn 1) ≤ x → twoStripShifter t c₂ c₃ c₄ x ≤ c₄ := by
      intro x hx1
      by_cases hx2 : x < ofOrd (ωn 2)
      · rw [ts_of_block₁ hx1 hx2]
        split_ifs with hlo
        · exact ((evr_arg_mono_K 3 t hlo).trans h12).trans (h23.trans h34)
        · exact h23.trans h34
      by_cases hx3 : x < ofOrd (ωn 3)
      · rw [ts_of_block₂ (not_lt.mp hx2) hx3]
        split_ifs
        · exact h34
        · exact le_rfl
      · rw [ts_of_ge_three (not_lt.mp hx3)]
    by_cases ha2 : a < ofOrd (ωn 2)
    · obtain ⟨α, rfl, hα1, hα2⟩ := ofOrd_of_block' 1 ha1' ha2
      by_cases hb2 : b < ofOrd (ωn 2)
      · obtain ⟨β, rfl, hβ1, hβ2⟩ := ofOrd_of_block' 1 hb1' hb2
        have hfp := fp_le_of_block' 1 hα1 hα2 hβ1 hβ2 (ofOrd_le_ofOrd.mp hab)
        rw [ts_of_block₁ ha1' ha2, ts_of_block₁ hb1' hb2, fpE_ofOrd, fpE_ofOrd]
        by_cases hlo : finitePart β ≤ 3
        · rw [ite_eq_left hlo, ite_eq_left (hfp.trans hlo)]; exact evr_arg_mono_K 3 t hfp
        · rw [ite_eq_right hlo]
          split_ifs with hlo'
          · exact (evr_arg_mono_K 3 t hlo').trans h12
          · exact le_rfl
      · -- `b` in a later block: `a`'s value is at most `c₂`
        have hac : twoStripShifter t c₂ c₃ c₄ (ofOrd α) ≤ c₂ := by
          rw [ts_of_block₁ ha1' ha2]
          split_ifs with hlo
          · exact (evr_arg_mono_K 3 t hlo).trans h12
          · exact le_rfl
        by_cases hb3 : b < ofOrd (ωn 3)
        · rw [ts_of_block₂ (not_lt.mp hb2) hb3]
          split_ifs
          · exact hac.trans h23
          · exact hac.trans (h23.trans h34)
        · rw [ts_of_ge_three (not_lt.mp hb3)]; exact hac.trans (h23.trans h34)
    · have ha2' : ofOrd (ωn 2) ≤ a := not_lt.mp ha2
      have hb2' : ofOrd (ωn 2) ≤ b := ha2'.trans hab
      by_cases ha3 : a < ofOrd (ωn 3)
      · obtain ⟨α, rfl, hα2, hα3⟩ := ofOrd_of_block' 2 ha2' ha3
        by_cases hb3 : b < ofOrd (ωn 3)
        · obtain ⟨β, rfl, hβ2, hβ3⟩ := ofOrd_of_block' 2 hb2' hb3
          have hfp := fp_le_of_block' 2 hα2 hα3 hβ2 hβ3 (ofOrd_le_ofOrd.mp hab)
          rw [ts_of_block₂ ha2' ha3, ts_of_block₂ hb2' hb3, fpE_ofOrd, fpE_ofOrd]
          by_cases hlo : finitePart β ≤ 3
          · rw [ite_eq_left hlo, ite_eq_left (hfp.trans hlo)]
          · rw [ite_eq_right hlo]
            split_ifs
            · exact h34
            · exact le_rfl
        · rw [ts_of_ge_three (not_lt.mp hb3), ts_of_block₂ ha2' ha3]
          split_ifs
          · exact h34
          · exact le_rfl
      · have ha3' : ofOrd (ωn 3) ≤ a := not_lt.mp ha3
        rw [ts_of_ge_three ha3', ts_of_ge_three (ha3'.trans hab)]
  clause5 := by
    intro α k hk i hi
    by_cases hα : α = ⊥
    · rw [hα, ts_bot, extVisibilityReplace_bot, ts_bot]
    have hα' : extVisibilityReplace α k i ≠ ⊥ := extVisibilityReplace_ne_bot hα k i
    by_cases h1 : α < ofOrd (ωn 1)
    · rw [ts_of_lt_one hα h1, ts_of_lt_one hα' (evr_lt_limit h1 k i), extVisibilityReplace_bot]
    have h1' : ofOrd (ωn 1) ≤ α := not_lt.mp h1
    by_cases hkK : k ≤ 3
    · by_cases h2 : α < ofOrd (ωn 2)
      · obtain ⟨a, rfl, ha1, ha2⟩ := ofOrd_of_block' 1 h1' h2
        rw [ts_of_block₁ h1' h2, fpE_ofOrd,
          ts_of_block₁ (evr_ge_limit h1' k i) (evr_lt_limit h2 k i), extVisibilityReplace_ofOrd,
          fpE_ofOrd, finitePart_visibilityReplace]
        by_cases hlo : finitePart a ≤ 3
        · rw [ite_eq_left hlo, ite_eq_left (by split_ifs <;> omega)]
          have := orbit_eq_K 3 ht (j := finitePart a) hkK hi
          rw [min_eq_left hlo, min_eq_left (by split_ifs <;> omega)] at this
          exact this.symm
        · rw [ite_eq_right hlo, ite_eq_right (by split_ifs <;> omega),
            evr_eq_self_of_selfVis (hc₂.mono hkK)]
      · have h2' : ofOrd (ωn 2) ≤ α := not_lt.mp h2
        by_cases h3 : α < ofOrd (ωn 3)
        · obtain ⟨a, rfl, ha2, ha3⟩ := ofOrd_of_block' 2 h2' h3
          rw [ts_of_block₂ h2' h3, fpE_ofOrd,
            ts_of_block₂ (evr_ge_limit h2' k i) (evr_lt_limit h3 k i), extVisibilityReplace_ofOrd,
            fpE_ofOrd, finitePart_visibilityReplace]
          by_cases hlo : finitePart a ≤ 3
          · rw [ite_eq_left hlo, ite_eq_left (by split_ifs <;> omega),
              evr_eq_self_of_selfVis (hc₃.mono hkK)]
          · rw [ite_eq_right hlo, ite_eq_right (by split_ifs <;> omega),
              evr_eq_self_of_selfVis (hc₄.mono hkK)]
        · have h3' : ofOrd (ωn 3) ≤ α := not_lt.mp h3
          rw [ts_of_ge_three h3', ts_of_ge_three (evr_ge_limit h3' k i),
            evr_eq_self_of_selfVis (hc₄.mono hkK)]
    · rw [gTop_of_gt (by omega)] at hk
      have hσ := le_bot_iff.mp hk
      by_cases h2 : α < ofOrd (ωn 2)
      · -- the block at `ω`: bottom there forces `t = ⊥` and `c₂ = ⊥`
        have hboth : t = ⊥ ∧ c₂ = ⊥ := by
          rw [ts_of_block₁ h1' h2] at hσ
          split_ifs at hσ with hlo
          · have ht0 : t = ⊥ := by
              by_contra hne; exact extVisibilityReplace_ne_bot hne 3 _ hσ
            exact ⟨ht0, hb₁ ht0⟩
          · have ht0 : t = ⊥ := (R₃_eq_bot_iff t).mp (le_bot_iff.mp (h12.trans hσ.le))
            exact ⟨ht0, hσ⟩
        rw [ts_block₁_bot hboth.1 hboth.2 (evr_ge_limit h1' k i) (evr_lt_limit h2 k i),
          ts_block₁_bot hboth.1 hboth.2 h1' h2, extVisibilityReplace_bot]
      · have h2' : ofOrd (ωn 2) ≤ α := not_lt.mp h2
        by_cases h3 : α < ofOrd (ωn 3)
        · have hboth : c₃ = ⊥ ∧ c₄ = ⊥ := by
            rw [ts_of_block₂ h2' h3] at hσ
            split_ifs at hσ
            · exact ⟨hσ, hb₂ hσ⟩
            · exact ⟨le_bot_iff.mp (h34.trans hσ.le), hσ⟩
          rw [ts_block₂_bot hboth.1 hboth.2 (evr_ge_limit h2' k i) (evr_lt_limit h3 k i),
            ts_block₂_bot hboth.1 hboth.2 h2' h3, extVisibilityReplace_bot]
        · have h3' : ofOrd (ωn 3) ≤ α := not_lt.mp h3
          rw [ts_of_ge_three h3'] at hσ
          rw [ts_of_ge_three (evr_ge_limit h3' k i), ts_of_ge_three h3', hσ,
            extVisibilityReplace_bot]

/-! ### The strip at the actual sources -/

theorem ω1j_eq (j : ℕ) : ω1j j = ωn 1 + j := rfl
theorem ω2_eq (j : ℕ) : ω2 j = ωn 2 + j := rfl

theorem ts_v₀ : twoStripShifter t c₂ c₃ c₄ v₀ = extVisibilityReplace t 3 1 := by
  rw [v₀_num, ω1j_eq]; exact ts_ω1 1 (by decide)
theorem ts_η₁ : twoStripShifter t c₂ c₃ c₄ η₁ = extVisibilityReplace t 3 3 := by
  rw [η₁_num, ω1j_eq]; exact ts_ω1 3 le_rfl
theorem ts_γ₀ : twoStripShifter t c₂ c₃ c₄ γ₀ = c₂ := by
  rw [γ₀_num', ω1j_eq]; exact ts_ω1_hi 4 le_rfl
theorem ts_ω2_three : twoStripShifter t c₂ c₃ c₄ (ofOrd (ω2 3)) = c₃ := by
  rw [ω2_eq]; exact ts_ω2 3 le_rfl
theorem ts_ω2_four : twoStripShifter t c₂ c₃ c₄ (ofOrd (ω2 4)) = c₄ := by
  rw [ω2_eq]; exact ts_ω2_hi 4 le_rfl
theorem ts_γ₁ : twoStripShifter t c₂ c₃ c₄ γ₁ = c₃ := by rw [γ₁_num]; exact ts_ω2_three

end TwoStrip

/-! ## The admissible parameters and the sufficiency theorem -/

section Sufficiency

theorem memH₀new₃ : GradedLe (D₂.cell H₀new) (Finset.univ, 3) := memB (by decide)
theorem memU_H₃ : GradedLe (D₂.cell U_H) (Finset.univ, 3) := by
  rw [cell_U_H]; exact ⟨Finset.subset_univ _, by decide⟩
theorem mems₀old₃ : GradedLe (D₂.cell s₀old) (Finset.univ, 3) :=
  ⟨Finset.subset_univ _, by change D₂.grade s₀old ≤ 3; rw [grade_s₀old]; decide⟩
theorem mems₀new₃ : GradedLe (D₂.cell s₀new) (Finset.univ, 3) :=
  ⟨Finset.subset_univ _, by change D₂.grade s₀new ≤ 3; rw [grade_s₀new]; decide⟩

/-- **The admissible grade-three parameters** over legal grade-two ones: the caps ordered below
the old occurrence and the high label, the high label below the grade-two controller, grade-three
visibility of the caps, the high label and `min x₀ w`, the exact orbit `z₁ = R₃ (min vP w)`, the
fixing law at `(3, 1)`, and the two bottom couplings. -/
structure Legal₃ (vP x₀ x₁ H z₁ z₂ w : ExtOrd) : Prop where
  two : Legal₂ vP x₀ x₁ H
  z12 : z₁ ≤ z₂
  z2x : z₂ ≤ x₀
  z2w : z₂ ≤ w
  wH : w ≤ H
  vis1 : SelfVis 3 z₁
  vis2 : SelfVis 3 z₂
  visw : SelfVis 3 w
  vismin : SelfVis 3 (min x₀ w)
  orbit : z₁ = extVisibilityReplace (min vP w) 3 3
  fix : extVisibilityReplace (min vP w) 3 1 = min vP w
  coup₃ : z₁ = ⊥ → z₂ = ⊥
  coup₄ : min x₀ w = ⊥ → w = ⊥

namespace Legal₃

variable {vP x₀ x₁ H z₁ z₂ w : ExtOrd} (L : Legal₃ vP x₀ x₁ H z₁ z₂ w)
include L

theorem z1w : z₁ ≤ w := L.z12.trans L.z2w
theorem z1x : z₁ ≤ x₀ := L.z12.trans L.z2x
theorem z2m : z₂ ≤ min x₀ w := le_min L.z2x L.z2w
theorem wx₁ : w ≤ x₁ := L.wH.trans L.two.Hle
theorem z1_le_minxH : z₁ ≤ min x₀ H := le_min L.z1x (L.z1w.trans L.wH)
theorem z2_le_minxH : z₂ ≤ min x₀ H := le_min L.z2x (L.z2w.trans L.wH)
theorem min_minxH_w : min (min x₀ H) w = min x₀ w := by
  rw [min_assoc, min_eq_right L.wH]

/-- With `z₁ < vP`, the lowest cap equals the high label. -/
theorem z1_eq_w_of_lt (h : z₁ < vP) : z₁ = w := by
  rcases le_or_gt vP w with hvw | hwv
  · exfalso
    have := L.orbit
    rw [min_eq_left hvw] at this
    exact absurd (this ▸ le_extVisibilityReplace_self vP 3) (not_le.mpr h)
  · have := L.orbit
    rw [min_eq_right hwv.le, evr_eq_self_of_selfVis L.visw] at this
    exact this

/-- **The orbit at any cap between the lowest and the high label** reads the lowest cap. -/
theorem R₃_min_eq {a : ExtOrd} (h1 : z₁ ≤ a) (h2 : a ≤ w) :
    extVisibilityReplace (min vP a) 3 3 = z₁ := by
  rcases le_or_gt vP z₁ with hv | hv
  · rw [min_eq_left (hv.trans h1), L.orbit, min_eq_left (hv.trans L.z1w)]
  · have hw := L.z1_eq_w_of_lt hv
    have ha' : a = z₁ := le_antisymm (hw ▸ h2) h1
    rw [ha', min_eq_right hv.le, evr_eq_self_of_selfVis L.vis1]

theorem fix_min_eq {a : ExtOrd} (h1 : z₁ ≤ a) (h2 : a ≤ w) :
    extVisibilityReplace (min vP a) 3 1 = min vP a := by
  rcases le_or_gt vP z₁ with hv | hv
  · rw [min_eq_left (hv.trans h1)]
    have := L.fix
    rwa [min_eq_left (hv.trans L.z1w)] at this
  · have hw := L.z1_eq_w_of_lt hv
    have ha' : a = z₁ := le_antisymm (hw ▸ h2) h1
    rw [ha', min_eq_right hv.le]
    exact fix₃₁_of_selfVis₃ L.vis1

theorem selfVis₁_min {a : ExtOrd} (ha : SelfVis 3 a) : SelfVis 1 (min vP a) :=
  selfVis_min' L.two.visP (ha.mono (by omega))

theorem R₃_min_eq_bot {a : ExtOrd} (h : min vP a = ⊥) (h1 : z₁ ≤ a) (h2 : a ≤ w) : z₁ = ⊥ := by
  rw [← L.R₃_min_eq h1 h2, h, extVisibilityReplace_bot]

theorem R₃_t_eq : extVisibilityReplace (min vP w) 3 3 = z₁ := L.orbit.symm
theorem selfVis₁_t : SelfVis 1 (min vP w) := L.selfVis₁_min L.visw
theorem z2_eq_bot_of_t (h : min vP w = ⊥) : z₂ = ⊥ :=
  L.coup₃ (by rw [L.orbit, h, extVisibilityReplace_bot])

end Legal₃

/-- **The value shape** of a grade-three labelling. -/
structure Shape₃ (r : D₂.below (Finset.univ, 3) → ExtOrd) (vP x₀ x₁ H z₁ z₂ w : ExtOrd) : Prop where
  at_H₀old : r ⟨H₀old, memH₀old₃⟩ = x₀
  at_H₀new : r ⟨H₀new, memH₀new₃⟩ = x₁
  at_U_H : r ⟨U_H, memU_H₃⟩ = x₁
  at_s₀old : r ⟨s₀old, mems₀old₃⟩ = min x₀ H
  at_s₀new : r ⟨s₀new, mems₀new₃⟩ = H
  at_U_S : r ⟨U_S, memU_S₃⟩ = H
  at_a₁old : r ⟨a₁old, mema₁old₃⟩ = z₁
  at_A₁c : r ⟨A₁c, memA₁c₃⟩ = z₁
  at_a₂old : r ⟨a₂old, mema₂old₃⟩ = z₂
  at_A₂c : r ⟨A₂c, memA₂c₃⟩ = z₂
  at_b₁new : r ⟨b₁new, memb₁new₃⟩ = w
  at_ub₁ : r ⟨ub₁, memub₁₃⟩ = w
  at_proper : ∀ d : D₂.below (Finset.univ, 3), IsProper d.1 →
    r d = if D₂.grade d.1 = 2 then ⊥ else vP

theorem Shape₃.two {r : D₂.below (Finset.univ, 3) → ExtOrd} {vP x₀ x₁ H z₁ z₂ w : ExtOrd}
    (S : Shape₃ r vP x₀ x₁ H z₁ z₂ w) :
    Shape₂ (fun d => r (CellScheme.below.mono h₂₃ d)) vP x₀ x₁ H where
  at_H₀old := S.at_H₀old
  at_H₀new := S.at_H₀new
  at_U_H := S.at_U_H
  at_s₀old := S.at_s₀old
  at_s₀new := S.at_s₀new
  at_U_S := S.at_U_S
  at_proper d hd := S.at_proper (CellScheme.below.mono h₂₃ d) hd

/-- Below an old cap: the old witnesses, the two old caps, or a proper cell. -/
theorem below_Aold_cases {d : Cell D₂} (hd : ¬ mute₂ d)
    (h : GradedLe (D₂.cell d) (({0, 1, 2} : Finset (Fin 4)), 3)) :
    d = H₀old ∨ d = s₀old ∨ d = a₁old ∨ d = a₂old ∨ IsProper d := by
  have hs : D₂.scope d ⊆ ({0, 1, 2} : Finset (Fin 4)) := h.1
  have h3 : (3 : Fin 4) ∉ D₂.scope d := fun h3 => by
    have := hs h3; revert this; decide
  by_cases hg : D₂.grade d = 3
  · rcases three_cases hd hg with e | e | e | e | e | e
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · exact absurd (e ▸ three_mem_scope_b₁new) h3
    · exact absurd (e ▸ three_mem_scope_A₁c) h3
    · exact absurd (e ▸ three_mem_scope_A₂c) h3
    · exact absurd (e ▸ three_mem_scope_ub₁) h3
  · have hg2 : D₂.grade d ≤ 2 := by have := h.2; change D₂.grade d ≤ 3 at this; omega
    rcases two_cases hd hg2 with e | e | e | e | e | e | ⟨e, -⟩ | ⟨e, -⟩
    · exact Or.inl e
    · exact absurd (e ▸ three_mem_scope_H₀new) h3
    · exact absurd (e ▸ three_mem_scope_U_H) h3
    · exact Or.inr (Or.inl e)
    · exact absurd (e ▸ three_mem_scope_s₀new) h3
    · exact absurd (e ▸ three_mem_scope_U_S) h3
    · exact Or.inr (Or.inr (Or.inr (Or.inr e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr e)))

theorem aFace_a₁old : AFace a₁old := aFace_castAdd _
theorem aFace_a₂old : AFace a₂old := aFace_castAdd _

/-- The rows of the `a₁` cells and of `A₁c` at a proper cell. -/
theorem rowX_a₁_proper {d : Cell D₂} (hd : ¬ mute₂ d) (hp : IsProper d) :
    pull a₁X d = if D₂.grade d = 2 then ⊥ else v₀ := by
  obtain ⟨c, hc⟩ := hp
  rw [pull_of_not_mute _ hd, hc, rowX_a₁_inl]
  by_cases hg : D₂.grade d = 2
  · rw [ite_eq_left hg, t₀_F_bot (by rw [gradeP_le_of_proper hd hc]; exact hg)]
  · rw [ite_eq_right hg, t₀_F_v₀ (by
      have := c.gradeP_le_two; rw [gradeP_le_of_proper hd hc] at this ⊢; omega)]
theorem rowX_a₂_proper {d : Cell D₂} (hd : ¬ mute₂ d) (hp : IsProper d) :
    pull a₂X d = if D₂.grade d = 2 then ⊥ else v₀ := by
  obtain ⟨c, hc⟩ := hp
  rw [pull_of_not_mute _ hd, hc, rowX_a₂_inl]
  by_cases hg : D₂.grade d = 2
  · rw [ite_eq_left hg, t₀_F_bot (by rw [gradeP_le_of_proper hd hc]; exact hg)]
  · rw [ite_eq_right hg, t₀_F_v₀ (by
      have := c.gradeP_le_two; rw [gradeP_le_of_proper hd hc] at this ⊢; omega)]
theorem qM_proper' {d : Cell D₂} (hd : ¬ mute₂ d) (hp : IsProper d) :
    qM d = if D₂.grade d = 2 then ⊥ else v₀ := by
  obtain ⟨c, hc⟩ := hp
  rw [qM_of_proper hd hc]
  by_cases hg : D₂.grade d = 2
  · rw [ite_eq_left hg, t₀_F_bot (by rw [gradeP_le_of_proper hd hc]; exact hg)]
  · rw [ite_eq_right hg, t₀_F_v₀ (by
      have := c.gradeP_le_two; rw [gradeP_le_of_proper hd hc] at this ⊢; omega)]

/-- The proper source and its two-strip value, against the shaped target. -/
theorem ts_proper_target {t c₂ c₃ c₄ vP a : ExtOrd} (hfix : extVisibilityReplace t 3 1 = t)
    (ht : t = min vP a) (g : ℕ) :
    twoStripShifter t c₂ c₃ c₄ (if g = 2 then ⊥ else v₀) = min (if g = 2 then ⊥ else vP) a := by
  split_ifs
  · rw [ts_bot, min_eq_left bot_le]
  · rw [ts_v₀, hfix, ht]

end Sufficiency

/-! ## The sufficiency theorem -/

section SufficiencyProof

theorem rowsR_E_b₁new' (d : D₂.below (D₂.cell b₁new)) : rowsR.E b₁new d = pull b₁X d.1 := by
  have hB : BFace b₁new := copyB_mem _
  rw [rowsR_E_of_B hB d, rows₂_E_eq_pull not_mute_b₁new, ret₂_b₁new, Equiv.symm_apply_apply]
theorem rowX_b₁_proper {d : Cell D₂} (hd : ¬ mute₂ d) (hp : IsProper d) :
    pull b₁X d = if D₂.grade d = 2 then ⊥ else v₀ := by
  obtain ⟨c, hc⟩ := hp
  rw [pull_of_not_mute _ hd, hc, rowX_b₁_inl]
  by_cases hg : D₂.grade d = 2
  · rw [ite_eq_left hg, t₀_F_bot (by rw [gradeP_le_of_proper hd hc]; exact hg)]
  · rw [ite_eq_right hg, t₀_F_v₀ (by
      have := c.gradeP_le_two; rw [gradeP_le_of_proper hd hc] at this ⊢; omega)]
theorem rowsR_E_A₁c' (d : D₂.below (D₂.cell A₁c)) : rowsR.E A₁c d = pull a₁X d.1 :=
  (rowsR_E_A₁c d).trans (E₃_A₁c d)
theorem rowsR_E_A₂c' (d : D₂.below (D₂.cell A₂c)) : rowsR.E A₂c d = pull a₂X d.1 :=
  (rowsR_E_A₂c d).trans (E₃_A₂c d)
theorem rowsR_E_a₁old' (d : D₂.below (D₂.cell a₁old)) : rowsR.E a₁old d = pull a₁X d.1 :=
  (rowsR_E_a₁old d).trans (rows₃_a₁old_eq d)
theorem rowsR_E_a₂old' (d : D₂.below (D₂.cell a₂old)) : rowsR.E a₂old d = pull a₂X d.1 := by
  have hA : AFace a₂old := aFace_castAdd _
  rw [rowsR_E_of_A hA d, rows₂_a₂old_eq]

theorem below_a₁old_mem (d : D₂.below (D₂.cell a₁old)) :
    GradedLe (D₂.cell d.1) (({0, 1, 2} : Finset (Fin 4)), 3) :=
  d.2.trans (by rw [cell_a₁old]; exact GradedLe.refl _)
theorem below_a₂old_mem (d : D₂.below (D₂.cell a₂old)) :
    GradedLe (D₂.cell d.1) (({0, 1, 2} : Finset (Fin 4)), 3) :=
  d.2.trans (by rw [cell_a₂old]; exact GradedLe.refl _)
theorem below_full₃_mem {X : Cell D₂} (hX : D₂.cell X = (Finset.univ, 3))
    (d : D₂.below (D₂.cell X)) : GradedLe (D₂.cell d.1) (Finset.univ, 3) :=
  d.2.trans (by rw [hX]; exact GradedLe.refl _)

/-- **Sufficiency**: admissible parameters in the value shape give a labelling respecting the
repaired semantics on the full grade-three lower set. -/
theorem respects_of_shape₃ {r : D₂.below (Finset.univ, 3) → ExtOrd} {vP x₀ x₁ H z₁ z₂ w : ExtOrd}
    (L : Legal₃ vP x₀ x₁ H z₁ z₂ w) (S : Shape₃ r vP x₀ x₁ H z₁ z₂ w) :
    RespectsSemanticsBelow rowsR (Finset.univ, 3) r := by
  have hr₂ : RespectsSemanticsBelow rows₃ (Finset.univ, 2)
      (fun d => r (CellScheme.below.mono h₂₃ d)) := respects_of_shape₂ L.two S.two
  have hnm : ∀ d : D₂.below (Finset.univ, 3), ¬ mute₂ d.1 := fun d => not_mute₂_of_low le_rfl d
  -- the witnesses
  have wA₁ : Witness (gTop 3) (twoStripShifter (min vP z₁) z₁ z₁ z₁) :=
    Witness.twoStrip (L.selfVis₁_min L.vis1) L.vis1 L.vis1 L.vis1 (L.R₃_min_eq le_rfl L.z1w).le
      le_rfl le_rfl (fun h => L.R₃_min_eq_bot h le_rfl L.z1w) id
  have wA₂ : Witness (gTop 3) (twoStripShifter (min vP z₂) z₂ z₂ z₂) :=
    Witness.twoStrip (L.selfVis₁_min L.vis2) L.vis2 L.vis2 L.vis2
      ((L.R₃_min_eq L.z12 L.z2w).trans_le L.z12) le_rfl le_rfl
      (fun h => L.coup₃ (L.R₃_min_eq_bot h L.z12 L.z2w)) id
  have wB : Witness (gTop 3) (twoStripShifter (min vP w) z₁ w w) :=
    Witness.twoStrip L.selfVis₁_t L.vis1 L.visw L.visw L.R₃_t_eq.le L.z1w le_rfl
      (fun h => by rw [L.orbit, h, extVisibilityReplace_bot]) id
  have wU : Witness (gTop 3) (twoStripShifter (min vP w) z₂ (min x₀ w) w) :=
    Witness.twoStrip L.selfVis₁_t L.vis2 L.vismin L.visw (L.R₃_t_eq.trans_le L.z12) L.z2m
      (min_le_right _ _) L.z2_eq_bot_of_t L.coup₄
  have hR₁ : extVisibilityReplace (min vP z₁) 3 3 = z₁ := L.R₃_min_eq le_rfl L.z1w
  have hR₂ : extVisibilityReplace (min vP z₂) 3 3 = z₁ := L.R₃_min_eq L.z12 L.z2w
  have hF₁ := L.fix_min_eq le_rfl L.z1w
  have hF₂ := L.fix_min_eq L.z12 L.z2w
  -- every grade-three label is at most the high label
  have hle_w : ∀ d : D₂.below (Finset.univ, 3), D₂.grade d.1 = 3 → r d ≤ w := by
    intro d hg
    rcases three_cases (hnm d) hg with h | h | h | h | h | h
    · rw [show d = ⟨a₁old, mema₁old₃⟩ from Subtype.ext h, S.at_a₁old]; exact L.z1w
    · rw [show d = ⟨a₂old, mema₂old₃⟩ from Subtype.ext h, S.at_a₂old]; exact L.z2w
    · rw [show d = ⟨b₁new, memb₁new₃⟩ from Subtype.ext h, S.at_b₁new]
    · rw [show d = ⟨A₁c, memA₁c₃⟩ from Subtype.ext h, S.at_A₁c]; exact L.z1w
    · rw [show d = ⟨A₂c, memA₂c₃⟩ from Subtype.ext h, S.at_A₂c]; exact L.z2w
    · rw [show d = ⟨ub₁, memub₁₃⟩ from Subtype.ext h, S.at_ub₁]
  refine ⟨?_, ?_, ?_⟩
  · -- orderly
    intro d
    change r d = extVisibilityReplace (r d) (D₂.grade d.1) (D₂.grade d.1)
    by_cases hg3 : D₂.grade d.1 = 3
    · rw [hg3]
      rcases three_cases (hnm d) hg3 with h | h | h | h | h | h
      · rw [show d = ⟨a₁old, mema₁old₃⟩ from Subtype.ext h, S.at_a₁old]; exact L.vis1.symm
      · rw [show d = ⟨a₂old, mema₂old₃⟩ from Subtype.ext h, S.at_a₂old]; exact L.vis2.symm
      · rw [show d = ⟨b₁new, memb₁new₃⟩ from Subtype.ext h, S.at_b₁new]; exact L.visw.symm
      · rw [show d = ⟨A₁c, memA₁c₃⟩ from Subtype.ext h, S.at_A₁c]; exact L.vis1.symm
      · rw [show d = ⟨A₂c, memA₂c₃⟩ from Subtype.ext h, S.at_A₂c]; exact L.vis2.symm
      · rw [show d = ⟨ub₁, memub₁₃⟩ from Subtype.ext h, S.at_ub₁]; exact L.visw.symm
    · have hg2 : D₂.grade d.1 ≤ 2 := by have := d.2.2; change D₂.grade d.1 ≤ 3 at this; omega
      have := hr₂.orderly ⟨d.1, ⟨Finset.subset_univ _, hg2⟩⟩
      rwa [show CellScheme.below.mono h₂₃ ⟨d.1, ⟨Finset.subset_univ _, hg2⟩⟩ = d from
        Subtype.ext rfl] at this
  · -- locality
    intro Sig
    obtain ⟨x, hx⟩ := Sig
    have hnx : ¬ mute₂ x := hnm ⟨x, hx⟩
    by_cases hg3 : D₂.grade x = 3
    · rcases three_cases hnx hg3 with rfl | rfl | rfl | rfl | rfl | rfl
      · -- the old cap `a₁`
        refine wA₁.transformsTo fun d => ?_
        rw [gTop_of_le (K := 3) (k := D₂.grade d.1) (d.2.2.trans grade_a₁old.le),
          min_eq_left le_top]
        change min (r (CellScheme.below.incl ⟨a₁old, hx⟩ d)) (r ⟨a₁old, mema₁old₃⟩) = _
        rw [S.at_a₁old, rowsR_E_a₁old' d]
        have hnd : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_a₁old d.2
        rcases below_Aold_cases hnd (below_a₁old_mem d) with hd | hd | hd | hd | hd
        · rw [show CellScheme.below.incl ⟨a₁old, hx⟩ d = ⟨H₀old, memH₀old₃⟩ from Subtype.ext hd,
            S.at_H₀old, min_eq_right L.z1x, hd, pull_eq_rowX _ not_mute_H₀old ret₂_H₀old, rowX_a₁_H,
            ts_η₁, hR₁]
        · rw [show CellScheme.below.incl ⟨a₁old, hx⟩ d = ⟨s₀old, mems₀old₃⟩ from Subtype.ext hd,
            S.at_s₀old, min_eq_right L.z1_le_minxH, hd, pull_eq_rowX _ not_mute_s₀old ret₂_s₀old,
            rowX_a₁_s, ts_η₁, hR₁]
        · rw [show CellScheme.below.incl ⟨a₁old, hx⟩ d = ⟨a₁old, mema₁old₃⟩ from Subtype.ext hd,
            S.at_a₁old, min_self, hd, pull_eq_rowX _ not_mute_a₁old ret₂_a₁old, rowX_a₁_a₁, ts_η₁,
            hR₁]
        · rw [show CellScheme.below.incl ⟨a₁old, hx⟩ d = ⟨a₂old, mema₂old₃⟩ from Subtype.ext hd,
            S.at_a₂old, min_eq_right L.z12, hd, pull_eq_rowX _ not_mute_a₂old ret₂_a₂old,
            rowX_a₁_a₂, ts_η₁, hR₁]
        · rw [S.at_proper (CellScheme.below.incl ⟨a₁old, hx⟩ d) hd, rowX_a₁_proper hnd hd]
          exact (ts_proper_target hF₁ rfl _).symm
      · -- the old cap `a₂`
        refine wA₂.transformsTo fun d => ?_
        rw [gTop_of_le (K := 3) (k := D₂.grade d.1) (d.2.2.trans grade_a₂old.le),
          min_eq_left le_top]
        change min (r (CellScheme.below.incl ⟨a₂old, hx⟩ d)) (r ⟨a₂old, mema₂old₃⟩) = _
        rw [S.at_a₂old, rowsR_E_a₂old' d]
        have hnd : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_a₂old d.2
        rcases below_Aold_cases hnd (below_a₂old_mem d) with hd | hd | hd | hd | hd
        · rw [show CellScheme.below.incl ⟨a₂old, hx⟩ d = ⟨H₀old, memH₀old₃⟩ from Subtype.ext hd,
            S.at_H₀old, min_eq_right L.z2x, hd, pull_eq_rowX _ not_mute_H₀old ret₂_H₀old, rowX_a₂_H,
            ts_γ₀]
        · rw [show CellScheme.below.incl ⟨a₂old, hx⟩ d = ⟨s₀old, mems₀old₃⟩ from Subtype.ext hd,
            S.at_s₀old, min_eq_right L.z2_le_minxH, hd, pull_eq_rowX _ not_mute_s₀old ret₂_s₀old,
            rowX_a₂_s, ts_γ₀]
        · rw [show CellScheme.below.incl ⟨a₂old, hx⟩ d = ⟨a₁old, mema₁old₃⟩ from Subtype.ext hd,
            S.at_a₁old, min_eq_left L.z12, hd, pull_eq_rowX _ not_mute_a₁old ret₂_a₁old, rowX_a₂_a₁,
            ts_η₁, hR₂]
        · rw [show CellScheme.below.incl ⟨a₂old, hx⟩ d = ⟨a₂old, mema₂old₃⟩ from Subtype.ext hd,
            S.at_a₂old, min_self, hd, pull_eq_rowX _ not_mute_a₂old ret₂_a₂old, rowX_a₂_a₂, ts_γ₀]
        · rw [S.at_proper (CellScheme.below.incl ⟨a₂old, hx⟩ d) hd, rowX_a₂_proper hnd hd]
          exact (ts_proper_target hF₂ rfl _).symm
      · -- the copy of `b₁`
        refine wB.transformsTo fun d => ?_
        rw [gTop_of_le (K := 3) (k := D₂.grade d.1) (d.2.2.trans grade_b₁new.le),
          min_eq_left le_top]
        change min (r (CellScheme.below.incl ⟨b₁new, hx⟩ d)) (r ⟨b₁new, memb₁new₃⟩) = _
        rw [S.at_b₁new, rowsR_E_b₁new' d]
        have hnd : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_b₁new d.2
        rcases below_b₁new_cases d with hd | hd | hd | hd
        · rw [show CellScheme.below.incl ⟨b₁new, hx⟩ d = ⟨b₁new, memb₁new₃⟩ from Subtype.ext hd,
            S.at_b₁new, min_self, hd, pull_eq_rowX _ not_mute_b₁new ret₂_b₁new, rowX_b₁_b₁, ts_γ₁]
        · rw [show CellScheme.below.incl ⟨b₁new, hx⟩ d = ⟨H₀new, memH₀new₃⟩ from Subtype.ext hd,
            S.at_H₀new, min_eq_right L.wx₁, hd, pull_eq_rowX _ not_mute_H₀new ret₂_H₀new, rowX_b₁_H,
            ts_γ₁]
        · rw [show CellScheme.below.incl ⟨b₁new, hx⟩ d = ⟨s₀new, mems₀new₃⟩ from Subtype.ext hd,
            S.at_s₀new, min_eq_right L.wH, hd, pull_eq_rowX _ not_mute_s₀new ret₂_s₀new, rowX_b₁_s,
            ts_γ₁]
        · rw [S.at_proper (CellScheme.below.incl ⟨b₁new, hx⟩ d) hd, rowX_b₁_proper hnd hd]
          exact (ts_proper_target L.fix rfl _).symm
      · -- `a₁`'s controller
        refine wA₁.transformsTo fun d => ?_
        rw [gTop_of_le (K := 3) (k := D₂.grade d.1) (below_full₃_mem cell_A₁c d).2,
          min_eq_left le_top]
        change min (r (CellScheme.below.incl ⟨A₁c, hx⟩ d)) (r ⟨A₁c, memA₁c₃⟩) = _
        rw [S.at_A₁c, rowsR_E_A₁c' d]
        have hnd : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_A₁c d.2
        by_cases hd3 : D₂.grade d.1 = 3
        · rcases three_cases hnd hd3 with hd | hd | hd | hd | hd | hd
          · rw [show CellScheme.below.incl ⟨A₁c, hx⟩ d = ⟨a₁old, mema₁old₃⟩ from Subtype.ext hd,
              S.at_a₁old, min_self, hd, pull_eq_rowX _ not_mute_a₁old ret₂_a₁old, rowX_a₁_a₁, ts_η₁,
              hR₁]
          · rw [show CellScheme.below.incl ⟨A₁c, hx⟩ d = ⟨a₂old, mema₂old₃⟩ from Subtype.ext hd,
              S.at_a₂old, min_eq_right L.z12, hd, pull_eq_rowX _ not_mute_a₂old ret₂_a₂old,
              rowX_a₁_a₂, ts_η₁, hR₁]
          · rw [show CellScheme.below.incl ⟨A₁c, hx⟩ d = ⟨b₁new, memb₁new₃⟩ from Subtype.ext hd,
              S.at_b₁new, min_eq_right L.z1w, hd, pull_eq_rowX _ not_mute_b₁new ret₂_b₁new,
              rowX_a₁_b₁, ts_η₁, hR₁]
          · rw [show CellScheme.below.incl ⟨A₁c, hx⟩ d = ⟨A₁c, memA₁c₃⟩ from Subtype.ext hd,
              S.at_A₁c, min_self, hd, pull_eq_rowX _ not_mute_A₁c ret₂_A₁c, rowX_a₁_a₁, ts_η₁, hR₁]
          · rw [show CellScheme.below.incl ⟨A₁c, hx⟩ d = ⟨A₂c, memA₂c₃⟩ from Subtype.ext hd,
              S.at_A₂c, min_eq_right L.z12, hd, pull_eq_rowX _ not_mute_A₂c ret₂_A₂c, rowX_a₁_a₂,
              ts_η₁, hR₁]
          · rw [show CellScheme.below.incl ⟨A₁c, hx⟩ d = ⟨ub₁, memub₁₃⟩ from Subtype.ext hd,
              S.at_ub₁, min_eq_right L.z1w, hd, pull_eq_rowX _ not_mute_ub₁ ret₂_ub₁, rowX_a₁_b₁,
              ts_η₁, hR₁]
        · have hd2 : D₂.grade d.1 ≤ 2 := by
            have := (below_full₃_mem cell_A₁c d).2; change D₂.grade d.1 ≤ 3 at this; omega
          rcases two_cases hnd hd2 with hd | hd | hd | hd | hd | hd | ⟨hd, -⟩ | ⟨hd, -⟩
          · rw [show CellScheme.below.incl ⟨A₁c, hx⟩ d = ⟨H₀old, memH₀old₃⟩ from Subtype.ext hd,
              S.at_H₀old, min_eq_right L.z1x, hd, pull_eq_rowX _ not_mute_H₀old ret₂_H₀old,
              rowX_a₁_H, ts_η₁, hR₁]
          · rw [show CellScheme.below.incl ⟨A₁c, hx⟩ d = ⟨H₀new, memH₀new₃⟩ from Subtype.ext hd,
              S.at_H₀new, min_eq_right (L.z1x.trans L.two.le01), hd,
              pull_eq_rowX _ not_mute_H₀new ret₂_H₀new, rowX_a₁_H, ts_η₁, hR₁]
          · rw [show CellScheme.below.incl ⟨A₁c, hx⟩ d = ⟨U_H, memU_H₃⟩ from Subtype.ext hd,
              S.at_U_H, min_eq_right (L.z1x.trans L.two.le01), hd,
              pull_eq_rowX _ not_mute_U_H ret₂_U_H, rowX_a₁_H, ts_η₁, hR₁]
          · rw [show CellScheme.below.incl ⟨A₁c, hx⟩ d = ⟨s₀old, mems₀old₃⟩ from Subtype.ext hd,
              S.at_s₀old, min_eq_right L.z1_le_minxH, hd, pull_eq_rowX _ not_mute_s₀old ret₂_s₀old,
              rowX_a₁_s, ts_η₁, hR₁]
          · rw [show CellScheme.below.incl ⟨A₁c, hx⟩ d = ⟨s₀new, mems₀new₃⟩ from Subtype.ext hd,
              S.at_s₀new, min_eq_right (L.z1w.trans L.wH), hd,
              pull_eq_rowX _ not_mute_s₀new ret₂_s₀new, rowX_a₁_s, ts_η₁, hR₁]
          · rw [show CellScheme.below.incl ⟨A₁c, hx⟩ d = ⟨U_S, memU_S₃⟩ from Subtype.ext hd,
              S.at_U_S, min_eq_right (L.z1w.trans L.wH), hd, pull_eq_rowX _ not_mute_U_S ret₂_U_S,
              rowX_a₁_s, ts_η₁, hR₁]
          · rw [S.at_proper (CellScheme.below.incl ⟨A₁c, hx⟩ d) hd, rowX_a₁_proper hnd hd]
            exact (ts_proper_target hF₁ rfl _).symm
          · rw [S.at_proper (CellScheme.below.incl ⟨A₁c, hx⟩ d) hd, rowX_a₁_proper hnd hd]
            exact (ts_proper_target hF₁ rfl _).symm
      · -- `a₂`'s controller
        refine wA₂.transformsTo fun d => ?_
        rw [gTop_of_le (K := 3) (k := D₂.grade d.1) (below_full₃_mem cell_A₂c d).2,
          min_eq_left le_top]
        change min (r (CellScheme.below.incl ⟨A₂c, hx⟩ d)) (r ⟨A₂c, memA₂c₃⟩) = _
        rw [S.at_A₂c, rowsR_E_A₂c' d]
        have hnd : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_A₂c d.2
        by_cases hd3 : D₂.grade d.1 = 3
        · rcases three_cases hnd hd3 with hd | hd | hd | hd | hd | hd
          · rw [show CellScheme.below.incl ⟨A₂c, hx⟩ d = ⟨a₁old, mema₁old₃⟩ from Subtype.ext hd,
              S.at_a₁old, min_eq_left L.z12, hd, pull_eq_rowX _ not_mute_a₁old ret₂_a₁old,
              rowX_a₂_a₁, ts_η₁, hR₂]
          · rw [show CellScheme.below.incl ⟨A₂c, hx⟩ d = ⟨a₂old, mema₂old₃⟩ from Subtype.ext hd,
              S.at_a₂old, min_self, hd, pull_eq_rowX _ not_mute_a₂old ret₂_a₂old, rowX_a₂_a₂, ts_γ₀]
          · rw [show CellScheme.below.incl ⟨A₂c, hx⟩ d = ⟨b₁new, memb₁new₃⟩ from Subtype.ext hd,
              S.at_b₁new, min_eq_right L.z2w, hd, pull_eq_rowX _ not_mute_b₁new ret₂_b₁new,
              rowX_a₂_b₁, ts_γ₀]
          · rw [show CellScheme.below.incl ⟨A₂c, hx⟩ d = ⟨A₁c, memA₁c₃⟩ from Subtype.ext hd,
              S.at_A₁c, min_eq_left L.z12, hd, pull_eq_rowX _ not_mute_A₁c ret₂_A₁c, rowX_a₂_a₁,
              ts_η₁, hR₂]
          · rw [show CellScheme.below.incl ⟨A₂c, hx⟩ d = ⟨A₂c, memA₂c₃⟩ from Subtype.ext hd,
              S.at_A₂c, min_self, hd, pull_eq_rowX _ not_mute_A₂c ret₂_A₂c, rowX_a₂_a₂, ts_γ₀]
          · rw [show CellScheme.below.incl ⟨A₂c, hx⟩ d = ⟨ub₁, memub₁₃⟩ from Subtype.ext hd,
              S.at_ub₁, min_eq_right L.z2w, hd, pull_eq_rowX _ not_mute_ub₁ ret₂_ub₁, rowX_a₂_b₁,
              ts_γ₀]
        · have hd2 : D₂.grade d.1 ≤ 2 := by
            have := (below_full₃_mem cell_A₂c d).2; change D₂.grade d.1 ≤ 3 at this; omega
          rcases two_cases hnd hd2 with hd | hd | hd | hd | hd | hd | ⟨hd, -⟩ | ⟨hd, -⟩
          · rw [show CellScheme.below.incl ⟨A₂c, hx⟩ d = ⟨H₀old, memH₀old₃⟩ from Subtype.ext hd,
              S.at_H₀old, min_eq_right L.z2x, hd, pull_eq_rowX _ not_mute_H₀old ret₂_H₀old,
              rowX_a₂_H, ts_γ₀]
          · rw [show CellScheme.below.incl ⟨A₂c, hx⟩ d = ⟨H₀new, memH₀new₃⟩ from Subtype.ext hd,
              S.at_H₀new, min_eq_right (L.z2x.trans L.two.le01), hd,
              pull_eq_rowX _ not_mute_H₀new ret₂_H₀new, rowX_a₂_H, ts_γ₀]
          · rw [show CellScheme.below.incl ⟨A₂c, hx⟩ d = ⟨U_H, memU_H₃⟩ from Subtype.ext hd,
              S.at_U_H, min_eq_right (L.z2x.trans L.two.le01), hd,
              pull_eq_rowX _ not_mute_U_H ret₂_U_H, rowX_a₂_H, ts_γ₀]
          · rw [show CellScheme.below.incl ⟨A₂c, hx⟩ d = ⟨s₀old, mems₀old₃⟩ from Subtype.ext hd,
              S.at_s₀old, min_eq_right L.z2_le_minxH, hd, pull_eq_rowX _ not_mute_s₀old ret₂_s₀old,
              rowX_a₂_s, ts_γ₀]
          · rw [show CellScheme.below.incl ⟨A₂c, hx⟩ d = ⟨s₀new, mems₀new₃⟩ from Subtype.ext hd,
              S.at_s₀new, min_eq_right (L.z2w.trans L.wH), hd,
              pull_eq_rowX _ not_mute_s₀new ret₂_s₀new, rowX_a₂_s, ts_γ₀]
          · rw [show CellScheme.below.incl ⟨A₂c, hx⟩ d = ⟨U_S, memU_S₃⟩ from Subtype.ext hd,
              S.at_U_S, min_eq_right (L.z2w.trans L.wH), hd, pull_eq_rowX _ not_mute_U_S ret₂_U_S,
              rowX_a₂_s, ts_γ₀]
          · rw [S.at_proper (CellScheme.below.incl ⟨A₂c, hx⟩ d) hd, rowX_a₂_proper hnd hd]
            exact (ts_proper_target hF₂ rfl _).symm
          · rw [S.at_proper (CellScheme.below.incl ⟨A₂c, hx⟩ d) hd, rowX_a₂_proper hnd hd]
            exact (ts_proper_target hF₂ rfl _).symm
      · -- `b₁`'s controller: the repaired row
        refine wU.transformsTo fun d => ?_
        rw [gTop_of_le (K := 3) (k := D₂.grade d.1) (grade_le_below_ub₁ d), min_eq_left le_top]
        change min (r (CellScheme.below.incl ⟨ub₁, hx⟩ d)) (r ⟨ub₁, memub₁₃⟩) = _
        rw [S.at_ub₁, rowsR_E_ub₁ d]
        have hnd : ¬ mute₂ d.1 := hmute_below₂ _ d.1 not_mute_ub₁ d.2
        by_cases hd3 : D₂.grade d.1 = 3
        · rcases three_cases hnd hd3 with hd | hd | hd | hd | hd | hd
          · rw [show CellScheme.below.incl ⟨ub₁, hx⟩ d = ⟨a₁old, mema₁old₃⟩ from Subtype.ext hd,
              S.at_a₁old, min_eq_left L.z1w, hd, qM_a₁old, ts_η₁, L.R₃_t_eq]
          · rw [show CellScheme.below.incl ⟨ub₁, hx⟩ d = ⟨a₂old, mema₂old₃⟩ from Subtype.ext hd,
              S.at_a₂old, min_eq_left L.z2w, hd, qM_a₂old, ts_γ₀]
          · rw [show CellScheme.below.incl ⟨ub₁, hx⟩ d = ⟨b₁new, memb₁new₃⟩ from Subtype.ext hd,
              S.at_b₁new, min_self, hd, qM_b₁new, ts_ω2_four]
          · rw [show CellScheme.below.incl ⟨ub₁, hx⟩ d = ⟨A₁c, memA₁c₃⟩ from Subtype.ext hd,
              S.at_A₁c, min_eq_left L.z1w, hd, qM_A₁c, ts_η₁, L.R₃_t_eq]
          · rw [show CellScheme.below.incl ⟨ub₁, hx⟩ d = ⟨A₂c, memA₂c₃⟩ from Subtype.ext hd,
              S.at_A₂c, min_eq_left L.z2w, hd, qM_A₂c, ts_γ₀]
          · rw [show CellScheme.below.incl ⟨ub₁, hx⟩ d = ⟨ub₁, memub₁₃⟩ from Subtype.ext hd,
              S.at_ub₁, min_self, hd, qM_ub₁, ts_ω2_four]
        · have hd2 : D₂.grade d.1 ≤ 2 := by
            have := grade_le_below_ub₁ d; omega
          rcases two_cases hnd hd2 with hd | hd | hd | hd | hd | hd | ⟨hd, -⟩ | ⟨hd, -⟩
          · rw [show CellScheme.below.incl ⟨ub₁, hx⟩ d = ⟨H₀old, memH₀old₃⟩ from Subtype.ext hd,
              S.at_H₀old, hd, qM_H₀old, ts_ω2_three]
          · rw [show CellScheme.below.incl ⟨ub₁, hx⟩ d = ⟨H₀new, memH₀new₃⟩ from Subtype.ext hd,
              S.at_H₀new, min_eq_right L.wx₁, hd, qM_H₀new, ts_ω2_four]
          · rw [show CellScheme.below.incl ⟨ub₁, hx⟩ d = ⟨U_H, memU_H₃⟩ from Subtype.ext hd,
              S.at_U_H, min_eq_right L.wx₁, hd, qM_U_H, ts_ω2_four]
          · rw [show CellScheme.below.incl ⟨ub₁, hx⟩ d = ⟨s₀old, mems₀old₃⟩ from Subtype.ext hd,
              S.at_s₀old, L.min_minxH_w, hd, qM_s₀old, ts_ω2_three]
          · rw [show CellScheme.below.incl ⟨ub₁, hx⟩ d = ⟨s₀new, mems₀new₃⟩ from Subtype.ext hd,
              S.at_s₀new, min_eq_right L.wH, hd, qM_s₀new, ts_ω2_four]
          · rw [show CellScheme.below.incl ⟨ub₁, hx⟩ d = ⟨U_S, memU_S₃⟩ from Subtype.ext hd,
              S.at_U_S, min_eq_right L.wH, hd, qM_U_S, ts_ω2_four]
          · rw [S.at_proper (CellScheme.below.incl ⟨ub₁, hx⟩ d) hd, qM_proper' hnd hd]
            exact (ts_proper_target L.fix rfl _).symm
          · rw [S.at_proper (CellScheme.below.incl ⟨ub₁, hx⟩ d) hd, qM_proper' hnd hd]
            exact (ts_proper_target L.fix rfl _).symm
    · -- grade at most two: the grade-two sufficiency lemma
      have hg2 : D₂.grade x ≤ 2 := by have := hx.2; change D₂.grade x ≤ 3 at this; omega
      have hne : x ≠ ub₁ := fun e => hg3 (by rw [e]; exact grade_ub₁)
      have hx₂ : GradedLe (D₂.cell x) (Finset.univ, 2) := ⟨Finset.subset_univ _, hg2⟩
      refine transformsTo_congr rfl (rowsR_E_of_ne hne).symm ?_ (hr₂.locality ⟨x, hx₂⟩)
      funext d
      rw [show CellScheme.below.mono h₂₃ (CellScheme.below.incl ⟨x, hx₂⟩ d) =
          CellScheme.below.incl ⟨x, hx⟩ d from Subtype.ext rfl,
        show CellScheme.below.mono h₂₃ ⟨x, hx₂⟩ = ⟨x, hx⟩ from Subtype.ext rfl]
  · -- availability
    intro Sig Xi₀ hs hg
    have hnmX : ¬ mute₂ Xi₀.1 := hnm Xi₀
    have hnmS : ¬ mute₂ Sig.1 := hnm Sig
    by_cases hg3 : D₂.grade Xi₀.1 = 3
    · have hgS : D₂.grade Sig.1 = 3 := hg.trans hg3
      rcases three_cases hnmX hg3 with h | h | h | h | h | h
      · refine ⟨⟨a₂old, mema₂old₃⟩, by rw [h, cell_a₂old, cell_a₁old], ?_⟩
        rw [S.at_a₂old]
        rw [h] at hs
        rcases three_cases hnmS hgS with h' | h' | h' | h' | h' | h'
        · rw [show Sig = ⟨a₁old, mema₁old₃⟩ from Subtype.ext h', S.at_a₁old]; exact L.z12
        · rw [show Sig = ⟨a₂old, mema₂old₃⟩ from Subtype.ext h', S.at_a₂old]
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_b₁new)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_A₁c)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_A₂c)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_ub₁)
      · refine ⟨Xi₀, rfl, ?_⟩
        rw [show Xi₀ = ⟨a₂old, mema₂old₃⟩ from Subtype.ext h, S.at_a₂old]
        rw [h] at hs
        rcases three_cases hnmS hgS with h' | h' | h' | h' | h' | h'
        · rw [show Sig = ⟨a₁old, mema₁old₃⟩ from Subtype.ext h', S.at_a₁old]; exact L.z12
        · rw [show Sig = ⟨a₂old, mema₂old₃⟩ from Subtype.ext h', S.at_a₂old]
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_b₁new)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_A₁c)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_A₂c)
        · exfalso; rw [h'] at hs; exact three_not_mem_scope_castAdd _ (hs three_mem_scope_ub₁)
      · refine ⟨Xi₀, rfl, ?_⟩
        rw [show Xi₀ = ⟨b₁new, memb₁new₃⟩ from Subtype.ext h, S.at_b₁new]
        exact hle_w Sig hgS
      · refine ⟨⟨ub₁, memub₁₃⟩, by rw [h, cell_ub₁, cell_A₁c], ?_⟩
        rw [S.at_ub₁]; exact hle_w Sig hgS
      · refine ⟨⟨ub₁, memub₁₃⟩, by rw [h, cell_ub₁, cell_A₂c], ?_⟩
        rw [S.at_ub₁]; exact hle_w Sig hgS
      · refine ⟨Xi₀, rfl, ?_⟩
        rw [show Xi₀ = ⟨ub₁, memub₁₃⟩ from Subtype.ext h, S.at_ub₁]; exact hle_w Sig hgS
    · have hg2 : D₂.grade Xi₀.1 ≤ 2 := by
        have := Xi₀.2.2; change D₂.grade Xi₀.1 ≤ 3 at this; omega
      have hS2 : D₂.grade Sig.1 ≤ 2 := hg ▸ hg2
      obtain ⟨Xi, hc, hle⟩ := hr₂.availability
        ⟨Sig.1, ⟨Finset.subset_univ _, hS2⟩⟩ ⟨Xi₀.1, ⟨Finset.subset_univ _, hg2⟩⟩ hs hg
      refine ⟨CellScheme.below.mono h₂₃ Xi, hc, ?_⟩
      rw [show CellScheme.below.mono h₂₃ ⟨Sig.1, ⟨Finset.subset_univ _, hS2⟩⟩ = Sig from
        Subtype.ext rfl] at hle
      exact hle

end SufficiencyProof

/-! ## Necessity: every respecting labelling is in the value shape with admissible parameters -/

section Necessity

theorem hq₂_of {q : D₂.below (Finset.univ, 3) → ExtOrd}
    (hq : RespectsSemanticsBelow rowsR (Finset.univ, 3) q) :
    RespectsSemanticsBelow rows₃ (Finset.univ, 2) (fun d => q (CellScheme.below.mono h₂₃ d)) :=
  (respectsR_iff_low (by decide) _).mp (hq.mono h₂₃)

theorem mono₂₃_eq {X : Cell D₂} (h₂ : GradedLe (D₂.cell X) (Finset.univ, 2))
    (h₃ : GradedLe (D₂.cell X) (Finset.univ, 3)) :
    CellScheme.below.mono h₂₃ ⟨X, h₂⟩ = ⟨X, h₃⟩ := Subtype.ext rfl
theorem mono₁₃_eq {X : Cell D₂} (h₁ : GradedLe (D₂.cell X) (Finset.univ, 1))
    (h₃ : GradedLe (D₂.cell X) (Finset.univ, 3)) :
    CellScheme.below.mono h₂₃ (CellScheme.below.mono h₁₂ ⟨X, h₁⟩) = ⟨X, h₃⟩ := Subtype.ext rfl

variable {q : D₂.below (Finset.univ, 3) → ExtOrd}
  (hq : RespectsSemanticsBelow rowsR (Finset.univ, 3) q)
include hq

/-- Every proper grade-one cell carries one label, and every proper grade-two cell `⊥`. -/
theorem proper_of_respectsR (d : D₂.below (Finset.univ, 3)) (hd : IsProper d.1)
    (sc : D₂.below (Finset.univ, 3)) (hsc : IsProper sc.1) (hg : D₂.grade sc.1 = 1) :
    q d = if D₂.grade d.1 = 2 then ⊥ else q sc := by
  have hnd : ¬ mute₂ d.1 := not_mute₂_of_low le_rfl d
  have hg2 : D₂.grade d.1 ≤ 2 := by
    obtain ⟨c, hc⟩ := hd; rw [← gradeP_le_of_proper hnd hc]; exact c.gradeP_le_two
  by_cases h2 : D₂.grade d.1 = 2
  · rw [ite_eq_left h2]
    exact proper_two_eq_bot (hq₂_of hq) ⟨d.1, ⟨Finset.subset_univ _, hg2⟩⟩ hd h2
  · rw [ite_eq_right h2]
    have hg1 : D₂.grade d.1 ≤ 1 := by omega
    have hq₁ := (hq₂_of hq).mono h₁₂
    exact const_of_respects rfl hq₁ ⟨U_H, memU₁⟩ cell_U_H ⟨d.1, ⟨Finset.subset_univ _, hg1⟩⟩
      ⟨sc.1, ⟨Finset.subset_univ _, hg.le⟩⟩ hd hsc

theorem selfVis_at (d : D₂.below (Finset.univ, 3)) : SelfVis (D₂.grade d.1) (q d) :=
  (hq.orderly d).symm

/-- **Necessity**: a respecting labelling has the value shape, and its parameters are
admissible.  The proper value is read at any proper grade-one cell `sc`. -/
theorem shape_legal_of_respectsR (sc : D₂.below (Finset.univ, 3)) (hsc : IsProper sc.1)
    (hg : D₂.grade sc.1 = 1) (s1 : D₂.below (Finset.univ, 3)) (hs1 : IsProper s1.1)
    (hs1c : D₂.cell s1.1 = ({1}, 1)) :
    Shape₃ q (q sc) (q ⟨H₀old, memH₀old₃⟩) (q ⟨U_H, memU_H₃⟩) (q ⟨U_S, memU_S₃⟩)
        (q ⟨A₁c, memA₁c₃⟩) (q ⟨A₂c, memA₂c₃⟩) (q ⟨ub₁, memub₁₃⟩) ∧
      Legal₃ (q sc) (q ⟨H₀old, memH₀old₃⟩) (q ⟨U_H, memU_H₃⟩) (q ⟨U_S, memU_S₃⟩)
        (q ⟨A₁c, memA₁c₃⟩) (q ⟨A₂c, memA₂c₃⟩) (q ⟨ub₁, memub₁₃⟩) := by
  have hq₂ := hq₂_of hq
  have hq₁ := hq₂.mono h₁₂
  have hH₀new : q ⟨H₀new, memH₀new₃⟩ = q ⟨U_H, memU_H₃⟩ := by
    have := H₀new_eq_U_H_of_respects hq₁
    rwa [mono₁₃_eq, mono₁₃_eq] at this
  have hs₀old : q ⟨s₀old, mems₀old₃⟩ = min (q ⟨H₀old, memH₀old₃⟩) (q ⟨U_S, memU_S₃⟩) := by
    have := s₀old_eq_min_of_respects hq₂
    rwa [mono₂₃_eq, mono₂₃_eq, mono₂₃_eq] at this
  have hs₀new : q ⟨s₀new, mems₀new₃⟩ = q ⟨U_S, memU_S₃⟩ := by
    have := s₀new_eq_U_S_of_respects hq₂
    rwa [mono₂₃_eq, mono₂₃_eq] at this
  have hHle : q ⟨U_S, memU_S₃⟩ ≤ q ⟨U_H, memU_H₃⟩ := by
    have := U_S_le_U_H_of_respects hq₂
    rwa [mono₂₃_eq, mono₂₃_eq] at this
  have h01 : q ⟨H₀old, memH₀old₃⟩ ≤ q ⟨U_H, memU_H₃⟩ := by
    have := le_U_H_of_respects hq₁ ⟨H₀old, memA le_rfl⟩
    rwa [mono₁₃_eq, mono₁₃_eq] at this
  have hcoup : q ⟨H₀old, memH₀old₃⟩ = ⊥ → q ⟨U_H, memU_H₃⟩ = ⊥ := by
    have := U_H_eq_bot_of_H₀old hq₁
    rwa [mono₁₃_eq, mono₁₃_eq] at this
  have hs1v : q s1 = q sc := by
    have := proper_of_respectsR hq s1 hs1 sc hsc hg
    rwa [ite_eq_right (by change (D₂.cell s1.1).2 ≠ 2; rw [hs1c]; decide)] at this
  have hvx : q sc ≤ q ⟨H₀old, memH₀old₃⟩ := by
    rw [← hs1v]
    obtain ⟨Xi, hXi, hle⟩ := hq.availability s1 ⟨H₀old, memH₀old₃⟩ (by
        change (D₂.cell s1.1).1 ⊆ D₂.scope H₀old; rw [hs1c, scope_H₀old']; decide)
      (by change (D₂.cell s1.1).2 = D₂.grade H₀old; rw [hs1c, grade_H₀old])
    have : Xi = ⟨H₀old, memH₀old₃⟩ :=
      Subtype.ext (cell_inj_low hXi (by
        change (D₂.cell Xi.1).2 ≤ 2; rw [hXi]
        exact (show D₂.grade H₀old ≤ 2 by rw [grade_H₀old]; decide)))
    rw [this] at hle; exact hle
  have vis : ∀ (X : Cell D₂) (h : GradedLe (D₂.cell X) (Finset.univ, 3)) (k : ℕ),
      D₂.grade X = k → SelfVis k (q ⟨X, h⟩) := fun X h k hk => by
    have := selfVis_at hq ⟨X, h⟩
    change SelfVis (D₂.grade X) _ at this
    rwa [hk] at this
  refine ⟨⟨rfl, hH₀new, rfl, hs₀old, hs₀new, rfl, a₁old_eq_A₁c_of_respectsR hq, rfl,
    a₂old_eq_A₂c_of_respectsR hq, rfl, b₁new_eq_ub₁_of_respectsR hq, rfl,
    fun d hd => proper_of_respectsR hq d hd sc hsc hg⟩, ?_⟩
  refine ⟨⟨?_, hvx, h01, hcoup, vis _ _ 1 grade_H₀old, vis _ _ 1 grade_U_H, vis _ _ 2 grade_U_S,
    hHle, ?_⟩, A₁c_le_A₂c_of_respectsR hq, A₂c_le_H₀old_of_respectsR hq,
    A₂c_le_ub₁_of_respectsR hq, ub₁_le_U_S_of_respectsR hq, vis _ _ 3 grade_A₁c,
    vis _ _ 3 grade_A₂c, vis _ _ 3 grade_ub₁, selfVis_min_H₀old_ub₁_of_respectsR hq,
    A₁c_eq_R₃_min_of_respectsR hq sc hsc hg, min_proper_ub₁_fixed_of_respectsR hq sc hsc hg,
    A₂c_eq_bot_of_A₁cR hq, ub₁_eq_bot_of_min_botR hq⟩
  · have := selfVis_at hq sc; rwa [hg] at this
  · rw [← hs₀old]; exact vis _ _ 2 grade_s₀old

end Necessity

/-! ## The face constraints (general lower sets) -/

section FaceConstraints

theorem evr_selfVis (K : ℕ) (t : ExtOrd) : SelfVis K (extVisibilityReplace t K K) := by
  rcases ExtOrd.cases t with rfl | rfl | ⟨α, rfl⟩
  · rw [extVisibilityReplace_bot]; exact selfVis_bot K
  · change extVisibilityReplace (extVisibilityReplace ⊤ K K) K K = extVisibilityReplace ⊤ K K
    rw [extVisibilityReplace_top, extVisibilityReplace_top]
  · rw [extVisibilityReplace_ofOrd, selfVis_ofOrd_iff, finitePart_visibilityReplace]
    split_ifs with h <;> omega
theorem R₃_mono {a b : ExtOrd} (h : a ≤ b) :
    extVisibilityReplace a 3 3 ≤ extVisibilityReplace b 3 3 := evr_mono h le_rfl

theorem a₁old_below_a₂old : GradedLe (D₂.cell a₁old) (D₂.cell a₂old) := by
  rw [cell_a₁old, cell_a₂old]; exact GradedLe.refl _
theorem H₀old_below_a₂old : GradedLe (D₂.cell H₀old) (D₂.cell a₂old) := by
  rw [cell_a₂old]; exact aFace_castAdd _
theorem s₀old_below_a₂old : GradedLe (D₂.cell s₀old) (D₂.cell a₂old) := by
  rw [cell_a₂old]; exact aFace_castAdd _
theorem refl_a₂old : GradedLe (D₂.cell a₂old) (D₂.cell a₂old) := GradedLe.refl _
theorem grade_le_grade_a₂old (e : D₂.below (D₂.cell a₂old)) : D₂.grade e.1 ≤ D₂.grade a₂old := by
  rw [grade_a₂old]; exact (below_a₂old_mem e).2
theorem incl_a₂old_self {BJ : Finset (Fin 4) × ℕ} (h1 : GradedLe (D₂.cell a₂old) BJ) :
    CellScheme.below.incl ⟨a₂old, h1⟩ ⟨a₂old, refl_a₂old⟩ = ⟨a₂old, h1⟩ := Subtype.ext rfl
theorem cell_b₁new : D₂.cell b₁new = (({1, 2, 3} : Finset (Fin 4)), 3) :=
  Prod.ext scope_b₁new grade_b₁new
theorem refl_b₁new : GradedLe (D₂.cell b₁new) (D₂.cell b₁new) := GradedLe.refl _
theorem H₀new_below_b₁new : GradedLe (D₂.cell H₀new) (D₂.cell b₁new) := by
  rw [cell_b₁new]; exact copyB_mem _
theorem s₀new_below_b₁new : GradedLe (D₂.cell s₀new) (D₂.cell b₁new) := by
  rw [cell_b₁new]; exact copyB_mem _

variable {BJ : Finset (Fin 4) × ℕ} {r : D₂.below BJ → ExtOrd}
  (hr : RespectsSemanticsBelow rowsR BJ r)
include hr

theorem selfVis_at' (d : D₂.below BJ) : SelfVis (D₂.grade d.1) (r d) := (hr.orderly d).symm

/-- The old cap `a₁` is below the old cap `a₂`. -/
theorem a₁old_le_a₂old' (h1 : GradedLe (D₂.cell a₁old) BJ) (h2 : GradedLe (D₂.cell a₂old) BJ) :
    r ⟨a₁old, h1⟩ ≤ r ⟨a₂old, h2⟩ := by
  have h := hr.probe_eq_of_row_eq ⟨a₁old, h1⟩ ⟨a₂old, a₂old_below_a₁old⟩ ⟨a₁old, refl_a₁old⟩
    ((rowsR_E_a₁old' ⟨a₂old, a₂old_below_a₁old⟩).trans
      (((pull_eq_rowX _ not_mute_a₂old ret₂_a₂old).trans rowX_a₁_a₂).trans
        (((pull_eq_rowX _ not_mute_a₁old ret₂_a₁old).trans rowX_a₁_a₁).symm.trans
          (rowsR_E_a₁old' ⟨a₁old, refl_a₁old⟩).symm)))
    (by rw [grade_a₂old, grade_a₁old])
  have e1 : CellScheme.below.incl ⟨a₁old, h1⟩ ⟨a₂old, a₂old_below_a₁old⟩ = ⟨a₂old, h2⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨a₁old, h1⟩ ⟨a₁old, refl_a₁old⟩ = ⟨a₁old, h1⟩ := Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.symm.le.trans (min_le_left _ _)

/-- The old cap `a₂` is below the old occurrence and the old level-two witness. -/
theorem a₂old_le_H₀old' (h1 : GradedLe (D₂.cell a₂old) BJ) (h2 : GradedLe (D₂.cell H₀old) BJ) :
    r ⟨a₂old, h1⟩ ≤ r ⟨H₀old, h2⟩ := by
  have h := hr.probe_ge_of_row_eq ⟨a₂old, h1⟩ ⟨H₀old, H₀old_below_a₂old⟩ ⟨a₂old, refl_a₂old⟩
    ((rowsR_E_a₂old' ⟨H₀old, H₀old_below_a₂old⟩).trans
      (((pull_eq_rowX _ not_mute_H₀old ret₂_H₀old).trans rowX_a₂_H).trans
        (((pull_eq_rowX _ not_mute_a₂old ret₂_a₂old).trans rowX_a₂_a₂).symm.trans
          (rowsR_E_a₂old' ⟨a₂old, refl_a₂old⟩).symm)))
    (by rw [grade_H₀old, grade_a₂old]; decide)
  have e1 : CellScheme.below.incl ⟨a₂old, h1⟩ ⟨H₀old, H₀old_below_a₂old⟩ = ⟨H₀old, h2⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨a₂old, h1⟩ ⟨a₂old, refl_a₂old⟩ = ⟨a₂old, h1⟩ := Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.trans (min_le_left _ _)
theorem a₂old_le_s₀old' (h1 : GradedLe (D₂.cell a₂old) BJ) (h2 : GradedLe (D₂.cell s₀old) BJ) :
    r ⟨a₂old, h1⟩ ≤ r ⟨s₀old, h2⟩ := by
  have h := hr.probe_ge_of_row_eq ⟨a₂old, h1⟩ ⟨s₀old, s₀old_below_a₂old⟩ ⟨a₂old, refl_a₂old⟩
    ((rowsR_E_a₂old' ⟨s₀old, s₀old_below_a₂old⟩).trans
      (((pull_eq_rowX _ not_mute_s₀old ret₂_s₀old).trans rowX_a₂_s).trans
        (((pull_eq_rowX _ not_mute_a₂old ret₂_a₂old).trans rowX_a₂_a₂).symm.trans
          (rowsR_E_a₂old' ⟨a₂old, refl_a₂old⟩).symm)))
    (by rw [grade_s₀old, grade_a₂old]; decide)
  have e1 : CellScheme.below.incl ⟨a₂old, h1⟩ ⟨s₀old, s₀old_below_a₂old⟩ = ⟨s₀old, h2⟩ :=
    Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨a₂old, h1⟩ ⟨a₂old, refl_a₂old⟩ = ⟨a₂old, h1⟩ := Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.trans (min_le_left _ _)

/-- **The old caps' orbit on the face**: `a = R₃ (min v b)` at any proper grade-one cell below the
old cap `a₂`. -/
theorem a₁old_eq_R₃_min' (h1 : GradedLe (D₂.cell a₁old) BJ) (h2 : GradedLe (D₂.cell a₂old) BJ)
    (sc : D₂.below BJ) (hsc : IsProper sc.1) (hg : D₂.grade sc.1 = 1)
    (hsub : GradedLe (D₂.cell sc.1) (D₂.cell a₂old)) :
    r ⟨a₁old, h1⟩ = extVisibilityReplace (min (r sc) (r ⟨a₂old, h2⟩)) 3 3 := by
  have hvis : SelfVis (D₂.grade a₂old)
      (r (CellScheme.below.incl ⟨a₂old, h2⟩ ⟨a₂old, refl_a₂old⟩)) := by
    rw [incl_a₂old_self]; exact selfVis_at' hr ⟨a₂old, h2⟩
  have h := label_of_probe_orbit (grade := fun e : D₂.below (D₂.cell a₂old) => D₂.grade e.1)
    (E := rowsR.E a₂old) (p := fun e => r (CellScheme.below.incl ⟨a₂old, h2⟩ e))
    (c := ⟨a₂old, refl_a₂old⟩) grade_le_grade_a₂old hvis (hr.locality ⟨a₂old, h2⟩)
    (d := ⟨sc.1, hsub⟩) (e := ⟨a₁old, a₁old_below_a₂old⟩) (k := 3) (i := 3)
    (by change 3 ≤ D₂.grade a₂old; rw [grade_a₂old]) le_rfl
    (by rw [rowsR_E_a₂old' ⟨a₁old, a₁old_below_a₂old⟩, rowsR_E_a₂old' ⟨sc.1, hsub⟩,
          pull_eq_rowX _ not_mute_a₁old ret₂_a₁old, rowX_a₂_a₁,
          rowX_a₂_proper (not_mute₂_of_low (by decide) ⟨sc.1, hsub.trans mema₂old₃⟩) hsc,
          ite_eq_right (show ¬ D₂.grade sc.1 = 2 by rw [hg]; decide), v₀_orbit_three])
    (by change r (CellScheme.below.incl ⟨a₂old, h2⟩ ⟨a₁old, a₁old_below_a₂old⟩) ≤
          r (CellScheme.below.incl ⟨a₂old, h2⟩ ⟨a₂old, refl_a₂old⟩)
        rw [show CellScheme.below.incl ⟨a₂old, h2⟩ ⟨a₁old, a₁old_below_a₂old⟩ = ⟨a₁old, h1⟩ from
          Subtype.ext rfl, incl_a₂old_self]
        exact a₁old_le_a₂old' hr h1 h2)
  change r (CellScheme.below.incl ⟨a₂old, h2⟩ ⟨a₁old, a₁old_below_a₂old⟩) =
    extVisibilityReplace (min (r (CellScheme.below.incl ⟨a₂old, h2⟩ ⟨sc.1, hsub⟩))
      (r (CellScheme.below.incl ⟨a₂old, h2⟩ ⟨a₂old, refl_a₂old⟩))) 3 3 at h
  rwa [show CellScheme.below.incl ⟨a₂old, h2⟩ ⟨a₁old, a₁old_below_a₂old⟩ = ⟨a₁old, h1⟩ from
    Subtype.ext rfl, show CellScheme.below.incl ⟨a₂old, h2⟩ ⟨sc.1, hsub⟩ = sc from
    Subtype.ext rfl, incl_a₂old_self] at h

/-- The fixing law on the face. -/
theorem fix_min_a₂old' (h2 : GradedLe (D₂.cell a₂old) BJ) (sc : D₂.below BJ) (hsc : IsProper sc.1)
    (hg : D₂.grade sc.1 = 1) (hsub : GradedLe (D₂.cell sc.1) (D₂.cell a₂old)) :
    extVisibilityReplace (min (r sc) (r ⟨a₂old, h2⟩)) 3 1 = min (r sc) (r ⟨a₂old, h2⟩) := by
  have hvis : SelfVis (D₂.grade a₂old)
      (r (CellScheme.below.incl ⟨a₂old, h2⟩ ⟨a₂old, refl_a₂old⟩)) := by
    rw [incl_a₂old_self]; exact selfVis_at' hr ⟨a₂old, h2⟩
  have h := probe_orbit (grade := fun e : D₂.below (D₂.cell a₂old) => D₂.grade e.1)
    (E := rowsR.E a₂old) (p := fun e => r (CellScheme.below.incl ⟨a₂old, h2⟩ e))
    (c := ⟨a₂old, refl_a₂old⟩) grade_le_grade_a₂old hvis (hr.locality ⟨a₂old, h2⟩)
    (d := ⟨sc.1, hsub⟩) (e := ⟨sc.1, hsub⟩) (k := 3) (i := 1)
    (by change 3 ≤ D₂.grade a₂old; rw [grade_a₂old]) (by decide)
    (by rw [rowsR_E_a₂old' ⟨sc.1, hsub⟩,
          rowX_a₂_proper (not_mute₂_of_low (by decide) ⟨sc.1, hsub.trans mema₂old₃⟩) hsc,
          ite_eq_right (show ¬ D₂.grade sc.1 = 2 by rw [hg]; decide), v₀_orbit_three_one])
  change min (r (CellScheme.below.incl ⟨a₂old, h2⟩ ⟨sc.1, hsub⟩))
      (r (CellScheme.below.incl ⟨a₂old, h2⟩ ⟨a₂old, refl_a₂old⟩)) =
    extVisibilityReplace (min (r (CellScheme.below.incl ⟨a₂old, h2⟩ ⟨sc.1, hsub⟩))
      (r (CellScheme.below.incl ⟨a₂old, h2⟩ ⟨a₂old, refl_a₂old⟩))) 3 1 at h
  rw [show CellScheme.below.incl ⟨a₂old, h2⟩ ⟨sc.1, hsub⟩ = sc from Subtype.ext rfl,
    incl_a₂old_self] at h
  exact h.symm

/-- The clause-5 coupling on the face: `a = ⊥ → b = ⊥`. -/
theorem a₂old_eq_bot_of_a₁old' (h1 : GradedLe (D₂.cell a₁old) BJ) (h2 : GradedLe (D₂.cell a₂old) BJ)
    (h : r ⟨a₁old, h1⟩ = ⊥) : r ⟨a₂old, h2⟩ = ⊥ := by
  obtain ⟨g, σ, hw, heq⟩ := TransformsTo.witness (hr.locality ⟨a₂old, h2⟩)
  have hA1 : min (r ⟨a₁old, h1⟩) (r ⟨a₂old, h2⟩) =
      min (σ (rowsR.E a₂old ⟨a₁old, a₁old_below_a₂old⟩)) (g (D₂.grade a₁old)) :=
    heq ⟨a₁old, a₁old_below_a₂old⟩
  have hA : min (r ⟨a₂old, h2⟩) (r ⟨a₂old, h2⟩) =
      min (σ (rowsR.E a₂old ⟨a₂old, refl_a₂old⟩)) (g (D₂.grade a₂old)) := heq ⟨a₂old, refl_a₂old⟩
  rw [h, rowsR_E_a₂old' ⟨a₁old, a₁old_below_a₂old⟩, pull_eq_rowX _ not_mute_a₁old ret₂_a₁old,
    rowX_a₂_a₁, grade_a₁old, min_eq_left bot_le] at hA1
  rw [min_self, rowsR_E_a₂old' ⟨a₂old, refl_a₂old⟩, pull_eq_rowX _ not_mute_a₂old ret₂_a₂old,
    rowX_a₂_a₂, grade_a₂old] at hA
  rcases min_eq_bot.mp hA1.symm with hσ | hg
  · have h5 := hw.clause5 η₁ 4 (by rw [hσ]; exact bot_le) 4 le_rfl
    rw [hσ, extVisibilityReplace_bot, evr_η₁_four] at h5
    rw [hA, h5]; exact min_eq_left bot_le
  · rw [hA, hg]; exact min_eq_right bot_le

/-- The copy of `b₁` is below the copies of `H₀` and `s₀` (its row reads `ω·2+3` at all three). -/
theorem b₁new_le_H₀new' (h1 : GradedLe (D₂.cell b₁new) BJ) (h2 : GradedLe (D₂.cell H₀new) BJ) :
    r ⟨b₁new, h1⟩ ≤ r ⟨H₀new, h2⟩ := by
  have hb : GradedLe (D₂.cell H₀new) (D₂.cell b₁new) := H₀new_below_b₁new
  have h := hr.probe_ge_of_row_eq ⟨b₁new, h1⟩ ⟨H₀new, hb⟩ ⟨b₁new, refl_b₁new⟩
    ((rowsR_E_b₁new' ⟨H₀new, hb⟩).trans
      (((pull_eq_rowX _ not_mute_H₀new ret₂_H₀new).trans rowX_b₁_H).trans
        (((pull_eq_rowX _ not_mute_b₁new ret₂_b₁new).trans rowX_b₁_b₁).symm.trans
          (rowsR_E_b₁new' ⟨b₁new, refl_b₁new⟩).symm)))
    (by rw [grade_H₀new, grade_b₁new]; decide)
  have e1 : CellScheme.below.incl ⟨b₁new, h1⟩ ⟨H₀new, hb⟩ = ⟨H₀new, h2⟩ := Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨b₁new, h1⟩ ⟨b₁new, refl_b₁new⟩ = ⟨b₁new, h1⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.trans (min_le_left _ _)

end FaceConstraints

/-! ## The two face sections -/

section Sections

theorem cell_H₀old : D₂.cell H₀old = (({0, 1, 2} : Finset (Fin 4)), 1) :=
  Prod.ext scope_H₀old' grade_H₀old
theorem cell_H₀new : D₂.cell H₀new = (({1, 2, 3} : Finset (Fin 4)), 1) :=
  Prod.ext scope_H₀new grade_H₀new

theorem hsing₁ : (({1} : Finset (Fin 4)), 1) ∈ Plan.gradedPlan plan₄ :=
  Plan.mem_gradedPlan.mpr ⟨singleton_mem_plan₄ 1, Nat.one_pos, by simp⟩

theorem grade_le_grade_b₁new (e : D₂.below (D₂.cell b₁new)) : D₂.grade e.1 ≤ D₂.grade b₁new := by
  rw [grade_b₁new]; exact (below_b₁new_mem e).2
theorem incl_b₁new_self {BJ : Finset (Fin 4) × ℕ} (h1 : GradedLe (D₂.cell b₁new) BJ) :
    CellScheme.below.incl ⟨b₁new, h1⟩ ⟨b₁new, refl_b₁new⟩ = ⟨b₁new, h1⟩ := Subtype.ext rfl

variable {BJ : Finset (Fin 4) × ℕ} {r : D₂.below BJ → ExtOrd}
  (hr : RespectsSemanticsBelow rowsR BJ r)
include hr

theorem b₁new_le_s₀new' (h1 : GradedLe (D₂.cell b₁new) BJ) (h2 : GradedLe (D₂.cell s₀new) BJ) :
    r ⟨b₁new, h1⟩ ≤ r ⟨s₀new, h2⟩ := by
  have hb : GradedLe (D₂.cell s₀new) (D₂.cell b₁new) := s₀new_below_b₁new
  have h := hr.probe_ge_of_row_eq ⟨b₁new, h1⟩ ⟨s₀new, hb⟩ ⟨b₁new, refl_b₁new⟩
    ((rowsR_E_b₁new' ⟨s₀new, hb⟩).trans
      (((pull_eq_rowX _ not_mute_s₀new ret₂_s₀new).trans rowX_b₁_s).trans
        (((pull_eq_rowX _ not_mute_b₁new ret₂_b₁new).trans rowX_b₁_b₁).symm.trans
          (rowsR_E_b₁new' ⟨b₁new, refl_b₁new⟩).symm)))
    (by rw [grade_s₀new, grade_b₁new]; decide)
  have e1 : CellScheme.below.incl ⟨b₁new, h1⟩ ⟨s₀new, hb⟩ = ⟨s₀new, h2⟩ := Subtype.ext rfl
  have e2 : CellScheme.below.incl ⟨b₁new, h1⟩ ⟨b₁new, refl_b₁new⟩ = ⟨b₁new, h1⟩ :=
    Subtype.ext rfl
  rw [e1, e2, min_self] at h
  exact h.trans (min_le_left _ _)

/-- The fixing law on the B face. -/
theorem fix_min_b₁new' (h1 : GradedLe (D₂.cell b₁new) BJ) (sc : D₂.below BJ) (hsc : IsProper sc.1)
    (hg : D₂.grade sc.1 = 1) (hsub : GradedLe (D₂.cell sc.1) (D₂.cell b₁new)) :
    extVisibilityReplace (min (r sc) (r ⟨b₁new, h1⟩)) 3 1 = min (r sc) (r ⟨b₁new, h1⟩) := by
  have hvis : SelfVis (D₂.grade b₁new)
      (r (CellScheme.below.incl ⟨b₁new, h1⟩ ⟨b₁new, refl_b₁new⟩)) := by
    rw [incl_b₁new_self]; exact selfVis_at' hr ⟨b₁new, h1⟩
  have h := probe_orbit (grade := fun e : D₂.below (D₂.cell b₁new) => D₂.grade e.1)
    (E := rowsR.E b₁new) (p := fun e => r (CellScheme.below.incl ⟨b₁new, h1⟩ e))
    (c := ⟨b₁new, refl_b₁new⟩) grade_le_grade_b₁new hvis (hr.locality ⟨b₁new, h1⟩)
    (d := ⟨sc.1, hsub⟩) (e := ⟨sc.1, hsub⟩) (k := 3) (i := 1)
    (by change 3 ≤ D₂.grade b₁new; rw [grade_b₁new]) (by decide)
    (by rw [rowsR_E_b₁new' ⟨sc.1, hsub⟩,
          rowX_b₁_proper (not_mute₂_of_low (by decide) ⟨sc.1, hsub.trans memb₁new₃⟩) hsc,
          ite_eq_right (show ¬ D₂.grade sc.1 = 2 by rw [hg]; decide), v₀_orbit_three_one])
  change min (r (CellScheme.below.incl ⟨b₁new, h1⟩ ⟨sc.1, hsub⟩))
      (r (CellScheme.below.incl ⟨b₁new, h1⟩ ⟨b₁new, refl_b₁new⟩)) =
    extVisibilityReplace (min (r (CellScheme.below.incl ⟨b₁new, h1⟩ ⟨sc.1, hsub⟩))
      (r (CellScheme.below.incl ⟨b₁new, h1⟩ ⟨b₁new, refl_b₁new⟩))) 3 1 at h
  rw [show CellScheme.below.incl ⟨b₁new, h1⟩ ⟨sc.1, hsub⟩ = sc from Subtype.ext rfl,
    incl_b₁new_self] at h
  exact h.symm

end Sections

/-! ### Cell inequalities by grade and scope -/

/-- The A face. -/
abbrev faceA : Finset (Fin 4) × ℕ := (({0, 1, 2} : Finset (Fin 4)), 3)

section Ne

theorem ne_of_grade_ne {a b : Cell D₂} (h : D₂.grade a ≠ D₂.grade b) : a ≠ b := fun e => h (e ▸ rfl)
theorem A₁c_ne_H₀new : A₁c ≠ H₀new := ne_of_grade_ne (by rw [grade_A₁c, grade_H₀new]; decide)
theorem A₁c_ne_s₀new : A₁c ≠ s₀new := ne_of_grade_ne (by rw [grade_A₁c, grade_s₀new]; decide)
theorem A₂c_ne_H₀new : A₂c ≠ H₀new := ne_of_grade_ne (by rw [grade_A₂c, grade_H₀new]; decide)
theorem A₂c_ne_s₀new : A₂c ≠ s₀new := ne_of_grade_ne (by rw [grade_A₂c, grade_s₀new]; decide)
theorem b₁new_ne_H₀new : b₁new ≠ H₀new := ne_of_grade_ne (by rw [grade_b₁new, grade_H₀new]; decide)
theorem b₁new_ne_U_H : b₁new ≠ U_H := ne_of_grade_ne (by rw [grade_b₁new, grade_U_H]; decide)
theorem b₁new_ne_s₀new : b₁new ≠ s₀new := ne_of_grade_ne (by rw [grade_b₁new, grade_s₀new]; decide)
theorem b₁new_ne_U_S : b₁new ≠ U_S := ne_of_grade_ne (by rw [grade_b₁new, grade_U_S]; decide)
theorem ub₁_ne_H₀new : ub₁ ≠ H₀new := ne_of_grade_ne (by rw [grade_ub₁, grade_H₀new]; decide)
theorem ub₁_ne_s₀new : ub₁ ≠ s₀new := ne_of_grade_ne (by rw [grade_ub₁, grade_s₀new]; decide)
theorem zero_mem_scope_A₁c : (0 : Fin 4) ∈ D₂.scope A₁c := by
  change (0 : Fin 4) ∈ (D₂.cell A₁c).1; rw [cell_A₁c]; exact Finset.mem_univ _
theorem b₁new_ne_A₁c : b₁new ≠ A₁c := fun h => zero_not_mem_scope_copyB _ (h ▸ zero_mem_scope_A₁c)
theorem A₁c_ne_A₂c : A₁c ≠ A₂c := ne_of_ret_ne (by
  rw [ret₂_A₁c, ret₂_A₂c]
  intro h
  exact a₁_ne_a₂ (congrArg Subtype.val (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
    (family₂.e.injective h))))))
theorem H₀old_ne_A₁c : H₀old ≠ A₁c := ne_of_grade_ne (by rw [grade_H₀old, grade_A₁c]; decide)
theorem H₀old_ne_A₂c : H₀old ≠ A₂c := ne_of_grade_ne (by rw [grade_H₀old, grade_A₂c]; decide)
theorem H₀old_ne_b₁new : H₀old ≠ b₁new := ne_of_grade_ne (by rw [grade_H₀old, grade_b₁new]; decide)
theorem H₀old_ne_ub₁' : H₀old ≠ ub₁ := H₀old_ne_ub₁
theorem s₀old_ne_A₁c : s₀old ≠ A₁c := ne_of_grade_ne (by rw [grade_s₀old, grade_A₁c]; decide)
theorem s₀old_ne_A₂c : s₀old ≠ A₂c := ne_of_grade_ne (by rw [grade_s₀old, grade_A₂c]; decide)
theorem s₀old_ne_b₁new : s₀old ≠ b₁new := ne_of_grade_ne (by rw [grade_s₀old, grade_b₁new]; decide)
theorem a₁old_ne_a₂old : a₁old ≠ a₂old := ne_of_ret_ne (by
  rw [ret₂_a₁old, ret₂_a₂old]
  intro h
  exact a₁_ne_a₂ (congrArg Subtype.val (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
    (family₂.e.injective h))))))
theorem a₁old_ne_A₁c : a₁old ≠ A₁c := fun h => castAdd_ne_fullCell _ a₁X rfl h
theorem a₁old_ne_A₂c : a₁old ≠ A₂c := fun h => castAdd_ne_fullCell _ a₂X rfl h
theorem a₂old_ne_A₁c : a₂old ≠ A₁c := fun h => castAdd_ne_fullCell _ a₁X rfl h
theorem a₂old_ne_A₂c : a₂old ≠ A₂c := fun h => castAdd_ne_fullCell _ a₂X rfl h
theorem a₁old_ne_b₁new : a₁old ≠ b₁new := fun h =>
  three_not_mem_scope_castAdd _ (h ▸ three_mem_scope_b₁new)
theorem a₂old_ne_b₁new : a₂old ≠ b₁new := fun h =>
  three_not_mem_scope_castAdd _ (h ▸ three_mem_scope_b₁new)
theorem a₂old_ne_ub₁ : a₂old ≠ ub₁ := fun h => castAdd_ne_fullCell _ b₁X rfl (h.trans ub₁_eq)

theorem not_faceA_of_three {d : Cell D₂} (h3 : (3 : Fin 4) ∈ D₂.scope d) :
    ¬ GradedLe (D₂.cell d) faceA := fun h => by
  have := h.1 h3; revert this; decide
theorem not_faceB_of_zero {d : Cell D₂} (h0 : (0 : Fin 4) ∈ D₂.scope d) :
    ¬ GradedLe (D₂.cell d) (({1, 2, 3} : Finset (Fin 4)), 3) := fun h => by
  have := h.1 h0; revert this; decide

end Ne

/-! ### The A-face section -/

section SectionA

theorem faceA_ne_univ : faceA.1 ≠ Finset.univ := by decide
theorem H₀old_memA : GradedLe (D₂.cell H₀old) faceA := aFace_castAdd _
theorem s₀old_memA : GradedLe (D₂.cell s₀old) faceA := aFace_castAdd _
theorem a₁old_memA : GradedLe (D₂.cell a₁old) faceA := aFace_castAdd _
theorem a₂old_memA : GradedLe (D₂.cell a₂old) faceA := aFace_castAdd _
theorem faceA₁ : GradedLe (faceA.1, 1) faceA := ⟨Finset.Subset.refl _, by decide⟩
theorem faceA_le : GradedLe faceA (Finset.univ, 3) := ⟨Finset.subset_univ _, le_rfl⟩

open Classical in
/-- **The A-face section** of a face labelling `p` with proper cell `sc`: the face literally;
`p H₀old` at the copy of `H₀` and the grade-one controller and at proper grade-one cells outside
the face is replaced by `p sc`; `p s₀old` at the copy of `s₀` and the grade-two controller;
`p a₁old` at `a₁`'s controller; `p a₂old` at `a₂`'s and `b₁`'s controllers and the copy of `b₁`;
`⊥` at proper grade-two cells. -/
noncomputable def sectA (p : D₂.below faceA → ExtOrd) (sc : D₂.below faceA)
    (d : D₂.below (Finset.univ, 3)) : ExtOrd :=
  if hd : GradedLe (D₂.cell d.1) faceA then p ⟨d.1, hd⟩
  else if d.1 = H₀new ∨ d.1 = U_H then p ⟨H₀old, H₀old_memA⟩
  else if d.1 = s₀new ∨ d.1 = U_S then p ⟨s₀old, s₀old_memA⟩
  else if d.1 = A₁c then p ⟨a₁old, a₁old_memA⟩
  else if d.1 = A₂c ∨ d.1 = b₁new ∨ d.1 = ub₁ then p ⟨a₂old, a₂old_memA⟩
  else if D₂.grade d.1 = 2 then ⊥ else p sc

variable {p : D₂.below faceA → ExtOrd} {sc : D₂.below faceA}

theorem sectA_in (d : D₂.below (Finset.univ, 3)) (hd : GradedLe (D₂.cell d.1) faceA) :
    sectA p sc d = p ⟨d.1, hd⟩ := by
  classical
  unfold sectA; rw [dite_of_pos hd]
theorem sectA_H₀new : sectA p sc ⟨H₀new, memH₀new₃⟩ = p ⟨H₀old, H₀old_memA⟩ := by
  classical
  unfold sectA
  rw [dite_of_neg (not_faceA_of_three three_mem_scope_H₀new), ite_eq_left (Or.inl rfl)]
theorem sectA_U_H : sectA p sc ⟨U_H, memU_H₃⟩ = p ⟨H₀old, H₀old_memA⟩ := by
  classical
  unfold sectA; rw [dite_of_neg (not_faceA_of_three three_mem_scope_U_H), ite_eq_left (Or.inr rfl)]
theorem sectA_s₀new : sectA p sc ⟨s₀new, mems₀new₃⟩ = p ⟨s₀old, s₀old_memA⟩ := by
  classical
  unfold sectA
  rw [dite_of_neg (not_faceA_of_three three_mem_scope_s₀new),
    ite_eq_right (by rintro (h | h); exacts [s₀new_ne_H₀new h, s₀new_ne_U_H h]),
    ite_eq_left (Or.inl rfl)]
theorem sectA_U_S : sectA p sc ⟨U_S, memU_S₃⟩ = p ⟨s₀old, s₀old_memA⟩ := by
  classical
  unfold sectA
  rw [dite_of_neg (not_faceA_of_three three_mem_scope_U_S),
    ite_eq_right (by rintro (h | h); exacts [U_S_ne_H₀new h, U_S_ne_U_H h]),
    ite_eq_left (Or.inr rfl)]
theorem sectA_A₁c : sectA p sc ⟨A₁c, memA₁c₃⟩ = p ⟨a₁old, a₁old_memA⟩ := by
  classical
  unfold sectA
  rw [dite_of_neg (not_faceA_of_three three_mem_scope_A₁c),
    ite_eq_right (by rintro (h | h); exacts [A₁c_ne_H₀new h, A₁c_ne_U_H h]),
    ite_eq_right (by rintro (h | h); exacts [A₁c_ne_s₀new h, A₁c_ne_U_S h]), ite_eq_left rfl]
theorem sectA_A₂c : sectA p sc ⟨A₂c, memA₂c₃⟩ = p ⟨a₂old, a₂old_memA⟩ := by
  classical
  unfold sectA
  rw [dite_of_neg (not_faceA_of_three three_mem_scope_A₂c),
    ite_eq_right (by rintro (h | h); exacts [A₂c_ne_H₀new h, A₂c_ne_U_H h]),
    ite_eq_right (by rintro (h | h); exacts [A₂c_ne_s₀new h, A₂c_ne_U_S h]),
    ite_eq_right (fun h => A₁c_ne_A₂c h.symm), ite_eq_left (Or.inl rfl)]
theorem sectA_b₁new : sectA p sc ⟨b₁new, memb₁new₃⟩ = p ⟨a₂old, a₂old_memA⟩ := by
  classical
  unfold sectA
  rw [dite_of_neg (not_faceA_of_three three_mem_scope_b₁new),
    ite_eq_right (by rintro (h | h); exacts [b₁new_ne_H₀new h, b₁new_ne_U_H h]),
    ite_eq_right (by rintro (h | h); exacts [b₁new_ne_s₀new h, b₁new_ne_U_S h]),
    ite_eq_right b₁new_ne_A₁c, ite_eq_left (Or.inr (Or.inl rfl))]
theorem sectA_ub₁ : sectA p sc ⟨ub₁, memub₁₃⟩ = p ⟨a₂old, a₂old_memA⟩ := by
  classical
  unfold sectA
  rw [dite_of_neg (not_faceA_of_three three_mem_scope_ub₁),
    ite_eq_right (by rintro (h | h); exacts [ub₁_ne_H₀new h, ub₁_ne_U_H h]),
    ite_eq_right (by rintro (h | h); exacts [ub₁_ne_s₀new h, ub₁_ne_U_S h]),
    ite_eq_right (fun h => A₁c_ne_ub₁ h.symm), ite_eq_left (Or.inr (Or.inr rfl))]
theorem sectA_proper_out (d : D₂.below (Finset.univ, 3)) (hd : IsProper d.1)
    (hdA : ¬ GradedLe (D₂.cell d.1) faceA) :
    sectA p sc d = if D₂.grade d.1 = 2 then ⊥ else p sc := by
  classical
  have h1 : ¬ (d.1 = H₀new ∨ d.1 = U_H) := by
    rintro (e | e)
    · exact not_isProper_of_ret rfl ret₂_H₀new (e ▸ hd)
    · exact not_isProper_of_ret rfl ret₂_U_H (e ▸ hd)
  have h2 : ¬ (d.1 = s₀new ∨ d.1 = U_S) := by
    rintro (e | e)
    · exact not_isProper_of_ret rfl ret₂_s₀new (e ▸ hd)
    · exact not_isProper_of_ret rfl ret₂_U_S (e ▸ hd)
  have h3 : ¬ d.1 = A₁c := fun e => not_isProper_of_ret rfl ret₂_A₁c (e ▸ hd)
  have h4 : ¬ (d.1 = A₂c ∨ d.1 = b₁new ∨ d.1 = ub₁) := by
    rintro (e | e | e)
    · exact not_isProper_of_ret rfl ret₂_A₂c (e ▸ hd)
    · exact not_isProper_of_ret rfl ret₂_b₁new (e ▸ hd)
    · exact not_isProper_of_ret rfl ret₂_ub₁ (e ▸ hd)
  unfold sectA
  rw [dite_of_neg hdA, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]

/-- **The A face extends**: every labelling respecting the repaired semantics on the old face
`({0,1,2}, 3)` is the restriction of one respecting it on `(univ, 3)`, by the section
`(v, x, x, y, a, b, b)`. -/
theorem faceA_extendsR (p : D₂.below faceA → ExtOrd) (hp : RespectsSemanticsBelow rowsR faceA p) :
    ∃ q : D₂.below (Finset.univ, 3) → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, 3) q ∧
      ∀ d : D₂.below faceA, q (CellScheme.below.mono faceA_le d) = p d := by
  classical
  obtain ⟨s1, hs1c⟩ := D₂_complete _ hsing₁
  have hs1A : GradedLe (D₂.cell s1) faceA := by rw [hs1c]; exact ⟨by decide, by decide⟩
  have hs1P : IsProper s1 := isProper_of_cell_singleton s1 1 hs1c
  have hg1 : D₂.grade s1 = 1 := by change (D₂.cell s1).2 = 1; rw [hs1c]
  set sc : D₂.below faceA := ⟨s1, hs1A⟩ with hsc
  have hp₃ : RespectsSemanticsBelow rows₃ faceA p :=
    (respects₃_iff_of_proper faceA_ne_univ p).mpr ((respectsR_iff_of_proper faceA_ne_univ p).mp hp)
  have hp₁ : RespectsSemanticsBelow rows₃ (faceA.1, 1)
      (fun d => p (CellScheme.below.mono faceA₁ d)) :=
    (respects₃_iff_of_proper (by decide) _).mpr
      ((respectsR_iff_of_proper (by decide) _).mp (hp.mono faceA₁))
  -- the parameters
  have hvx : p sc ≤ p ⟨H₀old, H₀old_memA⟩ := by
    obtain ⟨Xi, hXi, hle⟩ := hp.availability sc ⟨H₀old, H₀old_memA⟩ (by
        change (D₂.cell s1).1 ⊆ D₂.scope H₀old; rw [hs1c, scope_H₀old']; decide)
      (by change (D₂.cell s1).2 = D₂.grade H₀old; rw [hs1c, grade_H₀old])
    have : Xi = ⟨H₀old, H₀old_memA⟩ :=
      Subtype.ext (cell_inj_low hXi (by
        change (D₂.cell Xi.1).2 ≤ 2; rw [hXi]
        exact (show D₂.grade H₀old ≤ 2 by rw [grade_H₀old]; decide)))
    rw [this] at hle; exact hle
  have hyx := s₀old_le_H₀old_of_respects hp₃ s₀old_memA H₀old_memA
  have hab := a₁old_le_a₂old' hp a₁old_memA a₂old_memA
  have hbx := a₂old_le_H₀old' hp a₂old_memA H₀old_memA
  have hby := a₂old_le_s₀old' hp a₂old_memA s₀old_memA
  have hsub : GradedLe (D₂.cell sc.1) (D₂.cell a₂old) := by rw [cell_a₂old]; exact hs1A
  have horb := a₁old_eq_R₃_min' hp a₁old_memA a₂old_memA sc hs1P hg1 hsub
  have hfix := fix_min_a₂old' hp a₂old_memA sc hs1P hg1 hsub
  have hcoup := a₂old_eq_bot_of_a₁old' hp a₁old_memA a₂old_memA
  have vis : ∀ (X : Cell D₂) (h : GradedLe (D₂.cell X) faceA) (k : ℕ), D₂.grade X = k →
      SelfVis k (p ⟨X, h⟩) := fun X h k hk => by
    have := selfVis_at' hp ⟨X, h⟩
    change SelfVis (D₂.grade X) _ at this
    rwa [hk] at this
  have hvis : SelfVis 1 (p sc) := by
    have := selfVis_at' hp sc; rwa [show D₂.grade sc.1 = 1 from hg1] at this
  -- proper cells of the face
  have hproper : ∀ d : D₂.below faceA, IsProper d.1 →
      p d = if D₂.grade d.1 = 2 then ⊥ else p sc := by
    intro d hd
    have hnd : ¬ mute₂ d.1 := not_mute₂_of_low (by decide) ⟨d.1, d.2.trans faceA_le⟩
    by_cases h2 : D₂.grade d.1 = 2
    · rw [ite_eq_left h2]; exact proper_two_eq_bot' hp₃ d hd h2
    · rw [ite_eq_right h2]
      have hg2 : D₂.grade d.1 ≤ 2 := by
        obtain ⟨c, hc⟩ := hd; rw [← gradeP_le_of_proper hnd hc]; exact c.gradeP_le_two
      have hg1' : D₂.grade d.1 ≤ 1 := by omega
      exact const_of_respects rfl hp₁ ⟨H₀old, by rw [cell_H₀old]; exact GradedLe.refl _⟩ cell_H₀old
        ⟨d.1, ⟨d.2.1, hg1'⟩⟩ ⟨s1, ⟨hs1A.1, hg1.le⟩⟩ hd hs1P
  have L : Legal₃ (p sc) (p ⟨H₀old, H₀old_memA⟩) (p ⟨H₀old, H₀old_memA⟩) (p ⟨s₀old, s₀old_memA⟩)
      (p ⟨a₁old, a₁old_memA⟩) (p ⟨a₂old, a₂old_memA⟩) (p ⟨a₂old, a₂old_memA⟩) :=
    ⟨⟨hvis, hvx, le_rfl, id, vis _ _ 1 grade_H₀old, vis _ _ 1 grade_H₀old, vis _ _ 2 grade_s₀old,
      hyx, by rw [min_eq_right hyx]; exact vis _ _ 2 grade_s₀old⟩, hab, hbx, le_rfl, hby,
      vis _ _ 3 grade_a₁old, vis _ _ 3 grade_a₂old, vis _ _ 3 grade_a₂old,
      by rw [min_eq_right hbx]; exact vis _ _ 3 grade_a₂old, horb, hfix, hcoup,
      by rw [min_eq_right hbx]; exact id⟩
  have S : Shape₃ (sectA p sc) (p sc) (p ⟨H₀old, H₀old_memA⟩) (p ⟨H₀old, H₀old_memA⟩)
      (p ⟨s₀old, s₀old_memA⟩) (p ⟨a₁old, a₁old_memA⟩) (p ⟨a₂old, a₂old_memA⟩)
      (p ⟨a₂old, a₂old_memA⟩) :=
    ⟨sectA_in _ H₀old_memA, sectA_H₀new, sectA_U_H,
      by rw [sectA_in ⟨s₀old, mems₀old₃⟩ s₀old_memA, min_eq_right hyx], sectA_s₀new, sectA_U_S,
      sectA_in _ a₁old_memA, sectA_A₁c, sectA_in _ a₂old_memA, sectA_A₂c, sectA_b₁new, sectA_ub₁,
      fun d hd => by
        by_cases hdA : GradedLe (D₂.cell d.1) faceA
        · rw [sectA_in d hdA]; exact hproper ⟨d.1, hdA⟩ hd
        · exact sectA_proper_out d hd hdA⟩
  exact ⟨sectA p sc, respects_of_shape₃ L S, fun d => sectA_in _ d.2⟩

end SectionA

/-! ### The B-face section -/

section SectionB

/-- The B face. -/
abbrev faceB : Finset (Fin 4) × ℕ := (({1, 2, 3} : Finset (Fin 4)), 3)

theorem faceB_ne_univ : faceB.1 ≠ Finset.univ := by decide
theorem H₀new_memB : GradedLe (D₂.cell H₀new) faceB := copyB_mem _
theorem s₀new_memB : GradedLe (D₂.cell s₀new) faceB := copyB_mem _
theorem b₁new_memB : GradedLe (D₂.cell b₁new) faceB := copyB_mem _
theorem faceB₁ : GradedLe (faceB.1, 1) faceB := ⟨Finset.Subset.refl _, by decide⟩
theorem faceB_le : GradedLe faceB (Finset.univ, 3) := ⟨Finset.subset_univ _, le_rfl⟩

theorem a₁old_ne_H₀old : a₁old ≠ H₀old := ne_of_grade_ne (by rw [grade_a₁old, grade_H₀old]; decide)
theorem a₁old_ne_U_H : a₁old ≠ U_H := ne_of_grade_ne (by rw [grade_a₁old, grade_U_H]; decide)
theorem a₁old_ne_s₀old : a₁old ≠ s₀old := ne_of_grade_ne (by rw [grade_a₁old, grade_s₀old]; decide)
theorem a₁old_ne_U_S : a₁old ≠ U_S := ne_of_grade_ne (by rw [grade_a₁old, grade_U_S]; decide)
theorem a₂old_ne_H₀old : a₂old ≠ H₀old := ne_of_grade_ne (by rw [grade_a₂old, grade_H₀old]; decide)
theorem a₂old_ne_U_H : a₂old ≠ U_H := ne_of_grade_ne (by rw [grade_a₂old, grade_U_H]; decide)
theorem a₂old_ne_s₀old : a₂old ≠ s₀old := ne_of_grade_ne (by rw [grade_a₂old, grade_s₀old]; decide)
theorem a₂old_ne_U_S : a₂old ≠ U_S := ne_of_grade_ne (by rw [grade_a₂old, grade_U_S]; decide)
theorem zero_mem_scope_A₂c : (0 : Fin 4) ∈ D₂.scope A₂c := by
  change (0 : Fin 4) ∈ (D₂.cell A₂c).1; rw [cell_A₂c]; exact Finset.mem_univ _
theorem zero_mem_scope_ub₁ : (0 : Fin 4) ∈ D₂.scope ub₁ := by
  change (0 : Fin 4) ∈ (D₂.cell ub₁).1; rw [cell_ub₁]; exact Finset.mem_univ _
theorem zero_mem_scope_a₁old : (0 : Fin 4) ∈ D₂.scope a₁old := zero_mem_scope_castAdd a₁X₀ rfl
theorem zero_mem_scope_a₂old : (0 : Fin 4) ∈ D₂.scope a₂old := zero_mem_scope_castAdd a₂X₀ rfl

open Classical in
/-- **The B-face section** of a face labelling `p` with proper cell `sc`: the face literally;
`p H₀new` at the old occurrence and the grade-one controller; `min (p H₀new) (p s₀new)` at the old
level-two witness; `p s₀new` at the grade-two controller; `R₃ (min (p sc) (p b₁new))` at the four
`a` cells; `p b₁new` at `b₁`'s controller; proper cells outside the face by grade. -/
noncomputable def sectB (p : D₂.below faceB → ExtOrd) (sc : D₂.below faceB)
    (d : D₂.below (Finset.univ, 3)) : ExtOrd :=
  if hd : GradedLe (D₂.cell d.1) faceB then p ⟨d.1, hd⟩
  else if d.1 = H₀old ∨ d.1 = U_H then p ⟨H₀new, H₀new_memB⟩
  else if d.1 = s₀old then min (p ⟨H₀new, H₀new_memB⟩) (p ⟨s₀new, s₀new_memB⟩)
  else if d.1 = U_S then p ⟨s₀new, s₀new_memB⟩
  else if d.1 = a₁old ∨ d.1 = A₁c ∨ d.1 = a₂old ∨ d.1 = A₂c then
    extVisibilityReplace (min (p sc) (p ⟨b₁new, b₁new_memB⟩)) 3 3
  else if d.1 = ub₁ then p ⟨b₁new, b₁new_memB⟩
  else if D₂.grade d.1 = 2 then ⊥ else p sc

variable {p : D₂.below faceB → ExtOrd} {sc : D₂.below faceB}

theorem sectB_in (d : D₂.below (Finset.univ, 3)) (hd : GradedLe (D₂.cell d.1) faceB) :
    sectB p sc d = p ⟨d.1, hd⟩ := by
  classical
  unfold sectB; rw [dite_of_pos hd]
theorem sectB_H₀old : sectB p sc ⟨H₀old, memH₀old₃⟩ = p ⟨H₀new, H₀new_memB⟩ := by
  classical
  unfold sectB
  rw [dite_of_neg (not_faceB_of_zero zero_mem_scope_H₀old), ite_eq_left (Or.inl rfl)]
theorem sectB_U_H : sectB p sc ⟨U_H, memU_H₃⟩ = p ⟨H₀new, H₀new_memB⟩ := by
  classical
  unfold sectB
  rw [dite_of_neg (not_faceB_of_zero zero_mem_scope_U_H), ite_eq_left (Or.inr rfl)]
theorem sectB_s₀old :
    sectB p sc ⟨s₀old, mems₀old₃⟩ = min (p ⟨H₀new, H₀new_memB⟩) (p ⟨s₀new, s₀new_memB⟩) := by
  classical
  unfold sectB
  rw [dite_of_neg (not_faceB_of_zero zero_mem_scope_s₀old),
    ite_eq_right (by rintro (h | h); exacts [s₀old_ne_H₀old h, s₀old_ne_U_H h]), ite_eq_left rfl]
theorem sectB_U_S : sectB p sc ⟨U_S, memU_S₃⟩ = p ⟨s₀new, s₀new_memB⟩ := by
  classical
  unfold sectB
  rw [dite_of_neg (not_faceB_of_zero zero_mem_scope_U_S),
    ite_eq_right (by rintro (h | h); exacts [U_S_ne_H₀old h, U_S_ne_U_H h]),
    ite_eq_right U_S_ne_s₀old, ite_eq_left rfl]
theorem sectB_a (X : Cell D₂) (h : GradedLe (D₂.cell X) (Finset.univ, 3))
    (h0 : (0 : Fin 4) ∈ D₂.scope X) (h1 : X ≠ H₀old) (h2 : X ≠ U_H) (h3 : X ≠ s₀old)
    (h4 : X ≠ U_S) (ha : X = a₁old ∨ X = A₁c ∨ X = a₂old ∨ X = A₂c) :
    sectB p sc ⟨X, h⟩ = extVisibilityReplace (min (p sc) (p ⟨b₁new, b₁new_memB⟩)) 3 3 := by
  classical
  unfold sectB
  rw [dite_of_neg (not_faceB_of_zero h0), ite_eq_right (by rintro (e | e); exacts [h1 e, h2 e]),
    ite_eq_right h3, ite_eq_right h4, ite_eq_left ha]
theorem sectB_a₁old :
    sectB p sc ⟨a₁old, mema₁old₃⟩ = extVisibilityReplace (min (p sc) (p ⟨b₁new, b₁new_memB⟩)) 3 3 :=
  sectB_a _ _ zero_mem_scope_a₁old a₁old_ne_H₀old a₁old_ne_U_H a₁old_ne_s₀old a₁old_ne_U_S
    (Or.inl rfl)
theorem sectB_A₁c :
    sectB p sc ⟨A₁c, memA₁c₃⟩ = extVisibilityReplace (min (p sc) (p ⟨b₁new, b₁new_memB⟩)) 3 3 :=
  sectB_a _ _ zero_mem_scope_A₁c (fun h => H₀old_ne_A₁c h.symm) A₁c_ne_U_H
    (fun h => s₀old_ne_A₁c h.symm) A₁c_ne_U_S (Or.inr (Or.inl rfl))
theorem sectB_a₂old :
    sectB p sc ⟨a₂old, mema₂old₃⟩ = extVisibilityReplace (min (p sc) (p ⟨b₁new, b₁new_memB⟩)) 3 3 :=
  sectB_a _ _ zero_mem_scope_a₂old a₂old_ne_H₀old a₂old_ne_U_H a₂old_ne_s₀old a₂old_ne_U_S
    (Or.inr (Or.inr (Or.inl rfl)))
theorem sectB_A₂c :
    sectB p sc ⟨A₂c, memA₂c₃⟩ = extVisibilityReplace (min (p sc) (p ⟨b₁new, b₁new_memB⟩)) 3 3 :=
  sectB_a _ _ zero_mem_scope_A₂c (fun h => H₀old_ne_A₂c h.symm) A₂c_ne_U_H
    (fun h => s₀old_ne_A₂c h.symm) A₂c_ne_U_S (Or.inr (Or.inr (Or.inr rfl)))
theorem sectB_ub₁ : sectB p sc ⟨ub₁, memub₁₃⟩ = p ⟨b₁new, b₁new_memB⟩ := by
  classical
  have h4 : ¬ (ub₁ = a₁old ∨ ub₁ = A₁c ∨ ub₁ = a₂old ∨ ub₁ = A₂c) := by
    rintro (h | h | h | h)
    exacts [a₁old_ne_ub₁ h.symm, A₁c_ne_ub₁ h.symm, a₂old_ne_ub₁ h.symm, A₂c_ne_ub₁ h.symm]
  unfold sectB
  rw [dite_of_neg (not_faceB_of_zero zero_mem_scope_ub₁),
    ite_eq_right (by rintro (h | h); exacts [H₀old_ne_ub₁ h.symm, ub₁_ne_U_H h]),
    ite_eq_right (fun h => s₀old_ne_ub₁ h.symm), ite_eq_right ub₁_ne_U_S, ite_eq_right h4,
    ite_eq_left rfl]
theorem sectB_proper_out (d : D₂.below (Finset.univ, 3)) (hd : IsProper d.1)
    (hdB : ¬ GradedLe (D₂.cell d.1) faceB) :
    sectB p sc d = if D₂.grade d.1 = 2 then ⊥ else p sc := by
  classical
  have h1 : ¬ (d.1 = H₀old ∨ d.1 = U_H) := by
    rintro (e | e)
    · exact not_isProper_of_ret rfl ret₂_H₀old (e ▸ hd)
    · exact not_isProper_of_ret rfl ret₂_U_H (e ▸ hd)
  have h2 : ¬ d.1 = s₀old := fun e => not_isProper_of_ret rfl ret₂_s₀old (e ▸ hd)
  have h3 : ¬ d.1 = U_S := fun e => not_isProper_of_ret rfl ret₂_U_S (e ▸ hd)
  have h4 : ¬ (d.1 = a₁old ∨ d.1 = A₁c ∨ d.1 = a₂old ∨ d.1 = A₂c) := by
    rintro (e | e | e | e)
    · exact not_isProper_of_ret rfl ret₂_a₁old (e ▸ hd)
    · exact not_isProper_of_ret rfl ret₂_A₁c (e ▸ hd)
    · exact not_isProper_of_ret rfl ret₂_a₂old (e ▸ hd)
    · exact not_isProper_of_ret rfl ret₂_A₂c (e ▸ hd)
  have h5 : ¬ d.1 = ub₁ := fun e => not_isProper_of_ret rfl ret₂_ub₁ (e ▸ hd)
  unfold sectB
  rw [dite_of_neg hdB, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
    ite_eq_right h5]

/-- **The B face extends**: every labelling respecting the repaired semantics on the copy face
`({1,2,3}, 3)` is the restriction of one respecting it on `(univ, 3)`, by the section
`(v, x, x, y, r, r, b)` with `r = R₃ (min v b)`. -/
theorem faceB_extendsR (p : D₂.below faceB → ExtOrd) (hp : RespectsSemanticsBelow rowsR faceB p) :
    ∃ q : D₂.below (Finset.univ, 3) → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, 3) q ∧
      ∀ d : D₂.below faceB, q (CellScheme.below.mono faceB_le d) = p d := by
  classical
  obtain ⟨s1, hs1c⟩ := D₂_complete _ hsing₁
  have hs1B : GradedLe (D₂.cell s1) faceB := by rw [hs1c]; exact ⟨by decide, by decide⟩
  have hs1P : IsProper s1 := isProper_of_cell_singleton s1 1 hs1c
  have hg1 : D₂.grade s1 = 1 := by change (D₂.cell s1).2 = 1; rw [hs1c]
  set sc : D₂.below faceB := ⟨s1, hs1B⟩ with hsc
  have hp₃ : RespectsSemanticsBelow rows₃ faceB p :=
    (respects₃_iff_of_proper faceB_ne_univ p).mpr ((respectsR_iff_of_proper faceB_ne_univ p).mp hp)
  have hp₁ : RespectsSemanticsBelow rows₃ (faceB.1, 1)
      (fun d => p (CellScheme.below.mono faceB₁ d)) :=
    (respects₃_iff_of_proper (by decide) _).mpr
      ((respectsR_iff_of_proper (by decide) _).mp (hp.mono faceB₁))
  have hvx : p sc ≤ p ⟨H₀new, H₀new_memB⟩ := by
    obtain ⟨Xi, hXi, hle⟩ := hp.availability sc ⟨H₀new, H₀new_memB⟩ (by
        change (D₂.cell s1).1 ⊆ D₂.scope H₀new; rw [hs1c, scope_H₀new]; decide)
      (by change (D₂.cell s1).2 = D₂.grade H₀new; rw [hs1c, grade_H₀new])
    have : Xi = ⟨H₀new, H₀new_memB⟩ :=
      Subtype.ext (cell_inj_low hXi (by
        change (D₂.cell Xi.1).2 ≤ 2; rw [hXi]
        exact (show D₂.grade H₀new ≤ 2 by rw [grade_H₀new]; decide)))
    rw [this] at hle; exact hle
  have hyx := s₀new_le_H₀new_of_respects hp₃ s₀new_memB H₀new_memB
  have hby := b₁new_le_s₀new' hp b₁new_memB s₀new_memB
  have hbx := b₁new_le_H₀new' hp b₁new_memB H₀new_memB
  have hsub : GradedLe (D₂.cell sc.1) (D₂.cell b₁new) := by rw [cell_b₁new]; exact hs1B
  have hfix := fix_min_b₁new' hp b₁new_memB sc hs1P hg1 hsub
  have vis : ∀ (X : Cell D₂) (h : GradedLe (D₂.cell X) faceB) (k : ℕ), D₂.grade X = k →
      SelfVis k (p ⟨X, h⟩) := fun X h k hk => by
    have := selfVis_at' hp ⟨X, h⟩
    change SelfVis (D₂.grade X) _ at this
    rwa [hk] at this
  have hvis : SelfVis 1 (p sc) := by
    have := selfVis_at' hp sc; rwa [show D₂.grade sc.1 = 1 from hg1] at this
  have visb : SelfVis 3 (p ⟨b₁new, b₁new_memB⟩) := vis _ _ 3 grade_b₁new
  have hrb : extVisibilityReplace (min (p sc) (p ⟨b₁new, b₁new_memB⟩)) 3 3 ≤
      p ⟨b₁new, b₁new_memB⟩ :=
    (R₃_mono (min_le_right _ _)).trans (evr_eq_self_of_selfVis visb 3).le
  have hproper : ∀ d : D₂.below faceB, IsProper d.1 →
      p d = if D₂.grade d.1 = 2 then ⊥ else p sc := by
    intro d hd
    have hnd : ¬ mute₂ d.1 := not_mute₂_of_low (by decide) ⟨d.1, d.2.trans faceB_le⟩
    by_cases h2 : D₂.grade d.1 = 2
    · rw [ite_eq_left h2]; exact proper_two_eq_bot' hp₃ d hd h2
    · rw [ite_eq_right h2]
      have hg2 : D₂.grade d.1 ≤ 2 := by
        obtain ⟨c, hc⟩ := hd; rw [← gradeP_le_of_proper hnd hc]; exact c.gradeP_le_two
      have hg1' : D₂.grade d.1 ≤ 1 := by omega
      exact const_of_respects rfl hp₁ ⟨H₀new, by rw [cell_H₀new]; exact GradedLe.refl _⟩ cell_H₀new
        ⟨d.1, ⟨d.2.1, hg1'⟩⟩ ⟨s1, ⟨hs1B.1, hg1.le⟩⟩ hd hs1P
  have L : Legal₃ (p sc) (p ⟨H₀new, H₀new_memB⟩) (p ⟨H₀new, H₀new_memB⟩) (p ⟨s₀new, s₀new_memB⟩)
      (extVisibilityReplace (min (p sc) (p ⟨b₁new, b₁new_memB⟩)) 3 3)
      (extVisibilityReplace (min (p sc) (p ⟨b₁new, b₁new_memB⟩)) 3 3) (p ⟨b₁new, b₁new_memB⟩) :=
    ⟨⟨hvis, hvx, le_rfl, id, vis _ _ 1 grade_H₀new, vis _ _ 1 grade_H₀new, vis _ _ 2 grade_s₀new,
      hyx, by rw [min_eq_right hyx]; exact vis _ _ 2 grade_s₀new⟩, le_rfl, hrb.trans hbx, hrb, hby,
      evr_selfVis 3 _, evr_selfVis 3 _, visb, by rw [min_eq_right hbx]; exact visb, rfl, hfix, id,
      by rw [min_eq_right hbx]; exact id⟩
  have S : Shape₃ (sectB p sc) (p sc) (p ⟨H₀new, H₀new_memB⟩) (p ⟨H₀new, H₀new_memB⟩)
      (p ⟨s₀new, s₀new_memB⟩) (extVisibilityReplace (min (p sc) (p ⟨b₁new, b₁new_memB⟩)) 3 3)
      (extVisibilityReplace (min (p sc) (p ⟨b₁new, b₁new_memB⟩)) 3 3) (p ⟨b₁new, b₁new_memB⟩) :=
    ⟨sectB_H₀old, sectB_in _ H₀new_memB, sectB_U_H, sectB_s₀old, sectB_in _ s₀new_memB, sectB_U_S,
      sectB_a₁old, sectB_A₁c, sectB_a₂old, sectB_A₂c, sectB_in _ b₁new_memB, sectB_ub₁,
      fun d hd => by
        by_cases hdB : GradedLe (D₂.cell d.1) faceB
        · rw [sectB_in d hdB]; exact hproper ⟨d.1, hdB⟩ hd
        · exact sectB_proper_out d hd hdB⟩
  exact ⟨sectB p sc, respects_of_shape₃ L S, fun d => sectB_in _ d.2⟩

end SectionB

end VaughtConjecture.Knight
