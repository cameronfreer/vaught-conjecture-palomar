/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FullRowLifting

/-! # Interpolating a finite table of self-visible values

When all sources and targets are self-visible at K, source order and the bottom
read suffice to construct a bounded-commuting monotone map. Take the finite upper
envelope: at a nonbottom x, the least target whose source is at least x, or top
if there is none. Source cuts are invariant under every bounded replacement.

This map need not itself be a faithful witness at thresholds above K. For
positive-cap lifting, the existing source-block repair theorem supplies exactly
that missing step. This eliminates infinite shifter variables from the
grade-one lifting criterion, retaining finite occurrence-indexed label variables.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

section Interpolation

variable {X : Type*} [Fintype X]

open Classical in
/-- Finite upper envelope, with the actual bottom input treated separately. -/
noncomputable def orderInterpolate (E r : X → ExtOrd) (x : ExtOrd) : ExtOrd :=
  if x = ⊥ then ⊥ else Finset.univ.inf (fun i => if x ≤ E i then r i else ⊤)

theorem orderInterpolate_bot (E r : X → ExtOrd) : orderInterpolate E r ⊥ = ⊥ := by
  simp [orderInterpolate]

theorem orderInterpolate_mono (E r : X → ExtOrd) : Monotone (orderInterpolate E r) := by
  classical
  intro x y hxy
  by_cases hx : x = ⊥
  · rw [hx, orderInterpolate_bot]
    exact bot_le
  have hy : y ≠ ⊥ := fun hy => hx (le_bot_iff.mp (hy ▸ hxy))
  simp only [orderInterpolate, ite_eq_right hx, ite_eq_right hy]
  apply Finset.le_inf
  intro i _
  by_cases hi : y ≤ E i
  · rw [ite_eq_left hi]
    have hb := Finset.inf_le (f := fun j => if x ≤ E j then r j else ⊤)
      (Finset.mem_univ i)
    rwa [ite_eq_left (hxy.trans hi)] at hb
  · rw [ite_eq_right hi]
    exact le_top

theorem orderInterpolate_visible {E r : X → ExtOrd} {K : ℕ}
    (hr : ∀ i, SelfVis K (r i)) (x : ExtOrd) : SelfVis K (orderInterpolate E r x) := by
  classical
  unfold orderInterpolate
  split_ifs
  · exact extVisibilityReplace_bot _ _
  · apply Finset.inf_induction (p := SelfVis K) (extVisibilityReplace_top _ _)
      (fun _ ha _ hb => selfVis_min ha hb)
    intro i _
    split_ifs
    · exact hr i
    · exact extVisibilityReplace_top _ _

/-- The interpolation commutes with all replacements at thresholds at most K. -/
theorem orderInterpolate_bounded {E r : X → ExtOrd} {K : ℕ}
    (hE : ∀ i, SelfVis K (E i)) (hr : ∀ i, SelfVis K (r i)) :
    BoundedMap K (orderInterpolate E r) where
  bot := orderInterpolate_bot E r
  mono := orderInterpolate_mono E r
  comm x k i hk hi := by
    classical
    rw [evr_eq_self_of_selfVis ((orderInterpolate_visible hr x).mono hk) i]
    by_cases hx : x = ⊥
    · rw [hx, extVisibilityReplace_bot]
    · have he : extVisibilityReplace x k i ≠ ⊥ := extVisibilityReplace_ne_bot hx k i
      simp only [orderInterpolate, ite_eq_right hx, ite_eq_right he]
      apply Finset.inf_congr rfl
      intro j _
      simp only [replace_le_visible_cut_iff (hE j) hk hi]

/-- Equal source occurrences must have equal targets, as a consequence of the
two source-order implications. No quotient of the occurrences is taken. -/
theorem orderInterpolate_read {E r : X → ExtOrd}
    (hord : ∀ i j, E i ≤ E j → r i ≤ r j)
    (hbot : ∀ i, E i = ⊥ → r i = ⊥) (i : X) : orderInterpolate E r (E i) = r i := by
  classical
  by_cases hi : E i = ⊥
  · rw [hi, orderInterpolate_bot, hbot i hi]
  simp only [orderInterpolate, ite_eq_right hi]
  apply le_antisymm
  · have hh := Finset.inf_le (f := fun j => if E i ≤ E j then r j else ⊤)
      (Finset.mem_univ i)
    simpa only [ite_eq_left le_rfl] using hh
  · apply Finset.le_inf
    intro j _
    split_ifs with hij
    · exact hord i j hij
    · exact le_top

end Interpolation

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

/-- Finite occurrence constraints only: visibility, source order, source-bottom
readback, protected labels, and ambient caps. There is no scalar-map variable. -/
def OrderQuery {X : Type*} (embed : X → D.below BJ) (p : X → ExtOrd)
    (q : D.below BJ → ExtOrd) (γ : ExtOrd) : Prop :=
  ∃ c : Controller D BJ, ∃ r : D.below BJ → ExtOrd,
    (∀ d, SelfVis BJ.2 (r d)) ∧
    (∀ d e, c.row sem d ≤ c.row sem e → r d ≤ r e) ∧
    (∀ d, c.row sem d = ⊥ → r d = ⊥) ∧ Boundary embed p q γ r

theorem orderQuery_of_lift (hgrade : BJ.2 = 1) (c₀ : Controller D BJ)
    {X : Type*} {embed : X → D.below BJ} {p : X → ExtOrd}
    {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (h : HasLift (sem := sem) embed p q γ) : OrderQuery (sem := sem) embed p q γ := by
  obtain ⟨r, hr, hb⟩ := h
  obtain ⟨c, τ, hτ, _, he⟩ := exists_full_row_representation hgrade c₀ hr
  refine ⟨c, r, ?_, ?_, ?_, hb⟩
  · intro d
    have hv : SelfVis (D.grade d.1) (r d) := (hr.orderly d).symm
    rwa [grade_eq_one hgrade d, ← hgrade] at hv
  · intro d e hde
    rw [← he d, ← he e]
    exact hτ.mono hde
  · intro d hd
    rw [← he d, hd, hτ.bot]

/-- The finite order query suffices at positive cap: first interpolate the
visible table, then repair every nested locality using the ambient bottom pattern. -/
theorem lift_of_orderQuery (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    {X : Type*} {embed : X → D.below BJ} {p : X → ExtOrd}
    {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) (hγ : γ ≠ ⊥)
    (h : OrderQuery (sem := sem) embed p q γ) : HasLift (sem := sem) embed p q γ := by
  classical
  let := Fintype.ofFinite (D.below BJ)
  obtain ⟨c, r, hv, hord, hbot, hb⟩ := h
  have hE : ∀ d, SelfVis BJ.2 (c.row sem d) := by
    intro d
    have hh : SelfVis (D.grade d.1) (c.row sem d) := ((c.row_respects hc).orderly d).symm
    rwa [grade_eq_one hgrade d, ← hgrade] at hh
  have he := funext (orderInterpolate_read hord hbot)
  have hcap : ∀ d, min (orderInterpolate (c.row sem) r (c.row sem d)) γ = min (q d) γ :=
    fun d => by rw [orderInterpolate_read hord hbot]; exact hb.1 d
  have hr := map_respects_of_positive_cap_agreement (c.row_respects hc) hq
    (fun d => d.2.2) (orderInterpolate_bounded hE hv) hγ hcap
  exact ⟨r, he ▸ hr, hb⟩

/-- Exact finite-variable criterion. The finite carrier is not being confused
with a bounded alphabet: the remaining label variables are still ExtOrd values. -/
theorem lift_iff_orderQuery (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    (c₀ : Controller D BJ) {X : Type*} {embed : X → D.below BJ}
    {p : X → ExtOrd} {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) (hγ : γ ≠ ⊥) :
    HasLift (sem := sem) embed p q γ ↔ OrderQuery (sem := sem) embed p q γ :=
  ⟨orderQuery_of_lift hgrade c₀, lift_of_orderQuery hc hgrade hq hγ⟩

end VaughtConjecture.Knight.FullRowLifting
