/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrbitPrefixSupport

/-! # Right-filling an unused decoder gap

This is the gap arithmetic from `vc-notes/simplification/note4.md`, Section 2.
For a finite grid `G`, previous ceiling `L`, and next occupied floor `B`, the gap
is filled at `max L (floor G B)`. It stays between the two occupied pieces, reaches
every grid cut below `B`, preserves cap agreement, and introduces no unsupported
orbit or visibility defect.

These facts do not construct the paired normalization or its full decoder.
Matching the occupied groups of two profiles and locating their last common
source-grid cut remain separate obligations of the decoder comparison theorem.
The grid is explicit and finite; no nonexistent maximum below an arbitrary limit
ordinal is used. In the proposed construction it is the finite grid below the
chosen coded ceiling.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.RightFilledGap

open Transform Value ExtOrd

/-- The greatest grid value below the next floor, or bottom if none qualifies. -/
noncomputable def floor (G : Finset ExtOrd) (B : ExtOrd) : ExtOrd :=
  G.sup (fun z => if z ≤ B then z else ⊥)

theorem floor_le (G : Finset ExtOrd) (B : ExtOrd) : floor G B ≤ B := by
  apply Finset.sup_le
  intro z _
  split_ifs with hz
  · exact hz
  · exact bot_le

theorem le_floor {G : Finset ExtOrd} {h B : ExtOrd} (hh : h ∈ G) (hle : h ≤ B) :
    h ≤ floor G B := by
  unfold floor
  apply Finset.le_sup_of_le hh
  simp only [ite_eq_left hle, le_refl]

theorem floor_mono (G : Finset ExtOrd) : Monotone (floor G) := by
  intro B C hBC
  apply Finset.sup_mono_fun
  intro z _
  by_cases hz : z ≤ B
  · simp only [ite_eq_left hz, ite_eq_left (hz.trans hBC), le_refl]
  · simp only [ite_eq_right hz, bot_le]

theorem floor_eq_self {G : Finset ExtOrd} {h : ExtOrd} (hh : h ∈ G) : floor G h = h :=
  le_antisymm (floor_le G h) (le_floor hh le_rfl)

/-- The finite grid floor commutes with capping at a grid point. -/
theorem floor_cap {G : Finset ExtOrd} {h : ExtOrd} (hh : h ∈ G) (B : ExtOrd) :
    floor G (min B h) = min (floor G B) h := by
  rw [monotone_min_apply (floor_mono G), floor_eq_self hh]

/-- A finite maximum creates no extra value between the grid points. -/
theorem floor_eq_bot_or_mem (G : Finset ExtOrd) (B : ExtOrd) :
    floor G B = ⊥ ∨ floor G B ∈ G := by
  apply Finset.sup_induction (p := fun z => z = ⊥ ∨ z ∈ G)
  · exact Or.inl rfl
  · intro a ha b hb
    rcases le_total a b with hab | hba
    · simpa only [sup_eq_right.mpr hab] using hb
    · simpa only [sup_eq_left.mpr hba] using ha
  · intro z hz
    split_ifs
    · exact Or.inr hz
    · exact Or.inl rfl

/-- The right-filled value of an unused strip. -/
noncomputable def fill (G : Finset ExtOrd) (L B : ExtOrd) : ExtOrd := max L (floor G B)

theorem le_fill (G : Finset ExtOrd) (L B : ExtOrd) : L ≤ fill G L B := le_max_left _ _

theorem fill_le {G : Finset ExtOrd} {L B : ExtOrd} (hLB : L ≤ B) : fill G L B ≤ B :=
  max_le hLB (floor_le G B)

/-- Filling from the right reaches the cut even when the preceding ceiling is
strictly below it. This is the gap preceding a changed upper orbit. -/
theorem cut_le_fill {G : Finset ExtOrd} {h L B : ExtOrd} (hh : h ∈ G) (hB : h ≤ B) :
    h ≤ fill G L B := (le_floor hh hB).trans (le_max_right _ _)

/-- Two corresponding unused strips agree under a grid cut whenever both their
preceding ceilings and following floors agree under that cut. -/
theorem fill_cap_agree {G : Finset ExtOrd} {h L L' B B' : ExtOrd} (hh : h ∈ G)
    (hL : min L h = min L' h) (hB : min B h = min B' h) :
    min (fill G L B) h = min (fill G L' B') h := by
  have hf : min (floor G B) h = min (floor G B') h := by
    rw [← floor_cap hh, ← floor_cap hh, hB]
  simp only [fill, min_max_distrib_right]
  rw [hL, hf]

/-- If both next occupied pieces begin above the cut, no agreement of the earlier
ceilings is needed: both gaps already reach the cut. -/
theorem fill_cap_eq_of_next_ge {G : Finset ExtOrd} {h L L' B B' : ExtOrd}
    (hh : h ∈ G) (hB : h ≤ B) (hB' : h ≤ B') :
    min (fill G L B) h = min (fill G L' B') h := by
  rw [min_eq_right (cut_le_fill hh hB), min_eq_right (cut_le_fill hh hB')]

theorem fill_selfVis {G : Finset ExtOrd} {K : ℕ} {L B : ExtOrd}
    (hL : SelfVis K L) (hG : ∀ z ∈ G, SelfVis K z) : SelfVis K (fill G L B) := by
  have hf : SelfVis K (floor G B) := by
    rcases floor_eq_bot_or_mem G B with hbot | hmem
    · rw [hbot]; exact extVisibilityReplace_bot K K
    · exact hG _ hmem
  rcases le_total L (floor G B) with h | h
  · rw [fill, max_eq_right h]; exact hf
  · rw [fill, max_eq_left h]; exact hL

/-- Right-filling preserves the boundary-orbit support invariant: it returns the
previous supported ceiling, a grid value, or bottom. -/
theorem fill_supported {D : Type*} {G : Finset ExtOrd} {K : ℕ} {p : D → ExtOrd}
    {L B : ExtOrd} (hL : OrbitPrefixSupport.Supported K (G : Set ExtOrd) p L) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (fill G L B) := by
  rcases le_total L (floor G B) with h | h
  · rw [fill, max_eq_right h]
    rcases floor_eq_bot_or_mem G B with hbot | hmem
    · exact Or.inl hbot
    · exact Or.inr (Or.inl hmem)
  · rw [fill, max_eq_left h]; exact hL

end VaughtConjecture.Knight.RightFilledGap
