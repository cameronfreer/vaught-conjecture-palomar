/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TwoPointSlotPatterns

/-! # Refining the proper boundary across a source cut

Below the cut retain the ambient source order, including distinctions erased
by its decoder. Above it use the prescribed order. The two slot cones are
closed under this operation when lower prescribed values precede upper ones.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.SlotPatternRefinement

open Transform Value ExtOrd SlotControllerFamily ThreePointSlotBoundary TwoPointSlotPatterns

def mix {X : Type*} (q b : X → ℕ) (a : ℕ) (d : X) : ℕ :=
  if q d < a then q d else a + b d

set_option maxHeartbeats 800000 in
-- Four slot cones and the four threshold decisions give a finite linear-order split.
theorem pattern_mix (q b : Fin 5 → ℕ) (a : ℕ) (hq : Pattern q) (hb : Pattern b)
    (hs : ∀ d e, q d < a → a ≤ q e → b d < b e) : Pattern (mix q b a) := by
  have h01 := hs 0 1
  have h02 := hs 0 2
  have h03 := hs 0 3
  have h10 := hs 1 0
  have h12 := hs 1 2
  have h13 := hs 1 3
  have h20 := hs 2 0
  have h21 := hs 2 1
  have h23 := hs 2 3
  have h30 := hs 3 0
  have h31 := hs 3 1
  have h32 := hs 3 2
  rcases hq with ⟨hq1, hq2, hq3⟩ | ⟨hq1, hq2, hq3⟩ <;>
    rcases hb with ⟨hb1, hb2, hb3⟩ | ⟨hb1, hb2, hb3⟩ <;>
    unfold Pattern mix <;> split_ifs <;> omega

theorem pattern_value (q : Fin 5 → ℕ) : Pattern (fun d => value (q d)) ↔ Pattern q := by
  have eqv (i j : ℕ) : value i = value j ↔ i = j := by
    rw [le_antisymm_iff, value_le_iff, value_le_iff, le_antisymm_iff]
  simp only [Pattern, eqv, value_le_iff]

theorem face_mix {q b : Fin 5 → ℕ} {a : ℕ} (ha : 0 < a)
    (hq : RespectsSemantics TwoPointSlots.rows (fun d => value (q d)))
    (hb : RespectsSemantics TwoPointSlots.rows (fun d => value (b d)))
    (hs : ∀ d e, q d < a → a ≤ q e → b d < b e) :
    RespectsSemantics TwoPointSlots.rows (fun d => value (mix q b a d)) := by
  apply respects_of_pattern (fun d => value_visible _)
  · have hz := (respects_iff _).mp hq |>.2.1
    have he : q 4 = 0 := Nat.eq_zero_of_le_zero ((value_le_iff _ 0).mp (le_of_eq hz))
    simp only [mix, he, ha, ↓reduceIte]
    rfl
  · apply (pattern_value _).mpr
    exact pattern_mix q b a ((pattern_value _).mp (pattern_of_respects hq))
      ((pattern_value _).mp (pattern_of_respects hb)) hs

theorem boundary_mix {q b : Fin 9 → ℕ} {a : ℕ} (ha : 0 < a)
    (hq : Lawful (fun d => value (q d))) (hb : Lawful (fun d => value (b d)))
    (hs : ∀ d e, q d < a → a ≤ q e → b d < b e) :
    Lawful (fun d => value (mix q b a d)) := by
  constructor
  · exact face_mix ha hq.1 hb.1 (fun d e => hs (left d) (left e))
  · exact face_mix ha hq.2 hb.2 (fun d e => hs (right d) (right e))

end VaughtConjecture.Knight.SlotPatternRefinement
