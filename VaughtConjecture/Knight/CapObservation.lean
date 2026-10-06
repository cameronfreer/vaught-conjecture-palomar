/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Value

/-! # Finite-cut observations

Capping at an ordinal and strict truncation record exactly the same information:
the literal value below the cutoff, and one common value at or above it. Their
kernels coincide (`min_eq_min_iff_truncExt_eq`). Observing a lower cutoff commutes
with higher truncation, so capped agreement is both preserved and reflected by
stage reduction.

These are scalar order identities, including cutoff zero. No visibility, limit
stage or lawfulness premise is used. In particular, this file does **not** assert
that a section capped at an arbitrary cutoff remains lawful.
-/

@[expose] public section

namespace VaughtConjecture.Knight.Value
open ExtOrd

/-- Truncation does not change an observation at or below its cutoff. -/
theorem min_truncExt_of_le {α : Ordinal.{0}} {γ : ExtOrd}
    (hγ : γ ≤ ofOrd α) (x : ExtOrd) :
    min (truncExt α x) γ = min x γ := by
  rcases lt_or_ge x (ofOrd α) with hx | hx
  · rw [truncExt_id_of_lt hx]
  · rw [truncExt_eq_top_of_ge hx, min_eq_right le_top, min_eq_right (hγ.trans hx)]

/-- Capping and strict truncation have the same equality kernel. -/
theorem min_eq_min_iff_truncExt_eq {α : Ordinal.{0}} {x y : ExtOrd} :
    min x (ofOrd α) = min y (ofOrd α) ↔ truncExt α x = truncExt α y := by
  constructor
  · intro h
    have h' := congrArg (truncExt α) h
    simpa only [truncExt_min, truncExt_ofOrd_of_le le_rfl, min_eq_left le_top] using h'
  · intro h
    simpa only [min_truncExt_of_le le_rfl] using congrArg (fun z => min z (ofOrd α)) h

/-- A higher stage truncation preserves and reflects every lower cap equality. -/
theorem min_truncExt_eq_iff {α : Ordinal.{0}} {γ x y : ExtOrd}
    (hγ : γ ≤ ofOrd α) :
    min (truncExt α x) γ = min (truncExt α y) γ ↔ min x γ = min y γ := by
  rw [min_truncExt_of_le hγ, min_truncExt_of_le hγ]

/-- An observation descends to every lower ordinal cutoff. -/
theorem truncExt_eq_of_le {α β : Ordinal.{0}} {x y : ExtOrd}
    (hαβ : α ≤ β) (h : truncExt β x = truncExt β y) :
    truncExt α x = truncExt α y := by
  simpa only [truncExt_compose hαβ] using congrArg (truncExt α) h

end VaughtConjecture.Knight.Value
