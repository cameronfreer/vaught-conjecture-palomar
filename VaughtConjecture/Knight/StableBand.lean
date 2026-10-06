/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.ENat.Lattice
public import VaughtConjecture.Knight.ProvisionalOffset

/-! # Stable values as suprema in the completed band

Fix an actual labelled cover `x` and a source-top cell `Ξ`.  Along the rooted covers of `x` the
transported provisional value is `α + j` with a monotone natural offset `j`
(`RootedCover.offset`).  This module identifies the stable value with the supremum of those
offsets, taken in the **completed natural-number band** `ℕ∞` and then decoded:

  `stableValue x Ξ = bandValue α (⨆ y, offset Ξ y)`   (`stableValue_eq_bandValue_iSup`),

where `bandValue α` sends `k : ℕ` to `α + k` and `⊤` to `⊤`.  The definition of `stableValue`
is unchanged; the identification is a consequence of the offset dichotomy
(`RootedCover.stableValue_dichotomy`) and monotonicity.  A finite supremum is the stable offset
(`iSup_offset_eq_natCast_iff`), and an infinite supremum is stable top
(`iSup_offset_eq_top_iff`).

The supremum is taken in `ℕ∞`, never in the ordinal label space: there `⨆ n, α + n = α + ω`,
which is a proper label, not `⊤`.  Non-top source cells keep their literal labels
(`stableValue_of_ne_top`) and have no offset. -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd StageType Filter

universe w

namespace ExtOrd

/-- **Decoding of the completed band above `β`**: a finite offset `k` is the label `β + k`, and
the completion point `⊤` is the label `⊤`. -/
noncomputable def bandValue (β : Ordinal.{0}) (r : ℕ∞) : ExtOrd :=
  ENat.recTopCoe ⊤ (fun k : ℕ => ofOrd (β + k)) r

@[simp] theorem bandValue_natCast (β : Ordinal.{0}) (k : ℕ) :
    bandValue β k = ofOrd (β + k) :=
  ENat.recTopCoe_natCast _ _ k

@[simp] theorem bandValue_top (β : Ordinal.{0}) : bandValue β ⊤ = ⊤ :=
  ENat.recTopCoe_top _ _

/-- Decoding the band loses nothing. -/
theorem bandValue_injective (β : Ordinal.{0}) : Function.Injective (bandValue β) := by
  intro r s h
  induction r using ENat.recTopCoe <;> induction s using ENat.recTopCoe
  · rfl
  · exact absurd h.symm (by simp)
  · exact absurd h (by simp)
  · simp only [bandValue_natCast, ofOrd_inj, add_right_inj, Nat.cast_inj] at h
    rw [h]

end ExtOrd

namespace KnightRealization

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

namespace RootedCover

variable {x : R.LabelledExt} (Xi : Cell x.type.scheme.scheme) (htop : x.type.label Xi = ⊤)
  (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering)

include hcons hcov in
/-- **The stable value of a source top is the decoded supremum of its offsets**, the supremum
taken in the completed band `ℕ∞`.  An eventually constant offset has its plateau as supremum;
an escaping offset has supremum `⊤`. -/
theorem stableValue_eq_bandValue_iSup :
    R.stableValue x.tuple x.type Xi = bandValue α.1 (⨆ y, (offset Xi htop y : ℕ∞)) := by
  have := isDirectedOrder hcons hcov x
  rcases stableValue_dichotomy Xi htop hcons hcov with ⟨k, hk, hval⟩ | ⟨ht, hsv⟩
  · obtain ⟨i, hi⟩ := eventually_atTop.mp hk
    have hsup : (⨆ y, (offset Xi htop y : ℕ∞)) = k := by
      refine le_antisymm (iSup_le fun y => ?_) ?_
      · obtain ⟨z, hyz, hiz⟩ := exists_ge_ge y i
        exact_mod_cast (offset_mono Xi htop hyz).trans (hi z hiz).le
      · exact (hi i le_rfl).symm ▸ le_iSup (fun y => (offset Xi htop y : ℕ∞)) i
    rw [hsup, bandValue_natCast, hval]
  · have hsup : (⨆ y, (offset Xi htop y : ℕ∞)) = ⊤ := by
      refine ENat.eq_top_iff_forall_ge.mpr fun k => ?_
      obtain ⟨y, hy⟩ := (ht.eventually (eventually_ge_atTop k)).exists
      exact (Nat.cast_le.mpr hy).trans (le_iSup (fun y => (offset Xi htop y : ℕ∞)) y)
    rw [hsup, bandValue_top, hsv]

include hcons hcov in
/-- A finite supremum of the offsets is exactly a proper stable value `α + k`. -/
theorem iSup_offset_eq_natCast_iff (k : ℕ) :
    (⨆ y, (offset Xi htop y : ℕ∞)) = k ↔
      R.stableValue x.tuple x.type Xi = ofOrd (α.1 + k) := by
  rw [stableValue_eq_bandValue_iSup Xi htop hcons hcov, ← bandValue_natCast,
    (bandValue_injective _).eq_iff]

include hcons hcov in
/-- An infinite supremum of the offsets is exactly stable top. -/
theorem iSup_offset_eq_top_iff :
    (⨆ y, (offset Xi htop y : ℕ∞)) = ⊤ ↔ R.stableValue x.tuple x.type Xi = ⊤ := by
  rw [stableValue_eq_bandValue_iSup Xi htop hcons hcov, ← bandValue_top α.1,
    (bandValue_injective _).eq_iff]

end RootedCover

end KnightRealization

end VaughtConjecture.Knight
