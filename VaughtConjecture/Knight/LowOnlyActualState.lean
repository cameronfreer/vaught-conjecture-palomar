/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowSeparatorPaired
public import VaughtConjecture.Knight.FiniteCoverReceivingCore
public import VaughtConjecture.Knight.CappedDonorLowHighNormalization

/-! # An active LOW state below a limit stage

Two lawful, literally shared original sections, with the donor equal to the
family's designated labelling, have a stage-bounded active state. The cutoff
is constructed above the rounded non-top donor maximum and below the stage.
Admission is proved at every grade, not transported upward from a catalogue.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyActualState
open Transform Value ExtOrd CappedDonor LowOnly LowSeparator
noncomputable section

/-- A proper visible value strictly above any value below a limit stage. -/
theorem exists_visible_above {α : LimitStage} (K : ℕ) {x : ExtOrd}
    (hx : x < ofOrd α.1) :
    ∃ b : ExtOrd, SelfVis K b ∧ x < b ∧ b < ofOrd α.1 := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · refine ⟨ofOrd ((K + 1 : ℕ) : Ordinal.{0}), ?_, bot_lt_ofOrd _, ?_⟩
    · simpa only [zero_add] using
        (FiniteCoverReceiving.selfVis_ofOrd_add_nat 0 (K + 1)).mono (Nat.le_succ K)
    · exact ofOrd_lt_ofOrd.mpr (by
        simpa only [zero_add] using FiniteCoverReceiving.add_nat_lt_limitStage (α := α) α.2.pos (K
          + 1))
  · exact (not_top_lt hx).elim
  · refine ⟨ofOrd (ν + ((K + 1 : ℕ) : Ordinal.{0})),
      (FiniteCoverReceiving.selfVis_ofOrd_add_nat ν (K + 1)).mono (Nat.le_succ K), ?_, ?_⟩
    · exact ofOrd_lt_ofOrd.mpr (lt_add_of_pos_right ν (by positivity))
    · exact ofOrd_lt_ofOrd.mpr (FiniteCoverReceiving.add_nat_lt_limitStage (ofOrd_lt_ofOrd.mp hx) _)

variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

/-- The cutoff does not contribute to the designated non-top donor maximum. -/
theorem cutoffCut_actual (v : Cell C.scheme → ExtOrd) (b : ExtOrd) :
    cutoffCut K (donorField F) (State.profile (⟨F.p, v, b⟩ : State P C)) =
      cutoffCut K (donorField F) (State.profile (⟨F.p, v, ⊥⟩ : State P C)) := by
  unfold cutoffCut
  congr 1
  apply donorMax_congr
  intro d hd
  rcases d with d | d | d
  · rfl
  · exact hd.elim
  · exact hd.elim

/-- Construct the active state, with all original proper fields and the cutoff
below the stage. This uses only the two original lawful labellings. -/
theorem exists_active {α : LimitStage} (v : Cell C.scheme → ExtOrd)
    (hv : RespectsSemantics C.rows v) (hshared : F.root.Shared F.p v)
    (hpbound : ∀ d, F.p d ≠ ⊤ → F.p d < ofOrd α.1)
    (hvbound : ∀ d, v d ≠ ⊤ → v d < ofOrd α.1) :
    ∃ b : ExtOrd,
      b < ofOrd α.1 ∧
      (∀ j, F.Admissible j (⟨F.p, v, b⟩ : State P C)) ∧
      cutoffCut K (donorField F) (State.profile (⟨F.p, v, b⟩ : State P C)) < b ∧
      ∀ f, (State.profile (⟨F.p, v, b⟩ : State P C)) f ≠ ⊤ →
        (State.profile (⟨F.p, v, b⟩ : State P C)) f < ofOrd α.1 := by
  classical
  let S₀ : State P C := ⟨F.p, v, ⊥⟩
  have hm : donorMax (donorField F) S₀.profile < ofOrd α.1 := by
    apply (Finset.sup_lt_iff (bot_lt_ofOrd _)).mpr
    intro f hf
    have hd := (Finset.mem_filter.mp hf).2
    rcases f with d | d | d
    · exact hpbound d hd
    · exact hd.elim
    · exact hd.elim
  have hcut : cutoffCut K (donorField F) S₀.profile < ofOrd α.1 :=
    evr_lt_of_lt_limit (limitPart_eq_self_of_isNonSuccessor (Or.inr α.2)) hm K K
  obtain ⟨b, hbvis, hactive, hb⟩ := exists_visible_above K hcut
  refine ⟨b, hb, ?_, (cutoffCut_actual F v b).trans_lt hactive, ?_⟩
  · intro j
    exact
      { lawfulP := F.p_lawful.toBelow _
        lawfulC := hv.toBelow _
        shared := hshared
        futureP := fun d _ => SelfVis.mono (show SelfVis (P.scheme.grade d) (F.p d)
          from (F.p_lawful.orderly d).symm) (P.scheme.grade_pos d)
        futureC := fun d _ => SelfVis.mono (show SelfVis (C.scheme.grade d) (v d)
          from (hv.orderly d).symm) (C.scheme.grade_pos d)
        cutoff := hbvis.mono (min_le_right _ _)
        low := fun _ _ d hd => le_top.trans_eq hd.symm }
  · intro f hf
    rcases f with d | d | d
    · exact hpbound d hf
    · exact hvbound d hf
    · exact hb

end
end VaughtConjecture.Knight.LowOnlyActualState
