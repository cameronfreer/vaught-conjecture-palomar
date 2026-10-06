/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyDonorFibre

/-! # Both all-cap gate-free fibres and independent bottom supply

All current grades, empty roots, bottom and literal top are allowed. Bottom
supply starts from a constructed zero source, not positive-cap transport.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly.Family

open Transform Value ExtOrd AmalgamationPlan CappedDonor

noncomputable section

variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

/-- Private-prescribed repair on the complete inventory at every permitted cap. -/
theorem private_lift {j : ℕ} {S : State P C} (hS : F.Admissible j S)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (v d) γ = min (S.lowerC j d) γ) :
    ∃ S', F.Admissible j S' ∧ S'.lowerC j = v ∧ S.CapEq γ S' ∧ S.FutureEq j S' := by
  by_cases hj : K ≤ j
  · exact F.private_active hj hS hv hγ hag
  obtain ⟨u, hQ, hucap⟩ := hS.toSource.install_private F hv hγ hag
  refine ⟨S.replace u v (min S.b γ), ⟨hQ, ?_, fun h => (hj h).elim⟩,
    S.replace_lowerC _ _ _, S.replace_caps hucap hag (clipped_cutoff_cap _ _),
    S.replace_future _ _ _⟩
  exact selfVis_min hS.cutoff (hγ.mono
    (le_min (min_le_left _ _) ((min_le_right _ _).trans F.gap.K_le)))

/-- Donor-prescribed repair; no exchange-symmetry of LOW is used. -/
theorem donor_lift {j : ℕ} {S : State P C} (hS : F.Admissible j S)
    {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (u d) γ = min (S.lowerP j d) γ) :
    ∃ S', F.Admissible j S' ∧ S'.lowerP j = u ∧ S.CapEq γ S' ∧ S.FutureEq j S' := by
  by_cases hj : K ≤ j
  · exact F.donor_active hj hS hu hγ hag
  obtain ⟨v, hQ, hvcap⟩ := hS.toSource.install_donor F hu hγ hag
  refine ⟨S.replace u v (min S.b γ), ⟨hQ, ?_, fun h => (hj h).elim⟩,
    S.replace_lowerP _ _ _, S.replace_caps hag hvcap (clipped_cutoff_cap _ _),
    S.replace_future _ _ _⟩
  exact selfVis_min hS.cutoff (hγ.mono
    (le_min (min_le_left _ _) ((min_le_right _ _).trans F.gap.K_le)))

def zero : State P C := ⟨fun _ => ⊥, fun _ => ⊥, ⊥⟩

theorem zero_admissible (j : ℕ) : F.Admissible j (zero : State P C) where
  lawfulP := RespectsSemanticsBelow.bot _ _
  lawfulC := RespectsSemanticsBelow.bot _ _
  shared _ := rfl
  futureP _ _ := selfVis_bot _
  futureC _ _ := selfVis_bot _
  cutoff := selfVis_bot _
  low _ h := (not_lt_bot h).elim

/-- Independent private section supply, including literal-top prescriptions.
The opposite old face is extended at bottom using its own bountifulness. -/
theorem private_bottom_supply {j : ℕ} {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) :
    ∃ S : State P C, F.Admissible j S ∧ S.lowerC j = v ∧ S.b = ⊥ ∧
      (zero : State P C).FutureEq j S := by
  obtain ⟨u, hQ, -⟩ := (F.zero_admissible j).toSource.install_private F hv
    (selfVis_bot _) (fun _ => by simp only [min_bot_right])
  refine ⟨(zero : State P C).replace u v ⊥, ⟨?_, selfVis_bot _, ?_⟩,
    State.replace_lowerC _ _ _ _, rfl, State.replace_future _ _ _ _⟩
  · exact hQ
  · intro _ hm
    exact (not_lt_bot hm).elim

/-- Independent donor section supply with the free cutoff switched off. -/
theorem donor_bottom_supply {j : ℕ} {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) :
    ∃ S : State P C, F.Admissible j S ∧ S.lowerP j = u ∧ S.b = ⊥ ∧
      (zero : State P C).FutureEq j S := by
  obtain ⟨v, hQ, -⟩ := (F.zero_admissible j).toSource.install_donor F hu
    (selfVis_bot _) (fun _ => by simp only [min_bot_right])
  refine ⟨(zero : State P C).replace u v ⊥, ⟨?_, selfVis_bot _, ?_⟩,
    State.replace_lowerP _ _ _ _, rfl, State.replace_future _ _ _ _⟩
  · exact hQ
  · intro _ hm
    exact (not_lt_bot hm).elim

/-- At top cap the complete-field receipt is literal state equality. -/
theorem state_eq_of_top_caps {S S' : State P C} (h : S.CapEq ⊤ S') : S' = S := by
  obtain ⟨u, v, b⟩ := S
  obtain ⟨u', v', b'⟩ := S'
  obtain ⟨hu, hv, hb⟩ := h
  have hu' : u' = u := funext (fun d => by simpa only [min_top_right] using hu d)
  have hv' : v' = v := funext (fun d => by simpa only [min_top_right] using hv d)
  have hb' : b' = b := by simpa only [min_top_right] using hb
  cases hu'; cases hv'; cases hb'; rfl

end
end VaughtConjecture.Knight.LowOnly.Family
