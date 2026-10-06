/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyRelease

/-! # Complete-field receipts for LOW-only repairs

Local repair changes present coordinates only. Future coordinates are retained literally,
and must still participate in LOW's non-top maximum. The activation barrier below quantifies
over the complete finite field vector, with no grade restriction on its non-top set.
These are receipt lemmas, not the two coface repair fibres themselves.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd AmalgamationPlan CappedDonor

noncomputable section

variable {n : ℕ} {P : SemScheme n} {j : ℕ}

open Classical in
/-- Install the constructed present section, preserving all still-future fields. -/
def completeAt (a : Cell P.scheme → ExtOrd)
    (u : P.scheme.below (effC n j) → ExtOrd) (d : Cell P.scheme) : ExtOrd :=
  if hd : GradedLe (P.scheme.cell d) (effC n j) then u ⟨d, hd⟩ else a d

theorem completeAt_present (a : Cell P.scheme → ExtOrd)
    (u : P.scheme.below (effC n j) → ExtOrd) (d : P.scheme.below (effC n j)) :
    completeAt a u d.1 = u d := by
  unfold completeAt
  rw [dite_eq_left d.2]
  rfl

theorem completeAt_future (a : Cell P.scheme → ExtOrd)
    (u : P.scheme.below (effC n j) → ExtOrd) (d : Cell P.scheme)
    (hd : j < P.scheme.grade d) : completeAt a u d = a d := by
  unfold completeAt
  rw [dite_eq_right (fun h => (not_le.mpr hd) (h.2.trans (min_le_left _ _)))]

theorem completeAt_respects (a : Cell P.scheme → ExtOrd)
    {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) :
    RespectsSemanticsBelow P.rows (effC n j) (fun d => completeAt a u d.1) := by
  have h : (fun d : P.scheme.below (effC n j) => completeAt a u d.1) = u :=
    funext (completeAt_present a u)
  rw [h]; exact hu

/-- Every field, not just present fields, retains its original comparison-cap reading. -/
theorem completeAt_cap (a : Cell P.scheme → ExtOrd)
    {u : P.scheme.below (effC n j) → ExtOrd} {γ : ExtOrd}
    (hcap : ∀ d, min (u d) γ = min (a d.1) γ) (d : Cell P.scheme) :
    min (completeAt a u d) γ = min (a d) γ := by
  unfold completeAt
  split_ifs with hd
  · exact hcap ⟨d, hd⟩
  · rfl

section Barrier

variable {F : Type*} [Fintype F]

open Classical in
/-- The maximum includes every designated non-top field, irrespective of birth grade. -/
def nonTopMax (T : F → Prop) (a : F → ExtOrd) : ExtOrd :=
  (Finset.univ.filter fun d => ¬ T d).sup a

theorem le_nonTopMax {T : F → Prop} (a : F → ExtOrd) {d : F} (hd : ¬ T d) :
    a d ≤ nonTopMax T a := by
  classical
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)

/-- Activation after clipping the cutoff pins all old non-top fields literally.
There is no exception for future fields or fields above the LOW threshold. -/
theorem clipped_activation {T : F → Prop} {a a' : F → ExtOrd} {b γ : ExtOrd}
    (hcap : ∀ d, min (a' d) γ = min (a d) γ)
    (hactive : nonTopMax T a' < min b γ) :
    (∀ d, ¬ T d → a' d = a d) ∧ nonTopMax T a' = nonTopMax T a ∧
      nonTopMax T a < b := by
  classical
  have hfix : ∀ d, ¬ T d → a' d = a d := by
    intro d hd
    exact (eq_of_capAgree_of_lt (hcap d)
      (((le_nonTopMax a' hd).trans_lt hactive).trans_le (min_le_right _ _))).symm
  have hM : nonTopMax T a' = nonTopMax T a := by
    apply Finset.sup_congr rfl
    intro d hd
    exact hfix d (Finset.mem_filter.mp hd).2
  exact ⟨hfix, hM, hM ▸ hactive.trans_le (min_le_left _ _)⟩

theorem clipped_cutoff_cap (b γ : ExtOrd) : min (min b γ) γ = min b γ := by
  rw [min_assoc, min_self]

/-- Turning gate and cutoff off is always compatible with the bottom cap. It does
not assert section supply, which still requires the original scheme's extension. -/
theorem off_bottom_cap (g b : ExtOrd) :
    min (⊥ : ExtOrd) ⊥ = min g ⊥ ∧ min (⊥ : ExtOrd) ⊥ = min b ⊥ := by
  simp

omit [Fintype F] in
/-- At top comparison cap, cap agreement is already literal agreement. -/
theorem top_cap_literal {a a' : F → ExtOrd}
    (hcap : ∀ d, min (a' d) ⊤ = min (a d) ⊤) : a' = a := by
  funext d
  simpa only [min_top_right] using hcap d

end Barrier
end

end VaughtConjecture.Knight.LowOnly
