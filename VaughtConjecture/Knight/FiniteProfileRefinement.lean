/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteProfileControllers
public import VaughtConjecture.Knight.SlotPatternRefinement

/-! # Preservation of whole-profile lawfulness under source refinement

For any finite profile family, its whole joint labellings are closed under
visible bottom-preserving changes of order and under separated two-region
refinement. The latter selects a controller maximal for the upper prescription;
separation makes it active for the lower prescription too. All controller
occurrences participate. No transformation is composed and no new profile
membership hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.FiniteProfileRefinement

open Transform Value ExtOrd SlotControllerFamily FiniteProfileControllers
open SlotPatternRefinement (mix)

variable {X Q : Type*} [Finite X] [Finite Q] [Nonempty Q]
variable {H : ℕ} {profile : Q → X → ℕ}

omit [Nonempty Q] in
theorem joint_of_order (hbound : ∀ q d, profile q d ≤ H) (q : Q)
    (r : X ⊕ Q → ExtOrd) (hv : ∀ d, SelfVis 1 (r d))
    (hz : ∀ d, index H profile q d = 0 → r d = ⊥)
    (hm : ∀ d e, index H profile q d ≤ index H profile q e → r d ≤ r e) :
    Joint H profile r := by
  have ht : TransformsTo (fun _ : X ⊕ Q => 1) (row H profile q) r :=
    transforms_of_table _ _ hv hz hm
  obtain ⟨f, hf, h0, hfv, he⟩ := table_of_transform ht
  have h := label_joint hbound q f hf h0 hfv
  rwa [show (fun d => f (index H profile q d)) = r from funext he] at h

/-- Order transport is rebuilt from one actual serving row, not from a
composition of the ambient's faithful witness with an arbitrary map. -/
theorem order_image (hbound : ∀ q d, profile q d ≤ H)
    {p r : X ⊕ Q → ExtOrd} (hp : Joint H profile p)
    (hv : ∀ d, SelfVis 1 (r d)) (hz : ∀ d, p d = ⊥ → r d = ⊥)
    (hm : ∀ d e, p d ≤ p e → r d ≤ r e) : Joint H profile r := by
  obtain ⟨q, f, hf, h0, _, he⟩ := hp.exists_shape
  apply joint_of_order hbound q r hv
  · intro d hd
    apply hz d
    rw [he, hd, h0]
  · intro d e hde
    apply hm d e
    rw [he, he]
    exact hf hde

omit [Finite X] [Finite Q] [Nonempty Q] in
theorem capped_order {p : X ⊕ Q → ℕ}
    (hp : Joint H profile (fun d => value (p d))) (q : Q) (d e : X ⊕ Q)
    (hde : index H profile q d ≤ index H profile q e) :
    min (p d) (p (.inr q)) ≤ min (p e) (p (.inr q)) := by
  obtain ⟨g, σ, _, _, _, hm, _, he⟩ := hp.2.1 q
  dsimp only at he
  have h : min (value (p d)) (value (p (.inr q))) ≤
      min (value (p e)) (value (p (.inr q))) := by
    rw [he d, he e]
    exact min_le_min_right _ (hm (value_mono hde))
  rw [← value_mono.map_min, ← value_mono.map_min] at h
  exact (value_le_iff _ _).mp h

omit [Finite X] [Finite Q] [Nonempty Q] in
theorem capped_zero {p : X ⊕ Q → ℕ}
    (hp : Joint H profile (fun d => value (p d))) (q : Q) (d : X ⊕ Q)
    (hd : index H profile q d = 0) : min (p d) (p (.inr q)) = 0 := by
  obtain ⟨g, σ, _, _, h0, _, _, he⟩ := hp.2.1 q
  have h := he d
  change min (value (p d)) (value (p (.inr q))) =
    min (σ (value (index H profile q d))) (g 1) at h
  rw [hd, show value 0 = ⊥ from rfl, h0, min_bot_left,
    ← value_mono.map_min] at h
  exact Nat.eq_zero_of_le_zero ((value_le_iff _ 0).mp h.le)

/-- Whole joint profiles are closed under the same two-region refinement
used to construct ambient-active controllers. This is uniform in the finite
inventory and profile family, including all previously added controllers. -/
theorem joint_mix (hbound : ∀ q d, profile q d ≤ H)
    {q b : X ⊕ Q → ℕ} {a : ℕ} (ha : 0 < a)
    (hq : Joint H profile (fun d => value (q d)))
    (hb : Joint H profile (fun d => value (b d)))
    (hs : ∀ d e, q d < a → a ≤ q e → b d < b e) :
    Joint H profile (fun d => value (mix q b a d)) := by
  by_cases hreach : ∃ d, a ≤ q d
  swap
  · have he : mix q b a = q := by
      funext d
      exact ite_eq_left (lt_of_not_ge (fun h => hreach ⟨d, h⟩))
    rwa [he]
  obtain ⟨c, hc⟩ := Finite.exists_max (fun c : Q => b (.inr c))
  have hmax (d : X ⊕ Q) : b d ≤ b (.inr c) := by
    obtain ⟨e, he⟩ := hb.2.2 d
    exact ((value_le_iff _ _).mp he).trans (hc e)
  have hactive : a ≤ q (.inr c) := by
    by_contra hn
    obtain ⟨d, hd⟩ := hreach
    exact (not_lt_of_ge (hmax d)) (hs (.inr c) d (lt_of_not_ge hn) hd)
  apply joint_of_order hbound c _ (fun _ => value_visible _)
  · intro d hd
    have hz := capped_zero hq c d hd
    have hqd : q d = 0 := by omega
    simp only [mix, hqd, ha, ↓reduceIte]
    rfl
  · intro d e hde
    apply value_mono
    have hqde := capped_order hq c d e hde
    have hbde : b d ≤ b e := by
      have h := capped_order hb c d e hde
      rwa [min_eq_left (hmax d), min_eq_left (hmax e)] at h
    unfold mix
    split_ifs <;> omega

end VaughtConjecture.Knight.FiniteProfileRefinement
