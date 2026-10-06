/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ThreeLevelFragment

/-! # The remaining localities of the three-level fragment

`Knight/ThreeLevelFragment.lean` proves the cross-level localities `3 → 1`, `3 → 2` and the
same-level locality at level three.  A finite scheme assembled from the fragment's cells needs
the rest: the same-level locality at level one (`Row1.same1`), the cross-level locality `2 → 1`
(`Core2.cross21`, the grade-one decoder as shifter, the level-three proof verbatim), and the
same-level locality at level two (`Core2.same2`), together with the self-visibility and the cap
attainment of the level-two directed values (`Core2.rho_selfVis`, `Core2.rho_wit`, `Core2.rho_le`).
Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

section Fragment

variable {P : Type*} [Fintype P] [DecidableEq P] {gradeP : P → ℕ} {T : ℕ}

omit [Fintype P] [DecidableEq P] in
theorem Low1.grade_le_one (d : Low1 gradeP T) : Low1.grade d ≤ 1 := by
  rcases d with d | d
  · exact d.2
  · exact le_rfl

omit [Fintype P] [DecidableEq P] in
theorem Low2.grade_le_two (d : Low2 gradeP T) : Low2.grade d ≤ 2 := by
  rcases d with d | d | d
  · exact d.2
  · exact by simp [Low2.grade]
  · exact le_rfl

/-- **Same-level locality at level one**: identity shifter, the meet as suppressor. -/
theorem Row1.same1 (H H' : Row1 gradeP T) :
    TransformsTo Low1.grade H.row (fun d => min (H'.row d) (meet₁ H' H)) := by
  refine ⟨fun k => if k ≤ 1 then meet₁ H' H else ⊥, id, ?_, ?_, rfl, fun _ _ h => h,
    fun _ _ _ _ _ => rfl, ?_⟩
  · intro a b hab
    dsimp only
    split_ifs with h1 h2 <;> first | exact le_rfl | exact bot_le | omega
  · intro n
    dsimp only
    split_ifs with h
    · exact ((meet₁_selfVis H' H).mono h).symm
    · simp
  · intro d
    have hag := meet₁_agree H' H
    rcases d with c | H''
    · change min (H'.G c.1) (meet₁ H' H) = min (id (H.G c.1)) (if gradeP c.1 ≤ 1 then _ else ⊥)
      rw [ite_eq_left c.2]; exact hag c.1 c.2
    · change min (meet₁ H' H'') (meet₁ H' H) = min (id (meet₁ H H'')) (if (1 : ℕ) ≤ 1 then _ else ⊥)
      rw [ite_eq_left le_rfl]
      simp only [id]
      rw [meet₁_ultra H' H H'', meet₁_comm H H'']

theorem Core2.rho_selfVis (st : Setting gradeP T) (s : Core2 (gradeP := gradeP) (T := T))
    (H : Row1 gradeP T) : SelfVis 1 (s.rho st H) :=
  shift_selfVis_of_selfVis (s.γ_vis.mono (by omega)) (meet₁_selfVis _ H)

/-- The directed value of a level-two cell at its own witness is its cap. -/
theorem Core2.rho_wit (st : Setting gradeP T) (s : Core2 (gradeP := gradeP) (T := T)) :
    s.rho st (s.wit st) = s.γ :=
  dirVal1_witness st.hT s.F (s.orderly st) s.γ

theorem Core2.rho_le (st : Setting gradeP T) (s : Core2 (gradeP := gradeP) (T := T))
    (H : Row1 gradeP T) : s.rho st H ≤ s.γ :=
  dirVal1_le st.hT s.F (s.orderly st) (s.γ_vis.mono (by omega)) s.F_le H

/-- The level-two row restricted to the level-one lower set. -/
noncomputable def Core2.rowOn1 (st : Setting gradeP T) (s : Core2 (gradeP := gradeP) (T := T)) :
    Low1 gradeP T → ExtOrd := fun d =>
  match d with
  | Sum.inl c => s.F c.1
  | Sum.inr H => s.rho st H

/-- **Cross-level locality `2 → 1`**: the level-one row transforms to the level-two row capped at
the directed value (the grade-one decoder as shifter; the level-three proof verbatim). -/
theorem Core2.cross21 (st : Setting gradeP T) (s : Core2 (gradeP := gradeP) (T := T))
    (H : Row1 gradeP T) :
    TransformsTo Low1.grade H.row (fun d => min (s.rowOn1 st d) (s.rho st H)) := by
  have hγ : SelfVis 1 s.γ := s.γ_vis.mono (by omega)
  have hS : ∀ v ∈ valuesAt gradeP s.F 1, ofOrd v ≤ s.γ := fun v hv => by
    obtain ⟨c, -, hc⟩ := (mem_valuesAt gradeP).mp hv
    rw [← hc]; exact s.F_le c
  have h := transformsTo_of_shift 1 (valuesAt gradeP s.F 1) s.γ Low1.grade hγ hS H.row
    (s.rho_selfVis st H)
  have e : (fun d => min (shift 1 (valuesAt gradeP s.F 1) s.γ (H.row d))
      (if Low1.grade d ≤ 1 then s.rho st H else ⊥)) =
      fun d => min (s.rowOn1 st d) (s.rho st H) := by
    funext d
    rcases d with c | H'
    · change min (dec1 gradeP s.F s.γ (H.G c.1)) (if gradeP c.1 ≤ 1 then s.rho st H else ⊥) =
        min (s.F c.1) (s.rho st H)
      rw [ite_eq_left c.2]
      exact clause4_1 st.hT s.F (s.orderly st) hγ s.F_le H c.2
    · change min (dec1 gradeP s.F s.γ (meet₁ H H')) (if (1 : ℕ) ≤ 1 then s.rho st H else ⊥) =
        min (s.rho st H') (s.rho st H)
      rw [ite_eq_left (le_refl 1)]
      have hmono := dec1_mono gradeP s.F hγ s.F_le
      change min (dec1 gradeP s.F s.γ (meet₁ H H'))
          (dec1 gradeP s.F s.γ (meet₁ (witness1 st.hT s.F (s.orderly st)) H)) =
        min (dec1 gradeP s.F s.γ (meet₁ (witness1 st.hT s.F (s.orderly st)) H'))
          (dec1 gradeP s.F s.γ (meet₁ (witness1 st.hT s.F (s.orderly st)) H))
      rw [← Monotone.map_min hmono, ← Monotone.map_min hmono, meet₁_ultra]
  rw [e] at h
  exact h

/-- **Same-level locality at level two**: identity shifter, the level-two meet as suppressor. -/
theorem Core2.same2 (st : Setting gradeP T) (s s' : Core2 (gradeP := gradeP) (T := T)) :
    TransformsTo Low2.grade (s.row st) (fun d => min (s'.row st d) (meet₂ st s' s)) := by
  refine ⟨fun k => if k ≤ 2 then meet₂ st s' s else ⊥, id, ?_, ?_, rfl, fun _ _ h => h,
    fun _ _ _ _ _ => rfl, ?_⟩
  · intro a b hab
    dsimp only
    split_ifs with h1 h2 <;> first | exact le_rfl | exact bot_le | omega
  · intro n
    dsimp only
    split_ifs with h
    · exact ((meet₂_selfVis st s' s).mono h).symm
    · simp
  · intro d
    have hag := meet₂_agree st s' s
    rcases d with c | H | s''
    · change min (s'.F c.1) (meet₂ st s' s) =
        min (id (s.F c.1)) (if gradeP c.1 ≤ 2 then _ else ⊥)
      rw [ite_eq_left c.2]; exact hag.1 c.1 c.2
    · change min (s'.rho st H) (meet₂ st s' s) =
        min (id (s.rho st H)) (if (1 : ℕ) ≤ 2 then _ else ⊥)
      rw [ite_eq_left (by omega)]; exact hag.2 H
    · change min (meet₂ st s' s'') (meet₂ st s' s) =
        min (id (meet₂ st s s'')) (if (2 : ℕ) ≤ 2 then _ else ⊥)
      rw [ite_eq_left le_rfl]
      simp only [id]
      rw [meet₂_ultra st s' s s'', meet₂_comm st s s'']

end Fragment

end VaughtConjecture.Knight
