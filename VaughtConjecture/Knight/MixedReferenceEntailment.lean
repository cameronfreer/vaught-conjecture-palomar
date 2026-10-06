module

public import VaughtConjecture.Knight.FiniteCutEntailment

/-!
# Mixed low values and a protected high reference

On the unchanged repaired domain, retain the proper values and the old lowest cap literally,
while allowing the protected high reference and the fresh high value to vary. The parameters
are `(v₀, κ, κ', κ', η₁, κ, κ')`, where `γ₀ ≤ κ ≤ κ'` and both highs are self-visible at
grade three. The existing sufficiency theorem supplies all transformation witnesses.

The A face is independent of `κ'`. Thus a single mixed context has universal fresh top
readback at any cut below `κ`, but admits different fresh labels. This is a fixed-geometry
theorem about raw respecting labellings, not arbitrary finite-pattern transfer or realization
inside a fixed model. Universal entailment protects the high reference; it is not a consequence
of fixing the low root alone.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.MixedReferenceEntailment

open Transform Value ExtOrd FiniteCutEntailment

private theorem proper_lt_cap : v₀ < γ₀ := by
  unfold v₀ γ₀
  rw [ofOrd_lt_ofOrd]
  exact add_lt_add_right (Nat.cast_lt.mpr (by decide : 1 < 4)) _

private theorem lowCap_lt_cap : η₁ < γ₀ := lt_of_le_of_ne η₁_le_γ₀ η₁_ne_γ₀

/-- Keep the low part of the original display, replacing its two high values separately. -/
noncomputable def retarget (κ κ' a : ExtOrd) : ExtOrd :=
  if a < γ₀ then a else if a = γ₀ then κ else κ'

theorem retarget_low (κ κ' : ExtOrd) {a : ExtOrd} (ha : a < γ₀) :
    retarget κ κ' a = a := by simp only [retarget, ite_eq_left ha]

theorem retarget_cap (κ κ' : ExtOrd) : retarget κ κ' γ₀ = κ := by
  simp [retarget]

theorem retarget_high (κ κ' : ExtOrd) : retarget κ κ' γ₁ = κ' := by
  simp [retarget, not_lt_of_ge γ₀_le_γ₁, ne_of_gt γ₀_lt_γ₁]

/-- Below the old cap the choice of fresh high value has no effect. -/
theorem retarget_independent (κ κ' κ'' : ExtOrd) {a : ExtOrd} (ha : a ≤ γ₀) :
    retarget κ κ' a = retarget κ κ'' a := by
  rcases lt_or_eq_of_le ha with h | rfl
  · rw [retarget_low _ _ h, retarget_low _ _ h]
  · rw [retarget_cap, retarget_cap]

/-- The fixed source table is unchanged: only the respecting display is relabelled. -/
noncomputable def display (κ κ' : ExtOrd) (d : Lower) : ExtOrd :=
  retarget κ κ' (qL d.1)

/-- The family meets the exact seven-parameter legality conditions. -/
theorem legal {κ κ' : ExtOrd} (hκ : γ₀ ≤ κ) (hle : κ ≤ κ')
    (hvκ : SelfVis 3 κ) (hvκ' : SelfVis 3 κ') : Legal₃ v₀ κ κ' κ' η₁ κ κ' := by
  have hnκ : κ ≠ ⊥ := ne_bot_of_gt ((bot_lt_ofOrd _).trans_le hκ)
  refine ⟨?_, η₁_le_γ₀.trans hκ, le_rfl, hle, le_rfl, η₁_vis, hvκ, hvκ',
    ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨v₀_vis, v₀_le_γ₀.trans hκ, hle, fun h => (hnκ h).elim,
      hvκ.mono (by decide), hvκ'.mono (by decide), hvκ'.mono (by decide), le_rfl,
      by rw [min_eq_left hle]; exact hvκ.mono (by decide)⟩
  · rwa [min_eq_left hle]
  · rw [min_eq_left (v₀_le_γ₀.trans (hκ.trans hle))]
    exact v₀_orbit_three.symm
  · rw [min_eq_left (v₀_le_γ₀.trans (hκ.trans hle))]
    exact v₀_orbit_three_one
  · exact fun h => (ofOrd_ne_bot _ h).elim
  · rw [min_eq_left hle]
    exact fun h => (hnκ h).elim

private theorem original_shape : Shape₃ (fun d : Lower => qL d.1)
    v₀ γ₀ γ₁ γ₁ η₁ γ₀ γ₁ := by
  have hnew := H₀new_eq_U_H_of_respects ((hq₂_of qL_respectsR).mono h₁₂)
  have hsnew := s₀new_eq_U_S_of_respects (hq₂_of qL_respectsR)
  change qL H₀new = qL U_H at hnew
  change qL s₀new = qL U_S at hsnew
  refine ⟨qL_H₀old, hnew.trans qL_U_H, qL_U_H, ?_, hsnew.trans qL_U_S,
    qL_U_S, (a₁old_eq_A₁c_of_respectsR qL_respectsR).trans qL_A₁c, qL_A₁c,
    qL_a₂old, qL_A₂c, qL_b₁new, qL_ub₁, ?_⟩
  · rw [qL_s₀old, min_eq_left γ₀_le_γ₁]
  · intro d hd
    obtain ⟨c, hc⟩ := hd
    have hnd := not_mute₂_of_low le_rfl d
    rw [qL_of_proper hnd hc]
    by_cases hg : D₂.grade d.1 = 2
    · rw [ite_eq_left hg, t₀_F_bot (by rwa [gradeP_le_of_proper hnd hc])]
    · rw [ite_eq_right hg, t₀_F_v₀ (by
        have := c.gradeP_le_two
        rw [gradeP_le_of_proper hnd hc] at this ⊢
        omega)]

/-- Every named and dependent cell has the intended value. -/
theorem shape (κ κ' : ExtOrd) (hle : κ ≤ κ') :
    Shape₃ (display κ κ') v₀ κ κ' κ' η₁ κ κ' := by
  have S := original_shape
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change retarget κ κ' (qL H₀old) = κ
    rw [S.at_H₀old, retarget_cap]
  · change retarget κ κ' (qL H₀new) = κ'
    rw [S.at_H₀new, retarget_high]
  · change retarget κ κ' (qL U_H) = κ'
    rw [S.at_U_H, retarget_high]
  · change retarget κ κ' (qL s₀old) = min κ κ'
    rw [S.at_s₀old, min_eq_left γ₀_le_γ₁, retarget_cap, min_eq_left hle]
  · change retarget κ κ' (qL s₀new) = κ'
    rw [S.at_s₀new, retarget_high]
  · change retarget κ κ' (qL U_S) = κ'
    rw [S.at_U_S, retarget_high]
  · change retarget κ κ' (qL a₁old) = η₁
    rw [S.at_a₁old, retarget_low _ _ lowCap_lt_cap]
  · change retarget κ κ' (qL A₁c) = η₁
    rw [S.at_A₁c, retarget_low _ _ lowCap_lt_cap]
  · change retarget κ κ' (qL a₂old) = κ
    rw [S.at_a₂old, retarget_cap]
  · change retarget κ κ' (qL A₂c) = κ
    rw [S.at_A₂c, retarget_cap]
  · change retarget κ κ' (qL b₁new) = κ'
    rw [S.at_b₁new, retarget_high]
  · change retarget κ κ' (qL ub₁) = κ'
    rw [S.at_ub₁, retarget_high]
  · intro d hd
    change retarget κ κ' (qL d.1) = _
    rw [S.at_proper d hd]
    split
    · exact retarget_low _ _ (bot_lt_ofOrd _)
    · exact retarget_low _ _ proper_lt_cap

/-- All semantic laws for the display follow from the existing sufficiency theorem. -/
theorem display_respects {κ κ' : ExtOrd} (hκ : γ₀ ≤ κ) (hle : κ ≤ κ')
    (hvκ : SelfVis 3 κ) (hvκ' : SelfVis 3 κ') :
    RespectsSemanticsBelow rowsR (Finset.univ, 3) (display κ κ') :=
  respects_of_shape₃ (legal hκ hle hvκ hvκ') (shape κ κ' hle)

/-- The protected context is the whole A face, including both exact low values and a high cap. -/
noncomputable def context (κ : ExtOrd) (d : D₂.below faceA) : ExtOrd :=
  display κ κ (CellScheme.below.mono faceA_le d)

/-- Raising the fresh high value leaves the entire protected context literally unchanged. -/
theorem display_extends (κ κ' : ExtOrd) (d : D₂.below faceA) :
    display κ κ' (CellScheme.below.mono faceA_le d) = context κ d := by
  apply retarget_independent
  have h := (min_qL_γ₀ (not_mute₂_of_low le_rfl (CellScheme.below.mono faceA_le d))).trans
    (qL_of_A d.2).symm
  exact min_eq_left_iff.mp h

theorem context_respects {κ : ExtOrd} (hκ : γ₀ ≤ κ) (hvκ : SelfVis 3 κ) :
    RespectsSemanticsBelow rowsR faceA (context κ) :=
  (display_respects hκ le_rfl hvκ hvκ).mono faceA_le

theorem context_high (κ : ExtOrd) : context κ ⟨a₂old, a₂old_memA⟩ = κ :=
  (shape κ κ le_rfl).at_a₂old

theorem context_low (κ : ExtOrd) : context κ ⟨a₁old, a₁old_memA⟩ = η₁ :=
  (shape κ κ le_rfl).at_a₁old

/-- Exact low proper values are independent of both high parameters. -/
theorem display_proper (κ κ' : ExtOrd) (hle : κ ≤ κ') (d : Lower) (hd : IsProper d.1) :
    display κ κ' d = if D₂.grade d.1 = 2 then ⊥ else v₀ :=
  (shape κ κ' hle).at_proper d hd

/-- The mixed context is inhabited, and all its respecting extensions have fresh top readback. -/
theorem universal_readback (β : Ordinal.{0}) {κ : ExtOrd} (hκ : γ₀ ≤ κ)
    (hvκ : SelfVis 3 κ) (hβ : ofOrd β ≤ κ) :
    (∃ q : Lower → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, 3) q ∧
      ∀ d, q (CellScheme.below.mono faceA_le d) = context κ d) ∧
    (∀ q : Lower → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, 3) q →
      (∀ d, q (CellScheme.below.mono faceA_le d) = context κ d) →
      truncExt β (q fresh) = ⊤) :=
  faceA_universal_readback β (context κ) (context_respects hκ hvκ)
    (by rwa [context_high])

/-- Over the same mixed context one can prescribe any larger grade-three self-visible high. -/
theorem prescribed_fresh {κ κ' : ExtOrd} (hκ : γ₀ ≤ κ) (hle : κ ≤ κ')
    (hvκ : SelfVis 3 κ) (hvκ' : SelfVis 3 κ') :
    RespectsSemanticsBelow rowsR (Finset.univ, 3) (display κ κ') ∧
      (∀ d, display κ κ' (CellScheme.below.mono faceA_le d) = context κ d) ∧
      display κ κ' fresh = κ' :=
  ⟨display_respects hκ hle hvκ hvκ', display_extends κ κ', (shape κ κ' hle).at_b₁new⟩

/-- The protected shared pair, before either three-point face is added. -/
abbrev root : Finset (Fin 4) × ℕ := ({1, 2}, 2)

theorem root_le_faceA : GradedLe root faceA := ⟨by decide, by decide⟩

theorem root_isProper (d : D₂.below root) : IsProper d.1 := by
  have hA := d.2.trans root_le_faceA
  have hn := not_mute₂_of_low le_rfl (CellScheme.below.mono faceA_le ⟨d.1, hA⟩)
  have hz : (0 : Fin 4) ∉ D₂.scope d.1 := fun h => by
    have := d.2.1 h
    revert this
    decide
  rcases below_Aold_cases hn hA with h | h | h | h | h
  · exact False.elim (hz (h ▸ zero_mem_scope_H₀old))
  · exact False.elim (hz (h ▸ zero_mem_scope_s₀old))
  · exact False.elim (hz (h ▸ zero_mem_scope_a₁old))
  · exact False.elim (hz (h ▸ zero_mem_scope_a₂old))
  · exact h

/-- The whole shared root is retained literally, independently of the high reference. -/
theorem context_root (κ : ExtOrd) (d : D₂.below root) :
    context κ (CellScheme.below.mono root_le_faceA d) =
      if D₂.grade d.1 = 2 then ⊥ else v₀ :=
  display_proper κ κ le_rfl _ (root_isProper d)

/-- Different fresh labels really occur over one and the same protected mixed context. -/
theorem fresh_varies_over_context {κ κ' : ExtOrd} (hκ : γ₀ ≤ κ) (hlt : κ < κ')
    (hvκ : SelfVis 3 κ) (hvκ' : SelfVis 3 κ') :
    ∃ q r : Lower → ExtOrd,
      RespectsSemanticsBelow rowsR (Finset.univ, 3) q ∧
      RespectsSemanticsBelow rowsR (Finset.univ, 3) r ∧
      (∀ d, q (CellScheme.below.mono faceA_le d) = context κ d) ∧
      (∀ d, r (CellScheme.below.mono faceA_le d) = context κ d) ∧ q fresh < r fresh := by
  refine ⟨display κ κ, display κ κ', display_respects hκ le_rfl hvκ hvκ,
    display_respects hκ hlt.le hvκ hvκ', display_extends κ κ,
    display_extends κ κ', ?_⟩
  change display κ κ ⟨b₁new, memb₁new₃⟩ < display κ κ' ⟨b₁new, memb₁new₃⟩
  rw [(shape κ κ le_rfl).at_b₁new, (shape κ κ' hlt.le).at_b₁new]
  exact hlt

/-! ## A concrete mixed cut, not an all-high display -/

/-- At cut `ω·2`, the root values and the old lowest cap stay strictly below the cut. -/
theorem mixed_low_values :
    (∀ d : D₂.below root,
      context γ₁ (CellScheme.below.mono root_le_faceA d) < ofOrd (ω2 0)) ∧
    context γ₁ ⟨a₁old, a₁old_memA⟩ = η₁ ∧ η₁ < ofOrd (ω2 0) := by
  refine ⟨?_, context_low _, η₁_lt_ω2 0⟩
  intro d
  rw [context_root]
  split
  · exact bot_lt_ofOrd _
  · exact v₀_lt_ω2 0

/-- An inhabited mixed context forces top fresh readback in every respecting extension. -/
theorem mixed_cut_readback :
    (∃ q : Lower → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, 3) q ∧
      ∀ d, q (CellScheme.below.mono faceA_le d) = context γ₁ d) ∧
    (∀ q : Lower → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, 3) q →
      (∀ d, q (CellScheme.below.mono faceA_le d) = context γ₁ d) →
      truncExt (ω2 0) (q fresh) = ⊤) :=
  universal_readback (ω2 0) γ₀_le_γ₁ (selfVis_ω2 3 3 le_rfl)
    (ofOrd_le_ofOrd.mpr (ω2_lt_ω2 (by decide : 0 < 3)).le)

/-- The same concrete context admits fresh values `ω·2+3` and `ω·2+4`. -/
theorem mixed_fresh_not_determined :
    ∃ q r : Lower → ExtOrd,
      RespectsSemanticsBelow rowsR (Finset.univ, 3) q ∧
      RespectsSemanticsBelow rowsR (Finset.univ, 3) r ∧
      (∀ d, q (CellScheme.below.mono faceA_le d) = context γ₁ d) ∧
      (∀ d, r (CellScheme.below.mono faceA_le d) = context γ₁ d) ∧ q fresh < r fresh :=
  fresh_varies_over_context γ₀_le_γ₁ ω2_three_lt_four
    (selfVis_ω2 3 3 le_rfl) (selfVis_ω2 3 4 (by decide))

end VaughtConjecture.Knight.MixedReferenceEntailment
