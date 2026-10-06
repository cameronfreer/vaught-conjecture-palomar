/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TwoContextSeparation
public import VaughtConjecture.Knight.WitnessAlgebra

/-! # The coupled construction: separating mixed rows at grades one to three, jointly with a
respecting labelling realizing the original prescribed pair

**The milestone**: one attachment of the two contexts realizing the prescribed data — the
specified labellings `p₀` (input A, the row of its cap `ω+4`) and `p₁` (input B, the row of its
cap `ω·2+3`) — with both input faces (cells, rows, labels) untouched (`coupled_realization`).
Legality is established except bountifulness: the modified semantics `rows₃` is **coded**
(`rows₃_coded`) and **consistent** (`rows₃_consistent`), agrees with the fixed glue `rows₂` on
both faces (`rows₃_faceA`, `rows₃_faceB`), and the labelling `qL` **respects** it on the full
grade-three lower set (`qL_respects`) and **realizes the pair** (`qL_realizes`).

**The rows.** Exactly three rows change, at the three fresh full-scope controllers that the
labels force to separate (`separating_controllers_of_realizes`):
* grade one (`U_H`, the full copy of the level-one witness): the tested row — the pulled-back
  row with the separating value `ω·2+2` at the copy `H₀new` and at the diagonal (`vU`);
* grade two (`U_S`, the full copy of the level-two witness): the pulled-back row with `ω·2+3` at
  the copies of `H₀` and `s₀`, at `U_H` and at the diagonal (`vS`) — the raised grade-one value
  propagates through the grade-two row's value at `U_H` (`locality_U_S_U_H`: a double
  `Witness.raise`), not by raising the diagonal alone;
* grade three (`ub₁`, the full copy of input B's cap): the row *is* the labelling.
The other two level-three copies (`A₁c`, `A₂c`) and the mute cell keep their pulled-back rows.

**The labelling** `qL` is input B's row pulled back (`labelQ`), lowered to `ω+4` at input A's
two witnesses `H₀old`, `s₀old`.  On the A face it is the row of input A's cap `a₂`
(`qL_castAdd`), on the B face input B's row (`qL_of_B`).

**The witnesses.** The labelling's locality at `U_H` and `U_S` is a **clamp** witness
(`Witness.clamp`, new here: `min a c` below a cutoff of finite part `> K`, the constant `c'`
from the cutoff on): the grade-one decoder must send the cap codes `ω·2+1`, `ω·2+2` *down* to
`ω+4` and the separating values *up* to `ω·2+3`, which neither `Witness.raise` nor
`Witness.lower` alone can do.  Consistency at the higher controllers uses the two generic
modifications `transformsTo_of_raise` (raised sources under a cap) and `transformsTo_of_between`
(a source replaced by the source of a cell with equal target, between the two), and the explicit
raises `witness_raise2`, `witness_raise_H`, `witness_raise_s`.  The numeric code values are
computed (`H₀c.δ = ω·2+1`, `s₀c.γ = ω·2+2`, `v₀` the only proper value).

**Not claimed**: bountifulness of `rows₃` (Def. 2.5.14; `rows₂`'s was proved from the two face
obligations, stated against the glue's rows), the `SemScheme` packaging, any logical
extension-spectrum distinction, realization inside fixed models.  Construction-private
(not root-exported). -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## The numeric codes of the three-cell family -/

section Values

/-- The ordinal of `v₀`. -/
abbrev ω1 : Ordinal.{0} := Ordinal.omega0 * ((1 : ℕ) : Ordinal) + ((1 : ℕ) : Ordinal)

theorem v₀_eq_ω1 : v₀ = ofOrd ω1 := rfl

theorem valuesAt_t₀ {l : ℕ} (hl : 1 ≤ l) : valuesAt Prop3.gradeP t₀.F l = {ω1} := by
  ext v
  rw [mem_valuesAt Prop3.gradeP, Finset.mem_singleton]
  constructor
  · rintro ⟨c, -, hF⟩
    rcases t₀_F_cases c with h | h
    · rw [h, v₀_eq_ω1] at hF; exact (ofOrd_inj.mp hF).symm
    · rw [h] at hF; exact absurd hF.symm (ofOrd_ne_bot _)
  · rintro rfl
    exact ⟨Prop3.s0, (by decide : Prop3.s0.gradeP ≤ 1).trans hl, t₀_F_eq (by decide)⟩

theorem keys_t₀ {l : ℕ} (hl : 1 ≤ l) :
    keys l (valuesAt Prop3.gradeP t₀.F l) = {keyOrd l ω1} := by
  rw [valuesAt_t₀ hl]; exact Finset.image_singleton _ _

theorem card_keys_t₀ {l : ℕ} (hl : 1 ≤ l) : (keys l (valuesAt Prop3.gradeP t₀.F l)).card = 1 := by
  rw [keys_t₀ hl]; exact Finset.card_singleton _

theorem blockOf_t₀ {l : ℕ} (hl : 1 ≤ l) : blockOf l (valuesAt Prop3.gradeP t₀.F l) ω1 = 1 := by
  unfold blockOf blockOfKey
  rw [keys_t₀ hl, Finset.filter_singleton, ite_eq_left le_rfl]
  exact Finset.card_singleton _

theorem code_t₀ {l : ℕ} (hl : 1 ≤ l) : code l (valuesAt Prop3.gradeP t₀.F l) ω1 = ω1 := by
  unfold code
  rw [blockOf_t₀ hl, finitePart_mul_add, min_eq_left hl]

theorem capCode_t₀ {l : ℕ} (hl : 1 ≤ l) :
    capCode l (valuesAt Prop3.gradeP t₀.F l) =
      Ordinal.omega0 * ((2 : ℕ) : Ordinal) + ((l : ℕ) : Ordinal) := by
  unfold capCode
  rw [card_keys_t₀ hl]

/-- The ordinals `ω·2 + j`. -/
abbrev ω2 (j : ℕ) : Ordinal.{0} := Ordinal.omega0 * ((2 : ℕ) : Ordinal) + ((j : ℕ) : Ordinal)

theorem t₀_F_v₀ {c : Prop3} (hc : c.gradeP ≤ 1) : t₀.F c = v₀ := t₀_F_eq hc

theorem H₀c_G_v₀ {c : Prop3} (hc : c.gradeP ≤ 1) : H₀c.G c = v₀ := by
  rw [H₀c_G_eq hc]
  change ofOrd (code 1 _ ω1) = _
  rw [code_t₀ le_rfl]; rfl

theorem H₀c_δ_num : H₀c.δ = ofOrd (ω2 1) := by
  change ofOrd (capCode 1 (valuesAt Prop3.gradeP t₀.F 1)) = _
  rw [capCode_t₀ le_rfl]

theorem s₀c_F_v₀ {c : Prop3} (hc : c.gradeP ≤ 1) : s₀c.F c = v₀ := by
  change witnessRow Prop3.gradeP t₀.F 2 (valuesAt Prop3.gradeP t₀.F 2) c = v₀
  rw [witnessRow_ofOrd Prop3.gradeP (hc.trans (by decide)) (t₀_F_eq hc)]
  change ofOrd (code 2 _ ω1) = _
  rw [code_t₀ (by decide)]; rfl

theorem s₀c_γ_num : s₀c.γ = ofOrd (ω2 2) := by
  change ofOrd (capCode 2 (valuesAt Prop3.gradeP t₀.F 2)) = _
  rw [capCode_t₀ (by decide)]

theorem rho_s₀c_H₀c : s₀c.rho st₀ H₀c = s₀c.γ := by
  rw [← H₁c_eq]
  exact dirVal1_witness st₀.hT s₀c.F (s₀c.orderly st₀) s₀c.γ

theorem wSep_num : wSep = ofOrd (ω2 2) := by
  unfold wSep limSep kSep
  rw [card_keys_t₀ le_rfl]

theorem cutSep_num : cutSep = Ordinal.omega0 * ((1 : ℕ) : Ordinal) + ((2 : ℕ) : Ordinal) := by
  unfold cutSep kSep
  rw [card_keys_t₀ le_rfl]

theorem γ₁_num : γ₁ = ofOrd (ω2 3) := rfl
theorem γ₀_num : γ₀ = ofOrd (Ordinal.omega0 * ((1 : ℕ) : Ordinal) + ((4 : ℕ) : Ordinal)) := rfl

/-! ### The rows of the three-cell family at `s₀` -/

theorem rowX_s₀_inl (c : Prop3) : family₂.rowX s₀X (.inl c) = s₀c.F c := rfl
theorem rowX_s₀_H : family₂.rowX s₀X H₀X = s₀c.γ := rho_s₀c_H₀c
theorem rowX_s₀_s : family₂.rowX s₀X s₀X = s₀c.γ := meet₂_self st₀ s₀c

end Values

/-! ## A general witness: clamp below a cutoff, constant above -/

section Clamp

open Classical in
/-- **The clamp shifter**: `min a c` below the cutoff `ξ`, the constant `c'` from `ξ` on. -/
noncomputable def clampShifter (c : ExtOrd) (ξ : Ordinal.{0}) (c' : ExtOrd) : ExtOrd → ExtOrd :=
  fun a => if a < ofOrd ξ then min a c else c'

theorem clampShifter_of_lt {c : ExtOrd} {ξ : Ordinal.{0}} {c' a : ExtOrd} (h : a < ofOrd ξ) :
    clampShifter c ξ c' a = min a c := by
  classical
  unfold clampShifter; rw [ite_eq_left h]

theorem clampShifter_of_ge {c : ExtOrd} {ξ : Ordinal.{0}} {c' a : ExtOrd} (h : ofOrd ξ ≤ a) :
    clampShifter c ξ c' a = c' := by
  classical
  unfold clampShifter; rw [ite_eq_right (not_lt.mpr h)]

/-- **The clamp witness**: for a cutoff of finite part above `K`, a clamp value `c ≤ c'` and a
constant `c'`, both self-visible at `K` and nonbottom. -/
theorem Witness.clamp (K : ℕ) {ξ : Ordinal.{0}} (hξ : K < finitePart ξ) {c c' : ExtOrd}
    (hc : SelfVis K c) (hc' : SelfVis K c') (hcc' : c ≤ c') (hc0 : c ≠ ⊥) (hc'0 : c' ≠ ⊥) :
    Witness (gTop K) (clampShifter c ξ c') where
  anti := (witness_id K).anti
  vis := (witness_id K).vis
  bot := by rw [clampShifter_of_lt (bot_lt_ofOrd ξ)]; exact min_eq_left bot_le
  mono := by
    intro a b hab
    by_cases ha : a < ofOrd ξ
    · rw [clampShifter_of_lt ha]
      by_cases hb : b < ofOrd ξ
      · rw [clampShifter_of_lt hb]; exact min_le_min hab le_rfl
      · rw [clampShifter_of_ge (not_lt.mp hb)]; exact (min_le_right _ _).trans hcc'
    · have hb : ¬ b < ofOrd ξ := fun hb => ha (lt_of_le_of_lt hab hb)
      rw [clampShifter_of_ge (not_lt.mp ha), clampShifter_of_ge (not_lt.mp hb)]
  clause5 := by
    intro α k hk i hi
    by_cases hkK : k ≤ K
    · by_cases hα : α < ofOrd ξ
      · have h1 : extVisibilityReplace α k i < ofOrd ξ := extVisReplace_lt_cutoff hξ hkK hi hα
        rw [clampShifter_of_lt hα, clampShifter_of_lt h1]
        have hm : Monotone (fun z : ExtOrd => extVisibilityReplace z k i) :=
          fun a b h => evr_mono h hi
        rw [hm.map_min, evr_eq_self_of_selfVis (hc.mono hkK)]
      · have hα' : ofOrd ξ ≤ α := not_lt.mp hα
        have h1 : ofOrd ξ ≤ extVisibilityReplace α k i :=
          extVisReplace_ge_cutoff (hkK.trans hξ.le) hα'
        rw [clampShifter_of_ge hα', clampShifter_of_ge h1, evr_eq_self_of_selfVis (hc'.mono hkK)]
    · rw [gTop_of_gt (by omega)] at hk
      have hσ : clampShifter c ξ c' α = ⊥ := le_bot_iff.mp hk
      have hα : α = ⊥ := by
        by_cases hlt : α < ofOrd ξ
        · rw [clampShifter_of_lt hlt] at hσ
          rcases min_eq_bot.mp hσ with h | h
          · exact h
          · exact absurd h hc0
        · rw [clampShifter_of_ge (not_lt.mp hlt)] at hσ; exact absurd hσ hc'0
      subst hα
      rw [extVisibilityReplace_bot, hσ, extVisibilityReplace_bot]

end Clamp

/-! ## The cell inventory of the glued domain -/

section Inventory

/-- The fresh full copy of a full-scope cell of the three-cell family. -/
noncomputable def fullCell (x : family₂.X) (hx : (family₂.cellX x).1 = Finset.univ) : Cell D₂ :=
  Fin.natAdd C₀.card ((Fintype.equivFin New₂) (.inr (.inl ⟨family₂.e x, by
    change (C₂.cell (family₂.e x)).1 = _; rw [Family.cell_e]; exact hx⟩)))

theorem cell_fullCell (x : family₂.X) (hx : (family₂.cellX x).1 = Finset.univ) :
    D₂.cell (fullCell x hx) = (Finset.univ, (family₂.cellX x).2) := by
  unfold fullCell
  rw [D₂_cell_natAdd, Equiv.symm_apply_apply]
  change (Finset.univ, (C₂.cell (family₂.e x)).2) = _
  rw [Family.cell_e]

theorem ret₂_fullCell (x : family₂.X) (hx : (family₂.cellX x).1 = Finset.univ) :
    ret₂ (fullCell x hx) = family₂.e x := by
  unfold fullCell; rw [ret₂_natAdd, Equiv.symm_apply_apply]; rfl

theorem not_mute_fullCell (x : family₂.X) (hx : (family₂.cellX x).1 = Finset.univ)
    (h : (family₂.cellX x).2 ≠ 4) : ¬ mute₂ (fullCell x hx) := by
  intro hm
  change D₂.cell _ = _ at hm
  rw [cell_fullCell] at hm
  exact h (congrArg Prod.snd hm)

/-- The grade-two full controller (the fresh full copy of `s₀`) and the two level-three copies. -/
noncomputable def U_S : Cell D₂ := fullCell s₀X rfl
noncomputable def A₁c : Cell D₂ := fullCell a₁X rfl
noncomputable def A₂c : Cell D₂ := fullCell a₂X rfl

theorem U_H_eq : U_H = fullCell H₀X rfl := rfl
theorem ub₁_eq : ub₁ = fullCell b₁X rfl := rfl

theorem cell_U_S : D₂.cell U_S = (Finset.univ, 2) := cell_fullCell _ _
theorem cell_A₁c : D₂.cell A₁c = (Finset.univ, 3) := cell_fullCell _ _
theorem cell_A₂c : D₂.cell A₂c = (Finset.univ, 3) := cell_fullCell _ _
theorem grade_U_S : D₂.grade U_S = 2 := by change (D₂.cell U_S).2 = 2; rw [cell_U_S]
theorem grade_ub₁ : D₂.grade ub₁ = 3 := by change (D₂.cell ub₁).2 = 3; rw [cell_ub₁]
theorem ret₂_U_S : ret₂ U_S = family₂.e s₀X := ret₂_fullCell _ _
theorem ret₂_A₁c : ret₂ A₁c = family₂.e a₁X := ret₂_fullCell _ _
theorem ret₂_A₂c : ret₂ A₂c = family₂.e a₂X := ret₂_fullCell _ _
theorem not_mute_U_S : ¬ mute₂ U_S := not_mute_fullCell _ _ (by decide)
theorem not_mute_A₁c : ¬ mute₂ A₁c := not_mute_fullCell _ _ (by decide)
theorem not_mute_A₂c : ¬ mute₂ A₂c := not_mute_fullCell _ _ (by decide)

/-- Input A's level-two and level-three cells on the A face. -/
noncomputable def s₀old : Cell D₂ := Fin.castAdd (Fintype.card New₂) (family₀.e s₀X₀)
noncomputable def a₁old : Cell D₂ := Fin.castAdd (Fintype.card New₂) (family₀.e a₁X₀)
noncomputable def a₂old : Cell D₂ := Fin.castAdd (Fintype.card New₂) (family₀.e a₂X₀)

theorem ret₂_castAdd_X (x : family₀.X) :
    ret₂ (Fin.castAdd (Fintype.card New₂) (family₀.e x)) = family₂.e (embX₀ x) := by
  rw [ret₂_castAdd]
  change family₂.e (embX₀ (family₀.e.symm (family₀.e x))) = _
  rw [Equiv.symm_apply_apply]

theorem ret₂_copyB_X (x : family₁.X) : ret₂ (copyB (family₁.e x)) = family₂.e (embX₁ x) := by
  rw [ret₂_copyB]
  change family₂.e (embX₁ (family₁.e.symm (family₁.e x))) = _
  rw [Equiv.symm_apply_apply]

theorem ret₂_s₀old : ret₂ s₀old = family₂.e s₀X := ret₂_castAdd_X s₀X₀
theorem ret₂_a₁old : ret₂ a₁old = family₂.e a₁X := ret₂_castAdd_X a₁X₀
theorem ret₂_a₂old : ret₂ a₂old = family₂.e a₂X := ret₂_castAdd_X a₂X₀
theorem ret₂_s₀new : ret₂ s₀new = family₂.e s₀X := ret₂_copyB_X s₀X₁
theorem ret₂_b₁new : ret₂ b₁new = family₂.e b₁X := ret₂_copyB_X b₁X₁

theorem cell_castAdd_X (x : family₀.X) :
    D₂.cell (Fin.castAdd (Fintype.card New₂) (family₀.e x)) =
      pushGraded Fin.castSuccEmb (family₀.cellX x) := by
  rw [D₂_cell_castAdd, Family.cell_e]

theorem grade_s₀old : D₂.grade s₀old = 2 := by
  change (D₂.cell s₀old).2 = 2; unfold s₀old; rw [cell_castAdd_X]; rfl

theorem zero_mem_scope_castAdd (x : family₀.X) (hx : (family₀.cellX x).1 = Finset.univ) :
    (0 : Fin 4) ∈ D₂.scope (Fin.castAdd (Fintype.card New₂) (family₀.e x)) := by
  rw [D₂_scope_castAdd, Family.scope_eq, Equiv.symm_apply_apply, hx]
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

theorem three_not_mem_scope_castAdd (i : Cell C₀) :
    (3 : Fin 4) ∉ D₂.scope (Fin.castAdd (Fintype.card New₂) i) := by
  rw [D₂_scope_castAdd]
  intro h
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp h
  exact absurd hx (Fin.ne_of_lt (Fin.castSucc_lt_last x))

theorem zero_not_mem_scope_copyB (c : Cell C₁) : (0 : Fin 4) ∉ D₂.scope (copyB c) := fun h =>
  absurd ((copyB_mem c).1 h) (by decide)

theorem castAdd_ne_copyB (x : family₀.X) (hx : (family₀.cellX x).1 = Finset.univ) (c : Cell C₁) :
    Fin.castAdd (Fintype.card New₂) (family₀.e x) ≠ copyB c := fun h =>
  zero_not_mem_scope_copyB c (h ▸ zero_mem_scope_castAdd x hx)

theorem castAdd_ne_fullCell (i : Cell C₀) (x : family₂.X) (hx : (family₂.cellX x).1 = Finset.univ) :
    Fin.castAdd (Fintype.card New₂) i ≠ fullCell x hx := fun h => by
  apply three_not_mem_scope_castAdd i
  rw [h]
  change (3 : Fin 4) ∈ (D₂.cell (fullCell x hx)).1
  rw [cell_fullCell]; exact Finset.mem_univ _

theorem s₀old_ne_s₀new : s₀old ≠ s₀new := castAdd_ne_copyB s₀X₀ rfl _
theorem s₀old_ne_U_S : s₀old ≠ U_S := castAdd_ne_fullCell _ s₀X rfl
theorem H₀old_ne_U_S : H₀old ≠ U_S := castAdd_ne_fullCell _ s₀X rfl
theorem H₀old_ne_s₀new : H₀old ≠ s₀new := castAdd_ne_copyB H₀X₀ rfl _

/-- **The pulled-back row of a full cell of the three-cell family, as a total function.** -/
noncomputable def pull (x : family₂.X) (d : Cell D₂) : ExtOrd :=
  if mute₂ d then ⊥ else family₂.rowX x (family₂.e.symm (ret₂ d))

theorem pull_of_not_mute (x : family₂.X) {d : Cell D₂} (hd : ¬ mute₂ d) :
    pull x d = family₂.rowX x (family₂.e.symm (ret₂ d)) := by
  unfold pull; rw [ite_eq_right hd]

theorem rows₂_E_eq_pull {y : Cell D₂} (hy : ¬ mute₂ y) (d : D₂.below (D₂.cell y)) :
    rows₂.E y d = pull (family₂.e.symm (ret₂ y)) d.1 := by
  rw [pull_of_not_mute _ (hmute_below₂ y d.1 hy d.2)]
  exact rows₂_E_of_not_mute hy d

theorem labelQ_eq_pull (d : Cell D₂) : labelQ d = pull b₁X d := by
  by_cases hd : mute₂ d
  · rw [labelQ_of_mute hd]; unfold pull; rw [ite_eq_left hd]
  · rw [labelQ_eq_rowX hd, pull_of_not_mute _ hd]

end Inventory

/-! ## The labelling and the three modified rows -/

section Rows

/-- **The labelling**: input B's row pulled back, lowered to `ω+4` at input A's two witnesses. -/
noncomputable def qL (d : Cell D₂) : ExtOrd := if d = H₀old ∨ d = s₀old then γ₀ else labelQ d

/-- **The grade-one row**: the separating value at the copy and the diagonal. -/
noncomputable def vU (d : Cell D₂) : ExtOrd :=
  if ret₂ d = family₂.e H₀X ∧ d ≠ H₀old then wSep else pull H₀X d

/-- **The grade-two row**: `ω·2+3` at the copies of `H₀`, `s₀`, at `U_H` and at the diagonal. -/
noncomputable def vS (d : Cell D₂) : ExtOrd :=
  if (ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X) ∧ ¬ (d = H₀old ∨ d = s₀old) then γ₁
  else pull s₀X d

/-- **The modified rows.** -/
noncomputable def E₃ (Sig : Cell D₂) (d : D₂.below (D₂.cell Sig)) : ExtOrd :=
  if Sig = U_H then vU d.1 else if Sig = U_S then vS d.1 else if Sig = ub₁ then qL d.1
  else rows₂.E Sig d

theorem E₃_U_H (d : D₂.below (D₂.cell U_H)) : E₃ U_H d = vU d.1 := by
  unfold E₃; rw [ite_eq_left rfl]
theorem ne_of_cell_ne {a b : Cell D₂} (h : D₂.cell a ≠ D₂.cell b) : a ≠ b :=
  fun e => h (congrArg _ e)
theorem U_S_ne_U_H : U_S ≠ U_H := ne_of_cell_ne fun h => by
  rw [cell_U_S, cell_U_H] at h; exact absurd (congrArg Prod.snd h) (by decide)
theorem ub₁_ne_U_H : ub₁ ≠ U_H := ne_of_cell_ne fun h => by
  rw [cell_ub₁, cell_U_H] at h; exact absurd (congrArg Prod.snd h) (by decide)
theorem ub₁_ne_U_S : ub₁ ≠ U_S := ne_of_cell_ne fun h => by
  rw [cell_ub₁, cell_U_S] at h; exact absurd (congrArg Prod.snd h) (by decide)

theorem E₃_U_S (d : D₂.below (D₂.cell U_S)) : E₃ U_S d = vS d.1 := by
  unfold E₃; rw [ite_eq_right U_S_ne_U_H, ite_eq_left rfl]
theorem E₃_ub₁ (d : D₂.below (D₂.cell ub₁)) : E₃ ub₁ d = qL d.1 := by
  unfold E₃; rw [ite_eq_right ub₁_ne_U_H, ite_eq_right ub₁_ne_U_S, ite_eq_left rfl]
theorem E₃_of_ne {Sig : Cell D₂} (h1 : Sig ≠ U_H) (h2 : Sig ≠ U_S) (h3 : Sig ≠ ub₁)
    (d : D₂.below (D₂.cell Sig)) : E₃ Sig d = rows₂.E Sig d := by
  unfold E₃; rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

/-! ### Orderliness and coding of the modified rows -/

theorem grade_ret_eq {d : Cell D₂} (hd : ¬ mute₂ d) :
    D₂.grade d = (family₂.cellX (family₂.e.symm (ret₂ d))).2 := by
  rw [grade_ret₂ d hd]; rfl

theorem gradedLe_of_below {x : family₂.X} (hx : (family₂.cellX x).1 = Finset.univ) {d : Cell D₂}
    (hd : ¬ mute₂ d) (h : GradedLe (D₂.cell d) (Finset.univ, (family₂.cellX x).2)) :
    GradedLe (family₂.cellX (family₂.e.symm (ret₂ d))) (family₂.cellX x) :=
  ⟨by rw [hx]; exact Finset.subset_univ _, by rw [← grade_ret_eq hd]; exact h.2⟩

theorem pull_selfVis (x : family₂.X) (hx : (family₂.cellX x).1 = Finset.univ) {d : Cell D₂}
    (hd : ¬ mute₂ d) (h : GradedLe (D₂.cell d) (Finset.univ, (family₂.cellX x).2)) :
    SelfVis (D₂.grade d) (pull x d) := by
  rw [pull_of_not_mute x hd, grade_ret_eq hd]
  exact family₂.rowX_selfVis x _ (gradedLe_of_below hx hd h)

theorem pull_coded (x : family₂.X) (hx : (family₂.cellX x).1 = Finset.univ) {d : Cell D₂}
    (hd : ¬ mute₂ d) (h : GradedLe (D₂.cell d) (Finset.univ, (family₂.cellX x).2)) :
    IsCodedLabel (family₂.cellX x).2 (pull x d) := by
  rw [pull_of_not_mute x hd]
  exact family₂.rowX_coded x _ (gradedLe_of_below hx hd h)

theorem below_U_H_mem (d : D₂.below (D₂.cell U_H)) :
    GradedLe (D₂.cell d.1) (Finset.univ, (family₂.cellX H₀X).2) :=
  d.2.trans (by rw [cell_U_H]; exact GradedLe.refl _)
theorem below_U_S_mem (d : D₂.below (D₂.cell U_S)) :
    GradedLe (D₂.cell d.1) (Finset.univ, (family₂.cellX s₀X).2) :=
  d.2.trans (by rw [cell_U_S]; exact GradedLe.refl _)
theorem not_mute_below_U_H (d : D₂.below (D₂.cell U_H)) : ¬ mute₂ d.1 :=
  hmute_below₂ U_H d.1 not_mute_U_H d.2
theorem not_mute_below_U_S (d : D₂.below (D₂.cell U_S)) : ¬ mute₂ d.1 :=
  hmute_below₂ U_S d.1 not_mute_U_S d.2
theorem not_mute_below_ub₁ (d : D₂.below (D₂.cell ub₁)) : ¬ mute₂ d.1 :=
  hmute_below₂ ub₁ d.1 not_mute_ub₁ d.2
theorem grade_le_below_U_S (d : D₂.below (D₂.cell U_S)) : D₂.grade d.1 ≤ 2 := (below_U_S_mem d).2
theorem grade_le_below_ub₁ (d : D₂.below (D₂.cell ub₁)) : D₂.grade d.1 ≤ 3 :=
  (d.2.trans (show GradedLe (D₂.cell ub₁) (Finset.univ, 3) by
    rw [cell_ub₁]; exact GradedLe.refl _)).2

/-- A cell retracting to the level-one witness has grade one. -/
theorem grade_of_ret_H₀ {d : Cell D₂} (hd : ¬ mute₂ d) (h : ret₂ d = family₂.e H₀X) :
    D₂.grade d = 1 := by
  rw [grade_ret_eq hd, h, Equiv.symm_apply_apply]; rfl

theorem vU_selfVis (d : D₂.below (D₂.cell U_H)) : SelfVis (D₂.grade d.1) (vU d.1) := by
  unfold vU
  split_ifs with h
  · rw [grade_of_ret_H₀ (not_mute_below_U_H d) h.1]; exact wSep_selfVis
  · exact pull_selfVis H₀X rfl (not_mute_below_U_H d) (below_U_H_mem d)

theorem vS_selfVis (d : D₂.below (D₂.cell U_S)) : SelfVis (D₂.grade d.1) (vS d.1) := by
  unfold vS
  split_ifs with h
  · exact γ₁_vis.mono ((grade_le_below_U_S d).trans (by decide))
  · exact pull_selfVis s₀X rfl (not_mute_below_U_S d) (below_U_S_mem d)

theorem qL_selfVis (d : D₂.below (D₂.cell ub₁)) : SelfVis (D₂.grade d.1) (qL d.1) := by
  unfold qL
  split_ifs with h
  · exact γ₀_vis.mono (grade_le_below_ub₁ d)
  · exact (Q.respects.orderly d.1).symm

/-- **The modified semantics.** -/
noncomputable def rows₃ : Semantics D₂ where
  E := E₃
  orderly Sig d := by
    change E₃ Sig d = extVisibilityReplace (E₃ Sig d) (D₂.grade d.1) (D₂.grade d.1)
    by_cases h1 : Sig = U_H
    · subst h1; rw [E₃_U_H]; exact (vU_selfVis d).symm
    by_cases h2 : Sig = U_S
    · subst h2; rw [E₃_U_S]; exact (vS_selfVis d).symm
    by_cases h3 : Sig = ub₁
    · subst h3; rw [E₃_ub₁]; exact (qL_selfVis d).symm
    rw [E₃_of_ne h1 h2 h3]; exact rows₂.orderly Sig d

theorem rows₃_E (Sig : Cell D₂) (d : D₂.below (D₂.cell Sig)) : rows₃.E Sig d = E₃ Sig d := rfl

/-- **Coded.** -/
theorem rows₃_coded : rows₃.IsCoded := by
  intro Sig d
  change IsCodedLabel (D₂.grade Sig) (E₃ Sig d)
  by_cases h1 : Sig = U_H
  · subst h1; rw [E₃_U_H, grade_U_H]; unfold vU; split_ifs
    · rw [wSep_num]; exact Or.inr ⟨2, 2, by omega, rfl⟩
    · exact pull_coded H₀X rfl (not_mute_below_U_H d) (below_U_H_mem d)
  by_cases h2 : Sig = U_S
  · subst h2; rw [E₃_U_S, grade_U_S]; unfold vS; split_ifs
    · exact Or.inr ⟨2, 3, by omega, rfl⟩
    · exact pull_coded s₀X rfl (not_mute_below_U_S d) (below_U_S_mem d)
  by_cases h3 : Sig = ub₁
  · subst h3; rw [E₃_ub₁, grade_ub₁]; unfold qL; split_ifs
    · exact Or.inr ⟨1, 4, by omega, rfl⟩
    · have := rows₂_isCoded ub₁ d
      rw [grade_ub₁] at this
      erw [rows₂_ub₁] at this
      exact this
  rw [E₃_of_ne h1 h2 h3]; exact rows₂_isCoded Sig d

end Rows

/-! ## Generic transport lemmas -/

section Generic
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- Respect only reads the rows at the cells of the lower set. -/
theorem RespectsSemanticsBelow.congr_sem {sem sem' : Semantics D} {BJ : Finset ι × ℕ}
    {r : D.below BJ → ExtOrd} (h : RespectsSemanticsBelow sem BJ r)
    (he : ∀ Sig : D.below BJ, sem'.E Sig.1 = sem.E Sig.1) :
    RespectsSemanticsBelow sem' BJ r where
  orderly := h.orderly
  locality Sig := by rw [he Sig]; exact h.locality Sig
  availability := h.availability

theorem respects_of_cell_eq {sem : Semantics D} {BJ BJ' : Finset ι × ℕ} (h : BJ = BJ')
    {p : Cell D → ExtOrd} (hr : RespectsSemanticsBelow sem BJ (fun d => p d.1)) :
    RespectsSemanticsBelow sem BJ' (fun d => p d.1) := by
  subst h; exact hr

theorem Witness.anti_le {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hw : Witness g σ) {n m : ℕ}
    (h : n ≤ m) : g m ≤ g n := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact hw.anti n m h
  · exact le_rfl

/-- **Raising sources under a cap**: a transformation with targets at most `c` survives raising
some sources, provided each raised cell already has target `c` and its new source dominates the
source of a cell with target `c`. -/
theorem transformsTo_of_raise {X : Type*} {grade : X → ℕ} {f f' t : X → ExtOrd} (K : ℕ)
    {c : ExtOrd} (h : TransformsTo grade f t) (hK : ∀ d, grade d ≤ K) (hc : SelfVis K c)
    (ht : ∀ d, t d ≤ c)
    (hf' : ∀ d, f' d = f d ∨ (t d = c ∧ ∃ d₀, f d₀ ≤ f' d ∧ t d₀ = c)) :
    TransformsTo grade f' t := by
  obtain ⟨g, σ, hw, heq⟩ := TransformsTo.witness h
  refine (hw.cap K hc).transformsTo fun d => ?_
  rw [capG_of_le (hK d)]
  rcases hf' d with hd | ⟨htd, d₀, hle, htd₀⟩
  · rw [hd, ← min_assoc, ← heq d]; exact (min_eq_left (ht d)).symm
  · have h1 : c ≤ σ (f' d) := by
      have := heq d₀
      rw [htd₀] at this
      exact (this.le.trans (min_le_left _ _)).trans (hw.mono hle)
    have h2 : c ≤ g (grade d) := by
      have := heq d
      rw [htd] at this
      exact this.le.trans (min_le_right _ _)
    rw [htd, min_eq_right h2, min_eq_right h1]

/-- **Replacing a source between two sources with equal targets** keeps the transformation. -/
theorem transformsTo_of_between {X : Type*} {grade : X → ℕ} {f f' t : X → ExtOrd}
    (h : TransformsTo grade f t)
    (hf' : ∀ d, f' d = f d ∨
      ∃ d₀, f' d = f d₀ ∧ f d₀ ≤ f d ∧ t d₀ = t d ∧ grade d ≤ grade d₀) :
    TransformsTo grade f' t := by
  obtain ⟨g, σ, hw, heq⟩ := TransformsTo.witness h
  refine hw.transformsTo fun d => ?_
  rcases hf' d with hd | ⟨d₀, hd, hle, ht, hg⟩
  · rw [hd]; exact heq d
  · rw [hd]
    apply le_antisymm
    · rw [← ht, heq d₀]; exact min_le_min le_rfl (hw.anti_le hg)
    · rw [heq d]; exact min_le_min (hw.mono hle) le_rfl

end Generic

/-! ## Classification of the cells -/

section Classification

theorem newFacesB_sub : ∀ B ∈ newFacesB, B ⊆ ({1, 2, 3} : Finset (Fin 4)) := by decide

theorem a_cases (a : ↥family₂.S₃) :
    (.inr (.inr (.inr a)) : family₂.X) = a₁X ∨ (.inr (.inr (.inr a)) : family₂.X) = a₂X ∨
    (.inr (.inr (.inr a)) : family₂.X) = b₁X := by
  have h : a.1 ∈ ({a₁, a₂, b₁} : Finset (CappedCore3 Prop3.gradeP T₀)) := a.2
  rcases Finset.mem_insert.mp h with h | h
  · exact Or.inl (congrArg (fun z : ↥family₂.S₃ => (.inr (.inr (.inr z)) : family₂.X))
      (Subtype.ext h))
  rcases Finset.mem_insert.mp h with h | h
  · exact Or.inr (Or.inl (congrArg (fun z : ↥family₂.S₃ => (.inr (.inr (.inr z)) : family₂.X))
      (Subtype.ext h)))
  · exact Or.inr (Or.inr (congrArg (fun z : ↥family₂.S₃ => (.inr (.inr (.inr z)) : family₂.X))
      (Subtype.ext (Finset.mem_singleton.mp h))))

theorem a₀_cases (a : ↥family₀.S₃) :
    embX₀ (.inr (.inr (.inr a))) = a₁X ∨ embX₀ (.inr (.inr (.inr a))) = a₂X := by
  have h : a.1 ∈ ({a₁, a₂} : Finset (CappedCore3 Prop3.gradeP T₀)) := a.2
  rcases Finset.mem_insert.mp h with h | h
  · exact Or.inl (congrArg (fun z : ↥family₂.S₃ => (.inr (.inr (.inr z)) : family₂.X))
      (Subtype.ext h))
  · exact Or.inr (congrArg (fun z : ↥family₂.S₃ => (.inr (.inr (.inr z)) : family₂.X))
      (Subtype.ext (Finset.mem_singleton.mp h)))

theorem eq_H₀X₀ (H : ↥family₀.S₁) : (.inr (.inl H) : family₀.X) = H₀X₀ :=
  congrArg (fun z : ↥family₀.S₁ => (.inr (.inl z) : family₀.X)) (Subtype.ext (mem_S₁_eq H.2))
theorem eq_s₀X₀ (s : ↥family₀.S₂) : (.inr (.inr (.inl s)) : family₀.X) = s₀X₀ :=
  congrArg (fun z : ↥family₀.S₂ => (.inr (.inr (.inl z)) : family₀.X))
    (Subtype.ext (Finset.mem_singleton.mp s.2))

/-- Every non-mute cell is on the A face, on the B face, or one of the five fresh full cells. -/
theorem cell_cases (d : Cell D₂) (hd : ¬ mute₂ d) :
    (∃ i, d = Fin.castAdd (Fintype.card New₂) i) ∨
    GradedLe (D₂.cell d) (({1, 2, 3} : Finset (Fin 4)), 3) ∨
    d = U_H ∨ d = U_S ∨ d = A₁c ∨ d = A₂c ∨ d = ub₁ := by
  induction d using Fin.addCases with
  | left i => exact Or.inl ⟨i, rfl⟩
  | right j =>
    right
    rcases hy : (Fintype.equivFin New₂).symm j with p | f | u
    · left
      rw [D₂_cell_natAdd, hy]
      refine ⟨newFacesB_sub _ p.1.1.2, ?_⟩
      change C₁.grade p.1.2 ≤ 3
      exact (C₁.grade_le_card_scope _).trans ((Finset.card_le_univ _).trans (by simp))
    · right
      have hj : j = (Fintype.equivFin New₂) (.inr (.inl f)) := by
        rw [← hy, Equiv.apply_symm_apply]
      have hf : (family₂.cellX (family₂.e.symm f.1)).1 = Finset.univ := by
        rw [← Family.scope_eq]; exact f.2
      have hf1 : f.1 = family₂.e (family₂.e.symm f.1) := (Equiv.apply_symm_apply _ _).symm
      rcases hw : family₂.e.symm f.1 with c | H | s | a
      · exfalso; rw [hw] at hf; exact Prop3.scope_ne_univ c hf
      · left
        rw [hw, eq_H₀X H] at hf1
        rw [hj, U_H_eq]; unfold fullCell; congr 4; exact Subtype.ext hf1
      · right; left
        rw [hw, eq_s₀X s] at hf1
        rw [hj]; unfold U_S fullCell; congr 4; exact Subtype.ext hf1
      · rw [hw] at hf1
        rcases a_cases a with ha | ha | ha <;> rw [ha] at hf1
        · right; right; left
          rw [hj]; unfold A₁c fullCell; congr 4; exact Subtype.ext hf1
        · right; right; right; left
          rw [hj]; unfold A₂c fullCell; congr 4; exact Subtype.ext hf1
        · right; right; right; right
          rw [hj, ub₁_eq]; unfold fullCell; congr 4; exact Subtype.ext hf1
    · exfalso; exact hd (mute₂_natAdd_unit hy)

theorem B_face_ne_fullCell {d : Cell D₂}
    (hd : GradedLe (D₂.cell d) (({1, 2, 3} : Finset (Fin 4)), 3))
    (x : family₂.X) (hx : (family₂.cellX x).1 = Finset.univ) : d ≠ fullCell x hx := fun h => by
  have h0 : (0 : Fin 4) ∈ D₂.scope d := by
    rw [h]; change (0 : Fin 4) ∈ (D₂.cell _).1; rw [cell_fullCell]; exact Finset.mem_univ _
  exact absurd (hd.1 h0) (by decide)

theorem B_face_ne_old {d : Cell D₂} (hd : GradedLe (D₂.cell d) (({1, 2, 3} : Finset (Fin 4)), 3))
    (x : family₀.X) (hx : (family₀.cellX x).1 = Finset.univ) :
    d ≠ Fin.castAdd (Fintype.card New₂) (family₀.e x) := fun h =>
  absurd (hd.1 (h ▸ zero_mem_scope_castAdd x hx)) (by decide)

/-- A B-face cell is the copy of its retraction. -/
theorem eq_copyB_of_B {d : Cell D₂} (hd : GradedLe (D₂.cell d) (({1, 2, 3} : Finset (Fin 4)), 3)) :
    d = copyB (retB d) := by
  have := retB_inj zero_not_mem_B ⟨copyB (retB d), copyB_mem _⟩ ⟨d, hd⟩ (retB_copyB _)
  exact (congrArg Subtype.val this).symm

theorem embX₀_eq_H₀X {x : family₀.X} (h : embX₀ x = H₀X) : x = H₀X₀ := by
  rcases x with c | H | s | a
  · cases h
  · exact eq_H₀X₀ H
  · cases h
  · rcases a₀_cases a with ha | ha
    · rw [ha] at h; cases h
    · rw [ha] at h; cases h
theorem embX₀_eq_s₀X {x : family₀.X} (h : embX₀ x = s₀X) : x = s₀X₀ := by
  rcases x with c | H | s | a
  · cases h
  · cases h
  · exact eq_s₀X₀ s
  · rcases a₀_cases a with ha | ha
    · rw [ha] at h; cases h
    · rw [ha] at h; cases h
theorem embX₁_eq_H₀X {x : family₁.X} (h : embX₁ x = H₀X) : x = H₀X₁ := by
  rcases img_cases x with ⟨c, rfl⟩ | rfl | rfl | rfl
  · cases h
  · rfl
  · cases h
  · cases h
theorem embX₁_eq_s₀X {x : family₁.X} (h : embX₁ x = s₀X) : x = s₀X₁ := by
  rcases img_cases x with ⟨c, rfl⟩ | rfl | rfl | rfl
  · cases h
  · cases h
  · rfl
  · cases h

/-- **The cells retracting to the level-one witness.** -/
theorem ret_H₀_cases {d : Cell D₂} (hd : ¬ mute₂ d) (h : ret₂ d = family₂.e H₀X) :
    d = H₀old ∨ d = H₀new ∨ d = U_H := by
  rcases cell_cases d hd with ⟨i, rfl⟩ | hB | rfl | rfl | rfl | rfl | rfl
  · left
    rw [ret₂_castAdd] at h
    have h1 : family₀.e.symm i = H₀X₀ := embX₀_eq_H₀X (family₂.e.injective h)
    unfold H₀old; rw [← h1, Equiv.apply_symm_apply]
  · right; left
    rw [ret₂_eq_emb₁_retB zero_not_mem_B ⟨d, hB⟩] at h
    have h1 : family₁.e.symm (retB d) = H₀X₁ := embX₁_eq_H₀X (family₂.e.injective h)
    rw [eq_copyB_of_B hB]; unfold H₀new; rw [← h1, Equiv.apply_symm_apply]
  · right; right; rfl
  · exfalso; rw [ret₂_U_S] at h; cases family₂.e.injective h
  · exfalso; rw [ret₂_A₁c] at h; cases family₂.e.injective h
  · exfalso; rw [ret₂_A₂c] at h; cases family₂.e.injective h
  · exfalso; rw [ret₂_ub₁] at h; cases family₂.e.injective h

/-- **The cells retracting to the level-two witness.** -/
theorem ret_s₀_cases {d : Cell D₂} (hd : ¬ mute₂ d) (h : ret₂ d = family₂.e s₀X) :
    d = s₀old ∨ d = s₀new ∨ d = U_S := by
  rcases cell_cases d hd with ⟨i, rfl⟩ | hB | rfl | rfl | rfl | rfl | rfl
  · left
    rw [ret₂_castAdd] at h
    have h1 : family₀.e.symm i = s₀X₀ := embX₀_eq_s₀X (family₂.e.injective h)
    unfold s₀old; rw [← h1, Equiv.apply_symm_apply]
  · right; left
    rw [ret₂_eq_emb₁_retB zero_not_mem_B ⟨d, hB⟩] at h
    have h1 : family₁.e.symm (retB d) = s₀X₁ := embX₁_eq_s₀X (family₂.e.injective h)
    rw [eq_copyB_of_B hB]; unfold s₀new; rw [← h1, Equiv.apply_symm_apply]
  · exfalso; rw [ret₂_U_H] at h; cases family₂.e.injective h
  · right; right; rfl
  · exfalso; rw [ret₂_A₁c] at h; cases family₂.e.injective h
  · exfalso; rw [ret₂_A₂c] at h; cases family₂.e.injective h
  · exfalso; rw [ret₂_ub₁] at h; cases family₂.e.injective h

/-- A cell below a cell whose retraction is proper does not retract to a full cell. -/
theorem ret_ne_full_of_below {Sig d : Cell D₂} (hSig : ¬ mute₂ Sig) (hd : ¬ mute₂ d)
    (hle : GradedLe (D₂.cell d) (D₂.cell Sig)) {c : Prop3}
    (hc : family₂.e.symm (ret₂ Sig) = .inl c) {x : family₂.X}
    (hx : (family₂.cellX x).1 = Finset.univ) : ret₂ d ≠ family₂.e x := by
  intro h
  have h1 := hscope₂ d Sig hd hSig hle.1
  rw [h, Family.scope_eq, Family.scope_eq, Equiv.symm_apply_apply, hx, hc] at h1
  exact Prop3.scope_ne_univ c (Finset.univ_subset_iff.mp h1)

end Classification

/-! ## Values of the labelling and of the rows -/

section LabelValues

theorem η₁_le_γ₁ : η₁ ≤ γ₁ := η₁_le_γ₀.trans γ₀_le_γ₁

theorem min_b₁_η₁ (y : family₂.X) : min (family₂.rowX b₁X y) η₁ = family₂.rowX a₁X y := by
  rcases y with c | H | s | a
  · rw [rowX_b₁_inl, rowX_a₁_inl]
    rcases t₀_F_cases c with h | h <;> rw [h]
    · exact min_eq_left v₀_le_η₁
    · exact min_eq_left bot_le
  · rw [eq_H₀X H, rowX_b₁_H, rowX_a₁_H]; exact min_eq_right η₁_le_γ₁
  · rw [eq_s₀X s, rowX_b₁_s, rowX_a₁_s]; exact min_eq_right η₁_le_γ₁
  · rcases a_cases a with h | h | h <;> rw [h]
    · rw [rowX_b₁_a₁, rowX_a₁_a₁]; exact min_self _
    · rw [rowX_b₁_a₂, rowX_a₁_a₂]; exact min_eq_right η₁_le_γ₀
    · rw [rowX_b₁_b₁, rowX_a₁_b₁]; exact min_eq_right η₁_le_γ₁

theorem min_b₁_γ₀ (y : family₂.X) : min (family₂.rowX b₁X y) γ₀ = family₂.rowX a₂X y := by
  rcases y with c | H | s | a
  · rw [rowX_b₁_inl, rowX_a₂_inl]; exact min_eq_left (t₀.F_le c)
  · rw [eq_H₀X H, rowX_b₁_H, rowX_a₂_H]; exact min_eq_right γ₀_le_γ₁
  · rw [eq_s₀X s, rowX_b₁_s, rowX_a₂_s]; exact min_eq_right γ₀_le_γ₁
  · rcases a_cases a with h | h | h <;> rw [h]
    · rw [rowX_b₁_a₁, rowX_a₂_a₁]; exact min_eq_left η₁_le_γ₀
    · rw [rowX_b₁_a₂, rowX_a₂_a₂]; exact min_self _
    · rw [rowX_b₁_b₁, rowX_a₂_b₁]; exact min_eq_right γ₀_le_γ₁

theorem rowX_s₀_le (y : family₂.X) : family₂.rowX s₀X y ≤ s₀c.γ := by
  rcases y with c | H | s | a
  · exact s₀c.F_le c
  · rw [eq_H₀X H, rowX_s₀_H]
  · rw [eq_s₀X s, rowX_s₀_s]
  · exact (meet₂_le st₀ _ _).trans (min_le_left _ _)

theorem s₀c_γ_le_γ₁ : s₀c.γ ≤ γ₁ := by
  rw [s₀c_γ_num]; exact ofOrd_le_ofOrd.mpr (add_le_add_right (Nat.cast_le.mpr (by decide)) _)
theorem γ₀_le_s₀c_γ : γ₀ ≤ s₀c.γ := by
  rw [s₀c_γ_num, γ₀_num]
  exact ofOrd_le_ofOrd.mpr ((add_le_add_right (Ordinal.natCast_lt_omega0 4).le _).trans
    (by rw [← mul_add_one]; exact le_self_add))
theorem γ₀_le_H₀c_δ : γ₀ ≤ H₀c.δ := by
  rw [H₀c_δ_num, γ₀_num]
  exact ofOrd_le_ofOrd.mpr ((add_le_add_right (Ordinal.natCast_lt_omega0 4).le _).trans
    (by rw [← mul_add_one]; exact le_self_add))

theorem labelQ_le_γ₁ (d : Cell D₂) : labelQ d ≤ γ₁ := by
  by_cases hd : mute₂ d
  · rw [labelQ_of_mute hd]; exact bot_le
  · rw [labelQ_eq_rowX hd]; exact rowX_b₁_le _

theorem not_mute_H₀old : ¬ mute₂ H₀old := not_mute₂_castAdd _
theorem not_mute_s₀old : ¬ mute₂ s₀old := not_mute₂_castAdd _

theorem labelQ_H₀old : labelQ H₀old = γ₁ := by
  rw [labelQ_eq_pull, pull_of_not_mute _ not_mute_H₀old, ret₂_H₀old, Equiv.symm_apply_apply]
  exact rowX_b₁_H
theorem labelQ_s₀old : labelQ s₀old = γ₁ := by
  rw [labelQ_eq_pull, pull_of_not_mute _ not_mute_s₀old, ret₂_s₀old, Equiv.symm_apply_apply]
  exact rowX_b₁_s
theorem labelQ_fullCell (x : family₂.X) (hx : (family₂.cellX x).1 = Finset.univ)
    (h4 : (family₂.cellX x).2 ≠ 4) : labelQ (fullCell x hx) = family₂.rowX b₁X x := by
  rw [labelQ_eq_pull, pull_of_not_mute _ (not_mute_fullCell x hx h4), ret₂_fullCell,
    Equiv.symm_apply_apply]

theorem qL_of_ne {d : Cell D₂} (h : ¬ (d = H₀old ∨ d = s₀old)) : qL d = labelQ d := by
  unfold qL; rw [ite_eq_right h]
theorem qL_H₀old : qL H₀old = γ₀ := by unfold qL; rw [ite_eq_left (Or.inl rfl)]
theorem qL_s₀old : qL s₀old = γ₀ := by unfold qL; rw [ite_eq_left (Or.inr rfl)]
theorem qL_le_γ₁ (d : Cell D₂) : qL d ≤ γ₁ := by
  unfold qL; split_ifs
  · exact γ₀_le_γ₁
  · exact labelQ_le_γ₁ d
theorem qL_le_labelQ (d : Cell D₂) : qL d ≤ labelQ d := by
  unfold qL; split_ifs with h
  · rcases h with rfl | rfl
    · rw [labelQ_H₀old]; exact γ₀_le_γ₁
    · rw [labelQ_s₀old]; exact γ₀_le_γ₁
  · exact le_rfl

theorem fullCell_ne_old (x : family₂.X) (hx : (family₂.cellX x).1 = Finset.univ) :
    ¬ (fullCell x hx = H₀old ∨ fullCell x hx = s₀old) := by
  rintro (h | h)
  · exact castAdd_ne_fullCell _ x hx h.symm
  · exact castAdd_ne_fullCell _ x hx h.symm

theorem qL_fullCell (x : family₂.X) (hx : (family₂.cellX x).1 = Finset.univ)
    (h4 : (family₂.cellX x).2 ≠ 4) : qL (fullCell x hx) = family₂.rowX b₁X x := by
  rw [qL_of_ne (fullCell_ne_old x hx), labelQ_fullCell x hx h4]
theorem qL_U_H : qL U_H = γ₁ := (qL_fullCell H₀X rfl (by decide)).trans rowX_b₁_H
theorem qL_U_S : qL U_S = γ₁ := (qL_fullCell s₀X rfl (by decide)).trans rowX_b₁_s
theorem qL_A₁c : qL A₁c = η₁ := (qL_fullCell a₁X rfl (by decide)).trans rowX_b₁_a₁
theorem qL_A₂c : qL A₂c = γ₀ := (qL_fullCell a₂X rfl (by decide)).trans rowX_b₁_a₂
theorem qL_ub₁ : qL ub₁ = γ₁ := (qL_fullCell b₁X rfl (by decide)).trans rowX_b₁_b₁

/-- On the B face the labelling is input B's row. -/
theorem qL_of_B {d : Cell D₂} (hd : GradedLe (D₂.cell d) (({1, 2, 3} : Finset (Fin 4)), 3)) :
    qL d = labelQ d := by
  apply qL_of_ne
  rintro (h | h)
  · exact B_face_ne_old hd H₀X₀ rfl h
  · exact B_face_ne_old hd s₀X₀ rfl h

/-- **On the A face the labelling is the row of input A's cap `a₂`** (input A's specified
labelling). -/
theorem qL_castAdd (i : Cell C₀) :
    qL (Fin.castAdd (Fintype.card New₂) i) = pull a₂X (Fin.castAdd (Fintype.card New₂) i) := by
  rw [pull_of_not_mute _ (not_mute₂_castAdd i), ret₂_castAdd]
  change _ = family₂.rowX a₂X (family₂.e.symm (family₂.e (embX₀ (family₀.e.symm i))))
  rw [Equiv.symm_apply_apply]
  unfold qL
  split_ifs with h
  · rcases h with h | h
    · have h1 := congrArg ret₂ h
      rw [ret₂_castAdd, ret₂_H₀old] at h1
      have h2 : embX₀ (family₀.e.symm i) = H₀X := family₂.e.injective h1
      rw [h2]; exact rowX_a₂_H.symm
    · have h1 := congrArg ret₂ h
      rw [ret₂_castAdd, ret₂_s₀old] at h1
      have h2 : embX₀ (family₀.e.symm i) = s₀X := family₂.e.injective h1
      rw [h2]; exact rowX_a₂_s.symm
  · refine (labelQ_castAdd i).trans ?_
    change family₂.rowX b₁X (embX₀ (family₀.e.symm i)) = _
    rcases hw : family₀.e.symm i with c | H | s | a
    · rw [show embX₀ (.inl c) = .inl c from rfl, rowX_b₁_inl, rowX_a₂_inl]
    · exfalso; apply h; left
      unfold H₀old; rw [← Equiv.apply_symm_apply family₀.e i, hw, eq_H₀X₀]
    · exfalso; apply h; right
      unfold s₀old; rw [← Equiv.apply_symm_apply family₀.e i, hw, eq_s₀X₀]
    · rcases a₀_cases a with ha | ha <;> rw [ha]
      · rw [rowX_b₁_a₁, rowX_a₂_a₁]
      · rw [rowX_b₁_a₂, rowX_a₂_a₂]

end LabelValues

/-! ## Row values at the modified controllers -/

section RowValues

abbrev ω1j (j : ℕ) : Ordinal.{0} := Ordinal.omega0 * ((1 : ℕ) : Ordinal) + ((j : ℕ) : Ordinal)

theorem ω1j_lt_ω2 (a b : ℕ) : ω1j a < ω2 b :=
  calc ω1j a < Ordinal.omega0 * ((1 : ℕ) : Ordinal) + Ordinal.omega0 :=
        add_lt_add_right (Ordinal.natCast_lt_omega0 a) _
    _ = Ordinal.omega0 * ((2 : ℕ) : Ordinal) := by rw [← mul_add_one]; rfl
    _ ≤ ω2 b := le_self_add
theorem ω2_lt_ω2 {a b : ℕ} (h : a < b) : ω2 a < ω2 b := add_lt_add_right (Nat.cast_lt.mpr h) _
theorem ω2_le_ω2 {a b : ℕ} (h : a ≤ b) : ω2 a ≤ ω2 b := add_le_add_right (Nat.cast_le.mpr h) _
theorem fp_ω1j (j : ℕ) : finitePart (ω1j j) = j := finitePart_mul_add _ _
theorem fp_ω2 (j : ℕ) : finitePart (ω2 j) = j := finitePart_mul_add _ _
theorem v₀_num : v₀ = ofOrd (ω1j 1) := rfl
theorem η₁_num : η₁ = ofOrd (ω1j 3) := rfl
theorem γ₀_num' : γ₀ = ofOrd (ω1j 4) := rfl

theorem gTop_bot {K k : ℕ} (h : K < k) : gTop K k = ⊥ := gTop_of_gt h

/-! ### Cases below the controllers -/

theorem ne_of_ret_ne {d d' : Cell D₂} (h : ret₂ d ≠ ret₂ d') : d ≠ d' := fun e => h (congrArg _ e)

theorem ret_H₀_ne_s₀ : family₂.e H₀X ≠ family₂.e s₀X := fun h =>
  Sum.inl_ne_inr (Sum.inr.inj (family₂.e.injective h))
theorem ret_s₀_ne_H₀ : family₂.e s₀X ≠ family₂.e H₀X := fun h =>
  Sum.inr_ne_inl (Sum.inr.inj (family₂.e.injective h))

theorem s₀old_ne_H₀old : s₀old ≠ H₀old :=
  ne_of_ret_ne (by rw [ret₂_s₀old, ret₂_H₀old]; exact ret_s₀_ne_H₀)

/-- The cells below `U_H`: the old witness, the two new occurrences, or a proper cell of grade
one. -/
theorem vU_cases (d : Cell D₂) (hd : ¬ mute₂ d) (hg : D₂.grade d ≤ 1) :
    d = H₀old ∨ (ret₂ d = family₂.e H₀X ∧ d ≠ H₀old) ∨
    ∃ c : Prop3, c.gradeP ≤ 1 ∧ family₂.e.symm (ret₂ d) = .inl c := by
  by_cases h : ret₂ d = family₂.e H₀X
  · by_cases h' : d = H₀old
    · exact Or.inl h'
    · exact Or.inr (Or.inl ⟨h, h'⟩)
  · right; right
    rcases hw : family₂.e.symm (ret₂ d) with c | H | s | a
    · refine ⟨c, ?_, rfl⟩
      rw [grade_ret_eq hd, hw] at hg; exact hg
    · exfalso; apply h
      rw [← Equiv.apply_symm_apply family₂.e (ret₂ d), hw, eq_H₀X]
    · exfalso; rw [grade_ret_eq hd, hw] at hg; change (2 : ℕ) ≤ 1 at hg; omega
    · exfalso; rw [grade_ret_eq hd, hw] at hg; change (3 : ℕ) ≤ 1 at hg; omega

/-- The cells below `U_S`. -/
theorem vS_cases (d : Cell D₂) (hd : ¬ mute₂ d) (hg : D₂.grade d ≤ 2) :
    d = H₀old ∨ d = s₀old ∨
    ((ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X) ∧ ¬ (d = H₀old ∨ d = s₀old)) ∨
    ∃ c : Prop3, family₂.e.symm (ret₂ d) = .inl c := by
  by_cases h : ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X
  · by_cases h' : d = H₀old ∨ d = s₀old
    · rcases h' with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl ⟨h, h'⟩))
  · right; right; right
    rcases hw : family₂.e.symm (ret₂ d) with c | H | s | a
    · exact ⟨c, rfl⟩
    · exfalso; apply h; left
      rw [← Equiv.apply_symm_apply family₂.e (ret₂ d), hw, eq_H₀X]
    · exfalso; apply h; right
      rw [← Equiv.apply_symm_apply family₂.e (ret₂ d), hw, eq_s₀X]
    · exfalso; rw [grade_ret_eq hd, hw] at hg; change (3 : ℕ) ≤ 2 at hg; omega

theorem ret_ne_of_inl' {d : Cell D₂} {c : Prop3} (hc : family₂.e.symm (ret₂ d) = .inl c)
    {x : family₂.X} (hx : (family₂.cellX x).1 = Finset.univ) : ret₂ d ≠ family₂.e x := by
  intro h
  rw [h, Equiv.symm_apply_apply] at hc
  rw [hc] at hx
  exact Prop3.scope_ne_univ c hx

/-! ### Values of the labelling -/

theorem qL_of_ret_H₀ {d : Cell D₂} (hd : ¬ mute₂ d) (h : ret₂ d = family₂.e H₀X)
    (hne : d ≠ H₀old) : qL d = γ₁ := by
  have hnot : ¬ (d = H₀old ∨ d = s₀old) := by
    rintro (h' | h')
    · exact hne h'
    · rw [h', ret₂_s₀old] at h; exact ret_s₀_ne_H₀ h
  rw [qL_of_ne hnot, labelQ_eq_pull, pull_of_not_mute _ hd, h, Equiv.symm_apply_apply]
  exact rowX_b₁_H
theorem qL_of_ret_s₀ {d : Cell D₂} (hd : ¬ mute₂ d) (h : ret₂ d = family₂.e s₀X)
    (hne : d ≠ s₀old) : qL d = γ₁ := by
  have hnot : ¬ (d = H₀old ∨ d = s₀old) := by
    rintro (h' | h')
    · rw [h', ret₂_H₀old] at h; exact ret_H₀_ne_s₀ h
    · exact hne h'
  rw [qL_of_ne hnot, labelQ_eq_pull, pull_of_not_mute _ hd, h, Equiv.symm_apply_apply]
  exact rowX_b₁_s
theorem qL_of_proper {d : Cell D₂} (hd : ¬ mute₂ d) {c : Prop3}
    (hc : family₂.e.symm (ret₂ d) = .inl c) : qL d = t₀.F c := by
  rw [qL_of_ne (by
      rintro (h' | h')
      · rw [h', ret₂_H₀old, Equiv.symm_apply_apply] at hc; cases hc
      · rw [h', ret₂_s₀old, Equiv.symm_apply_apply] at hc; cases hc),
    labelQ_eq_pull, pull_of_not_mute _ hd, hc]
  exact rowX_b₁_inl c

/-! ### Values of the grade-one row -/

theorem vU_of_new {d : Cell D₂} (h : ret₂ d = family₂.e H₀X ∧ d ≠ H₀old) : vU d = wSep := by
  unfold vU; rw [ite_eq_left h]
theorem vU_of_not_new {d : Cell D₂} (h : ¬ (ret₂ d = family₂.e H₀X ∧ d ≠ H₀old)) :
    vU d = pull H₀X d := by
  unfold vU; rw [ite_eq_right h]
theorem vU_H₀old : vU H₀old = H₀c.δ := by
  rw [vU_of_not_new (by rintro ⟨-, h⟩; exact h rfl), pull_of_not_mute _ not_mute_H₀old, ret₂_H₀old,
    Equiv.symm_apply_apply]
  exact rowX_H₀X_H₀X
theorem vU_of_proper {d : Cell D₂} (hd : ¬ mute₂ d) {c : Prop3} (hc1 : c.gradeP ≤ 1)
    (hc : family₂.e.symm (ret₂ d) = .inl c) : vU d = v₀ := by
  rw [vU_of_not_new (fun h => ret_ne_of_inl' hc rfl h.1), pull_of_not_mute _ hd, hc,
    family₂.rowX_H_inl _ c hc1]
  exact H₀c_G_v₀ hc1
theorem rows₂_U_H_eq' (d : D₂.below (D₂.cell U_H)) : rows₂.E U_H d = pull H₀X d.1 := by
  rw [rows₂_E_eq_pull not_mute_U_H, ret₂_U_H, Equiv.symm_apply_apply]
theorem vU_eq_rows₂ (d : D₂.below (D₂.cell U_H)) (h : ¬ (ret₂ d.1 = family₂.e H₀X ∧ d.1 ≠ H₀old)) :
    vU d.1 = rows₂.E U_H d := by
  rw [vU_of_not_new h, rows₂_U_H_eq']
theorem rows₂_le_vU (d : D₂.below (D₂.cell U_H)) : rows₂.E U_H d ≤ vU d.1 := by
  by_cases h : ret₂ d.1 = family₂.e H₀X ∧ d.1 ≠ H₀old
  · rw [vU_of_new h, rows₂_U_H_eq', pull_of_not_mute _ (not_mute_below_U_H d)]
    exact (rowX_H₀X_le _).trans δ_le_wSep
  · rw [vU_eq_rows₂ d h]
theorem vU_le_wSep (d : D₂.below (D₂.cell U_H)) : vU d.1 ≤ wSep := by
  by_cases h : ret₂ d.1 = family₂.e H₀X ∧ d.1 ≠ H₀old
  · rw [vU_of_new h]
  · rw [vU_of_not_new h, pull_of_not_mute _ (not_mute_below_U_H d)]
    exact (rowX_H₀X_le _).trans δ_le_wSep
theorem vU_eq_row₃ (d : D₂.below (D₂.cell U_H)) : vU d.1 = row₃ d := by
  by_cases h : d.1 = H₀new ∨ d.1 = U_H
  · rw [row₃_of_eq d h]
    apply vU_of_new
    rcases h with h | h
    · exact ⟨by rw [h]; exact ret₂_H₀new, by rw [h]; exact H₀old_ne_H₀new.symm⟩
    · exact ⟨by rw [h]; exact ret₂_U_H, by rw [h]; exact H₀old_ne_U_H.symm⟩
  · rw [row₃_of_ne d (fun h1 => h (Or.inl h1)) (fun h2 => h (Or.inr h2))]
    apply vU_eq_rows₂
    rintro ⟨h1, h2⟩
    rcases ret_H₀_cases (not_mute_below_U_H d) h1 with h3 | h3 | h3
    · exact h2 h3
    · exact h (Or.inl h3)
    · exact h (Or.inr h3)

/-! ### Values of the grade-two row -/

theorem vS_of_new {d : Cell D₂}
    (h : (ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X) ∧ ¬ (d = H₀old ∨ d = s₀old)) :
    vS d = γ₁ := by
  unfold vS; rw [ite_eq_left h]
theorem vS_of_not_new {d : Cell D₂}
    (h : ¬ ((ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X) ∧ ¬ (d = H₀old ∨ d = s₀old))) :
    vS d = pull s₀X d := by
  unfold vS; rw [ite_eq_right h]
theorem vS_H₀old : vS H₀old = s₀c.γ := by
  rw [vS_of_not_new (by rintro ⟨-, h⟩; exact h (Or.inl rfl)), pull_of_not_mute _ not_mute_H₀old,
    ret₂_H₀old, Equiv.symm_apply_apply]
  exact rowX_s₀_H
theorem vS_s₀old : vS s₀old = s₀c.γ := by
  rw [vS_of_not_new (by rintro ⟨-, h⟩; exact h (Or.inr rfl)), pull_of_not_mute _ not_mute_s₀old,
    ret₂_s₀old, Equiv.symm_apply_apply]
  exact rowX_s₀_s
theorem vS_of_proper {d : Cell D₂} (hd : ¬ mute₂ d) {c : Prop3}
    (hc : family₂.e.symm (ret₂ d) = .inl c) : vS d = s₀c.F c := by
  have hnot : ¬ ((ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X) ∧
      ¬ (d = H₀old ∨ d = s₀old)) := by
    rintro ⟨h, -⟩
    rcases h with h | h
    · exact ret_ne_of_inl' hc rfl h
    · exact ret_ne_of_inl' hc rfl h
  rw [vS_of_not_new hnot, pull_of_not_mute _ hd, hc]
  rfl
theorem rows₂_U_S_eq' (d : D₂.below (D₂.cell U_S)) : rows₂.E U_S d = pull s₀X d.1 := by
  rw [rows₂_E_eq_pull not_mute_U_S, ret₂_U_S, Equiv.symm_apply_apply]
theorem vS_eq_rows₂ (d : D₂.below (D₂.cell U_S))
    (h : ¬ ((ret₂ d.1 = family₂.e H₀X ∨ ret₂ d.1 = family₂.e s₀X) ∧
      ¬ (d.1 = H₀old ∨ d.1 = s₀old))) :
    vS d.1 = rows₂.E U_S d := by
  rw [vS_of_not_new h, rows₂_U_S_eq']
theorem pull_s₀_le (d : Cell D₂) : pull s₀X d ≤ s₀c.γ := by
  unfold pull; split_ifs
  · exact bot_le
  · exact rowX_s₀_le _
theorem rows₂_le_vS (d : D₂.below (D₂.cell U_S)) : rows₂.E U_S d ≤ vS d.1 := by
  by_cases h : (ret₂ d.1 = family₂.e H₀X ∨ ret₂ d.1 = family₂.e s₀X) ∧ ¬ (d.1 = H₀old ∨ d.1 = s₀old)
  · rw [vS_of_new h, rows₂_U_S_eq']; exact (pull_s₀_le _).trans s₀c_γ_le_γ₁
  · rw [vS_eq_rows₂ d h]
theorem vS_le_γ₁ (d : D₂.below (D₂.cell U_S)) : vS d.1 ≤ γ₁ := by
  by_cases h : (ret₂ d.1 = family₂.e H₀X ∨ ret₂ d.1 = family₂.e s₀X) ∧ ¬ (d.1 = H₀old ∨ d.1 = s₀old)
  · rw [vS_of_new h]
  · rw [vS_of_not_new h]; exact (pull_s₀_le _).trans s₀c_γ_le_γ₁

end RowValues

/-! ## The labelling respects the modified semantics -/

section Respect

/-- The A face: cells of scope inside `{0, 1, 2}`. -/
abbrev AFace (d : Cell D₂) : Prop := GradedLe (D₂.cell d) (({0, 1, 2} : Finset (Fin 4)), 3)
abbrev BFace (d : Cell D₂) : Prop := GradedLe (D₂.cell d) (({1, 2, 3} : Finset (Fin 4)), 3)

theorem scope_castAdd_sub (i : Cell C₀) :
    D₂.scope (Fin.castAdd (Fintype.card New₂) i) ⊆ ({0, 1, 2} : Finset (Fin 4)) := by
  rw [D₂_scope_castAdd]
  exact (Finset.image_subset_image (Finset.subset_univ _)).trans (by decide)
theorem aFace_castAdd (i : Cell C₀) : AFace (Fin.castAdd (Fintype.card New₂) i) :=
  ⟨scope_castAdd_sub i, by
    change D₂.grade _ ≤ 3; rw [D₂_grade_castAdd]
    exact (C₀.grade_le_card_scope i).trans ((Finset.card_le_univ _).trans (by simp))⟩
theorem aFace_of_below {Sig : Cell D₂} (h : AFace Sig) {d : Cell D₂}
    (hd : GradedLe (D₂.cell d) (D₂.cell Sig)) : AFace d := hd.trans h
theorem bFace_of_below {Sig : Cell D₂} (h : BFace Sig) {d : Cell D₂}
    (hd : GradedLe (D₂.cell d) (D₂.cell Sig)) : BFace d := hd.trans h
theorem exists_castAdd_of_A {d : Cell D₂} (h : AFace d) :
    ∃ i, Fin.castAdd (Fintype.card New₂) i = d :=
  old_of_A (sub_castSucc_of_not_last _ A_face_mem three_not_mem_A) ⟨d, h⟩
theorem aFace_ne_fullCell {d : Cell D₂} (h : AFace d) (x : family₂.X)
    (hx : (family₂.cellX x).1 = Finset.univ) : d ≠ fullCell x hx := by
  obtain ⟨i, rfl⟩ := exists_castAdd_of_A h
  exact castAdd_ne_fullCell i x hx
theorem qL_of_A {d : Cell D₂} (h : AFace d) : qL d = pull a₂X d := by
  obtain ⟨i, rfl⟩ := exists_castAdd_of_A h
  exact qL_castAdd i
theorem cell_a₂old : D₂.cell a₂old = (({0, 1, 2} : Finset (Fin 4)), 3) := by
  unfold a₂old; rw [cell_castAdd_X]
  exact Prod.ext (by decide) rfl
theorem not_mute_a₂old : ¬ mute₂ a₂old := not_mute₂_castAdd _
theorem rows₂_a₂old_eq (d : D₂.below (D₂.cell a₂old)) : rows₂.E a₂old d = pull a₂X d.1 := by
  rw [rows₂_E_eq_pull not_mute_a₂old, ret₂_a₂old, Equiv.symm_apply_apply]
theorem rows₂_ub₁_eq (d : D₂.below (D₂.cell ub₁)) : rows₂.E ub₁ d = labelQ d.1 := rows₂_ub₁ d

/-- Rows at face cells are unchanged. -/
theorem E₃_of_A {Sig : Cell D₂} (h : AFace Sig) (d : D₂.below (D₂.cell Sig)) :
    rows₃.E Sig d = rows₂.E Sig d :=
  E₃_of_ne (aFace_ne_fullCell h H₀X rfl) (aFace_ne_fullCell h s₀X rfl)
    (aFace_ne_fullCell h b₁X rfl) d
theorem E₃_of_B {Sig : Cell D₂} (h : BFace Sig) (d : D₂.below (D₂.cell Sig)) :
    rows₃.E Sig d = rows₂.E Sig d :=
  E₃_of_ne (B_face_ne_fullCell h H₀X rfl) (B_face_ne_fullCell h s₀X rfl)
    (B_face_ne_fullCell h b₁X rfl) d
theorem A₁c_ne_ub₁ : A₁c ≠ ub₁ :=
  ne_of_ret_ne (by
    rw [ret₂_A₁c, ret₂_ub₁]; intro h
    exact a₁_ne_b₁ (congrArg Subtype.val
      (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (family₂.e.injective h)))))) 
theorem A₂c_ne_ub₁ : A₂c ≠ ub₁ :=
  ne_of_ret_ne (by
    rw [ret₂_A₂c, ret₂_ub₁]; intro h
    exact a₂_ne_b₁ (congrArg Subtype.val
      (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (family₂.e.injective h))))))
theorem A₁c_ne_U_H : A₁c ≠ U_H := ne_of_cell_ne fun h => by
  rw [cell_A₁c, cell_U_H] at h; exact absurd (congrArg Prod.snd h) (by decide)
theorem A₁c_ne_U_S : A₁c ≠ U_S := ne_of_cell_ne fun h => by
  rw [cell_A₁c, cell_U_S] at h; exact absurd (congrArg Prod.snd h) (by decide)
theorem A₂c_ne_U_H : A₂c ≠ U_H := ne_of_cell_ne fun h => by
  rw [cell_A₂c, cell_U_H] at h; exact absurd (congrArg Prod.snd h) (by decide)
theorem A₂c_ne_U_S : A₂c ≠ U_S := ne_of_cell_ne fun h => by
  rw [cell_A₂c, cell_U_S] at h; exact absurd (congrArg Prod.snd h) (by decide)
theorem E₃_A₁c (d : D₂.below (D₂.cell A₁c)) : rows₃.E A₁c d = pull a₁X d.1 := by
  rw [rows₃_E, E₃_of_ne A₁c_ne_U_H A₁c_ne_U_S A₁c_ne_ub₁, rows₂_E_eq_pull not_mute_A₁c, ret₂_A₁c,
    Equiv.symm_apply_apply]
theorem E₃_A₂c (d : D₂.below (D₂.cell A₂c)) : rows₃.E A₂c d = pull a₂X d.1 := by
  rw [rows₃_E, E₃_of_ne A₂c_ne_U_H A₂c_ne_U_S A₂c_ne_ub₁, rows₂_E_eq_pull not_mute_A₂c, ret₂_A₂c,
    Equiv.symm_apply_apply]

theorem min_qL_η₁ {d : Cell D₂} (hd : ¬ mute₂ d) : min (qL d) η₁ = pull a₁X d := by
  rw [pull_of_not_mute _ hd]
  by_cases h : d = H₀old ∨ d = s₀old
  · unfold qL; rw [ite_eq_left h]
    rcases h with rfl | rfl
    · rw [ret₂_H₀old, Equiv.symm_apply_apply, rowX_a₁_H]; exact min_eq_right η₁_le_γ₀
    · rw [ret₂_s₀old, Equiv.symm_apply_apply, rowX_a₁_s]; exact min_eq_right η₁_le_γ₀
  · rw [qL_of_ne h, labelQ_eq_pull, pull_of_not_mute _ hd]; exact min_b₁_η₁ _
theorem min_qL_γ₀ {d : Cell D₂} (hd : ¬ mute₂ d) : min (qL d) γ₀ = pull a₂X d := by
  rw [pull_of_not_mute _ hd]
  by_cases h : d = H₀old ∨ d = s₀old
  · unfold qL; rw [ite_eq_left h]
    rcases h with rfl | rfl
    · rw [ret₂_H₀old, Equiv.symm_apply_apply, rowX_a₂_H]; exact min_self _
    · rw [ret₂_s₀old, Equiv.symm_apply_apply, rowX_a₂_s]; exact min_self _
  · rw [qL_of_ne h, labelQ_eq_pull, pull_of_not_mute _ hd]; exact min_b₁_γ₀ _

/-- **The clamp witness at the grade-one controller.** -/
theorem witness_qU : Witness (gTop 1) (clampShifter γ₀ (ω2 2) γ₁) :=
  Witness.clamp 1 (by rw [fp_ω2]; omega) (γ₀_vis.mono (by omega)) (γ₁_vis.mono (by omega))
    γ₀_le_γ₁ (ofOrd_ne_bot _) (ofOrd_ne_bot _)
/-- **The clamp witness at the grade-two controller.** -/
theorem witness_qS : Witness (gTop 2) (clampShifter γ₀ (ω2 3) γ₁) :=
  Witness.clamp 2 (by rw [fp_ω2]; omega) (γ₀_vis.mono (by omega)) (γ₁_vis.mono (by omega))
    γ₀_le_γ₁ (ofOrd_ne_bot _) (ofOrd_ne_bot _)

theorem clamp_γ₀_of_between {a : ExtOrd} {ξ : ℕ} (h1 : γ₀ ≤ a) (h2 : a < ofOrd (ω2 ξ)) :
    clampShifter γ₀ (ω2 ξ) γ₁ a = γ₀ := by
  rw [clampShifter_of_lt h2]; exact min_eq_right h1
theorem clamp_of_le_γ₀ {a : ExtOrd} {ξ : ℕ} (h1 : a ≤ γ₀) (h2 : a < ofOrd (ω2 ξ)) :
    clampShifter γ₀ (ω2 ξ) γ₁ a = a := by
  rw [clampShifter_of_lt h2]; exact min_eq_left h1
theorem v₀_lt_ω2 (j : ℕ) : v₀ < ofOrd (ω2 j) := ofOrd_lt_ofOrd.mpr (ω1j_lt_ω2 _ _)

/-- **The locality of the labelling at the grade-one controller.** -/
theorem qL_locality_U_H (hx : GradedLe (D₂.cell U_H) (Finset.univ, 3)) :
    TransformsTo (fun d : D₂.below (D₂.cell U_H) => D₂.grade d.1) (rows₃.E U_H)
      (fun d => min (qL (CellScheme.below.incl ⟨U_H, hx⟩ d).1) (qL U_H)) := by
  refine witness_qU.transformsTo fun d => ?_
  change min (qL d.1) (qL U_H) = _
  rw [rows₃_E, E₃_U_H, qL_U_H, gTop_of_le (K := 1) (k := D₂.grade d.1) (below_U_H_mem d).2,
    min_eq_left le_top]
  have hd := not_mute_below_U_H d
  rcases vU_cases d.1 hd (below_U_H_mem d).2 with h | h | ⟨c, hc1, hc⟩
  · rw [h, vU_H₀old, qL_H₀old, min_eq_left γ₀_le_γ₁, H₀c_δ_num,
      clamp_γ₀_of_between (H₀c_δ_num ▸ γ₀_le_H₀c_δ) (ofOrd_lt_ofOrd.mpr (ω2_lt_ω2 (by decide)))]
  · rw [vU_of_new h, qL_of_ret_H₀ hd h.1 h.2, min_self, wSep_num, clampShifter_of_ge le_rfl]
  · rw [vU_of_proper hd hc1 hc, qL_of_proper hd hc, t₀_F_v₀ hc1,
      min_eq_left (v₀_le_γ₀.trans γ₀_le_γ₁),
      clamp_of_le_γ₀ v₀_le_γ₀ (v₀_lt_ω2 2)]

/-- **The locality of the labelling at the grade-two controller.** -/
theorem qL_locality_U_S (hx : GradedLe (D₂.cell U_S) (Finset.univ, 3)) :
    TransformsTo (fun d : D₂.below (D₂.cell U_S) => D₂.grade d.1) (rows₃.E U_S)
      (fun d => min (qL (CellScheme.below.incl ⟨U_S, hx⟩ d).1) (qL U_S)) := by
  refine witness_qS.transformsTo fun d => ?_
  change min (qL d.1) (qL U_S) = _
  rw [rows₃_E, E₃_U_S, qL_U_S, gTop_of_le (K := 2) (k := D₂.grade d.1) (below_U_S_mem d).2,
    min_eq_left le_top]
  have hd := not_mute_below_U_S d
  have hγ : s₀c.γ < ofOrd (ω2 3) := by
    rw [s₀c_γ_num]; exact ofOrd_lt_ofOrd.mpr (ω2_lt_ω2 (by decide))
  rcases vS_cases d.1 hd (below_U_S_mem d).2 with h | h | h | ⟨c, hc⟩
  · rw [h, vS_H₀old, qL_H₀old, min_eq_left γ₀_le_γ₁, clamp_γ₀_of_between γ₀_le_s₀c_γ hγ]
  · rw [h, vS_s₀old, qL_s₀old, min_eq_left γ₀_le_γ₁, clamp_γ₀_of_between γ₀_le_s₀c_γ hγ]
  · rw [vS_of_new h, clampShifter_of_ge (a := γ₁) (le_of_eq γ₁_num.symm)]
    rcases h.1 with h1 | h1
    · rw [qL_of_ret_H₀ hd h1 (fun e => h.2 (Or.inl e)), min_self]
    · rw [qL_of_ret_s₀ hd h1 (fun e => h.2 (Or.inr e)), min_self]
  · rw [vS_of_proper hd hc, qL_of_proper hd hc]
    by_cases hc1 : c.gradeP ≤ 1
    · rw [s₀c_F_v₀ hc1, t₀_F_v₀ hc1, min_eq_left (v₀_le_γ₀.trans γ₀_le_γ₁),
        clamp_of_le_γ₀ v₀_le_γ₀ (v₀_lt_ω2 3)]
    · have hc2 : c.gradeP = 2 := by have := c.gradeP_le_two; omega
      rw [s₀c_F_bot hc2, t₀_F_bot hc2, min_eq_left bot_le, clampShifter_of_lt (bot_lt_ofOrd _),
        min_eq_left bot_le]

theorem qL_of_eq {d : Cell D₂} (h : d = H₀old ∨ d = s₀old) : qL d = γ₀ := by
  unfold qL; rw [ite_eq_left h]

/-- **The labelling respects the modified semantics on the full grade-three lower set.** -/
theorem qL_respects : RespectsSemanticsBelow rows₃ (Finset.univ, 3) (fun d => qL d.1) where
  orderly d := by
    change qL d.1 = extVisibilityReplace (qL d.1) (D₂.grade d.1) (D₂.grade d.1)
    by_cases h : d.1 = H₀old ∨ d.1 = s₀old
    · rw [qL_of_eq h]; exact (γ₀_vis.mono d.2.2).symm
    · rw [qL_of_ne h]; exact Q.respects.orderly d.1
  locality := by
    intro Sig
    obtain ⟨x, hx⟩ := Sig
    have hnm : ¬ mute₂ x := not_mute₂_of_low le_rfl ⟨x, hx⟩
    rcases cell_cases x hnm with ⟨i, rfl⟩ | hB | rfl | rfl | rfl | rfl | rfl
    · -- the A face: input A's own locality (the row of its cap)
      have hA : AFace (Fin.castAdd (Fintype.card New₂) i) := aFace_castAdd i
      have hmem : GradedLe (D₂.cell (Fin.castAdd (Fintype.card New₂) i)) (D₂.cell a₂old) := by
        rw [cell_a₂old]; exact hA
      have key := (rows₂_isConsistent a₂old).locality ⟨_, hmem⟩
      refine transformsTo_congr rfl ?_ ?_ key
      · funext d; exact (E₃_of_A hA d).symm
      · funext d
        change min (rows₂.E a₂old ⟨d.1, _⟩) (rows₂.E a₂old ⟨_, hmem⟩) = min (qL d.1) (qL _)
        erw [rows₂_a₂old_eq, rows₂_a₂old_eq]
        rw [qL_of_A hA, qL_of_A (aFace_of_below hA d.2)]
    · -- the B face: input B's own locality (the row of its cap)
      have key := (rows₂_isConsistent ub₁).locality ⟨x, below_ub₁ hnm⟩
      refine transformsTo_congr rfl ?_ ?_ key
      · funext d; exact (E₃_of_B hB d).symm
      · funext d
        change min (rows₂.E ub₁ ⟨d.1, _⟩) (rows₂.E ub₁ ⟨x, _⟩) = min (qL d.1) (qL x)
        erw [rows₂_ub₁_eq, rows₂_ub₁_eq]
        rw [qL_of_B hB, qL_of_B (bFace_of_below hB d.2)]
    · exact qL_locality_U_H hx
    · exact qL_locality_U_S hx
    · -- the copy of `a₁`: the target is the source
      refine transformsTo_congr rfl rfl ?_ (TransformsTo.refl _)
      funext d
      change rows₃.E A₁c d = min (qL d.1) (qL A₁c)
      rw [E₃_A₁c d, qL_A₁c, min_qL_η₁ (hmute_below₂ A₁c d.1 not_mute_A₁c d.2)]
    · -- the copy of `a₂`: the target is the source
      refine transformsTo_congr rfl rfl ?_ (TransformsTo.refl _)
      funext d
      change rows₃.E A₂c d = min (qL d.1) (qL A₂c)
      rw [E₃_A₂c d, qL_A₂c, min_qL_γ₀ (hmute_below₂ A₂c d.1 not_mute_A₂c d.2)]
    · -- the copy of `b₁`: its row is the labelling
      refine transformsTo_congr rfl rfl ?_ (TransformsTo.refl _)
      funext d
      change rows₃.E ub₁ d = min (qL d.1) (qL ub₁)
      rw [rows₃_E, E₃_ub₁, qL_ub₁, min_eq_left (qL_le_γ₁ _)]
  availability := by
    intro Sig Xi₀ hs hg
    obtain ⟨Xi, hcell, hle⟩ := Q.respects.availability Sig.1 Xi₀.1 hs hg
    change D₂.cell Xi = D₂.cell Xi₀.1 at hcell
    refine ⟨⟨Xi, by rw [hcell]; exact Xi₀.2⟩, hcell, ?_⟩
    change qL Sig.1 ≤ qL Xi
    by_cases hXi : Xi = H₀old ∨ Xi = s₀old
    · rw [qL_of_eq hXi]
      have hA : AFace Sig.1 := by
        refine ⟨?_, Sig.2.2⟩
        refine hs.trans ?_
        change (D₂.cell Xi₀.1).1 ⊆ _
        rw [← hcell]
        rcases hXi with rfl | rfl
        · exact scope_castAdd_sub _
        · exact scope_castAdd_sub _
      rw [qL_of_A hA, pull_of_not_mute _ (not_mute₂_of_low le_rfl Sig)]
      exact rowX_a₂_le _
    · rw [qL_of_ne hXi]
      exact (qL_le_labelQ _).trans hle

end Respect

/-! ## Consistency of the modified semantics -/

section Consistency

theorem rows₃_E_mute {Sig : Cell D₂} (h : mute₂ Sig) (d : D₂.below (D₂.cell Sig)) :
    rows₃.E Sig d = ⊥ := by
  rw [rows₃_E, E₃_of_ne (fun e => not_mute_U_H (e ▸ h)) (fun e => not_mute_U_S (e ▸ h))
    (fun e => not_mute_ub₁ (e ▸ h))]
  exact Semantics.pullback_E_of_mute h d

theorem consistent_mute {Sig : Cell D₂} (h : mute₂ Sig) :
    RespectsSemanticsBelow rows₃ (D₂.cell Sig) (rows₃.E Sig) where
  orderly := rows₃.orderly Sig
  locality Sig' := by
    refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
    funext d; rw [rows₃_E_mute h, rows₃_E_mute h, min_self]
  availability Sig' Xi₀ _ _ := ⟨Xi₀, rfl, by rw [rows₃_E_mute h, rows₃_E_mute h]⟩

theorem consistent_unchanged {Sig : Cell D₂}
    (h : ∀ Sig' : D₂.below (D₂.cell Sig), rows₃.E Sig'.1 = rows₂.E Sig'.1) :
    RespectsSemanticsBelow rows₃ (D₂.cell Sig) (rows₃.E Sig) := by
  have h0 : rows₃.E Sig = rows₂.E Sig := h ⟨Sig, GradedLe.refl _⟩
  rw [h0]
  exact (rows₂_isConsistent Sig).congr_sem h

theorem consistent_A {Sig : Cell D₂} (hA : AFace Sig) :
    RespectsSemanticsBelow rows₃ (D₂.cell Sig) (rows₃.E Sig) :=
  consistent_unchanged fun Sig' => funext (E₃_of_A (aFace_of_below hA Sig'.2))
theorem consistent_B {Sig : Cell D₂} (hB : BFace Sig) :
    RespectsSemanticsBelow rows₃ (D₂.cell Sig) (rows₃.E Sig) :=
  consistent_unchanged fun Sig' => funext (E₃_of_B (bFace_of_below hB Sig'.2))

theorem consistent_ub₁ : RespectsSemanticsBelow rows₃ (D₂.cell ub₁) (rows₃.E ub₁) := by
  rw [show rows₃.E ub₁ = fun d => qL d.1 from funext E₃_ub₁]
  exact respects_of_cell_eq cell_ub₁.symm qL_respects

/-! ### Scopes of the new occurrences -/

theorem scope_H₀new : D₂.scope H₀new = {1, 2, 3} := by
  apply fold_univ_of_B _ (D₂.scope_mem_plan _) (zero_not_mem_scope_copyB _)
  have h := cell_copyB (family₁.e H₀X₁)
  rw [Family.cell_e] at h
  exact (congrArg Prod.fst h).symm
theorem scope_s₀new : D₂.scope s₀new = {1, 2, 3} := by
  apply fold_univ_of_B _ (D₂.scope_mem_plan _) (zero_not_mem_scope_copyB _)
  have h := cell_copyB (family₁.e s₀X₁)
  rw [Family.cell_e] at h
  exact (congrArg Prod.fst h).symm
theorem scope_fullCell (x : family₂.X) (hx : (family₂.cellX x).1 = Finset.univ) :
    D₂.scope (fullCell x hx) = Finset.univ := congrArg Prod.fst (cell_fullCell x hx)
theorem bFace_H₀new : BFace H₀new := copyB_mem _
theorem bFace_s₀new : BFace s₀new := copyB_mem _

theorem eq_H₀old_of_A {d : Cell D₂} (hA : AFace d) (h : ret₂ d = family₂.e H₀X) : d = H₀old := by
  obtain ⟨i, rfl⟩ := exists_castAdd_of_A hA
  rw [ret₂_castAdd] at h
  have h1 : family₀.e.symm i = H₀X₀ := embX₀_eq_H₀X (family₂.e.injective h)
  unfold H₀old; rw [← h1, Equiv.apply_symm_apply]
theorem eq_s₀old_of_A {d : Cell D₂} (hA : AFace d) (h : ret₂ d = family₂.e s₀X) : d = s₀old := by
  obtain ⟨i, rfl⟩ := exists_castAdd_of_A hA
  rw [ret₂_castAdd] at h
  have h1 : family₀.e.symm i = s₀X₀ := embX₀_eq_s₀X (family₂.e.injective h)
  unfold s₀old; rw [← h1, Equiv.apply_symm_apply]

theorem not_new_of_A {d : Cell D₂} (hA : AFace d) : ¬ (ret₂ d = family₂.e H₀X ∧ d ≠ H₀old) :=
  fun h => h.2 (eq_H₀old_of_A hA h.1)
theorem not_newS_of_A {d : Cell D₂} (hA : AFace d) :
    ¬ ((ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X) ∧ ¬ (d = H₀old ∨ d = s₀old)) := by
  rintro ⟨h, h'⟩
  rcases h with h | h
  · exact h' (Or.inl (eq_H₀old_of_A hA h))
  · exact h' (Or.inr (eq_s₀old_of_A hA h))

/-- A cell of grade one whose scope contains the fresh face retracts to the level-one witness. -/
theorem ret_eq_H₀X_of_full {d : Cell D₂} (hd : ¬ mute₂ d)
    (h3 : ({1, 2, 3} : Finset (Fin 4)) ⊆ D₂.scope d) (hg : D₂.grade d = 1) :
    ret₂ d = family₂.e H₀X := by
  have hsc : (family₂.cellX (family₂.e.symm (ret₂ d))).1 = Finset.univ := by
    rw [← Family.scope_eq, scope_ret₂ d hd]
    apply Finset.univ_subset_iff.mp
    rw [← image_fold_one_two_three]; exact Finset.image_subset_image h3
  rw [grade_ret_eq hd] at hg
  rw [← Equiv.apply_symm_apply family₂.e (ret₂ d)]
  rcases hw : family₂.e.symm (ret₂ d) with c | H | s | a
  · exfalso; rw [hw] at hsc; exact Prop3.scope_ne_univ c hsc
  · rw [eq_H₀X H]
  · exfalso; rw [hw] at hg; change (2 : ℕ) = 1 at hg; omega
  · exfalso; rw [hw] at hg; change (3 : ℕ) = 1 at hg; omega
theorem ret_eq_s₀X_of_full {d : Cell D₂} (hd : ¬ mute₂ d)
    (h3 : ({1, 2, 3} : Finset (Fin 4)) ⊆ D₂.scope d) (hg : D₂.grade d = 2) :
    ret₂ d = family₂.e s₀X := by
  have hsc : (family₂.cellX (family₂.e.symm (ret₂ d))).1 = Finset.univ := by
    rw [← Family.scope_eq, scope_ret₂ d hd]
    apply Finset.univ_subset_iff.mp
    rw [← image_fold_one_two_three]; exact Finset.image_subset_image h3
  rw [grade_ret_eq hd] at hg
  rw [← Equiv.apply_symm_apply family₂.e (ret₂ d)]
  rcases hw : family₂.e.symm (ret₂ d) with c | H | s | a
  · exfalso; rw [hw] at hsc; exact Prop3.scope_ne_univ c hsc
  · exfalso; rw [hw] at hg; change (1 : ℕ) = 2 at hg; omega
  · rw [eq_s₀X s]
  · exfalso; rw [hw] at hg; change (3 : ℕ) = 2 at hg; omega

theorem three_mem_of_new {d : Cell D₂} (hd : ¬ mute₂ d) (h : ret₂ d = family₂.e H₀X ∧ d ≠ H₀old) :
    ({1, 2, 3} : Finset (Fin 4)) ⊆ D₂.scope d := by
  rcases ret_H₀_cases hd h.1 with h' | h' | h'
  · exact absurd h' h.2
  · rw [h', scope_H₀new]
  · rw [h']; intro i _; change i ∈ (D₂.cell U_H).1; rw [cell_U_H]; exact Finset.mem_univ i
theorem three_mem_of_newS {d : Cell D₂} (hd : ¬ mute₂ d)
    (h : (ret₂ d = family₂.e H₀X ∨ ret₂ d = family₂.e s₀X) ∧ ¬ (d = H₀old ∨ d = s₀old)) :
    ({1, 2, 3} : Finset (Fin 4)) ⊆ D₂.scope d := by
  rcases h.1 with h1 | h1
  · exact three_mem_of_new hd ⟨h1, fun e => h.2 (Or.inl e)⟩
  · rcases ret_s₀_cases hd h1 with h' | h' | h'
    · exact absurd (Or.inr h') h.2
    · rw [h', scope_s₀new]
    · rw [h']; intro i _; change i ∈ (D₂.cell U_S).1; rw [cell_U_S]; exact Finset.mem_univ i
theorem not_old_of_three {d : Cell D₂} (h : ({1, 2, 3} : Finset (Fin 4)) ⊆ D₂.scope d) :
    ¬ (d = H₀old ∨ d = s₀old) := by
  rintro (rfl | rfl)
  · exact three_not_mem_scope_castAdd _ (h (by decide))
  · exact three_not_mem_scope_castAdd _ (h (by decide))

/-! ### The grade-one controller -/

theorem ne_full_of_proper {x : Cell D₂} {c : Prop3} (hc : family₂.e.symm (ret₂ x) = .inl c)
    (y : family₂.X) (hy : (family₂.cellX y).1 = Finset.univ) : x ≠ fullCell y hy :=
  ne_of_ret_ne (by rw [ret₂_fullCell]; exact ret_ne_of_inl' hc hy)
theorem E₃_of_proper {x : Cell D₂} {c : Prop3} (hc : family₂.e.symm (ret₂ x) = .inl c)
    (d : D₂.below (D₂.cell x)) : rows₃.E x d = rows₂.E x d :=
  E₃_of_ne (ne_full_of_proper hc H₀X rfl) (ne_full_of_proper hc s₀X rfl)
    (ne_full_of_proper hc b₁X rfl) d

theorem consistent_U_H : RespectsSemanticsBelow rows₃ (D₂.cell U_H) (rows₃.E U_H) := by
  rw [show rows₃.E U_H = fun d => vU d.1 from funext E₃_U_H]
  refine ⟨fun d => (vU_selfVis d).symm, ?_, ?_⟩
  · intro Sig'
    obtain ⟨x, hx⟩ := Sig'
    have hnm := not_mute_below_U_H ⟨x, hx⟩
    rcases vU_cases x hnm (below_U_H_mem ⟨x, hx⟩).2 with rfl | ⟨h1, h2⟩ | ⟨c, -, hc⟩
    · have key := (rows₂_isConsistent U_H).locality ⟨H₀old, hx⟩
      refine transformsTo_congr rfl ?_ ?_ key
      · funext d; exact (E₃_of_A (aFace_castAdd _) d).symm
      · funext d
        rw [vU_eq_rows₂ (CellScheme.below.incl ⟨H₀old, hx⟩ d)
            (not_new_of_A (aFace_of_below (aFace_castAdd _) d.2)),
          vU_eq_rows₂ ⟨H₀old, hx⟩ (not_new_of_A (aFace_castAdd _))]
    · rcases ret_H₀_cases hnm h1 with rfl | rfl | rfl
      · exact absurd rfl h2
      · have key := locality_H₀new
        refine transformsTo_congr rfl ?_ ?_ key
        · funext d; exact (E₃_of_B bFace_H₀new d).symm
        · funext d
          rw [vU_eq_row₃ (CellScheme.below.incl ⟨H₀new, hx⟩ d), vU_eq_row₃ ⟨H₀new, hx⟩]
      · refine transformsTo_congr rfl (funext fun d => (E₃_U_H d).symm) ?_
          (TransformsTo.refl fun d : D₂.below (D₂.cell U_H) => vU d.1)
        funext d
        change vU d.1 = min (vU d.1) (vU U_H)
        rw [vU_of_new ⟨ret₂_U_H, H₀old_ne_U_H.symm⟩, min_eq_left (vU_le_wSep d)]
    · have key := (rows₂_isConsistent U_H).locality ⟨x, hx⟩
      refine transformsTo_congr rfl ?_ ?_ key
      · funext d; exact (E₃_of_proper hc d).symm
      · funext d
        rw [vU_eq_rows₂ (CellScheme.below.incl ⟨x, hx⟩ d)
            (fun h => ret_ne_full_of_below hnm (not_mute_below_U_H _) d.2 hc rfl h.1),
          vU_eq_rows₂ ⟨x, hx⟩ (fun h => ret_ne_of_inl' hc rfl h.1)]
  · intro Sig' Xi₀ hs hg
    by_cases hnew : ret₂ Sig'.1 = family₂.e H₀X ∧ Sig'.1 ≠ H₀old
    · refine ⟨Xi₀, rfl, ?_⟩
      have h3 : ({1, 2, 3} : Finset (Fin 4)) ⊆ D₂.scope Xi₀.1 :=
        (three_mem_of_new (not_mute_below_U_H Sig') hnew).trans hs
      have hg1 : D₂.grade Xi₀.1 = 1 := by
        rw [← hg]; exact grade_of_ret_H₀ (not_mute_below_U_H Sig') hnew.1
      rw [vU_of_new hnew, vU_of_new ⟨ret_eq_H₀X_of_full (not_mute_below_U_H Xi₀) h3 hg1,
        fun e => not_old_of_three h3 (Or.inl e)⟩]
    · obtain ⟨Xi, hc, hle⟩ := (rows₂_isConsistent U_H).availability Sig' Xi₀ hs hg
      refine ⟨Xi, hc, ?_⟩
      rw [vU_eq_rows₂ Sig' hnew]
      exact hle.trans (rows₂_le_vU Xi)

/-! ### The grade-two controller -/

theorem witness_raise2 :
    Witness (gTop 1) (raiseShifter (raiseShifter id (ω1j 2) (ofOrd (ω2 2))) (ω2 2) γ₁) :=
  ((witness_id 1).raise 1 (fun _ hk => gTop_bot hk) (by rw [fp_ω1j]; omega)
    (selfVis_ofOrd_iff.mpr (by rw [fp_ω2]; omega))).raise 1 (fun _ hk => gTop_bot hk)
    (by rw [fp_ω2]; omega) (γ₁_vis.mono (by omega))
theorem witness_raise_H : Witness (gTop 1) (raiseShifter id (ω1j 2) γ₁) :=
  (witness_id 1).raise 1 (fun _ hk => gTop_bot hk) (by rw [fp_ω1j]; omega) (γ₁_vis.mono (by omega))
theorem witness_raise_s : Witness (gTop 2) (raiseShifter id (ω1j 3) γ₁) :=
  (witness_id 2).raise 2 (fun _ hk => gTop_bot hk) (by rw [fp_ω1j]; omega) (γ₁_vis.mono (by omega))

theorem below_U_H_of_U_S (d : D₂.below (D₂.cell U_H)) : GradedLe (D₂.cell d.1) (D₂.cell U_S) := by
  rw [cell_U_S]; exact ⟨Finset.subset_univ _, (below_U_H_mem d).2.trans (by decide)⟩
theorem vS_U_H : vS U_H = γ₁ := vS_of_new ⟨Or.inl ret₂_U_H, fullCell_ne_old H₀X rfl⟩
theorem vS_H₀new : vS H₀new = γ₁ := by
  apply vS_of_new
  refine ⟨Or.inl ret₂_H₀new, ?_⟩
  rintro (h | h)
  · exact H₀old_ne_H₀new h.symm
  · exact castAdd_ne_copyB s₀X₀ rfl _ h.symm
theorem vS_s₀new : vS s₀new = γ₁ := by
  apply vS_of_new
  refine ⟨Or.inr ret₂_s₀new, ?_⟩
  rintro (h | h)
  · exact castAdd_ne_copyB H₀X₀ rfl _ h.symm
  · exact s₀old_ne_s₀new h.symm
theorem ω2_two_le_γ₁ : ofOrd (ω2 2) ≤ γ₁ := by
  rw [γ₁_num]; exact ofOrd_le_ofOrd.mpr (ω2_le_ω2 (by decide))
theorem ω2_one_le_γ₁ : ofOrd (ω2 1) ≤ γ₁ := by
  rw [γ₁_num]; exact ofOrd_le_ofOrd.mpr (ω2_le_ω2 (by decide))
theorem vS_of_newH {d : Cell D₂} (h : ret₂ d = family₂.e H₀X ∧ d ≠ H₀old) : vS d = γ₁ :=
  vS_of_new ⟨Or.inl h.1, by
    rintro (e | e)
    · exact h.2 e
    · rw [e, ret₂_s₀old] at h; exact ret_s₀_ne_H₀ h.1⟩

/-- The row of `U_H` transforms to the row of `U_S` (the raised value propagates). -/
theorem locality_U_S_U_H (hx : GradedLe (D₂.cell U_H) (D₂.cell U_S)) :
    TransformsTo (fun d : D₂.below (D₂.cell U_H) => D₂.grade d.1) (rows₃.E U_H)
      (fun d => min (vS (CellScheme.below.incl ⟨U_H, hx⟩ d).1) (vS U_H)) := by
  refine witness_raise2.transformsTo fun d => ?_
  change min (vS d.1) (vS U_H) = _
  have hd := not_mute_below_U_H d
  rw [rows₃_E, E₃_U_H, vS_U_H, gTop_of_le (K := 1) (k := D₂.grade d.1) (below_U_H_mem d).2,
    min_eq_left le_top]
  rcases vU_cases d.1 hd (below_U_H_mem d).2 with h | h | ⟨c, hc1, hc⟩
  · rw [h, vU_H₀old, vS_H₀old, min_eq_left s₀c_γ_le_γ₁, H₀c_δ_num, s₀c_γ_num,
      raiseShifter_of_lt (ofOrd_lt_ofOrd.mpr (ω2_lt_ω2 (by decide))),
      raiseShifter_of_ge (ofOrd_le_ofOrd.mpr (ω1j_lt_ω2 2 1).le) (ofOrd_ne_bot _)]
    change ofOrd (ω2 2) = max (ofOrd (ω2 1)) (ofOrd (ω2 2))
    rw [max_eq_right (ofOrd_le_ofOrd.mpr (ω2_le_ω2 (by decide)))]
  · rw [vU_of_new h, vS_of_newH h, min_self, wSep_num]
    have hne : raiseShifter id (ω1j 2) (ofOrd (ω2 2)) (ofOrd (ω2 2)) ≠ ⊥ := fun hb =>
      not_ofOrd_le_bot _ (hb ▸ le_raiseShifter id (ω1j 2) (ofOrd (ω2 2)) (ofOrd (ω2 2)))
    rw [raiseShifter_of_ge le_rfl hne,
      raiseShifter_of_ge (ofOrd_le_ofOrd.mpr (ω1j_lt_ω2 2 2).le) (ofOrd_ne_bot _)]
    change γ₁ = max (max (ofOrd (ω2 2)) (ofOrd (ω2 2))) γ₁
    rw [max_self, max_eq_right ω2_two_le_γ₁]
  · rw [vU_of_proper hd hc1 hc, vS_of_proper hd hc, s₀c_F_v₀ hc1,
      min_eq_left (v₀_le_γ₀.trans γ₀_le_γ₁), v₀_num,
      raiseShifter_of_lt (ofOrd_lt_ofOrd.mpr (ω1j_lt_ω2 1 2)),
      raiseShifter_of_lt (ofOrd_lt_ofOrd.mpr (add_lt_add_right (Nat.cast_lt.mpr (by decide)) _))]
    rfl

theorem rows₂_H₀new_eq' (d : D₂.below (D₂.cell H₀new)) :
    rows₂.E H₀new d = family₂.rowX H₀X (family₂.e.symm (ret₂ d.1)) := rows₂_H₀new_eq d

/-- The copy's row transforms to the row of `U_S`. -/
theorem locality_U_S_H₀new (hx : GradedLe (D₂.cell H₀new) (D₂.cell U_S)) :
    TransformsTo (fun d : D₂.below (D₂.cell H₀new) => D₂.grade d.1) (rows₃.E H₀new)
      (fun d => min (vS (CellScheme.below.incl ⟨H₀new, hx⟩ d).1) (vS H₀new)) := by
  refine witness_raise_H.transformsTo fun d => ?_
  change min (vS d.1) (vS H₀new) = _
  have hd : ¬ mute₂ d.1 := hmute_below₂ H₀new d.1 not_mute_H₀new d.2
  rw [E₃_of_B bFace_H₀new, rows₂_H₀new_eq', vS_H₀new,
    gTop_of_le (K := 1) (k := D₂.grade d.1) (below_H₀new_mem d).2, min_eq_left le_top]
  rcases below_H₀new_cases d with h | ⟨c, hc1, hc⟩
  · rw [h, ret₂_H₀new, Equiv.symm_apply_apply, rowX_H₀X_H₀X, vS_H₀new, min_self, H₀c_δ_num,
      raiseShifter_of_ge (ofOrd_le_ofOrd.mpr (ω1j_lt_ω2 2 1).le) (ofOrd_ne_bot _)]
    change γ₁ = max (ofOrd (ω2 1)) γ₁
    rw [max_eq_right ω2_one_le_γ₁]
  · rw [hc, family₂.rowX_H_inl _ c hc1, H₀c_G_v₀ hc1, vS_of_proper hd hc, s₀c_F_v₀ hc1,
      min_eq_left (v₀_le_γ₀.trans γ₀_le_γ₁), v₀_num,
      raiseShifter_of_lt (ofOrd_lt_ofOrd.mpr (add_lt_add_right (Nat.cast_lt.mpr (by decide)) _))]
    rfl

theorem below_s₀new_mem (d : D₂.below (D₂.cell s₀new)) :
    GradedLe (D₂.cell d.1) (({1, 2, 3} : Finset (Fin 4)), 2) :=
  ⟨d.2.1.trans (copyB_mem _).1, d.2.2.trans grade_s₀new.le⟩

/-- A cell below the copy of `s₀` is that copy, the copy of `H₀`, or a proper cell. -/
theorem below_s₀new_cases (d : D₂.below (D₂.cell s₀new)) :
    d.1 = s₀new ∨ d.1 = H₀new ∨ ∃ c : Prop3, family₂.e.symm (ret₂ d.1) = .inl c := by
  have hr := ret₂_eq_emb₁_retB zero_not_mem_B ⟨d.1, below_s₀new_mem d⟩
  have hcell := cell_retB zero_not_mem_B ⟨d.1, below_s₀new_mem d⟩
  have h2 : C₁.grade (retB d.1) = D₂.grade d.1 := congrArg Prod.snd hcell
  have h3 : D₂.grade d.1 ≤ 2 := (below_s₀new_mem d).2
  rcases img_cases (family₁.e.symm (retB d.1)) with ⟨c, hc⟩ | hc | hc | hc
  · right; right
    refine ⟨c, ?_⟩
    rw [hr]
    change family₂.e.symm (family₂.e (embX₁ (family₁.e.symm (retB d.1)))) = _
    rw [Equiv.symm_apply_apply, hc]; rfl
  · right; left
    have h1 : retB d.1 = family₁.e H₀X₁ := by rw [← hc, Equiv.apply_symm_apply]
    have := retB_inj zero_not_mem_B
      ⟨d.1, (below_s₀new_mem d).trans ⟨Finset.Subset.refl _, by decide⟩⟩
      ⟨H₀new, ⟨(copyB_mem _).1, grade_H₀new.le.trans (by decide)⟩⟩ (h1.trans (retB_copyB _).symm)
    exact congrArg Subtype.val this
  · left
    have h1 : retB d.1 = family₁.e s₀X₁ := by rw [← hc, Equiv.apply_symm_apply]
    have := retB_inj zero_not_mem_B
      ⟨d.1, (below_s₀new_mem d).trans ⟨Finset.Subset.refl _, by decide⟩⟩
      ⟨s₀new, ⟨(copyB_mem _).1, grade_s₀new.le.trans (by decide)⟩⟩ (h1.trans (retB_copyB _).symm)
    exact congrArg Subtype.val this
  · exfalso
    have h1 : C₁.grade (retB d.1) = 3 := by rw [Family.grade_eq, hc]; rfl
    omega

theorem rows₂_s₀new_eq (d : D₂.below (D₂.cell s₀new)) :
    rows₂.E s₀new d = family₂.rowX s₀X (family₂.e.symm (ret₂ d.1)) := by
  refine (rows₂_E_of_not_mute (not_mute_copyB _) d).trans ?_
  change family₂.rowX (family₂.e.symm (ret₂ s₀new)) (family₂.e.symm (ret₂ d.1)) = _
  rw [ret₂_s₀new, Equiv.symm_apply_apply]

/-- The copy of `s₀`'s row transforms to the row of `U_S`. -/
theorem locality_U_S_s₀new (hx : GradedLe (D₂.cell s₀new) (D₂.cell U_S)) :
    TransformsTo (fun d : D₂.below (D₂.cell s₀new) => D₂.grade d.1) (rows₃.E s₀new)
      (fun d => min (vS (CellScheme.below.incl ⟨s₀new, hx⟩ d).1) (vS s₀new)) := by
  refine witness_raise_s.transformsTo fun d => ?_
  change min (vS d.1) (vS s₀new) = _
  have hd : ¬ mute₂ d.1 := hmute_below₂ s₀new d.1 (not_mute_copyB _) d.2
  rw [E₃_of_B bFace_s₀new, rows₂_s₀new_eq, vS_s₀new,
    gTop_of_le (K := 2) (k := D₂.grade d.1) (below_s₀new_mem d).2, min_eq_left le_top]
  have hγ : ofOrd (ω1j 3) ≤ s₀c.γ := by
    rw [s₀c_γ_num]; exact (ofOrd_lt_ofOrd.mpr (ω1j_lt_ω2 3 2)).le
  rcases below_s₀new_cases d with h | h | ⟨c, hc⟩
  · rw [h, ret₂_s₀new, Equiv.symm_apply_apply, rowX_s₀_s, vS_s₀new, min_self,
      raiseShifter_of_ge hγ (s₀c_γ_num ▸ ofOrd_ne_bot _)]
    change γ₁ = max s₀c.γ γ₁
    rw [max_eq_right s₀c_γ_le_γ₁]
  · rw [h, ret₂_H₀new, Equiv.symm_apply_apply, rowX_s₀_H, vS_H₀new, min_self,
      raiseShifter_of_ge hγ (s₀c_γ_num ▸ ofOrd_ne_bot _)]
    change γ₁ = max s₀c.γ γ₁
    rw [max_eq_right s₀c_γ_le_γ₁]
  · rw [hc, rowX_s₀_inl, vS_of_proper hd hc]
    by_cases hc1 : c.gradeP ≤ 1
    · rw [s₀c_F_v₀ hc1, min_eq_left (v₀_le_γ₀.trans γ₀_le_γ₁), v₀_num,
        raiseShifter_of_lt (ofOrd_lt_ofOrd.mpr (add_lt_add_right (Nat.cast_lt.mpr (by decide)) _))]
      rfl
    · have hc2 : c.gradeP = 2 := by have := c.gradeP_le_two; omega
      rw [s₀c_F_bot hc2, min_eq_left bot_le, raiseShifter_of_bot rfl]

theorem consistent_U_S : RespectsSemanticsBelow rows₃ (D₂.cell U_S) (rows₃.E U_S) := by
  rw [show rows₃.E U_S = fun d => vS d.1 from funext E₃_U_S]
  refine ⟨fun d => (vS_selfVis d).symm, ?_, ?_⟩
  · intro Sig'
    obtain ⟨x, hx⟩ := Sig'
    have hnm := not_mute_below_U_S ⟨x, hx⟩
    rcases vS_cases x hnm (below_U_S_mem ⟨x, hx⟩).2 with rfl | rfl | ⟨h1, h2⟩ | ⟨c, hc⟩
    · have key := (rows₂_isConsistent U_S).locality ⟨H₀old, hx⟩
      refine transformsTo_congr rfl ?_ ?_ key
      · funext d; exact (E₃_of_A (aFace_castAdd _) d).symm
      · funext d
        rw [vS_eq_rows₂ (CellScheme.below.incl ⟨H₀old, hx⟩ d)
            (not_newS_of_A (aFace_of_below (aFace_castAdd _) d.2)),
          vS_eq_rows₂ ⟨H₀old, hx⟩ (not_newS_of_A (aFace_castAdd _))]
    · have key := (rows₂_isConsistent U_S).locality ⟨s₀old, hx⟩
      refine transformsTo_congr rfl ?_ ?_ key
      · funext d; exact (E₃_of_A (aFace_castAdd _) d).symm
      · funext d
        rw [vS_eq_rows₂ (CellScheme.below.incl ⟨s₀old, hx⟩ d)
            (not_newS_of_A (aFace_of_below (aFace_castAdd _) d.2)),
          vS_eq_rows₂ ⟨s₀old, hx⟩ (not_newS_of_A (aFace_castAdd _))]
    · rcases h1 with h1 | h1
      · rcases ret_H₀_cases hnm h1 with rfl | rfl | rfl
        · exact absurd (Or.inl rfl) h2
        · exact locality_U_S_H₀new hx
        · exact locality_U_S_U_H hx
      · rcases ret_s₀_cases hnm h1 with rfl | rfl | rfl
        · exact absurd (Or.inr rfl) h2
        · exact locality_U_S_s₀new hx
        · refine transformsTo_congr rfl (funext fun d => (E₃_U_S d).symm) ?_
            (TransformsTo.refl fun d : D₂.below (D₂.cell U_S) => vS d.1)
          funext d
          change vS d.1 = min (vS d.1) (vS U_S)
          rw [vS_of_new ⟨Or.inr ret₂_U_S, fullCell_ne_old s₀X rfl⟩, min_eq_left (vS_le_γ₁ d)]
    · have key := (rows₂_isConsistent U_S).locality ⟨x, hx⟩
      refine transformsTo_congr rfl ?_ ?_ key
      · funext d; exact (E₃_of_proper hc d).symm
      · funext d
        have hd := not_mute_below_U_S (CellScheme.below.incl ⟨x, hx⟩ d)
        rw [vS_eq_rows₂ (CellScheme.below.incl ⟨x, hx⟩ d) (by
            rintro ⟨h, -⟩
            rcases h with h | h
            · exact ret_ne_full_of_below hnm hd d.2 hc rfl h
            · exact ret_ne_full_of_below hnm hd d.2 hc rfl h),
          vS_eq_rows₂ ⟨x, hx⟩ (by
            rintro ⟨h, -⟩
            rcases h with h | h
            · exact ret_ne_of_inl' hc rfl h
            · exact ret_ne_of_inl' hc rfl h)]
  · intro Sig' Xi₀ hs hg
    by_cases hnew : (ret₂ Sig'.1 = family₂.e H₀X ∨ ret₂ Sig'.1 = family₂.e s₀X) ∧
        ¬ (Sig'.1 = H₀old ∨ Sig'.1 = s₀old)
    · refine ⟨Xi₀, rfl, ?_⟩
      have h3 : ({1, 2, 3} : Finset (Fin 4)) ⊆ D₂.scope Xi₀.1 :=
        (three_mem_of_newS (not_mute_below_U_S Sig') hnew).trans hs
      rw [vS_of_new hnew, vS_of_new ⟨?_, not_old_of_three h3⟩]
      rcases hnew.1 with h1 | h1
      · left
        refine ret_eq_H₀X_of_full (not_mute_below_U_S Xi₀) h3 ?_
        rw [← hg]; exact grade_of_ret_H₀ (not_mute_below_U_S Sig') h1
      · right
        refine ret_eq_s₀X_of_full (not_mute_below_U_S Xi₀) h3 ?_
        rw [← hg, grade_ret_eq (not_mute_below_U_S Sig'), h1, Equiv.symm_apply_apply]; rfl
    · obtain ⟨Xi, hc, hle⟩ := (rows₂_isConsistent U_S).availability Sig' Xi₀ hs hg
      refine ⟨Xi, hc, ?_⟩
      rw [vS_eq_rows₂ Sig' hnew]
      exact hle.trans (rows₂_le_vS Xi)

/-! ### The two level-three copies: raised sources under a cap, lowered sources between -/

theorem rows₂_fullCell_eq (x : family₂.X) (hx : (family₂.cellX x).1 = Finset.univ)
    (h4 : (family₂.cellX x).2 ≠ 4) (d : D₂.below (D₂.cell (fullCell x hx))) :
    rows₂.E (fullCell x hx) d = pull x d.1 := by
  rw [rows₂_E_eq_pull (not_mute_fullCell x hx h4), ret₂_fullCell, Equiv.symm_apply_apply]

theorem pull_of_ret {x y : family₂.X} {d : Cell D₂} (hd : ¬ mute₂ d) (h : ret₂ d = family₂.e y) :
    pull x d = family₂.rowX x y := by
  rw [pull_of_not_mute _ hd, h, Equiv.symm_apply_apply]

theorem grade_a₂old : D₂.grade a₂old = 3 := by change (D₂.cell a₂old).2 = 3; rw [cell_a₂old]
theorem a₂old_below_ub₁ : GradedLe (D₂.cell a₂old) (D₂.cell ub₁) := by
  rw [cell_a₂old, cell_ub₁]; exact ⟨Finset.subset_univ _, le_rfl⟩
theorem H₀old_below_U_S : GradedLe (D₂.cell H₀old) (D₂.cell U_S) := by
  rw [cell_U_S]; exact memA (by decide)
theorem labelQ_a₂old : labelQ a₂old = γ₀ := by
  rw [labelQ_eq_pull, pull_of_ret not_mute_a₂old ret₂_a₂old]; exact rowX_b₁_a₂

/-- **Consistency at a level-three copy** whose row reads a constant `cval` at the level-one and
level-two witnesses, at `a₂` and at `b₁`. -/
theorem consistent_Ac (x : family₂.X) (hx : (family₂.cellX x).1 = Finset.univ)
    (hx3 : (family₂.cellX x).2 = 3) {cval : ExtOrd} (hH : family₂.rowX x H₀X = cval)
    (hs : family₂.rowX x s₀X = cval) (ha₂ : family₂.rowX x a₂X = cval)
    (hb : family₂.rowX x b₁X = cval) (hvis : SelfVis 2 cval)
    (hne : fullCell x hx ≠ ub₁) :
    RespectsSemanticsBelow rows₃ (D₂.cell (fullCell x hx)) (rows₃.E (fullCell x hx)) := by
  have h4 : (family₂.cellX x).2 ≠ 4 := by rw [hx3]; decide
  have hnm := not_mute_fullCell x hx h4
  have hneH : fullCell x hx ≠ U_H := ne_of_cell_ne fun h => by
    rw [cell_fullCell, cell_U_H, hx3] at h; exact absurd (congrArg Prod.snd h) (by decide)
  have hneS : fullCell x hx ≠ U_S := ne_of_cell_ne fun h => by
    rw [cell_fullCell, cell_U_S, hx3] at h; exact absurd (congrArg Prod.snd h) (by decide)
  have h0 := rows₂_isConsistent (fullCell x hx)
  have hE : rows₃.E (fullCell x hx) = rows₂.E (fullCell x hx) := funext (E₃_of_ne hneH hneS hne)
  have hval : ∀ d : D₂.below (D₂.cell (fullCell x hx)),
      (ret₂ d.1 = family₂.e H₀X ∨ ret₂ d.1 = family₂.e s₀X) → rows₂.E (fullCell x hx) d = cval := by
    intro d hd
    rw [rows₂_fullCell_eq x hx h4]
    rcases hd with hd | hd
    · rw [pull_of_ret (hmute_below₂ _ d.1 hnm d.2) hd, hH]
    · rw [pull_of_ret (hmute_below₂ _ d.1 hnm d.2) hd, hs]
  rw [hE]
  refine ⟨h0.orderly, ?_, h0.availability⟩
  intro Sig'
  obtain ⟨y, hy⟩ := Sig'
  have hnmy : ¬ mute₂ y := hmute_below₂ _ y hnm hy
  rcases cell_cases y hnmy with ⟨i, rfl⟩ | hB | rfl | rfl | rfl | rfl | rfl
  · exact transformsTo_congr rfl (funext fun d => (E₃_of_A (aFace_castAdd i) d).symm) rfl
      (h0.locality ⟨_, hy⟩)
  · exact transformsTo_congr rfl (funext fun d => (E₃_of_B hB d).symm) rfl (h0.locality ⟨y, hy⟩)
  · -- the grade-one controller: raised sources under the cap `cval`
    have hcU : rows₂.E (fullCell x hx) ⟨U_H, hy⟩ = cval := hval ⟨U_H, hy⟩ (Or.inl ret₂_U_H)
    refine transformsTo_of_raise 1 (h0.locality ⟨U_H, hy⟩) (fun d => (below_U_H_mem d).2)
      (hvis.mono (by omega)) (fun d => (min_le_right _ _).trans hcU.le) fun d => ?_
    by_cases hnew : ret₂ d.1 = family₂.e H₀X ∧ d.1 ≠ H₀old
    · right
      refine ⟨?_, ⟨H₀old, memA_U⟩, ?_, ?_⟩
      · rw [hval (CellScheme.below.incl ⟨U_H, hy⟩ d) (Or.inl hnew.1), hcU, min_self]
      · change rows₂.E U_H ⟨H₀old, memA_U⟩ ≤ rows₃.E U_H d
        rw [rows₃_E, E₃_U_H, vU_of_new hnew, rows₂_U_H_H₀old]; exact δ_le_wSep
      · rw [hval (CellScheme.below.incl ⟨U_H, hy⟩ ⟨H₀old, memA_U⟩) (Or.inl ret₂_H₀old), hcU,
          min_self]
    · left; rw [rows₃_E, E₃_U_H]; exact vU_eq_rows₂ d hnew
  · -- the grade-two controller
    have hcS : rows₂.E (fullCell x hx) ⟨U_S, hy⟩ = cval := hval ⟨U_S, hy⟩ (Or.inr ret₂_U_S)
    refine transformsTo_of_raise 2 (h0.locality ⟨U_S, hy⟩) (fun d => (below_U_S_mem d).2)
      hvis (fun d => (min_le_right _ _).trans hcS.le) fun d => ?_
    by_cases hnew : (ret₂ d.1 = family₂.e H₀X ∨ ret₂ d.1 = family₂.e s₀X) ∧
        ¬ (d.1 = H₀old ∨ d.1 = s₀old)
    · right
      refine ⟨?_, ⟨H₀old, H₀old_below_U_S⟩, ?_, ?_⟩
      · rw [hval (CellScheme.below.incl ⟨U_S, hy⟩ d) hnew.1, hcS, min_self]
      · change rows₂.E U_S ⟨H₀old, H₀old_below_U_S⟩ ≤ rows₃.E U_S d
        rw [rows₃_E, E₃_U_S, vS_of_new hnew]
        exact (rows₂_U_S_eq' ⟨H₀old, H₀old_below_U_S⟩).le.trans
          ((pull_s₀_le _).trans s₀c_γ_le_γ₁)
      · rw [hval (CellScheme.below.incl ⟨U_S, hy⟩ ⟨H₀old, H₀old_below_U_S⟩) (Or.inl ret₂_H₀old),
          hcS, min_self]
    · left; rw [rows₃_E, E₃_U_S]; exact vS_eq_rows₂ d hnew
  · exact transformsTo_congr rfl
      (funext fun d => (E₃_of_ne A₁c_ne_U_H A₁c_ne_U_S A₁c_ne_ub₁ d).symm)
      rfl (h0.locality ⟨_, hy⟩)
  · exact transformsTo_congr rfl
      (funext fun d => (E₃_of_ne A₂c_ne_U_H A₂c_ne_U_S A₂c_ne_ub₁ d).symm)
      rfl (h0.locality ⟨_, hy⟩)
  · -- the copy of `b₁`: the lowered labels sit between the old label and `a₂`'s
    have hcb : rows₂.E (fullCell x hx) ⟨ub₁, hy⟩ = cval := by
      rw [rows₂_fullCell_eq x hx h4 ⟨ub₁, hy⟩, pull_of_ret not_mute_ub₁ ret₂_ub₁, hb]
    have hca : rows₂.E (fullCell x hx)
        (CellScheme.below.incl ⟨ub₁, hy⟩ ⟨a₂old, a₂old_below_ub₁⟩) = cval := by
      rw [rows₂_fullCell_eq x hx h4 (CellScheme.below.incl ⟨ub₁, hy⟩ ⟨a₂old, a₂old_below_ub₁⟩)]
      change pull x a₂old = cval
      rw [pull_of_ret not_mute_a₂old ret₂_a₂old, ha₂]
    refine transformsTo_of_between (h0.locality ⟨ub₁, hy⟩) fun d => ?_
    by_cases hold : d.1 = H₀old ∨ d.1 = s₀old
    · right
      refine ⟨⟨a₂old, a₂old_below_ub₁⟩, ?_, ?_, ?_, ?_⟩
      · rw [rows₃_E, E₃_ub₁, qL_of_eq hold]; erw [rows₂_ub₁_eq]; exact labelQ_a₂old.symm
      · erw [rows₂_ub₁_eq, rows₂_ub₁_eq]
        rw [labelQ_a₂old]
        rcases hold with h | h
        · rw [h, labelQ_H₀old]; exact γ₀_le_γ₁
        · rw [h, labelQ_s₀old]; exact γ₀_le_γ₁
      · rw [hca, hcb, hval (CellScheme.below.incl ⟨ub₁, hy⟩ d) (by
          rcases hold with h | h
          · exact Or.inl (by
              change ret₂ d.1 = _
              rw [h]; exact ret₂_H₀old)
          · exact Or.inr (by
              change ret₂ d.1 = _
              rw [h]; exact ret₂_s₀old))]
      · change D₂.grade d.1 ≤ D₂.grade a₂old
        rw [grade_a₂old]; exact grade_le_below_ub₁ d
    · left; rw [rows₃_E, E₃_ub₁, qL_of_ne hold]; erw [rows₂_ub₁_eq]

theorem consistent_A₁c : RespectsSemanticsBelow rows₃ (D₂.cell A₁c) (rows₃.E A₁c) :=
  consistent_Ac a₁X rfl rfl rowX_a₁_H rowX_a₁_s rowX_a₁_a₂ rowX_a₁_b₁ (η₁_vis.mono (by omega))
    A₁c_ne_ub₁
theorem consistent_A₂c : RespectsSemanticsBelow rows₃ (D₂.cell A₂c) (rows₃.E A₂c) :=
  consistent_Ac a₂X rfl rfl rowX_a₂_H rowX_a₂_s rowX_a₂_a₂ rowX_a₂_b₁ (γ₀_vis.mono (by omega))
    A₂c_ne_ub₁

/-- **The modified semantics is consistent.** -/
theorem rows₃_consistent : rows₃.IsConsistent := by
  intro Sig
  by_cases hm : mute₂ Sig
  · exact consistent_mute hm
  rcases cell_cases Sig hm with ⟨i, rfl⟩ | hB | rfl | rfl | rfl | rfl | rfl
  · exact consistent_A (aFace_castAdd i)
  · exact consistent_B hB
  · exact consistent_U_H
  · exact consistent_U_S
  · exact consistent_A₁c
  · exact consistent_A₂c
  · exact consistent_ub₁

end Consistency

/-! ## The realization -/

section Realization

theorem p₀_label' (i : Cell C₀) : p₀.label i = family₂.rowX a₂X (embX₀ (family₀.e.symm i)) := by
  change family₀.rows.E top ⟨i, hall₀ i⟩ = _
  change family₀.rowX (family₀.e.symm (family₀.e _)) (family₀.e.symm i) = _
  rw [Equiv.symm_apply_apply, rowX₀_eq]; rfl

/-- **The labelling realizes the original prescribed pair.** -/
theorem qL_realizes : RealizesPair (fun d => qL d.1) where
  faceA i := by
    change qL (Fin.castAdd (Fintype.card New₂) i) = p₀.label i
    rw [qL_castAdd i, pull_of_not_mute _ (not_mute₂_castAdd i), ret₂_castAdd, p₀_label']
    change family₂.rowX a₂X (family₂.e.symm (family₂.e (embX₀ (family₀.e.symm i)))) = _
    rw [Equiv.symm_apply_apply]
  faceB c := by
    change qL (copyB c) = p₁.label c
    rw [qL_of_B (copyB_mem c), ← Q_label, label_copyB]

/-- **Both input faces are untouched.** -/
theorem rows₃_faceA (i : Cell C₀) (d : D₂.below (D₂.cell (Fin.castAdd (Fintype.card New₂) i))) :
    rows₃.E (Fin.castAdd (Fintype.card New₂) i) d = rows₂.E (Fin.castAdd (Fintype.card New₂) i) d :=
  E₃_of_A (aFace_castAdd i) d
theorem rows₃_faceB (c : Cell C₁) (d : D₂.below (D₂.cell (copyB c))) :
    rows₃.E (copyB c) d = rows₂.E (copyB c) d :=
  E₃_of_B (copyB_mem c) d

/-- **The coupled construction**: a coded, consistent semantics on the glued scheme, agreeing
with the fixed glue on both input faces, together with a respecting labelling of the full
grade-three lower set realizing the original prescribed pair `(p₀, p₁)`. -/
theorem coupled_realization :
    ∃ sem : Semantics D₂, sem.IsCoded ∧ sem.IsConsistent ∧
      (∀ (i : Cell C₀) (d : D₂.below (D₂.cell (Fin.castAdd (Fintype.card New₂) i))),
        sem.E (Fin.castAdd (Fintype.card New₂) i) d =
          rows₂.E (Fin.castAdd (Fintype.card New₂) i) d) ∧
      (∀ (c : Cell C₁) (d : D₂.below (D₂.cell (copyB c))),
        sem.E (copyB c) d = rows₂.E (copyB c) d) ∧
      ∃ q : D₂.below (Finset.univ, 3) → ExtOrd,
        RespectsSemanticsBelow sem (Finset.univ, 3) q ∧ RealizesPair q :=
  ⟨rows₃, rows₃_coded, rows₃_consistent, rows₃_faceA, rows₃_faceB, fun d => qL d.1, qL_respects,
    qL_realizes⟩

end Realization




end VaughtConjecture.Knight
