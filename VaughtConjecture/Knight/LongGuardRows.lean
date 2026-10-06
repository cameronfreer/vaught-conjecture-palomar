/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.VisibleOrderInterpolation
public import VaughtConjecture.Knight.SlotControllerFamily

/-! # Explicit grade-one long guards

At cut `i`, retain the separated short sources through rank `i` and collapse
all higher ranks to the long endpoint `ω * i + 2`. A monotone visible table
is a faithful target precisely when its two readings at this mixed source
block have the same bottom flag (provided both endpoints actually occur).

The sufficiency proof constructs a faithful witness at every threshold, not
just a bounded numerical map. This is the local guard used by the proposed
support compiler in `simplification-notes6/zero_implications.md`, Section 2.
It does not by itself install a support plan or prove lifting.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.LongGuardRows

open Transform Value ExtOrd SharpWitnessComposition FullRowLifting

/-- A finite visible table with the exact source-block zero condition has a
faithful witness. Repeated source occurrences remain literal. -/
theorem transforms_of_visible_table {Y : Type*} [Finite Y] {E t : Y → ExtOrd}
    (hE : ∀ d, SelfVis 1 (E d)) (ht : ∀ d, SelfVis 1 (t d))
    (hord : ∀ d e, E d ≤ E e → t d ≤ t e)
    (hbot : ∀ d, E d = ⊥ → t d = ⊥)
    (hblock : ∀ d e, blockFloor (E d) = blockFloor (E e) → t d = ⊥ → t e = ⊥) :
    TransformsTo (fun _ : Y => 1) E t := by
  classical
  let _ := Fintype.ofFinite Y
  let s := Finset.univ.image E
  have hf := orderInterpolate_bounded hE ht
  have hb : BlockBottom s (orderInterpolate E t) := by
    intro x hx y hy hxy hz
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hy
    rw [orderInterpolate_read hord hbot] at hz ⊢
    exact hblock d e hxy hz
  obtain ⟨τ, hτ, hread⟩ := (hf.interpolate_iff_source_blocks s).mpr hb
  apply hτ.transformsTo
  intro d
  rw [gTop_of_le le_rfl, min_top_right,
    hread _ (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩),
    orderInterpolate_read hord hbot]

/-- Actual faithful locality, even with a nontrivial suppressor, prohibits
different bottom flags in one source block at a common grade. -/
theorem bottom_of_same_block {Y : Type*} {E t : Y → ExtOrd}
    (h : TransformsTo (fun _ : Y => 1) E t) {d e : Y}
    (hb : blockFloor (E d) = blockFloor (E e)) (hd : t d = ⊥) : t e = ⊥ := by
  obtain ⟨g, σ, hg, hgv, h0, hm, h5, hr⟩ := h
  have hz : min (σ (E d)) (g 1) = ⊥ := (hr d).symm.trans hd
  rcases min_eq_bot.mp hz with hz | hz
  · have he := witness_bot_of_same_block
      (show Witness g σ from ⟨hg, hgv, h0, hm, h5⟩) hb hz
    rw [hr e, he, min_bot_left]
  · rw [hr e, hz, min_bot_right]

noncomputable def endpoint (i : ℕ) : ExtOrd :=
  ofOrd (Ordinal.omega0 * i + (2 : ℕ))

noncomputable def source (i k : ℕ) : ExtOrd :=
  if k ≤ i then SlotControllerFamily.value k else endpoint i

theorem endpoint_visible (i : ℕ) : SelfVis 1 (endpoint i) := by
  rw [endpoint, selfVis_ofOrd_iff, finitePart_code]
  omega

theorem source_visible (i k : ℕ) : SelfVis 1 (source i k) := by
  unfold source
  split_ifs
  · exact SlotControllerFamily.value_visible k
  · exact endpoint_visible i

theorem source_coded (i k : ℕ) : IsCodedLabel 1 (source i k) := by
  unfold source
  split_ifs
  · exact SlotControllerFamily.value_coded k
  · exact Or.inr ⟨i, 2, le_rfl, rfl⟩

@[simp] theorem source_zero (i : ℕ) : source i 0 = ⊥ := by
  simp [source, SlotControllerFamily.value]

theorem source_bot_iff (i k : ℕ) : source i k = ⊥ ↔ k = 0 := by
  by_cases hk : k ≤ i
  · simp [source, hk, SlotControllerFamily.value, SeparatedGradeOne.band]
  · simp [source, hk, endpoint, show k ≠ 0 by omega]

theorem value_lt_endpoint {i k : ℕ} (hk : k ≤ i) :
    SlotControllerFamily.value k < endpoint i := by
  by_cases h0 : k = 0
  · simp [h0, SlotControllerFamily.value, endpoint]
  · rw [SlotControllerFamily.value, ite_eq_right h0, SeparatedGradeOne.band, endpoint,
      ofOrd_lt_ofOrd]
    rcases lt_or_eq_of_le hk with hk | rfl
    · exact code_lt_code_of_lt (Nat.cast_lt.mpr hk) 1 2
    · exact add_lt_add_right (Nat.cast_lt.mpr (by omega : (1 : ℕ) < 2)) _

theorem source_le_iff (i k l : ℕ) :
    source i k ≤ source i l ↔ min k (i + 1) ≤ min l (i + 1) := by
  by_cases hk : k ≤ i <;> by_cases hl : l ≤ i
  · simp only [source, ite_eq_left hk, ite_eq_left hl,
      SlotControllerFamily.value_le_iff, min_eq_left (by omega : k ≤ i + 1),
      min_eq_left (by omega : l ≤ i + 1)]
  · have hv := (value_lt_endpoint hk).le
    simp only [source, ite_eq_left hk, ite_eq_right hl]
    constructor
    · intro _; omega
    · intro _; exact hv
  · have hv := not_le_of_gt (value_lt_endpoint hl)
    simp only [source, ite_eq_right hk, ite_eq_left hl]
    constructor
    · intro h; exact (hv h).elim
    · intro h; omega
  · simp only [source, ite_eq_right hk, ite_eq_right hl, le_refl,
      min_eq_right (by omega : i + 1 ≤ k), min_eq_right (by omega : i + 1 ≤ l)]

/-- Only the last short source shares a block with the long endpoint. -/
theorem value_floor_endpoint {i k : ℕ} (hk : k ≠ 0)
    (h : blockFloor (SlotControllerFamily.value k) = blockFloor (endpoint i)) : k = i := by
  rw [SlotControllerFamily.value, ite_eq_right hk, SeparatedGradeOne.band_floor,
    endpoint, blockFloor_ofOrd, limitPart_code, ofOrd_inj] at h
  exact Nat.cast_injective ((Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.injective h)

/-- The guard receives every visible monotone table with its sole residual
zero implication. No bottom-reflection is required at other blocks. -/
theorem transforms {Y : Type*} [Finite Y] (a : Y → ℕ) (i : ℕ)
    (f : ℕ → ExtOrd) (hm : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ k, SelfVis 1 (f k)) (hz : f i = ⊥ → f (i + 1) = ⊥) :
    TransformsTo (fun _ : Y => 1) (fun d => source i (a d))
      (fun d => f (min (a d) (i + 1))) := by
  apply transforms_of_visible_table (fun _ => source_visible _ _) (fun _ => hv _)
  · intro d e hde
    exact hm ((source_le_iff _ _ _).mp hde)
  · intro d hd
    rw [(source_bot_iff _ _).mp hd, Nat.zero_min, h0]
  · intro d e hb hd
    by_cases hdz : a d = 0
    · have he : source i (a e) = ⊥ := by
        rw [hdz, source_zero, blockFloor_bot] at hb
        by_contra he
        unfold source at hb
        split_ifs at hb with hae
        · have hn : a e ≠ 0 := fun h => he ((source_bot_iff _ _).mpr h)
          simp only [SlotControllerFamily.value, ite_eq_right hn,
            SeparatedGradeOne.band_floor] at hb
          exact ofOrd_ne_bot _ hb.symm
        · simp only [endpoint, blockFloor_ofOrd] at hb
          exact ofOrd_ne_bot _ hb.symm
      rw [(source_bot_iff _ _).mp he, Nat.zero_min, h0]
    by_cases hez : a e = 0
    · rw [hez, Nat.zero_min, h0]
    by_cases hdi : a d ≤ i <;> by_cases hei : a e ≤ i
    · have heq : a d = a e := by
        simp only [source, ite_eq_left hdi, ite_eq_left hei, SlotControllerFamily.value,
          ite_eq_right hdz, ite_eq_right hez] at hb
        have hh := SeparatedGradeOne.band_separated hb
        exact le_antisymm ((FreshSourceSlots.band_le_iff _ _).mp hh.le)
          ((FreshSourceSlots.band_le_iff _ _).mp hh.ge)
      simpa only [heq] using hd
    · have heq : a d = i := value_floor_endpoint hdz (by
        simpa only [source, ite_eq_left hdi, ite_eq_right hei] using hb)
      rw [heq, min_eq_left (Nat.le_succ i)] at hd
      rw [min_eq_right (by omega : i + 1 ≤ a e)]
      exact hz hd
    · rw [min_eq_right (by omega : i + 1 ≤ a d)] at hd
      exact le_bot_iff.mp ((hm (min_le_right _ _)).trans_eq hd)
    · simpa only [min_eq_right (by omega : i + 1 ≤ a d),
        min_eq_right (by omega : i + 1 ≤ a e)] using hd

/-- If both endpoint ranks occur, faithful locality forces the guard's exact
zero implication; a forbidden erasure fails an actual row. -/
theorem residual_of_transform {Y : Type*} {a : Y → ℕ} {i : ℕ} (hi : i ≠ 0)
    {f : ℕ → ExtOrd} {d e : Y} (hd : a d = i) (he : i < a e)
    (h : TransformsTo (fun _ : Y => 1) (fun v => source i (a v))
      (fun v => f (min (a v) (i + 1)))) : f i = ⊥ → f (i + 1) = ⊥ := by
  intro hz
  have hb : blockFloor (source i (a d)) = blockFloor (source i (a e)) := by
    simp only [hd, source, le_refl, ite_eq_left, ite_eq_right (not_le.mpr he),
      SlotControllerFamily.value, ite_eq_right hi, SeparatedGradeOne.band_floor,
      endpoint, blockFloor_ofOrd, limitPart_code]
  have hzero : f (min (a d) (i + 1)) = ⊥ := by
    simpa only [hd, min_eq_left (Nat.le_succ i)] using hz
  have hresult := bottom_of_same_block h hb hzero
  simpa only [min_eq_right (by omega : i + 1 ≤ a e)] using hresult

/-- Exact finite guard test, including the long endpoint and every threshold. -/
theorem transforms_iff {Y : Type*} [Finite Y] (a : Y → ℕ) {i : ℕ} (hi : i ≠ 0)
    (f : ℕ → ExtOrd) (hm : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ k, SelfVis 1 (f k)) {d e : Y} (hd : a d = i) (he : i < a e) :
    TransformsTo (fun _ : Y => 1) (fun v => source i (a v))
      (fun v => f (min (a v) (i + 1))) ↔ (f i = ⊥ → f (i + 1) = ⊥) :=
  ⟨residual_of_transform hi hd he, transforms a i f hm h0 hv⟩

/-- An allowed scalar profile cannot cross a forbidden support cut of an
agreeing profile. This constructs the residual implication from support data. -/
theorem residual_of_allowed_profile {X : Type*} {a b : X → ℕ} {i e : ℕ}
    {allowed : Set (Set X)} {f : ℕ → ExtOrd} (hm : Monotone f)
    (hag : ∀ d, min (a d) e = min (b d) e)
    (hbad : {d | i < a d} ∉ allowed) (hgood : {d | f (b d) ≠ ⊥} ∈ allowed) :
    f (min i e) = ⊥ → f (min (i + 1) e) = ⊥ := by
  intro hz
  by_cases he : e ≤ i
  · simpa only [min_eq_right he, min_eq_right (he.trans (Nat.le_succ i))] using hz
  have hi : i + 1 ≤ e := by omega
  rw [min_eq_left (by omega : i ≤ e)] at hz
  rw [min_eq_left hi]
  by_contra hn
  have heq : {d | i < a d} = {d | f (b d) ≠ ⊥} := by
    ext d
    change i < a d ↔ f (b d) ≠ ⊥
    have hd := hag d
    constructor
    · intro ha hf
      have hb : i + 1 ≤ b d := by omega
      exact hn (le_bot_iff.mp ((hm hb).trans_eq hf))
    · intro hf
      by_contra ha
      have hb : b d ≤ i := by omega
      exact hf (le_bot_iff.mp ((hm hb).trans_eq hz))
  exact hbad (heq.symm ▸ hgood)

/-- The whole guard locality of a common-prefix family. The target is capped
at its actual cross-reading `min e (i+1)`; support admissibility supplies the
otherwise missing long-source implication. -/
theorem transforms_from_allowed_profile {X Y : Type*} [Finite Y]
    (r : Y → ℕ) {a b : X → ℕ} (i e : ℕ) {allowed : Set (Set X)}
    (f : ℕ → ExtOrd) (hm : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ k, SelfVis 1 (f k)) (hag : ∀ d, min (a d) e = min (b d) e)
    (hbad : {d | i < a d} ∉ allowed) (hgood : {d | f (b d) ≠ ⊥} ∈ allowed) :
    TransformsTo (fun _ : Y => 1) (fun v => source i (r v))
      (fun v => f (min (r v) (min e (i + 1)))) := by
  have h := transforms r i (fun k => f (min k e))
    (fun _ _ h => hm (min_le_min_right _ h)) (by simpa using h0) (fun _ => hv _)
    (residual_of_allowed_profile hm hag hbad hgood)
  simpa only [min_assoc, min_comm (i + 1) e] using h

namespace Regression

/-- Reference, cap, negative-test coordinate, selector, and an actual guard. -/
def ranks : Fin 5 → ℕ := ![2, 3, 1, 0, 2]

noncomputable def erased (k : ℕ) : ExtOrd := if k ≤ 1 then ⊥ else ofOrd 1

/-- Erasing the negative-test coordinate while keeping the reference, cap,
and guard positive is rejected by the guard's own faithful locality. -/
theorem forbidden_erasure : ¬ TransformsTo (fun _ : Fin 5 => 1)
    (fun d => source 1 (ranks d)) (fun d => erased (min (ranks d) 2)) := by
  intro h
  have hz := residual_of_transform (by decide : (1 : ℕ) ≠ 0)
    (d := (2 : Fin 5)) (e := (4 : Fin 5)) (by decide : ranks 2 = 1)
    (by decide : 1 < ranks 4) h
  exact ofOrd_ne_bot 1 (hz rfl)

/-- The same frozen row admits the unerased profile; the negative result is
not an inconsistent-row artifact. -/
theorem unerased_locality : TransformsTo (fun _ : Fin 5 => 1)
    (fun d => source 1 (ranks d))
      (fun d => SlotControllerFamily.value (min (ranks d) 2)) := by
  apply transforms ranks 1 SlotControllerFamily.value SlotControllerFamily.value_mono
    rfl SlotControllerFamily.value_visible
  intro hz
  exact (ofOrd_ne_bot _ hz).elim

end Regression

end VaughtConjecture.Knight.LongGuardRows
