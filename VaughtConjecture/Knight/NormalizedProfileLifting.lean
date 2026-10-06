/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.NormalizedProfileFamily
public import VaughtConjecture.Knight.GradeOneSectionLifting

/-! # Uniform original-cap lifting for normalized finite profile families

The controller is constructed from the input order/refinement laws. The
output again has those laws by `NormalizedProfileFamily.family`, so the
algebraic construction may be reapplied. No support-plan assembly, nonbottom
higher-grade controller, guarded forcing, or legal successor is asserted.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.NormalizedProfileLifting

open Transform Value ExtOrd SlotControllerFamily FullRowLifting
open NormalizedProfileFamily SlotPatternRefinement

local notation "rankCode" => NormalizedProfileFamily.code

variable {X : Type*} [Fintype X] (L : OrderLaw X)

theorem active_cover {r : X ⊕ Profile L → ExtOrd} {p : X → ExtOrd} {γ : ExtOrd}
    (hr : (family L).holds r) (hp : L.holds p)
    (hγ : ⊥ < γ) (hag : ∀ d, min (r (.inl d)) γ = min (p d) γ)
    (hreach : ∃ d, γ ≤ p d) :
    ∃ q : Profile L, γ ≤ r (.inr q) ∧
      TransformsTo (fun _ : X => 1) (fun d => value (profile L q d)) p := by
  classical
  obtain ⟨q, f, hf, h0, _, he⟩ := hr.exists_shape
  have hag' (d : X) : min (f (profile L q d)) γ = min (p d) γ := by
    simpa only [he, FiniteProfileControllers.index] using hag d
  have htop : γ ≤ f (Fintype.card X) := by
    obtain ⟨d, hd⟩ := hreach
    have hh := hag' d
    rw [min_eq_right hd] at hh
    exact (hh.symm.trans_le (min_le_left _ _)).trans (hf (profile_bound L q d))
  have hex : ∃ n : ℕ, γ ≤ f n := ⟨Fintype.card X, htop⟩
  let a := Nat.find hex
  have hab : a ≤ Fintype.card X := Nat.find_min' hex htop
  have hfa : γ ≤ f a := Nat.find_spec hex
  have hlo : ∀ k, k < a → f k < γ := fun k hk => lt_of_not_ge (Nat.find_min hex hk)
  have ha : 0 < a := by
    by_contra hn
    have haz : a = 0 := by omega
    rw [haz, h0] at hfa
    exact (not_le_of_gt hγ) hfa
  have low (d : X) (hd : profile L q d < a) : p d = f (profile L q d) := by
    have hh := (hag' d).symm
    rw [min_eq_left (hlo _ hd).le] at hh
    have hpd : p d < γ := by
      by_contra hn
      rw [min_eq_right (le_of_not_gt hn)] at hh
      exact (ne_of_lt (hlo _ hd)) hh.symm
    rwa [min_eq_left hpd.le] at hh
  have high (d : X) (hd : a ≤ profile L q d) : γ ≤ p d := by
    have hh := hag' d
    rw [min_eq_right (hfa.trans (hf hd))] at hh
    exact hh.trans_le (min_le_left _ _)
  have hsep (d e : X) (hd : profile L q d < a) (he : a ≤ profile L q e) :
      rankCode p d < rankCode p e := by
    rw [lt_iff_not_ge, code_order]
    have hpd : p d < γ := (low d hd).trans_lt (hlo _ hd)
    exact not_le_of_gt (hpd.trans_le (high e he))
  let s := mix (profile L q) (rankCode p) a
  have hs : L.holds (fun d => value (s d)) :=
    L.refine ha q.property.1 (encoded_lawful L hp) hsep
  let q' := encode L hs
  have sl (d : X) (hd : profile L q d < a) : s d = profile L q d := by
    simp only [s, mix, hd, ↓reduceIte]
  have su (d : X) (hd : a ≤ profile L q d) : a ≤ s d := by
    simp only [s, mix, Nat.not_lt.mpr hd, ↓reduceIte]
    omega
  have hagree : FiniteProfileControllers.Agree (profile L q) (profile L q') a :=
    prefix_agree L q s ha sl su
  have hc : a ≤ FiniteProfileControllers.cut (Fintype.card X) (profile L q) (profile L q') :=
    FiniteProfileControllers.le_cut hab hagree
  refine ⟨q', ?_, ?_⟩
  · rw [he]
    exact hfa.trans (hf hc)
  · apply transforms_of_table
    · exact L.visible hp
    · intro d hd
      have hv : value (s d) = ⊥ := (code_zero (fun e => value (s e)) d).mp hd
      have hsz : s d = 0 := Nat.eq_zero_of_le_zero ((value_le_iff _ 0).mp hv.le)
      have hqd : profile L q d < a := by
        by_contra hn
        have hh := su d (Nat.le_of_not_gt hn)
        omega
      have hqz : profile L q d = 0 := (sl d hqd).symm.trans hsz
      rw [low d hqd, hqz, h0]
    · intro d e hde
      have hvalues : value (s d) ≤ value (s e) :=
        (code_order (fun j => value (s j)) d e).mp hde
      have hse := (value_le_iff _ _).mp hvalues
      by_cases hd : profile L q d < a
      · by_cases he : profile L q e < a
        · rw [low d hd, low e he]
          exact hf (by rwa [sl d hd, sl e he] at hse)
        · exact ((low d hd).trans_lt (hlo _ hd)).le.trans (high e (Nat.le_of_not_gt he))
      · by_cases he : profile L q e < a
        · have hh := su d (Nat.le_of_not_gt hd)
          rw [sl e he] at hse
          omega
        · apply (code_order p d e).mp
          simp only [s, mix, hd, he, ↓reduceIte] at hse
          omega

private theorem transform_order {Y : Type*} {s t : Y → ExtOrd}
    (h : TransformsTo (fun _ : Y => 1) s t) (d e : Y) (hde : s d ≤ s e) : t d ≤ t e := by
  obtain ⟨g, σ, _, _, _, hm, _, hr⟩ := h
  rw [hr d, hr e]
  exact min_le_min_right _ (hm hde)

private theorem transform_bottom {Y : Type*} {s t : Y → ExtOrd}
    (h : TransformsTo (fun _ : Y => 1) s t) (d : Y) (hd : s d = ⊥) : t d = ⊥ := by
  obtain ⟨g, σ, _, _, hb, _, _, hr⟩ := h
  rw [hr d, hd, hb, min_bot_left]

/-- Every lawful whole input lifts at the original cap against every joint
ambient. All newly added controller caps are retained as well. -/
theorem lift {a : X ⊕ Profile L → ExtOrd} {p : X → ExtOrd} {γ : ExtOrd}
    (ha : (family L).holds a) (hp : L.holds p)
    (hγ : SelfVis 1 γ) (hag : ∀ d, min (a (.inl d)) γ = min (p d) γ) :
    ∃ r, (family L).holds r ∧
      (∀ d, min (r d) γ = min (a d) γ) ∧ ∀ d, r (.inl d) = p d := by
  classical
  by_cases hbot : γ = ⊥
  · obtain ⟨r, hr, he⟩ := exists_section L hp
    exact ⟨r, hr, fun d => by simp only [hbot, min_bot_right], he⟩
  by_cases hreach : ∃ d, γ ≤ p d
  swap
  · refine ⟨a, ha, fun _ => rfl, ?_⟩
    intro d
    have hd : p d < γ := lt_of_not_ge (fun h => hreach ⟨d, h⟩)
    exact ((cap_eq_iff_profile _ _ _).mp (hag d)).1 hd
  obtain ⟨q, hact, hface⟩ := active_cover L ha hp (bot_lt_iff_ne_bot.mpr hbot) hag hreach
  let s := FiniteProfileControllers.row (Fintype.card X) (profile L) q
  let t : X ⊕ Profile L → ExtOrd := fun d => min (a d) γ
  have htrace : TransformsTo (fun _ : X ⊕ Profile L => 1) s t := by
    have ht := (ha.2.1 q).cap (fun _ => le_rfl) hγ
    have he : ∀ d, min (min (a d) (a (.inr q))) γ = min (a d) γ := by
      intro d
      rw [min_assoc, min_eq_right hact]
    simpa only [he] using ht
  have htvis : ∀ d, SelfVis 1 (t d) := fun d => selfVis_min (ha.1 d) hγ
  have hcheck : Propagation.Check s Sum.inl p t γ :=
    Propagation.check_of_compatible_order (transform_order hface) (transform_order htrace)
      (transform_bottom hface) (transform_bottom htrace)
      (fun d => by simpa only [t, min_assoc, min_self] using hag d)
  let r := Propagation.close s Sum.inl p t γ
  have hrvis : ∀ d, SelfVis 1 (r d) :=
    Propagation.close_visible s Sum.inl (L.visible hp) htvis hγ
  have hj : (family L).holds r := by
    apply FiniteProfileRefinement.joint_of_order (profile_bound L) q r hrvis
    · intro d hd
      apply hcheck.2.2 d
      change value (FiniteProfileControllers.index (Fintype.card X) (profile L) q d) = ⊥
      rw [hd]
      rfl
    · intro d e hde
      exact Propagation.close_order _ _ _ _ _ (value_mono hde)
  refine ⟨r, hj, ?_, ?_⟩
  · intro d
    have hh : min (r d) γ = min (t d) γ := by
      apply (cap_eq_iff_profile _ _ _).mpr
      constructor
      · intro hd
        apply le_antisymm (hcheck.1 d hd)
        have hl := Propagation.cap_le_close s Sum.inl p t γ d
        rwa [min_eq_left hd.le] at hl
      · intro hd
        have hl := Propagation.cap_le_close s Sum.inl p t γ d
        rwa [min_eq_right hd] at hl
    simpa only [t, min_assoc, min_self] using hh
  · intro d
    exact le_antisymm (hcheck.2.1 d) (Propagation.prescribed_le_close s Sum.inl p t γ d)

end VaughtConjecture.Knight.NormalizedProfileLifting
