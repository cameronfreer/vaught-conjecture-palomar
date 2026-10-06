/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowHighAboveN

/-! # The two-threshold same-grade fibres at every cutoff (audit16 §1; note §11 (5))

The all-grade statements of both same-grade fibres of the two-threshold family
(`LowRef.exists_private_lift`, `LowRef.exists_request_lift`): for an admissible two-threshold
state and a lawful current prescription on one original face agreeing with the state below a
permissible cap `γ`, there is an admissible state with that prescription literally, every
coordinate of the other section retained below `γ`, the cap receipts of the gate and of every
persistent field, the cap receipt of the stored cutoff, and — at a positive cap — the gate and
every shadow (every still-future field) retained **literally**.  The cases: below `K`, at bottom
cap, between `K` and `N`, and at or above `N`.

On **source profiles** (`Synchronized`), resynchronization preserves two-threshold admissibility
(`TAdmissible.resync`: the source vector, hence the non-top maximum and the cap field, is
unchanged), and both fibres carry complete cap receipts for every persistent field
(`exists_private_lift_sync`, `exists_request_lift_sync`).

This is a theorem about complete source states with one prescribed original face, not about
simultaneous exact prescriptions on two original faces or arbitrary physical histories; the
conversion of the complete field receipts into controller/node/guard receipts of a constructed
physical scheme is the separate prefix/row obligation, not asserted here. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

namespace CappedDonor

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C} {K : ℕ} (L : R.LowRef K)

/-! ## Both fibres at every cutoff -/

/-- **The private fibre** (all cutoffs). -/
theorem LowRef.exists_private_lift {j : ℕ} {S : R.TState j} (hS : L.TAdmissible S)
    {v₁ : C.scheme.below (effC J j) → ExtOrd} (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁)
    {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (v₁ d) γ = min (S.st.v d) γ) :
    ∃ S₁ : R.TState j, L.TAdmissible S₁ ∧ S₁.st.v = v₁ ∧
      (∀ d, min (S₁.st.u d) γ = min (S.st.u d) γ) ∧ R.CapReceipts γ S.st S₁.st ∧
      min S₁.b γ = min S.b γ ∧
      (γ ≠ ⊥ → S₁.st.gate = S.st.gate ∧ S₁.st.shadowP = S.st.shadowP ∧
        S₁.st.shadowC = S.st.shadowC) := by
  by_cases hbot : γ = ⊥
  · subst hbot
    obtain ⟨S₁, hS₁, hv, -⟩ := L.exists_private_lift_bot hS hv₁
    exact ⟨S₁, hS₁, hv, fun _ => by rw [min_bot_right, min_bot_right], R.capReceipts_bot _ _,
      by rw [min_bot_right, min_bot_right], fun h => absurd rfl h⟩
  by_cases hjK : j < K
  · exact L.exists_private_lift_lt_K hjK hS hv₁ hγ hagree
  by_cases hjN : j < N
  · obtain ⟨S₁, hS₁, hv, hu, hb, hg, hP, hC⟩ :=
      L.exists_private_lift_belowN (not_lt.mp hjK) hjN hS hv₁ hγ hbot hagree
    exact ⟨S₁, hS₁, hv, hu, R.capReceipts_of_eq γ hg hP hC, hb, fun _ => ⟨hg, hP, hC⟩⟩
  · obtain ⟨S₁, hS₁, hv, hu, hb, hg, hP, hC⟩ :=
      L.exists_private_lift_aboveN (not_lt.mp hjN) hS hv₁ hγ hbot hagree
    exact ⟨S₁, hS₁, hv, hu, R.capReceipts_of_eq γ hg hP hC, hb, fun _ => ⟨hg, hP, hC⟩⟩

/-- **The request fibre** (all cutoffs). -/
theorem LowRef.exists_request_lift {j : ℕ} {S : R.TState j} (hS : L.TAdmissible S)
    {u₁ : P.scheme.below (effP nP j) → ExtOrd} (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁)
    {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (u₁ d) γ = min (S.st.u d) γ) :
    ∃ S₁ : R.TState j, L.TAdmissible S₁ ∧ S₁.st.u = u₁ ∧
      (∀ d, min (S₁.st.v d) γ = min (S.st.v d) γ) ∧ R.CapReceipts γ S.st S₁.st ∧
      min S₁.b γ = min S.b γ ∧
      (γ ≠ ⊥ → S₁.st.gate = S.st.gate ∧ S₁.st.shadowP = S.st.shadowP ∧
        S₁.st.shadowC = S.st.shadowC) := by
  by_cases hbot : γ = ⊥
  · subst hbot
    obtain ⟨S₁, hS₁, hu, -⟩ := L.exists_request_lift_bot hS hu₁
    exact ⟨S₁, hS₁, hu, fun _ => by rw [min_bot_right, min_bot_right], R.capReceipts_bot _ _,
      by rw [min_bot_right, min_bot_right], fun h => absurd rfl h⟩
  by_cases hjK : j < K
  · exact L.exists_request_lift_lt_K hjK hS hu₁ hγ hagree
  by_cases hjN : j < N
  · obtain ⟨S₁, hS₁, hu, hv, hb, hg, hP, hC⟩ :=
      L.exists_request_lift_belowN (not_lt.mp hjK) hjN hS hu₁ hγ hbot hagree
    exact ⟨S₁, hS₁, hu, hv, R.capReceipts_of_eq γ hg hP hC, hb, fun _ => ⟨hg, hP, hC⟩⟩
  · obtain ⟨S₁, hS₁, hu, hv, hb, hg, hP, hC⟩ :=
      L.exists_request_lift_aboveN (not_lt.mp hjN) hS hu₁ hγ hbot hagree
    exact ⟨S₁, hS₁, hu, hv, R.capReceipts_of_eq γ hg hP hC, hb, fun _ => ⟨hg, hP, hC⟩⟩

/-! ## Source profiles -/

/-- The source vector is unchanged by resynchronization. -/
theorem sourceProfile_resync {j : ℕ} (st : R.State j) :
    (resync st).sourceProfile = st.sourceProfile := by
  funext f
  by_cases h : f.grade ≤ j
  · rw [State.sourceProfile_of_present _ h, State.sourceProfile_of_present _ h]
    cases f <;> rfl
  · rw [State.sourceProfile_of_future _ h, State.sourceProfile_of_future _ h]
    cases f with
    | req d => exact resync_shadowP_of_future st h
    | priv d => exact resync_shadowC_of_future st h
    | gate => rfl

theorem nonTopMax_resync {j : ℕ} (st : R.State j) : (resync st).nonTopMax = st.nonTopMax := by
  unfold State.nonTopMax; rw [sourceProfile_resync]

theorem capField_resync {j : ℕ} (st : R.State j) : (resync st).capField = st.capField := by
  unfold State.capField; rw [sourceProfile_resync]

/-- Resynchronization preserves two-threshold admissibility. -/
theorem LowRef.TAdmissible.resync {j : ℕ} {S : R.TState j} (hS : L.TAdmissible S) :
    L.TAdmissible ⟨resync S.st, S.b⟩ where
  adm := hS.adm.resync
  b_vis := hS.b_vis
  b_visK := hS.b_visK
  low hj hg hm hH := by
    rw [nonTopMax_resync] at hm
    rw [capField_resync] at hH
    exact hS.low hj hg hm hH
  high := hS.high

/-- **The private fibre on source profiles**: admissible, synchronized, with complete cap
receipts for every persistent field and for the stored cutoff. -/
theorem LowRef.exists_private_lift_sync {j : ℕ} {S : R.TState j} (hS : L.TAdmissible S)
    (hs : Synchronized S.st) {v₁ : C.scheme.below (effC J j) → ExtOrd}
    (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁) {γ : ExtOrd}
    (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (v₁ d) γ = min (S.st.v d) γ) :
    ∃ S₁ : R.TState j, L.TAdmissible S₁ ∧ Synchronized S₁.st ∧ S₁.st.v = v₁ ∧
      (∀ d, min (S₁.st.u d) γ = min (S.st.u d) γ) ∧ R.CapReceipts γ S.st S₁.st ∧
      min S₁.b γ = min S.b γ := by
  obtain ⟨S₁, hS₁, hv, hu, hrec, hb, -⟩ := L.exists_private_lift hS hv₁ hγ hagree
  refine ⟨⟨resync S₁.st, S₁.b⟩, hS₁.resync, resync_synchronized hS₁.adm, hv, hu, ?_, hb⟩
  exact resync_capReceipts (R := R) hs hγ hu (fun d => by rw [hv]; exact hagree d) hrec

/-- **The request fibre on source profiles**. -/
theorem LowRef.exists_request_lift_sync {j : ℕ} {S : R.TState j} (hS : L.TAdmissible S)
    (hs : Synchronized S.st) {u₁ : P.scheme.below (effP nP j) → ExtOrd}
    (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁) {γ : ExtOrd}
    (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (u₁ d) γ = min (S.st.u d) γ) :
    ∃ S₁ : R.TState j, L.TAdmissible S₁ ∧ Synchronized S₁.st ∧ S₁.st.u = u₁ ∧
      (∀ d, min (S₁.st.v d) γ = min (S.st.v d) γ) ∧ R.CapReceipts γ S.st S₁.st ∧
      min S₁.b γ = min S.b γ := by
  obtain ⟨S₁, hS₁, hu, hv, hrec, hb, -⟩ := L.exists_request_lift hS hu₁ hγ hagree
  refine ⟨⟨resync S₁.st, S₁.b⟩, hS₁.resync, resync_synchronized hS₁.adm, hu, hv, ?_, hb⟩
  exact resync_capReceipts (R := R) hs hγ (fun d => by rw [hu]; exact hagree d) hv hrec

end Ref

end CappedDonor

end VaughtConjecture.Knight
