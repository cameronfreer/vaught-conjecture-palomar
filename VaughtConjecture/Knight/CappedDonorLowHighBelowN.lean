/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorRetarget
public import VaughtConjecture.Knight.CappedDonorRelease

/-! # The two-threshold fibres below the high grade (audit16 §§3, 5; note §§4, 6)

Both same-grade fibres of the two-threshold family at cutoffs `j < N`, with **every future field
retained literally at a positive cap** and the stored cutoff repaired by the policy.

* **Below `K`** neither numerical condition is present: the receiving fibres with the stored
  cutoff unchanged (`exists_private_lift_lt_K`, `exists_request_lift_lt_K`).
* **At bottom cap** the gate is switched off and the stored cutoff set to bottom
  (`exists_private_lift_bot`, `exists_request_lift_bot`).
* **Between `K` and `N`** (`exists_private_lift_belowN`, `exists_request_lift_belowN`): the
  receiving fibre installs the face by old bountifulness; the cap field `H` and every other future
  field are kept literally, and the stored cutoff becomes `policy b H γ`.  If the new LOW
  condition activates, the **activation barrier** (`policy_barrier`, `barrier`) shows that it is
  the clipped branch below the cap, every new donor non-top value is pinned below the cap, so the
  old LOW condition was active as well.  Then, with the new floor `max b' (e v₁)`:
  - private context prescribed: if the floor is at most the cap, the **floor cap** (`floor_min`)
    shows the lifted request section already satisfies LOW; otherwise every request top reaches the
    cap and the exact old-face restoration (`exists_retarget_restore`) raises the tops to the floor
    with every non-top value literal;
  - request prescribed: if the frontier is at most the cap, the floor cap suffices; otherwise
    every prescribed top reaches the cap, SHIELD holds because every protected non-top value is
    strictly below the clipped cutoff, and the exact frontier release (`exists_release`) makes
    the frontier exactly the cap.

The negative control of audit16 §6 (unconditional clipping can activate a condition disabled by
`H ≤ b`) is exactly why the policy keeps `b` when `H ≤ b`. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

namespace CappedDonor

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-! ## Helpers on the non-top maximum -/

theorem State.u_le_nonTopMax {j : ℕ} (st : R.State j) (d : P.scheme.below (effP nP j))
    (hd : R.p d.1 ≠ ⊤) : st.u d ≤ st.nonTopMax := by
  have h := st.le_nonTopMax hd
  rwa [st.sourceProfile_req_of_present d.1 ((present_req_iff j d.1).mp d.2)] at h

/-- Two states with the same request shadows and the same non-top request values have the same
non-top maximum. -/
theorem State.nonTopMax_eq_of_pinned {j : ℕ} {st st₁ : R.State j} (hP : st₁.shadowP = st.shadowP)
    (hu : ∀ d, R.p d.1 ≠ ⊤ → st₁.u d = st.u d) : st₁.nonTopMax = st.nonTopMax := by
  apply State.nonTopMax_congr
  intro d hd
  by_cases h : P.scheme.grade d ≤ j
  · rw [st₁.sourceProfile_req_of_present d h, st.sourceProfile_req_of_present d h]
    exact hu (reqCell d h) hd
  · rw [st₁.sourceProfile_req_of_future d h, st.sourceProfile_req_of_future d h, hP]

/-- A non-top maximum strictly below a value at most the cap pins every non-top request value
of a cap-equivalent state. -/
theorem State.pin_of_nonTopMax_lt {j : ℕ} {st st₁ : R.State j} {γ b' : ExtOrd}
    (hagree : ∀ d, min (st₁.u d) γ = min (st.u d) γ) (hm : st₁.nonTopMax < b') (hb' : b' ≤ γ) :
    ∀ d, R.p d.1 ≠ ⊤ → st₁.u d = st.u d := fun d hd =>
  (eq_of_capAgree_of_lt (hagree d) (((st₁.u_le_nonTopMax d hd).trans_lt hm).trans_le hb')).symm

variable {K : ℕ} (L : R.LowRef K)

/-! ## Admissibility in the vacuous cases -/

/-- Below `K` neither condition is present. -/
theorem LowRef.tadmissible_of_lt_K {j : ℕ} (hj : j < K) {st : R.State j} (hst : R.Admissible st)
    {b : ExtOrd} (hb : SelfVis 1 b) : L.TAdmissible ⟨st, b⟩ where
  adm := hst
  b_vis := hb
  b_visK hK := absurd hK (not_le.mpr hj)
  low hK := absurd hK (not_le.mpr hj)
  high hN := absurd hN (not_le.mpr (hj.trans L.K_lt_N))

/-- With the gate off neither condition is imposed. -/
theorem LowRef.tadmissible_of_gate_bot {j : ℕ} {st : R.State j} (hst : R.Admissible st)
    (hg : st.gate = ⊥) {b : ExtOrd} (hb : SelfVis 1 b) (hbK : K ≤ j → SelfVis K b) :
    L.TAdmissible ⟨st, b⟩ where
  adm := hst
  b_vis := hb
  b_visK := hbK
  low _ hne := absurd hg hne
  high _ hne := absurd hg hne

/-! ## Below `K` and at bottom cap -/

theorem LowRef.exists_private_lift_lt_K {j : ℕ} (hj : j < K) {S : R.TState j}
    (hS : L.TAdmissible S) {v₁ : C.scheme.below (effC J j) → ExtOrd}
    (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁) {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ)
    (hagree : ∀ d, min (v₁ d) γ = min (S.st.v d) γ) :
    ∃ S₁ : R.TState j, L.TAdmissible S₁ ∧ S₁.st.v = v₁ ∧
      (∀ d, min (S₁.st.u d) γ = min (S.st.u d) γ) ∧ R.CapReceipts γ S.st S₁.st ∧
      min S₁.b γ = min S.b γ ∧
      (γ ≠ ⊥ → S₁.st.gate = S.st.gate ∧ S₁.st.shadowP = S.st.shadowP ∧
        S₁.st.shadowC = S.st.shadowC) := by
  obtain ⟨st₁, hst₁, hv, hu, hrec, hlit⟩ := R.exists_private_lift hS.adm hv₁ hγ hagree
  exact ⟨⟨st₁, S.b⟩, L.tadmissible_of_lt_K hj hst₁ hS.b_vis, hv, hu, hrec, rfl, hlit⟩

theorem LowRef.exists_request_lift_lt_K {j : ℕ} (hj : j < K) {S : R.TState j}
    (hS : L.TAdmissible S) {u₁ : P.scheme.below (effP nP j) → ExtOrd}
    (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁) {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ)
    (hagree : ∀ d, min (u₁ d) γ = min (S.st.u d) γ) :
    ∃ S₁ : R.TState j, L.TAdmissible S₁ ∧ S₁.st.u = u₁ ∧
      (∀ d, min (S₁.st.v d) γ = min (S.st.v d) γ) ∧ R.CapReceipts γ S.st S₁.st ∧
      min S₁.b γ = min S.b γ ∧
      (γ ≠ ⊥ → S₁.st.gate = S.st.gate ∧ S₁.st.shadowP = S.st.shadowP ∧
        S₁.st.shadowC = S.st.shadowC) := by
  obtain ⟨st₁, hst₁, hu, hv, hrec, hlit⟩ := R.exists_request_lift hS.adm hu₁ hγ hagree
  exact ⟨⟨st₁, S.b⟩, L.tadmissible_of_lt_K hj hst₁ hS.b_vis, hu, hv, hrec, rfl, hlit⟩

/-- At bottom cap: the gate off, the stored cutoff bottom. -/
theorem LowRef.exists_private_lift_bot {j : ℕ} {S : R.TState j} (hS : L.TAdmissible S)
    {v₁ : C.scheme.below (effC J j) → ExtOrd} (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁) :
    ∃ S₁ : R.TState j, L.TAdmissible S₁ ∧ S₁.st.v = v₁ ∧ S₁.b = ⊥ := by
  obtain ⟨u₁, hu₁, -, hface⟩ := R.exists_installP hS.adm.u_respects hv₁ (selfVis_bot _)
    (fun _ _ => by rw [min_bot_right, min_bot_right])
  exact ⟨⟨R.offState S.st u₁ v₁, ⊥⟩, L.tadmissible_of_gate_bot (R.admissible_off hS.adm hu₁ hv₁
    hface) rfl (selfVis_bot 1) (fun _ => selfVis_bot K), rfl, rfl⟩

theorem LowRef.exists_request_lift_bot {j : ℕ} {S : R.TState j} (hS : L.TAdmissible S)
    {u₁ : P.scheme.below (effP nP j) → ExtOrd}
    (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁) :
    ∃ S₁ : R.TState j, L.TAdmissible S₁ ∧ S₁.st.u = u₁ ∧ S₁.b = ⊥ := by
  obtain ⟨v₀, hv₀, -, hface⟩ := R.exists_installC hS.adm.v_respects hu₁ (selfVis_bot _)
    (fun _ _ => by rw [min_bot_right, min_bot_right])
  exact ⟨⟨R.offState S.st u₁ v₀, ⊥⟩, L.tadmissible_of_gate_bot (R.admissible_off hS.adm hu₁ hv₀
    hface) rfl (selfVis_bot 1) (fun _ => selfVis_bot K), rfl, rfl⟩

/-! ## The activation barrier between `K` and `N` -/

/-- **The activation barrier** (audit16 (3)): if the policy cutoff activates LOW in a state whose
request section agrees with the old one below the cap and whose shadows are the old ones, then it
is the clipped cutoff, at most the cap, the non-top maxima coincide, and the old LOW antecedent
held. -/
theorem barrier {j : ℕ} (hjN : j < N) {S : R.TState j} {st₁ : R.State j}
    (hP : st₁.shadowP = S.st.shadowP) (hC : st₁.shadowC = S.st.shadowC) {γ : ExtOrd}
    (hagree : ∀ d, min (st₁.u d) γ = min (S.st.u d) γ)
    (hm : st₁.nonTopMax < policy S.b S.st.capField γ)
    (hH : policy S.b S.st.capField γ < st₁.capField) :
    st₁.nonTopMax = S.st.nonTopMax ∧ S.st.nonTopMax < S.b ∧ S.b < S.st.capField ∧
      policy S.b S.st.capField γ ≤ γ := by
  have hcapF : st₁.capField = S.st.capField := by
    rw [st₁.capField_of_future (not_le.mpr hjN), S.st.capField_of_future (not_le.mpr hjN), hC]
  rw [hcapF] at hH
  obtain ⟨-, hb'γ, hbH⟩ := policy_barrier hH
  have hmeq : st₁.nonTopMax = S.st.nonTopMax :=
    State.nonTopMax_eq_of_pinned hP (State.pin_of_nonTopMax_lt hagree hm hb'γ)
  exact ⟨hmeq, hmeq ▸ hm.trans_le (policy_le _ _ _), hbH, hb'γ⟩

/-! ## The private fibre between `K` and `N` -/

/-- **The private fibre between `K` and `N`** (audit16 §3, note §4.1): every future field, the
gate and the shadows retained literally; the stored cutoff repaired by the policy; the request
tops raised to the new floor by exact old-face restoration when the floor exceeds the cap. -/
theorem LowRef.exists_private_lift_belowN {j : ℕ} (hj : K ≤ j) (hjN : j < N) {S : R.TState j}
    (hS : L.TAdmissible S) {v₁ : C.scheme.below (effC J j) → ExtOrd}
    (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁) {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ)
    (hbot : γ ≠ ⊥) (hagree : ∀ d, min (v₁ d) γ = min (S.st.v d) γ) :
    ∃ S₁ : R.TState j, L.TAdmissible S₁ ∧ S₁.st.v = v₁ ∧
      (∀ d, min (S₁.st.u d) γ = min (S.st.u d) γ) ∧ min S₁.b γ = min S.b γ ∧
      S₁.st.gate = S.st.gate ∧ S₁.st.shadowP = S.st.shadowP ∧ S₁.st.shadowC = S.st.shadowC := by
  obtain ⟨st₁, hst₁, hv, hu, -, hlit⟩ := R.exists_private_lift hS.adm hv₁ hγ hagree
  obtain ⟨hg, hP, hC⟩ := hlit hbot
  have hnotN : ¬ N ≤ j := not_le.mpr hjN
  have hγK : SelfVis K γ := L.selfVis_K_of_effC hj hγ
  have hb'vis : SelfVis K (policy S.b S.st.capField γ) := policy_selfVis (hS.b_visK hj) hγK
  have hb'min : min (policy S.b S.st.capField γ) γ = min S.b γ := policy_min _ _ _
  have hfloor : min (max (policy S.b S.st.capField γ) (L.eC hj v₁)) γ =
      min (max S.b (L.eC hj S.st.v)) γ :=
    floor_min hb'min (L.eC_agree hj hγK hagree)
  by_cases hact : st₁.gate ≠ ⊥ ∧ st₁.nonTopMax < policy S.b S.st.capField γ ∧
      policy S.b S.st.capField γ < st₁.capField ∧ γ < max (policy S.b S.st.capField γ) (L.eC hj v₁)
  · -- the floor exceeds the cap: retarget the request tops
    obtain ⟨hg₁, hm, hH, hη⟩ := hact
    obtain ⟨-, hm₀, hbH₀, hb'γ⟩ := barrier hjN hP hC hu hm hH
    have hlow₀ := hS.low hj (by rw [← hg]; exact hg₁) hm₀ hbH₀
    have hγfloor : γ ≤ max S.b (L.eC hj S.st.v) := by
      rw [min_eq_right hη.le] at hfloor
      exact min_eq_right_iff.mp hfloor.symm
    have htopγ : ∀ d : P.scheme.below (effP nP j), R.p d.1 = ⊤ → γ ≤ st₁.u d := fun d hd =>
      le_of_capAgree_of_le (hu d).symm (hγfloor.trans (hlow₀ d.1 hd))
    have hRD : RetargetData (R := R) (K := K) st₁.u (policy S.b S.st.capField γ)
        (max (policy S.b S.st.capField γ) (L.eC hj v₁)) :=
      ⟨hst₁.u_respects, hb'vis, bot_lt_iff_ne_bot.mpr fun h => absurd (h ▸ hm) not_lt_bot,
        fun d hd => (st₁.u_le_nonTopMax d hd).trans_lt hm, fun d hd => hb'γ.trans (htopγ d hd),
        TopSupport.selfVis_max_of hb'vis (L.eC_selfVis hj hv₁), le_max_left _ _⟩
    obtain ⟨u', hu', hnon', htop', hface'⟩ := exists_retarget_restore L hj hRD hv₁
      (fun a h _ => by rw [hst₁.face a h, hv])
      (fun a h ha => by
        have h1 : γ ≤ st₁.u (R.reqFace a h) := htopγ _ ha
        rw [hst₁.face a h, hv] at h1
        exact max_le (hb'γ.trans h1) (L.eC_le_top hj hv₁ a ha))
    have hcap₂ : ∀ d, min (u' d) γ = min (S.st.u d) γ := by
      intro d
      by_cases hd : R.p d.1 = ⊤
      · rw [min_eq_right ((htop' d hd).trans' hη.le)]
        exact (min_eq_right (hγfloor.trans (hlow₀ d.1 hd))).symm
      · rw [hnon' d hd, hu d]
    have hadm₂ : R.Admissible ⟨u', v₁, S.st.gate, S.st.shadowP, S.st.shadowC⟩ :=
      R.admissible_persist hS.adm hbot hu' hv₁ hcap₂ hagree hface' (fun hN => absurd hN hnotN)
    refine ⟨⟨⟨u', v₁, S.st.gate, S.st.shadowP, S.st.shadowC⟩, policy S.b S.st.capField γ⟩,
      ⟨hadm₂, hb'vis.mono L.K_pos, fun _ => hb'vis, fun _ _ _ _ t ht => htop' _ ht,
        fun hN => absurd hN hnotN⟩, rfl, hcap₂,
      hb'min, rfl, rfl, rfl⟩
  · -- the floor is at most the cap, or LOW is inactive: the lifted state with the policy cutoff
    refine ⟨⟨st₁, policy S.b S.st.capField γ⟩,
      ⟨hst₁, hb'vis.mono L.K_pos, fun _ => hb'vis, ?_, fun hN => absurd hN hnotN⟩, hv, hu, hb'min,
      hg, hP, hC⟩
    intro hj₁ hg₁ hm hH t ht
    obtain ⟨-, hm₀, hbH₀, hb'γ⟩ := barrier hjN hP hC hu hm hH
    have hlow₀ := hS.low hj (by rw [← hg]; exact hg₁) hm₀ hbH₀ t ht
    have hη : ¬ γ < max (policy S.b S.st.capField γ) (L.eC hj v₁) := fun h =>
      hact ⟨hg₁, hm, hH, h⟩
    change max _ (L.eC hj₁ st₁.v) ≤ st₁.u (reqCell t _)
    rw [hv]
    calc max (policy S.b S.st.capField γ) (L.eC hj₁ v₁)
        = min (max (policy S.b S.st.capField γ) (L.eC hj v₁)) γ :=
          (min_eq_left (not_lt.mp hη)).symm
      _ = min (max S.b (L.eC hj S.st.v)) γ := hfloor
      _ ≤ min (S.st.u (reqCell t ((L.top_grade t ht).trans hj))) γ :=
          min_le_min_right _ hlow₀
      _ = min (st₁.u (reqCell t ((L.top_grade t ht).trans hj))) γ := (hu _).symm
      _ ≤ st₁.u (reqCell t _) := min_le_left _ _

/-! ## The request fibre between `K` and `N` -/

/-- **The request fibre between `K` and `N`** (audit16 §3, note §4.2): every future field, the
gate and the shadows retained literally; the stored cutoff repaired by the policy; the private
frontier released exactly to the cap when it exceeds the cap under an active LOW condition. -/
theorem LowRef.exists_request_lift_belowN {j : ℕ} (hj : K ≤ j) (hjN : j < N) {S : R.TState j}
    (hS : L.TAdmissible S) {u₁ : P.scheme.below (effP nP j) → ExtOrd}
    (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁) {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ)
    (hbot : γ ≠ ⊥) (hagree : ∀ d, min (u₁ d) γ = min (S.st.u d) γ) :
    ∃ S₁ : R.TState j, L.TAdmissible S₁ ∧ S₁.st.u = u₁ ∧
      (∀ d, min (S₁.st.v d) γ = min (S.st.v d) γ) ∧ min S₁.b γ = min S.b γ ∧
      S₁.st.gate = S.st.gate ∧ S₁.st.shadowP = S.st.shadowP ∧ S₁.st.shadowC = S.st.shadowC := by
  obtain ⟨st₁, hst₁, hu, hv, -, hlit⟩ := R.exists_request_lift hS.adm hu₁ hγ hagree
  obtain ⟨hg, hP, hC⟩ := hlit hbot
  have hnotN : ¬ N ≤ j := not_le.mpr hjN
  have hγK : SelfVis K γ := L.selfVis_K_of_effC hj hγ
  have hagree₁ : ∀ d, min (st₁.u d) γ = min (S.st.u d) γ := by rw [hu]; exact hagree
  have hb'vis : SelfVis K (policy S.b S.st.capField γ) := policy_selfVis (hS.b_visK hj) hγK
  have hb'min : min (policy S.b S.st.capField γ) γ = min S.b γ := policy_min _ _ _
  have hfloor : min (max (policy S.b S.st.capField γ) (L.eC hj st₁.v)) γ =
      min (max S.b (L.eC hj S.st.v)) γ :=
    floor_min hb'min (L.eC_agree hj hγK hv)
  by_cases hact : st₁.gate ≠ ⊥ ∧ st₁.nonTopMax < policy S.b S.st.capField γ ∧
      policy S.b S.st.capField γ < st₁.capField ∧ γ < L.eC hj st₁.v
  · -- the frontier exceeds the cap under an active condition: release it exactly to the cap
    obtain ⟨hg₁, hm, hH, he⟩ := hact
    obtain ⟨-, hm₀, hbH₀, hb'γ⟩ := barrier hjN hP hC hagree₁ hm hH
    have hlow₀ := hS.low hj (by rw [← hg]; exact hg₁) hm₀ hbH₀
    have hγfloor : γ ≤ max S.b (L.eC hj S.st.v) := by
      rw [min_eq_right (he.le.trans (le_max_right _ _))] at hfloor
      exact min_eq_right_iff.mp hfloor.symm
    have hshield : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
        R.p a.1 ≠ ⊤ → st₁.v (R.privFace a h) < γ := by
      intro a h ha
      rw [← hst₁.face a h]
      exact ((st₁.u_le_nonTopMax _ ha).trans_lt hm).trans_le hb'γ
    obtain ⟨v', hv', hface', hcap', -, -, he'⟩ :=
      L.exists_release hj hst₁.v_respects hγ hbot he hshield
    have hcap₂ : ∀ d, min (v' d) γ = min (S.st.v d) γ := fun d => (hcap' d).trans (hv d)
    have hadm₂ : R.Admissible ⟨st₁.u, v', S.st.gate, S.st.shadowP, S.st.shadowC⟩ :=
      R.admissible_persist hS.adm hbot hst₁.u_respects hv' hagree₁ hcap₂
        (fun a h => (hst₁.face a h).trans (hface' a h).symm) (fun hN => absurd hN hnotN)
    refine ⟨⟨⟨st₁.u, v', S.st.gate, S.st.shadowP, S.st.shadowC⟩, policy S.b S.st.capField γ⟩,
      ⟨hadm₂, hb'vis.mono L.K_pos, fun _ => hb'vis, ?_, fun hN => absurd hN hnotN⟩, hu, hcap₂,
      hb'min, rfl, rfl, rfl⟩
    intro hj₁ _ _ _ t ht
    change max _ (L.eC hj₁ v') ≤ st₁.u (reqCell t _)
    rw [he', max_eq_right hb'γ]
    exact le_of_capAgree_of_le (hagree₁ _).symm (hγfloor.trans (hlow₀ t ht))
  · -- the frontier is at most the cap, or LOW is inactive
    refine ⟨⟨st₁, policy S.b S.st.capField γ⟩,
      ⟨hst₁, hb'vis.mono L.K_pos, fun _ => hb'vis, ?_, fun hN => absurd hN hnotN⟩, hu, hv, hb'min,
      hg, hP, hC⟩
    intro hj₁ hg₁ hm hH t ht
    obtain ⟨-, hm₀, hbH₀, hb'γ⟩ := barrier hjN hP hC hagree₁ hm hH
    have hlow₀ := hS.low hj (by rw [← hg]; exact hg₁) hm₀ hbH₀ t ht
    have he : ¬ γ < L.eC hj st₁.v := fun h => hact ⟨hg₁, hm, hH, h⟩
    change max _ (L.eC hj₁ st₁.v) ≤ st₁.u (reqCell t _)
    calc max (policy S.b S.st.capField γ) (L.eC hj₁ st₁.v)
        = min (max (policy S.b S.st.capField γ) (L.eC hj st₁.v)) γ :=
          (min_eq_left (max_le hb'γ (not_lt.mp he))).symm
      _ = min (max S.b (L.eC hj S.st.v)) γ := hfloor
      _ ≤ min (S.st.u (reqCell t ((L.top_grade t ht).trans hj))) γ :=
          min_le_min_right _ hlow₀
      _ = min (st₁.u (reqCell t ((L.top_grade t ht).trans hj))) γ := (hagree₁ _).symm
      _ ≤ st₁.u (reqCell t _) := min_le_left _ _

end Ref

end CappedDonor

end VaughtConjecture.Knight
