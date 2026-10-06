/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorFields
public import VaughtConjecture.Knight.PositiveNormalization

/-! # The synchronized source-profile family and its normalization (the source-family adapter)

The **source profiles** are the specialization of the receiving family of
`Knight/CappedDonorReceiving.lean` in which the two-component state is one field vector: the
persistent value of every *present* field is the `1`-visible rounding of its numerical value
(`Synchronized`), while the persistent values of *future* fields are retained as they are.  Such
a state is determined by its single source vector `State.sourceProfile` (numerical values at
present fields, persistent values at future fields): `persistent = R₁ ∘ sourceProfile`
(`Synchronized`, `synchronized_iff`).

This is a specialization of the source family only.  Arbitrary physical sections are **not**
required to satisfy it (a positive persistent shadow with a bottom numerical owner at an inactive
controller is a legitimate physical section but not a source profile); nothing here extracts a
source profile from a physical section, and no positive-continuability filtering is imposed.

* **Resynchronization** (`resync`): recompute the present persistent fields from the numerical
  values, retain the future ones.  It preserves admissibility (`Admissible.resync`) and makes any
  admissible state synchronized (`resync_synchronized`); when the numerical fields agree with a
  synchronized state below a permissible cap, the cap receipts of every persistent field survive
  resynchronization (`resync_capReceipts`).
* **Both same-grade fibres on source profiles** (`exists_private_lift_sync`,
  `exists_request_lift_sync`): the general fibres followed by resynchronization — the lifted
  state is admissible and synchronized, retains the prescription literally and the other section
  below the cap, and carries **complete cap receipts** for every persistent field, present or
  future.  At bottom cap the general fibres already resynchronize (`offState`).
* **Normalization preservation** (`mapState`, `Admissible.map`, `Synchronized.map`): applying a
  bottom-reflecting normalized witness `σ` with suppressor `gTop K`, `K` at least the grades
  currently present and at least `1` (the arity form `K ≥ J` is `Admissible.map_of_arity`), to
  every field —
  the shape of the incoming normalization maps (`FiniteOrbitEmbedding.interpolate`,
  `SourceBlockPadding.pad`; `Admissible.interpolate`, `Admissible.pad`) — preserves admissibility
  and synchronization.  The selector commutes with such maps (`cut_map`, `sel_map`), so the
  numerical relation is preserved exactly; supports are preserved because `σ` reflects bottom. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

namespace CappedDonor

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-! ## The source profile and synchronization -/

/-- A present request cell as a present field. -/
def reqCell {j : ℕ} (d : Cell P.scheme) (h : P.scheme.grade d ≤ j) : P.scheme.below (effP nP j) :=
  ⟨d, (present_req_iff j d).mpr h⟩

/-- A present private cell as a present field. -/
def privCell {j : ℕ} (d : Cell C.scheme) (h : C.scheme.grade d ≤ j) : C.scheme.below (effC J j) :=
  ⟨d, (present_priv_iff j d).mpr h⟩

/-- The single source field vector: numerical values at present fields, persistent values at
future fields. -/
noncomputable def State.sourceProfile {j : ℕ} (st : R.State j) (f : Field P C) : ExtOrd :=
  if h : f.grade ≤ j then st.numeric f h else st.persistent f

theorem State.sourceProfile_of_present {j : ℕ} (st : R.State j) {f : Field P C}
    (h : f.grade ≤ j) : st.sourceProfile f = st.numeric f h := by
  unfold State.sourceProfile; rw [dite_eq_left h]

theorem State.sourceProfile_of_future {j : ℕ} (st : R.State j) {f : Field P C}
    (h : ¬ f.grade ≤ j) : st.sourceProfile f = st.persistent f := by
  unfold State.sourceProfile; rw [dite_eq_right h]

/-- **Synchronized**: every persistent value is the `1`-visible rounding of the source vector. -/
def Synchronized {j : ℕ} (st : R.State j) : Prop :=
  ∀ f : Field P C, st.persistent f = extVisibilityReplace (st.sourceProfile f) 1 1

theorem Synchronized.shadowP {j : ℕ} {st : R.State j} (hs : Synchronized st)
    (d : P.scheme.below (effP nP j)) : st.shadowP d.1 = extVisibilityReplace (st.u d) 1 1 := by
  have h := hs (.req d.1)
  rw [st.sourceProfile_of_present (f := .req d.1) ((present_req_iff j d.1).mp d.2)] at h
  exact h

theorem Synchronized.shadowC {j : ℕ} {st : R.State j} (hs : Synchronized st)
    (d : C.scheme.below (effC J j)) : st.shadowC d.1 = extVisibilityReplace (st.v d) 1 1 := by
  have h := hs (.priv d.1)
  rw [st.sourceProfile_of_present (f := .priv d.1) ((present_priv_iff j d.1).mp d.2)] at h
  exact h

theorem Synchronized.shadowP' {j : ℕ} {st : R.State j} (hs : Synchronized st) (d : Cell P.scheme)
    (h : P.scheme.grade d ≤ j) : st.shadowP d = extVisibilityReplace (st.u (reqCell d h)) 1 1 :=
  hs.shadowP (reqCell d h)

theorem Synchronized.shadowC' {j : ℕ} {st : R.State j} (hs : Synchronized st) (d : Cell C.scheme)
    (h : C.scheme.grade d ≤ j) : st.shadowC d = extVisibilityReplace (st.v (privCell d h)) 1 1 :=
  hs.shadowC (privCell d h)

/-- Synchronization of an admissible state is the synchronization of its present cells. -/
theorem synchronized_iff {j : ℕ} {st : R.State j} (hst : R.Admissible st) :
    Synchronized st ↔
      (∀ d : P.scheme.below (effP nP j), st.shadowP d.1 = extVisibilityReplace (st.u d) 1 1) ∧
      ∀ d : C.scheme.below (effC J j), st.shadowC d.1 = extVisibilityReplace (st.v d) 1 1 := by
  refine ⟨fun hs => ⟨hs.shadowP, hs.shadowC⟩, fun ⟨hP, hC⟩ f => ?_⟩
  by_cases h : f.grade ≤ j
  · rw [st.sourceProfile_of_present h]
    cases f with
    | req d => exact hP ⟨d, (present_req_iff j d).mpr h⟩
    | priv d => exact hC ⟨d, (present_priv_iff j d).mpr h⟩
    | gate => exact hst.gate_vis.symm
  · rw [st.sourceProfile_of_future h]
    exact (hst.persistent_selfVis f).symm

/-! ## Resynchronization -/

/-- Recompute the present persistent fields from the numerical values; retain the future ones. -/
noncomputable def resync {j : ℕ} (st : R.State j) : R.State j where
  u := st.u
  v := st.v
  gate := st.gate
  shadowP d := if h : P.scheme.grade d ≤ j then
    extVisibilityReplace (st.u (reqCell d h)) 1 1 else st.shadowP d
  shadowC d := if h : C.scheme.grade d ≤ j then
    extVisibilityReplace (st.v (privCell d h)) 1 1 else st.shadowC d

theorem resync_shadowP_of_present {j : ℕ} (st : R.State j) (d : Cell P.scheme)
    (h : P.scheme.grade d ≤ j) :
    (resync st).shadowP d = extVisibilityReplace (st.u (reqCell d h)) 1 1 := by
  change (if h : P.scheme.grade d ≤ j then
    extVisibilityReplace (st.u (reqCell d h)) 1 1 else st.shadowP d) = _
  rw [dite_eq_left h]

theorem resync_shadowC_of_present {j : ℕ} (st : R.State j) (d : Cell C.scheme)
    (h : C.scheme.grade d ≤ j) :
    (resync st).shadowC d = extVisibilityReplace (st.v (privCell d h)) 1 1 := by
  change (if h : C.scheme.grade d ≤ j then
    extVisibilityReplace (st.v (privCell d h)) 1 1 else st.shadowC d) = _
  rw [dite_eq_left h]

theorem resync_shadowP_of_future {j : ℕ} (st : R.State j) {d : Cell P.scheme}
    (h : ¬ P.scheme.grade d ≤ j) : (resync st).shadowP d = st.shadowP d := by
  change (if h : P.scheme.grade d ≤ j then _ else st.shadowP d) = _
  rw [dite_eq_right h]

theorem resync_shadowC_of_future {j : ℕ} (st : R.State j) {d : Cell C.scheme}
    (h : ¬ C.scheme.grade d ≤ j) : (resync st).shadowC d = st.shadowC d := by
  change (if h : C.scheme.grade d ≤ j then _ else st.shadowC d) = _
  rw [dite_eq_right h]

/-- Resynchronization preserves every persistent support. -/
theorem resync_shadowP_ne_bot_iff {j : ℕ} {st : R.State j} (hst : R.Admissible st)
    (d : Cell P.scheme) : (resync st).shadowP d ≠ ⊥ ↔ st.shadowP d ≠ ⊥ := by
  by_cases h : P.scheme.grade d ≤ j
  · rw [resync_shadowP_of_present st d h]
    exact (not_congr (evr_eq_bot_iff 1 1)).trans (hst.shadowP_iff (reqCell d h)).symm
  · rw [resync_shadowP_of_future st h]

theorem resync_shadowC_ne_bot_iff {j : ℕ} {st : R.State j} (hst : R.Admissible st)
    (d : Cell C.scheme) : (resync st).shadowC d ≠ ⊥ ↔ st.shadowC d ≠ ⊥ := by
  by_cases h : C.scheme.grade d ≤ j
  · rw [resync_shadowC_of_present st d h]
    exact (not_congr (evr_eq_bot_iff 1 1)).trans (hst.shadowC_iff (privCell d h)).symm
  · rw [resync_shadowC_of_future st h]

/-- Resynchronization preserves admissibility. -/
theorem Admissible.resync {j : ℕ} {st : R.State j} (hst : R.Admissible st) :
    R.Admissible (resync st) where
  u_respects := hst.u_respects
  v_respects := hst.v_respects
  face := hst.face
  gate_vis := hst.gate_vis
  shadowP_vis d := by
    by_cases h : P.scheme.grade d ≤ j
    · rw [resync_shadowP_of_present st d h]
      exact TopSupport.selfVis_evr_self 1 _
    · rw [resync_shadowP_of_future st h]; exact hst.shadowP_vis d
  shadowC_vis d := by
    by_cases h : C.scheme.grade d ≤ j
    · rw [resync_shadowC_of_present st d h]
      exact TopSupport.selfVis_evr_self 1 _
    · rw [resync_shadowC_of_future st h]; exact hst.shadowC_vis d
  shadowP_iff d := by
    rw [resync_shadowP_of_present st d.1 ((present_req_iff j d.1).mp d.2)]
    exact not_congr (evr_eq_bot_iff 1 1)
  shadowC_iff d := by
    rw [resync_shadowC_of_present st d.1 ((present_priv_iff j d.1).mp d.2)]
    exact not_congr (evr_eq_bot_iff 1 1)
  support hg hc := by
    obtain ⟨href, hsupp⟩ := hst.support hg ((resync_shadowC_ne_bot_iff hst R.cap).mp hc)
    exact ⟨fun i => (resync_shadowC_ne_bot_iff hst _).mpr (href i),
      fun d => (resync_shadowP_ne_bot_iff hst d).trans (hsupp d)⟩
  relation := hst.relation

/-- The resynchronized state of an admissible state is synchronized. -/
theorem resync_synchronized {j : ℕ} {st : R.State j} (hst : R.Admissible st) :
    Synchronized (resync st) :=
  (synchronized_iff hst.resync).mpr
    ⟨fun d => resync_shadowP_of_present st d.1 ((present_req_iff j d.1).mp d.2),
      fun d => resync_shadowC_of_present st d.1 ((present_priv_iff j d.1).mp d.2)⟩

include R in
/-- The comparison cap of a nonempty cutoff is `1`-visible. -/
theorem selfVis_one_of_effC {j : ℕ} (hj : 1 ≤ j) {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) :
    SelfVis 1 γ := by
  have hJ : 1 ≤ J := (Nat.succ_pos _).trans_le (R.arity_lt.le.trans R.N_le)
  exact hγ.mono (le_min hj hJ)

include R in
/-- **Cap receipts survive resynchronization**: if the numerical fields of a new admissible state
agree below a permissible cap with those of a synchronized state, and the persistent fields carry
receipts, then the resynchronized new state carries receipts for every persistent field. -/
theorem resync_capReceipts {j : ℕ} {st st₁ : R.State j} (hs : Synchronized st) {γ : ExtOrd}
    (hγ : SelfVis (effC J j).2 γ) (hu : ∀ d, min (st₁.u d) γ = min (st.u d) γ)
    (hv : ∀ d, min (st₁.v d) γ = min (st.v d) γ) (hrec : R.CapReceipts γ st st₁) :
    R.CapReceipts γ st (resync st₁) := by
  obtain ⟨hg, hP, hC⟩ := hrec
  refine ⟨hg, fun d => ?_, fun d => ?_⟩
  · by_cases h : P.scheme.grade d ≤ j
    · have h1 : SelfVis 1 γ := selfVis_one_of_effC (R := R) ((P.scheme.grade_pos d).trans_le h) hγ
      rw [resync_shadowP_of_present st₁ d h, hs.shadowP' d h,
        ← evr_min_of_selfVis h1 le_rfl le_rfl, ← evr_min_of_selfVis h1 le_rfl le_rfl,
        hu (reqCell d h)]
    · rw [resync_shadowP_of_future st₁ h]; exact hP d
  · by_cases h : C.scheme.grade d ≤ j
    · have h1 : SelfVis 1 γ := selfVis_one_of_effC (R := R) ((C.scheme.grade_pos d).trans_le h) hγ
      rw [resync_shadowC_of_present st₁ d h, hs.shadowC' d h,
        ← evr_min_of_selfVis h1 le_rfl le_rfl, ← evr_min_of_selfVis h1 le_rfl le_rfl,
        hv (privCell d h)]
    · rw [resync_shadowC_of_future st₁ h]; exact hC d

/-! ## Both same-grade fibres on source profiles -/

/-- **The private fibre on source profiles**: the general private fibre followed by
resynchronization; the lift is admissible and synchronized, with complete cap receipts. -/
theorem exists_private_lift_sync {j : ℕ} {st : R.State j} (hst : R.Admissible st)
    (hs : Synchronized st) {v₁ : C.scheme.below (effC J j) → ExtOrd}
    (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁) {γ : ExtOrd}
    (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (v₁ d) γ = min (st.v d) γ) :
    ∃ st₁ : R.State j, R.Admissible st₁ ∧ Synchronized st₁ ∧ st₁.v = v₁ ∧
      (∀ d, min (st₁.u d) γ = min (st.u d) γ) ∧ R.CapReceipts γ st st₁ := by
  obtain ⟨st₁, hst₁, hv, hu, hrec, -⟩ := R.exists_private_lift hst hv₁ hγ hagree
  refine ⟨resync st₁, hst₁.resync, resync_synchronized hst₁, hv, hu, ?_⟩
  exact resync_capReceipts (R := R) hs hγ hu (fun d => by rw [hv]; exact hagree d) hrec

/-- **The request fibre on source profiles**: the general request fibre followed by
resynchronization; the lift is admissible and synchronized, with complete cap receipts. -/
theorem exists_request_lift_sync {j : ℕ} {st : R.State j} (hst : R.Admissible st)
    (hs : Synchronized st) {u₁ : P.scheme.below (effP nP j) → ExtOrd}
    (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁) {γ : ExtOrd}
    (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (u₁ d) γ = min (st.u d) γ) :
    ∃ st₁ : R.State j, R.Admissible st₁ ∧ Synchronized st₁ ∧ st₁.u = u₁ ∧
      (∀ d, min (st₁.v d) γ = min (st.v d) γ) ∧ R.CapReceipts γ st st₁ := by
  obtain ⟨st₁, hst₁, hu, hv, hrec, -⟩ := R.exists_request_lift hst hu₁ hγ hagree
  refine ⟨resync st₁, hst₁.resync, resync_synchronized hst₁, hu, hv, ?_⟩
  exact resync_capReceipts (R := R) hs hγ (fun d => by rw [hu]; exact hagree d) hv hrec

/-! ## Normalization preservation -/

/-- Apply a scalar map to every field of a state. -/
def mapState {j : ℕ} (σ : ExtOrd → ExtOrd) (st : R.State j) : R.State j where
  u d := σ (st.u d)
  v d := σ (st.v d)
  gate := σ st.gate
  shadowP d := σ (st.shadowP d)
  shadowC d := σ (st.shadowC d)

theorem sourceProfile_map (σ : ExtOrd → ExtOrd) {j : ℕ} (st : R.State j) (f : Field P C) :
    (mapState σ st).sourceProfile f = σ (st.sourceProfile f) := by
  by_cases h : f.grade ≤ j
  · rw [State.sourceProfile_of_present _ h, State.sourceProfile_of_present _ h]
    cases f <;> rfl
  · rw [State.sourceProfile_of_future _ h, State.sourceProfile_of_future _ h]
    cases f <;> rfl

section Map

variable {K : ℕ} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop K) σ)

include hσ

theorem map_comm {k : ℕ} (hk : k ≤ K) (x : ExtOrd) {i : ℕ} (hi : i ≤ k) :
    σ (extVisibilityReplace x k i) = extVisibilityReplace (σ x) k i :=
  hσ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi

theorem selfVis_map {k : ℕ} (hk : k ≤ K) {x : ExtOrd} (h : SelfVis k x) : SelfVis k (σ x) := by
  change extVisibilityReplace (σ x) k k = σ x
  rw [← map_comm hσ hk x le_rfl, h]

theorem map_ne_bot_iff (hbot : ∀ x, σ x = ⊥ → x = ⊥) (x : ExtOrd) : σ x ≠ ⊥ ↔ x ≠ ⊥ :=
  not_congr ⟨hbot x, fun h => by rw [h, hσ.bot]⟩

theorem map_sup (f : I → ExtOrd) :
    σ (Finset.univ.sup f) = Finset.univ.sup fun i => σ (f i) :=
  Finset.apply_sup_eq_sup_comp σ (fun _ _ => hσ.mono.map_max) hσ.bot

/-- The cut commutes with a normalized witness through `N`. -/
theorem cut_map (hN : N ≤ K) (v : R.Low → ExtOrd) : R.cut (fun d => σ (v d)) = σ (R.cut v) := by
  unfold cut
  rw [hσ.mono.map_min, map_sup hσ]
  congr 2
  funext i
  exact (map_comm hσ hN _ le_rfl).symm

/-- The selector commutes with a normalized witness through `N`. -/
theorem sel_map (hN : N ≤ K) (v : R.Low → ExtOrd) (d : Cell P.scheme) :
    R.sel (fun d => σ (v d)) d = σ (R.sel v d) := by
  by_cases h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤
  · rw [R.sel_of_proper h, R.sel_of_proper h, cut_map hσ hN, hσ.mono.map_min,
      map_comm hσ hN _ (R.poff_lt d h).le]
  by_cases hb : R.p d = ⊥
  · rw [R.sel_of_bot hb, R.sel_of_bot hb, hσ.bot]
  · have ht := not_not.mp fun ht => h ⟨hb, ht⟩
    rw [R.sel_of_top ht, R.sel_of_top ht, cut_map hσ hN]

/-- **Admissibility is preserved by every bottom-reflecting normalized witness through the grades
currently present** (and grade one, for the gate and the persistent fields): lawfulness by
`FiniteOrbitEmbedding.map_respects`, visibility and supports by commutation and bottom reflection,
the relation by `cut_map`/`sel_map` — which needs commutation through `N` only when the cap is
present, i.e. when `N` is among the present grades. -/
theorem Admissible.map {j : ℕ} (hK : (effC J j).2 ≤ K) (h1 : 1 ≤ K)
    (hbot : ∀ x, σ x = ⊥ → x = ⊥) {st : R.State j} (hst : R.Admissible st) :
    R.Admissible (mapState σ st) where
  u_respects := FiniteOrbitEmbedding.map_respects hst.u_respects
    (fun d => d.2.2.trans ((R.effP_snd_le_effC j).trans hK)) hσ hbot
  v_respects := FiniteOrbitEmbedding.map_respects hst.v_respects (fun d => d.2.2.trans hK) hσ hbot
  face a h := congrArg σ (hst.face a h)
  gate_vis := selfVis_map hσ h1 hst.gate_vis
  shadowP_vis d := selfVis_map hσ h1 (hst.shadowP_vis d)
  shadowC_vis d := selfVis_map hσ h1 (hst.shadowC_vis d)
  shadowP_iff d := (map_ne_bot_iff hσ hbot _).trans ((hst.shadowP_iff d).trans
    (map_ne_bot_iff hσ hbot _).symm)
  shadowC_iff d := (map_ne_bot_iff hσ hbot _).trans ((hst.shadowC_iff d).trans
    (map_ne_bot_iff hσ hbot _).symm)
  support hg hc := by
    obtain ⟨href, hsupp⟩ := hst.support ((map_ne_bot_iff hσ hbot _).mp hg)
      ((map_ne_bot_iff hσ hbot _).mp hc)
    exact ⟨fun i => (map_ne_bot_iff hσ hbot _).mpr (href i),
      fun d => (map_ne_bot_iff hσ hbot _).trans (hsupp d)⟩
  relation hj hg hc d := by
    have hN : N ≤ K := (le_min hj R.N_le).trans hK
    have h := hst.relation hj ((map_ne_bot_iff hσ hbot _).mp hg)
      ((map_ne_bot_iff hσ hbot _).mp hc) d
    change min (σ (st.u d)) (R.cut (fun e => σ (R.lowC hj st.v e))) =
      R.sel (fun e => σ (R.lowC hj st.v e)) d.1
    rw [cut_map hσ hN, sel_map hσ hN, ← hσ.mono.map_min, h]

/-- The arity form: a witness through the whole private arity. -/
theorem Admissible.map_of_arity (hK : J ≤ K) (hbot : ∀ x, σ x = ⊥ → x = ⊥) {j : ℕ}
    {st : R.State j} (hst : R.Admissible st) : R.Admissible (mapState σ st) :=
  hst.map hσ ((min_le_right _ _).trans hK)
    ((Nat.succ_pos _).trans_le (R.arity_lt.le.trans (R.N_le.trans hK))) hbot

/-- Synchronization is preserved by every normalized witness through a grade at least `1`. -/
theorem Synchronized.map (hK : 1 ≤ K) {j : ℕ} {st : R.State j} (hs : Synchronized st) :
    Synchronized (mapState σ st) := by
  intro f
  rw [sourceProfile_map σ, ← map_comm hσ hK _ le_rfl, ← hs f]
  cases f <;> rfl

end Map

/-- The incoming block interpolation preserves admissibility. -/
theorem Admissible.interpolate {I' : Type*} [Fintype I'] {K : ℕ} (hK : J ≤ K)
    (μ ν : I' → Ordinal.{0}) (hν : ∀ i, limitPart (ν i) = ν i) {j : ℕ} {st : R.State j}
    (hst : R.Admissible st) :
    R.Admissible (mapState (FiniteOrbitEmbedding.interpolate K μ ν) st) :=
  hst.map_of_arity (FiniteOrbitEmbedding.interpolate_witness K μ ν hν) hK
    (FiniteOrbitEmbedding.interpolate_reflects_bottom K μ ν)

/-- Source-block padding preserves admissibility. -/
theorem Admissible.pad {j : ℕ} {st : R.State j} (hst : R.Admissible st) :
    R.Admissible (mapState SourceBlockPadding.pad st) :=
  hst.map_of_arity (SourceBlockPadding.pad_step J).normalizedWitness le_rfl
    SourceBlockPadding.pad_reflects_bottom

end Ref

end CappedDonor

end VaughtConjecture.Knight
