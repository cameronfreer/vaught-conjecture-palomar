/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorAdmission
public import VaughtConjecture.Knight.CappedDonorNormalization
public import VaughtConjecture.Knight.CappedDonorLowHighNormalization
public import VaughtConjecture.Knight.CanonicalPairedProfiles

/-! # The ordinary final catalogue at the threshold cutoff

The final weighted layer of the upper-only receiver (newapproach16 new31 §4) indexes its
controllers by **ordinary** admitted sources at cutoff `N`: complete `Field` vectors that are
source profiles of synchronized `R.Admissible` states with an `N`-visible gate.  This is not the
two-threshold (`LowRef`) catalogue: no stored cutoff and no LOW clause appear, and gate-off states
are included.  This file defines that family and banks its closure properties from the existing
normalization and fibre results, with complete-field receipts:

* `Admitted`: the predicate; `one_le_N`.
* `Admitted.normalize`, `Admitted.cap` (positive `N`-visible caps), `Admitted.zero`.
* `Admitted.private_repair`: the ordinary private fibre at a positive `N`-visible cap keeps the
  gate literally (hence `N`-visible), installs the prescription exactly, and retains every
  complete-field `γ`-cap — present fields numerically, future fields persistently.
* `Admitted.exists_terminal`: **terminal insertion** — cap the literal tops into a fresh proper
  terminal block above every proper value and above a prescribed cut, so the capped source is
  admitted, proper, prefix-preserving below the cut and literal on every proper field; its
  canonical normalization is an admitted
  member of the finite canonical inventory, and one witness through `N` (the right-filled decoder
  followed by whole-block collapse) reads every original field back exactly, literal tops
  included.
* `Catalogue`, `catalogue_finite`: the canonical admitted family is finite.

Nothing here asserts admission of an arbitrary physical section or any upward admission. -/

@[expose] public section

namespace VaughtConjecture.Knight.CappedDonor.Ref

open Transform Value ExtOrd
noncomputable section

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

variable (R) in
/-- **Ordinary admission at the threshold cutoff**: the complete source vectors of synchronized
admissible states at cutoff `N` whose gate is `N`-visible. -/
def Admitted (a : Field P C → ExtOrd) : Prop :=
  ∃ st : R.State N, R.Admissible st ∧ Synchronized st ∧ SelfVis N st.gate ∧ st.sourceProfile = a

theorem one_le_N (R : Ref I nP N J P C) : 1 ≤ N := by
  have := R.arity_lt
  omega

/-! ## Closure -/

/-- Canonical normalization preserves admission. -/
theorem Admitted.normalize {a : Field P C → ExtOrd} (h : R.Admitted a) :
    R.Admitted (PairedSlotEncoding.normalize N a) := by
  obtain ⟨st, hst, hs, hg, rfl⟩ := h
  exact ⟨normalizeState st, normalizeState_admissible R.one_le_N hst,
    normalizeState_synchronized R.one_le_N hs, selfVis_map st.encoder_witness le_rfl hg,
    funext fun f => sourceProfile_normalizeState st f⟩

/-- Positive `N`-visible caps preserve admission. -/
theorem Admitted.cap {a : Field P C → ExtOrd} (h : R.Admitted a) {β : ExtOrd}
    (hβ : SelfVis N β) (hβbot : β ≠ ⊥) : R.Admitted (fun f => min (a f) β) := by
  obtain ⟨st, hst, hs, hg, rfl⟩ := h
  exact ⟨mapState (fun x => min x β) st,
    hst.map (capWitness hβ hβbot) (min_le_left _ _) R.one_le_N (capWitness_reflects_bottom hβbot),
    hs.map (capWitness hβ hβbot) R.one_le_N, selfVis_map (capWitness hβ hβbot) le_rfl hg,
    funext fun f => sourceProfile_map _ st f⟩

variable (R) in
/-- The zero vector is admitted (the all-bottom state, gate off). -/
theorem Admitted.zero : R.Admitted (fun _ => ⊥) :=
  ⟨zeroState R N, zeroState_admissible N, zeroState_synchronized N,
    extVisibilityReplace_bot _ _, funext (zeroState_sourceProfile N)⟩

/-- **Private-repair closure with complete-field receipts.**  A lawful private prescription
agreeing with an admitted source below a positive `N`-visible cap is installed exactly in an
admitted source that keeps every complete-field `γ`-cap: present fields numerically, future
fields persistently, the gate literally. -/
theorem Admitted.private_repair {a : Field P C → ExtOrd} (h : R.Admitted a)
    {v₁ : C.scheme.below (effC J N) → ExtOrd} (hv₁ : RespectsSemanticsBelow C.rows (effC J N) v₁)
    {γ : ExtOrd} (hγ : SelfVis N γ) (hγbot : γ ≠ ⊥)
    (hagree : ∀ d, min (v₁ d) γ = min (a (.priv d.1)) γ) :
    ∃ b : Field P C → ExtOrd, R.Admitted b ∧
      (∀ d : C.scheme.below (effC J N), b (.priv d.1) = v₁ d) ∧
      ∀ f, min (b f) γ = min (a f) γ := by
  obtain ⟨st, hst, hs, hg, rfl⟩ := h
  have hγ' : SelfVis (effC J N).2 γ := selfVis_mono hγ (min_le_left _ _)
  have hagree' : ∀ d, min (v₁ d) γ = min (st.v d) γ := fun d => by
    rw [hagree d, st.sourceProfile_of_present (f := .priv d.1) ((present_priv_iff N d.1).mp d.2)]
    rfl
  obtain ⟨st₁, hst₁, hv, hu, hrec, hlit⟩ := R.exists_private_lift hst hv₁ hγ' hagree'
  obtain ⟨hgate, -, -⟩ := hlit hγbot
  have hrec' := resync_capReceipts (R := R) hs hγ' hu (fun d => by rw [hv]; exact hagree' d) hrec
  refine ⟨(resync st₁).sourceProfile,
    ⟨resync st₁, hst₁.resync, resync_synchronized hst₁, ?_, rfl⟩, ?_, ?_⟩
  · change SelfVis N st₁.gate
    rw [hgate]
    exact hg
  · intro d
    rw [State.sourceProfile_of_present _ ((present_priv_iff N d.1).mp d.2)]
    change st₁.v ⟨d.1, _⟩ = v₁ d
    rw [hv]
    exact congrArg v₁ (Subtype.ext rfl)
  · intro f
    by_cases hf : f.grade ≤ N
    · rw [State.sourceProfile_of_present _ hf, State.sourceProfile_of_present _ hf]
      cases f with
      | req d => exact hu _
      | priv d =>
          change min (st₁.v _) γ = min (st.v _) γ
          rw [hv]
          exact hagree' _
      | gate =>
          change min st₁.gate γ = min st.gate γ
          rw [hgate]
    · rw [State.sourceProfile_of_future _ hf, State.sourceProfile_of_future _ hf]
      exact (capReceipts_iff γ st (resync st₁)).mp hrec' f

/-! ## Switching the gate off -/

/-- The state with its gate switched off. -/
def gateOff {j : ℕ} (st : R.State j) : R.State j := { st with gate := ⊥ }

/-- Switching the gate off preserves admissibility: the support guard and the relation have a
positive-gate antecedent, and nothing else reads the gate. -/
theorem Admissible.gateOff {j : ℕ} {st : R.State j} (hst : R.Admissible st) :
    R.Admissible (Ref.gateOff st) where
  u_respects := hst.u_respects
  v_respects := hst.v_respects
  face := hst.face
  gate_vis := extVisibilityReplace_bot _ _
  shadowP_vis := hst.shadowP_vis
  shadowC_vis := hst.shadowC_vis
  shadowP_iff := hst.shadowP_iff
  shadowC_iff := hst.shadowC_iff
  support hg := absurd rfl hg
  relation _ hg := absurd rfl hg

/-- Switching the gate off preserves synchronization. -/
theorem Synchronized.gateOff {j : ℕ} (hj : 1 ≤ j) {st : R.State j} (hs : Synchronized st) :
    Synchronized (Ref.gateOff st) := by
  intro f
  cases f with
  | gate =>
      change (⊥ : ExtOrd) = extVisibilityReplace ((Ref.gateOff st).sourceProfile .gate) 1 1
      rw [State.sourceProfile_of_present _ (by exact hj)]
      rfl
  | req d =>
      change st.shadowP d = _
      have h := hs (.req d)
      change st.shadowP d = _ at h
      rw [h]
      congr 1
  | priv d =>
      change st.shadowC d = _
      have h := hs (.priv d)
      change st.shadowC d = _ at h
      rw [h]
      congr 1

/-! ## Terminal insertion -/

/-- A fresh limit block floor above every proper value of the source vector and above a given
ordinal. -/
noncomputable def State.freshFloor {j : ℕ} (st : R.State j) (h : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.omega0 * ((insert h st.inventory).sup id + 1)

theorem State.freshFloor_limit {j : ℕ} (st : R.State j) (h : Ordinal.{0}) :
    limitPart (st.freshFloor h) = st.freshFloor h :=
  limitPart_omega0_mul _

theorem State.lt_freshFloor {j : ℕ} (st : R.State j) (h : Ordinal.{0}) {a : Ordinal.{0}}
    (ha : a ∈ insert h st.inventory) : a < st.freshFloor h := by
  unfold State.freshFloor
  set m : Ordinal.{0} := (insert h st.inventory).sup id with hm
  have h1 : a ≤ m := Finset.le_sup (f := id) ha
  have h2 : m + 1 ≤ Ordinal.omega0 * (m + 1) := Ordinal.le_mul_right _ Ordinal.omega0_pos
  have h3 : a < m + 1 := Order.lt_add_one_iff.mpr h1
  exact h3.trans_le h2

theorem State.profile_lt_freshFloor {j : ℕ} (st : R.State j) (h : Ordinal.{0}) (f : Field P C) :
    st.sourceProfile f < ofOrd (st.freshFloor h) ∨ st.sourceProfile f = ⊤ := by
  rcases ExtOrd.cases (st.sourceProfile f) with hb | ht | ⟨a, ha⟩
  · exact Or.inl (hb ▸ bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _))
  · exact Or.inr ht
  · refine Or.inl ?_
    rw [ha, ofOrd_lt_ofOrd]
    exact st.lt_freshFloor h (Finset.mem_insert_of_mem
      (PairedSlotEncoding.mem_values.mpr ⟨f, ha⟩))

theorem State.h_lt_freshFloor {j : ℕ} (st : R.State j) (h : Ordinal.{0}) :
    h < st.freshFloor h :=
  st.lt_freshFloor h (Finset.mem_insert_self _ _)

/-- **Terminal insertion, with a supported decoder.**  Capping an admitted source at `β = λ + N`
for the fresh limit floor `λ` above every proper value and above a prescribed cut `h` gives an
admitted **proper** source `b₀` with the same prefix below `h` and literal on every proper field;
its canonical normalization `b` is an admitted member of the finite canonical inventory, and one
normalized witness through `N` (the right-filled decoder over the grid `{β}`, then whole-block
collapse) reads every original field back exactly, literal tops included, and sends **every**
value — represented or not, unused grid points and the terminal region included — to a value
supported by the original field vector `a`, with bottom and top allowed. -/
theorem Admitted.exists_terminal' {a : Field P C → ExtOrd} (h : R.Admitted a)
    (hh : Ordinal.{0}) :
    ∃ b₀ : Field P C → ExtOrd, R.Admitted b₀ ∧ (∀ f, b₀ f ≠ ⊤) ∧
      (∀ f, min (b₀ f) (ofOrd hh) = min (a f) (ofOrd hh)) ∧ (∀ f, a f ≠ ⊤ → b₀ f = a f) ∧
      R.Admitted (PairedSlotEncoding.normalize N b₀) ∧
      PairedSlotEncoding.normalize N b₀ ∈ CanonicalPairedProfiles.inventory (Field P C) N ∧
      ∃ δ : ExtOrd → ExtOrd, Witness (gTop N) δ ∧
        (∀ f, δ (PairedSlotEncoding.normalize N b₀ f) = a f) ∧
        ∀ x, OrbitPrefixSupport.Supported N ({⊤} : Set ExtOrd) a (δ x) := by
  obtain ⟨st, hst, hs, hg, rfl⟩ := h
  set l := st.freshFloor hh with hl
  have hlim : limitPart l = l := st.freshFloor_limit hh
  set β : ExtOrd := ofOrd (l + N) with hβdef
  have hβfp : finitePart (l + N) = N := by
    have := finitePart_limitPart_add_nat l N
    rwa [hlim] at this
  have hβvis : SelfVis N β := by
    rw [hβdef, selfVis_ofOrd_iff, hβfp]
  have hβbot : β ≠ ⊥ := ofOrd_ne_bot _
  have hlβ : ofOrd l ≤ β := ofOrd_le_ofOrd.mpr le_self_add
  have hcap : R.Admitted (fun f => min (st.sourceProfile f) β) :=
    Admitted.cap ⟨st, hst, hs, hg, rfl⟩ hβvis hβbot
  have hproper : ∀ f, min (st.sourceProfile f) β ≠ ⊤ := fun f ht =>
    ofOrd_ne_top _ ((min_eq_top.mp ht).2)
  refine ⟨fun f => min (st.sourceProfile f) β, hcap, hproper, ?_, ?_, hcap.normalize,
    CanonicalPairedProfiles.normalize_mem_inventory _ _ hproper, ?_⟩
  · intro f
    rw [min_assoc, min_eq_right ((ofOrd_le_ofOrd.mpr (st.h_lt_freshFloor hh).le).trans hlβ)]
  · intro f hf
    rcases st.profile_lt_freshFloor hh f with hlt | ht
    · exact min_eq_left (hlt.le.trans hlβ)
    · exact absurd ht hf
  · have hG : ∀ z ∈ ({β} : Finset ExtOrd), SelfVis N z := fun z hz => by
      rw [Finset.mem_singleton.mp hz]; exact hβvis
    have hC : β ∈ ({β} : Finset ExtOrd) := Finset.mem_singleton_self β
    refine ⟨collapseBlock l ∘ PairedSlotDecoder.decode N
      (PairedSlotEncoding.values (fun f => min (st.sourceProfile f) β)) {β} β,
      Witness.comp_of_bottom_reflecting (PairedSlotDecoder.decode_witness hG hβvis)
        (collapseBlock_witness N hlim) le_rfl (collapseBlock_reflects_bottom l), ?_, ?_⟩
    · intro f
      rw [Function.comp_apply, PairedSlotDecoder.decode_normalize hG hβvis hproper f]
      exact collapseBlock_min hlβ (st.profile_lt_freshFloor hh f)
    · intro x
      rw [Function.comp_apply]
      rcases PairedSlotDecoder.decode_supported (j := N) (K := N)
        (p := fun f => min (st.sourceProfile f) β) le_rfl hC x with hz | hβ' | ⟨f, i, hi, he⟩
      · rw [hz]
        exact Or.inl (collapseBlock_witness N hlim).bot
      · rw [Finset.mem_singleton.mp (Finset.mem_coe.mp hβ'), collapseBlock_of_le hlβ]
        exact Or.inr (Or.inl (Set.mem_singleton _))
      · rw [he]
        change OrbitPrefixSupport.Supported N ({⊤} : Set ExtOrd) st.sourceProfile
          (collapseBlock l (extVisibilityReplace (min (st.sourceProfile f) β) N i))
        rcases st.profile_lt_freshFloor hh f with hlt | ht
        · rw [min_eq_left (hlt.le.trans hlβ),
            collapseBlock_of_lt (evr_lt_of_lt_limit hlim hlt N i)]
          exact Or.inr (Or.inr ⟨f, i, hi, rfl⟩)
        · rw [ht, min_top_left, evr_eq_self_of_selfVis hβvis i, collapseBlock_of_le hlβ]
          exact Or.inr (Or.inl (Set.mem_singleton _))

/-- **Terminal insertion** (the decoder's support conjunct dropped). -/
theorem Admitted.exists_terminal {a : Field P C → ExtOrd} (h : R.Admitted a) (hh : Ordinal.{0}) :
    ∃ b₀ : Field P C → ExtOrd, R.Admitted b₀ ∧ (∀ f, b₀ f ≠ ⊤) ∧
      (∀ f, min (b₀ f) (ofOrd hh) = min (a f) (ofOrd hh)) ∧ (∀ f, a f ≠ ⊤ → b₀ f = a f) ∧
      R.Admitted (PairedSlotEncoding.normalize N b₀) ∧
      PairedSlotEncoding.normalize N b₀ ∈ CanonicalPairedProfiles.inventory (Field P C) N ∧
      ∃ δ : ExtOrd → ExtOrd, Witness (gTop N) δ ∧
        ∀ f, δ (PairedSlotEncoding.normalize N b₀ f) = a f := by
  obtain ⟨b₀, h1, h2, h3, h4, h5, h6, δ, hδ, hread, -⟩ := h.exists_terminal' hh
  exact ⟨b₀, h1, h2, h3, h4, h5, h6, δ, hδ, hread⟩

/-! ## The finite canonical catalogue -/

variable (R) in
/-- The canonical admitted catalogue: proper canonical fixed points that are admitted. -/
def Catalogue : Set (Field P C → ExtOrd) :=
  {a | a ∈ CanonicalPairedProfiles.inventory (Field P C) N ∧ R.Admitted a}

variable (R) in
theorem catalogue_finite : (R.Catalogue).Finite :=
  (CanonicalPairedProfiles.inventory_finite (Field P C) N).subset fun _ h => h.1

/-- The normalization of a proper admitted source is in the catalogue. -/
theorem Admitted.normalize_mem_catalogue {a : Field P C → ExtOrd} (h : R.Admitted a)
    (hproper : ∀ f, a f ≠ ⊤) : PairedSlotEncoding.normalize N a ∈ R.Catalogue :=
  ⟨CanonicalPairedProfiles.normalize_mem_inventory _ _ hproper, h.normalize⟩

end
end VaughtConjecture.Knight.CappedDonor.Ref
