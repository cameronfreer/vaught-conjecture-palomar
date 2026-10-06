/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowHighFibres
public import VaughtConjecture.Knight.CappedDonorNormalization
public import VaughtConjecture.Knight.PairedSlotDecoder

/-! # Current-grade normalization and the terminal-block decoding of the two-threshold family
(audit16 §5; note §7, §11 (1), (6))

**Closure under current-grade maps** (`TAdmissible.map`): every bottom-reflecting normalized
witness through the grades currently present (and grade one) preserves two-threshold
admissibility.  LOW transports because a strict *output* antecedent reflects through a monotone
map to a strict source antecedent (`lt_of_map_lt`), the non-top maximum and the cap field commute
with the map (`nonTopMax_map`, `capField_map`), and the frontier commutes once the map commutes
with replacement through `K` (`eC_map`); HIGH transports through `cut_map`.  No commutation
through the private arity is needed.

**Canonical normalization on the complete inventory** (`TField`, `TState.profile`,
`normalizeT`): the paired point/orbit encoder built from the values of the **complete** source
vector — every receiving field *and the stored cutoff* — applied to every field.  It preserves
admissibility (`normalizeT_tadmissible`) and synchronization, yields coded (`normalizeT_coded`,
block bound `2·|TField|`) and `j`-short (`normalizeT_short`) values with literal top and bottom
preserved, and has relative prefix preservation (`normalizeT_prefix`).  Both same-grade fibres on
source profiles compose with it (`exists_private_lift_normalized`,
`exists_request_lift_normalized`).

**The supported decoding contract with terminal-block top** (`exists_terminal_decoding`): for
any admissible state, choose a fresh limit block floor `λ` above every proper value of the source
vector and above a prescribed prefix cut, and `β = λ + j`; capping at `β` (`capWitness`, a
bottom-reflecting witness through `j`) gives an admissible **proper** state with the same prefix
below the cut; the reviewer's right-filled decoder reads its normalization back exactly
(`decode_normalize`), and collapsing the **whole** terminal block and everything above to top
(`collapseBlock`, a bottom-reflecting witness through `j` because it acts on whole blocks:
`collapseBlock_witness`) recovers the original vector literally, tops included.  The composite
outgoing map is one normalized witness through `j` (`Witness.comp_of_bottom_reflecting`).  A
jump only at the endpoint `β` would not commute with replacement on the short strip below `β`;
whole-block collapse does.  Normalization itself does not retain a top-valued prescription
literally; the fibre retained it before coding and the decoder reads it back. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

/-! ## Order facts about limit block floors -/

/-- Below a limit block floor, replacement stays below it. -/
theorem evr_lt_of_lt_limit {l : Ordinal.{0}} (hl : limitPart l = l) {x : ExtOrd}
    (hx : x < ofOrd l) (k i : ℕ) : extVisibilityReplace x k i < ofOrd l := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [extVisibilityReplace_bot]; exact hx
  · exact absurd hx not_top_lt
  · rw [extVisibilityReplace_ofOrd]
    unfold visibilityReplace
    split_ifs with hf
    · unfold ordinalReplace
      rw [ofOrd_lt_ofOrd] at hx ⊢
      have h1 : limitPart α < limitPart l := by
        rw [hl]
        exact (limitPart_le α).trans_lt hx
      exact (((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 i)).trans_le
        (limitPart_add_omega0_le h1)).trans_le hl.le
    · exact hx

/-- Above a limit block floor, replacement stays above it. -/
theorem le_evr_of_limit_le {l : Ordinal.{0}} (hl : limitPart l = l) {x : ExtOrd}
    (hx : ofOrd l ≤ x) (k i : ℕ) : ofOrd l ≤ extVisibilityReplace x k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · exact absurd hx (not_le.mpr (bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)))
  · rw [extVisibilityReplace_top]; exact le_top
  · rw [extVisibilityReplace_ofOrd]
    unfold visibilityReplace
    split_ifs with hf
    · unfold ordinalReplace
      rw [ofOrd_le_ofOrd] at hx ⊢
      have h1 : l ≤ limitPart α := by rw [← hl]; exact limitPart_mono hx
      exact h1.trans le_self_add
    · exact hx

/-! ## Two elementary witnesses -/

/-- Capping at a `j`-visible positive value is a bottom-reflecting witness through `j`. -/
theorem capWitness {j : ℕ} {β : ExtOrd} (hβ : SelfVis j β) (hβbot : β ≠ ⊥) :
    Witness (gTop j) (fun x => min x β) where
  anti := (witness_id j).anti
  vis := (witness_id j).vis
  bot := min_bot_left _
  mono := fun _ _ h => min_le_min_right _ h
  clause5 := by
    intro x kk hle i hi
    by_cases hkk : kk ≤ j
    · exact (evr_min_of_selfVis hβ hkk hi x).symm
    · rw [gTop_of_gt (not_le.mp hkk), le_bot_iff] at hle
      have hx : x = ⊥ := (min_eq_bot.mp hle).resolve_right hβbot
      rw [hx, extVisibilityReplace_bot, min_bot_left, extVisibilityReplace_bot]

theorem capWitness_reflects_bottom {β : ExtOrd} (hβbot : β ≠ ⊥) (x : ExtOrd)
    (h : min x β = ⊥) : x = ⊥ := (min_eq_bot.mp h).resolve_right hβbot

/-- Collapse a whole terminal block and everything above it to top. -/
noncomputable def collapseBlock (l : Ordinal.{0}) (x : ExtOrd) : ExtOrd :=
  if ofOrd l ≤ x then ⊤ else x

theorem collapseBlock_of_le {l : Ordinal.{0}} {x : ExtOrd} (h : ofOrd l ≤ x) :
    collapseBlock l x = ⊤ := by
  unfold collapseBlock; rw [ite_eq_left h]

theorem collapseBlock_of_lt {l : Ordinal.{0}} {x : ExtOrd} (h : x < ofOrd l) :
    collapseBlock l x = x := by
  unfold collapseBlock; rw [ite_eq_right (not_le.mpr h)]

theorem collapseBlock_reflects_bottom (l : Ordinal.{0}) (x : ExtOrd) (h : collapseBlock l x = ⊥) :
    x = ⊥ := by
  unfold collapseBlock at h
  split_ifs at h with hx
  · exact absurd h top_ne_bot
  · exact h

/-- Whole-block collapse at a limit floor is a witness through every grade. -/
theorem collapseBlock_witness (j : ℕ) {l : Ordinal.{0}} (hl : limitPart l = l) :
    Witness (gTop j) (collapseBlock l) where
  anti := (witness_id j).anti
  vis := (witness_id j).vis
  bot := collapseBlock_of_lt (bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _))
  mono := by
    intro x y hxy
    by_cases hx : ofOrd l ≤ x
    · rw [collapseBlock_of_le hx, collapseBlock_of_le (hx.trans hxy)]
    · rw [collapseBlock_of_lt (not_le.mp hx)]
      by_cases hy : ofOrd l ≤ y
      · rw [collapseBlock_of_le hy]; exact le_top
      · rw [collapseBlock_of_lt (not_le.mp hy)]; exact hxy
  clause5 := by
    intro x kk hle i hi
    by_cases hx : ofOrd l ≤ x
    · rw [collapseBlock_of_le hx, collapseBlock_of_le (le_evr_of_limit_le hl hx kk i),
        extVisibilityReplace_top]
    · rw [collapseBlock_of_lt (not_le.mp hx),
        collapseBlock_of_lt (evr_lt_of_lt_limit hl (not_le.mp hx) kk i)]

/-- Readback: collapsing the terminal block after capping at `β ≥ λ` recovers every value below
`λ` and literal top. -/
theorem collapseBlock_min {l : Ordinal.{0}} {β x : ExtOrd} (hβ : ofOrd l ≤ β)
    (hx : x < ofOrd l ∨ x = ⊤) : collapseBlock l (min x β) = x := by
  rcases hx with hx | rfl
  · rw [min_eq_left (hx.le.trans hβ), collapseBlock_of_lt hx]
  · rw [min_top_left, collapseBlock_of_le hβ]

namespace CappedDonor

variable {nP J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}

/-! ## The complete inventory: receiving fields and the stored cutoff -/

/-- The complete field inventory of the two-threshold family: the receiving fields and the stored
cutoff. -/
inductive TField {nP J : ℕ} (P : SemScheme (nP + 1)) (C : SemScheme J)
  | field (f : Field P C)
  | cutoff

/-- The complete inventory as a sum type. -/
def TField.equivSum : TField P C ≃ Field P C ⊕ Unit where
  toFun
    | .field f => Sum.inl f
    | .cutoff => Sum.inr ()
  invFun
    | Sum.inl f => .field f
    | Sum.inr _ => .cutoff
  left_inv f := by cases f <;> rfl
  right_inv s := by rcases s with f | ⟨⟩ <;> rfl

instance : Fintype (TField P C) := Fintype.ofEquiv _ TField.equivSum.symm

namespace Ref

variable {I : Type*} [Fintype I] {N : ℕ} {R : Ref I nP N J P C}

/-- The complete source vector of a two-threshold state. -/
noncomputable def TState.profile {j : ℕ} (S : R.TState j) : TField P C → ExtOrd
  | .field f => S.st.sourceProfile f
  | .cutoff => S.b

/-- Apply a scalar map to every field, including the stored cutoff. -/
def mapT {j : ℕ} (σ : ExtOrd → ExtOrd) (S : R.TState j) : R.TState j :=
  ⟨mapState σ S.st, σ S.b⟩

theorem profile_mapT (σ : ExtOrd → ExtOrd) {j : ℕ} (S : R.TState j) (f : TField P C) :
    (mapT σ S).profile f = σ (S.profile f) := by
  cases f with
  | field f => exact sourceProfile_map σ S.st f
  | cutoff => rfl

/-! ## Closure under current-grade maps -/

section Map

variable {Kσ : ℕ} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop Kσ) σ)

include hσ

theorem lt_of_map_lt {x y : ExtOrd} (h : σ x < σ y) : x < y :=
  lt_of_not_ge fun hle => not_le.mpr h (hσ.mono hle)

theorem nonTopMax_map {j : ℕ} (st : R.State j) : (mapState σ st).nonTopMax = σ st.nonTopMax := by
  classical
  unfold State.nonTopMax
  rw [Finset.apply_sup_eq_sup_comp σ (fun _ _ => hσ.mono.map_max) hσ.bot]
  congr 1
  funext d
  exact sourceProfile_map σ st _

omit hσ in
theorem capField_map (σ : ExtOrd → ExtOrd) {j : ℕ} (st : R.State j) :
    (mapState σ st).capField = σ st.capField :=
  sourceProfile_map σ st _

variable {K : ℕ} (L : R.LowRef K)

/-- The frontier commutes with a witness through `K`. -/
theorem LowRef.eC_map (hK : K ≤ Kσ) {j : ℕ} (hj : K ≤ j) (v : C.scheme.below (effC J j) → ExtOrd) :
    L.eC hj (fun d => σ (v d)) = σ (L.eC hj v) := by
  unfold LowRef.eC LowRef.lowD LowRef.e
  rw [hσ.mono.map_min, map_comm hσ hK _ le_rfl]

/-- **Closure under current-grade maps**: a bottom-reflecting normalized witness through the
present grades (and grade one) preserves two-threshold admissibility. -/
theorem LowRef.TAdmissible.map {j : ℕ} (hK : (effC J j).2 ≤ Kσ) (h1 : 1 ≤ Kσ)
    (hbot : ∀ x, σ x = ⊥ → x = ⊥) {S : R.TState j} (hS : L.TAdmissible S) :
    L.TAdmissible (mapT σ S) where
  adm := hS.adm.map hσ hK h1 hbot
  b_vis := selfVis_map hσ h1 hS.b_vis
  b_visK hjK :=
    selfVis_map hσ ((le_min hjK (L.K_lt_N.le.trans R.N_le)).trans hK) (hS.b_visK hjK)
  low hjK hg hm hH t ht := by
    have hKσ : K ≤ Kσ := (le_min hjK (L.K_lt_N.le.trans R.N_le)).trans hK
    change (mapState σ S.st).nonTopMax < σ S.b at hm
    change σ S.b < (mapState σ S.st).capField at hH
    rw [nonTopMax_map hσ] at hm
    rw [capField_map] at hH
    change max (σ S.b) (L.eC hjK (fun d => σ (S.st.v d))) ≤ σ (S.st.u _)
    rw [L.eC_map hσ hKσ, ← hσ.mono.map_max]
    exact hσ.mono (hS.low hjK ((map_ne_bot_iff hσ hbot _).mp hg) (lt_of_map_lt hσ hm)
      (lt_of_map_lt hσ hH) t ht)
  high hj hg := by
    have hN : N ≤ Kσ := (le_min hj R.N_le).trans hK
    change min (σ S.b) (σ (S.st.v (R.capC hj))) = R.cut (fun e => σ (R.lowC hj S.st.v e))
    rw [cut_map hσ hN, ← hσ.mono.map_min, hS.high hj ((map_ne_bot_iff hσ hbot _).mp hg)]

end Map

/-! ## Canonical normalization on the complete inventory -/

/-- The complete inventory of a two-threshold state: the ordinal values of its source vector,
the stored cutoff included. -/
noncomputable def TState.inventory {j : ℕ} (S : R.TState j) : Finset Ordinal.{0} :=
  PairedSlotEncoding.values S.profile

/-- The canonical incoming encoder of a two-threshold state at its cutoff. -/
noncomputable def TState.encoder {j : ℕ} (S : R.TState j) : ExtOrd → ExtOrd :=
  PairedSlotIncoming.encoder j S.inventory

theorem TState.encoder_witness {j : ℕ} (S : R.TState j) : Witness (gTop j) S.encoder :=
  PairedSlotIncoming.encoder_witness j S.inventory

theorem TState.encoder_reflects_bottom {j : ℕ} (S : R.TState j) (x : ExtOrd)
    (h : S.encoder x = ⊥) : x = ⊥ :=
  PairedSlotIncoming.encoder_reflects_bottom j S.inventory x h

/-- **Canonical normalization** of a two-threshold state on its complete inventory. -/
noncomputable def normalizeT {j : ℕ} (S : R.TState j) : R.TState j := mapT S.encoder S

/-- On the complete source vector, normalization is the paired-slot normalization. -/
theorem profile_normalizeT {j : ℕ} (S : R.TState j) (f : TField P C) :
    (normalizeT S).profile f = PairedSlotEncoding.normalize j S.profile f := by
  rw [normalizeT, profile_mapT]
  exact PairedSlotIncoming.encoder_profile j S.profile f

variable {K : ℕ} (L : R.LowRef K)

/-- Normalization preserves two-threshold admissibility, at the current grade. -/
theorem LowRef.normalizeT_tadmissible {j : ℕ} (hj : 1 ≤ j) {S : R.TState j}
    (hS : L.TAdmissible S) : L.TAdmissible (normalizeT S) :=
  hS.map S.encoder_witness L (min_le_left j J) hj S.encoder_reflects_bottom

/-- Normalization preserves synchronization of the receiving state. -/
theorem normalizeT_synchronized {j : ℕ} (hj : 1 ≤ j) {S : R.TState j}
    (hs : Synchronized S.st) : Synchronized (normalizeT S).st :=
  hs.map S.encoder_witness hj

/-- Every normalized value other than literal top lies in the coded alphabet with block bound
twice the size of the complete inventory. -/
theorem normalizeT_coded {j : ℕ} (S : R.TState j) (f : TField P C) (hf : S.profile f ≠ ⊤) :
    (normalizeT S).profile f ∈ ExtOrd.codedAlphabet (2 * Fintype.card (TField P C)) j := by
  rw [profile_normalizeT]
  exact PairedSlotEncoding.normalize_mem j S.profile f hf

/-- Every normalized value is `j`-short. -/
theorem normalizeT_short {j : ℕ} (S : R.TState j) (f : TField P C) :
    SharpWitnessComposition.Short j ((normalizeT S).profile f) := by
  rw [profile_normalizeT]
  rcases ExtOrd.cases (S.profile f) with hb | ht | ⟨a, ha⟩
  · exact Or.inl ((PairedSlotEncoding.normalize_bot_iff j _ f).mpr hb)
  · exact Or.inr (Or.inl (by simp only [PairedSlotEncoding.normalize, ht]))
  · refine Or.inr (Or.inr ⟨_, PairedSlotEncoding.normalize_ofOrd ha, ?_⟩)
    rw [finitePart_mul_add]
    exact PairedSlotEncoding.offset_le j _ a

theorem normalizeT_top {j : ℕ} (S : R.TState j) (f : TField P C) (hf : S.profile f = ⊤) :
    (normalizeT S).profile f = ⊤ := by
  rw [profile_normalizeT]
  simp only [PairedSlotEncoding.normalize, hf]

theorem normalizeT_bot_iff {j : ℕ} (S : R.TState j) (f : TField P C) :
    (normalizeT S).profile f = ⊥ ↔ S.profile f = ⊥ := by
  rw [profile_normalizeT]
  exact PairedSlotEncoding.normalize_bot_iff j _ f

/-- **Relative prefix preservation**: states agreeing on every field of the complete inventory
below a `j`-visible cut have the same normalized value at every field below the cut. -/
theorem normalizeT_prefix {j : ℕ} {S S' : R.TState j} {h : Ordinal.{0}} (hh : j ≤ finitePart h)
    (hpq : ∀ f, min (S.profile f) (ofOrd h) = min (S'.profile f) (ofOrd h)) (f : TField P C)
    (hf : S.profile f < ofOrd h) : (normalizeT S).profile f = (normalizeT S').profile f := by
  rw [profile_normalizeT, profile_normalizeT]
  exact PairedSlotEncoding.normalize_prefix hh hpq f hf

/-! ## Normalized repairs stay in the catalogue -/

/-- The private fibre on source profiles, followed by normalization. -/
theorem LowRef.exists_private_lift_normalized {j : ℕ} (hj : 1 ≤ j) {S : R.TState j}
    (hS : L.TAdmissible S) (hs : Synchronized S.st) {v₁ : C.scheme.below (effC J j) → ExtOrd}
    (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁) {γ : ExtOrd}
    (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (v₁ d) γ = min (S.st.v d) γ) :
    ∃ S₁ : R.TState j, L.TAdmissible S₁ ∧ Synchronized S₁.st ∧ S₁.st.v = v₁ ∧
      (∀ d, min (S₁.st.u d) γ = min (S.st.u d) γ) ∧ R.CapReceipts γ S.st S₁.st ∧
      min S₁.b γ = min S.b γ ∧ L.TAdmissible (normalizeT S₁) ∧
      Synchronized (normalizeT S₁).st ∧
      ∀ f, SharpWitnessComposition.Short j ((normalizeT S₁).profile f) := by
  obtain ⟨S₁, hS₁, hs₁, hv, hu, hrec, hb⟩ := L.exists_private_lift_sync hS hs hv₁ hγ hagree
  exact ⟨S₁, hS₁, hs₁, hv, hu, hrec, hb, L.normalizeT_tadmissible hj hS₁,
    normalizeT_synchronized hj hs₁, normalizeT_short S₁⟩

/-- The request fibre on source profiles, followed by normalization. -/
theorem LowRef.exists_request_lift_normalized {j : ℕ} (hj : 1 ≤ j) {S : R.TState j}
    (hS : L.TAdmissible S) (hs : Synchronized S.st) {u₁ : P.scheme.below (effP nP j) → ExtOrd}
    (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁) {γ : ExtOrd}
    (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (u₁ d) γ = min (S.st.u d) γ) :
    ∃ S₁ : R.TState j, L.TAdmissible S₁ ∧ Synchronized S₁.st ∧ S₁.st.u = u₁ ∧
      (∀ d, min (S₁.st.v d) γ = min (S.st.v d) γ) ∧ R.CapReceipts γ S.st S₁.st ∧
      min S₁.b γ = min S.b γ ∧ L.TAdmissible (normalizeT S₁) ∧
      Synchronized (normalizeT S₁).st ∧
      ∀ f, SharpWitnessComposition.Short j ((normalizeT S₁).profile f) := by
  obtain ⟨S₁, hS₁, hs₁, hu, hv, hrec, hb⟩ := L.exists_request_lift_sync hS hs hu₁ hγ hagree
  exact ⟨S₁, hS₁, hs₁, hu, hv, hrec, hb, L.normalizeT_tadmissible hj hS₁,
    normalizeT_synchronized hj hs₁, normalizeT_short S₁⟩

/-! ## The supported decoding contract with terminal-block top -/

/-- A fresh limit block floor above every proper value of the source vector and above a given
ordinal. -/
noncomputable def TState.freshFloor {j : ℕ} (S : R.TState j) (h : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.omega0 * ((insert h (PairedSlotEncoding.values S.profile)).sup id + 1)

theorem TState.freshFloor_limit {j : ℕ} (S : R.TState j) (h : Ordinal.{0}) :
    limitPart (S.freshFloor h) = S.freshFloor h :=
  limitPart_omega0_mul _

theorem TState.lt_freshFloor {j : ℕ} (S : R.TState j) (h : Ordinal.{0}) {a : Ordinal.{0}}
    (ha : a ∈ insert h (PairedSlotEncoding.values S.profile)) : a < S.freshFloor h := by
  unfold TState.freshFloor
  set m : Ordinal.{0} := (insert h (PairedSlotEncoding.values S.profile)).sup id with hm
  have h1 : a ≤ m := Finset.le_sup (f := id) ha
  have h2 : m + 1 ≤ Ordinal.omega0 * (m + 1) := Ordinal.le_mul_right _ Ordinal.omega0_pos
  have h3 : a < m + 1 := Order.lt_add_one_iff.mpr h1
  exact h3.trans_le h2

theorem TState.profile_lt_freshFloor {j : ℕ} (S : R.TState j) (h : Ordinal.{0}) (f : TField P C) :
    S.profile f < ofOrd (S.freshFloor h) ∨ S.profile f = ⊤ := by
  rcases ExtOrd.cases (S.profile f) with hb | ht | ⟨a, ha⟩
  · exact Or.inl (hb ▸ bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _))
  · exact Or.inr ht
  · refine Or.inl ?_
    rw [ha, ofOrd_lt_ofOrd]
    exact S.lt_freshFloor h (Finset.mem_insert_of_mem
      (PairedSlotEncoding.mem_values.mpr ⟨f, ha⟩))

theorem TState.h_lt_freshFloor {j : ℕ} (S : R.TState j) (h : Ordinal.{0}) :
    h < S.freshFloor h :=
  S.lt_freshFloor h (Finset.mem_insert_self _ _)

/-- **The supported decoding contract with terminal-block top**: capping an admissible state at
`β = λ + j` for the fresh limit floor `λ` gives an admissible proper state with the same prefix
below any prescribed cut `h < λ`; the right-filled decoder of the capped inventory reads its
canonical normalization back exactly, and whole-block collapse recovers the original vector,
literal tops included; the composite is one normalized witness through `j`. -/
theorem LowRef.exists_terminal_decoding {j : ℕ} (hj : 1 ≤ j) {S : R.TState j}
    (hS : L.TAdmissible S) (h : Ordinal.{0}) :
    ∃ (l : Ordinal.{0}) (β : ExtOrd), limitPart l = l ∧ β = ofOrd (l + j) ∧ SelfVis j β ∧
      L.TAdmissible (mapT (fun x => min x β) S) ∧
      (∀ f, (mapT (fun x => min x β) S).profile f ≠ ⊤) ∧
      (∀ f, min ((mapT (fun x => min x β) S).profile f) (ofOrd h) = min (S.profile f) (ofOrd h)) ∧
      ∃ δ : ExtOrd → ExtOrd, Witness (gTop j) δ ∧
        ∀ f, δ ((normalizeT (mapT (fun x => min x β) S)).profile f) = S.profile f := by
  set l := S.freshFloor h with hl
  have hlim : limitPart l = l := S.freshFloor_limit h
  set β : ExtOrd := ofOrd (l + j) with hβdef
  have hβvis : SelfVis j β := by
    rw [hβdef, selfVis_ofOrd_iff]
    have := finitePart_limitPart_add_nat l j
    rw [hlim] at this
    rw [this]
  have hβbot : β ≠ ⊥ := ofOrd_ne_bot _
  have hlβ : ofOrd l ≤ β := ofOrd_le_ofOrd.mpr le_self_add
  have hcap : L.TAdmissible (mapT (fun x => min x β) S) :=
    hS.map (capWitness hβvis hβbot) L (min_le_left j J) hj (capWitness_reflects_bottom hβbot)
  have hproper : ∀ f, (mapT (fun x => min x β) S).profile f ≠ ⊤ := by
    intro f
    rw [profile_mapT]
    exact fun ht => ofOrd_ne_top _ ((min_eq_top.mp ht).2)
  have hprefix : ∀ f, min ((mapT (fun x => min x β) S).profile f) (ofOrd h) =
      min (S.profile f) (ofOrd h) := by
    intro f
    rw [profile_mapT, min_assoc, min_eq_right
      ((ofOrd_le_ofOrd.mpr (S.h_lt_freshFloor h).le).trans hlβ)]
  refine ⟨l, β, hlim, rfl, hβvis, hcap, hproper, hprefix, ?_⟩
  -- the outgoing map: the right-filled decoder followed by whole-block collapse
  have hG : ∀ z ∈ (∅ : Finset ExtOrd), SelfVis j z := fun z hz => absurd hz (Finset.notMem_empty z)
  refine ⟨collapseBlock l ∘ PairedSlotDecoder.decode j
    (PairedSlotEncoding.values (mapT (fun x => min x β) S).profile) ∅ β,
    Witness.comp_of_bottom_reflecting (PairedSlotDecoder.decode_witness hG hβvis)
      (collapseBlock_witness j hlim) le_rfl (collapseBlock_reflects_bottom l), ?_⟩
  intro f
  rw [Function.comp_apply, profile_normalizeT,
    PairedSlotDecoder.decode_normalize hG hβvis hproper f, profile_mapT]
  exact collapseBlock_min hlβ (S.profile_lt_freshFloor h f)

end Ref

end CappedDonor

end VaughtConjecture.Knight
