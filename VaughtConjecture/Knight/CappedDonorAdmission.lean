/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowHighNormalization

/-! # Concrete source admission: complete-vector restriction and downward admission

The recursive physical construction (newapproach8/9) consumes a *scalar source family*
`S_j ⊆ (TField P C → ExtOrd)` with six closure properties.  This file instantiates that family
by the repository's actual two-threshold predicate — not by an unspecified family whose closure is
postulated — and banks the closure results that follow from the existing normalization theorems
(new19 §§1.1–1.3):

* `SourceAdmitted j a`: some two-threshold state at cutoff `j` is `TAdmissible` for the low
  reference, synchronized, and has complete source vector `a`.
* `sourceProfile_eq_persistent`: in an admissible synchronized state every persistent value *is*
  the source value — present numerical values are already `1`-visible (positive grade), future
  values are persistent by definition.  No equality between distinct future root channels is
  imposed.
* **Complete-vector restriction** (`sourceProfile_restrict_of_sync`, `profile_restrictT`):
  restricting a synchronized admissible state to a lower cutoff keeps the *entire* source vector,
  including the fields that cross from numerical to future status.  Synchronization is what
  justifies this; restriction of an arbitrary state can change a crossing field's source read.
* **Downward admission** (`SourceAdmitted.restrict`): `Adm_j a → Adm_i a` for `i ≤ j`.  Any LOW or
  HIGH obligation active at `i` was active at `j` with the same readings (the low frontier, the
  cap and the request tops are present at both cutoffs).
* **Closure under bottom-reflecting normalized maps, permissible positive caps and canonical
  normalization** (`SourceAdmitted.map`, `.positive_cap`, `.normalize`), from
  `LowRef.TAdmissible.map`, `capWitness` and `normalizeT_*`; at cap `⊥` the zero state is used
  instead (`SourceAdmitted.zero`), never a false bottom-reflection hypothesis.
* `SourceAdmitted.restrict_normalize`: the predecessor call `Norm_i a ∈ Q_i` for `i ≤ j`.

**Upward admission is deliberately absent**: `Adm_{K-1} a` does not imply `Adm_K a`, nor
`Adm_{N-1} a` implies `Adm_N a` (new19 §1.5 retains explicit failures); activation adds new
admitted layers and never re-admits old profiles at a higher grade.  Nothing here asserts that an
arbitrary lawful physical output is admitted or synchronized.  Grade-one positive monotone
interpolation (new19 §1.4) is not banked here. -/

@[expose] public section

namespace VaughtConjecture.Knight.CappedDonor.Ref

open Transform Value ExtOrd AmalgamationPlan
noncomputable section

variable {I : Type*} [Fintype I] {nP N J K : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C} (L : R.LowRef K)

/-- **Concrete source admission** at cutoff `j`: the complete source vectors of the two-threshold
states that are admissible for the low reference and synchronized. -/
def LowRef.SourceAdmitted (j : ℕ) (a : TField P C → ExtOrd) : Prop :=
  ∃ S : R.TState j, L.TAdmissible S ∧ Synchronized S.st ∧ S.profile = a

omit [Fintype I] in
/-- Every field has positive grade. -/
theorem field_grade_pos (f : Field P C) : 1 ≤ f.grade := by
  cases f with
  | req d => exact P.scheme.grade_pos d
  | priv d => exact C.scheme.grade_pos d
  | gate => exact le_rfl

/-! ## Synchronization identifies the persistent and source vectors -/

/-- In an admissible synchronized state every persistent value is the source value: present
numerical values are `1`-visible, future values are persistent by definition. -/
theorem sourceProfile_eq_persistent {j : ℕ} {st : R.State j} (ha : R.Admissible st)
    (hs : Synchronized st) : st.sourceProfile = st.persistent := by
  funext f
  by_cases hf : f.grade ≤ j
  · have hv : SelfVis 1 (st.numeric f hf) :=
      selfVis_mono (ha.numeric_selfVis f hf) (field_grade_pos f)
    have hh := hs f
    rw [st.sourceProfile_of_present hf, hv] at hh
    exact (st.sourceProfile_of_present hf).trans hh.symm
  · exact st.sourceProfile_of_future hf

/-! ## Complete-vector restriction -/

/-- **Restriction keeps the complete source vector**, the fields crossing from numerical to
future status included; synchronization supplies the crossing case. -/
theorem sourceProfile_restrict_of_sync {i j : ℕ} (hij : i ≤ j) {st : R.State j}
    (ha : R.Admissible st) (hs : Synchronized st) :
    (restrict hij st).sourceProfile = st.sourceProfile := by
  funext f
  by_cases hf : f.grade ≤ i
  · rw [State.sourceProfile_of_present _ hf, restrict_numeric,
      State.sourceProfile_of_present _ (hf.trans hij)]
  · rw [State.sourceProfile_of_future _ hf]
    change st.persistent f = st.sourceProfile f
    exact (congrFun (sourceProfile_eq_persistent ha hs) f).symm

/-- Restriction preserves synchronization. -/
theorem synchronized_restrict {i j : ℕ} (hij : i ≤ j) {st : R.State j} (ha : R.Admissible st)
    (hs : Synchronized st) : Synchronized (restrict hij st) := by
  intro f
  rw [sourceProfile_restrict_of_sync hij ha hs]
  change st.persistent f = extVisibilityReplace (st.sourceProfile f) 1 1
  exact hs f

/-- Restrict a two-threshold state to a lower cutoff, keeping the stored cutoff. -/
def restrictT {i j : ℕ} (hij : i ≤ j) (S : R.TState j) : R.TState i :=
  ⟨restrict hij S.st, S.b⟩

theorem profile_restrictT {i j : ℕ} (hij : i ≤ j) {S : R.TState j} (ha : R.Admissible S.st)
    (hs : Synchronized S.st) : (restrictT hij S).profile = S.profile := by
  funext f
  cases f with
  | field f => exact congrFun (sourceProfile_restrict_of_sync hij ha hs) f
  | cutoff => rfl

/-- The low frontier of a restricted section is the frontier of the section: the owner's lower
domain is present at both cutoffs. -/
theorem eC_restrict {i j : ℕ} (hij : i ≤ j) (hKi : K ≤ i) (st : R.State j) :
    L.eC hKi (restrict hij st).v = L.eC (hKi.trans hij) st.v := rfl

/-- **Downward admission of the two-threshold state**: LOW and HIGH obligations active at the
lower cutoff were active at the higher one, with the same readings. -/
theorem tadmissible_restrictT {i j : ℕ} (hij : i ≤ j) {S : R.TState j} (hS : L.TAdmissible S)
    (hs : Synchronized S.st) : L.TAdmissible (restrictT hij S) := by
  have hM : (restrict hij S.st).nonTopMax = S.st.nonTopMax := by
    unfold State.nonTopMax
    rw [sourceProfile_restrict_of_sync hij hS.adm hs]
  have hH : (restrict hij S.st).capField = S.st.capField := by
    unfold State.capField
    rw [sourceProfile_restrict_of_sync hij hS.adm hs]
  refine ⟨hS.adm.restrict hij, hS.b_vis, fun hKi => hS.b_visK (hKi.trans hij), ?_, ?_⟩
  · intro hKi hg hm hHlt t ht
    have hm' : S.st.nonTopMax < S.b := by
      change (restrict hij S.st).nonTopMax < S.b at hm
      rwa [hM] at hm
    have hH' : S.b < S.st.capField := by
      change S.b < (restrict hij S.st).capField at hHlt
      rwa [hH] at hHlt
    exact hS.low (hKi.trans hij) hg hm' hH' t ht
  · intro hNi hg
    exact hS.high (hNi.trans hij) hg

/-- **Downward admission** (`Adm_j a → Adm_i a`, `i ≤ j`).  One-way: upward admission is not
asserted. -/
theorem LowRef.SourceAdmitted.restrict {i j : ℕ} (hij : i ≤ j) {a : TField P C → ExtOrd}
    (ha : L.SourceAdmitted j a) : L.SourceAdmitted i a := by
  obtain ⟨S, hS, hs, hprof⟩ := ha
  exact ⟨restrictT hij S, tadmissible_restrictT L hij hS hs,
    synchronized_restrict hij hS.adm hs, (profile_restrictT hij hS.adm hs).trans hprof⟩

/-! ## Closure under maps, permissible caps and normalization -/

/-- Closure under a bottom-reflecting normalized witness through the present grades and grade
one. -/
theorem LowRef.SourceAdmitted.map {j M : ℕ} {a : TField P C → ExtOrd} (ha : L.SourceAdmitted j a)
    {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop M) σ) (hgrades : (effC J j).2 ≤ M) (h1 : 1 ≤ M)
    (hbot : ∀ x, σ x = ⊥ → x = ⊥) : L.SourceAdmitted j (fun f => σ (a f)) := by
  obtain ⟨S, hS, hs, hprof⟩ := ha
  refine ⟨mapT σ S, hS.map hσ L hgrades h1 hbot, hs.map hσ h1, ?_⟩
  funext f
  rw [profile_mapT, hprof]

/-- **Permissible positive caps** preserve admission (`Adm_j a → Adm_j (a ∧ β)` for a positive
`j`-visible `β`); the cap `⊥` is the zero state (`SourceAdmitted.zero`). -/
theorem LowRef.SourceAdmitted.positive_cap {j : ℕ} (hj : 1 ≤ j) {a : TField P C → ExtOrd}
    (ha : L.SourceAdmitted j a) {β : ExtOrd} (hβ : SelfVis j β) (hβbot : β ≠ ⊥) :
    L.SourceAdmitted j (fun f => min (a f) β) :=
  ha.map L (capWitness hβ hβbot) (min_le_left _ _) hj (capWitness_reflects_bottom hβbot)

/-- **Canonical normalization** preserves admission (`Adm_j a → Adm_j (Norm_j a)`). -/
theorem LowRef.SourceAdmitted.normalize {j : ℕ} (hj : 1 ≤ j) {a : TField P C → ExtOrd}
    (ha : L.SourceAdmitted j a) : L.SourceAdmitted j (PairedSlotEncoding.normalize j a) := by
  obtain ⟨S, hS, hs, hprof⟩ := ha
  refine ⟨normalizeT S, L.normalizeT_tadmissible hj hS, normalizeT_synchronized hj hs, ?_⟩
  funext f
  rw [profile_normalizeT, hprof]

/-- **The predecessor call**: an admitted `j`-profile normalizes to an admitted `i`-profile at
every lower positive cutoff (`Norm_i a ∈ Q_i`, new19 §1.5) — by downward admission, not by any
re-admission of old profiles at higher grades. -/
theorem LowRef.SourceAdmitted.restrict_normalize {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    {a : TField P C → ExtOrd} (ha : L.SourceAdmitted j a) :
    L.SourceAdmitted i (PairedSlotEncoding.normalize i a) :=
  (ha.restrict L hij).normalize L hi

/-! ## The zero state is admitted at every cutoff -/

/-- The all-bottom section of any lower set is lawful: the zero witness at every owner and the
target cell itself for availability. -/
theorem respectsBelow_bot {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    (sem : Semantics D) (BJ : Finset ι × ℕ) :
    RespectsSemanticsBelow sem BJ (fun _ => (⊥ : ExtOrd)) :=
  RespectsSemanticsBelow.bot sem BJ

/-- The all-bottom receiving state. -/
def zeroState (R : Ref I nP N J P C) (j : ℕ) : R.State j where
  u _ := ⊥
  v _ := ⊥
  gate := ⊥
  shadowP _ := ⊥
  shadowC _ := ⊥

theorem zeroState_admissible (j : ℕ) : R.Admissible (zeroState R j) where
  u_respects := respectsBelow_bot _ _
  v_respects := respectsBelow_bot _ _
  face _ _ := rfl
  gate_vis := extVisibilityReplace_bot _ _
  shadowP_vis _ := extVisibilityReplace_bot _ _
  shadowC_vis _ := extVisibilityReplace_bot _ _
  shadowP_iff _ := Iff.rfl
  shadowC_iff _ := Iff.rfl
  support hg := absurd rfl hg
  relation _ hg := absurd rfl hg

theorem zeroState_sourceProfile (j : ℕ) (f : Field P C) :
    (zeroState R j).sourceProfile f = ⊥ := by
  by_cases hf : f.grade ≤ j
  · rw [State.sourceProfile_of_present _ hf]
    cases f <;> rfl
  · rw [State.sourceProfile_of_future _ hf]
    cases f <;> rfl

theorem zeroState_synchronized (j : ℕ) : Synchronized (zeroState R j) := by
  intro f
  rw [zeroState_sourceProfile, extVisibilityReplace_bot]
  cases f <;> rfl

/-- **Zero is admitted at every cutoff.**  (A scalar statement: the selected physical master of
the zero profile may still have positive spare rungs.) -/
theorem LowRef.SourceAdmitted.zero (j : ℕ) : L.SourceAdmitted j (fun _ => ⊥) := by
  refine ⟨⟨zeroState R j, ⊥⟩, ⟨zeroState_admissible j, extVisibilityReplace_bot _ _,
    fun _ => extVisibilityReplace_bot _ _, fun _ hg => absurd rfl hg, fun _ hg => absurd rfl hg⟩,
    zeroState_synchronized j, ?_⟩
  funext f
  cases f with
  | field f => exact zeroState_sourceProfile j f
  | cutoff => rfl

end
end VaughtConjecture.Knight.CappedDonor.Ref
