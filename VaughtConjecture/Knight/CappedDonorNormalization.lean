/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorSource
public import VaughtConjecture.Knight.PairedSlotIncoming

/-! # Canonical normalization of the receiving family on the complete field inventory

The paired point/orbit normalization of the reviewer's `PairedSlotEncoding` /
`PairedSlotIncoming` (ported with attribution) instantiated on the **complete receiving-field
inventory** `Field P C` — every request field, every private field (present or future) and the
gate — at the current cutoff `j`.

* The **inventory** of a state is the set of ordinal values of its single source vector
  (`State.inventory`); the **canonical incoming encoder** is the paired-slot encoder of that
  inventory at grade `j` (`State.encoder`), a bottom-reflecting normalized witness with suppressor
  `gTop j` that leaves literal top literally.  **Normalization** applies it to every field
  (`normalizeState`); on the source vector it is exactly the paired-slot `normalize`
  (`sourceProfile_normalizeState`).
* **Preservation.**  Normalization preserves admissibility (`normalizeState_admissible`) and
  synchronization (`normalizeState_synchronized`) — this is `Admissible.map` at the *current*
  grade `j`, not the private arity: the encoder commutes with replacement through the grades
  present, and through `N` exactly when the cap is present.
* **Coded, short, literal top.**  Every normalized source value other than literal top lies in the
  coded alphabet with block bound `2·|Field P C|` (`normalizeState_coded`, the inventory count of
  the complete field vector, no boundary-cardinality substitute); every normalized source value
  is `j`-short (`normalizeState_short`); literal top and bottom are preserved
  (`normalizeState_top`, `normalizeState_bot_iff`).
* **Relative prefix preservation.**  Two states agreeing on every source field below a
  `j`-visible cut `h` have the same normalized value at every field whose value lies below `h`
  (`normalizeState_prefix`): the codes below the cut are determined by the prefix.
* **Normalized repairs stay in the catalogue.**  Both same-grade fibres on source profiles
  compose with normalization: the lift and its normalization are admissible and synchronized,
  the normalized lift is coded and short, and the cap receipts of the lift are those of the
  source-profile fibres (`exists_private_lift_normalized`, `exists_request_lift_normalized`).

Nothing here extracts a source profile from a physical section; the physical decoder side
(`PairedSlotDecoder`) is not used. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

namespace CappedDonor

variable {nP J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}

/-- The field inventory as a sum type. -/
def Field.equivSum : Field P C ≃ Cell P.scheme ⊕ Cell C.scheme ⊕ Unit where
  toFun
    | .req d => Sum.inl d
    | .priv d => Sum.inr (Sum.inl d)
    | .gate => Sum.inr (Sum.inr ())
  invFun
    | Sum.inl d => .req d
    | Sum.inr (Sum.inl d) => .priv d
    | Sum.inr (Sum.inr _) => .gate
  left_inv f := by cases f <;> rfl
  right_inv s := by rcases s with d | d | ⟨⟩ <;> rfl

instance : Fintype (Field P C) := Fintype.ofEquiv _ Field.equivSum.symm

namespace Ref

variable {I : Type*} [Fintype I] {N : ℕ} {R : Ref I nP N J P C}

/-! ## The inventory and the canonical incoming encoder -/

/-- The receiving inventory of a state: the ordinal values of its source vector. -/
noncomputable def State.inventory {j : ℕ} (st : R.State j) : Finset Ordinal.{0} :=
  PairedSlotEncoding.values st.sourceProfile

/-- The canonical incoming encoder of a state at its cutoff. -/
noncomputable def State.encoder {j : ℕ} (st : R.State j) : ExtOrd → ExtOrd :=
  PairedSlotIncoming.encoder j st.inventory

theorem State.encoder_witness {j : ℕ} (st : R.State j) : Witness (gTop j) st.encoder :=
  PairedSlotIncoming.encoder_witness j st.inventory

theorem State.encoder_reflects_bottom {j : ℕ} (st : R.State j) (x : ExtOrd)
    (h : st.encoder x = ⊥) : x = ⊥ :=
  PairedSlotIncoming.encoder_reflects_bottom j st.inventory x h

/-- The encoder leaves literal top literally. -/
theorem State.encoder_top {j : ℕ} (st : R.State j) : st.encoder ⊤ = ⊤ := by
  unfold State.encoder PairedSlotIncoming.encoder
  rw [ite_eq_left rfl]

/-- **Canonical normalization** of a state: the encoder applied to every field. -/
noncomputable def normalizeState {j : ℕ} (st : R.State j) : R.State j := mapState st.encoder st

/-- On the source vector, normalization is the paired-slot normalization. -/
theorem sourceProfile_normalizeState {j : ℕ} (st : R.State j) (f : Field P C) :
    (normalizeState st).sourceProfile f = PairedSlotEncoding.normalize j st.sourceProfile f := by
  rw [normalizeState, sourceProfile_map]
  exact PairedSlotIncoming.encoder_profile j st.sourceProfile f

/-! ## Preservation -/

/-- Normalization preserves admissibility, at the current grade. -/
theorem normalizeState_admissible {j : ℕ} (hj : 1 ≤ j) {st : R.State j}
    (hst : R.Admissible st) : R.Admissible (normalizeState st) :=
  hst.map st.encoder_witness (min_le_left j J) hj st.encoder_reflects_bottom

/-- Normalization preserves synchronization. -/
theorem normalizeState_synchronized {j : ℕ} (hj : 1 ≤ j) {st : R.State j}
    (hs : Synchronized st) : Synchronized (normalizeState st) :=
  hs.map st.encoder_witness hj

/-! ## Coded, short, literal top -/

/-- Every normalized source value other than literal top lies in the coded alphabet with block
bound twice the size of the complete field inventory. -/
theorem normalizeState_coded {j : ℕ} (st : R.State j) (f : Field P C)
    (hf : st.sourceProfile f ≠ ⊤) :
    (normalizeState st).sourceProfile f ∈
      ExtOrd.codedAlphabet (2 * Fintype.card (Field P C)) j := by
  rw [sourceProfile_normalizeState]
  exact PairedSlotEncoding.normalize_mem j st.sourceProfile f hf

/-- Every normalized source value is `j`-short. -/
theorem normalizeState_short {j : ℕ} (st : R.State j) (f : Field P C) :
    SharpWitnessComposition.Short j ((normalizeState st).sourceProfile f) := by
  rw [sourceProfile_normalizeState]
  rcases ExtOrd.cases (st.sourceProfile f) with hb | ht | ⟨a, ha⟩
  · exact Or.inl ((PairedSlotEncoding.normalize_bot_iff j _ f).mpr hb)
  · exact Or.inr (Or.inl (by simp only [PairedSlotEncoding.normalize, ht]))
  · refine Or.inr (Or.inr ⟨_, PairedSlotEncoding.normalize_ofOrd ha, ?_⟩)
    rw [finitePart_mul_add]
    exact PairedSlotEncoding.offset_le j _ a

/-- Literal top is preserved. -/
theorem normalizeState_top {j : ℕ} (st : R.State j) (f : Field P C)
    (hf : st.sourceProfile f = ⊤) : (normalizeState st).sourceProfile f = ⊤ := by
  rw [sourceProfile_normalizeState]
  simp only [PairedSlotEncoding.normalize, hf]

/-- Bottom is preserved and reflected. -/
theorem normalizeState_bot_iff {j : ℕ} (st : R.State j) (f : Field P C) :
    (normalizeState st).sourceProfile f = ⊥ ↔ st.sourceProfile f = ⊥ := by
  rw [sourceProfile_normalizeState]
  exact PairedSlotEncoding.normalize_bot_iff j _ f

/-! ## Relative prefix preservation -/

/-- States agreeing on every source field below a `j`-visible cut have the same normalized value
at every field whose value lies below the cut. -/
theorem normalizeState_prefix {j : ℕ} {st st' : R.State j} {h : Ordinal.{0}}
    (hh : j ≤ finitePart h)
    (hpq : ∀ f, min (st.sourceProfile f) (ofOrd h) = min (st'.sourceProfile f) (ofOrd h))
    (f : Field P C) (hf : st.sourceProfile f < ofOrd h) :
    (normalizeState st).sourceProfile f = (normalizeState st').sourceProfile f := by
  rw [sourceProfile_normalizeState, sourceProfile_normalizeState]
  exact PairedSlotEncoding.normalize_prefix hh hpq f hf

/-! ## Normalized repairs stay in the catalogue -/

/-- The private fibre on source profiles, followed by normalization: the lift and its
normalization are admissible and synchronized; the normalized lift is coded and short. -/
theorem exists_private_lift_normalized {j : ℕ} (hj : 1 ≤ j) {st : R.State j}
    (hst : R.Admissible st) (hs : Synchronized st) {v₁ : C.scheme.below (effC J j) → ExtOrd}
    (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁) {γ : ExtOrd}
    (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (v₁ d) γ = min (st.v d) γ) :
    ∃ st₁ : R.State j, R.Admissible st₁ ∧ Synchronized st₁ ∧ st₁.v = v₁ ∧
      (∀ d, min (st₁.u d) γ = min (st.u d) γ) ∧ R.CapReceipts γ st st₁ ∧
      R.Admissible (normalizeState st₁) ∧ Synchronized (normalizeState st₁) ∧
      ∀ f, SharpWitnessComposition.Short j ((normalizeState st₁).sourceProfile f) := by
  obtain ⟨st₁, hst₁, hs₁, hv, hu, hrec⟩ := R.exists_private_lift_sync hst hs hv₁ hγ hagree
  exact ⟨st₁, hst₁, hs₁, hv, hu, hrec, normalizeState_admissible hj hst₁,
    normalizeState_synchronized hj hs₁, normalizeState_short st₁⟩

/-- The request fibre on source profiles, followed by normalization. -/
theorem exists_request_lift_normalized {j : ℕ} (hj : 1 ≤ j) {st : R.State j}
    (hst : R.Admissible st) (hs : Synchronized st) {u₁ : P.scheme.below (effP nP j) → ExtOrd}
    (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁) {γ : ExtOrd}
    (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (u₁ d) γ = min (st.u d) γ) :
    ∃ st₁ : R.State j, R.Admissible st₁ ∧ Synchronized st₁ ∧ st₁.u = u₁ ∧
      (∀ d, min (st₁.v d) γ = min (st.v d) γ) ∧ R.CapReceipts γ st st₁ ∧
      R.Admissible (normalizeState st₁) ∧ Synchronized (normalizeState st₁) ∧
      ∀ f, SharpWitnessComposition.Short j ((normalizeState st₁).sourceProfile f) := by
  obtain ⟨st₁, hst₁, hs₁, hu, hv, hrec⟩ := R.exists_request_lift_sync hst hs hu₁ hγ hagree
  exact ⟨st₁, hst₁, hs₁, hu, hv, hrec, normalizeState_admissible hj hst₁,
    normalizeState_synchronized hj hs₁, normalizeState_short st₁⟩

end Ref

end CappedDonor

end VaughtConjecture.Knight
