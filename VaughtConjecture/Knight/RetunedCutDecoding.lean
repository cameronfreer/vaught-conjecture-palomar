/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AlignedCutEncoding

/-! # Separate the retuned readback level from the original agreement cap

Plan 29 may retune the first saturated strip to a level delta above gamma.
`decode_lift` then applies at delta, NOT at gamma. Its intermediate ambient
is constructed from the lawful source and the retuned witness. Positive-cap
transport against the original ambient proves its lawfulness, even on long
rows. The final output still agrees at the original gamma on every coordinate.

This discharges the two-cap transport step. Producing the retuned witness
and the lawful prefix-preserving coded completion remains separate.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.RetunedCutDecoding

open Transform Value ExtOrd SharpWitnessComposition

/-- No lawful intermediate ambient is supplied. It is constructed as sigma(s)
using original-cap agreement, before consuming the existing aligned decoder. -/
theorem decode_lift
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} {X : Type*} [Fintype X]
    (s : D.below BJ → ExtOrd) (p : X → ExtOrd) (incl : X → D.below BJ)
    {r q : D.below BJ → ExtOrd} {K b : ℕ} {a γ δ : ExtOrd} {σ : ExtOrd → ExtOrd}
    (hs : RespectsSemanticsBelow sem BJ s)
    (hr : RespectsSemanticsBelow sem BJ r) (hq : RespectsSemanticsBelow sem BJ q)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hσ : Witness (gTop K) σ) (hδ : SelfVis K δ) (hγb : γ ≠ ⊥) (hγδ : γ ≤ δ)
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (hactive : δ ≤ σ a)
    (hsource : ∀ d, min (r d) a = min (s d) a)
    (hambient : ∀ d, min (σ (s d)) γ = min (q d) γ)
    (hface : ∀ d, min (p d) δ = min (σ (s (incl d))) δ)
    (hlit : ∀ d, r (incl d) = AlignedCutEncoding.encode (s ∘ incl) p K b a δ d) :
    ∃ q' : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ q' ∧
      (∀ d, q' (incl d) = p d) ∧ ∀ d, min (q' d) γ = min (q d) γ := by
  have hδb : δ ≠ ⊥ := fun he => hγb (le_bot_iff.mp (he ▸ hγδ))
  have hmid : RespectsSemanticsBelow sem BJ (fun d => σ (s d)) :=
    map_respects_of_positive_cap_agreement hs hq hK (boundedMap_of_witness hσ) hγb hambient
  obtain ⟨q', hq', hread, hcap⟩ := AlignedCutEncoding.decode_lift s p incl hr hmid hK
    hσ hδ hδb hroom hactive hsource (fun _ => rfl) hface hlit
  refine ⟨q', hq', hread, ?_⟩
  intro d
  have he := congrArg (fun z => min z γ) (hcap d)
  simp only [min_assoc, min_eq_right hγδ] at he
  exact he.trans (hambient d)

end VaughtConjecture.Knight.RetunedCutDecoding
