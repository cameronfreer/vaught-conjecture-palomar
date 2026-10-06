/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorRepairPackage
public import VaughtConjecture.Knight.ReferenceContext

/-! # Selected-decoder support and the stage bound

Exact readback of the original fields does not bound the *auxiliary* labels of a selected
display: the decoder is also applied to unused grid points and to the terminal region.  The
strengthened terminal insertion (`Admitted.exists_terminal'`) sends **every** value to one
supported by the original field vector with bottom and top allowed
(`OrbitPrefixSupport.Supported N {⊤} a`).  This file derives the stage bound from that support:

* `supported_lt_limit`: at a limit `λ`, a value supported by a vector whose proper entries lie
  below `λ` and by a set whose non-top members lie below `λ` is itself below `λ` unless it is top
  (replacement never crosses a limit, `evr_lt_of_lt_limit`).
* `bottom_supply_lt_stage`: at a nonzero limit stage `α`, if every proper original field of the
  bottom-cap supply is below `α`, every proper decoded value is below `α` — unused grid points
  and the terminal region included, gate-off sources included.

No model-side receiving wrapper is introduced. -/

@[expose] public section

namespace VaughtConjecture.Knight.CappedDonor.Ref

open Transform Value ExtOrd
noncomputable section

/-- A supported value below a limit: replacement never crosses the limit, and the supporting set
is below it apart from top. -/
theorem supported_lt_limit {X : Type*} {K : ℕ} {l : Ordinal.{0}} (hl : limitPart l = l)
    {S : Set ExtOrd} (hS : ∀ z ∈ S, z ≠ ⊤ → z < ofOrd l) {a : X → ExtOrd}
    (ha : ∀ f, a f ≠ ⊤ → a f < ofOrd l) {x : ExtOrd}
    (hx : OrbitPrefixSupport.Supported K S a x) (hne : x ≠ ⊤) : x < ofOrd l := by
  rcases hx with rfl | hS' | ⟨f, i, -, rfl⟩
  · exact bot_lt_ofOrd _
  · exact hS x hS' hne
  · by_cases hf : a f = ⊤
    · rw [hf, extVisibilityReplace_top] at hne
      exact absurd rfl hne
    · exact evr_lt_of_lt_limit hl (ha f hf) K i

/-- The bound for values supported by the original vector with only top added. -/
theorem supported_top_lt_limit {X : Type*} {K : ℕ} {l : Ordinal.{0}} (hl : limitPart l = l)
    {a : X → ExtOrd} (ha : ∀ f, a f ≠ ⊤ → a f < ofOrd l) {x : ExtOrd}
    (hx : OrbitPrefixSupport.Supported K ({⊤} : Set ExtOrd) a x) (hne : x ≠ ⊤) :
    x < ofOrd l :=
  supported_lt_limit hl (fun _ hz hz' => absurd (Set.mem_singleton_iff.mp hz) hz') ha hx hne

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-- **The stage bound of the bottom-cap selected display.**  At a nonzero limit stage `α`, the
bottom-cap private supply's decoder sends every value whose original fields are proper and below
`α` to a value below `α`, unless it is top: unused grid points and the terminal region included,
the gate off. -/
theorem bottom_supply_lt_stage (α : LimitStage) {v₁ : C.scheme.below (effC J N) → ExtOrd}
    (hv₁ : RespectsSemanticsBelow C.rows (effC J N) v₁) :
    ∃ a : Field P C → ExtOrd, R.Admitted a ∧
      (∀ d : C.scheme.below (effC J N), a (.priv d.1) = v₁ d) ∧ a .gate = ⊥ ∧
      ∃ b₀ : Field P C → ExtOrd, R.Admitted b₀ ∧ (∀ f, b₀ f ≠ ⊤) ∧
        PairedSlotEncoding.normalize N b₀ ∈ R.Catalogue ∧
        ∃ δ : ExtOrd → ExtOrd, Witness (gTop N) δ ∧
          (∀ f, δ (PairedSlotEncoding.normalize N b₀ f) = a f) ∧
          ((∀ f, a f ≠ ⊤ → a f < ofOrd α.1) → ∀ x, δ x ≠ ⊤ → δ x < ofOrd α.1) := by
  obtain ⟨a, h1, h2, h3, b₀, h4, h5, h6, δ, hδ, hread, hsupp⟩ := bottom_supply' (R := R) hv₁
  refine ⟨a, h1, h2, h3, b₀, h4, h5, h6, δ, hδ, hread, fun ha x hne => ?_⟩
  exact supported_top_lt_limit (limitPart_eq_self_of_isNonSuccessor (Or.inr α.2)) ha (hsupp x) hne

end
end VaughtConjecture.Knight.CappedDonor.Ref
