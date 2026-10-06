/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingContext

/-! # Short block encoding below a proper stable marker

The physical chart commutes through `N`; the encoder has width `L < N`
and need only commute through the donor grade `r < L`. The encoder is
constructed from reference readings, including the new stable block.
No source encoding or source-strip separation is assumed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthFiniteCapEncoding
open Value ExtOrd SharpWitnessComposition
noncomputable section
variable {N L r i : ℕ} {τ : ExtOrd → ExtOrd} (hτ : BoundedMap N τ)
  {α sa : Ordinal.{0}} (hα : limitPart α = α)
  (ha : τ (ofOrd sa) = ofOrd (α + i)) (hi : i < N)
  (hLN : L < N) (hrL : r < L)
  (S : Finset Ordinal.{0}) (hS : ∀ μ ∈ S, limitPart μ = μ)
  (hle : ∀ μ ∈ S, μ ≤ α) (src : Ordinal.{0} → Ordinal.{0})
  (off : Ordinal.{0} → ℕ) (hoff : ∀ μ ∈ S, off μ < N)
  (hread : ∀ μ ∈ S, τ (ofOrd (src μ)) = ofOrd (μ + off μ))

include hτ hα ha hi hLN in
theorem marker_read :
    τ (ofOrd (limitPart sa + L)) = ofOrd (α + L) := by
  have hf : finitePart (α + i) < N := by rw [finitePart_add_nat_of_limit hα]; exact hi
  have hs := (read_finitePart hτ ha hf).1
  have he := hτ.comm (ofOrd sa) N L le_rfl hLN.le
  rwa [extVisibilityReplace_of_finitePart_lt hs, ha,
    extVisibilityReplace_of_finitePart_lt hf, limitPart_add_nat_of_limit hα] at he

include hτ hα ha hi hS hle hoff hread in
theorem strip_le (μ : Ordinal.{0}) (hμ : μ ∈ S) :
    limitPart (src μ) ≤ limitPart sa := by
  have hf : finitePart (μ + off μ) < N := by
    rw [finitePart_add_nat_of_limit (hS μ hμ)]; exact hoff μ hμ
  have hfa : finitePart (α + i) < N := by rw [finitePart_add_nat_of_limit hα]; exact hi
  rcases (hle μ hμ).lt_or_eq with hm | hm
  · exact (strip_lt_of_read hτ (hread μ hμ) ha hf hfa (by
      rw [limitPart_add_nat_of_limit (hS μ hμ), limitPart_add_nat_of_limit hα]; exact hm)).le
  · exact (strip_unique_of_read hτ (hread μ hμ) ha hf hfa (by
      rw [limitPart_add_nat_of_limit (hS μ hμ), limitPart_add_nat_of_limit hα, hm])).le

include hτ hS hoff hread in
theorem strip_strict (μ : Ordinal.{0}) (hμ : μ ∈ S) (ν : Ordinal.{0})
    (hν : ν ∈ S) (hμν : μ < ν) : limitPart (src μ) < limitPart (src ν) := by
  apply strip_lt_of_read hτ (hread μ hμ) (hread ν hν)
  · rw [finitePart_add_nat_of_limit (hS μ hμ)]; exact hoff μ hμ
  · rw [finitePart_add_nat_of_limit (hS ν hν)]; exact hoff ν hν
  · rw [limitPart_add_nat_of_limit (hS μ hμ), limitPart_add_nat_of_limit (hS ν hν)]
    exact hμν

/-- The shorter encoder is an existing `BlockCode`, with a genuinely smaller
width than the physical grade. The source-strip bounds are derived from the
actual chart's reference and marker readings. -/
def code : BlockCode :=
  BlockCode.ofFinset L r hrL S (fun μ => limitPart (src μ)) (limitPart sa + L)
    (fun μ _ => limitPart_idem (src μ))
    (fun μ hμ => add_le_add_left (strip_le hτ hα ha hi S hS hle src off hoff hread μ hμ) _)
    (strip_strict hτ S hS src off hoff hread)
    (by rw [finitePart_limitPart_add_nat]; exact hrL.le)

theorem code_top : (code hτ hα ha hi hrL S hS hle src off hoff hread).code ⊤ =
    ofOrd (limitPart sa + L) := rfl

theorem code_listed {p : Ordinal.{0}} (hp : limitPart p ∈ S) (hfp : finitePart p ≤ L) :
    (code hτ hα ha hi hrL S hS hle src off hoff hread).code (ofOrd p) =
      ofOrd (limitPart (src (limitPart p)) + finitePart p) := by
  apply BlockCode.code_listed _ hp
    (BlockCode.ofFinset_Λ_listed L r hrL S _ _ _ _ _ _ hp) hfp

include hLN in
/-- Exact source alignment is derived from the chart, not added as an
encoding premise. This is used at every proper shared-root occurrence. -/
theorem code_of_read {p b : Ordinal.{0}} (hp : limitPart p ∈ S)
    (hfp : finitePart p < L) (hb : τ (ofOrd b) = ofOrd p) :
    (code hτ hα ha hi hrL S hS hle src off hoff hread).code (ofOrd p) = ofOrd b := by
  have href := hread (limitPart p) hp
  have ho : finitePart (limitPart p + off (limitPart p)) < N := by
    rw [finitePart_limitPart_add_nat]; exact hoff _ hp
  have hsame := strip_unique_of_read hτ hb href (hfp.trans hLN) ho (by
    rw [limitPart_add_nat_of_limit (limitPart_idem p)])
  have hf := (read_finitePart hτ hb (hfp.trans hLN)).2
  rw [code_listed hτ hα ha hi hrL S hS hle src off hoff hread hp hfp.le,
    ← hsame, ← hf, limitPart_add_finitePart]

end
end VaughtConjecture.Knight.GrowthFiniteCapEncoding
