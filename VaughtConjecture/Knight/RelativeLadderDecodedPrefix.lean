/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLadderRankRendering
public import VaughtConjecture.Knight.OrbitPrefixSupport

/-! # Decoded agreement on the complete installed ladder

The two renderings use one fixed outer ceiling. Scalar agreement and fixation
imply agreement on every actual occurrence, not just original readouts. Support
and the raw physical prefix are derived from the complete rank table. In
particular there is no shortness hypothesis on the long grade-one tips.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.RelativeLadderLayer
open Transform Value ExtOrd LadderScalarRendering
noncomputable section
variable {ι X Q : Type*} [DecidableEq ι] [Fintype X] [Fintype Q] {A : Finset ι}
variable (D : CellScheme A) (hA : 0 < A.card)
  (field : Cell D → X) (fields : Q → X → ExtOrd)

/-- Complete physical receipt, including unused ranks, foreign rungs and all
ceiling parents. No physical-support or physical-agreement premise is required. -/
theorem renderWith_decoded_agreement {a b : Q} {p q : X → ExtOrd} {C h : ExtOrd}
    (hra : ∀ x, ranks fields a x = fieldRank p x)
    (hrb : ∀ x, ranks fields b x = fieldRank q x)
    (ha : ∀ x, p x ≤ C) (hb : ∀ x, q x ≤ C) (hC : h ≤ C)
    (hag : ∀ x, min (p x) h = min (q x) h)
    {σ : ExtOrd → ExtOrd} (hm : Monotone σ) (hbot : σ ⊥ = ⊥)
    (hreach : h ≤ σ h) (hfix : ∀ x, p x < h → σ (p x) = p x)
    (d : Cell (carrier D hA (X := X) (Q := Q))) :
    min (σ (renderWith D hA field fields b q C d)) h =
      min (renderWith D hA field fields a p C d) h := by
  let u := renderWith D hA field fields a p C d
  let v := renderWith D hA field fields b q C d
  have hpref : min u h = min v h :=
    renderWith_agreement D hA field fields hra hrb ha hb hC hag d
  have hcap : min (σ u) h = min u h := by
    by_cases hu : u < h
    · have he : σ u = u := by
        rcases renderWith_supported D hA field fields a p C d with hz | ⟨x, hx⟩ | hc
        · change u = ⊥ at hz
          rw [hz, hbot]
        · change u = p x at hx
          rw [hx] at hu ⊢
          exact hfix x hu
        · exact (not_lt_of_ge hC (hc ▸ hu)).elim
      rw [he]
    · have hle := le_of_not_gt hu
      rw [min_eq_right hle, min_eq_right (hreach.trans (hm hle))]
  calc
    min (σ v) h = min (σ (min v h)) h := by
      rw [hm.map_min, min_assoc, min_eq_right hreach]
    _ = min (σ (min u h)) h := by rw [hpref]
    _ = min (σ u) h := by rw [hm.map_min, min_assoc, min_eq_right hreach]
    _ = min u h := hcap

/-- Once original restrictions are lawful, the actual installed rows are lawful
after decoding. Lawfulness transport is used once, after all cap equations.
Neither selected renderings at different grades nor short ladder tips are used. -/
theorem renderWith_decoded_respects (sem : Semantics D) (hp : ∀ d, D.scope d ≠ A)
    {j k : ℕ} (hjk : j ≤ k) {a b : Q} {p q : X → ExtOrd} {C h : ExtOrd}
    (hra : ∀ x, ranks fields a x = fieldRank p x)
    (hrb : ∀ x, ranks fields b x = fieldRank q x)
    (ha : ∀ x, p x ≤ C) (hb : ∀ x, q x ≤ C) (hC : h ≤ C)
    (hvp : ∀ x, SelfVis 1 (p x)) (hvq : ∀ x, SelfVis 1 (q x)) (hvC : SelfVis 1 C)
    (hlp : RespectsSemanticsBelow sem (A, j) (fun d => p (field d.1)))
    (hlq : RespectsSemanticsBelow sem (A, j) (fun d => q (field d.1)))
    (hag : ∀ x, min (p x) h = min (q x) h)
    {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop k) σ) (hpos : h ≠ ⊥)
    (hreach : h ≤ σ h) (hfix : ∀ x, p x < h → σ (p x) = p x) :
    RespectsSemanticsBelow (rows D sem hA field fields hp) (A, j)
      (fun d => σ (renderWith D hA field fields b q C d.1)) := by
  have hp' := renderWith_respects D sem hA field fields hp a p hra ha hvp hvC hlp
  have hq' := renderWith_respects D sem hA field fields hp b q hrb hb hvq hvC hlq
  exact SharpWitnessComposition.map_respects_of_positive_cap_agreement hq' hp'
    (fun d => d.2.2.trans hjk) (SharpWitnessComposition.boundedMap_of_witness hσ) hpos
    (fun d => renderWith_decoded_agreement D hA field fields hra hrb ha hb hC hag
      hσ.mono hσ.bot hreach hfix d.1)

end
end VaughtConjecture.Knight.RelativeLadderLayer
