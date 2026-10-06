/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RefinedRowFamily
public import VaughtConjecture.Knight.PositiveNormalization
public import VaughtConjecture.Knight.MixedRows
public import VaughtConjecture.Knight.RestrictedComposition

/-! # Relabelling witnesses at a non-limit cut, and relabelled decoding

The reviewer's qualification (2026-09-17): the relabelling that serves the intermediate cells
carrying a copy of `H₀old` must fix the request as well as the proper old readings; for offsets
at most two, cutting at `ω + 3` fits, and the request's position relative to the cut must be
stated explicitly.  This file provides the two generic tools.

**A witness at a non-limit cut** (`witness_cutRelabel`).  `spliceAt (ω·t + c) id w` — the
identity below `ω·t + c`, the constant `w` from there on — is a `gTop K`-witness whenever
`K < c`, `w` is self-visible at `K`, and `ω·t + c ≤ w`.  Clause 5 holds because visibility
replacement at thresholds `k ≤ K < c` with offsets `i ≤ k` never crosses the cut
(`extVisibilityReplace_lt_cut`, `cut_le_extVisibilityReplace`).  This differs from
`witness_spliceAt`, whose cut is a block floor.

**Relabelled decoding** (`recode_transformsTo_relabel`).  The decoding shifter is itself a
`gTop l`-witness (`shift_witness_top`); composed with any bottom-reflecting `gTop K`-witness
`φ` (`K ≥ l`) it yields a faithful transformation from the recoding at `l` of a keyed labelling
`p` to `φ ∘ p`.  With `φ` the identity this is `recode_transformsTo` at cap `⊤`.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Replacement does not cross a cut `ω·t + c` at thresholds below `c` -/

/-- Below the cut stays below: `x < ω·t + c` and `i < c` give `R_k^i x < ω·t + c`. -/
theorem extVisibilityReplace_lt_cut {t c : ℕ} {x : ExtOrd}
    (hx : x < ofOrd (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal))) {k i : ℕ} (hi : i < c) :
    extVisibilityReplace x k i < ofOrd (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal)) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · rw [extVisibilityReplace_bot]; exact bot_lt_ofOrd _
  · exact absurd hx not_top_lt
  · rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
    rw [ofOrd_lt_ofOrd] at hx
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hβ : β ≤ Ordinal.omega0 * (t : Ordinal) + (c' : Ordinal) := by
      rw [Nat.cast_succ, ← add_assoc] at hx
      exact Order.lt_add_one_iff.mp hx
    have h := visibilityReplace_le_add_of_le_of_limitPart_eq (limitPart_mul_nat t) hβ k
      (show i ≤ c' by omega)
    rw [Nat.cast_succ, ← add_assoc]
    exact Order.lt_add_one_iff.mpr h

/-- At or above the cut stays there: `ω·t + c ≤ x` and `i ≤ k ≤ c` give
`ω·t + c ≤ R_k^i x`. -/
theorem cut_le_extVisibilityReplace {t c : ℕ} {x : ExtOrd}
    (hx : ofOrd (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal)) ≤ x) {k i : ℕ} (hk : k ≤ c)
    (hi : i ≤ k) :
    ofOrd (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal)) ≤ extVisibilityReplace x k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact absurd hx (not_ofOrd_le_bot _)
  · rw [extVisibilityReplace_top]; exact le_top
  · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
    rw [ofOrd_le_ofOrd] at hx
    rcases hx.lt_or_eq with hlt | heq
    · exact le_visibilityReplace_of_lt_of_limitPart_eq (limitPart_mul_nat t) hlt hk hi
    · rw [← heq, visibilityReplace_of_not_lt]
      rw [finitePart_mul_add]
      exact not_lt.mpr hk

/-! ## The cut relabelling -/

/-- **A witness at a non-limit cut**: the identity below `ω·t + c`, the constant `w` from there
on, is a `gTop K`-witness when `K < c`, `w` is self-visible at `K`, and `ω·t + c ≤ w`. -/
theorem witness_cutRelabel {K t c : ℕ} (hKc : K < c) {w : ExtOrd} (hw : SelfVis K w)
    (hcw : ofOrd (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal)) ≤ w) :
    Witness (gTop K) (spliceAt (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal)) id w) where
  anti := (witness_id K).anti
  vis := (witness_id K).vis
  bot := by rw [spliceAt_of_lt (bot_lt_ofOrd _)]; rfl
  mono := by
    intro x y hxy
    by_cases hx : x < ofOrd (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal))
    · rw [spliceAt_of_lt hx]
      by_cases hy : y < ofOrd (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal))
      · rw [spliceAt_of_lt hy]; exact hxy
      · rw [spliceAt_of_le (not_lt.mp hy)]; exact hx.le.trans hcw
    · have hx' := not_lt.mp hx
      rw [spliceAt_of_le hx', spliceAt_of_le (hx'.trans hxy)]
  clause5 := by
    intro α k hα i hi
    by_cases hk : k ≤ K
    · by_cases hx : α < ofOrd (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal))
      · rw [spliceAt_of_lt hx, spliceAt_of_lt (extVisibilityReplace_lt_cut hx (by omega))]
        rfl
      · have hx' := not_lt.mp hx
        rw [spliceAt_of_le hx',
          spliceAt_of_le (cut_le_extVisibilityReplace hx' (by omega) hi)]
        exact (extVisibilityReplace_eq_of_selfVis hw hk).symm
    · rw [gTop_of_gt (not_le.mp hk)] at hα
      have h0 := le_bot_iff.mp hα
      have hαb : α = ⊥ := by
        by_cases hx : α < ofOrd (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal))
        · rw [spliceAt_of_lt hx] at h0; exact h0
        · rw [spliceAt_of_le (not_lt.mp hx)] at h0
          exact absurd (h0 ▸ hcw) (not_ofOrd_le_bot _)
      subst hαb
      rw [extVisibilityReplace_bot, h0, extVisibilityReplace_bot]

/-- The cut relabelling reflects bottom when its constant is above the cut. -/
theorem cutRelabel_bot_reflecting {t c : ℕ} {w : ExtOrd}
    (hcw : ofOrd (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal)) ≤ w) (x : ExtOrd)
    (h : spliceAt (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal)) id w x = ⊥) : x = ⊥ := by
  by_cases hx : x < ofOrd (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal))
  · rw [spliceAt_of_lt hx] at h; exact h
  · rw [spliceAt_of_le (not_lt.mp hx)] at h
    exact absurd (h ▸ hcw) (not_ofOrd_le_bot _)

/-- The cut relabelling is bounded by its constant when the constant is above the cut. -/
theorem cutRelabel_le {t c : ℕ} {w : ExtOrd}
    (hcw : ofOrd (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal)) ≤ w) (x : ExtOrd) :
    spliceAt (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal)) id w x ≤ w := by
  by_cases hx : x < ofOrd (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal))
  · rw [spliceAt_of_lt hx]; exact hx.le.trans hcw
  · rw [spliceAt_of_le (not_lt.mp hx)]

/-- The cut relabelling preserves self-visibility at thresholds where its constant is
self-visible. -/
theorem cutRelabel_selfVis {t c K : ℕ} {w : ExtOrd} (hw : SelfVis K w) {x : ExtOrd}
    (hx : SelfVis K x) :
    SelfVis K (spliceAt (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal)) id w x) := by
  by_cases h : x < ofOrd (Ordinal.omega0 * (t : Ordinal) + (c : Ordinal))
  · rw [spliceAt_of_lt h]; exact hx
  · rw [spliceAt_of_le (not_lt.mp h)]; exact hw

/-! ## Relabelled decoding -/

/-- The decoding shifter at cap `⊤` is a `gTop l`-witness. -/
theorem shift_witness_top (l : ℕ) (S : Finset Ordinal.{0}) : Witness (gTop l) (shift l S ⊤) where
  anti := (witness_id l).anti
  vis := (witness_id l).vis
  bot := shift_bot l S ⊤
  mono := shift_mono l S ⊤ (extVisibilityReplace_top _ _) (fun _ _ => le_top)
  clause5 := by
    intro α k hle i hi
    by_cases hk : k ≤ l
    · exact shift_evr_of_le l S ⊤ (extVisibilityReplace_top _ _) hk α hi
    · rw [gTop_of_gt (not_le.mp hk)] at hle
      have h0 : shift l S ⊤ α = ⊥ := le_bot_iff.mp hle
      rw [shift_evr_of_bot l S ⊤ α k i h0, h0]
      simp

/-- Decoding inverts the recoding on keyed values. -/
theorem shift_recode_of_inVals {l : ℕ} {S : Finset Ordinal.{0}} {x : ExtOrd}
    (h : InVals S x) : shift l S ⊤ (recode l S x) = x := by
  rcases h with h | h | ⟨v, hv, h⟩ <;> rw [h]
  · rw [recode_bot, shift_bot]
  · rw [recode_top, shift_capCode]
  · rw [recode_ofOrd, shift_code l S ⊤ hv]

/-- **Relabelled decoding**: the recoding at `l` of a keyed labelling `p` transforms faithfully
to `φ ∘ p` for every bottom-reflecting `gTop K`-witness `φ` with `l ≤ K`. -/
theorem recode_transformsTo_relabel {D : Type*} {l : ℕ} {S : Finset Ordinal.{0}}
    (grade : D → ℕ) (hgr : ∀ d, grade d ≤ l) (p : D → ExtOrd) (hp : ∀ d, InVals S (p d))
    {K : ℕ} (hlK : l ≤ K) {φ : ExtOrd → ExtOrd} (hφ : Witness (gTop K) φ)
    (hbot : ∀ x, φ x = ⊥ → x = ⊥) :
    TransformsTo grade (fun d => recode l S (p d)) (fun d => φ (p d)) :=
  (Witness.comp_of_bottom_reflecting (shift_witness_top l S) hφ hlK hbot).transformsTo
    (fun d => by
      change φ (p d) = min (φ (shift l S ⊤ (recode l S (p d)))) (gTop l (grade d))
      rw [shift_recode_of_inVals (hp d), gTop_of_le (hgr d), min_eq_left le_top])

/-! ## Cuts at an arbitrary limit part, and replacement-closed cuts -/

/-- Below the cut `μ + c` stays below, for `μ` a limit part. -/
theorem extVisibilityReplace_lt_cut' {μ : Ordinal.{0}} (hμ : limitPart μ = μ) {c : ℕ}
    {x : ExtOrd} (hx : x < ofOrd (μ + (c : Ordinal))) {k i : ℕ} (hi : i < c) :
    extVisibilityReplace x k i < ofOrd (μ + (c : Ordinal)) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · rw [extVisibilityReplace_bot]; exact bot_lt_ofOrd _
  · exact absurd hx not_top_lt
  · rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
    rw [ofOrd_lt_ofOrd] at hx
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hβ : β ≤ μ + (c' : Ordinal) := by
      rw [Nat.cast_succ, ← add_assoc] at hx
      exact Order.lt_add_one_iff.mp hx
    have h := visibilityReplace_le_add_of_le_of_limitPart_eq hμ hβ k (show i ≤ c' by omega)
    rw [Nat.cast_succ, ← add_assoc]
    exact Order.lt_add_one_iff.mpr h

/-- At or above the cut `μ + c` stays there, for `μ` a limit part. -/
theorem cut_le_extVisibilityReplace' {μ : Ordinal.{0}} (hμ : limitPart μ = μ) {c : ℕ}
    {x : ExtOrd} (hx : ofOrd (μ + (c : Ordinal)) ≤ x) {k i : ℕ} (hk : k ≤ c) (hi : i ≤ k) :
    ofOrd (μ + (c : Ordinal)) ≤ extVisibilityReplace x k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact absurd hx (not_ofOrd_le_bot _)
  · rw [extVisibilityReplace_top]; exact le_top
  · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
    rw [ofOrd_le_ofOrd] at hx
    rcases hx.lt_or_eq with hlt | heq
    · exact le_visibilityReplace_of_lt_of_limitPart_eq hμ hlt hk hi
    · rw [← heq, visibilityReplace_of_not_lt]
      rw [finitePart_limitPart_add_nat' hμ]
      exact not_lt.mpr hk

/-- A cut `θ` is **replacement-closed at `K`**: at thresholds `k ≤ K` with offsets `i ≤ k`,
replacement preserves being below `θ`. -/
def CutClosed (K : ℕ) (θ : ExtOrd) : Prop :=
  ∀ (x : ExtOrd) (k i : ℕ), k ≤ K → i ≤ k → (extVisibilityReplace x k i < θ ↔ x < θ)

theorem cutClosed_ofOrd {K : ℕ} {μ : Ordinal.{0}} (hμ : limitPart μ = μ) {c : ℕ} (hKc : K < c) :
    CutClosed K (ofOrd (μ + (c : Ordinal))) := by
  intro x k i hk hi
  constructor
  · intro h
    by_contra hx
    exact absurd h (not_lt.mpr (cut_le_extVisibilityReplace' hμ (not_lt.mp hx) (by omega) hi))
  · intro h
    exact extVisibilityReplace_lt_cut' hμ h (by omega)

theorem cutClosed_top (K : ℕ) : CutClosed K ⊤ := by
  intro x k i _ _
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · rw [extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top]
  · rw [extVisibilityReplace_ofOrd]
    exact ⟨fun _ => ofOrd_lt_top _, fun _ => ofOrd_lt_top _⟩

/-- A nonbottom value self-visible at grade three is a replacement-closed cut at `2`. -/
theorem cutClosed_of_selfVis {θ : ExtOrd} (hv : SelfVis 3 θ) (hne : θ ≠ ⊥) : CutClosed 2 θ := by
  rcases ExtOrd.cases θ with rfl | rfl | ⟨ν, rfl⟩
  · exact absurd rfl hne
  · exact cutClosed_top 2
  · have hfp : 3 ≤ finitePart ν := selfVis_ofOrd_iff.mp hv
    have hμ : limitPart (limitPart ν) = limitPart ν := by
      have := limitPart_limitPart_add_nat ν 0
      rwa [Nat.cast_zero, add_zero] at this
    have hdec : ν = limitPart ν + (finitePart ν : Ordinal) := (limitPart_add_finitePart ν).symm
    rw [hdec]
    exact cutClosed_ofOrd hμ (by omega)

/-- **The cut splice**: `τ` below `θ`, the constant `w` from `θ` on. -/
noncomputable def cutIf (θ : ExtOrd) (τ : ExtOrd → ExtOrd) (w x : ExtOrd) : ExtOrd :=
  if x < θ then τ x else w

theorem cutIf_of_lt {θ : ExtOrd} {τ : ExtOrd → ExtOrd} {w x : ExtOrd} (h : x < θ) :
    cutIf θ τ w x = τ x := by
  unfold cutIf; exact ite_eq_left h

theorem cutIf_of_le {θ : ExtOrd} {τ : ExtOrd → ExtOrd} {w x : ExtOrd} (h : θ ≤ x) :
    cutIf θ τ w x = w := by
  unfold cutIf; exact ite_eq_right (not_lt.mpr h)

/-- **A witness at a replacement-closed cut**: `τ` below `θ`, the constant `w` from `θ` on, is a
`gTop K`-witness when `θ` is replacement-closed at `K` and positive, `τ` is a bottom-reflecting
`gTop K`-witness, `w` is self-visible at `K` and nonbottom, and `τ` is bounded by `w` below the
cut. -/
theorem witness_cutIf {K : ℕ} {θ : ExtOrd} (hθ : CutClosed K θ) (hθ0 : (⊥ : ExtOrd) < θ)
    {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop K) τ) (hτbot : ∀ x, τ x = ⊥ → x = ⊥)
    {w : ExtOrd} (hw : SelfVis K w) (hwne : w ≠ ⊥) (hle : ∀ x, x < θ → τ x ≤ w) :
    Witness (gTop K) (cutIf θ τ w) where
  anti := (witness_id K).anti
  vis := (witness_id K).vis
  bot := by rw [cutIf_of_lt hθ0]; exact hτ.bot
  mono := by
    intro x y hxy
    by_cases hx : x < θ
    · rw [cutIf_of_lt hx]
      by_cases hy : y < θ
      · rw [cutIf_of_lt hy]; exact hτ.mono hxy
      · rw [cutIf_of_le (not_lt.mp hy)]; exact hle x hx
    · have hx' := not_lt.mp hx
      rw [cutIf_of_le hx', cutIf_of_le (hx'.trans hxy)]
  clause5 := by
    intro α k hα i hi
    by_cases hk : k ≤ K
    · by_cases hx : α < θ
      · rw [cutIf_of_lt hx] at hα
        rw [cutIf_of_lt hx, cutIf_of_lt ((hθ α k i hk hi).mpr hx)]
        exact hτ.clause5 α k hα i hi
      · have hx' := not_lt.mp hx
        rw [cutIf_of_le hx', cutIf_of_le (not_lt.mp (fun h => hx ((hθ α k i hk hi).mp h)))]
        exact (extVisibilityReplace_eq_of_selfVis hw hk).symm
    · rw [gTop_of_gt (not_le.mp hk)] at hα
      have h0 := le_bot_iff.mp hα
      have hαb : α = ⊥ := by
        by_cases hx : α < θ
        · rw [cutIf_of_lt hx] at h0; exact hτbot α h0
        · rw [cutIf_of_le (not_lt.mp hx)] at h0; exact absurd h0 hwne
      subst hαb
      rw [extVisibilityReplace_bot, h0, extVisibilityReplace_bot]

theorem cutIf_bot_reflecting {θ : ExtOrd} {τ : ExtOrd → ExtOrd} (hτbot : ∀ x, τ x = ⊥ → x = ⊥)
    {w : ExtOrd} (hwne : w ≠ ⊥) (x : ExtOrd) (h : cutIf θ τ w x = ⊥) : x = ⊥ := by
  by_cases hx : x < θ
  · rw [cutIf_of_lt hx] at h; exact hτbot x h
  · rw [cutIf_of_le (not_lt.mp hx)] at h; exact absurd h hwne

theorem cutIf_le {θ : ExtOrd} {τ : ExtOrd → ExtOrd} {w : ExtOrd} (hle : ∀ x, x < θ → τ x ≤ w)
    (x : ExtOrd) : cutIf θ τ w x ≤ w := by
  by_cases hx : x < θ
  · rw [cutIf_of_lt hx]; exact hle x hx
  · rw [cutIf_of_le (not_lt.mp hx)]

theorem cutIf_selfVis {K : ℕ} {θ : ExtOrd} {τ : ExtOrd → ExtOrd} {w : ExtOrd} (hw : SelfVis K w)
    {x : ExtOrd} (hx : SelfVis K (τ x)) : SelfVis K (cutIf θ τ w x) := by
  by_cases h : x < θ
  · rw [cutIf_of_lt h]; exact hx
  · rw [cutIf_of_le (not_lt.mp h)]; exact hw

end VaughtConjecture.Knight
