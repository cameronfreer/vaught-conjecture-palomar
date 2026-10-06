/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProvisionalBandBridge

/-! # Locality of the provisional labelling at every top-labelled controller

Lemma 5.3.5 at an arbitrary `∞`-cell `Σ`: `E(Σ) ⇒ min (p⁺, p⁺(Σ))`.  At a maximal top witness
`Θ` the provisional value is the band map of `E(Θ)` (`ProvisionalBandBridge`); at a controller
`Σ ≠ Θ` the target `min (p⁺ d) (p⁺ Σ)` is the band map of `min (E(Θ)(d)) (E(Θ)(Σ))` on the
`∞`-cells — a function of the row of `Θ`, **not** of the row of `Σ` (row consistency
`E(Σ) ⇒ E(Θ)↾` may collapse band indices above the grade of `Σ`, so `p⁺` is not a band map of
`E(Σ)` and `TransformsTo.comp_bandMap` does not apply) — while on the finite cells it is the
label, reached from `E(Σ)` by the locality witness of the labels.

## The two-witness splice

`TransformsTo.merge_bandMap` composes the two: the label witness `⟨g, σ⟩ : E(Σ) ⇒ p↾` on the
region `σ < α`, and the band map of the row-consistency witness
`⟨g₁, σ₁⟩ : E(Σ) ⇒ min (E(Θ)↾, E(Θ)(Σ))` on the region `σ ≥ α`; the suppressor is `⊥` above
`J = grade Σ`, where `g = ⊤` keeps clause 5 honest exactly as in `comp_bandMap` (which is the
instance `σ₁ = id`, `g₁ = ⊤`).  This is not a general composite (Lemma 2.3.14 remains blocked,
#89/NC): both regions carry explicit hypotheses, and the cut between them is a constant below
`α`.

## The cap argument

Visibility replacement is **not** monotone in the value: `⊔⁺_k i a < a` when `i < fp a < k`.
So in the band region with `g₁ k < σ₁ a` (both at cap level, forced by injectivity of the band
map on the band, `cap_of_bandMap_eq_of_lt`) clause 5 cannot be read off monotonicity.
`cap_le_of_witness` instead reads clause 5 of `σ₁` at the *lowered* point `⊔⁺_k i a`, which
`⊔⁺_k (fp a)` sends back to `a`: were `σ₁ (⊔⁺_k i a)` below cap level, `σ₁ a` would be at most
`lam + K`, contradicting `g₁ k < σ₁ a`. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd

namespace Value

/-- An ordinal in the band `[lam, lam + K)` of a multiple `lam` of `ω` has limit part `lam`
and finite part `< K`. -/
theorem limitPart_eq_and_finitePart_lt_of_band {lam ν : Ordinal.{0}}
    (hlam : limitPart lam = lam) {K : ℕ} (h₁ : lam ≤ ν) (h₂ : ν < lam + K) :
    limitPart ν = lam ∧ finitePart ν < K := by
  have hle : lam ≤ limitPart ν := by have := limitPart_mono h₁; rwa [hlam] at this
  have heq : limitPart ν = lam := by
    rcases hle.lt_or_eq with hlt | heq
    · exfalso
      have h3 := add_omega0_le_limitPart_of_lt hlam hlt
      have h4 : lam + (K : Ordinal.{0}) < lam + Ordinal.omega0 :=
        (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _)
      exact absurd ((limitPart_le ν).trans_lt h₂) (not_lt.mpr (h4.le.trans h3))
    · exact heq.symm
  refine ⟨heq, ?_⟩
  have hdec := decomposition ν
  rw [heq] at hdec
  rw [← hdec] at h₂
  exact Nat.cast_lt.mp ((add_lt_add_iff_left lam).mp h₂)

/-- Below cap level, visibility replacement at `k ≤ K` with `j ≤ k` stays at or below cap. -/
theorem visibilityReplace_le_cap_of_lt {lam ρ : Ordinal.{0}} (hlam : limitPart lam = lam)
    {K k j : ℕ} (hρ : ρ < lam + K) (hk : k ≤ K) (hj : j ≤ k) :
    visibilityReplace ρ k j ≤ lam + K := by
  unfold visibilityReplace ordinalReplace
  split_ifs with h
  · have hlim : limitPart ρ ≤ lam := by
      by_contra hlt
      have h3 := add_omega0_le_limitPart_of_lt hlam (not_le.mp hlt)
      have h4 : lam + (K : Ordinal.{0}) < lam + Ordinal.omega0 :=
        (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _)
      exact absurd ((limitPart_le ρ).trans_lt hρ) (not_lt.mpr (h4.le.trans h3))
    exact add_le_add hlim ((Nat.cast_le (α := Ordinal.{0})).mpr (hj.trans hk))
  · exact hρ.le

/-- Visibility replacement does not drop below a multiple of `ω` that bounds the input. -/
theorem le_visibilityReplace_of_le_of_limitPart_eq {lam ν : Ordinal.{0}}
    (hlam : limitPart lam = lam) (hν : lam ≤ ν) (k i : ℕ) : lam ≤ visibilityReplace ν k i := by
  unfold visibilityReplace ordinalReplace
  split_ifs with h
  · have := limitPart_mono hν
    rw [hlam] at this
    exact this.trans (le_add_of_nonneg_right zero_le)
  · exact hν

/-- Replacing the finite part downwards (`i < fp ν < k`) is undone by replacing it back. -/
theorem visibilityReplace_visibilityReplace_finitePart {ν : Ordinal.{0}} {k i : ℕ}
    (hfp : finitePart ν < k) (hi : i < k) :
    visibilityReplace (visibilityReplace ν k i) k (finitePart ν) = ν := by
  have h1 : visibilityReplace ν k i = limitPart ν + i := by
    unfold visibilityReplace ordinalReplace; rw [ite_eq_left hfp]
  rw [h1]
  have h2 : finitePart (limitPart ν + i) < k := by rw [finitePart_limitPart_add_nat]; exact hi
  unfold visibilityReplace ordinalReplace
  rw [ite_eq_left h2, limitPart_limitPart_add_nat, decomposition]

end Value

namespace ExtOrd

/-- The band map commutes with `min` at or above `lam`. -/
theorem bandMap_min {α lam : Ordinal.{0}} (hlam : limitPart lam = lam) (K : ℕ) {x y : ExtOrd}
    (hx : ofOrd lam ≤ x) (hy : ofOrd lam ≤ y) :
    bandMap α lam K (min x y) = min (bandMap α lam K x) (bandMap α lam K y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (bandMap_mono_of_le hlam K hx h)]
  · rw [min_eq_right h, min_eq_right (bandMap_mono_of_le hlam K hy h)]

/-- At or above cap level the band map is the cap `α + K`. -/
theorem bandMap_of_cap_le {α lam : Ordinal.{0}} {K : ℕ} {x : ExtOrd}
    (hx : ofOrd (lam + K) ≤ x) : bandMap α lam K x = ofOrd (α + K) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · exact absurd hx (not_le.mpr (bot_lt_ofOrd _))
  · exact bandMap_top α lam K
  · exact bandMap_ofOrd_of_cap (ofOrd_le_ofOrd.mp hx)

/-- Two values at or above `lam`, strictly ordered, with the same band-map value, are both at
cap level (the band map is injective on the band `[lam, lam + K)`). -/
theorem cap_of_bandMap_eq_of_lt {α lam : Ordinal.{0}} (hlam : limitPart lam = lam) (K : ℕ)
    {x y : ExtOrd} (hx : ofOrd lam ≤ x) (hxy : x < y)
    (h : bandMap α lam K x = bandMap α lam K y) : ofOrd (lam + K) ≤ x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · exact absurd hx (not_le.mpr (bot_lt_ofOrd _))
  · exact absurd hxy (not_lt.mpr le_top)
  · by_contra hcap
    have hν : ν < lam + K := not_le.mp (fun h' => hcap (ofOrd_le_ofOrd.mpr h'))
    have hlν : lam ≤ ν := ofOrd_le_ofOrd.mp hx
    obtain ⟨hlimν, hfpν⟩ := limitPart_eq_and_finitePart_lt_of_band hlam hlν hν
    rw [bandMap_ofOrd_of_band hlν hν] at h
    rcases ExtOrd.cases y with rfl | rfl | ⟨ρ, rfl⟩
    · exact absurd hxy (not_lt.mpr bot_le)
    · rw [bandMap_top, ofOrd_inj] at h
      have := Nat.cast_injective (R := Ordinal.{0}) (add_left_cancel h)
      omega
    · have hνρ : ν < ρ := ofOrd_lt_ofOrd.mp hxy
      by_cases hρ : lam + K ≤ ρ
      · rw [bandMap_ofOrd_of_cap hρ, ofOrd_inj] at h
        have := Nat.cast_injective (R := Ordinal.{0}) (add_left_cancel h)
        omega
      · have hρ' : ρ < lam + K := not_le.mp hρ
        obtain ⟨hlimρ, _⟩ :=
          limitPart_eq_and_finitePart_lt_of_band hlam (hlν.trans hνρ.le) hρ'
        rw [bandMap_ofOrd_of_band (hlν.trans hνρ.le) hρ', ofOrd_inj] at h
        have hfp := Nat.cast_injective (R := Ordinal.{0}) (add_left_cancel h)
        have h1 := decomposition ν
        have h2 := decomposition ρ
        rw [hlimν] at h1
        rw [hlimρ, ← hfp] at h2
        rw [← h1, ← h2] at hνρ
        exact lt_irrefl _ hνρ

end ExtOrd

open Transform in
/-- In a transform witness `⟨g₁, σ₁⟩`, a value `a` sent strictly above a cap-level threshold
`g₁ k ≥ lam + K` stays at cap level under every visibility replacement at `k`: if the
replacement lowers `a` (`i < fp a < k`), clause 5 of `σ₁` at the lowered point `⊔⁺_k i a`
(which `⊔⁺_k (fp a)` sends back to `a`) would otherwise pin `σ₁ a ≤ lam + K`. -/
theorem cap_le_of_witness {g₁ : ℕ → ExtOrd} {σ₁ : ExtOrd → ExtOrd} (hσ₁mono : Monotone σ₁)
    (hσ₁5 : ∀ (a : ExtOrd) (k : ℕ), σ₁ a ≤ g₁ k → ∀ i : ℕ, i ≤ k →
      σ₁ (extVisibilityReplace a k i) = extVisibilityReplace (σ₁ a) k i)
    {lam : Ordinal.{0}} (hlam : limitPart lam = lam) {K k i : ℕ} (hk : k ≤ K) (_hi : i ≤ k)
    {a : ExtOrd} (hcap : ofOrd (lam + K) ≤ g₁ k) (hlt : g₁ k < σ₁ a) :
    ofOrd (lam + K) ≤ σ₁ (extVisibilityReplace a k i) := by
  have hcapa : ofOrd (lam + K) ≤ σ₁ a := hcap.trans hlt.le
  rcases ExtOrd.cases a with rfl | rfl | ⟨ν, rfl⟩
  · rwa [extVisibilityReplace_bot]
  · rwa [extVisibilityReplace_top]
  · rw [extVisibilityReplace_ofOrd]
    by_cases hfp : finitePart ν < k
    · have hrep : visibilityReplace ν k i = limitPart ν + i := by
        unfold visibilityReplace ordinalReplace; rw [ite_eq_left hfp]
      by_cases hi' : finitePart ν ≤ i
      · -- the replacement does not lower `a`
        have hle : ofOrd ν ≤ ofOrd (visibilityReplace ν k i) := by
          rw [hrep, ofOrd_le_ofOrd]
          calc ν = limitPart ν + (finitePart ν : Ordinal.{0}) := (decomposition ν).symm
            _ ≤ limitPart ν + (i : Ordinal.{0}) :=
                add_le_add (le_refl _) ((Nat.cast_le (α := Ordinal.{0})).mpr hi')
        exact hcapa.trans (hσ₁mono hle)
      · -- the replacement lowers `a`; read clause 5 at the lowered point
        have hi'' : i < finitePart ν := not_le.mp hi'
        by_contra hcon
        have hb : σ₁ (ofOrd (visibilityReplace ν k i)) ≤ g₁ k :=
          (not_le.mp hcon).le.trans hcap
        have h5 := hσ₁5 _ k hb (finitePart ν) hfp.le
        rw [extVisibilityReplace_ofOrd,
          visibilityReplace_visibilityReplace_finitePart hfp (hi''.trans hfp)] at h5
        rw [h5] at hlt
        rcases ExtOrd.cases (σ₁ (ofOrd (visibilityReplace ν k i))) with hb' | ht' | ⟨ρ, hρ⟩
        · rw [hb', extVisibilityReplace_bot] at hlt
          exact absurd (hcap.trans_lt hlt) (not_lt.mpr bot_le)
        · rw [ht'] at hcon
          exact hcon le_top
        · rw [hρ] at hlt hcon
          have hρ' : ρ < lam + K := ofOrd_lt_ofOrd.mp (not_le.mp hcon)
          rw [extVisibilityReplace_ofOrd] at hlt
          have := visibilityReplace_le_cap_of_lt hlam hρ' hk hfp.le
          exact absurd (hcap.trans_lt hlt) (not_lt.mpr (ofOrd_le_ofOrd.mpr this))
    · rw [visibilityReplace_of_not_lt hfp]; exact hcapa

open Transform in
/-- **Two-witness band-map merge.**  On a finite cell family of grades `≤ J ≤ K`:
`⟨g, σ⟩ : p ⇒ q` with `g = ⊤` up to `J` and `q` valued below `α` or `⊤`; `⟨g₁, σ₁⟩ : p ⇒ r`
arbitrary; `q'` keeps `q` where `q < α` and is the band map of `r` (a value `≥ lam`) where
`q = ⊤`.  Then `p ⇒ q'`.  (`comp_bandMap` is the instance `r = p`.) -/
theorem TransformsTo.merge_bandMap {D : Type*} [Finite D] {grade : D → ℕ}
    {p q r q' : D → ExtOrd}
    (g : ℕ → ExtOrd) (σ : ExtOrd → ExtOrd)
    (hσbot : σ ⊥ = ⊥) (hσmono : Monotone σ)
    (hσ5 : ∀ (a : ExtOrd) (k : ℕ), σ a ≤ g k → ∀ i : ℕ, i ≤ k →
      σ (extVisibilityReplace a k i) = extVisibilityReplace (σ a) k i)
    (heq : ∀ d, q d = min (σ (p d)) (g (grade d)))
    (g₁ : ℕ → ExtOrd) (σ₁ : ExtOrd → ExtOrd)
    (hg₁anti : ∀ n m : ℕ, n < m → g₁ m ≤ g₁ n)
    (hg₁self : ∀ n : ℕ, g₁ n = extVisibilityReplace (g₁ n) n n)
    (hσ₁mono : Monotone σ₁)
    (hσ₁5 : ∀ (a : ExtOrd) (k : ℕ), σ₁ a ≤ g₁ k → ∀ i : ℕ, i ≤ k →
      σ₁ (extVisibilityReplace a k i) = extVisibilityReplace (σ₁ a) k i)
    (heq₁ : ∀ d, r d = min (σ₁ (p d)) (g₁ (grade d)))
    {α lam : Ordinal.{0}} (hα : Order.IsSuccLimit α) (hlam : limitPart lam = lam) (K J : ℕ)
    (hJK : J ≤ K) (hgr : ∀ d, grade d ≤ J) (hgJ : ∀ k, k ≤ J → g k = ⊤)
    (hbound : ∀ d, q d < ofOrd α ∨ q d = ⊤)
    (hlow : ∀ d, q d < ofOrd α → q' d = q d)
    (htop : ∀ d, q d = ⊤ → ofOrd lam ≤ r d ∧ q' d = bandMap α lam K (r d)) :
    TransformsTo grade p q' := by
  classical
  have := Fintype.ofFinite D
  have hα0 : (0 : Ordinal.{0}) < α := hα.pos
  have hαlam : ∀ x : ExtOrd, x ≠ ⊥ → ofOrd α ≤ bandMap α lam K x :=
    fun x hx => le_bandMap_of_ne_bot α lam K hx
  have hlam_ne_bot : ∀ x : ExtOrd, ofOrd lam ≤ x → x ≠ ⊥ := fun x hx hb => by
    rw [hb] at hx; exact absurd hx (not_le.mpr (bot_lt_ofOrd _))
  -- every cell's `q` is `σ (p d)`
  have hq : ∀ d, q d = σ (p d) := fun d => by rw [heq d, hgJ _ (hgr d), min_top_right]
  -- the sub-`α` bounds `c₁ = μ + K' < c = μ + (K' + 1)`
  let S : Ordinal.{0} :=
    Finset.univ.sup fun d => if σ (p d) < ofOrd α then ordOrZero (σ (p d)) else 0
  have hS : S < α := by
    rw [Finset.sup_lt_iff hα0]
    intro d _
    split_ifs with hd
    · rcases ExtOrd.cases (σ (p d)) with hb | ht | ⟨ν, hν⟩
      · rw [hb, ordOrZero_bot]; exact hα0
      · rw [ht] at hd; exact absurd hd (not_lt.mpr le_top)
      · rw [hν, ordOrZero_ofOrd]; rw [hν] at hd; exact ofOrd_lt_ofOrd.mp hd
    · exact hα0
  let μ : Ordinal.{0} := limitPart S
  have hμ : limitPart μ = μ := limitPart_limitPart S
  let K' : ℕ := max K (finitePart S)
  have hKK' : K ≤ K' := le_max_left _ _
  let c₁ : Ordinal.{0} := μ + K'
  let c : Ordinal.{0} := μ + (K' + 1 : ℕ)
  have hμα : μ + Ordinal.omega0 ≤ α :=
    add_omega0_le_of_lt_isSuccLimit hα ((limitPart_le S).trans_lt hS)
  have hc₁ : c₁ < α := by
    calc μ + (K' : Ordinal.{0}) < μ + Ordinal.omega0 :=
          (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _)
      _ ≤ α := hμα
  have hc : c < α := by
    calc μ + ((K' + 1 : ℕ) : Ordinal.{0}) < μ + Ordinal.omega0 :=
          (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _)
      _ ≤ α := hμα
  have hc₁c : c₁ < c := by
    change μ + (K' : Ordinal.{0}) < μ + ((K' + 1 : ℕ) : Ordinal.{0})
    exact (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr (Nat.lt_succ_self _))
  have hc₁α : ofOrd c₁ < ofOrd α := ofOrd_lt_ofOrd.mpr hc₁
  have hcα : ofOrd c < ofOrd α := ofOrd_lt_ofOrd.mpr hc
  have hc₁c' : ofOrd c₁ < ofOrd c := ofOrd_lt_ofOrd.mpr hc₁c
  have hfpc₁ : finitePart c₁ = K' := finitePart_limitPart_add_nat' hμ K'
  have hfpc : finitePart c = K' + 1 := finitePart_limitPart_add_nat' hμ (K' + 1)
  have hc₁self : ∀ k, k ≤ K → extVisibilityReplace (ofOrd c₁) k k = ofOrd c₁ := fun k hk => by
    have hkc : k ≤ finitePart c₁ := by rw [hfpc₁]; exact hk.trans hKK'
    rw [extVisibilityReplace_ofOrd, (visibilityReplace_self_iff c₁ k).mpr hkc]
  have hcrep : ∀ k i, k ≤ K → i ≤ k → extVisibilityReplace (ofOrd c) k i = ofOrd c := by
    intro k i hk _
    have hnl : ¬ finitePart c < k := by
      rw [hfpc]; exact not_lt.mpr ((hk.trans hKK').trans (Nat.le_succ _))
    rw [extVisibilityReplace_ofOrd, visibilityReplace_of_not_lt hnl]
  have hSc₁ : S ≤ c₁ := by
    calc S = limitPart S + (finitePart S : Ordinal.{0}) := (decomposition S).symm
      _ ≤ c₁ := add_le_add (le_refl _) ((Nat.cast_le (α := Ordinal.{0})).mpr (le_max_right _ _))
  have hσc : ∀ d, σ (p d) < ofOrd α → σ (p d) ≤ ofOrd c₁ := fun d hd => by
    have hxS : ordOrZero (σ (p d)) ≤ S := by
      have := Finset.le_sup
        (f := fun d => if σ (p d) < ofOrd α then ordOrZero (σ (p d)) else 0) (Finset.mem_univ d)
      rwa [ite_eq_left hd] at this
    rcases ExtOrd.cases (σ (p d)) with hb | ht | ⟨ν, hν⟩
    · rw [hb]; exact bot_le
    · rw [ht] at hd; exact absurd hd (not_lt.mpr le_top)
    · rw [hν] at hxS ⊢
      rw [ordOrZero_ofOrd] at hxS
      rw [ofOrd_le_ofOrd]
      exact hxS.trans hSc₁
  -- region closure
  have hlowreg : ∀ (a : ExtOrd) (k i : ℕ), k ≤ J → i ≤ k → σ a < ofOrd α →
      σ (extVisibilityReplace a k i) = extVisibilityReplace (σ a) k i ∧
        σ (extVisibilityReplace a k i) < ofOrd α := by
    intro a k i hk hi ha
    have h5 := hσ5 a k (by rw [hgJ k hk]; exact le_top) i hi
    refine ⟨h5, ?_⟩
    rw [h5]
    rcases ExtOrd.cases (σ a) with hb | ht | ⟨ν, hν⟩
    · rw [hb, extVisibilityReplace_bot]; exact bot_lt_ofOrd _
    · rw [ht] at ha; exact absurd ha (not_lt.mpr le_top)
    · rw [hν] at ha ⊢
      rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
      exact visibilityReplace_lt_of_lt hα (ofOrd_lt_ofOrd.mp ha) k i
  have hhighreg : ∀ (a : ExtOrd) (k i : ℕ), k ≤ J → i ≤ k → ¬ σ a < ofOrd α →
      ¬ σ (extVisibilityReplace a k i) < ofOrd α := by
    intro a k i hk hi ha
    have h5 := hσ5 a k (by rw [hgJ k hk]; exact le_top) i hi
    rw [h5]
    rcases ExtOrd.cases (σ a) with hb | ht | ⟨ν, hν⟩
    · rw [hb] at ha; exact absurd (bot_lt_ofOrd α) ha
    · rw [ht, extVisibilityReplace_top]; exact not_lt.mpr le_top
    · rw [hν] at ha ⊢
      rw [extVisibilityReplace_ofOrd]
      intro hlt
      apply ha
      rw [ofOrd_lt_ofOrd] at hlt ⊢
      have hαν : α ≤ ν := not_lt.mp (fun h => ha (ofOrd_lt_ofOrd.mpr h))
      unfold visibilityReplace ordinalReplace at hlt
      split_ifs at hlt with h
      · exact absurd ((succLimit_le_limitPart hα hαν).trans (le_add_of_nonneg_right zero_le))
          (not_le.mpr hlt)
      · exact absurd hαν (not_le.mpr hlt)
  have hne_bot : ∀ a : ExtOrd, ¬ σ a < ofOrd α → a ≠ ⊥ := fun a ha hb => by
    rw [hb, hσbot] at ha; exact ha (bot_lt_ofOrd α)
  -- the witnesses
  let σ' : ExtOrd → ExtOrd := fun a =>
    if σ a < ofOrd α then min (σ a) (ofOrd c₁)
    else if σ₁ a < ofOrd lam then ofOrd c else bandMap α lam K (σ₁ a)
  let g' : ℕ → ExtOrd := fun k =>
    if k ≤ J then (if ofOrd lam ≤ g₁ k then bandMap α lam K (g₁ k) else ofOrd c₁) else ⊥
  have hσ'low : ∀ a, σ a < ofOrd α → σ' a = min (σ a) (ofOrd c₁) := fun a ha => by
    change (if σ a < ofOrd α then _ else _) = _
    rw [ite_eq_left ha]
  have hσ'free : ∀ a, ¬ σ a < ofOrd α → σ₁ a < ofOrd lam → σ' a = ofOrd c := fun a ha hl => by
    change (if σ a < ofOrd α then _ else if σ₁ a < ofOrd lam then _ else _) = _
    rw [ite_eq_right ha, ite_eq_left hl]
  have hσ'band : ∀ a, ¬ σ a < ofOrd α → ¬ σ₁ a < ofOrd lam →
      σ' a = bandMap α lam K (σ₁ a) := fun a ha hl => by
    change (if σ a < ofOrd α then _ else if σ₁ a < ofOrd lam then _ else _) = _
    rw [ite_eq_right ha, ite_eq_right hl]
  have hσ'high_ge : ∀ a, ¬ σ a < ofOrd α → ofOrd c ≤ σ' a := fun a ha => by
    by_cases hl : σ₁ a < ofOrd lam
    · rw [hσ'free a ha hl]
    · rw [hσ'band a ha hl]
      exact hcα.le.trans (hαlam _ (hlam_ne_bot _ (not_lt.mp hl)))
  have hσ'low_le : ∀ a, σ a < ofOrd α → σ' a ≤ ofOrd c₁ := fun a ha => by
    rw [hσ'low a ha]; exact min_le_right _ _
  have hg'high : ∀ k, k ≤ J → ofOrd lam ≤ g₁ k → g' k = bandMap α lam K (g₁ k) :=
    fun k hk hl => by
      change (if k ≤ J then (if ofOrd lam ≤ g₁ k then _ else _) else _) = _
      rw [ite_eq_left hk, ite_eq_left hl]
  have hg'low : ∀ k, k ≤ J → ¬ ofOrd lam ≤ g₁ k → g' k = ofOrd c₁ := fun k hk hl => by
    change (if k ≤ J then (if ofOrd lam ≤ g₁ k then _ else _) else _) = _
    rw [ite_eq_left hk, ite_eq_right hl]
  have hg'top : ∀ k, J < k → g' k = ⊥ := fun k hk => by
    change (if k ≤ J then _ else _) = _; rw [ite_eq_right (not_le.mpr hk)]
  have hg'ge : ∀ k, k ≤ J → ofOrd c₁ ≤ g' k := fun k hk => by
    by_cases hl : ofOrd lam ≤ g₁ k
    · rw [hg'high k hk hl]; exact hc₁α.le.trans (hαlam _ (hlam_ne_bot _ hl))
    · rw [hg'low k hk hl]
  -- a high `σ'`-value below `g' k` forces the high branch of `g'`
  have hforce : ∀ a k, k ≤ J → ¬ σ a < ofOrd α → σ' a ≤ g' k → ofOrd lam ≤ g₁ k := by
    intro a k hk ha hle
    by_contra hl
    rw [hg'low k hk hl] at hle
    exact absurd (hc₁c'.trans_le ((hσ'high_ge a ha).trans hle)) (lt_irrefl _)
  refine ⟨g', σ', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- antitone
    intro k₁ k₂ hlt
    by_cases h2 : k₂ ≤ J
    · have h1 : k₁ ≤ J := hlt.le.trans h2
      by_cases hl2 : ofOrd lam ≤ g₁ k₂
      · have hl1 : ofOrd lam ≤ g₁ k₁ := hl2.trans (hg₁anti _ _ hlt)
        rw [hg'high k₂ h2 hl2, hg'high k₁ h1 hl1]
        exact bandMap_mono_of_le hlam K hl2 (hg₁anti _ _ hlt)
      · rw [hg'low k₂ h2 hl2]; exact hg'ge k₁ h1
    · rw [hg'top k₂ (not_le.mp h2)]; exact bot_le
  · -- self-visible
    intro k
    by_cases hk : k ≤ J
    · by_cases hl : ofOrd lam ≤ g₁ k
      · rw [hg'high k hk hl]
        have h1 := bandMap_extVisibilityReplace (α := α) hα hlam (hk.trans hJK) le_rfl hl
        rw [← hg₁self k] at h1
        exact h1
      · rw [hg'low k hk hl, hc₁self k (hk.trans hJK)]
    · rw [hg'top k (not_le.mp hk), extVisibilityReplace_bot]
  · -- `σ' ⊥ = ⊥`
    rw [hσ'low ⊥ (by rw [hσbot]; exact bot_lt_ofOrd _), hσbot, min_eq_left bot_le]
  · -- monotone
    intro a b hab
    by_cases ha : σ a < ofOrd α
    · by_cases hb : σ b < ofOrd α
      · rw [hσ'low a ha, hσ'low b hb]; exact min_le_min_right _ (hσmono hab)
      · exact (hσ'low_le a ha).trans (hc₁c'.le.trans (hσ'high_ge b hb))
    · have hb : ¬ σ b < ofOrd α := fun hb => ha (lt_of_le_of_lt (hσmono hab) hb)
      by_cases hla : σ₁ a < ofOrd lam
      · rw [hσ'free a ha hla]; exact hσ'high_ge b hb
      · have hlb : ¬ σ₁ b < ofOrd lam := fun hlb => hla (lt_of_le_of_lt (hσ₁mono hab) hlb)
        rw [hσ'band a ha hla, hσ'band b hb hlb]
        exact bandMap_mono_of_le hlam K (not_lt.mp hla) (hσ₁mono hab)
  · -- clause 5
    intro a k hak i hik
    by_cases hk : k ≤ J
    · have hkK : k ≤ K := hk.trans hJK
      by_cases ha : σ a < ofOrd α
      · obtain ⟨h5, hlt⟩ := hlowreg a k i hk hik ha
        rw [hσ'low _ hlt, hσ'low a ha, h5]
        exact min_extVisibilityReplace_cap hμ hKK' hkK hik (σ a) ha.ne_top
      · have hhi := hhighreg a k i hk hik ha
        have hgk : ofOrd lam ≤ g₁ k := hforce a k hk ha hak
        by_cases hla : σ₁ a < ofOrd lam
        · -- free region: `σ₁ a < lam ≤ g₁ k`, clause 5 of `σ₁` keeps it below `lam`
            have h5 := hσ₁5 a k (hla.le.trans hgk) i hik
            have hla' : σ₁ (extVisibilityReplace a k i) < ofOrd lam := by
              rw [h5]
              rcases ExtOrd.cases (σ₁ a) with hb | ht | ⟨ν, hν⟩
              · rw [hb, extVisibilityReplace_bot]; exact bot_lt_ofOrd _
              · rw [ht] at hla; exact absurd hla (not_lt.mpr le_top)
              · rw [hν] at hla ⊢
                rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
                exact visibilityReplace_lt_of_lt_of_limitPart_eq hlam (ofOrd_lt_ofOrd.mp hla) k i
            rw [hσ'free _ hhi hla', hσ'free a ha hla, hcrep k i hkK hik]
        · -- band region
          rw [hσ'band a ha hla, hg'high k hk hgk] at hak
          have hla₀ : ofOrd lam ≤ σ₁ a := not_lt.mp hla
          rcases le_or_gt (σ₁ a) (g₁ k) with hle | hlt
          · have h5 := hσ₁5 a k hle i hik
            have hla' : ¬ σ₁ (extVisibilityReplace a k i) < ofOrd lam := by
              rw [h5]
              rcases ExtOrd.cases (σ₁ a) with hb | ht | ⟨ν, hν⟩
              · rw [hb] at hla₀; exact absurd hla₀ (not_le.mpr (bot_lt_ofOrd _))
              · rw [ht, extVisibilityReplace_top]; exact not_lt.mpr le_top
              · rw [hν] at hla₀ ⊢
                rw [extVisibilityReplace_ofOrd]
                exact not_lt.mpr (ofOrd_le_ofOrd.mpr
                  (le_visibilityReplace_of_le_of_limitPart_eq hlam (ofOrd_le_ofOrd.mp hla₀) k i))
            rw [hσ'band _ hhi hla', hσ'band a ha hla, h5]
            exact bandMap_extVisibilityReplace hα hlam hkK hik hla₀
          · -- `g₁ k < σ₁ a` with equal band-map values: both at cap level
            have heqB : bandMap α lam K (g₁ k) = bandMap α lam K (σ₁ a) :=
              le_antisymm (bandMap_mono_of_le hlam K hgk hlt.le) hak
            have hcap : ofOrd (lam + K) ≤ g₁ k := cap_of_bandMap_eq_of_lt hlam K hgk hlt heqB
            have hcapa : ofOrd (lam + K) ≤ σ₁ a := hcap.trans hlt.le
            have hcapa' : ofOrd (lam + K) ≤ σ₁ (extVisibilityReplace a k i) :=
              cap_le_of_witness hσ₁mono hσ₁5 hlam hkK hik hcap hlt
            have hla' : ¬ σ₁ (extVisibilityReplace a k i) < ofOrd lam := not_lt.mpr
              ((ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)).trans hcapa')
            rw [hσ'band _ hhi hla', hσ'band a ha hla]
            rw [bandMap_of_cap_le hcapa', bandMap_of_cap_le hcapa]
            -- `α + K` is self-visible at `k ≤ K`
            have hαlim : limitPart α = α :=
              le_antisymm (limitPart_le α) (succLimit_le_limitPart hα (le_refl α))
            have hnl : ¬ finitePart (α + K) < k := by
              rw [finitePart_limitPart_add_nat' hαlim]; exact not_lt.mpr hkK
            rw [extVisibilityReplace_ofOrd, visibilityReplace_of_not_lt hnl]
    · rw [hg'top k (not_le.mp hk)] at hak
      have hσ'a : σ' a = ⊥ := le_bot_iff.mp hak
      have ha : σ a < ofOrd α := by
        by_contra h
        have := hσ'high_ge a h
        rw [hσ'a] at this
        exact absurd this (not_le.mpr (bot_lt_ofOrd c))
      rw [hσ'low a ha] at hσ'a
      have hσab : σ a = ⊥ := by
        by_contra hne
        have h1 : ⊥ < σ a := bot_lt_iff_ne_bot.mpr hne
        have := lt_min h1 (bot_lt_ofOrd c₁)
        rw [hσ'a] at this
        exact lt_irrefl _ this
      have h5 := hσ5 a k (by rw [hσab]; exact bot_le) i hik
      rw [hσab, extVisibilityReplace_bot] at h5
      rw [hσ'low _ (by rw [h5]; exact bot_lt_ofOrd _), h5, min_eq_left bot_le,
        hσ'low a ha, hσab, min_eq_left bot_le, extVisibilityReplace_bot]
  · -- the transform equation
    intro d
    have hk := hgr d
    rcases hbound d with hd | hd
    · rw [hlow d hd, hq d]
      have hσ : σ (p d) < ofOrd α := by rwa [hq d] at hd
      rw [hσ'low _ hσ, min_eq_left (hσc d hσ)]
      exact (min_eq_left ((hσc d hσ).trans (hg'ge _ hk))).symm
    · obtain ⟨hlr, hq'⟩ := htop d hd
      rw [hq', heq₁ d]
      have hσtop : σ (p d) = ⊤ := by rw [← hq d]; exact hd
      have hσ : ¬ σ (p d) < ofOrd α := by rw [hσtop]; exact not_lt.mpr le_top
      rw [heq₁ d] at hlr
      have hl₁ : ofOrd lam ≤ σ₁ (p d) := hlr.trans (min_le_left _ _)
      have hl₂ : ofOrd lam ≤ g₁ (grade d) := hlr.trans (min_le_right _ _)
      rw [hσ'band _ hσ (not_lt.mpr hl₁), hg'high _ hk hl₂, bandMap_min hlam K hl₁ hl₂]

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

open Transform in
/-- **Locality of `p⁺` at an arbitrary top-labelled controller `Σ`** (Lemma 5.3.5 at `Σ`):
`E(Σ) ⇒ min (p⁺, p⁺(Σ))`.  Choose a full-scope maximal top witness `Θ` above `Σ`; the label
witness of `E(Σ)` handles the finite cells, the row-consistency witness `E(Σ) ⇒
min (E(Θ)↾, E(Θ)(Σ))` post-composed with the band map of `Θ` handles the `∞`-cells
(`exists_bandBridge`), and `TransformsTo.merge_bandMap` merges the two. -/
theorem topController_locality_provisional (p : S α n) (hα : Order.IsSuccLimit α)
    {Sg : Cell p.scheme.scheme} (hSg : p.label Sg = ⊤) :
    TransformsTo (fun d : p.scheme.scheme.below (p.scheme.scheme.cell Sg) =>
        p.scheme.scheme.grade d.1)
      (p.scheme.rows.E Sg)
      (fun d => min (p.someProvisionalValue d.1) (p.someProvisionalValue Sg)) := by
  obtain ⟨Θ, hSgΘ, hsc, hgr, hΘ⟩ := exists_top_witness hSg
  obtain ⟨g, σ, hganti, _hgself, hσbot, hσmono, hσ5, heq⟩ := p.respects.locality Sg
  obtain ⟨g₁, σ₁, hg₁anti, hg₁self, _hσ₁bot, hσ₁mono, hσ₁5, heq₁⟩ :=
    (p.scheme.consistent Θ).locality ⟨Sg, hSgΘ⟩
  obtain ⟨lam, hlam, hbridge⟩ := exists_bandBridge p hsc hgr hΘ
  have heq' : ∀ d : p.scheme.scheme.below (p.scheme.scheme.cell Sg),
      p.label d.1 = min (σ (p.scheme.rows.E Sg d)) (g (p.scheme.scheme.grade d.1)) := by
    intro d
    have := heq d
    change min (p.label d.1) (p.label Sg) = min (σ (p.scheme.rows.E Sg d))
      (g (p.scheme.scheme.grade d.1)) at this
    rwa [hSg, min_top_right] at this
  have hgJ : ∀ k, k ≤ p.scheme.scheme.grade Sg → g k = ⊤ := by
    intro k hk
    have hSg' := heq' ⟨Sg, GradedLe.refl _⟩
    change p.label Sg = min (σ (p.scheme.rows.E Sg ⟨Sg, GradedLe.refl _⟩))
      (g (p.scheme.scheme.grade Sg)) at hSg'
    rw [hSg] at hSg'
    have hgtop : g (p.scheme.scheme.grade Sg) = ⊤ :=
      top_le_iff.mp (hSg'.le.trans (min_le_right _ _))
    rcases hk.lt_or_eq with hlt | rfl
    · exact top_le_iff.mp (hgtop ▸ hganti _ _ hlt)
    · exact hgtop
  -- the provisional value of `Σ` itself
  obtain ⟨hlSg, hvalSg⟩ := hbridge ⟨Sg, hSgΘ⟩ hSg
  have hpSg : p.someProvisionalValue Sg =
      bandMap α lam p.topGrade (p.scheme.rows.E Θ ⟨Sg, hSgΘ⟩) :=
    (isProvisionalValue_iff.mp hvalSg).symm
  have hpSgα : ofOrd α ≤ p.someProvisionalValue Sg := by
    rw [hpSg]
    exact le_bandMap_of_ne_bot α lam p.topGrade (fun hb => by
      rw [hb] at hlSg; exact absurd hlSg (not_le.mpr (bot_lt_ofOrd _)))
  refine TransformsTo.merge_bandMap (q := fun d => p.label d.1)
    (r := fun d => min (p.scheme.rows.E Θ (CellScheme.below.incl ⟨Sg, hSgΘ⟩ d))
      (p.scheme.rows.E Θ ⟨Sg, hSgΘ⟩))
    g σ hσbot hσmono hσ5 heq' g₁ σ₁ hg₁anti hg₁self hσ₁mono hσ₁5 heq₁ hα hlam
    p.topGrade (p.scheme.scheme.grade Sg) (grade_le_topGrade_of_top hSg) ?_ hgJ ?_ ?_ ?_
  · intro d
    exact d.2.2
  · intro d
    exact p.label_bound d.1
  · intro d hd
    rw [someProvisionalValue_of_ne_top hd.ne_top]
    exact min_eq_left (hd.le.trans hpSgα)
  · intro d hd
    obtain ⟨hle, hval⟩ := hbridge (CellScheme.below.incl ⟨Sg, hSgΘ⟩ d) hd
    have hpd : p.someProvisionalValue d.1 =
        bandMap α lam p.topGrade (p.scheme.rows.E Θ (CellScheme.below.incl ⟨Sg, hSgΘ⟩ d)) :=
      (isProvisionalValue_iff.mp hval).symm
    refine ⟨le_min hle hlSg, ?_⟩
    rw [hpd, hpSg, bandMap_min hlam p.topGrade hle hlSg]

end StageType

end VaughtConjecture.Knight
