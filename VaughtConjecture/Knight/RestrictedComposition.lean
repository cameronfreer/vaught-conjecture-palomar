/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteBandReadback
public import VaughtConjecture.Knight.SuccLimitBandArithmetic
public import VaughtConjecture.Knight.NormalForm

/-! # Restricted composition: post-composition with threshold and band maps preserves `⇒`

The faithful `⇒` of Def. 2.3.9 is not generally transitive, as proved by
`SharpWitnessCompositionControls.not_transitive`. The provisional-lift route needs only
two special post-compositions, both proved
here without any general composite: the **threshold** (jump) map, which Lemma 5.3.10's `∞`
case needs, and the **band map**, which Lemma 5.3.5 needs.  In both, clause 5 is only demanded
at grades `≤ K`, where `σ`'s own clause 5 at the band mate keeps the composite honest; above
`K` the suppressor is kept below `α` (or `⊥`), where the outer map is the identity.

## The threshold map

`jump τ` is the identity at or below `τ` and `⊤`
above.  If `⟨g, σ⟩ : p ⇒ q` and every cell of grade `> K` has target `< α`, then
`p ⇒ jump (α + K) ∘ q`, with witnesses `jump ∘ σ` and a suppressor that is `jump ∘ g` up to
grade `K` and a sub-`α` self-visible bound beyond.  The clause-5 obstruction of general
transitivity does not arise: at grades `≤ K`, monotonicity and `σ`'s own clause 5 at the band
mate force `σ a ≤ τ` whenever `σ (a ⊔⁺_k i) ≤ τ`; at grades `> K` the suppressor keeps
everything below `α`, where the map is the identity. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd

namespace ExtOrd

/-- The threshold map: identity at or below `τ`, `⊤` above. -/
noncomputable def jump (τ x : ExtOrd) : ExtOrd := if x ≤ τ then x else ⊤

theorem jump_of_le {τ x : ExtOrd} (h : x ≤ τ) : jump τ x = x := by
  unfold jump; rw [ite_eq_left h]

theorem jump_of_not_le {τ x : ExtOrd} (h : ¬ x ≤ τ) : jump τ x = ⊤ := by
  unfold jump; rw [ite_eq_right h]

theorem le_jump (τ x : ExtOrd) : x ≤ jump τ x := by
  unfold jump; split_ifs <;> simp

theorem jump_mono (τ : ExtOrd) : Monotone (jump τ) := by
  intro x y hxy
  by_cases hy : y ≤ τ
  · rw [jump_of_le (hxy.trans hy), jump_of_le hy]; exact hxy
  · rw [jump_of_not_le hy]; exact le_top

theorem jump_min (τ x y : ExtOrd) : jump τ (min x y) = min (jump τ x) (jump τ y) :=
  (jump_mono τ).map_min

@[simp] theorem jump_bot (τ : ExtOrd) : jump τ ⊥ = ⊥ := jump_of_le bot_le

theorem jump_lt_iff {τ x y : ExtOrd} (hy : y ≤ τ) : jump τ x ≤ y ↔ x ≤ y := by
  constructor
  · intro h; exact (le_jump τ x).trans h
  · intro h; rw [jump_of_le (h.trans hy)]; exact h

/-- A value that stays below a self-visible bound after the jump is unchanged. -/
theorem eq_of_jump_le {τ x y : ExtOrd} (hy : y ≤ τ) (h : jump τ x ≤ y) : jump τ x = x :=
  jump_of_le ((le_jump τ x).trans (h.trans hy))

open Classical in
/-- The sub-`α` part of a value (`0` for `⊥`, `⊤`, or values `≥ α`). -/
noncomputable def ordOrZero (x : ExtOrd) : Ordinal.{0} :=
  if h : ∃ μ : Ordinal.{0}, x = ofOrd μ then h.choose else 0

theorem ordOrZero_bot : ordOrZero ⊥ = 0 := by
  unfold ordOrZero
  rw [dite_eq_right]
  rintro ⟨μ, hμ⟩
  exact ofOrd_ne_bot μ hμ.symm

theorem ordOrZero_ofOrd (μ : Ordinal.{0}) : ordOrZero (ofOrd μ) = μ := by
  unfold ordOrZero
  have h : ∃ μ' : Ordinal.{0}, ofOrd μ = ofOrd μ' := ⟨μ, rfl⟩
  rw [dite_eq_left h]
  exact (ofOrd_inj.mp h.choose_spec).symm

end ExtOrd

/-! ### Band arithmetic for the threshold -/

namespace Value

/-- Below a limit, band replacement stays below the limit. -/
theorem visibilityReplace_lt_of_lt {α μ : Ordinal.{0}} (hα : Order.IsSuccLimit α) (hμ : μ < α)
    (k i : ℕ) : visibilityReplace μ k i < α := by
  unfold visibilityReplace ordinalReplace
  split_ifs with h
  · calc limitPart μ + (i : Ordinal.{0}) < limitPart μ + Ordinal.omega0 :=
          (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 i)
      _ ≤ α := add_omega0_le_of_lt_isSuccLimit hα ((limitPart_le μ).trans_lt hμ)
  · exact hμ

theorem visibilityReplace_of_not_lt {μ : Ordinal.{0}} {k i : ℕ} (h : ¬ finitePart μ < k) :
    visibilityReplace μ k i = μ := by
  unfold visibilityReplace ordinalReplace
  rw [ite_eq_right h]

/-- Below `α + K`, band replacement at threshold `k ≤ K` with `i ≤ K` stays below `α + K`. -/
theorem visibilityReplace_le_add_of_le {α μ : Ordinal.{0}} (hα : Order.IsSuccLimit α) {K i : ℕ}
    (hμ : μ ≤ α + K) (k : ℕ) (hi : i ≤ K) : visibilityReplace μ k i ≤ α + K := by
  unfold visibilityReplace ordinalReplace
  split_ifs with h
  · have hlp : limitPart μ ≤ α := by
      rcases lt_or_ge μ α with hlt | hge
      · exact (limitPart_le μ).trans hlt.le
      · have hlt : μ < α + (K + 1 : ℕ) := by
          push_cast
          exact hμ.trans_lt ((add_lt_add_iff_left α).mpr (lt_add_one _))
        have := limitPart_eq_of_le_of_lt (μ := α) (z := μ)
          (by rw [limitPart_of_succLimit hα]; exact hge)
          (by rw [limitPart_of_succLimit hα]; exact hlt)
        rw [this, limitPart_of_succLimit hα]
    exact add_le_add hlp ((Nat.cast_le (α := Ordinal.{0})).mpr hi)
  · exact hμ

end Value

open Transform in
/-- **Threshold composition**: if `⟨g, σ⟩ : p ⇒ q` and every cell of grade `> K` has target
`< α`, then `p ⇒ jump (α + K) ∘ q`. -/
theorem TransformsTo.comp_jump {D : Type*} [Finite D] {grade : D → ℕ} {p q : D → ExtOrd}
    (h : TransformsTo grade p q) {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) (K n : ℕ)
    (hK_le_n : K ≤ n) (hn : ∀ d, grade d ≤ n) (hK : ∀ d, K < grade d → q d < ofOrd α) :
    TransformsTo grade p (fun d => jump (ofOrd (α + K)) (q d)) := by
  classical
  have := Fintype.ofFinite D
  obtain ⟨g, σ, hganti, hgself, hσbot, hσmono, hσ5, heq⟩ := h
  set τ : ExtOrd := ofOrd (α + K) with hτ
  have hα0 : (0 : Ordinal.{0}) < α := hα.pos
  have hατ : ofOrd α ≤ τ := ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)
  -- the sub-`α` bound
  let S : Ordinal.{0} :=
    (Finset.univ.sup fun d => if q d < ofOrd α then ordOrZero (q d) else 0) ⊔
      ((Finset.range (n + 1)).sup fun k => if g k < ofOrd α then ordOrZero (g k) else 0)
  have hS : S < α := by
    refine sup_lt_iff.mpr ⟨?_, ?_⟩
    · rw [Finset.sup_lt_iff hα0]
      intro d _
      split_ifs with hd
      · rcases ExtOrd.cases (q d) with hb | ht | ⟨μ, hμ⟩
        · rw [hb, ordOrZero_bot]; exact hα0
        · rw [ht] at hd; exact absurd hd (not_lt.mpr le_top)
        · rw [hμ, ordOrZero_ofOrd]; rw [hμ] at hd; exact ofOrd_lt_ofOrd.mp hd
      · exact hα0
    · rw [Finset.sup_lt_iff hα0]
      intro k _
      split_ifs with hk
      · rcases ExtOrd.cases (g k) with hb | ht | ⟨μ, hμ⟩
        · rw [hb, ordOrZero_bot]; exact hα0
        · rw [ht] at hk; exact absurd hk (not_lt.mpr le_top)
        · rw [hμ, ordOrZero_ofOrd]; rw [hμ] at hk; exact ofOrd_lt_ofOrd.mp hk
      · exact hα0
  let c : Ordinal.{0} := limitPart S + (max n (finitePart S) : ℕ)
  have hc : c < α := by
    calc limitPart S + ((max n (finitePart S) : ℕ) : Ordinal.{0})
        < limitPart S + Ordinal.omega0 := (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _)
      _ ≤ α := add_omega0_le_of_lt_isSuccLimit hα ((limitPart_le S).trans_lt hS)
  have hSc : S ≤ c := by
    calc S = limitPart S + (finitePart S : Ordinal.{0}) := (decomposition S).symm
      _ ≤ c := add_le_add (le_refl _) ((Nat.cast_le (α := Ordinal.{0})).mpr (le_max_right _ _))
  have hfpc : finitePart c = max n (finitePart S) := finitePart_limitPart_add_nat _ _
  have hcself : ∀ k, k ≤ n → visibilityReplace c k k = c := fun k hk =>
    (visibilityReplace_self_iff c k).mpr (by rw [hfpc]; exact hk.trans (le_max_left _ _))
  have hqc : ∀ d, q d < ofOrd α → q d ≤ ofOrd c := by
    intro d hd
    rcases ExtOrd.cases (q d) with hb | ht | ⟨μ, hμ⟩
    · rw [hb]; exact bot_le
    · rw [ht] at hd; exact absurd hd (not_lt.mpr le_top)
    · rw [hμ, ofOrd_le_ofOrd]
      refine le_trans ?_ hSc
      refine le_trans ?_ le_sup_left
      have := Finset.le_sup (f := fun d => if q d < ofOrd α then ordOrZero (q d) else 0)
        (Finset.mem_univ d)
      rw [ite_eq_left hd, hμ, ordOrZero_ofOrd] at this
      exact this
  have hgc : ∀ k, k ≤ n → g k < ofOrd α → g k ≤ ofOrd c := by
    intro k hk hg
    rcases ExtOrd.cases (g k) with hb | ht | ⟨μ, hμ⟩
    · rw [hb]; exact bot_le
    · rw [ht] at hg; exact absurd hg (not_lt.mpr le_top)
    · rw [hμ, ofOrd_le_ofOrd]
      refine le_trans ?_ hSc
      refine le_trans ?_ le_sup_right
      have := Finset.le_sup (f := fun k => if g k < ofOrd α then ordOrZero (g k) else 0)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
      rw [ite_eq_left hg, hμ, ordOrZero_ofOrd] at this
      exact this
  -- the witnesses: `jump ∘ g` up to `K`, the sub-`α` bound on `(K, n]`, `⊥` beyond
  let g' : ℕ → ExtOrd := fun k =>
    if k ≤ K then jump τ (g k) else if k ≤ n then (if g k < ofOrd α then g k else ofOrd c) else ⊥
  let σ' : ExtOrd → ExtOrd := fun x => jump τ (σ x)
  have hg'K : ∀ k, k ≤ K → g' k = jump τ (g k) := fun k hk => by
    change (if k ≤ K then _ else _) = _
    rw [ite_eq_left hk]
  have hg'mid : ∀ k, K < k → k ≤ n → g' k = (if g k < ofOrd α then g k else ofOrd c) :=
    fun k hk hkn => by
      change (if k ≤ K then _ else if k ≤ n then _ else _) = _
      rw [ite_eq_right (not_le.mpr hk), ite_eq_left hkn]
  have hg'top : ∀ k, n < k → g' k = ⊥ := fun k hk => by
    have hkK : ¬ k ≤ K := not_le.mpr (lt_of_le_of_lt hK_le_n hk)
    change (if k ≤ K then _ else if k ≤ n then _ else _) = _
    rw [ite_eq_right hkK, ite_eq_right (not_le.mpr hk)]
  have hg'mid_lt : ∀ k, K < k → k ≤ n → g' k < ofOrd α := by
    intro k hk hkn
    rw [hg'mid k hk hkn]
    split_ifs with h
    · exact h
    · exact ofOrd_lt_ofOrd.mpr hc
  have hg'mid_le : ∀ k, K < k → k ≤ n → g' k ≤ g k := by
    intro k hk hkn
    rw [hg'mid k hk hkn]
    split_ifs with h
    · exact le_rfl
    · exact (ofOrd_lt_ofOrd.mpr hc).le.trans (not_lt.mp h)
  -- `σ a ≤ τ` is forced by a band mate below the threshold
  have key : ∀ (a : ExtOrd) (k i : ℕ), k ≤ K → i ≤ k → τ < g k →
      σ (extVisibilityReplace a k i) ≤ τ → σ a ≤ τ := by
    intro a k i hkK hik hgk hb
    rcases ExtOrd.cases a with rfl | rfl | ⟨ν, rfl⟩
    · rw [hσbot]; exact bot_le
    · rw [extVisibilityReplace_top] at hb; exact hb
    · rw [extVisibilityReplace_ofOrd] at hb
      by_cases hfp : finitePart ν < k
      · rw [visibilityReplace_of_finitePart_lt hfp] at hb
        rcases lt_or_eq_of_le hik with hik' | hik'
        · -- clause 5 at the mate `limitPart ν + i` with index `finitePart ν`
          have h5 := hσ5 (ofOrd (limitPart ν + i)) k (hb.trans hgk.le) (finitePart ν) hfp.le
          rw [extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt
            (by rw [finitePart_limitPart_add_nat]; exact hik'), limitPart_limitPart_add_nat,
            decomposition] at h5
          rw [h5]
          -- `evr (σ (mate)) k (fp ν) ≤ τ`
          rcases ExtOrd.cases (σ (ofOrd (limitPart ν + i))) with hb' | ht' | ⟨μ, hμ⟩
          · rw [hb', extVisibilityReplace_bot]; exact bot_le
          · rw [ht'] at hb; exact absurd hb (not_le.mpr (ofOrd_lt_top _))
          · rw [hμ] at hb ⊢
            rw [extVisibilityReplace_ofOrd, hτ, ofOrd_le_ofOrd]
            exact visibilityReplace_le_add_of_le hα (ofOrd_le_ofOrd.mp hb) k (hfp.le.trans hkK)
        · -- `i = k`: the mate is above `ν`
          rw [hik'] at hb
          have hle : ofOrd ν ≤ ofOrd (limitPart ν + k) := by
            rw [ofOrd_le_ofOrd]
            calc ν = limitPart ν + (finitePart ν : Ordinal.{0}) := (decomposition ν).symm
              _ ≤ limitPart ν + k := add_le_add (le_refl _)
                ((Nat.cast_le (α := Ordinal.{0})).mpr hfp.le)
          exact (hσmono hle).trans hb
      · rw [visibilityReplace_of_not_lt hfp] at hb
        exact hb
  refine ⟨g', σ', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- antitone
    intro k₁ k₂ hlt
    have hg := hganti k₁ k₂ hlt
    by_cases h2 : k₂ ≤ K
    · rw [hg'K k₁ (hlt.le.trans h2), hg'K k₂ h2]; exact jump_mono τ hg
    by_cases h2n : k₂ ≤ n
    · rw [hg'mid k₂ (not_le.mp h2) h2n]
      by_cases h1 : k₁ ≤ K
      · rw [hg'K k₁ h1]
        split_ifs with hk₂
        · exact hg.trans (le_jump τ _)
        · exact (ofOrd_lt_ofOrd.mpr hc).le.trans ((not_lt.mp hk₂).trans (hg.trans (le_jump τ _)))
      · rw [hg'mid k₁ (not_le.mp h1) (hlt.le.trans h2n)]
        by_cases hk₁ : g k₁ < ofOrd α
        · rw [ite_eq_left hk₁]
          by_cases hk₂ : g k₂ < ofOrd α
          · rw [ite_eq_left hk₂]; exact hg
          · exact absurd (lt_of_lt_of_le hk₁ ((not_lt.mp hk₂).trans hg)) (lt_irrefl _)
        · rw [ite_eq_right hk₁]
          by_cases hk₂ : g k₂ < ofOrd α
          · rw [ite_eq_left hk₂]; exact hgc k₂ h2n hk₂
          · rw [ite_eq_right hk₂]
    · rw [hg'top k₂ (not_le.mp h2n)]; exact bot_le
  · -- self-visible
    intro k
    by_cases hk : k ≤ K
    · rw [hg'K k hk]
      by_cases hgk : g k ≤ τ
      · rw [jump_of_le hgk]; exact hgself k
      · rw [jump_of_not_le hgk, extVisibilityReplace_top]
    by_cases hkn : k ≤ n
    · rw [hg'mid k (not_le.mp hk) hkn]
      split_ifs with h
      · exact hgself k
      · rw [extVisibilityReplace_ofOrd, hcself k hkn]
    · rw [hg'top k (not_le.mp hkn), extVisibilityReplace_bot]
  · -- `σ' ⊥ = ⊥`
    simp only [σ', hσbot, jump_bot]
  · -- monotone
    intro x y hxy
    exact jump_mono τ (hσmono hxy)
  · -- clause 5
    intro a k hak i hik
    simp only [σ'] at hak ⊢
    by_cases hkK : k ≤ K
    · rw [hg'K k hkK] at hak
      by_cases hσa : σ a ≤ τ
      · -- `σ a ≤ τ`: everything stays at or below `τ`
        rw [jump_of_le hσa] at hak ⊢
        have hσag : σ a ≤ g k := by
          by_cases hgk : g k ≤ τ
          · rwa [jump_of_le hgk] at hak
          · exact hσa.trans (not_le.mp hgk).le
        rw [hσ5 a k hσag i hik]
        have hle : extVisibilityReplace (σ a) k i ≤ τ := by
          rcases ExtOrd.cases (σ a) with hb | ht | ⟨μ, hμ⟩
          · rw [hb, extVisibilityReplace_bot]; exact bot_le
          · rw [ht] at hσa; exact absurd hσa (not_le.mpr (ofOrd_lt_top _))
          · rw [hμ] at hσa ⊢
            rw [extVisibilityReplace_ofOrd, hτ, ofOrd_le_ofOrd]
            exact visibilityReplace_le_add_of_le hα (ofOrd_le_ofOrd.mp hσa) k (hik.trans hkK)
        rw [jump_of_le hle]
      · -- `σ a > τ`: the target is `⊤`, and the band mate cannot drop below `τ`
        rw [jump_of_not_le hσa] at hak ⊢
        have hgk : τ < g k := by
          by_contra hle
          rw [jump_of_le (not_lt.mp hle)] at hak
          exact hσa (le_top.trans hak |>.trans (not_lt.mp hle))
        rw [extVisibilityReplace_top]
        by_contra hne
        have hb : σ (extVisibilityReplace a k i) ≤ τ := by
          by_contra hgt
          exact hne (jump_of_not_le hgt)
        exact hσa (key a k i hkK hik hgk hb)
    · -- `k > K`: the suppressor is below `α`, where the jump is the identity
      by_cases hkn : k ≤ n
      · have hlt := hg'mid_lt k (not_le.mp hkK) hkn
        have hσ'lt : jump τ (σ a) < ofOrd α := hak.trans_lt hlt
        have hσa : σ a ≤ τ := by
          by_contra h
          rw [jump_of_not_le h] at hσ'lt
          exact absurd hσ'lt (not_lt.mpr le_top)
        rw [jump_of_le hσa] at hak hσ'lt ⊢
        have hσag : σ a ≤ g k := hak.trans (hg'mid_le k (not_le.mp hkK) hkn)
        rw [hσ5 a k hσag i hik]
        have hlt' : extVisibilityReplace (σ a) k i < ofOrd α := by
          rcases ExtOrd.cases (σ a) with hb | ht | ⟨μ, hμ⟩
          · rw [hb, extVisibilityReplace_bot]; exact bot_lt_ofOrd _
          · rw [ht] at hσ'lt; exact absurd hσ'lt (not_lt.mpr le_top)
          · rw [hμ] at hσ'lt ⊢
            rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
            exact visibilityReplace_lt_of_lt hα (ofOrd_lt_ofOrd.mp hσ'lt) k i
        rw [jump_of_le (hlt'.le.trans hατ)]
      · rw [hg'top k (not_le.mp hkn)] at hak
        have hσ'bot : jump τ (σ a) = ⊥ := le_bot_iff.mp hak
        have hσa : σ a = ⊥ := by
          by_contra h
          have := le_jump τ (σ a)
          rw [hσ'bot] at this
          exact h (le_bot_iff.mp this)
        rw [hσa, jump_bot, extVisibilityReplace_bot]
        have := hσ5 a k (by rw [hσa]; exact bot_le) i hik
        rw [hσa, extVisibilityReplace_bot] at this
        rw [this, jump_bot]
  · -- the transform equation
    intro d
    have hd := heq d
    change jump τ (q d) = min (jump τ (σ (p d))) (g' (grade d))
    by_cases hk : grade d ≤ K
    · rw [hg'K _ hk, hd, jump_min]
    · have hkn := hn d
      have hqd0 : q d < ofOrd α := hK d (not_le.mp hk)
      have hqd := hqd0
      rw [hg'mid _ (not_le.mp hk) hkn, jump_of_le (hqd0.le.trans hατ)]
      rw [hd] at hqd ⊢
      by_cases hg : g (grade d) < ofOrd α
      · rw [ite_eq_left hg]
        rcases le_total (σ (p d)) (g (grade d)) with hle | hle
        · rw [min_eq_left hle] at hqd ⊢
          rw [jump_of_le (hqd.le.trans hατ), min_eq_left hle]
        · rw [min_eq_right hle] at hqd ⊢
          rw [min_eq_right (hle.trans (le_jump τ _))]
      · rw [ite_eq_right hg]
        have hle : σ (p d) ≤ g (grade d) := by
          by_contra h'
          rw [min_eq_right (not_le.mp h').le] at hqd
          exact hg hqd
        rw [min_eq_left hle] at hqd ⊢
        have hc' : σ (p d) ≤ ofOrd c := by
          have := hqc d hqd0
          rwa [hd, min_eq_left hle] at this
        rw [jump_of_le (hqd.le.trans hατ), min_eq_left hc']

/-! ## The band map -/


namespace ExtOrd

/-- The provisional band map with active band `lam` and threshold `K`. -/
noncomputable def bandMap (α lam : Ordinal.{0}) (K : ℕ) : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ofOrd (α + K)
  | some (some ν) =>
      if lam + K ≤ ν then ofOrd (α + K) else if lam ≤ ν then ofOrd (α + finitePart ν) else ofOrd α

theorem bandMap_bot (α lam : Ordinal.{0}) (K : ℕ) : bandMap α lam K ⊥ = ⊥ := rfl

theorem bandMap_top (α lam : Ordinal.{0}) (K : ℕ) : bandMap α lam K ⊤ = ofOrd (α + K) := rfl

theorem bandMap_ofOrd_of_cap {α lam : Ordinal.{0}} {K : ℕ} {ν : Ordinal.{0}} (h : lam + K ≤ ν) :
    bandMap α lam K (ofOrd ν) = ofOrd (α + K) := by
  change (if lam + K ≤ ν then _ else _) = _
  rw [ite_eq_left h]

theorem bandMap_ofOrd_of_band {α lam : Ordinal.{0}} {K : ℕ} {ν : Ordinal.{0}} (h₁ : lam ≤ ν)
    (h₂ : ν < lam + K) : bandMap α lam K (ofOrd ν) = ofOrd (α + finitePart ν) := by
  change (if lam + K ≤ ν then _ else if lam ≤ ν then _ else _) = _
  rw [ite_eq_right (not_le.mpr h₂), ite_eq_left h₁]

theorem bandMap_ofOrd_of_lt {α lam : Ordinal.{0}} {K : ℕ} {ν : Ordinal.{0}} (h : ν < lam) :
    bandMap α lam K (ofOrd ν) = ofOrd α := by
  change (if lam + K ≤ ν then _ else if lam ≤ ν then _ else _) = _
  have h' : ¬ lam + K ≤ ν := not_le.mpr (h.trans_le (le_add_of_nonneg_right zero_le))
  rw [ite_eq_right h', ite_eq_right (not_le.mpr h)]

theorem le_bandMap_of_ne_bot (α lam : Ordinal.{0}) (K : ℕ) {x : ExtOrd} (hx : x ≠ ⊥) :
    ofOrd α ≤ bandMap α lam K x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · exact absurd rfl hx
  · rw [bandMap_top]; exact ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)
  · by_cases h1 : lam + K ≤ ν
    · rw [bandMap_ofOrd_of_cap h1]; exact ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)
    · by_cases h2 : lam ≤ ν
      · rw [bandMap_ofOrd_of_band h2 (not_le.mp h1)]
        exact ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)
      · rw [bandMap_ofOrd_of_lt (not_le.mp h2)]

theorem bandMap_le {α lam : Ordinal.{0}} (hlam : limitPart lam = lam) (K : ℕ) (x : ExtOrd) :
    bandMap α lam K x ≤ ofOrd (α + K) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · rw [bandMap_bot]; exact bot_le
  · rw [bandMap_top]
  · by_cases h1 : lam + K ≤ ν
    · rw [bandMap_ofOrd_of_cap h1]
    · by_cases h2 : lam ≤ ν
      · rw [bandMap_ofOrd_of_band h2 (not_le.mp h1), ofOrd_le_ofOrd]
        refine add_le_add (le_refl _) ((Nat.cast_le (α := Ordinal.{0})).mpr ?_)
        -- `ν = lam + fp ν < lam + K`
        have hlp : limitPart ν = lam := by
          have := limitPart_eq_of_le_of_lt (μ := lam) (z := ν) (by rwa [hlam])
            (by rw [hlam]; exact not_le.mp h1)
          rwa [hlam] at this
        have hν : ν = lam + (finitePart ν : Ordinal.{0}) := by
          rw [← hlp]; exact (decomposition ν).symm
        rw [hν] at h1
        by_contra hK
        exact h1 (add_le_add (le_refl _) ((Nat.cast_le (α := Ordinal.{0})).mpr (not_le.mp hK).le))
      · rw [bandMap_ofOrd_of_lt (not_le.mp h2), ofOrd_le_ofOrd]
        exact le_add_of_nonneg_right zero_le


/-- The band map is monotone on `[lam, ⊤]`. -/
theorem bandMap_mono_of_le {α lam : Ordinal.{0}} (hlam : limitPart lam = lam) (K : ℕ)
    {x y : ExtOrd} (hx : ofOrd lam ≤ x) (hxy : x ≤ y) :
    bandMap α lam K x ≤ bandMap α lam K y := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · exact absurd hx (not_le.mpr (bot_lt_ofOrd _))
  · rw [top_le_iff.mp hxy]
  · rcases ExtOrd.cases y with rfl | rfl | ⟨ν', rfl⟩
    · exact absurd hxy (not_le.mpr (bot_lt_ofOrd _))
    · rw [bandMap_top]; exact bandMap_le hlam K _
    · have hνν' : ν ≤ ν' := ofOrd_le_ofOrd.mp hxy
      have hlν : lam ≤ ν := ofOrd_le_ofOrd.mp hx
      by_cases h1 : lam + K ≤ ν
      · rw [bandMap_ofOrd_of_cap h1, bandMap_ofOrd_of_cap (h1.trans hνν')]
      · rw [bandMap_ofOrd_of_band hlν (not_le.mp h1)]
        by_cases h1' : lam + K ≤ ν'
        · rw [bandMap_ofOrd_of_cap h1']
          have := bandMap_le (α := α) hlam K (ofOrd ν)
          rwa [bandMap_ofOrd_of_band hlν (not_le.mp h1)] at this
        · rw [bandMap_ofOrd_of_band (hlν.trans hνν') (not_le.mp h1'), ofOrd_le_ofOrd]
          -- same limit part `lam`, so finite parts compare
          have hlp : limitPart ν = lam := by
            have := limitPart_eq_of_le_of_lt (μ := lam) (z := ν) (by rwa [hlam])
              (by rw [hlam]; exact not_le.mp h1)
            rwa [hlam] at this
          have hlp' : limitPart ν' = lam := by
            have h₁ : limitPart lam ≤ ν' := by rw [hlam]; exact hlν.trans hνν'
            have h₂ : ν' < limitPart lam + K := by rw [hlam]; exact not_le.mp h1'
            have := limitPart_eq_of_le_of_lt (μ := lam) (z := ν') h₁ h₂
            rwa [hlam] at this
          have hfp : finitePart ν ≤ finitePart ν' := finitePart_le_of_le (hlp.trans hlp'.symm) hνν'
          exact add_le_add (le_refl _) ((Nat.cast_le (α := Ordinal.{0})).mpr hfp)


end ExtOrd

/-! ### Multiples of `ω` -/

namespace Value

/-- `finitePart (μ + i) = i` for a multiple of `ω`. -/
theorem finitePart_limitPart_add_nat' {μ : Ordinal.{0}} (hμ : limitPart μ = μ) (i : ℕ) :
    finitePart (μ + i) = i := by
  have := finitePart_limitPart_add_nat μ i
  rwa [hμ] at this

/-- `limitPart (μ + i) = μ` for a multiple of `ω`. -/
theorem limitPart_add_nat_of_limitPart_eq {μ : Ordinal.{0}} (hμ : limitPart μ = μ) (i : ℕ) :
    limitPart (μ + i) = μ := by
  have := limitPart_limitPart_add_nat μ i
  rwa [hμ] at this

/-- A multiple of `ω` strictly below a limit part sits a whole `ω` below it. -/
theorem add_omega0_le_limitPart_of_lt {μ ν : Ordinal.{0}} (hμ : limitPart μ = μ)
    (h : μ < limitPart ν) : μ + Ordinal.omega0 ≤ limitPart ν := by
  rw [← hμ] at h ⊢
  unfold limitPart at h ⊢
  have hq : μ / Ordinal.omega0 < ν / Ordinal.omega0 :=
    (mul_lt_mul_iff_right₀ Ordinal.omega0_pos).mp h
  rw [← Ordinal.mul_succ]
  exact mul_le_mul_right (Order.succ_le_of_lt hq) _

/-- Band replacement below a multiple-of-`ω` bound stays below it. -/
theorem visibilityReplace_lt_of_lt_of_limitPart_eq {μ ν : Ordinal.{0}} (hμ : limitPart μ = μ)
    (hν : ν < μ) (k i : ℕ) : visibilityReplace ν k i < μ := by
  unfold visibilityReplace ordinalReplace
  split_ifs with h
  · have hlt : limitPart ν < μ := (limitPart_le ν).trans_lt hν
    have := add_omega0_le_limitPart_of_lt (μ := limitPart ν) (ν := μ) (limitPart_limitPart ν)
      (by rwa [hμ])
    rw [hμ] at this
    exact lt_of_lt_of_le ((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 i)) this
  · exact hν

/-- Band replacement with `i ≤ K` below `μ + K` (`μ` a multiple of `ω`) stays below `μ + K`. -/
theorem visibilityReplace_le_add_of_le_of_limitPart_eq {μ ν : Ordinal.{0}}
    (hμ : limitPart μ = μ) {K i : ℕ} (hν : ν ≤ μ + K) (k : ℕ) (hi : i ≤ K) :
    visibilityReplace ν k i ≤ μ + K := by
  unfold visibilityReplace ordinalReplace
  split_ifs with h
  · have hlp : limitPart ν ≤ μ := by
      have := limitPart_mono hν
      rwa [limitPart_add_nat_of_limitPart_eq hμ] at this
    exact add_le_add hlp ((Nat.cast_le (α := Ordinal.{0})).mpr hi)
  · exact hν

/-- Band replacement at threshold `k ≤ K` with `i ≤ k` of a value above `μ + K` (`μ` a
multiple of `ω`) stays at or above `μ + K`. -/
theorem le_visibilityReplace_of_lt_of_limitPart_eq {μ ν : Ordinal.{0}} (hμ : limitPart μ = μ)
    {K k i : ℕ} (hν : μ + K < ν) (hk : k ≤ K) (_hi : i ≤ k) :
    μ + K ≤ visibilityReplace ν k i := by
  unfold visibilityReplace ordinalReplace
  split_ifs with h
  · -- `limitPart ν ≠ μ`, else `ν = μ + fp ν` with `fp ν < k ≤ K`
    have hne : limitPart ν ≠ μ := by
      intro heq
      have hdec := decomposition ν
      rw [heq] at hdec
      rw [← hdec] at hν
      have : (K : Ordinal.{0}) < finitePart ν := (add_lt_add_iff_left _).mp hν
      have : K < finitePart ν := by exact_mod_cast this
      omega
    have hlt : μ < limitPart ν := by
      rcases lt_or_ge μ (limitPart ν) with h' | h'
      · exact h'
      · exfalso
        have h1 : limitPart ν ≤ μ := h'
        have h2 : μ ≤ limitPart ν := by
          have := limitPart_mono hν.le
          rwa [limitPart_add_nat_of_limitPart_eq hμ] at this
        exact hne (le_antisymm h1 h2)
    calc μ + (K : Ordinal.{0}) ≤ μ + Ordinal.omega0 :=
          add_le_add (le_refl _) (Ordinal.natCast_lt_omega0 K).le
      _ ≤ limitPart ν := add_omega0_le_limitPart_of_lt hμ hlt
      _ ≤ limitPart ν + i := le_add_of_nonneg_right zero_le
  · exact hν.le

end Value

namespace ExtOrd

/-- The band map commutes with band replacement at thresholds `≤ K` on `[lam, ⊤]`. -/
theorem bandMap_extVisibilityReplace {α lam : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    (hlam : limitPart lam = lam) {K k i : ℕ} (hk : k ≤ K) (hi : i ≤ k) {x : ExtOrd}
    (hx : ofOrd lam ≤ x) :
    bandMap α lam K (extVisibilityReplace x k i) =
      extVisibilityReplace (bandMap α lam K x) k i := by
  have hfpK : ¬ finitePart (α + K) < k := by
    rw [finitePart_succLimit_add_nat hα]; exact not_lt.mpr hk
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · exact absurd hx (not_le.mpr (bot_lt_ofOrd _))
  · rw [extVisibilityReplace_top, bandMap_top, extVisibilityReplace_ofOrd,
      visibilityReplace_of_not_lt hfpK]
  · have hlν : lam ≤ ν := ofOrd_le_ofOrd.mp hx
    rw [extVisibilityReplace_ofOrd]
    by_cases hcap : lam + K ≤ ν
    · rw [bandMap_ofOrd_of_cap hcap, extVisibilityReplace_ofOrd, visibilityReplace_of_not_lt hfpK]
      rcases hcap.lt_or_eq with hlt | heq
      · exact bandMap_ofOrd_of_cap (le_visibilityReplace_of_lt_of_limitPart_eq hlam hlt hk hi)
      · -- `ν = lam + K`: finite part `K ≥ k`, no replacement
        have hnl : ¬ finitePart (lam + K) < k := by
          rw [finitePart_limitPart_add_nat' hlam]; exact not_lt.mpr hk
        rw [← heq, visibilityReplace_of_not_lt hnl]
        exact bandMap_ofOrd_of_cap le_rfl
    · have hband := not_le.mp hcap
      rw [bandMap_ofOrd_of_band hlν hband, extVisibilityReplace_ofOrd]
      have hlp : limitPart ν = lam := by
        have := limitPart_eq_of_le_of_lt (μ := lam) (z := ν) (by rwa [hlam]) (by rwa [hlam])
        rwa [hlam] at this
      have hfpν : finitePart ν < K := by
        have hdec := decomposition ν
        rw [hlp] at hdec
        rw [← hdec] at hband
        exact_mod_cast (add_lt_add_iff_left _).mp hband
      by_cases hfp : finitePart ν < k
      · rw [visibilityReplace_of_finitePart_lt hfp, hlp,
          visibilityReplace_of_finitePart_lt (by rw [finitePart_succLimit_add_nat hα]; exact hfp),
          limitPart_succLimit_add_nat hα]
        rcases lt_or_eq_of_le (hi.trans hk) with hiK | hiK
        · rw [bandMap_ofOrd_of_band (le_add_of_nonneg_right zero_le)
            ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hiK)), finitePart_limitPart_add_nat' hlam]
        · rw [hiK, bandMap_ofOrd_of_cap le_rfl]
      · rw [visibilityReplace_of_not_lt hfp, visibilityReplace_of_not_lt
          (by rw [finitePart_succLimit_add_nat hα]; exact hfp)]
        exact bandMap_ofOrd_of_band hlν hband

end ExtOrd


/-! ### The gate: post-composition with the band map -/

open Value ExtOrd in
/-- Under a multiple-of-`ω` bound `c = μ + K'` with `K ≤ K'`, band replacement at thresholds
`≤ K` commutes with capping at `c`. -/
theorem min_extVisibilityReplace_cap {μ : Ordinal.{0}} (hμ : limitPart μ = μ) {K K' k i : ℕ}
    (hKK' : K ≤ K') (hk : k ≤ K) (hi : i ≤ k) (x : ExtOrd) (hx : x ≠ ⊤) :
    min (extVisibilityReplace x k i) (ofOrd (μ + K')) =
      extVisibilityReplace (min x (ofOrd (μ + K'))) k i := by
  have hfp : ¬ finitePart (μ + K') < k := by
    rw [finitePart_limitPart_add_nat' hμ]; exact not_lt.mpr (hk.trans hKK')
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · simp only [extVisibilityReplace_bot, min_eq_left bot_le]
  · exact absurd rfl hx
  · rw [extVisibilityReplace_ofOrd]
    rcases le_or_gt ν (μ + K') with hle | hlt
    · have h1 : visibilityReplace ν k i ≤ μ + K' :=
        visibilityReplace_le_add_of_le_of_limitPart_eq hμ hle k ((hi.trans hk).trans hKK')
      rw [min_eq_left (ofOrd_le_ofOrd.mpr h1), min_eq_left (ofOrd_le_ofOrd.mpr hle),
        extVisibilityReplace_ofOrd]
    · have h1 : μ + K' ≤ visibilityReplace ν k i :=
        le_visibilityReplace_of_lt_of_limitPart_eq hμ hlt (hk.trans hKK') hi
      rw [min_eq_right (ofOrd_le_ofOrd.mpr h1), min_eq_right (ofOrd_le_ofOrd.mpr hlt.le),
        extVisibilityReplace_ofOrd, visibilityReplace_of_not_lt hfp]

open Value ExtOrd Transform in
/-- **Band-map composition**: if `⟨g, σ⟩ : p ⇒ q` on a finite cell family with all grades
`≤ K` and `g = ⊤` up to `K`, and `q'` keeps every value of `q` below `α` while replacing every
`⊤` value by the band map of its row (a row `≥ lam`), then `p ⇒ q'`. -/
theorem TransformsTo.comp_bandMap {D : Type*} [Finite D] {grade : D → ℕ} {p q q' : D → ExtOrd}
    (g : ℕ → ExtOrd) (σ : ExtOrd → ExtOrd)
    (hganti : ∀ n m : ℕ, n < m → g m ≤ g n)
    (hgself : ∀ n : ℕ, g n = extVisibilityReplace (g n) n n)
    (hσbot : σ ⊥ = ⊥) (hσmono : Monotone σ)
    (hσ5 : ∀ (a : ExtOrd) (k : ℕ), σ a ≤ g k → ∀ i : ℕ, i ≤ k →
      σ (extVisibilityReplace a k i) = extVisibilityReplace (σ a) k i)
    (heq : ∀ d, q d = min (σ (p d)) (g (grade d)))
    {α lam : Ordinal.{0}} (hα : Order.IsSuccLimit α) (hlam : limitPart lam = lam) (K : ℕ)
    (hgr : ∀ d, grade d ≤ K) (hgK : ∀ k, k ≤ K → g k = ⊤)
    (hbound : ∀ d, q d < ofOrd α ∨ q d = ⊤)
    (hlow : ∀ d, q d < ofOrd α → q' d = q d)
    (htop : ∀ d, q d = ⊤ → ofOrd lam ≤ p d ∧ q' d = bandMap α lam K (p d)) :
    TransformsTo grade p q' := by
  classical
  have := Fintype.ofFinite D
  have hα0 : (0 : Ordinal.{0}) < α := hα.pos
  have hαlam : ∀ x : ExtOrd, x ≠ ⊥ → ofOrd α ≤ bandMap α lam K x :=
    fun x hx => le_bandMap_of_ne_bot α lam K hx
  -- the sub-`α` bound `c = μ + K'`
  let S : Ordinal.{0} :=
    (Finset.univ.sup fun d => if q d < ofOrd α then ordOrZero (q d) else 0) ⊔
      (Finset.univ.sup fun d => if σ (p d) < ofOrd α then ordOrZero (σ (p d)) else 0)
  have hS : S < α := by
    refine sup_lt_iff.mpr ⟨?_, ?_⟩
    · rw [Finset.sup_lt_iff hα0]
      intro d _
      split_ifs with hd
      · rcases ExtOrd.cases (q d) with hb | ht | ⟨ν, hν⟩
        · rw [hb, ordOrZero_bot]; exact hα0
        · rw [ht] at hd; exact absurd hd (not_lt.mpr le_top)
        · rw [hν, ordOrZero_ofOrd]; rw [hν] at hd; exact ofOrd_lt_ofOrd.mp hd
      · exact hα0
    · rw [Finset.sup_lt_iff hα0]
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
  let c : Ordinal.{0} := μ + K'
  have hc : c < α := by
    calc μ + (K' : Ordinal.{0}) < μ + Ordinal.omega0 :=
          (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _)
      _ ≤ α := add_omega0_le_of_lt_isSuccLimit hα ((limitPart_le S).trans_lt hS)
  have hcα : ofOrd c < ofOrd α := ofOrd_lt_ofOrd.mpr hc
  have hfpc : finitePart c = K' := finitePart_limitPart_add_nat' hμ K'
  have hcself : ∀ k, k ≤ K → extVisibilityReplace (ofOrd c) k k = ofOrd c := fun k hk => by
    have hkc : k ≤ finitePart c := by rw [hfpc]; exact hk.trans hKK'
    rw [extVisibilityReplace_ofOrd, (visibilityReplace_self_iff c k).mpr hkc]
  have hcrep : ∀ k i, k ≤ K → i ≤ k → extVisibilityReplace (ofOrd c) k i = ofOrd c := by
    intro k i hk _
    have hnl : ¬ finitePart c < k := by rw [hfpc]; exact not_lt.mpr (hk.trans hKK')
    rw [extVisibilityReplace_ofOrd, visibilityReplace_of_not_lt hnl]
  have hSc : S ≤ c := by
    calc S = limitPart S + (finitePart S : Ordinal.{0}) := (decomposition S).symm
      _ ≤ c := add_le_add (le_refl _) ((Nat.cast_le (α := Ordinal.{0})).mpr (le_max_right _ _))
  have hval : ∀ x : ExtOrd, x < ofOrd α → ordOrZero x ≤ S → x ≤ ofOrd c := by
    intro x hx hxS
    rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
    · exact bot_le
    · exact absurd hx (not_lt.mpr le_top)
    · rw [ordOrZero_ofOrd] at hxS
      rw [ofOrd_le_ofOrd]
      exact hxS.trans hSc
  have hqc : ∀ d, q d < ofOrd α → q d ≤ ofOrd c := fun d hd => by
    refine hval _ hd (le_trans ?_ le_sup_left)
    have := Finset.le_sup (f := fun d => if q d < ofOrd α then ordOrZero (q d) else 0)
      (Finset.mem_univ d)
    rwa [ite_eq_left hd] at this
  have hσc : ∀ d, σ (p d) < ofOrd α → σ (p d) ≤ ofOrd c := fun d hd => by
    refine hval _ hd (le_trans ?_ le_sup_right)
    have := Finset.le_sup (f := fun d => if σ (p d) < ofOrd α then ordOrZero (σ (p d)) else 0)
      (Finset.mem_univ d)
    rwa [ite_eq_left hd] at this
  -- region closure
  have hlowreg : ∀ (a : ExtOrd) (k i : ℕ), k ≤ K → i ≤ k → σ a < ofOrd α →
      σ (extVisibilityReplace a k i) = extVisibilityReplace (σ a) k i ∧
        σ (extVisibilityReplace a k i) < ofOrd α := by
    intro a k i hk hi ha
    have h5 := hσ5 a k (by rw [hgK k hk]; exact le_top) i hi
    refine ⟨h5, ?_⟩
    rw [h5]
    rcases ExtOrd.cases (σ a) with hb | ht | ⟨ν, hν⟩
    · rw [hb, extVisibilityReplace_bot]; exact bot_lt_ofOrd _
    · rw [ht] at ha; exact absurd ha (not_lt.mpr le_top)
    · rw [hν] at ha ⊢
      rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
      exact visibilityReplace_lt_of_lt hα (ofOrd_lt_ofOrd.mp ha) k i
  have hhighreg : ∀ (a : ExtOrd) (k i : ℕ), k ≤ K → i ≤ k → ¬ σ a < ofOrd α →
      ¬ σ (extVisibilityReplace a k i) < ofOrd α := by
    intro a k i hk hi ha
    have h5 := hσ5 a k (by rw [hgK k hk]; exact le_top) i hi
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
    if σ a < ofOrd α then min (σ a) (ofOrd c)
    else if a < ofOrd lam then ofOrd c else bandMap α lam K a
  let g' : ℕ → ExtOrd := fun k => if k ≤ K then g k else ⊥
  have hσ'low : ∀ a, σ a < ofOrd α → σ' a = min (σ a) (ofOrd c) := fun a ha => by
    change (if σ a < ofOrd α then _ else _) = _
    rw [ite_eq_left ha]
  have hσ'free : ∀ a, ¬ σ a < ofOrd α → a < ofOrd lam → σ' a = ofOrd c := fun a ha hl => by
    change (if σ a < ofOrd α then _ else if a < ofOrd lam then _ else _) = _
    rw [ite_eq_right ha, ite_eq_left hl]
  have hσ'band : ∀ a, ¬ σ a < ofOrd α → ¬ a < ofOrd lam → σ' a = bandMap α lam K a :=
    fun a ha hl => by
      change (if σ a < ofOrd α then _ else if a < ofOrd lam then _ else _) = _
      rw [ite_eq_right ha, ite_eq_right hl]
  have hσ'high_ge : ∀ a, ¬ σ a < ofOrd α → ofOrd c ≤ σ' a := fun a ha => by
    by_cases hl : a < ofOrd lam
    · rw [hσ'free a ha hl]
    · rw [hσ'band a ha hl]; exact hcα.le.trans (hαlam a (hne_bot a ha))
  have hσ'low_le : ∀ a, σ a < ofOrd α → σ' a ≤ ofOrd c := fun a ha => by
    rw [hσ'low a ha]; exact min_le_right _ _
  have hg'K : ∀ k, k ≤ K → g' k = g k := fun k hk => by
    change (if k ≤ K then _ else _) = _; rw [ite_eq_left hk]
  have hg'top : ∀ k, K < k → g' k = ⊥ := fun k hk => by
    change (if k ≤ K then _ else _) = _; rw [ite_eq_right (not_le.mpr hk)]
  refine ⟨g', σ', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- antitone
    intro k₁ k₂ hlt
    by_cases h2 : k₂ ≤ K
    · rw [hg'K k₁ (hlt.le.trans h2), hg'K k₂ h2]; exact hganti k₁ k₂ hlt
    · rw [hg'top k₂ (not_le.mp h2)]; exact bot_le
  · -- self-visible
    intro k
    by_cases hk : k ≤ K
    · rw [hg'K k hk]; exact hgself k
    · rw [hg'top k (not_le.mp hk), extVisibilityReplace_bot]
  · -- `σ' ⊥ = ⊥`
    rw [hσ'low ⊥ (by rw [hσbot]; exact bot_lt_ofOrd _), hσbot, min_eq_left bot_le]
  · -- monotone
    intro a b hab
    by_cases ha : σ a < ofOrd α
    · by_cases hb : σ b < ofOrd α
      · rw [hσ'low a ha, hσ'low b hb]; exact min_le_min_right _ (hσmono hab)
      · exact (hσ'low_le a ha).trans (hσ'high_ge b hb)
    · have hb : ¬ σ b < ofOrd α := fun hb => ha (lt_of_le_of_lt (hσmono hab) hb)
      by_cases hla : a < ofOrd lam
      · rw [hσ'free a ha hla]; exact hσ'high_ge b hb
      · have hlb : ¬ b < ofOrd lam := fun hlb => hla (lt_of_le_of_lt hab hlb)
        rw [hσ'band a ha hla, hσ'band b hb hlb]
        exact bandMap_mono_of_le hlam K (not_lt.mp hla) hab
  · -- clause 5
    intro a k hak i hik
    by_cases hk : k ≤ K
    · rw [hg'K k hk] at hak
      by_cases ha : σ a < ofOrd α
      · obtain ⟨h5, hlt⟩ := hlowreg a k i hk hik ha
        rw [hσ'low _ hlt, hσ'low a ha, h5]
        exact min_extVisibilityReplace_cap hμ hKK' hk hik (σ a) ha.ne_top
      · have hhi := hhighreg a k i hk hik ha
        by_cases hla : a < ofOrd lam
        · have hla' : extVisibilityReplace a k i < ofOrd lam := by
            rcases ExtOrd.cases a with rfl | rfl | ⟨ν, rfl⟩
            · exact absurd rfl (hne_bot _ ha)
            · exact absurd hla (not_lt.mpr le_top)
            · rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
              exact visibilityReplace_lt_of_lt_of_limitPart_eq hlam (ofOrd_lt_ofOrd.mp hla) k i
          rw [hσ'free _ hhi hla', hσ'free a ha hla, hcrep k i hk hik]
        · have hla' : ¬ extVisibilityReplace a k i < ofOrd lam := by
            rcases ExtOrd.cases a with rfl | rfl | ⟨ν, rfl⟩
            · exact absurd rfl (hne_bot _ ha)
            · rw [extVisibilityReplace_top]; exact not_lt.mpr le_top
            · rw [extVisibilityReplace_ofOrd]
              intro hlt
              apply hla
              rw [ofOrd_lt_ofOrd] at hlt ⊢
              have hlν : lam ≤ ν := not_lt.mp (fun h => hla (ofOrd_lt_ofOrd.mpr h))
              unfold visibilityReplace ordinalReplace at hlt
              split_ifs at hlt with h
              · have : lam ≤ limitPart ν := by
                  have := limitPart_mono hlν; rwa [hlam] at this
                exact absurd (this.trans (le_add_of_nonneg_right zero_le)) (not_le.mpr hlt)
              · exact absurd hlν (not_le.mpr hlt)
          rw [hσ'band _ hhi hla', hσ'band a ha hla]
          exact bandMap_extVisibilityReplace hα hlam hk hik (not_lt.mp hla)
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
        have := lt_min h1 (bot_lt_ofOrd c)
        rw [hσ'a] at this
        exact lt_irrefl _ this
      have h5 := hσ5 a k (by rw [hσab]; exact bot_le) i hik
      rw [hσab, extVisibilityReplace_bot] at h5
      rw [hσ'low _ (by rw [h5]; exact bot_lt_ofOrd _), h5, min_eq_left bot_le,
        hσ'low a ha, hσab, min_eq_left bot_le, extVisibilityReplace_bot]
  · -- the transform equation
    intro d
    have hk := hgr d
    rw [hg'K _ hk]
    rcases hbound d with hd | hd
    · rw [hlow d hd, heq d]
      by_cases hσ : σ (p d) < ofOrd α
      · rw [hσ'low _ hσ, min_eq_left (hσc d hσ)]
      · have hq : min (σ (p d)) (g (grade d)) = g (grade d) := by
          rcases le_total (σ (p d)) (g (grade d)) with hle | hle
          · rw [heq d, min_eq_left hle] at hd
            exact absurd hd hσ
          · exact min_eq_right hle
        have hgc : g (grade d) ≤ ofOrd c := by
          have := hqc d hd
          rwa [heq d, hq] at this
        rw [hq, min_eq_right (hgc.trans (hσ'high_ge _ hσ))]
    · obtain ⟨hlp, hq'⟩ := htop d hd
      rw [hq']
      have hσtop : σ (p d) = ⊤ := by
        have := heq d
        rw [hd] at this
        exact top_le_iff.mp (this.le.trans (min_le_left _ _))
      have hgtop : g (grade d) = ⊤ := by
        have := heq d
        rw [hd] at this
        exact top_le_iff.mp (this.le.trans (min_le_right _ _))
      have hσ : ¬ σ (p d) < ofOrd α := by rw [hσtop]; exact not_lt.mpr le_top
      rw [hσ'band _ hσ (not_lt.mpr hlp), hgtop, min_top_right]

end VaughtConjecture.Knight
