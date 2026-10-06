/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RestrictedComposition
public import VaughtConjecture.Knight.ProvisionalUniqueness
public import VaughtConjecture.Knight.FiniteRowReadback

/-! # The provisional value is the band map of the row at a top witness

For a full-scope `∞`-cell `Θ` of grade `K = K^p` and an `∞`-cell `d` below it, the provisional
value `p⁺(d)` (Def. 5.3.1, functional by Lemma 5.3.2) is the band map of the row `E(Θ)(d)`:
`α + fp` on the active band `[lam, lam + K)` and `α + K` at cap level, where `lam` is the
common limit part of the non-cap `∞`-rows below `Θ` (band comparability + clause 2.(a)).
This is the bridge that turns `TransformsTo.comp_bandMap` into Lemma 5.3.5's top-row
transform `E(Θ) ⇒ p⁺` (`topRow_transformsTo_provisional`).

## Cap transport (an argument the paper omits)

Def. 5.3.1's cap clause is existential in the top witness, but Lemma 5.3.5 reads `p⁺` through
one fixed maximal witness `Θ`.  `ProvisionalCap.transport` shows a cell capped at some witness
`Θ'` is capped at every witness `Θ`: the locality of `E(Θ)` at `Θ'` carries the cap across
(clause 5 when the cap witness is below the row's value at `Θ'`, monotonicity otherwise).
Without it the band-map reading of `p⁺` at `Θ` is not justified. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

/-! ### Band comparability -/

namespace Value

/-- Two ordinals with finite parts `< K` are band-comparable: same limit part, or one lies at
or above the other's cap `limitPart + K`. -/
theorem band_trichotomy (x y : Ordinal.{0}) (K : ℕ) :
    limitPart x = limitPart y ∨ limitPart x + K ≤ y ∨ limitPart y + K ≤ x := by
  rcases lt_trichotomy (limitPart x) (limitPart y) with h | h | h
  · right; left
    calc limitPart x + (K : Ordinal.{0}) ≤ limitPart x + Ordinal.omega0 :=
          add_le_add (le_refl _) (Ordinal.natCast_lt_omega0 K).le
      _ ≤ limitPart y := add_omega0_le_limitPart_of_lt (limitPart_limitPart x) h
      _ ≤ y := limitPart_le y
  · exact Or.inl h
  · right; right
    calc limitPart y + (K : Ordinal.{0}) ≤ limitPart y + Ordinal.omega0 :=
          add_le_add (le_refl _) (Ordinal.natCast_lt_omega0 K).le
      _ ≤ limitPart x := add_omega0_le_limitPart_of_lt (limitPart_limitPart y) h
      _ ≤ x := limitPart_le x

end Value

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-- The rows of `∞`-cells below a top witness are not `⊥`. -/
theorem row_ne_bot' (p : S α n) {Θ : Cell p.scheme.scheme} (hΘ : p.label Θ = ⊤)
    (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (hd : p.label d.1 = ⊤) :
    p.scheme.rows.E Θ d ≠ ⊥ := row_ne_bot_of_label_top p hΘ d hd

/-- **Non-cap `∞`-rows below a top witness share one limit part.**  If `d, d'` are `∞`-cells
below the top witness `Θ` with neither capped, their rows are ordinals with finite part
`< K^p` and equal limit parts. -/
theorem limitPart_eq_of_not_cap {p : S α n} {Θ : Cell p.scheme.scheme}
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘ : p.label Θ = ⊤) {d d' : p.scheme.scheme.below (p.scheme.scheme.cell Θ)}
    (hd : p.label d.1 = ⊤) (hd' : p.label d'.1 = ⊤)
    (hcap : ¬ p.ProvisionalCap d.1) (hcap' : ¬ p.ProvisionalCap d'.1)
    {ν ν' : Ordinal.{0}} (hν : p.scheme.rows.E Θ d = ofOrd ν)
    (hν' : p.scheme.rows.E Θ d' = ofOrd ν') :
    finitePart ν < p.topGrade ∧ finitePart ν' < p.topGrade ∧ limitPart ν = limitPart ν' := by
  -- finite parts below `K`: otherwise the cell caps itself
  have hfp : ∀ (e : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (μ : Ordinal.{0}),
      p.label e.1 = ⊤ → ¬ p.ProvisionalCap e.1 → p.scheme.rows.E Θ e = ofOrd μ →
      finitePart μ < p.topGrade := by
    intro e μ he hce hμ
    by_contra hge
    apply hce
    refine ⟨Θ, e.2, e, hsc, hgr, hΘ, he, ?_⟩
    change extVisibilityReplace (p.scheme.rows.E Θ e) p.topGrade p.topGrade ≤ p.scheme.rows.E Θ e
    rw [hμ, extVisibilityReplace_ofOrd, (visibilityReplace_self_iff μ _).mpr (not_lt.mp hge)]
  have h1 := hfp d ν hd hcap hν
  have h2 := hfp d' ν' hd' hcap' hν'
  refine ⟨h1, h2, ?_⟩
  rcases band_trichotomy ν ν' p.topGrade with h | h | h
  · exact h
  · -- `d'` is capped by `d`
    exfalso
    apply hcap'
    refine ⟨Θ, d'.2, d, hsc, hgr, hΘ, hd, ?_⟩
    change extVisibilityReplace (p.scheme.rows.E Θ d) p.topGrade p.topGrade ≤ p.scheme.rows.E Θ d'
    rw [hν, hν', extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt h1,
      ofOrd_le_ofOrd]
    exact h
  · exfalso
    apply hcap
    refine ⟨Θ, d.2, d', hsc, hgr, hΘ, hd', ?_⟩
    change extVisibilityReplace (p.scheme.rows.E Θ d') p.topGrade p.topGrade ≤ p.scheme.rows.E Θ d
    rw [hν, hν', extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt h2,
      ofOrd_le_ofOrd]
    exact h


/-- **Cap transport** (the cap half of Lemma 5.3.2): a cell capped at some top witness is
capped at every top witness.  Proof: read the locality of `E(Θ)` at `Θ'`; if `d` were not
capped at `Θ`, its row `a` would lie strictly below `E(Θ)(Θ')`, hence `a = σ' (E(Θ')(d))`
with clause 5 available, and the cap inequality at `Θ'` transports to `Θ` through `σ'`. -/
theorem ProvisionalCap.transport {p : S α n} {d : Cell p.scheme.scheme} (hcap : p.ProvisionalCap d)
    {Θ : Cell p.scheme.scheme} (hdΘ : GradedLe (p.scheme.scheme.cell d) (p.scheme.scheme.cell Θ))
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (_hΘ : p.label Θ = ⊤) :
    ∃ Sg : p.scheme.scheme.below (p.scheme.scheme.cell Θ), p.label Sg.1 = ⊤ ∧
      extVisibilityReplace (p.scheme.rows.E Θ Sg) p.topGrade p.topGrade ≤
        p.scheme.rows.E Θ ⟨d, hdΘ⟩ := by
  obtain ⟨Θ', hdΘ', Sg', hsc', hgr', hΘ', hSg', hle⟩ := hcap
  set K := p.topGrade with hK
  -- the two witnesses lie below each other
  have hΘ'Θ : GradedLe (p.scheme.scheme.cell Θ') (p.scheme.scheme.cell Θ) := by
    refine ⟨?_, ?_⟩
    · change p.scheme.scheme.scope Θ' ⊆ p.scheme.scheme.scope Θ
      rw [hsc]; exact Finset.subset_univ _
    · change p.scheme.scheme.grade Θ' ≤ p.scheme.scheme.grade Θ
      rw [hgr, hgr']
  have hSgΘ : GradedLe (p.scheme.scheme.cell Sg'.1) (p.scheme.scheme.cell Θ) := Sg'.2.trans hΘ'Θ
  by_contra hnc
  push Not at hnc
  set a := p.scheme.rows.E Θ ⟨d, hdΘ⟩ with ha
  set Y := p.scheme.rows.E Θ ⟨Θ', hΘ'Θ⟩ with hY
  set s := p.scheme.rows.E Θ ⟨Sg'.1, hSgΘ⟩ with hs
  set b := p.scheme.rows.E Θ' ⟨d, hdΘ'⟩ with hb
  set t := p.scheme.rows.E Θ' Sg' with ht
  -- `Y` is self-visible at `K`, and `a < Y`
  have hYself : extVisibilityReplace Y K K = Y := by
    have := p.scheme.rows.orderly Θ ⟨Θ', hΘ'Θ⟩
    change Y = extVisibilityReplace Y (p.scheme.scheme.grade Θ') (p.scheme.scheme.grade Θ') at this
    rw [hgr'] at this
    exact this.symm
  have haY : a < Y := by
    have := hnc ⟨Θ', hΘ'Θ⟩ hΘ'
    rw [hYself] at this
    exact this
  have hsa : ¬ extVisibilityReplace s K K ≤ a := not_le.mpr (hnc ⟨Sg'.1, hSgΘ⟩ hSg')
  -- locality of `E(Θ)` at `Θ'`
  obtain ⟨g', σ', hganti, -, -, hσmono, hσ5, hloc⟩ :=
    (p.scheme.consistent Θ).locality ⟨Θ', hΘ'Θ⟩
  have hlocΘ' := hloc ⟨Θ', GradedLe.refl _⟩
  have hlocd := hloc ⟨d, hdΘ'⟩
  have hlocS := hloc Sg'
  change min Y Y =
    min (σ' (p.scheme.rows.E Θ' ⟨Θ', GradedLe.refl _⟩)) (g' (p.scheme.scheme.grade Θ')) at hlocΘ'
  change min (p.scheme.rows.E Θ ⟨d, _⟩) Y = min (σ' b) (g' (p.scheme.scheme.grade d)) at hlocd
  change min (p.scheme.rows.E Θ ⟨Sg'.1, _⟩) Y = min (σ' t) (g' (p.scheme.scheme.grade Sg'.1))
    at hlocS
  have hYg : Y ≤ g' K := by
    rw [min_self, hgr'] at hlocΘ'
    rw [hlocΘ']
    exact min_le_right _ _
  have hgd : g' K ≤ g' (p.scheme.scheme.grade d) := by
    have h2 : p.scheme.scheme.grade d ≤ p.scheme.scheme.grade Θ' := hdΘ'.2
    rw [hgr'] at h2
    rcases h2.lt_or_eq with hlt | heq
    · exact hganti _ _ hlt
    · rw [heq]
  have hgS : g' K ≤ g' (p.scheme.scheme.grade Sg'.1) := by
    have h2 : p.scheme.scheme.grade Sg'.1 ≤ p.scheme.scheme.grade Θ' := Sg'.2.2
    rw [hgr'] at h2
    rcases h2.lt_or_eq with hlt | heq
    · exact hganti _ _ hlt
    · rw [heq]
  -- `a = σ' b`, with `σ' b ≤ g' K`
  have hlocd' : a = min (σ' b) (g' (p.scheme.scheme.grade d)) := by
    rw [← hlocd, min_eq_left haY.le]
  have haσ : a = σ' b := by
    rcases le_total (σ' b) (g' (p.scheme.scheme.grade d)) with hle' | hle'
    · rw [min_eq_left hle'] at hlocd'; exact hlocd'
    · rw [min_eq_right hle'] at hlocd'
      exact absurd (lt_of_lt_of_le haY (hYg.trans hgd)) (not_lt.mpr hlocd'.ge)
  -- the cap inequality at `Θ'` transports through `σ'`
  have htb : σ' (extVisibilityReplace t K K) ≤ a := by
    rw [haσ]; exact hσmono hle
  rcases lt_or_ge s Y with hsY | hsY
  · -- `s = σ' t` with clause 5 available
    have hlocS' : s = min (σ' t) (g' (p.scheme.scheme.grade Sg'.1)) := by
      rw [← hlocS, min_eq_left hsY.le]
    have hsσ : s = σ' t := by
      rcases le_total (σ' t) (g' (p.scheme.scheme.grade Sg'.1)) with hle' | hle'
      · rw [min_eq_left hle'] at hlocS'; exact hlocS'
      · rw [min_eq_right hle'] at hlocS'
        exact absurd (lt_of_lt_of_le hsY (hYg.trans hgS)) (not_lt.mpr hlocS'.ge)
    have hσtK : σ' t ≤ g' K := hsσ ▸ (hsY.le.trans hYg)
    have h5 := hσ5 t K hσtK K le_rfl
    rw [h5, ← hsσ] at htb
    exact hsa htb
  · -- `Y ≤ σ' t`, so `a ≥ Y`
    have hYσ : Y ≤ σ' t := by
      rw [min_eq_right hsY] at hlocS
      exact hlocS.le.trans (min_le_left _ _)
    have : Y ≤ a := hYσ.trans ((hσmono (le_extVisibilityReplace_self t K)).trans htb)
    exact absurd haY (not_lt.mpr this)

/-- Capped **at `Θ`**: some `∞`-cell below `Θ` caps `d` in the row of `Θ`. -/
def CapAt (p : S α n) (Θ : Cell p.scheme.scheme) (d : p.scheme.scheme.below
  (p.scheme.scheme.cell Θ)) :
    Prop :=
  ∃ Sg : p.scheme.scheme.below (p.scheme.scheme.cell Θ), p.label Sg.1 = ⊤ ∧
    extVisibilityReplace (p.scheme.rows.E Θ Sg) p.topGrade p.topGrade ≤ p.scheme.rows.E Θ d

/-- **A capped row is at cap level**: with a non-cap `∞`-cell `d₀` of row `lam + j` (`j < K`)
below `Θ`, every cell capped at `Θ` has row `≥ lam + K` (well-founded induction on the row:
the cap witness is either non-capped, hence in the active band, or capped with a smaller row;
a cell capping itself has finite part `≥ K` and limit part `≥ lam`, else it would cap `d₀`). -/
theorem CapAt.row_ge {p : S α n} {Θ : Cell p.scheme.scheme}
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘ : p.label Θ = ⊤) {d₀ : p.scheme.scheme.below (p.scheme.scheme.cell Θ)}
    (hd₀ : p.label d₀.1 = ⊤) (hc₀ : ¬ p.ProvisionalCap d₀.1) {ν₀ : Ordinal.{0}}
    (hν₀ : p.scheme.rows.E Θ d₀ = ofOrd ν₀) :
    ∀ (ν : Ordinal.{0}) (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)), p.label d.1 = ⊤ →
      p.scheme.rows.E Θ d = ofOrd ν → CapAt p Θ d → limitPart ν₀ + p.topGrade ≤ ν := by
  set K := p.topGrade with hK
  have hfp₀ : finitePart ν₀ < K := by
    by_contra hge
    apply hc₀
    refine ⟨Θ, d₀.2, d₀, hsc, hgr, hΘ, hd₀, ?_⟩
    change extVisibilityReplace (p.scheme.rows.E Θ d₀) K K ≤ p.scheme.rows.E Θ d₀
    rw [hν₀, extVisibilityReplace_ofOrd, (visibilityReplace_self_iff ν₀ _).mpr (not_lt.mp hge)]
  intro ν
  induction ν using WellFoundedLT.induction with
  | _ ν ih =>
  intro d hd hν ⟨Sg, hSg, hle⟩
  rw [hν] at hle
  rcases ExtOrd.cases (p.scheme.rows.E Θ Sg) with hb | ht | ⟨μ, hμ⟩
  · exact absurd hb (row_ne_bot' p hΘ Sg hSg)
  · rw [ht, extVisibilityReplace_top] at hle
    exact absurd hle (not_le.mpr (ofOrd_lt_top _))
  · rw [hμ, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hle
    by_cases hcapS : CapAt p Θ Sg
    · -- the witness is itself capped
      rcases lt_or_ge μ ν with hlt | hge
      · exact (ih μ hlt Sg hSg hμ hcapS).trans ((le_visibilityReplace_self μ K).trans hle)
      · -- `μ ≥ ν` and `μ ⊔⁺_K K ≤ ν`: then `fp μ ≥ K` (else `μ ⊔⁺ K > μ ≥ ν`), so `ν = μ`
        have hfpμ : K ≤ finitePart μ := by
          by_contra hlt
          rw [visibilityReplace_of_finitePart_lt (not_le.mp hlt)] at hle
          have : ν < limitPart μ + K := by
            calc ν ≤ μ := hge
              _ = limitPart μ + finitePart μ := (decomposition μ).symm
              _ < limitPart μ + K := (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr (not_le.mp hlt))
          exact absurd hle (not_le.mpr this)
        rw [(visibilityReplace_self_iff μ K).mpr hfpμ] at hle
        have hμν : μ = ν := le_antisymm hle hge
        subst hμν
        -- `limitPart μ ≥ limitPart ν₀`, else `d` (row `μ`, `fp μ ≥ K`) would cap `d₀`
        have hlp : limitPart ν₀ ≤ limitPart μ := by
          by_contra hlt
          have hlt' := not_le.mp hlt
          apply hc₀
          refine ⟨Θ, d₀.2, Sg, hsc, hgr, hΘ, hSg, ?_⟩
          change extVisibilityReplace (p.scheme.rows.E Θ Sg) K K ≤ p.scheme.rows.E Θ d₀
          rw [hμ, hν₀, extVisibilityReplace_ofOrd, (visibilityReplace_self_iff μ K).mpr hfpμ,
            ofOrd_le_ofOrd]
          refine le_of_lt ?_
          calc μ = limitPart μ + (finitePart μ : Ordinal.{0}) := (decomposition μ).symm
            _ < limitPart μ + Ordinal.omega0 :=
                (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _)
            _ ≤ limitPart ν₀ := add_omega0_le_limitPart_of_lt (limitPart_limitPart μ) hlt'
            _ ≤ ν₀ := limitPart_le ν₀
        calc limitPart ν₀ + (K : Ordinal.{0}) ≤ limitPart μ + K := add_le_add hlp le_rfl
          _ ≤ limitPart μ + finitePart μ := add_le_add (le_refl _) (Nat.cast_le.mpr hfpμ)
          _ = μ := decomposition μ
    · -- the witness is a non-cap `∞`-cell: its row lies in the active band
      have hncS : ¬ p.ProvisionalCap Sg.1 := fun hc =>
        hcapS (by
          obtain ⟨Sg₁, h1, h2⟩ := hc.transport Sg.2 hsc hgr hΘ
          exact ⟨Sg₁, h1, h2⟩)
      obtain ⟨hfpμ, -, hlp⟩ := limitPart_eq_of_not_cap hsc hgr hΘ hSg hd₀ hncS hc₀ hμ hν₀
      rw [visibilityReplace_of_finitePart_lt hfpμ, hlp] at hle
      exact hle

/-- Every `∞`-row below a top witness is `≥ K` at cap level: a capped cell's row dominates
`E(Θ')(Σ) ⊔⁺_K K ≥ K` (via its own witness); here we only need the weak form for rows at our
witness `Θ`: if `fp ν ≥ K` then `ν ≥ K`. -/
theorem le_of_finitePart_ge {ν : Ordinal.{0}} {K : ℕ} (h : K ≤ finitePart ν) : (K :
  Ordinal.{0}) ≤ ν :=
  calc (K : Ordinal.{0}) ≤ finitePart ν := Nat.cast_le.mpr h
    _ ≤ limitPart ν + finitePart ν := le_add_of_nonneg_left zero_le
    _ = ν := decomposition ν

/-- **The band bridge.**  Below a top witness `Θ` of a stage type `p` there is a multiple of
`ω`, `lam`, such that every `∞`-cell `d` below `Θ` has row `≥ lam` and provisional value
`bandMap α lam K^p (E(Θ)(d))`. -/
theorem exists_bandBridge (p : S α n) {Θ : Cell p.scheme.scheme}
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘ : p.label Θ = ⊤) :
    ∃ lam : Ordinal.{0}, limitPart lam = lam ∧
      ∀ d : p.scheme.scheme.below (p.scheme.scheme.cell Θ), p.label d.1 = ⊤ →
        ofOrd lam ≤ p.scheme.rows.E Θ d ∧
          p.IsProvisionalValue d.1 (bandMap α lam p.topGrade (p.scheme.rows.E Θ d)) := by
  classical
  set K := p.topGrade with hK
  -- the cap case is uniform; the band index at `Θ` is the finite part of the row
  have hcapval : ∀ d : p.scheme.scheme.below (p.scheme.scheme.cell Θ), p.label d.1 = ⊤ →
      p.ProvisionalCap d.1 → p.IsProvisionalValue d.1 (ofOrd (α + K)) :=
    fun d hd hc => Or.inr (Or.inl ⟨hd, hc, rfl⟩)
  have hbandval : ∀ (d : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (ν : Ordinal.{0}),
      p.label d.1 = ⊤ → ¬ p.ProvisionalCap d.1 → p.scheme.rows.E Θ d = ofOrd ν →
      finitePart ν < K ∧ p.IsProvisionalValue d.1 (ofOrd (α + finitePart ν)) := by
    intro d ν hd hc hν
    have hfp : finitePart ν < K := by
      by_contra hge
      apply hc
      refine ⟨Θ, d.2, d, hsc, hgr, hΘ, hd, ?_⟩
      change extVisibilityReplace (p.scheme.rows.E Θ d) K K ≤ p.scheme.rows.E Θ d
      rw [hν, extVisibilityReplace_ofOrd, (visibilityReplace_self_iff ν _).mpr (not_lt.mp hge)]
    refine ⟨hfp, Or.inr (Or.inr ⟨hd, hc, finitePart ν, ⟨Θ, d.2, hsc, hgr, hΘ, ?_⟩, rfl⟩)⟩
    change p.scheme.rows.E Θ d = extVisibilityReplace (p.scheme.rows.E Θ d) K (finitePart ν)
    rw [hν, extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt hfp, decomposition]
  -- rows of `∞`-cells are `⊤` or ordinals
  have hrow : ∀ d : p.scheme.scheme.below (p.scheme.scheme.cell Θ), p.label d.1 = ⊤ →
      p.scheme.rows.E Θ d = ⊤ ∨ ∃ ν, p.scheme.rows.E Θ d = ofOrd ν := by
    intro d hd
    rcases ExtOrd.cases (p.scheme.rows.E Θ d) with hb | ht | ⟨ν, hν⟩
    · exact absurd hb (row_ne_bot' p hΘ d hd)
    · exact Or.inl ht
    · exact Or.inr ⟨ν, hν⟩
  by_cases hex : ∃ (d₀ : p.scheme.scheme.below (p.scheme.scheme.cell Θ)) (ν₀ : Ordinal.{0}),
      p.label d₀.1 = ⊤ ∧ ¬ p.ProvisionalCap d₀.1 ∧ p.scheme.rows.E Θ d₀ = ofOrd ν₀
  · obtain ⟨d₀, ν₀, hd₀, hc₀, hν₀⟩ := hex
    refine ⟨limitPart ν₀, limitPart_limitPart ν₀, fun d hd => ?_⟩
    rcases hrow d hd with ht | ⟨ν, hν⟩
    · rw [ht, bandMap_top]
      exact ⟨le_top, hcapval d hd (by
        refine ⟨Θ, d.2, d, hsc, hgr, hΘ, hd, ?_⟩
        change extVisibilityReplace (p.scheme.rows.E Θ d) K K ≤ p.scheme.rows.E Θ d
        rw [ht]; exact le_top)⟩
    · rw [hν]
      by_cases hc : p.ProvisionalCap d.1
      · -- capped: capped at `Θ` by transport, hence at cap level of the active band
        have hcapΘ : CapAt p Θ d := by
          obtain ⟨Sg₁, h1, h2⟩ := hc.transport d.2 hsc hgr hΘ
          exact ⟨Sg₁, h1, h2⟩
        have hge := CapAt.row_ge hsc hgr hΘ hd₀ hc₀ hν₀ ν d hd hν hcapΘ
        refine ⟨ofOrd_le_ofOrd.mpr ((le_add_of_nonneg_right zero_le).trans hge), ?_⟩
        rw [bandMap_ofOrd_of_cap hge]
        exact hcapval d hd hc
      · obtain ⟨hfp, hval⟩ := hbandval d ν hd hc hν
        obtain ⟨-, -, hlp⟩ := limitPart_eq_of_not_cap hsc hgr hΘ hd hd₀ hc hc₀ hν hν₀
        have hlν : limitPart ν₀ ≤ ν := by rw [← hlp]; exact limitPart_le ν
        have hlt : ν < limitPart ν₀ + K := by
          rw [← hlp]
          calc ν = limitPart ν + (finitePart ν : Ordinal.{0}) := (decomposition ν).symm
            _ < limitPart ν + K := (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hfp)
        refine ⟨ofOrd_le_ofOrd.mpr hlν, ?_⟩
        rw [bandMap_ofOrd_of_band hlν hlt]
        exact hval
  · -- every `∞`-cell below `Θ` is capped: `lam = 0`
    push Not at hex
    refine ⟨0, by simp [limitPart], fun d hd => ?_⟩
    have hc : p.ProvisionalCap d.1 := by
      rcases hrow d hd with ht | ⟨ν, hν⟩
      · refine ⟨Θ, d.2, d, hsc, hgr, hΘ, hd, ?_⟩
        change extVisibilityReplace (p.scheme.rows.E Θ d) K K ≤ p.scheme.rows.E Θ d
        rw [ht]; exact le_top
      · by_contra hnc
        exact hex d ν hd hnc hν
    refine ⟨?_, ?_⟩
    · rcases hrow d hd with ht | ⟨ν, hν⟩
      · rw [ht]; exact le_top
      · rw [hν]; exact ofOrd_le_ofOrd.mpr zero_le
    · rcases hrow d hd with ht | ⟨ν, hν⟩
      · rw [ht, bandMap_top]; exact hcapval d hd hc
      · rw [hν]
        -- every cap row is `≥ K`: the witness's row `μ` has `μ ⊔⁺_K K ≥ K`
        obtain ⟨Sg₁, h1, h2⟩ := hc.transport d.2 hsc hgr hΘ
        have hK : (0 : Ordinal.{0}) + K ≤ ν := by
          rw [zero_add]
          rcases ExtOrd.cases (p.scheme.rows.E Θ Sg₁) with hb | ht | ⟨μ, hμ⟩
          · exact absurd hb (row_ne_bot' p hΘ Sg₁ h1)
          · rw [ht, extVisibilityReplace_top] at h2
            change ⊤ ≤ p.scheme.rows.E Θ d at h2
            rw [hν] at h2
            exact absurd h2 (not_le.mpr (ofOrd_lt_top _))
          · change extVisibilityReplace (p.scheme.rows.E Θ Sg₁) K K ≤ p.scheme.rows.E Θ d at h2
            rw [hμ, hν, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at h2
            refine le_trans ?_ h2
            unfold visibilityReplace ordinalReplace
            split_ifs with hfp
            · exact le_add_of_nonneg_left zero_le
            · exact le_of_finitePart_ge (not_lt.mp hfp)
        rw [bandMap_ofOrd_of_cap hK]
        exact hcapval d hd hc


open Transform in
/-- **Lemma 5.3.5 at a top witness**: the row of a full-scope `∞`-cell `Θ` of grade `K^p`
transforms to the provisional values of the cells below `Θ` (`p⁺(Θ) = α + K^p` dominates
them all, so the cap by `p⁺(Θ)` is invisible). -/
theorem topRow_transformsTo_provisional (p : S α n) (hα : Order.IsSuccLimit α)
    {Θ : Cell p.scheme.scheme}
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (hΘ : p.label Θ = ⊤) :
    TransformsTo (fun d : p.scheme.scheme.below (p.scheme.scheme.cell Θ) =>
        p.scheme.scheme.grade d.1)
      (p.scheme.rows.E Θ) (fun d => p.someProvisionalValue d.1) := by
  obtain ⟨g, σ, hganti, hgself, hσbot, hσmono, hσ5, heq⟩ := p.respects.locality Θ
  obtain ⟨lam, hlam, hbridge⟩ := exists_bandBridge p hsc hgr hΘ
  have heq' : ∀ d : p.scheme.scheme.below (p.scheme.scheme.cell Θ),
      p.label d.1 = min (σ (p.scheme.rows.E Θ d)) (g (p.scheme.scheme.grade d.1)) := by
    intro d
    have := heq d
    change min (p.label d.1) (p.label Θ) = min (σ (p.scheme.rows.E Θ d))
      (g (p.scheme.scheme.grade d.1)) at this
    rwa [hΘ, min_top_right] at this
  have hgK : ∀ k, k ≤ p.topGrade → g k = ⊤ := by
    intro k hk
    have hΘ' := heq' ⟨Θ, GradedLe.refl _⟩
    change p.label Θ = min (σ (p.scheme.rows.E Θ ⟨Θ, GradedLe.refl _⟩))
      (g (p.scheme.scheme.grade Θ)) at hΘ'
    rw [hΘ, hgr] at hΘ'
    have hgKtop : g p.topGrade = ⊤ := top_le_iff.mp (hΘ'.le.trans (min_le_right _ _))
    rcases hk.lt_or_eq with hlt | rfl
    · exact top_le_iff.mp (hgKtop ▸ hganti _ _ hlt)
    · exact hgKtop
  refine TransformsTo.comp_bandMap (q := fun d => p.label d.1) g σ hganti hgself hσbot hσmono hσ5
    heq' hα hlam p.topGrade ?_ hgK ?_ ?_ ?_
  · intro d
    have h2 : p.scheme.scheme.grade d.1 ≤ p.scheme.scheme.grade Θ := d.2.2
    rwa [hgr] at h2
  · intro d
    exact p.label_bound d.1
  · intro d hd
    exact someProvisionalValue_of_ne_top hd.ne_top
  · intro d hd
    obtain ⟨hle, hval⟩ := hbridge d hd
    exact ⟨hle, (isProvisionalValue_iff.mp hval).symm⟩

end StageType

end VaughtConjecture.Knight
