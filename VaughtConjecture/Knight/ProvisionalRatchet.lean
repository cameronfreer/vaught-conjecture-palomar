/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProvisionalUniqueness
public import VaughtConjecture.Knight.Directedness
public import VaughtConjecture.Knight.FiniteOffset
public import VaughtConjecture.Knight.NormalForm
public import VaughtConjecture.Knight.VisibilityBandArithmetic
public import VaughtConjecture.Knight.FiniteRowReadback

/-! # Lemma 5.3.7: the provisional-value ratchet, and stable-value functionality

Knight's Lemma 5.3.7: if `p` is the
exact restriction of `q`, then for every cell `Ξ` of `p`, either `p⁺(Ξ) = q⁺(Ξ)` or
`q⁺(Ξ) ≥ α + K^p`.  Consequently the stabilization sets of Def. 5.3.9 are ratcheted in the
labelled-cover poset (`isRatcheted_stableSet`), Cor. 5.3.8's dominating ⇒ coinitial upgrade
applies, and the stabilized value is unique (`StabilizesTo.unique`, `HasStableValue.unique`).

**The argument** (the paper's Case 2 made exact in the faithful `⇒`).  `Ξ' := toCell Ξ`,
`K := K^p ≤ K^q`.  Clause 1 and the `q`-cap case are immediate.  If `q` is in the band case
with witness `Θ` (full scope, grade `K^q`, `z := E_q(Θ)(Ξ') = ofOrd β'`, `fp β' = j`) and `p` has
a witness `Ψ` (full scope in `p`, grade `K`), then `Ψ' := toCell Ψ` lies below `Θ`, and
consistency of the rows gives the locality transform `E_q(Ψ') ⇒ min(E_q(Θ) ∘ incl, y)`,
`y := E_q(Θ)(Ψ')`, with witnesses `g, σ`; `E_q(Ψ')` is `E_p(Ψ)` on the cells of `p`.  Reading it
at `Ψ'` gives `y ≤ g K`.
* If `y ≤ z`: `y` is self-visible at `K` (orderly), `¬cap_q` at `Σ := Ψ'` gives
  `z < y ⊔⁺_{K^q} K^q`, so `z` sits in the band of `y` with finite part `≥ K`: `j ≥ K`.
* If `z < y`: reading the transform at `Ξ'` gives `z = min(σ t, g (grade Ξ))`, `t := E_p(Ψ)(Ξ)`;
  the `g`-branch is impossible (`z < y ≤ g K ≤ g (grade Ξ)`), so `z = σ t ≤ g K`.
  - `p` band `i`: clause 5 transports `t = t ⊔⁺_K i` to `z = z ⊔⁺_K i`: `j = i` or `j ≥ K`.
  - `p` cap with `Σ`, `u := E_p(Ψ)(Σ)`, `u ⊔⁺_K K ≤ t`: `σ u ≤ σ t = z < g K`, clause 5 gives
    `(σ u) ⊔⁺_K K ≤ z`; the row values at `∞`-cells are not `-∞`, which forces
    `E_q(Θ)(Sg) = σ u ≠ -∞`; `¬cap_q` at `Sg` gives `z < (σ u) ⊔⁺_{K^q} K^q`; band position
    yields `j ≥ K`.

Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe w

/-! ### Ordinal band arithmetic -/

namespace Value

theorem le_finitePart_of_ge_of_lt {μ z : Ordinal.{0}} {K : ℕ}
    (h1 : limitPart μ + K ≤ z) {K' : ℕ} (h2 : z < limitPart μ + K') : K ≤ finitePart z := by
  have hlp : limitPart μ ≤ z := (le_add_of_nonneg_right zero_le).trans h1
  have hlim := limitPart_eq_of_le_of_lt hlp h2
  have hz := decomposition z
  rw [← hz, hlim] at h1
  exact (Nat.cast_le (α := Ordinal.{0})).mp ((add_le_add_iff_left _).mp h1)

/-- **Band position**: if `μ ⊔⁺_K K ≤ z < μ ⊔⁺_{K'} K'` with `K ≤ K'`, then `K ≤ finitePart z`. -/
theorem le_finitePart_of_visReplace_le_of_lt {μ z : Ordinal.{0}} {K K' : ℕ} (hK : K ≤ K')
    (hlo : visibilityReplace μ K K ≤ z) (hhi : z < visibilityReplace μ K' K') :
    K ≤ finitePart z := by
  unfold visibilityReplace ordinalReplace at hlo hhi
  by_cases hμK' : finitePart μ < K'
  · rw [ite_eq_left hμK'] at hhi
    by_cases hμK : finitePart μ < K
    · rw [ite_eq_left hμK] at hlo
      exact le_finitePart_of_ge_of_lt hlo hhi
    · rw [ite_eq_right hμK] at hlo
      have hlp : limitPart μ ≤ z := (limitPart_le μ).trans hlo
      have hlim := limitPart_eq_of_le_of_lt hlp hhi
      exact (not_lt.mp hμK).trans (finitePart_le_of_le hlim.symm hlo)
  · rw [ite_eq_right hμK'] at hhi
    have hμK : ¬ finitePart μ < K := fun h => hμK' (h.trans_le hK)
    rw [ite_eq_right hμK] at hlo
    exact absurd (hlo.trans_lt hhi) (lt_irrefl μ)

/-- A self-visible label that is neither `-∞` nor `∞` is an ordinal with finite part `≥ K`. -/
theorem exists_ordinal_of_selfVis {v : ExtOrd} {K : ℕ} (h : extVisibilityReplace v K K = v)
    (hbot : v ≠ ⊥) (htop : v ≠ ⊤) : ∃ μ : Ordinal.{0}, v = ofOrd μ ∧ K ≤ finitePart μ := by
  rcases (extVisibilityReplace_self_iff v K).mp h with rfl | rfl | ⟨μ, rfl, hμ⟩
  · exact absurd rfl hbot
  · exact absurd rfl htop
  · exact ⟨μ, rfl, hμ⟩

end Value

/-! ### Row values at `∞`-cells are not `-∞` -/

namespace StageType

variable {α : Ordinal.{0}} {m n : ℕ}

/-! ### Lemma 5.3.7 for a face restriction -/

open CellScheme.restrictFace (toCell belowMap)

variable {q : S α n} {f : Fin m ↪ Fin n} {hr : Finset.univ.image f ∈ q.scheme.scheme.plan}

/-- A full-scope cell of the restriction has, in `q`, the scope `image f univ`. -/
theorem scope_toCell_of_full (Ψ : Cell (q.scheme.scheme.restrictFace f hr))
    (hsc : (q.scheme.scheme.restrictFace f hr).scope Ψ = Finset.univ) :
    q.scheme.scheme.scope (toCell q.scheme.scheme f hr Ψ) = Finset.univ.image f := by
  rw [← CellScheme.restrictFace.image_scope_restrictFace q.scheme.scheme f hr Ψ, hsc]

/-- A full-scope witness of the restriction lies below a full-scope cell of `q` of at least
its grade. -/
theorem gradedLe_toCell_of_full (Ψ : Cell (q.scheme.scheme.restrictFace f hr))
    (hsc : (q.scheme.scheme.restrictFace f hr).scope Ψ = Finset.univ)
    {Θ : Cell q.scheme.scheme} (hscΘ : q.scheme.scheme.scope Θ = Finset.univ)
    (hgr : (q.scheme.scheme.restrictFace f hr).grade Ψ ≤ q.scheme.scheme.grade Θ) :
    GradedLe (q.scheme.scheme.cell (toCell q.scheme.scheme f hr Ψ)) (q.scheme.scheme.cell Θ) := by
  refine ⟨?_, ?_⟩
  · change q.scheme.scheme.scope (toCell q.scheme.scheme f hr Ψ) ⊆ q.scheme.scheme.scope Θ
    rw [scope_toCell_of_full Ψ hsc, hscΘ]
    exact Finset.subset_univ _
  · exact hgr

/-- **The `y ≤ z` half**: the row of the `q`-witness `Θ` at the restricted witness `Ψ'` (self-
visible at `K^p`) lies below `z`; `¬cap_q` at `Ψ'` then puts `z` in the band of `y` with finite
part `≥ K^p`. -/
theorem band_ge_of_row_le {Θ Ψ' Ξ' : Cell q.scheme.scheme}
    (hΞ'Θ : GradedLe (q.scheme.scheme.cell Ξ') (q.scheme.scheme.cell Θ))
    (hΨ'Θ : GradedLe (q.scheme.scheme.cell Ψ') (q.scheme.scheme.cell Θ))
    (hscΘ : q.scheme.scheme.scope Θ = Finset.univ) (hgrΘ : q.scheme.scheme.grade Θ = q.topGrade)
    (hΘtop : q.label Θ = ⊤) (hΨ'top : q.label Ψ' = ⊤) {K : ℕ}
    (hgrΨ' : q.scheme.scheme.grade Ψ' = K) (hK : K ≤ q.topGrade)
    (hcapq : ¬ q.ProvisionalCap Ξ') {β' : Ordinal.{0}}
    (hz : q.scheme.rows.E Θ ⟨Ξ', hΞ'Θ⟩ = ofOrd β')
    (hyz : q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩ ≤ q.scheme.rows.E Θ ⟨Ξ', hΞ'Θ⟩) :
    K ≤ finitePart β' := by
  set y := q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩ with hy
  have hself : extVisibilityReplace y K K = y := by
    have h := q.scheme.rows.orderly Θ ⟨Ψ', hΨ'Θ⟩
    change y = extVisibilityReplace y (q.scheme.scheme.grade Ψ') (q.scheme.scheme.grade Ψ') at h
    rw [hgrΨ'] at h
    exact h.symm
  have hnotcap : ¬ extVisibilityReplace y q.topGrade q.topGrade ≤
      q.scheme.rows.E Θ ⟨Ξ', hΞ'Θ⟩ := fun hle =>
    hcapq ⟨Θ, hΞ'Θ, ⟨Ψ', hΨ'Θ⟩, hscΘ, hgrΘ, hΘtop, hΨ'top, hle⟩
  have hybot : y ≠ ⊥ := by
    intro hb
    rw [hb] at hnotcap
    exact hnotcap (by simp)
  have hytop : y ≠ ⊤ := by
    intro ht
    rw [ht, hz] at hyz
    exact absurd hyz (by simp)
  obtain ⟨μ, hμ, hKμ⟩ := exists_ordinal_of_selfVis hself hybot hytop
  rw [hμ, hz, ofOrd_le_ofOrd] at hyz
  rw [hμ, hz, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hnotcap
  have hlo : visibilityReplace μ K K ≤ β' := by
    rw [(visibilityReplace_self_iff μ K).mpr hKμ]
    exact hyz
  exact le_finitePart_of_visReplace_le_of_lt hK hlo (not_le.mp hnotcap)

/-- The transform data of the locality of `E_q(Θ)` at `Ψ'`, read at a cell `d` below `Ψ'`:
`min (E_q Θ d) y = min (σ (E_q Ψ' d)) (g (grade d))`, together with `y ≤ g (grade Ψ')`. -/
theorem locality_data {Θ Ψ' : Cell q.scheme.scheme}
    (hΨ'Θ : GradedLe (q.scheme.scheme.cell Ψ') (q.scheme.scheme.cell Θ)) :
    ∃ (g : ℕ → ExtOrd) (σ : ExtOrd → ExtOrd),
      (∀ n m : ℕ, n < m → g m ≤ g n) ∧ Monotone σ ∧
      (∀ (a : ExtOrd) (k : ℕ), σ a ≤ g k → ∀ i : ℕ, i ≤ k →
        σ (extVisibilityReplace a k i) = extVisibilityReplace (σ a) k i) ∧
      (∀ d : q.scheme.scheme.below (q.scheme.scheme.cell Ψ'),
        min (q.scheme.rows.E Θ ⟨d.1, d.2.trans hΨ'Θ⟩) (q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩) =
          min (σ (q.scheme.rows.E Ψ' d)) (g (q.scheme.scheme.grade d.1))) ∧
      q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩ ≤ g (q.scheme.scheme.grade Ψ') := by
  obtain ⟨g, σ, hganti, -, -, hσmono, hσ5, hloc⟩ := (q.scheme.consistent Θ).locality ⟨Ψ', hΨ'Θ⟩
  refine ⟨g, σ, hganti, hσmono, hσ5, fun d => hloc d, ?_⟩
  have h := hloc ⟨Ψ', GradedLe.refl _⟩
  change min (q.scheme.rows.E Θ ⟨Ψ', _⟩) (q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩) =
    min (σ (q.scheme.rows.E Ψ' ⟨Ψ', GradedLe.refl _⟩)) (g (q.scheme.scheme.grade Ψ')) at h
  rw [min_self] at h
  rw [h]
  exact min_le_right _ _

/-- **Lemma 5.3.7, band/band core**: `p` in the band case with index `i`, `q` in the band case
with index `j` (`¬cap` on both sides): `i = j` or `K^p ≤ j`. -/
theorem ratchet_core_band (Ξ : Cell (q.scheme.scheme.restrictFace f hr))
    (htop : (q.restrictFace f hr).label Ξ = ⊤)
    (hcapp : ¬ (q.restrictFace f hr).ProvisionalCap Ξ) {i : ℕ}
    (hbandp : (q.restrictFace f hr).ProvisionalBand Ξ i)
    (hcapq : ¬ q.ProvisionalCap (toCell q.scheme.scheme f hr Ξ)) {j : ℕ}
    (hbandq : q.ProvisionalBand (toCell q.scheme.scheme f hr Ξ) j) :
    i = j ∨ (q.restrictFace f hr).topGrade ≤ j := by
  obtain ⟨Ψ, hΞΨ, hscΨ, hgrΨ, hΨtop, heqp⟩ := hbandp
  obtain ⟨Θ, hΞ'Θ, hscΘ, hgrΘ, hΘtop, heqq⟩ := hbandq
  have hKle : (q.restrictFace f hr).topGrade ≤ q.topGrade :=
    topGrade_le_of_typeMap_eq_some (typeMap_eq_some f q hr)
  set K := (q.restrictFace f hr).topGrade with hK
  -- the restricted witness in q
  set Ψ' := toCell q.scheme.scheme f hr Ψ with hΨ'
  have hgrΨ' : q.scheme.scheme.grade Ψ' = K := hgrΨ
  have hΨ'top : q.label Ψ' = ⊤ := hΨtop
  have hΨ'Θ : GradedLe (q.scheme.scheme.cell Ψ') (q.scheme.scheme.cell Θ) :=
    gradedLe_toCell_of_full Ψ hscΨ hscΘ (by rw [hgrΘ]; exact hgrΨ ▸ hKle)
  have hΞ'Ψ' : GradedLe (q.scheme.scheme.cell (toCell q.scheme.scheme f hr Ξ))
      (q.scheme.scheme.cell Ψ') := CellScheme.restrictFace.gradedLe_of_restrictFace _ f hr hΞΨ
  obtain ⟨g, σ, hganti, hσmono, hσ5, hloc, hyg⟩ := locality_data (Θ := Θ) hΨ'Θ
  -- values
  set z := q.scheme.rows.E Θ ⟨toCell q.scheme.scheme f hr Ξ, hΞ'Θ⟩ with hz
  set y := q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩ with hy
  set t := (q.restrictFace f hr).scheme.rows.E Ψ ⟨Ξ, hΞΨ⟩ with ht
  have hloc_Ξ := hloc ⟨toCell q.scheme.scheme f hr Ξ, hΞ'Ψ'⟩
  change min z y = min (σ t) (g (q.scheme.scheme.grade (toCell q.scheme.scheme f hr Ξ)))
    at hloc_Ξ
  rw [hgrΨ'] at hyg
  obtain ⟨β', hzβ, hfp', hj⟩ :=
    ProvisionalBand.exists_ordinal (show q.label (toCell q.scheme.scheme f hr Ξ) = ⊤ from htop)
      hcapq hΞ'Θ hscΘ hgrΘ hΘtop heqq
  obtain ⟨τ, htτ, hfpτ, hi⟩ :=
    ProvisionalBand.exists_ordinal htop hcapp hΞΨ hscΨ hgrΨ hΨtop heqp
  rcases le_or_gt y z with hyz | hzy
  · right
    rw [hj]
    exact band_ge_of_row_le hΞ'Θ hΨ'Θ hscΘ hgrΘ hΘtop hΨ'top hgrΨ' hKle hcapq hzβ hyz
  · -- z < y: the minimum on the left is z, the one on the right is σ t
    have hgrΞ : q.scheme.scheme.grade (toCell q.scheme.scheme f hr Ξ) ≤ K := by
      have h2 : (q.restrictFace f hr).scheme.scheme.grade Ξ ≤
          (q.restrictFace f hr).scheme.scheme.grade Ψ := hΞΨ.2
      rw [hgrΨ] at h2
      exact h2
    have hgle : g K ≤ g (q.scheme.scheme.grade (toCell q.scheme.scheme f hr Ξ)) := by
      rcases hgrΞ.lt_or_eq with hlt | heq
      · exact hganti _ _ hlt
      · rw [heq]
    rw [min_eq_left hzy.le] at hloc_Ξ
    have hzσ : z = σ t := by
      rcases le_total (σ t) (g (q.scheme.scheme.grade (toCell q.scheme.scheme f hr Ξ))) with
        hle | hle
      · rw [min_eq_left hle] at hloc_Ξ
        exact hloc_Ξ
      · rw [min_eq_right hle] at hloc_Ξ
        exact absurd hloc_Ξ (lt_of_lt_of_le hzy (hyg.trans hgle)).ne
    have hσt : σ t ≤ g K := hzσ ▸ (hzy.le.trans hyg)
    have hiK : i ≤ K := (hi ▸ hfpτ).le
    have h5 := hσ5 t K hσt i hiK
    rw [← heqp] at h5
    -- h5 : σ t = extVisibilityReplace (σ t) K i, i.e. z = z ⊔⁺_K i
    have hzβ' : z = ofOrd β' := hzβ
    rw [← hzσ, hzβ', extVisibilityReplace_ofOrd] at h5
    have hβ'eq : β' = visibilityReplace β' K i := ofOrd_inj.mp h5
    by_cases hlt : finitePart β' < K
    · left
      unfold visibilityReplace ordinalReplace at hβ'eq
      rw [ite_eq_left hlt] at hβ'eq
      have hcast : (i : Ordinal.{0}) = (finitePart β' : Ordinal.{0}) :=
        add_left_cancel (hβ'eq.symm.trans (decomposition β').symm)
      have : i = finitePart β' := by exact_mod_cast hcast
      omega
    · right
      rw [hj]
      exact not_lt.mp hlt

/-- **Lemma 5.3.7, cap/band core**: `p` in the cap case, `q` in the band case with index `j`:
`K^p ≤ j`. -/
theorem ratchet_core_cap (Ξ : Cell (q.scheme.scheme.restrictFace f hr))
    (htop : (q.restrictFace f hr).label Ξ = ⊤)
    (hcapp : (q.restrictFace f hr).ProvisionalCap Ξ)
    (hcapq : ¬ q.ProvisionalCap (toCell q.scheme.scheme f hr Ξ)) {j : ℕ}
    (hbandq : q.ProvisionalBand (toCell q.scheme.scheme f hr Ξ) j) :
    (q.restrictFace f hr).topGrade ≤ j := by
  obtain ⟨Ψ, hΞΨ, Sg, hscΨ, hgrΨ, hΨtop, hSgtop, hcapineq⟩ := hcapp
  obtain ⟨Θ, hΞ'Θ, hscΘ, hgrΘ, hΘtop, heqq⟩ := hbandq
  have hKle : (q.restrictFace f hr).topGrade ≤ q.topGrade :=
    topGrade_le_of_typeMap_eq_some (typeMap_eq_some f q hr)
  set K := (q.restrictFace f hr).topGrade with hK
  set Ψ' := toCell q.scheme.scheme f hr Ψ with hΨ'
  have hgrΨ' : q.scheme.scheme.grade Ψ' = K := hgrΨ
  have hΨ'top : q.label Ψ' = ⊤ := hΨtop
  have hΨ'Θ : GradedLe (q.scheme.scheme.cell Ψ') (q.scheme.scheme.cell Θ) :=
    gradedLe_toCell_of_full Ψ hscΨ hscΘ (by rw [hgrΘ]; exact hgrΨ ▸ hKle)
  have hΞ'Ψ' : GradedLe (q.scheme.scheme.cell (toCell q.scheme.scheme f hr Ξ))
      (q.scheme.scheme.cell Ψ') := CellScheme.restrictFace.gradedLe_of_restrictFace _ f hr hΞΨ
  -- the cap cell Σ, transported
  set Sg' : q.scheme.scheme.below (q.scheme.scheme.cell Ψ') := belowMap q.scheme.scheme f hr Ψ Sg
    with hSg'
  have hSg'top : q.label Sg'.1 = ⊤ := hSgtop
  have hgrSg : q.scheme.scheme.grade Sg'.1 ≤ K := by
    have h2 : (q.restrictFace f hr).scheme.scheme.grade Sg.1 ≤
        (q.restrictFace f hr).scheme.scheme.grade Ψ := Sg.2.2
    rw [hgrΨ] at h2
    exact h2
  obtain ⟨g, σ, hganti, hσmono, hσ5, hloc, hyg⟩ := locality_data (Θ := Θ) hΨ'Θ
  set z := q.scheme.rows.E Θ ⟨toCell q.scheme.scheme f hr Ξ, hΞ'Θ⟩ with hz
  set y := q.scheme.rows.E Θ ⟨Ψ', hΨ'Θ⟩ with hy
  set t := (q.restrictFace f hr).scheme.rows.E Ψ ⟨Ξ, hΞΨ⟩ with ht
  set u := (q.restrictFace f hr).scheme.rows.E Ψ Sg with hu
  set s := q.scheme.rows.E Θ ⟨Sg'.1, Sg'.2.trans hΨ'Θ⟩ with hs
  have hloc_Ξ := hloc ⟨toCell q.scheme.scheme f hr Ξ, hΞ'Ψ'⟩
  change min z y = min (σ t) (g (q.scheme.scheme.grade (toCell q.scheme.scheme f hr Ξ)))
    at hloc_Ξ
  have hloc_Sg := hloc Sg'
  change min s y = min (σ u) (g (q.scheme.scheme.grade Sg'.1)) at hloc_Sg
  rw [hgrΨ'] at hyg
  obtain ⟨β', hzβ, hfp', hj⟩ :=
    ProvisionalBand.exists_ordinal (show q.label (toCell q.scheme.scheme f hr Ξ) = ⊤ from htop)
      hcapq hΞ'Θ hscΘ hgrΘ hΘtop heqq
  rcases le_or_gt y z with hyz | hzy
  · rw [hj]
    exact band_ge_of_row_le hΞ'Θ hΨ'Θ hscΘ hgrΘ hΘtop hΨ'top hgrΨ' hKle hcapq hzβ hyz
  · have hgrΞ : q.scheme.scheme.grade (toCell q.scheme.scheme f hr Ξ) ≤ K := by
      have h2 : (q.restrictFace f hr).scheme.scheme.grade Ξ ≤
          (q.restrictFace f hr).scheme.scheme.grade Ψ := hΞΨ.2
      rw [hgrΨ] at h2
      exact h2
    have hgle : g K ≤ g (q.scheme.scheme.grade (toCell q.scheme.scheme f hr Ξ)) := by
      rcases hgrΞ.lt_or_eq with hlt | heq
      · exact hganti _ _ hlt
      · rw [heq]
    have hgleS : g K ≤ g (q.scheme.scheme.grade Sg'.1) := by
      rcases hgrSg.lt_or_eq with hlt | heq
      · exact hganti _ _ hlt
      · rw [heq]
    rw [min_eq_left hzy.le] at hloc_Ξ
    have hzσ : z = σ t := by
      rcases le_total (σ t) (g (q.scheme.scheme.grade (toCell q.scheme.scheme f hr Ξ)))
          with hle | hle
      · rw [min_eq_left hle] at hloc_Ξ
        exact hloc_Ξ
      · rw [min_eq_right hle] at hloc_Ξ
        exact absurd hloc_Ξ (lt_of_lt_of_le hzy (hyg.trans hgle)).ne
    -- u ≤ t, hence σ u ≤ σ t = z
    have hut : u ≤ t := (le_extVisibilityReplace_self u K).trans hcapineq
    have hσu : σ u ≤ z := hzσ ▸ hσmono hut
    have hσuK : σ u ≤ g K := hσu.trans (hzy.le.trans hyg)
    -- s = σ u
    have hsσ : s = σ u := by
      rcases le_total (σ u) (g (q.scheme.scheme.grade Sg'.1)) with hle | hle
      · rw [min_eq_left hle] at hloc_Sg
        rcases le_total s y with hsy | hys
        · rw [min_eq_left hsy] at hloc_Sg
          exact hloc_Sg
        · rw [min_eq_right hys] at hloc_Sg
          -- y = σ u ≤ z < y
          exact absurd (hloc_Sg ▸ hσu) (not_le.mpr hzy)
      · -- y ≤ g K ≤ g (grade Σ') ≤ σ u ≤ z < y
        exact absurd (lt_of_le_of_lt ((hyg.trans hgleS).trans (hle.trans hσu)) hzy)
          (lt_irrefl y)
    -- clause 5 at (u, K, K): (σ u) ⊔⁺_K K ≤ z
    have h5 := hσ5 u K hσuK K le_rfl
    have hlo : extVisibilityReplace (σ u) K K ≤ z := by
      rw [← h5, hzσ]
      exact hσmono hcapineq
    -- ¬cap_q at Sg: z < s ⊔⁺_{K^q} K^q
    have hnotcap : ¬ extVisibilityReplace s q.topGrade q.topGrade ≤ z := fun hle =>
      hcapq ⟨Θ, hΞ'Θ, ⟨Sg'.1, Sg'.2.trans hΨ'Θ⟩, hscΘ, hgrΘ, hΘtop, hSg'top, hle⟩
    have hsbot : s ≠ ⊥ := row_ne_bot_of_label_top q hΘtop ⟨Sg'.1, Sg'.2.trans hΨ'Θ⟩ hSg'top
    have hσubot : σ u ≠ ⊥ := hsσ ▸ hsbot
    have hzβ' : z = ofOrd β' := hzβ
    have hσutop : σ u ≠ ⊤ := by
      intro h
      rw [h, hzβ'] at hσu
      exact absurd hσu (by simp)
    rcases ExtOrd.cases (σ u) with hb | hT | ⟨μ, hμ⟩
    · exact absurd hb hσubot
    · exact absurd hT hσutop
    rw [hμ, hzβ', extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hlo
    rw [hsσ, hμ, hzβ', extVisibilityReplace_ofOrd, ofOrd_le_ofOrd] at hnotcap
    rw [hj]
    exact le_finitePart_of_visReplace_le_of_lt hKle hlo (not_le.mp hnotcap)

/-- **Lemma 5.3.7 (restriction form)**: for a cell `Ξ` of `p := q.restrictFace f hr` with
provisional values `v` in `p` and `w` at `toCell Ξ` in `q`: `v = w` or `α + K^p ≤ w`. -/
theorem provisional_ratchet (Ξ : Cell (q.scheme.scheme.restrictFace f hr)) {v w : ExtOrd}
    (hv : (q.restrictFace f hr).IsProvisionalValue Ξ v)
    (hw : q.IsProvisionalValue (toCell q.scheme.scheme f hr Ξ) w) :
    v = w ∨ ofOrd (α + (q.restrictFace f hr).topGrade) ≤ w := by
  have hlab : q.label (toCell q.scheme.scheme f hr Ξ) = (q.restrictFace f hr).label Ξ := rfl
  have hKle : (q.restrictFace f hr).topGrade ≤ q.topGrade :=
    topGrade_le_of_typeMap_eq_some (typeMap_eq_some f q hr)
  have hKq : ofOrd (α + (q.restrictFace f hr).topGrade) ≤ ofOrd (α + q.topGrade) := by
    rw [ofOrd_le_ofOrd]
    exact add_le_add (le_refl α) ((Nat.cast_le (α := Ordinal.{0})).mpr hKle)
  rcases hv with ⟨hne, rfl⟩ | ⟨htop, hcapp, rfl⟩ | ⟨htop, hcapp, i, hbandp, rfl⟩
  · rcases hw with ⟨-, rfl⟩ | ⟨htop', -, -⟩ | ⟨htop', -, -⟩
    · exact Or.inl rfl
    · exact absurd (hlab ▸ htop') hne
    · exact absurd (hlab ▸ htop') hne
  · rcases hw with ⟨hne', -⟩ | ⟨-, -, rfl⟩ | ⟨htop', hcapq, j, hbandq, rfl⟩
    · exact absurd (hlab ▸ htop) hne'
    · exact Or.inr hKq
    · right
      rw [ofOrd_le_ofOrd]
      exact add_le_add (le_refl α) ((Nat.cast_le (α := Ordinal.{0})).mpr
        (ratchet_core_cap Ξ htop hcapp hcapq hbandq))
  · rcases hw with ⟨hne', -⟩ | ⟨-, -, rfl⟩ | ⟨htop', hcapq, j, hbandq, rfl⟩
    · exact absurd (hlab ▸ htop) hne'
    · exact Or.inr hKq
    · rcases ratchet_core_band Ξ htop hcapp hbandp hcapq hbandq with hij | hK
      · exact Or.inl (by rw [hij])
      · right
        rw [ofOrd_le_ofOrd]
        exact add_le_add (le_refl α) ((Nat.cast_le (α := Ordinal.{0})).mpr hK)

/-- **Lemma 5.3.7 (`typeMap` form)**: along `typeMap f q = some p`, provisional values of a
cell `Ξ` of `p` and of `mapCell Ξ` in `q` agree or the latter is `≥ α + K^p`. -/
theorem provisional_ratchet' {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (Ξ : Cell p.scheme.scheme) {v w : ExtOrd}
    (hv : p.IsProvisionalValue Ξ v) (hw : q.IsProvisionalValue (mapCell h Ξ) w) :
    v = w ∨ ofOrd (α + p.topGrade) ≤ w := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some h, restrictFace_eq_of_typeMap_eq_some h⟩
  exact provisional_ratchet Ξ hv hw

/-- **Provisional monotonicity along an exact face.**  The ratchet (Lemma 5.3.7) and the source
bound `IsProvisionalValue.le` together give `v ≤ v'` outright.  This is the canonical home of
the inequality; the ratchet itself is retained for clients that need its gap information. -/
theorem IsProvisionalValue.le_of_typeMap {α : Ordinal.{0}} {n m : ℕ}
    {p : S α n} {q : S α m} {f : Fin n ↪ Fin m}
    (hf : typeMap f q = some p) {d : Cell p.scheme.scheme} {v v' : ExtOrd}
    (hv : p.IsProvisionalValue d v) (hv' : q.IsProvisionalValue (mapCell hf d) v') :
    v ≤ v' := by
  rcases provisional_ratchet' hf d hv hv' with h | h
  · exact h.le
  · exact hv.le.trans h

end StageType

/-! ### The ratchet on the labelled-cover poset, and stable-value functionality -/

namespace KnightRealization

open StageType

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-- The embedding of a labelled cover into a larger one is determined by the tuples. -/
theorem LabelledExt.emb_unique {x y : R.LabelledExt} {f f' : Fin x.arity ↪ Fin y.arity}
    (hf : f.trans y.tuple = x.tuple) (hf' : f'.trans y.tuple = x.tuple) : f = f' := by
  apply Function.Embedding.ext
  intro i
  apply y.tuple.injective
  have h1 := DFunLike.congr_fun hf i
  have h2 := DFunLike.congr_fun hf' i
  simp only [Function.Embedding.trans_apply] at h1 h2
  exact h1.trans h2.symm

/-- **Lemma 5.3.7 on the poset**: the stabilization sets are ratcheted. -/
theorem isRatcheted_stableSet (x : R.LabelledExt) (Xi : Cell x.type.scheme.scheme)
    (γ : ExtOrd) : IsRatcheted (stableSet x Xi γ) := by
  intro y hy z hyz hz w hzw hw
  obtain ⟨f₁, hf₁, hpq₁, hval₁⟩ := hy
  obtain ⟨f₂, hf₂, hpq₂⟩ := hyz
  obtain ⟨f₃, hf₃, hpq₃⟩ := hzw
  obtain ⟨f₄, hf₄, hpq₄, hval₄⟩ := hw
  -- the cell of Ξ in z and in w
  have hpqz : typeMap (f₁.trans f₂) z.type = some x.type := by
    rw [← typeMap_trans f₁ f₂ z.type y.type hpq₂]
    exact hpq₁
  have hpqw : typeMap ((f₁.trans f₂).trans f₃) w.type = some x.type := by
    rw [← typeMap_trans (f₁.trans f₂) f₃ w.type z.type hpq₃]
    exact hpqz
  have hf₄' : f₄ = (f₁.trans f₂).trans f₃ := by
    apply LabelledExt.emb_unique hf₄
    rw [Function.Embedding.trans_assoc, hf₃, Function.Embedding.trans_assoc, hf₂, hf₁]
  subst hf₄'
  -- values
  set vz := z.type.someProvisionalValue (mapCell hpqz Xi) with hvz
  have hvz_is := isProvisionalValue_someProvisionalValue z.type (mapCell hpqz Xi)
  have hval₄' : w.type.IsProvisionalValue (mapCell hpqw Xi) γ := hval₄
  -- y ≤ z: γ = vz or α + K^y ≤ vz
  have h1 := provisional_ratchet' hpq₂ (mapCell hpq₁ Xi) hval₁
    (by rw [← mapCell_trans hpq₂ hpq₁ hpqz Xi]; exact hvz_is)
  -- z ≤ w: vz = γ or α + K^z ≤ γ
  have h2 := provisional_ratchet' hpq₃ (mapCell hpqz Xi) hvz_is
    (by rw [← mapCell_trans hpq₃ hpqz hpqw Xi]; exact hval₄')
  -- z ∉ D means vz ≠ γ
  have hne : vz ≠ γ := fun heq => hz ⟨f₁.trans f₂, by
    rw [Function.Embedding.trans_assoc, hf₂, hf₁], hpqz, heq ▸ hvz_is⟩
  rcases h1 with h1 | h1
  · exact hne h1.symm
  rcases h2 with h2 | h2
  · exact hne h2
  -- α + K^z ≤ γ ≤ α + K^y ≤ vz ≤ α + K^z
  have hγle : γ ≤ ofOrd (α.1 + y.type.topGrade) := hval₁.le
  have hvzle : vz ≤ ofOrd (α.1 + z.type.topGrade) := hvz_is.le
  have hKyz : y.type.topGrade ≤ z.type.topGrade := topGrade_le_of_typeMap_eq_some hpq₂
  have hvzγ : vz = γ := by
    apply le_antisymm
    · calc vz ≤ ofOrd (α.1 + z.type.topGrade) := hvzle
        _ ≤ γ := h2
    · calc γ ≤ ofOrd (α.1 + y.type.topGrade) := hγle
        _ ≤ vz := h1
  exact hne hvzγ

/-! ### Stable-value functionality from exact consistency alone

Each stabilization witness supplies a realized extension on which the other stabilization can
be tested; provisional monotonicity along the exact face then orders the two values.  Neither
covering nor a separately chosen root realization enters. -/

/-- Any realized provisional value of a source cell lies below a stabilized value of that cell:
stabilization supplies a larger realized tuple, exact consistency identifies the face, and
provisional monotonicity compares the readings. -/
theorem StabilizesTo.provisional_le (hcons : R.IsExactParentConsistent)
    {n m : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {u : Fin m ↪ M} {q : S α.1 m}
    (hu : R.eval u = some q) {f : Fin n ↪ Fin m} (hf : f.trans u = t)
    (hpq : typeMap f q = some p) {d : Cell p.scheme.scheme} {v γ : ExtOrd}
    (hv : q.IsProvisionalValue (mapCell hpq d) v) (hγ : R.StabilizesTo t p d γ) : v ≤ γ := by
  obtain ⟨k, z, g, e, r, hpr, hz, hgz, hez, hγz⟩ := hγ u
  have hqr : typeMap g r = some q := by
    have h := hcons z r g hz
    rw [hgz, hu] at h
    exact h.symm
  have hfg : (f.trans g).trans z = t := by
    rw [Function.Embedding.trans_assoc, hgz, hf]
  have he : e = f.trans g := by
    apply Function.Embedding.ext
    intro i
    apply z.injective
    exact (DFunLike.congr_fun hez i).trans (DFunLike.congr_fun hfg i).symm
  subst he
  have hγz' : r.IsProvisionalValue (mapCell hqr (mapCell hpq d)) γ := by
    rw [← mapCell_trans hqr hpq hpr d]
    exact hγz
  exact hv.le_of_typeMap hqr hγz'

/-- **Functionality of the stabilized value** (Def. 5.3.9) **from exact consistency alone**. -/
theorem StabilizesTo.unique_of_consistent (hcons : R.IsExactParentConsistent)
    {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {d : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.StabilizesTo t p d γ) (h' : R.StabilizesTo t p d γ') : γ = γ' := by
  apply le_antisymm
  · obtain ⟨m, u, g, f, q, hpq, hu, _, hf, hv⟩ := h t
    exact StabilizesTo.provisional_le hcons hu hf hpq hv h'
  · obtain ⟨m, u, g, f, q, hpq, hu, _, hf, hv⟩ := h' t
    exact StabilizesTo.provisional_le hcons hu hf hpq hv h

/-- **Functionality of `M⁺(Ξ)`** (the graph of Def. 5.3.9 is a function), from exact
consistency alone. -/
theorem HasStableValue.unique_of_consistent (hcons : R.IsExactParentConsistent)
    {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {d : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.HasStableValue t p d γ) (h' : R.HasStableValue t p d γ') : γ = γ' := by
  rcases h with ⟨hlt, hs⟩ | ⟨rfl, hno⟩ <;> rcases h' with ⟨hlt', hs'⟩ | ⟨rfl, hno'⟩
  · exact StabilizesTo.unique_of_consistent hcons @hs @hs'
  · exact absurd @hs (hno' γ hlt)
  · exact absurd @hs' (hno γ' hlt')
  · rfl

set_option linter.unusedVariables false in
/-- **Functionality of the stabilized value** (Def. 5.3.9), in its original interface.  The
covering and root-evaluation hypotheses are no longer used; see
`StabilizesTo.unique_of_consistent`.  The former dominating/coinitial proof is superseded by
provisional monotonicity, while `isRatcheted_stableSet` and the dominating theory remain
available for clients that need them. -/
theorem StabilizesTo.unique (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.StabilizesTo t p Xi γ) (h' : R.StabilizesTo t p Xi γ') : γ = γ' :=
  StabilizesTo.unique_of_consistent hcons h h'

set_option linter.unusedVariables false in
/-- **Functionality of `M⁺(Ξ)`** (the graph of Def. 5.3.9 is a function), in its original
interface; see `HasStableValue.unique_of_consistent`. -/
theorem HasStableValue.unique (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.HasStableValue t p Xi γ) (h' : R.HasStableValue t p Xi γ') : γ = γ' :=
  HasStableValue.unique_of_consistent hcons h h'

/-- Convenience wrappers for a full model. -/
theorem IsModel.stabilizesTo_unique (hR : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.StabilizesTo t p Xi γ) (h' : R.StabilizesTo t p Xi γ') : γ = γ' :=
  StabilizesTo.unique hR.consistent hR.covering hpt h h'

theorem IsModel.hasStableValue_unique (hR : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} {γ γ' : ExtOrd}
    (h : R.HasStableValue t p Xi γ) (h' : R.HasStableValue t p Xi γ') : γ = γ' :=
  HasStableValue.unique hR.consistent hR.covering hpt h h'

end KnightRealization

end VaughtConjecture.Knight
