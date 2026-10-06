/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.VisibilityBandArithmetic
public import VaughtConjecture.Knight.ProvisionalUniqueness
public import VaughtConjecture.Knight.Reduction

/-! # Finite band readback for higher stage types

The band case of Lemma 5.5.2 uses only ordinal arithmetic, lawful finite labels,
and provisional values of the literal reduct. The public declarations retain
their original names and proofs and are re-exported by `ExpansionUniqueness`.

This supplier excludes the expansion-uniqueness, reduct-model, block-geometry,
and provisional-ratchet cones. Visibility arithmetic is supplied independently;
`Model` remains upstream of the provisional definitions in `Terminal`.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

/-! ### Ordinal band arithmetic -/

namespace Value

theorem limitPart_of_succLimit {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) :
    limitPart α = α :=
  le_antisymm (limitPart_le α) (succLimit_le_limitPart hα le_rfl)

theorem limitPart_succLimit_add_nat {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) (i : ℕ) :
    limitPart (α + i) = α := by
  have h := limitPart_limitPart_add_nat α i
  rwa [limitPart_of_succLimit hα] at h

theorem finitePart_succLimit_add_nat {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) (i : ℕ) :
    finitePart (α + i) = i := by
  have h := finitePart_limitPart_add_nat α i
  rwa [limitPart_of_succLimit hα] at h

theorem exists_nat_of_lt_add_omega {α μ : Ordinal.{0}} (hle : α ≤ μ)
    (hlt : μ < α + Ordinal.omega0) : ∃ k : ℕ, μ = α + k := by
  obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp ((Ordinal.sub_lt_of_le hle).mpr hlt)
  exact ⟨k, by rw [← hk, Ordinal.add_sub_cancel_of_le hle]⟩

/-- `visibilityReplace` below the threshold: `μ ⊔_K i = limitPart μ + i` when `fp μ < K`. -/
theorem visibilityReplace_of_finitePart_lt {μ : Ordinal.{0}} {K i : ℕ} (h : finitePart μ < K) :
    visibilityReplace μ K i = limitPart μ + i := by
  unfold visibilityReplace ordinalReplace
  rw [ite_eq_left h]

/-- `limitPart μ + K ≤ μ ⊔_K K` always. -/
theorem limitPart_add_le_visibilityReplace (μ : Ordinal.{0}) (K : ℕ) :
    limitPart μ + K ≤ visibilityReplace μ K K := by
  unfold visibilityReplace ordinalReplace
  by_cases h : finitePart μ < K
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    calc limitPart μ + K ≤ limitPart μ + finitePart μ :=
          add_le_add (le_refl _) ((Nat.cast_le (α := Ordinal.{0})).mpr (not_lt.mp h))
      _ = μ := decomposition μ

end Value

namespace ExtOrd

theorem exists_nat_of_mem_band {α : Ordinal.{0}} {x : ExtOrd} (hle : ofOrd α ≤ x)
    (hlt : x < ofOrd (α + Ordinal.omega0)) : ∃ k : ℕ, x = ofOrd (α + k) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨μ, rfl⟩
  · exact absurd hle (not_le.mpr (bot_lt_ofOrd α))
  · exact absurd hlt (not_lt.mpr le_top)
  · obtain ⟨k, hk⟩ := Value.exists_nat_of_lt_add_omega (ofOrd_le_ofOrd.mp hle)
      (ofOrd_lt_ofOrd.mp hlt)
    exact ⟨k, by rw [hk]⟩

end ExtOrd

namespace StageType

variable {α β : Ordinal.{0}} {n : ℕ}

/-- **Orderliness pins the band of an `∞`-cell**: a label `≥ α` (`α` a limit) at a cell of
grade `K` is `≥ α + K` (self-visibility at `K` means finite part `≥ K`). -/
theorem label_ge_add_grade (hα : Order.IsSuccLimit α) {q : S β n} (Θ : Cell q.scheme.scheme)
    (hge : ofOrd α ≤ q.label Θ) :
    ofOrd (α + q.scheme.scheme.grade Θ) ≤ q.label Θ := by
  have hord : q.label Θ = extVisibilityReplace (q.label Θ) (q.scheme.scheme.grade Θ)
      (q.scheme.scheme.grade Θ) := q.respects.orderly Θ
  rcases ExtOrd.cases (q.label Θ) with hb | ht | ⟨μ, hμ⟩
  · rw [hb] at hge
    exact absurd hge (not_le.mpr (bot_lt_ofOrd α))
  · rw [ht]
    exact le_top
  · rw [hμ] at hord hge ⊢
    rw [extVisibilityReplace_ofOrd, ofOrd_inj] at hord
    have hK := (visibilityReplace_self_iff μ _).mp hord.symm
    rw [ofOrd_le_ofOrd] at hge ⊢
    calc α + (q.scheme.scheme.grade Θ : Ordinal.{0}) ≤ limitPart μ + finitePart μ :=
          add_le_add (succLimit_le_limitPart hα hge) ((Nat.cast_le (α := Ordinal.{0})).mpr hK)
      _ = μ := decomposition μ

/-- The top witness: a full-scope `∞`-cell of grade `K^q` above any `∞`-cell. -/
theorem exists_top_witness {q : S β n} {Xi : Cell q.scheme.scheme} (htop : q.label Xi = ⊤) :
    ∃ Θ : Cell q.scheme.scheme, GradedLe (q.scheme.scheme.cell Xi) (q.scheme.scheme.cell Θ) ∧
      q.scheme.scheme.scope Θ = Finset.univ ∧ q.scheme.scheme.grade Θ = q.topGrade ∧
      q.label Θ = ⊤ := by
  have hmem := grade_mem_topGrades htop
  have hbdd := q.topGrades_bddAbove
  obtain ⟨Θ, hsc, hgr, hΘtop⟩ : q.topGrade ∈ q.topGrades := Nat.sSup_mem ⟨_, hmem⟩ hbdd
  refine ⟨Θ, ⟨?_, ?_⟩, hsc, hgr, hΘtop⟩
  · change q.scheme.scheme.scope Xi ⊆ q.scheme.scheme.scope Θ
    rw [hsc]
    exact Finset.subset_univ _
  · change q.scheme.scheme.grade Xi ≤ q.scheme.scheme.grade Θ
    rw [hgr]
    exact le_csSup hbdd hmem

/-- Any `∞`-cell has grade `≤ K^q`. -/
theorem grade_le_topGrade_of_top {q : S β n} {Xi : Cell q.scheme.scheme}
    (htop : q.label Xi = ⊤) : q.scheme.scheme.grade Xi ≤ q.topGrade :=
  le_csSup q.topGrades_bddAbove (grade_mem_topGrades htop)

/-! ### Reading the transform of the labelling at a top cell -/

/-- The locality data of the labelling of `q` at `Θ` (Def. 2.5.4(1)), spelled out. -/
theorem locality_label_data (q : S β n) (Θ : Cell q.scheme.scheme) :
    ∃ (g : ℕ → ExtOrd) (σ : ExtOrd → ExtOrd),
      (∀ n m : ℕ, n < m → g m ≤ g n) ∧ σ ⊥ = ⊥ ∧ Monotone σ ∧
      (∀ (a : ExtOrd) (k : ℕ), σ a ≤ g k → ∀ i : ℕ, i ≤ k →
        σ (extVisibilityReplace a k i) = extVisibilityReplace (σ a) k i) ∧
      (∀ d : q.scheme.scheme.below (q.scheme.scheme.cell Θ),
        min (q.label d.1) (q.label Θ) =
          min (σ (q.scheme.rows.E Θ d)) (g (q.scheme.scheme.grade d.1))) ∧
      q.label Θ ≤ g (q.scheme.scheme.grade Θ) := by
  obtain ⟨g, σ, hganti, -, hσbot, hσmono, hσ5, hloc⟩ := q.respects.locality Θ
  refine ⟨g, σ, hganti, hσbot, hσmono, hσ5, fun d => hloc d, ?_⟩
  have h : min (q.label Θ) (q.label Θ) =
      min (σ (q.scheme.rows.E Θ ⟨Θ, GradedLe.refl _⟩)) (g (q.scheme.scheme.grade Θ)) :=
    hloc ⟨Θ, GradedLe.refl _⟩
  rw [min_self] at h
  rw [h]
  exact min_le_right _ _

theorem g_le_of_le {g : ℕ → ExtOrd} (hganti : ∀ n m : ℕ, n < m → g m ≤ g n) {k K : ℕ}
    (h : k ≤ K) : g K ≤ g k := by
  rcases h.lt_or_eq with hlt | heq
  · exact hganti _ _ hlt
  · rw [heq]

/-- **Pinning**: below a top cell, the transform reproduces every label strictly below the
label of the top cell: `σ (E(Θ)(d)) = q(d) ≤ g (grade Θ)`. -/
theorem sigma_eq_of_lt_label {q : S β n} {Θ : Cell q.scheme.scheme} {g : ℕ → ExtOrd}
    {σ : ExtOrd → ExtOrd} (hganti : ∀ n m : ℕ, n < m → g m ≤ g n)
    (hΘg : q.label Θ ≤ g (q.scheme.scheme.grade Θ))
    {d : q.scheme.scheme.below (q.scheme.scheme.cell Θ)}
    (hd : min (q.label d.1) (q.label Θ) =
      min (σ (q.scheme.rows.E Θ d)) (g (q.scheme.scheme.grade d.1)))
    (hlt : q.label d.1 < q.label Θ) :
    σ (q.scheme.rows.E Θ d) = q.label d.1 ∧
      σ (q.scheme.rows.E Θ d) ≤ g (q.scheme.scheme.grade Θ) := by
  have hgd : g (q.scheme.scheme.grade Θ) ≤ g (q.scheme.scheme.grade d.1) :=
    g_le_of_le hganti d.2.2
  rw [min_eq_left hlt.le] at hd
  rcases le_total (σ (q.scheme.rows.E Θ d)) (g (q.scheme.scheme.grade d.1)) with hle | hle
  · rw [min_eq_left hle] at hd
    refine ⟨hd.symm, ?_⟩
    rw [← hd]
    exact hlt.le.trans hΘg
  · rw [min_eq_right hle] at hd
    exact absurd (lt_of_lt_of_le hlt (hΘg.trans hgd)) (not_lt.mpr hd.ge)

/-! ### The band case -/

/-- **Lemma 5.5.2, band case**: if `N(Ξ) = α + i` with `i < K^q` (top grade of the reduct),
then the reduct's provisional value at `Ξ` is `α + i`. -/
theorem isProvisionalValue_band_of_expansion (hα : Order.IsSuccLimit α) (hαβ : α ≤ β)
    {q : S β n} (Xi : Cell q.scheme.scheme) {i : ℕ} (hXi : q.label Xi = ofOrd (α + i))
    (hK : i < (reduceType hα hαβ q).topGrade) :
    (reduceType hα hαβ q).IsProvisionalValue Xi (ofOrd (α + i)) := by
  set p := reduceType hα hαβ q with hp
  have hαi : ofOrd α ≤ ofOrd (α + i) := ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)
  have hptop : p.label Xi = ⊤ := by
    change truncExt α (q.label Xi) = ⊤
    rw [hXi]
    exact truncExt_eq_top_of_ge hαi
  -- every `p`-`∞` cell has `q`-label `≥ α`; a full-scope grade-`K` one has `q`-label `≥ α + K`
  have hge : ∀ Θ : Cell q.scheme.scheme, p.label Θ = ⊤ → ofOrd α ≤ q.label Θ := fun Θ h =>
    truncExt_eq_top_iff.mp h
  have hgeK : ∀ Θ : Cell q.scheme.scheme, q.scheme.scheme.grade Θ = p.topGrade → p.label Θ = ⊤ →
      ofOrd (α + p.topGrade) ≤ q.label Θ := fun Θ hgr h => by
    have := label_ge_add_grade hα (q := q) Θ (hge Θ h)
    rwa [hgr] at this
  have hiK : ofOrd (α + i) < ofOrd (α + p.topGrade) :=
    ofOrd_lt_ofOrd.mpr ((add_lt_add_iff_left α).mpr (Nat.cast_lt.mpr hK))
  -- no cap
  have hncap : ¬ p.ProvisionalCap Xi := by
    rintro ⟨Θ, hXiΘ, Sg, hsc, hgr, hΘtop, hSgtop, hle⟩
    have hgr' : q.scheme.scheme.grade Θ = p.topGrade := hgr
    obtain ⟨g, σ, hganti, hσbot, hσmono, hσ5, hloc, hΘg⟩ := locality_label_data q Θ
    have hΘK : ofOrd (α + p.topGrade) ≤ q.label Θ := hgeK Θ hgr' hΘtop
    have hΘg' : q.label Θ ≤ g p.topGrade := by rw [← hgr']; exact hΘg
    -- at Ξ
    obtain ⟨hσa, hσaK⟩ := sigma_eq_of_lt_label hganti hΘg (hloc ⟨Xi, hXiΘ⟩)
      (by rw [hXi]; exact lt_of_lt_of_le hiK hΘK)
    rw [hgr'] at hσaK
    set a := q.scheme.rows.E Θ ⟨Xi, hXiΘ⟩ with ha
    set u := q.scheme.rows.E Θ Sg with hu
    rw [hXi] at hσa
    -- at Σ: `σ u ≥ α`
    have hu_le_a : u ≤ a := (le_extVisibilityReplace_self u p.topGrade).trans hle
    have hσu_le : σ u ≤ ofOrd (α + i) := hσa ▸ hσmono hu_le_a
    have hσuK : σ u ≤ g p.topGrade := hσu_le.trans (hσa ▸ hσaK)
    have hσu_ge : ofOrd α ≤ σ u := by
      have hd := hloc Sg
      have hSgα : ofOrd α ≤ q.label Sg.1 := hge Sg.1 hSgtop
      have hΘα : ofOrd α ≤ q.label Θ := hαi.trans (hiK.le.trans hΘK)
      have hlhs : ofOrd α ≤ min (q.label Sg.1) (q.label Θ) := le_min hSgα hΘα
      rw [hd] at hlhs
      have hgS : σ u ≤ g (q.scheme.scheme.grade Sg.1) :=
        hσuK.trans (g_le_of_le hganti (by rw [← hgr']; exact Sg.2.2))
      rw [min_eq_left hgS] at hlhs
      exact hlhs
    -- clause 5 at `(u, p.topGrade, p.topGrade)`: `σ (u ⊔⁺_K p.topGrade) ≥ α + p.topGrade`
    have h5 := hσ5 u p.topGrade hσuK p.topGrade le_rfl
    rcases ExtOrd.cases (σ u) with hb | ht | ⟨μ, hμ⟩
    · rw [hb] at hσu_ge
      exact absurd hσu_ge (not_le.mpr (bot_lt_ofOrd α))
    · rw [ht] at hσu_le
      exact absurd hσu_le (not_le.mpr (ofOrd_lt_top _))
    · rw [hμ] at h5 hσu_ge
      rw [extVisibilityReplace_ofOrd] at h5
      have hαμ : α ≤ μ := ofOrd_le_ofOrd.mp hσu_ge
      have hbig : ofOrd (α + p.topGrade) ≤ σ (extVisibilityReplace u p.topGrade p.topGrade) := by
        rw [h5, ofOrd_le_ofOrd]
        calc α + (p.topGrade : Ordinal.{0}) ≤ limitPart μ + p.topGrade :=
              add_le_add (succLimit_le_limitPart hα hαμ) le_rfl
          _ ≤ visibilityReplace μ p.topGrade p.topGrade := limitPart_add_le_visibilityReplace
              μ p.topGrade
      have hsmall : σ (extVisibilityReplace u p.topGrade p.topGrade) ≤ ofOrd (α + i) := hσa ▸
          hσmono hle
      exact absurd (hbig.trans hsmall) (not_le.mpr hiK)
  -- band witness
  obtain ⟨Θ, hXiΘ, hsc, hgr, hΘtop⟩ := exists_top_witness hptop
  have hgr' : q.scheme.scheme.grade Θ = p.topGrade := hgr
  obtain ⟨g, σ, hganti, hσbot, hσmono, hσ5, hloc, hΘg⟩ := locality_label_data q Θ
  have hΘK : ofOrd (α + p.topGrade) ≤ q.label Θ := hgeK Θ hgr' hΘtop
  obtain ⟨hσa, hσaK⟩ := sigma_eq_of_lt_label hganti hΘg (hloc ⟨Xi, hXiΘ⟩)
    (by rw [hXi]; exact lt_of_lt_of_le hiK hΘK)
  rw [hgr'] at hσaK
  set a := q.scheme.rows.E Θ ⟨Xi, hXiΘ⟩ with ha
  rw [hXi] at hσa
  -- `a` is an ordinal with finite part `< p.topGrade` (else the cap fires at `Σ := Ξ`)
  have hcapXi : ¬ extVisibilityReplace a p.topGrade p.topGrade ≤ a := fun h =>
    hncap ⟨Θ, hXiΘ, ⟨Xi, hXiΘ⟩, hsc, hgr, hΘtop, hptop, h⟩
  rcases ExtOrd.cases a with hb | ht | ⟨ν, hν⟩
  · rw [hb, hσbot] at hσa
    exact absurd hσa.symm (ofOrd_ne_bot _)
  · rw [ht] at hcapXi
    exact (hcapXi (by simp)).elim
  · rw [hν] at hcapXi hσa hσaK
    have hfp : finitePart ν < p.topGrade := by
      by_contra hge'
      rw [extVisibilityReplace_ofOrd,
        (visibilityReplace_self_iff ν p.topGrade).mpr (not_lt.mp hge')] at hcapXi
      exact hcapXi le_rfl
    have hfpαi : finitePart (α + i) < p.topGrade := by
      rw [finitePart_succLimit_add_nat hα]
      exact hK
    -- clause 5 at `(a, K, fp ν)` reads the band index
    have h5 := hσ5 (ofOrd ν) p.topGrade hσaK (finitePart ν) (le_of_lt hfp)
    rw [hσa, extVisibilityReplace_ofOrd, extVisibilityReplace_ofOrd,
      visibilityReplace_of_finitePart_lt hfp, decomposition ν, hσa,
      visibilityReplace_of_finitePart_lt hfpαi, limitPart_succLimit_add_nat hα, ofOrd_inj] at h5
    have hi : (i : Ordinal.{0}) = finitePart ν := add_left_cancel h5
    have hi' : i = finitePart ν := by exact_mod_cast hi
    refine Or.inr (Or.inr ⟨hptop, hncap, i, ⟨Θ, hXiΘ, hsc, hgr, hΘtop, ?_⟩, rfl⟩)
    change a = extVisibilityReplace a p.topGrade i
    rw [hν, extVisibilityReplace_ofOrd, hi', visibilityReplace_of_finitePart_lt hfp,
      decomposition]

end StageType

end VaughtConjecture.Knight
