/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProvisionalRatchet
public import VaughtConjecture.Knight.TopGradeDichotomy

/-! # Structural stable-spectrum bounds and characteristic-to-tail implication

These proofs use exact parent consistency and initial-segment covering. In particular,
`IsCharacteristicArity.isCoinitial_topGrade` does not invoke the converse or proper-label
cofinality. The zero-grade converse remains in `TopGradeStableSpectrum`.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe w

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-- A full-scope `∞`-cell of grade `K^p` has provisional value `α + K^p`. -/
theorem isProvisionalValue_top_of_topCell {p : S α n} {Θ : Cell p.scheme.scheme}
    (hsc : p.scheme.scheme.scope Θ = Finset.univ) (hgr : p.scheme.scheme.grade Θ = p.topGrade)
    (htop : p.label Θ = ⊤) : p.IsProvisionalValue Θ (ofOrd (α + p.topGrade)) := by
  refine Or.inr (Or.inl ⟨htop, ⟨Θ, GradedLe.refl _, ⟨Θ, GradedLe.refl _⟩, hsc, hgr, htop, htop,
    ?_⟩, rfl⟩)
  have h := p.scheme.rows.orderly Θ ⟨Θ, GradedLe.refl _⟩
  change p.scheme.rows.E Θ ⟨Θ, GradedLe.refl _⟩ = extVisibilityReplace
    (p.scheme.rows.E Θ ⟨Θ, GradedLe.refl _⟩) (p.scheme.scheme.grade Θ) (p.scheme.scheme.grade Θ)
    at h
  rw [hgr] at h
  exact h.symm.le

/-- A positive top grade is attained by a full-scope `∞`-cell. -/
theorem exists_topCell_of_topGrade_pos (p : S α n) (hpos : 0 < p.topGrade) :
    ∃ Θ : Cell p.scheme.scheme, p.scheme.scheme.scope Θ = Finset.univ ∧
      p.scheme.scheme.grade Θ = p.topGrade ∧ p.label Θ = ⊤ := by
  have hne : p.topGrades.Nonempty := by
    by_contra hn
    have hempty : p.topGrades = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have : p.topGrade = 0 := by
      unfold topGrade
      rw [hempty, csSup_empty]
      rfl
    omega
  exact Nat.sSup_mem hne p.topGrades_bddAbove

/-- A top grade `0` means no `∞`-cell at all (grades are positive). -/
theorem label_ne_top_of_topGrade_eq_zero {p : S α n} (h : p.topGrade = 0)
    (Xi : Cell p.scheme.scheme) : p.label Xi ≠ ⊤ := fun htop => by
  have hmem := grade_mem_topGrades htop
  have hle : p.scheme.scheme.grade Xi ≤ p.topGrade := le_csSup p.topGrades_bddAbove hmem
  have hpos := p.scheme.scheme.grade_pos Xi
  omega

end StageType

namespace KnightRealization

open StageType

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-- Every cell has a stable value (classical totality of the graph `HasStableValue`). -/
theorem exists_hasStableValue {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n)
    (Xi : Cell p.scheme.scheme) : ∃ γ, R.HasStableValue t p Xi γ := by
  by_cases h : ∃ δ : ExtOrd, δ < ofOrd (α.1 + Ordinal.omega0) ∧ R.StabilizesTo t p Xi δ
  · obtain ⟨δ, hδ, hs⟩ := h
    exact ⟨δ, Or.inl ⟨hδ, hs⟩⟩
  · push Not at h
    exact ⟨⊤, Or.inr ⟨rfl, h⟩⟩

/-- A cell whose label is not `∞` stabilizes at its label. -/
theorem stabilizesTo_label_of_ne_top (x : R.LabelledExt) {Xi : Cell x.type.scheme.scheme}
    (hne : x.type.label Xi ≠ ⊤) (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) :
    R.StabilizesTo x.tuple x.type Xi (x.type.label Xi) := by
  intro m s
  obtain ⟨y, ⟨f, hf, hpq⟩, g, hg⟩ := exists_labelledExt_le hcons hcov x s
  refine ⟨y.arity, y.tuple, g, f, y.type, hpq, y.eval_eq, hg, hf, Or.inl ⟨?_, ?_⟩⟩
  · rw [label_mapCell hpq Xi]; exact hne
  · rw [label_mapCell hpq Xi]

/-- **The stable value of a top cell is at least `α + K^x`** (ratchet): every member of the
stable set above `x` carries a value `≥ α + K^x`. -/
theorem le_of_hasStableValue_topCell (x : R.LabelledExt) {Θ : Cell x.type.scheme.scheme}
    (hsc : x.type.scheme.scheme.scope Θ = Finset.univ)
    (hgr : x.type.scheme.scheme.grade Θ = x.type.topGrade) (htop : x.type.label Θ = ⊤)
    (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering) {γ : ExtOrd}
    (h : R.HasStableValue x.tuple x.type Θ γ) : ofOrd (α.1 + x.type.topGrade) ≤ γ := by
  rcases h with ⟨-, hs⟩ | ⟨rfl, -⟩
  · have hD := (stabilizesTo_iff_isDominating hcons hcov x Θ γ).mp @hs
    obtain ⟨y, ⟨f, -, hpq, hval⟩, -⟩ := hD x
    rcases provisional_ratchet' hpq Θ (isProvisionalValue_top_of_topCell hsc hgr htop) hval
      with h | h
    · exact h.le
    · exact h
  · exact le_top

/-- **Growth excludes finite characteristic arity**: with cofinally growing top grade, the
stable spectrum contains values above every `α + K`. -/
theorem not_isCharacteristicArity_of_hasTopGradeGrowth (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (hg : R.HasTopGradeGrowth) (K : ℕ) :
    ¬ R.IsCharacteristicArity K := by
  intro hK
  obtain ⟨x₀⟩ := nonempty_labelledExt hcov
  obtain ⟨y, hyK, -⟩ := hg K x₀
  change K < y.type.topGrade at hyK
  obtain ⟨Θ, hsc, hgr, htop⟩ := exists_topCell_of_topGrade_pos y.type (by omega)
  obtain ⟨γ, hγ⟩ := exists_hasStableValue (R := R) y.tuple y.type Θ
  have hmem : γ ∈ R.stableSpectrum := ⟨y.arity, y.tuple, y.type, y.eval_eq, Θ, hγ⟩
  have h1 : ofOrd (α.1 + y.type.topGrade) ≤ γ :=
    le_of_hasStableValue_topCell y hsc hgr htop hcons hcov hγ
  have h2 : γ ≤ ofOrd (α.1 + K) := hK.1 hmem
  have : ofOrd (α.1 + y.type.topGrade) ≤ ofOrd (α.1 + K) := h1.trans h2
  rw [ofOrd_le_ofOrd] at this
  have : (y.type.topGrade : Ordinal.{0}) ≤ K := (add_le_add_iff_left _).mp this
  have : y.type.topGrade ≤ K := by exact_mod_cast this
  omega

/-! ### Stabilization on a tail of constant top grade -/

/-- On a tail where the top grade is constantly `K`, every cell stabilizes, at a value
`≤ α + K`: the ratchet from the tail's base only permits the value `α + K`, and once that value
is reached it persists. -/
theorem exists_stabilizesTo_of_tail_topGrade_const (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x : R.LabelledExt) (Xi : Cell x.type.scheme.scheme)
    {K : ℕ} (z : R.LabelledExt) (hxz : x ≤ z)
    (hz : ∀ w : R.LabelledExt, z ≤ w → w.type.topGrade = K) :
    ∃ γ, γ ≤ ofOrd (α.1 + K) ∧ R.StabilizesTo x.tuple x.type Xi γ := by
  classical
  -- the canonical values along the tail
  have key : ∀ (y : R.LabelledExt) (fy : Fin x.arity ↪ Fin y.arity) (_ : fy.trans y.tuple = x.tuple)
      (hpy : typeMap fy y.type = some x.type) (w : R.LabelledExt) (hyw : y ≤ w),
      ∃ (fw : Fin x.arity ↪ Fin w.arity) (_ : fw.trans w.tuple = x.tuple)
        (hpw : typeMap fw w.type = some x.type),
        w.type.IsProvisionalValue (mapCell hpw Xi)
          (w.type.someProvisionalValue (mapCell hpw Xi)) ∧
        (w.type.someProvisionalValue (mapCell hpw Xi) =
            y.type.someProvisionalValue (mapCell hpy Xi) ∨
          ofOrd (α.1 + y.type.topGrade) ≤ w.type.someProvisionalValue (mapCell hpw Xi)) := by
    intro y fy hfy hpy w hyw
    obtain ⟨g, hg, hpq⟩ := hyw
    have hpw : typeMap (fy.trans g) w.type = some x.type := by
      rw [← typeMap_trans fy g w.type y.type hpq]; exact hpy
    refine ⟨fy.trans g, by rw [Function.Embedding.trans_assoc, hg, hfy], hpw,
      isProvisionalValue_someProvisionalValue _ _, ?_⟩
    have hr := provisional_ratchet' hpq (mapCell hpy Xi)
      (isProvisionalValue_someProvisionalValue y.type (mapCell hpy Xi))
      (by rw [← mapCell_trans hpq hpy hpw Xi]
          exact isProvisionalValue_someProvisionalValue w.type (mapCell hpw Xi))
    rcases hr with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  obtain ⟨fz, hfz, hpz⟩ := hxz
  set v₀ := z.type.someProvisionalValue (mapCell hpz Xi) with hv₀
  have hzK : z.type.topGrade = K := hz z le_rfl
  by_cases hjump : ∃ y : R.LabelledExt, z ≤ y ∧ ∃ (fy : Fin x.arity ↪ Fin y.arity)
      (_ : fy.trans y.tuple = x.tuple) (hpy : typeMap fy y.type = some x.type),
      y.type.someProvisionalValue (mapCell hpy Xi) = ofOrd (α.1 + K)
  · obtain ⟨y, hzy, fy, hfy, hpy, hyK⟩ := hjump
    refine ⟨ofOrd (α.1 + K), le_rfl, ?_⟩
    rw [stabilizesTo_iff_isDominating hcons hcov x Xi]
    intro a
    obtain ⟨w, haw, hyw⟩ := directed_labelledExt hcons hcov a y
    obtain ⟨fw, hfw, hpw, hval, hr⟩ := key y fy hfy hpy w hyw
    have hwK : w.type.topGrade = K := hz w (hzy.trans hyw)
    have hle : w.type.someProvisionalValue (mapCell hpw Xi) ≤ ofOrd (α.1 + K) := by
      have := hval.le; rwa [hwK] at this
    have hyK' : y.type.topGrade = K := hz y hzy
    have heq : w.type.someProvisionalValue (mapCell hpw Xi) = ofOrd (α.1 + K) := by
      rcases hr with h | h
      · rw [h, hyK]
      · rw [hyK'] at h; exact le_antisymm hle h
    exact ⟨w, ⟨fw, hfw, hpw, heq ▸ hval⟩, haw⟩
  · push Not at hjump
    refine ⟨v₀, ?_, ?_⟩
    · have := (isProvisionalValue_someProvisionalValue z.type (mapCell hpz Xi)).le
      rwa [hzK] at this
    rw [stabilizesTo_iff_isDominating hcons hcov x Xi]
    intro a
    obtain ⟨w, haw, hzw⟩ := directed_labelledExt hcons hcov a z
    obtain ⟨fw, hfw, hpw, hval, hr⟩ := key z fz hfz hpz w hzw
    have hwK : w.type.topGrade = K := hz w hzw
    have hne := hjump w hzw fw hfw hpw
    have heq : w.type.someProvisionalValue (mapCell hpw Xi) = v₀ := by
      rcases hr with h | h
      · exact h
      · exfalso
        have hle : w.type.someProvisionalValue (mapCell hpw Xi) ≤ ofOrd (α.1 + K) := by
          have := hval.le; rwa [hwK] at this
        rw [hzK] at h
        exact hne (le_antisymm hle h)
    exact ⟨w, ⟨fw, hfw, hpw, heq ▸ hval⟩, haw⟩

/-- A constant top-grade tail bounds every stable value; no proper-label cofinality is needed. -/
theorem stableSpectrum_bounded_of_isCoinitial_topGrade
    (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering) {K : ℕ}
    (hcoin : IsCoinitial {x : R.LabelledExt | x.type.topGrade = K}) :
    ∀ γ ∈ R.stableSpectrum, γ ≤ ofOrd (α.1 + K) := by
  rintro γ ⟨n, t, p, hpt, Xi, hγ⟩
  let x : R.LabelledExt := ⟨n, t, p, hpt⟩
  obtain ⟨z, hxz, hztail⟩ := hcoin x
  have hz : ∀ w : R.LabelledExt, z ≤ w → w.type.topGrade = K := fun w hw => hztail hw
  obtain ⟨δ, hδK, hδ⟩ := exists_stabilizesTo_of_tail_topGrade_const hcons hcov x Xi z hxz hz
  have hδω : δ < ofOrd (α.1 + Ordinal.omega0) :=
    hδK.trans_lt (ofOrd_lt_ofOrd.mpr ((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 K)))
  rcases hγ with ⟨-, hs⟩ | ⟨rfl, hno⟩
  · have : γ = δ := StabilizesTo.unique hcons hcov hpt @hs @hδ
    rw [this]; exact hδK
  · exact absurd @hδ (hno δ hδω)

/-- Finite characteristic forces a constant top-grade tail using only structural clauses.
The zero-grade converse is deliberately not asserted here. -/
theorem IsCharacteristicArity.isCoinitial_topGrade {K : ℕ}
    (hK : R.IsCharacteristicArity K) (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) :
    IsCoinitial {x : R.LabelledExt | x.type.topGrade = K} := by
  rcases hasTopGradeGrowth_or_coinitial_constant hcons hcov with hg | ⟨L, hL⟩
  · exact False.elim (not_isCharacteristicArity_of_hasTopGradeGrowth hcons hcov hg K hK)
  have hKL : K ≤ L := by
    have hh := hK.2 (stableSpectrum_bounded_of_isCoinitial_topGrade hcons hcov hL)
    have hh' : (K : Ordinal.{0}) ≤ L := (add_le_add_iff_left _).mp (ofOrd_le_ofOrd.mp hh)
    exact_mod_cast hh'
  have hLK : L ≤ K := by
    rcases Nat.eq_zero_or_pos L with rfl | hpos
    · exact Nat.zero_le _
    · obtain ⟨x⟩ := nonempty_labelledExt hcov
      obtain ⟨z, _, hz⟩ := hL x
      have hzL : z.type.topGrade = L := hz (le_refl z)
      obtain ⟨d, hsc, hgr, ht⟩ := exists_topCell_of_topGrade_pos z.type (by omega)
      obtain ⟨γ, hγ⟩ := exists_hasStableValue (R := R) z.tuple z.type d
      have hm : γ ∈ R.stableSpectrum := ⟨z.arity, z.tuple, z.type, z.eval_eq, d, hγ⟩
      have hh := (le_of_hasStableValue_topCell z hsc hgr ht hcons hcov hγ).trans (hK.1 hm)
      rw [hzL] at hh
      have hh' : (L : Ordinal.{0}) ≤ K := (add_le_add_iff_left _).mp (ofOrd_le_ofOrd.mp hh)
      exact_mod_cast hh'
  obtain rfl := le_antisymm hKL hLK
  exact hL

end KnightRealization
end VaughtConjecture.Knight
