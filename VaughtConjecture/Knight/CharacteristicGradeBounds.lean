/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TopGradeStableCore

/-! # Elementary grade bounds at finite characteristic

These bounds use the coinitial top-grade characterization only. Historical
anchor-threshold and profile-code consequences remain in `AnchorThresholdBoundary`,
which reexports these declarations without changing their names or statements.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

/-- A constant tail above every context bounds the top grade of every context. -/
theorem topGrade_le_of_isCoinitial {K : ℕ}
    (hcoin : KnightRealization.IsCoinitial {x : R.LabelledExt | x.type.topGrade = K})
    (x : R.LabelledExt) : x.type.topGrade ≤ K := by
  obtain ⟨y, hxy, hy⟩ := hcoin x
  exact (LabelledExt.topGrade_mono hxy).trans_eq (hy (le_refl y))

/-- Structural characteristic bounds do not use the converse characterization. -/
theorem topGrade_le_of_isCharacteristicArity_of_structural
    (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering) {K : ℕ}
    (hK : R.IsCharacteristicArity K) (x : R.LabelledExt) : x.type.topGrade ≤ K :=
  topGrade_le_of_isCoinitial (hK.isCoinitial_topGrade hcons hcov) x

/-- The corresponding bound on every actual top-labelled occurrence. -/
theorem grade_le_of_label_top_of_isCharacteristicArity_of_structural
    (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering) {K : ℕ}
    (hK : R.IsCharacteristicArity K) {m : ℕ} {s : Fin m ↪ M} {q : S α.1 m}
    (hq : R.eval s = some q) {Θ : Cell q.scheme.scheme} (hΘ : q.label Θ = ⊤) :
    q.scheme.scheme.grade Θ ≤ K :=
  (le_csSup q.topGrades_bddAbove (grade_mem_topGrades hΘ)).trans
    (topGrade_le_of_isCharacteristicArity_of_structural hcons hcov hK ⟨m, s, q, hq⟩)

/-- At finite characteristic arity `K`, every labelled cover has top grade `≤ K`. -/
theorem topGrade_le_of_isCharacteristicArity (hM : R.IsModel) {K : ℕ}
    (hK : R.IsCharacteristicArity K) (x : R.LabelledExt) : x.type.topGrade ≤ K := by
  exact topGrade_le_of_isCharacteristicArity_of_structural hM.consistent hM.covering hK x

/-- **Finite characteristic arity bounds every `⊤`-cell grade**: at characteristic arity `K`,
every `⊤`-labelled cell of every labelled tuple has grade `≤ K` (no full-scope hypothesis:
`grade_mem_topGrades`). -/
theorem grade_le_of_label_top_of_isCharacteristicArity (hM : R.IsModel) {K : ℕ}
    (hK : R.IsCharacteristicArity K) {m : ℕ} {s : Fin m ↪ M} {q : S α.1 m}
    (hq : R.eval s = some q) {Θ : Cell q.scheme.scheme} (hΘ : q.label Θ = ⊤) :
    q.scheme.scheme.grade Θ ≤ K := by
  have h1 : q.scheme.scheme.grade Θ ≤ q.topGrade :=
    le_csSup q.topGrades_bddAbove (grade_mem_topGrades hΘ)
  exact h1.trans (topGrade_le_of_isCharacteristicArity hM hK ⟨m, s, q, hq⟩)

end VaughtConjecture.Knight
