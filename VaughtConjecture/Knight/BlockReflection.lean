/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReductModel
public import VaughtConjecture.Knight.ExpansionUniqueness

/-! # Old-block requests reflect through reduction; the next block

Reduction to the source stage fixes every proper label and sends every label at or above the
source stage to `∞` (`truncExt`).  Consequently membership in each of the four old-block
request families — a generalized-saturation domain, a prescribed `−∞`-pattern, an old
uniformity band, an old high-grade threshold — **reflects** from the reduct to the type
(`mem_*_of_reduceType_mem`): a target label whose reduct witnesses the request witnesses it
itself.  This is what lets a next-block realization discharge the four old model clauses by
exhibiting source witnesses (its reduct being literally the source).

In the block `[α, α + ω)` itself, the only new non-successor uniformity index is `α`
(`nonSuccessor_lt_add_omega_old_or_base`), and the natural ladder `α + (k+1)` is cofinal
among the new high-grade thresholds (`lt_add_nat_succ_of_lt_add_omega`).

`LimitStage.nextBlock` packages `α + ω` as a limit stage.  (Reviewer kernels, 2026-08-30.) -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe w

/-- The next `ω`-block of a limit stage. -/
noncomputable def LimitStage.nextBlock (α : LimitStage) : LimitStage :=
  ⟨α.1 + Ordinal.omega0, Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0⟩

theorem LimitStage.le_nextBlock (α : LimitStage) : α ≤ α.nextBlock :=
  show α.1 ≤ α.1 + Ordinal.omega0 from le_add_of_nonneg_right zero_le

/-- Every ordinal below the next `ω`-block is below a member of the natural ladder. -/
theorem lt_add_nat_succ_of_lt_add_omega {α γ : Ordinal.{0}}
    (hγ : γ < α + Ordinal.omega0) : ∃ k : ℕ, γ < α + (k + 1) := by
  by_cases h : γ < α
  · exact ⟨0, h.trans_le (le_add_right (le_refl α))⟩
  · have hle : α ≤ γ := not_lt.mp h
    obtain ⟨k, rfl⟩ := exists_nat_of_lt_add_omega hle hγ
    refine ⟨k, (add_lt_add_iff_left α).mpr ?_⟩
    exact_mod_cast Nat.lt_succ_self k

/-- In the new `ω`-block above a limit `α`, `α` itself is the only new non-successor
index. -/
theorem nonSuccessor_lt_add_omega_old_or_base {α γ : Ordinal.{0}}
    (hns : IsNonSuccessor γ) (hγ : γ < α + Ordinal.omega0) : γ < α ∨ γ = α := by
  by_cases h : γ < α
  · exact Or.inl h
  · have hle : α ≤ γ := not_lt.mp h
    obtain ⟨k, hk⟩ := exists_nat_of_lt_add_omega hle hγ
    cases k with
    | zero =>
        right
        simpa using hk
    | succ k =>
        exfalso
        have hpre : Order.IsSuccPrelimit γ := isNonSuccessor_iff_isSuccPrelimit.mp hns
        rw [Nat.cast_add_one, ← add_assoc, ← Order.succ_eq_add_one] at hk
        rw [hk] at hpre
        exact Order.not_isSuccPrelimit_succ _ hpre

/-- The bottom-pattern family depends only on the `⊥`-pattern of the prescribed
labelling. -/
theorem bottomPatternFamily_congr {γ : Ordinal.{0}} {n : ℕ} {D : SemScheme (n + 1)}
    {row row' : Cell D.scheme → ExtOrd}
    (h : ∀ Θ : D.scheme.below (Finset.univ, n), row Θ.1 = ⊥ ↔ row' Θ.1 = ⊥) :
    BottomPatternFamily (α := γ) D row = BottomPatternFamily D row' := by
  ext q
  constructor
  · rintro ⟨hs, hp⟩; exact ⟨hs, fun Θ => (hp Θ).trans (h Θ)⟩
  · rintro ⟨hs, hp⟩; exact ⟨hs, fun Θ => (hp Θ).trans (h Θ).symm⟩

namespace Value

/-- If a truncation is still proper, truncation did nothing. -/
theorem truncExt_eq_self_of_lt {α : Ordinal.{0}} {x : ExtOrd}
    (h : truncExt α x < ofOrd α) : truncExt α x = x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · rfl
  · exact absurd h (not_lt.mpr le_top)
  · rcases lt_or_ge β α with hβ | hβ
    · exact truncExt_ofOrd_of_lt hβ
    · rw [truncExt_ofOrd_of_le hβ] at h
      exact absurd h (not_lt.mpr le_top)

/-- A proper lower bound visible after truncation was already a lower bound before it. -/
theorem lt_of_lt_truncExt {α γ : Ordinal.{0}} {x : ExtOrd}
    (hγ : γ < α) (h : ofOrd γ < truncExt α x) : ofOrd γ < x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · rw [truncExt_bot] at h
    exact absurd h (not_lt.mpr bot_le)
  · exact ofOrd_lt_top γ
  · rcases lt_or_ge β α with hβ | hβ
    · rwa [truncExt_ofOrd_of_lt hβ] at h
    · exact ofOrd_lt_ofOrd.mpr (hγ.trans_le hβ)

end Value

namespace StageType

variable {α β : Ordinal.{0}} {n : ℕ}

/-- Domain membership lifts because reduction never changes the scheme. -/
theorem mem_genSatFamily_of_reduceType_mem (hα : Order.IsSuccLimit α)
    (h : α ≤ β) {q : S β (n + 1)} {D : SemScheme (n + 1)}
    (hq : reduceType hα h q ∈ GenSatFamily D) : q ∈ GenSatFamily D := hq

/-- The prescribed bottom pattern lifts: truncation preserves and reflects bottom. -/
theorem mem_bottomPatternFamily_of_reduceType_mem (hα : Order.IsSuccLimit α)
    (h : α ≤ β) {q : S β (n + 1)} {D : SemScheme (n + 1)}
    {row : Cell D.scheme → ExtOrd}
    (hq : reduceType hα h q ∈ BottomPatternFamily D row) :
    q ∈ BottomPatternFamily D row := by
  rcases hq with ⟨hscheme, hpattern⟩
  refine ⟨hscheme, fun Θ => ?_⟩
  have hΘ := hpattern Θ
  change truncExt α (q.label (SemScheme.castCell hscheme.symm Θ.1)) = ⊥ ↔ row Θ.1 = ⊥ at hΘ
  rwa [truncExt_eq_bot_iff] at hΘ

/-- Every old uniformity-band witness lifts through reduction: the whole old band is below
the source stage, so its witnessing label could not have truncated. -/
theorem mem_uniformityFamily_of_reduceType_mem (hα : Order.IsSuccLimit α)
    (h : α ≤ β) {q : S β (n + 1)} {γ : Ordinal.{0}} (hγ : γ < α)
    (hq : reduceType hα h q ∈ UniformityFamily γ) : q ∈ UniformityFamily γ := by
  rcases hq with ⟨Sig, hlo, hhi⟩
  have htrunc : truncExt α (q.label Sig) < ofOrd α :=
    hhi.trans_le (ofOrd_le_ofOrd.mpr (add_omega0_le_of_lt_isSuccLimit hα hγ))
  have heq := Value.truncExt_eq_self_of_lt htrunc
  exact ⟨Sig, heq ▸ hlo, heq ▸ hhi⟩

/-- Every old high-grade witness lifts through reduction. -/
theorem mem_highGradeDominanceFamily_of_reduceType_mem
    (hα : Order.IsSuccLimit α) (h : α ≤ β)
    {q : S β (n + 1)} {γ : Ordinal.{0}} (hγ : γ < α)
    (hq : reduceType hα h q ∈ HighGradeDominanceFamily γ) :
    q ∈ HighGradeDominanceFamily γ := by
  rcases hq with ⟨Sig, hgrade, hlab⟩
  exact ⟨Sig, hgrade, Value.lt_of_lt_truncExt hγ hlab⟩

end StageType

end VaughtConjecture.Knight
