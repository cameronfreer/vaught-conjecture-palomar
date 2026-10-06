/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthStableTemplate
public import VaughtConjecture.Knight.GrowthStableCarrierReceiving
public import VaughtConjecture.Knight.AnchorStable

/-! # Positive-root stable receiving before its modelhood applications

Non-hollowness supplies an attained proper stable marker. The constructed
calibration and native template feed the positive-cap physical receiver over
the actual private context. Its independently lawful stable labels satisfy
correctness; modelhood of the stable candidate is not assumed.

The two conclusions remain distinct: non-top donor values are exact, while
donor tops read above the requested threshold. Cap receiving and selected
occurrence supplies are downstream applications, not imports of this producer.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.NonHollowGrowthReceiving
open TypeTower StageType KnightRealization Value ExtOrd
noncomputable section
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}

/-- Stable receiving over a positive root, with no supplied calibration,
template, admission or physical-correctness hypothesis. -/
theorem receives_positive (hM : W.IsModel) (hh : ¬ W.IsHollow)
    (hg : W.HasTopGradeGrowth) {n : ℕ} (hn : 0 < n)
    (t : Fin n ↪ M) (p : S α.1 n) (hp : W.eval t = some p)
    (q : S α.nextBlock.1 (n + 1)) (hq : IsCoface (stableLiftType hM t p hp) q)
    (γ : Ordinal.{0}) (hγ : γ < α.nextBlock.1) :
    ∃ (y : M) (hy : y ∉ Set.range t) (s : S α.1 (n + 1)),
      W.eval (snoc t y hy) = some s ∧ ∃ he : q.scheme = s.scheme,
        (∀ d, q.label d ≠ ⊤ →
          W.stableValue (snoc t y hy) s (SemScheme.castCell he d) = q.label d) ∧
        (∀ d, q.label d = ⊤ →
          ofOrd γ < W.stableValue (snoc t y hy) s (SemScheme.castCell he d)) := by
  have ha : W.HasInfinityAnchor := Classical.not_not.mp hh
  obtain ⟨k, a, p₀, ha₀, d₀, i, hd₀, hstable⟩ :=
    (hasInfinityAnchor_iff_exists_finite_stable hM).mp ha
  obtain ⟨J, u, C, hC, f, hfu, _, hvP, hP, hvC, hF, X, _, hsmall,
    _, _, ⟨T⟩, hclass, _, hread⟩ :=
    GrowthStableTemplate.exists_input hM hg ha₀ d₀ hd₀ hstable hn hp q hq γ hγ
  have hin : InClass X.ZA C.label := by
    intro d
    rw [hclass]
    rfl
  obtain ⟨y, _, hyRoot, s, hev, he, hc⟩ :=
    GrowthStableCarrierReceiving.exists_correct_donor C q.scheme p.scheme f
      hvC hvP hF hP X T hsmall hM hC hin
  have hy : y ∉ Set.range t := by rwa [hfu] at hyRoot
  have htup : snoc (f.trans u) y hyRoot = snoc t y hy := by
    cases hfu
    rfl
  rw [htup] at hev hc
  exact ⟨y, hy, s, hev, he.symm, hread _ hc⟩

end
end VaughtConjecture.Knight.NonHollowGrowthReceiving
