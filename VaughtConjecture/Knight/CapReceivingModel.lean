/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteCoverReceivingCore
public import VaughtConjecture.Knight.CanonicalCoatomFiniteSupply
public import VaughtConjecture.Knight.CoatomFaceLift

/-! # Finite-cut receiving supplies the old model requests

This direction uses the constructed finite coface supplier, not ordinary receiving
in an already established model. The reverse implication remains downstream.
Ordinal zero is a positive extended-ordinal observation cutoff, not bottom; we
never assert that capping a lawful labelling at this cutoff is lawful.
-/

@[expose] public section

namespace VaughtConjecture.Knight
open TypeTower StageType KnightRealization Value ExtOrd
universe w
variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

namespace FiniteCutReceiving

private theorem eq_of_cap_lt {x y δ : ExtOrd}
    (h : min x δ = min y δ) (hy : y < δ) : x = y := by
  rw [min_eq_left hy.le] at h
  rcases le_or_gt x δ with hx | hx
  · rwa [min_eq_left hx] at h
  · rw [min_eq_right hx.le] at h
    exact False.elim (hy.ne h.symm)

/-- The four original clauses, with structural assumptions retained explicitly.
The bottom-pattern source still has no stage bound. -/
theorem isModel (hFC : FiniteCutReceiving R) (hne : Nonempty M)
    (hcons : R.IsExactParentConsistent) (hcover : R.IsInitialSegmentCovering) :
    R.IsModel := by
  refine ⟨hne, hcons, hcover, ?_, ?_, ?_, ?_⟩
  · intro n t p ht D hD
    obtain ⟨q, hqD, hqp⟩ := exists_coface_of_extendsDomain α.2 p D hD
    obtain ⟨y, hy, r, hr, he, _⟩ := hFC t p ht q hqp (ofOrd 0)
      (bot_lt_ofOrd _) (ofOrd_lt_ofOrd.mpr α.2.bot_lt)
    exact ⟨y, hy, r, he.trans hqD, isCoface_of_consistent hcons ht hr, hr⟩
  · intro n t p ht D hD l hl hext
    obtain ⟨q, ⟨hqD, hpat⟩, hqp⟩ := bottomPatternFamily_nonempty α.2 hD l hl hext
    obtain ⟨y, hy, r, hr, he, hcap⟩ := hFC t p ht q hqp (ofOrd 0)
      (bot_lt_ofOrd _) (ofOrd_lt_ofOrd.mpr α.2.bot_lt)
    refine ⟨y, hy, r, ⟨he.trans hqD, ?_⟩, isCoface_of_consistent hcons ht hr, hr⟩
    intro d
    have hc := hcap (SemScheme.castCell (he.trans hqD).symm d.val)
    have hb : r.label (SemScheme.castCell (he.trans hqD).symm d.val) = ⊥ ↔
        q.label (SemScheme.castCell hqD.symm d.val) = ⊥ := by
      have hh := congrArg (fun x : ExtOrd => x = ⊥) hc
      simp only [min_eq_bot, ofOrd_ne_bot, or_false] at hh
      exact Iff.of_eq hh
    exact hb.trans (hpat d)
  · intro n t p ht γ hγ hγα
    obtain ⟨q, ⟨d, hlo, hhi⟩, hqp⟩ :=
      FixedHeight.exists_uniformity_coface (CanonicalCoatomSupply.supply α.2) p γ hγ hγα
    obtain ⟨a, ha⟩ : ∃ a : Ordinal.{0}, q.label d = ofOrd a := by
      rcases ExtOrd.cases (q.label d) with hb | ht | h
      · rw [hb] at hlo
        exact False.elim ((not_le_of_gt (bot_lt_ofOrd γ)) hlo)
      · rw [ht] at hhi
        exact False.elim ((not_lt_of_ge le_top) hhi)
      · exact h
    have haα : a < α.1 := ofOrd_lt_ofOrd.mp
      ((q.label_bound d).resolve_right (by rw [ha]; exact ofOrd_ne_top _) |> fun h => ha ▸ h)
    obtain ⟨y, hy, r, hr, he, hcap⟩ := hFC t p ht q hqp (ofOrd (a + 1))
      (bot_lt_ofOrd _) (ofOrd_lt_ofOrd.mpr (α.2.succ_lt haα))
    have hd : r.label (SemScheme.castCell he.symm d) = q.label d :=
      eq_of_cap_lt (hcap _) (by rw [ha, ofOrd_lt_ofOrd]; exact Order.lt_succ a)
    refine ⟨y, hy, r, ⟨SemScheme.castCell he.symm d, ?_, ?_⟩,
      isCoface_of_consistent hcons ht hr, hr⟩
    · rwa [hd]
    · rwa [hd]
  · intro n t p ht γ hγα
    obtain ⟨q, ⟨d, hgrade, hhigh⟩, hqp⟩ :=
      FixedHeight.exists_highGrade_coface (CanonicalCoatomSupply.supply α.2) p γ hγα
    obtain ⟨y, hy, r, hr, he, hcap⟩ := hFC t p ht q hqp (ofOrd (γ + 1))
      (bot_lt_ofOrd _) (ofOrd_lt_ofOrd.mpr (α.2.succ_lt hγα))
    refine ⟨y, hy, r, ⟨SemScheme.castCell he.symm d, ?_, ?_⟩,
      isCoface_of_consistent hcons ht hr, hr⟩
    · have hgcast : ∀ {X Y : SemScheme (n + 1)} (e : X = Y) (d : Cell X.scheme),
          Y.scheme.grade (SemScheme.castCell e d) = X.scheme.grade d := by
        intro X Y e d
        cases e
        rfl
      exact (hgcast he.symm d).trans hgrade
    · have hc := hcap (SemScheme.castCell he.symm d)
      have hh : ofOrd γ < min (q.label d) (ofOrd (γ + 1)) :=
        lt_min hhigh (ofOrd_lt_ofOrd.mpr (Order.lt_succ γ))
      change min (r.label (SemScheme.castCell he.symm d)) (ofOrd (γ + 1)) =
        min (q.label d) (ofOrd (γ + 1)) at hc
      rw [← hc] at hh
      exact hh.trans_le (min_le_left _ _)

end FiniteCutReceiving
end VaughtConjecture.Knight
