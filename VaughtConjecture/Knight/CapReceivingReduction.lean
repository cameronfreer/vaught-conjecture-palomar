/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteCoverReceivingCore

/-! # Direct reduction and cofinal reflection of finite-cut receiving

Reduction repairs the donor to the actual upper root using only its finite
bountifulness. Reflection needs a reduct above the observation cutoff, not above
all donor labels. Neither proof assumes old modelhood or invokes its reduction
theorem. Structural consistency and covering transfer separately.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FiniteCutReceiving
open TypeTower StageType KnightRealization Value ExtOrd FiniteCoverReceiving
universe w
variable {M : Type w} {α β : LimitStage}

private theorem label_cast {δ : Ordinal.{0}} {n : ℕ} {p q : S δ n}
    (h : p = q) (d : Cell p.scheme.scheme) :
    q.label (SemScheme.castCell (congrArg StageType.scheme h) d) = p.label d := by
  cases h
  rfl

private theorem coface_read {δ : Ordinal.{0}} {n : ℕ}
    {p : S δ n} {q : S δ (n + 1)} (h : IsCoface p q)
    (d : Cell p.scheme.scheme) : q.label (h.extendsDomain.cellOf d) = p.label d := by
  have hp : q.restrictFace Fin.castSuccEmb h.extendsDomain.visible = p :=
    Option.some.inj ((typeMap_eq_some _ q h.extendsDomain.visible).symm.trans h)
  rw [← label_cast hp.symm d]
  rfl

/-- The actual upper root is restored before receiving; lower caps need not be lawful. -/
theorem reduct {R : KnightRealization β M} (hFC : FiniteCutReceiving R) (hαβ : α ≤ β) :
    FiniteCutReceiving (R.reduct hαβ) := by
  intro n t p hp q hqp δ hδ hδα
  obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨ν, rfl, hν⟩ : ∃ ν : Ordinal.{0}, δ = ofOrd ν ∧ ν < α.1 := by
    rcases ExtOrd.cases δ with rfl | rfl | ⟨ν, rfl⟩
    · exact False.elim (lt_irrefl _ hδ)
    · exact False.elim ((not_lt_of_ge le_top) hδα)
    · exact ⟨ν, rfl, ofOrd_lt_ofOrd.mp hδα⟩
  let γ := ofOrd (ν + (n + 1 : ℕ))
  have hγα : γ < ofOrd α.1 := ofOrd_lt_ofOrd.mpr (add_nat_lt_limitStage hν _)
  have hγβ : γ < ofOrd β.1 := hγα.trans_le (ofOrd_le_ofOrd.mpr hαβ)
  have hδγ : ofOrd ν ≤ γ := ofOrd_le_ofOrd.mpr (le_add_nat ν _)
  have hD : ExtendsDomain P q.scheme :=
    ⟨hqp.extendsDomain.visible, hqp.extendsDomain.restrict⟩
  have hag : ∀ d, min (q.label (hD.cellOf d)) γ = min (P.label d) γ := by
    intro d
    have hd := coface_read hqp d
    change q.label (hD.cellOf d) = truncExt α.1 (P.label d) at hd
    rw [hd, min_truncExt_of_lt hγα]
  obtain ⟨⟨Ds, labels, bounds, lawful⟩, hDs, hup, hcap⟩ :=
    exists_stage_extends_capped hD q.respects (selfVis_ofOrd_add_nat ν (n + 1)) hγβ hag
  dsimp only at hDs
  subst Ds
  let u : S β.1 (n + 1) := ⟨q.scheme, labels, bounds, lawful⟩
  obtain ⟨y, hy, s, hs, he, hscap⟩ := hFC t P hP u hup γ (bot_lt_ofOrd _) hγβ
  refine ⟨y, hy, reduceType α.2 hαβ s,
    congrArg (Option.map (reduceType α.2 hαβ)) hs, he, ?_⟩
  intro d
  change min (truncExt α.1 (s.label d)) (ofOrd ν) = _
  rw [min_truncExt_of_lt (ofOrd_lt_ofOrd.mpr hν)]
  apply GradeTailRestoration.cap_below (M := γ) _ hδγ
  rw [hscap d]
  exact hcap (SemScheme.castCell he d)

/-- Reflection from sufficiently high literal reducts, without stabilizing donor labels. -/
theorem of_cofinal_reducts {R : KnightRealization α M}
    (hcof : ∀ ν : Ordinal.{0}, ν < α.1 →
      ∃ (β : LimitStage) (hβα : β ≤ α), ν < β.1 ∧ FiniteCutReceiving (R.reduct hβα)) :
    FiniteCutReceiving R := by
  intro n t p hp q hqp δ hδ hδα
  obtain ⟨ν, rfl, hν⟩ : ∃ ν : Ordinal.{0}, δ = ofOrd ν ∧ ν < α.1 := by
    rcases ExtOrd.cases δ with rfl | rfl | ⟨ν, rfl⟩
    · exact False.elim (lt_irrefl _ hδ)
    · exact False.elim ((not_lt_of_ge le_top) hδα)
    · exact ⟨ν, rfl, ofOrd_lt_ofOrd.mp hδα⟩
  obtain ⟨β, hβα, hνβ, hFC⟩ := hcof ν hν
  have hpβ : (R.reduct hβα).eval t = some (reduceType β.2 hβα p) :=
    congrArg (Option.map (reduceType β.2 hβα)) hp
  have hqβ : IsCoface (reduceType β.2 hβα p) (reduceType β.2 hβα q) :=
    (typeMap_reduceType_comm β.2 hβα Fin.castSuccEmb q).trans
      (congrArg (Option.map (reduceType β.2 hβα)) hqp)
  obtain ⟨y, hy, s, hs, he, hcap⟩ := hFC t _ hpβ _ hqβ (ofOrd ν)
    (bot_lt_ofOrd _) (ofOrd_lt_ofOrd.mpr hνβ)
  obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hs
  change s'.scheme = q.scheme at he
  refine ⟨y, hy, s', hs', he, ?_⟩
  intro d
  have hc := hcap d
  change min (truncExt β.1 (s'.label d)) (ofOrd ν) =
    min (truncExt β.1 (q.label (SemScheme.castCell he d))) (ofOrd ν) at hc
  exact (min_truncExt_eq_iff (ofOrd_le_ofOrd.mpr hνβ.le)).mp hc

end VaughtConjecture.Knight.FiniteCutReceiving
