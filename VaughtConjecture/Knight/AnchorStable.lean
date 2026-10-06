/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.StableAnchor
public import VaughtConjecture.Knight.ProvisionalOffset

/-! # Anchors at infinity are exactly the finite stable top values

The reviewer's notes16 §2 (2026-09-19), completing `Knight/StableAnchor.lean`
(`isInfinityAnchor_of_stable`: a finite stable top value is an anchor at threshold `j + 1`)
with the converse and the resulting equivalences.

* **The band forced by an anchor** (`someProvisionalValue_lt_of_anchor`): in a cover whose top
  grade exceeds the threshold `K'`, the strict anchor clause at the cover's full-scope top owner,
  taken against the anchor itself as the top source, gives `E(Θ)(∞̃) < R_{K',K'}(E(Θ)(∞̃))`, so
  the source has finite part `j < K'`; the cap clause fails (the cap inequality at the top grade
  would contradict the strict clause, replacement at a larger grade being larger), and the band
  is at most `j`.  Hence the provisional value is `α + j` with `j < K'`
  (`someProvisionalValue_le_of_anchor` in every cover).
* **Stabilization from a uniform bound** (`exists_stabilizesTo_of_bounded`): if the provisional
  values of a top cell are bounded by `α + K` on every cover, the greatest attained offset
  stabilizes — the ratchet only allows a value to stay or to jump above `α + K^y`, and the
  greatest offset is attained at a cover `y` whose `α + K^y` dominates it.
* **Anchor ⇒ finite stable value** (`exists_stableValue_of_anchor`,
  `stableValue_le_of_anchor`), and the equivalences `hasInfinityAnchor_iff_exists_finite_stable`
  and `isHollow_iff_stable_identity` (hollowness is exactly stable-label fixedness; the forward
  direction is `stableValue_eq_label_of_hollow`).
* **The sharp threshold, under top-grade growth only** (`lt_of_anchor_of_growth`,
  `isLeast_anchor_threshold`): with `HasTopGradeGrowth`, an anchor at `K'` with stable value
  `α + j` has `j < K'`, so `j + 1` is the least threshold.  This is stated separately from the
  equivalence: at finite characteristic arity, thresholds above the characteristic are vacuous
  (`isInfinityAnchor_succ_of_label_top`), and the sharp calculation does not hold there.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd Transform

/-! ## Replacement at a larger grade is larger -/

theorem evr_self_le_evr_self (x : ExtOrd) {k k' : ℕ} (h : k ≤ k') :
    extVisibilityReplace x k k ≤ extVisibilityReplace x k' k' := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot, extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top, extVisibilityReplace_top]
  · by_cases h' : k' ≤ finitePart a
    · rw [extVisibilityReplace_of_le_finitePart h',
        extVisibilityReplace_of_le_finitePart (h.trans h')]
    · have h'' := not_le.mp h'
      rw [extVisibilityReplace_of_finitePart_lt h'']
      by_cases hk : k ≤ finitePart a
      · rw [extVisibilityReplace_of_le_finitePart hk, ofOrd_le_ofOrd]
        conv_lhs => rw [← limitPart_add_finitePart a]
        exact add_le_add_right (Nat.cast_le.mpr h''.le) _
      · rw [extVisibilityReplace_of_finitePart_lt (not_le.mp hk), ofOrd_le_ofOrd]
        exact add_le_add_right (Nat.cast_le.mpr h) _

/-- A value strictly below its own replacement is a proper value with finite part below the
grade. -/
theorem exists_finitePart_lt_of_lt_evr {x : ExtOrd} {k : ℕ}
    (h : x < extVisibilityReplace x k k) : ∃ a : Ordinal.{0}, x = ofOrd a ∧ finitePart a < k := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot] at h; exact absurd h (lt_irrefl _)
  · rw [extVisibilityReplace_top] at h; exact absurd h (lt_irrefl _)
  · refine ⟨a, rfl, ?_⟩
    by_contra hk
    rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hk)] at h
    exact lt_irrefl _ h

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

/-! ## The band forced by an anchor -/

/-- **In a cover whose top grade exceeds the threshold, an anchor reads a band below the
threshold.** -/
theorem someProvisionalValue_lt_of_anchor {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    {Xi : Cell p.scheme.scheme} {K' : ℕ} (h : R.IsInfinityAnchor t p Xi K') {m : ℕ}
    {s : Fin m ↪ M} {f : Fin n ↪ Fin m} {q : S α.1 m} (hfs : f.trans s = t)
    (hq : R.eval s = some q) (hpq : typeMap f q = some p) (hN : K' < q.topGrade) :
    ∃ j < K', q.someProvisionalValue (mapCell hpq Xi) = ofOrd (α.1 + j) := by
  classical
  set Xi' := mapCell hpq Xi with hXi'def
  have htop' : q.label Xi' = ⊤ := by rw [hXi'def, label_mapCell]; exact h.1
  obtain ⟨Θ, hsc, hgr, hΘ⟩ := exists_topCell_of_topGrade_pos q (lt_of_le_of_lt (Nat.zero_le _) hN)
  have hXiΘ : GradedLe (q.scheme.scheme.cell Xi') (q.scheme.scheme.cell Θ) := by
    refine ⟨?_, ?_⟩
    · change q.scheme.scheme.scope Xi' ⊆ q.scheme.scheme.scope Θ
      rw [hsc]; exact Finset.subset_univ _
    · change q.scheme.scheme.grade Xi' ≤ q.scheme.scheme.grade Θ
      rw [hgr]
      exact le_csSup (topGrades_bddAbove q) (grade_mem_topGrades htop')
  -- the strict anchor clause against the anchor itself
  have hstrict := (h.2 s f q hfs hq hpq Θ (by rw [hgr]; exact hN.le) hΘ ⟨Xi', hXiΘ⟩ htop' hXiΘ).2
    (by rw [hgr]; exact hN)
  obtain ⟨a, ha, hfp⟩ := exists_finitePart_lt_of_lt_evr hstrict
  -- the cap clause fails
  have hcap : ¬ q.ProvisionalCap Xi' := by
    rintro ⟨Θ', hXi'', Sig', hsc', hgr', hΘ', hSig', hle⟩
    have hst := (h.2 s f q hfs hq hpq Θ' (by rw [hgr']; exact hN.le) hΘ' Sig' hSig' hXi'').2
      (by rw [hgr']; exact hN)
    have h1 := hst.trans_le (evr_self_le_evr_self _ hN.le)
    exact lt_irrefl _ (h1.trans_le hle)
  -- the band at the finite part
  have hband : q.ProvisionalBand Xi' (finitePart a) := by
    refine ⟨Θ, hXiΘ, hsc, hgr, hΘ, ?_⟩
    rw [ha, extVisibilityReplace_of_finitePart_lt (hfp.trans hN), limitPart_add_finitePart]
  have hex : ∃ i, q.ProvisionalBand Xi' i := ⟨_, hband⟩
  refine ⟨Nat.find hex, lt_of_le_of_lt (Nat.find_le hband) hfp, ?_⟩
  unfold someProvisionalValue
  rw [ite_eq_left htop', ite_eq_right hcap, dite_eq_left hex]

/-- **The provisional value of an anchor is at most `α + K'` in every cover.** -/
theorem someProvisionalValue_le_of_anchor {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    {Xi : Cell p.scheme.scheme} {K' : ℕ} (h : R.IsInfinityAnchor t p Xi K') {m : ℕ}
    {s : Fin m ↪ M} {f : Fin n ↪ Fin m} {q : S α.1 m} (hfs : f.trans s = t)
    (hq : R.eval s = some q) (hpq : typeMap f q = some p) :
    q.someProvisionalValue (mapCell hpq Xi) ≤ ofOrd (α.1 + K') := by
  by_cases hN : K' < q.topGrade
  · obtain ⟨j, hj, hval⟩ := someProvisionalValue_lt_of_anchor h hfs hq hpq hN
    rw [hval, ofOrd_le_ofOrd]
    exact add_le_add_right (Nat.cast_le.mpr hj.le) _
  · refine (someProvisionalValue_le q _).trans ?_
    rw [ofOrd_le_ofOrd]
    exact add_le_add_right (Nat.cast_le.mpr (not_lt.mp hN)) _

/-! ## Stabilization from a uniform bound -/

/-- **Bounded provisional values stabilize**: if the provisional values of a top cell are at
most `α + K` on every cover, the greatest attained offset stabilizes.  The offsets along the
rooted covers of `x` are a bounded monotone natural-valued observation
(`RootedCover.offset_mono`), so `RootedCover.exists_stabilizesTo_of_bddAbove` supplies the
stabilization; the bound `K` is inherited by the attained offset. -/
theorem exists_stabilizesTo_of_bounded (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x : R.LabelledExt) {Xi : Cell x.type.scheme.scheme}
    (htop : x.type.label Xi = ⊤) (K : ℕ)
    (hB : ∀ (y : R.LabelledExt) (f : Fin x.arity ↪ Fin y.arity), f.trans y.tuple = x.tuple →
      ∀ hpq : typeMap f y.type = some x.type,
        y.type.someProvisionalValue (mapCell hpq Xi) ≤ ofOrd (α.1 + K)) :
    ∃ j ≤ K, R.StabilizesTo x.tuple x.type Xi (ofOrd (α.1 + j)) := by
  have hle (y : RootedCover x) : RootedCover.offset Xi htop y ≤ K :=
    RootedCover.offset_le_of_value_le Xi htop
      (hB y.1 (RootedCover.emb y) (RootedCover.emb_trans y) (RootedCover.emb_typeMap y))
  obtain ⟨i, hi⟩ := RootedCover.exists_stabilizesTo_of_bddAbove Xi htop hcons hcov
    ⟨K, by rintro _ ⟨y, rfl⟩; exact hle y⟩
  exact ⟨_, hle i, hi⟩

/-! ## Anchor ⇒ finite stable value -/

/-- **An anchor at threshold `K'` has stable value `α + j` for some `j ≤ K'`.** -/
theorem exists_stableValue_of_anchor (hM : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} {K' : ℕ}
    (h : R.IsInfinityAnchor t p Xi K') :
    ∃ j ≤ K', R.stableValue t p Xi = ofOrd (α.1 + j) := by
  obtain ⟨j, hj, hs⟩ := exists_stabilizesTo_of_bounded hM.consistent hM.covering
    ⟨n, t, p, hpt⟩ h.1 K'
    (fun y f hf hpq => someProvisionalValue_le_of_anchor h hf y.eval_eq hpq)
  refine ⟨j, hj, stableValue_of_stabilizesTo hM.consistent hM.covering hpt ?_ hs⟩
  rw [ofOrd_lt_ofOrd]
  exact (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 j)

theorem stableValue_le_of_anchor (hM : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} {K' : ℕ}
    (h : R.IsInfinityAnchor t p Xi K') : R.stableValue t p Xi ≤ ofOrd (α.1 + K') := by
  obtain ⟨j, hj, hs⟩ := exists_stableValue_of_anchor hM hpt h
  rw [hs, ofOrd_le_ofOrd]
  exact add_le_add_right (Nat.cast_le.mpr hj) _

/-! ## The equivalences -/

/-- **Anchors are exactly the finite stable top values.** -/
theorem hasInfinityAnchor_iff_exists_finite_stable (hM : R.IsModel) :
    R.HasInfinityAnchor ↔ ∃ (n : ℕ) (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p ∧
      ∃ (Xi : Cell p.scheme.scheme) (j : ℕ), p.label Xi = ⊤ ∧
        R.stableValue t p Xi = ofOrd (α.1 + j) := by
  constructor
  · rintro ⟨n, t, p, hpt, Xi, K', h⟩
    obtain ⟨j, -, hs⟩ := exists_stableValue_of_anchor hM hpt h
    exact ⟨n, t, p, hpt, Xi, j, h.1, hs⟩
  · rintro ⟨n, t, p, hpt, Xi, j, hXi, hs⟩
    exact ⟨n, t, p, hpt, Xi, j + 1, isInfinityAnchor_of_stable hM hpt hXi hs⟩

/-- **Hollowness is exactly stable-label fixedness.** -/
theorem isHollow_iff_stable_identity (hM : R.IsModel) :
    R.IsHollow ↔ ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
      ∀ Xi : Cell p.scheme.scheme, R.stableValue t p Xi = p.label Xi := by
  constructor
  · intro hh n t p hpt Xi
    exact stableValue_eq_label_of_hollow hM hh hpt Xi
  · rintro hid ⟨n, t, p, hpt, Xi, K', h⟩
    obtain ⟨j, -, hs⟩ := exists_stableValue_of_anchor hM hpt h
    rw [hid t p hpt Xi, h.1] at hs
    exact ofOrd_ne_top _ hs.symm

/-! ## The sharp threshold under top-grade growth -/

/-- **Under top-grade growth, an anchor at `K'` with stable value `α + j` has `j < K'`.** -/
theorem lt_of_anchor_of_growth (hM : R.IsModel) (hg : R.HasTopGradeGrowth) {n : ℕ}
    {t : Fin n ↪ M} {p : S α.1 n} (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme}
    {K' : ℕ} (h : R.IsInfinityAnchor t p Xi K') {j : ℕ}
    (hs : R.stableValue t p Xi = ofOrd (α.1 + j)) : j < K' := by
  set x : R.LabelledExt := ⟨n, t, p, hpt⟩ with hxdef
  obtain ⟨y, hy, hxy⟩ := hg K' x
  have hyK : K' < y.type.topGrade := hy
  -- the stable value stabilizes: a cover above `y` reads it
  have hst : R.StabilizesTo t p Xi (ofOrd (α.1 + j)) := by
    rcases R.hasStableValue_stableValue t p Xi with ⟨-, hs'⟩ | ⟨heq, -⟩
    · rwa [hs] at hs'
    · rw [heq] at hs; exact absurd hs (ofOrd_ne_top _).symm
  have hD := (stabilizesTo_iff_isDominating hM.consistent hM.covering x Xi _).mp hst
  obtain ⟨w, ⟨fw, hfw, hpw, hval⟩, hyw⟩ := hD y
  have hwK : K' < w.type.topGrade := hyK.trans_le (LabelledExt.topGrade_mono hyw)
  obtain ⟨j', hj', hval'⟩ := someProvisionalValue_lt_of_anchor h hfw w.eval_eq hpw hwK
  rw [isProvisionalValue_iff, hval', ofOrd_inj] at hval
  have := Nat.cast_injective (add_left_cancel hval)
  omega

/-- **The least anchor threshold is `j + 1`**, under top-grade growth. -/
theorem isLeast_anchor_threshold (hM : R.IsModel) (hg : R.HasTopGradeGrowth) {n : ℕ}
    {t : Fin n ↪ M} {p : S α.1 n} (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme}
    (hXi : p.label Xi = ⊤) {j : ℕ} (hs : R.stableValue t p Xi = ofOrd (α.1 + j)) :
    IsLeast {K' : ℕ | R.IsInfinityAnchor t p Xi K'} (j + 1) :=
  ⟨isInfinityAnchor_of_stable hM hpt hXi hs, fun _ hK' => lt_of_anchor_of_growth hM hg hpt hK' hs⟩

end VaughtConjecture.Knight
