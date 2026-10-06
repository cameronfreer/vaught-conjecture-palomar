/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SameStageCalibration
public import VaughtConjecture.Knight.ReferenceContext
public import VaughtConjecture.Knight.SlackCutPasting
public import VaughtConjecture.Knight.CountedEncoding
public import VaughtConjecture.Knight.RestrictedComposition

/-! # A finite stable top value is an anchor at infinity; hollow models have stable identity

The reviewer's notes4 (`same_stage_top.md` §7, 2026-09-18), formalized against the **literal**
definitions `IsInfinityAnchor` / `IsHollow` of `Knight/Terminal.lean`.

**Theorem** (`isInfinityAnchor_of_stable`).  An actual ordinary-`⊤` occurrence `Xi` of a
realized type with stable value `α + j` is an anchor at infinity at threshold `j + 1`; the
defining source inequality is **strict already at owner grade `j + 1`** (the definition asks
for strictness only above the threshold).  Proof: in any actual extension, at any `⊤`-labelled
owner `Θ` of grade `N ≥ j + 1` above `Xi`, the stable labelling is lawful on the unchanged
rows (`stableLiftRespects`), retains the value `α + j` at `Xi` (`stableValue_mapCell`), and
reads every `⊤`-labelled cell at least `α + grade`, so the stable owner cap `s(Θ) ≥ α + N` lies
**strictly above** `α + j` and the exact capped shifter of the stable locality at `Θ`
(`exists_exact_capped_shifter`) reads the source of `Xi` exactly as `α + j`; commutation with
replacement through `N` then pins that source to `ξ + j` for a block start `ξ` decoding to `α`
(`source_pinned`).  Every `⊤`-labelled `Σ` below `Θ` has stable capped reading above `α`, hence
source above `ξ`, hence replacement at `(j+1, j+1)` above `ξ + j` (`evr_succ_gt_of_gt_limit`).
Two independent stable localities on the original rows; no transformation from ordinary to
stable labels, and no assertion that the stable lift is a model.

**Corollary** (`stableValue_eq_label_of_hollow`).  In a hollow model every actual stable label
equals its ordinary label: non-`⊤` labels are already stable, and a `⊤` label with a finite
stable value `α + j` would supply an anchor.

**Caveats, kept literal.**  This is the repository's `IsHollow` — no anchor at *any* threshold
— not a repaired reading of the paper; the documented finite-characteristic vacuity of anchors
above a bounded characteristic arity is untouched.  Nothing here needs full-arity top covers.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd Transform

/-! ## Scalar lemmas -/

/-- **Source pinning.**  A bottom-preserving map commuting with replacement through `N` that
sends `x` to `α + j` (`α` a limit, `j < N`) sees `x = ξ + j` for a block start `ξ` that it sends
to `α`. -/
theorem source_pinned {τ : ExtOrd → ExtOrd} (hbot : τ ⊥ = ⊥) {N j : ℕ} (hjN : j < N)
    (hcomm : ∀ x k i, k ≤ N → i ≤ k →
      τ (extVisibilityReplace x k i) = extVisibilityReplace (τ x) k i)
    {α : Ordinal.{0}} (hα : limitPart α = α) {x : ExtOrd} (hτx : τ x = ofOrd (α + j)) :
    ∃ ξ : Ordinal.{0}, limitPart ξ = ξ ∧ x = ofOrd (ξ + j) ∧ τ (ofOrd ξ) = ofOrd α := by
  have hevr : ∀ k, k ≤ N → extVisibilityReplace (ofOrd (α + j)) N k = ofOrd (α + k) := by
    intro k _
    rw [extVisibilityReplace_of_finitePart_lt (by
      rw [finitePart_limitPart_add_nat' hα]; exact hjN), limitPart_add_nat_of_limitPart_eq hα]
  rcases ExtOrd.cases x with rfl | rfl | ⟨ξ', rfl⟩
  · rw [hbot] at hτx; exact absurd hτx.symm (ofOrd_ne_bot _)
  · exfalso
    have h := hcomm ⊤ N N le_rfl le_rfl
    rw [extVisibilityReplace_top, hτx, hevr N le_rfl, ofOrd_inj] at h
    exact hjN.ne (Nat.cast_injective (add_left_cancel h))
  · by_cases hfp : N ≤ finitePart ξ'
    · exfalso
      have h := hcomm (ofOrd ξ') N N le_rfl le_rfl
      rw [extVisibilityReplace_of_le_finitePart hfp, hτx, hevr N le_rfl, ofOrd_inj] at h
      exact hjN.ne (Nat.cast_injective (add_left_cancel h))
    · have hfp' := not_le.mp hfp
      have hk : ∀ k, k ≤ N → τ (ofOrd (limitPart ξ' + k)) = ofOrd (α + k) := by
        intro k hk
        have h := hcomm (ofOrd ξ') N k le_rfl hk
        rwa [extVisibilityReplace_of_finitePart_lt hfp', hτx, hevr k hk] at h
      have hj : finitePart ξ' = j := by
        have h := hk (finitePart ξ') hfp'.le
        rw [limitPart_add_finitePart, hτx, ofOrd_inj] at h
        exact (Nat.cast_injective (add_left_cancel h)).symm
      refine ⟨limitPart ξ', limitPart_idem ξ', ?_, ?_⟩
      · rw [← hj, limitPart_add_finitePart]
      · have h := hk 0 (Nat.zero_le _)
        rwa [Nat.cast_zero, add_zero, add_zero] at h

/-- **Replacement above a block start**: for `y` strictly above the limit `ξ`, its replacement
at `(j+1, j+1)` is strictly above `ξ + j`. -/
theorem evr_succ_gt_of_gt_limit {ξ : Ordinal.{0}} (hξ : limitPart ξ = ξ) {y : ExtOrd}
    (hy : ofOrd ξ < y) (j : ℕ) :
    ofOrd (ξ + j) < extVisibilityReplace y (j + 1) (j + 1) := by
  have hstep : ξ + (j : Ordinal.{0}) < ξ + ((j + 1 : ℕ) : Ordinal.{0}) :=
    add_lt_add_right (Nat.cast_lt.mpr (Nat.lt_succ_self j)) _
  rcases ExtOrd.cases y with rfl | rfl | ⟨η, rfl⟩
  · exact absurd hy not_lt_bot
  · rw [extVisibilityReplace_top]; exact ofOrd_lt_top _
  · rw [ofOrd_lt_ofOrd] at hy
    have hl : ξ ≤ limitPart η := by
      have := limitPart_mono hy.le
      rwa [hξ] at this
    by_cases hfp : j + 1 ≤ finitePart η
    · rw [extVisibilityReplace_of_le_finitePart hfp]
      apply ofOrd_lt_ofOrd.mpr
      calc ξ + (j : Ordinal.{0}) < ξ + ((j + 1 : ℕ) : Ordinal.{0}) := hstep
        _ ≤ limitPart η + ((j + 1 : ℕ) : Ordinal.{0}) := add_le_add_left hl _
        _ ≤ limitPart η + (finitePart η : Ordinal.{0}) := add_le_add_right (Nat.cast_le.mpr hfp) _
        _ = η := limitPart_add_finitePart η
    · rw [extVisibilityReplace_of_finitePart_lt (not_le.mp hfp)]
      apply ofOrd_lt_ofOrd.mpr
      calc ξ + (j : Ordinal.{0}) < ξ + ((j + 1 : ℕ) : Ordinal.{0}) := hstep
        _ ≤ limitPart η + ((j + 1 : ℕ) : Ordinal.{0}) := add_le_add_left hl _

/-! ## The anchor -/

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

/-- **A finite stable top value is an anchor at infinity** at threshold `j + 1`, with the
source inequality strict already at owner grade `j + 1`. -/
theorem isInfinityAnchor_of_stable (hM : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} (hXi : p.label Xi = ⊤) {j : ℕ}
    (hs : R.stableValue t p Xi = ofOrd (α.1 + j)) : R.IsInfinityAnchor t p Xi (j + 1) := by
  refine ⟨hXi, ?_⟩
  intro m s f q hfs hq hpq Θ hΘgr hΘtop Sig hSig hXi'
  suffices hlt : q.scheme.rows.E Θ ⟨mapCell hpq Xi, hXi'⟩ <
      extVisibilityReplace (q.scheme.rows.E Θ Sig) (j + 1) (j + 1) from ⟨hlt.le, fun _ => hlt⟩
  -- the stable labelling of the extension
  have hσr : RespectsSemantics q.scheme.rows (fun d => R.stableValue s q d) :=
    stableLiftRespects hM hq
  have hσa : R.stableValue s q (mapCell hpq Xi) = ofOrd (α.1 + j) := by
    rw [stableValue_mapCell hM.consistent hM.covering hpt hq hfs hpq Xi, hs]
  have hjN : j < q.scheme.scheme.grade Θ := hΘgr
  have hσΘ : ofOrd (α.1 + q.scheme.scheme.grade Θ) ≤ R.stableValue s q Θ :=
    stable_ge_of_top hM hq hΘtop
  have hσS : ofOrd (α.1 + q.scheme.scheme.grade Sig.1) ≤ R.stableValue s q Sig.1 :=
    stable_ge_of_top hM hq hSig
  have hαjΘ : ofOrd (α.1 + j) ≤ R.stableValue s q Θ := (stage_add_lt hjN).le.trans hσΘ
  -- the exact capped shifter of the stable locality at `Θ`
  have hvis : SelfVis (q.scheme.scheme.grade Θ) (R.stableValue s q Θ) := (hσr.orderly Θ).symm
  obtain ⟨τ, hbot, hmono, hread, hcomm, -⟩ := exists_exact_capped_shifter
    (D := q.scheme.scheme.below (q.scheme.scheme.cell Θ))
    (grade := fun d => q.scheme.scheme.grade d.1) (p := fun d => R.stableValue s q d.1)
    (c := ⟨Θ, GradedLe.refl _⟩) (fun d => d.2.2) hvis (hσr.locality Θ)
  have hτa : τ (q.scheme.rows.E Θ ⟨mapCell hpq Xi, hXi'⟩) = ofOrd (α.1 + j) := by
    have h := hread ⟨mapCell hpq Xi, hXi'⟩
    change τ _ = min (R.stableValue s q (mapCell hpq Xi)) (R.stableValue s q Θ) at h
    rwa [hσa, min_eq_left hαjΘ] at h
  have hτS : ofOrd (α.1 + ((1 : ℕ) : Ordinal.{0})) ≤ τ (q.scheme.rows.E Θ Sig) := by
    have h := hread Sig
    change τ _ = min (R.stableValue s q Sig.1) (R.stableValue s q Θ) at h
    rw [h]
    refine le_min ?_ ?_
    · exact (ofOrd_le_ofOrd.mpr (add_le_add_right
        (Nat.cast_le.mpr (q.scheme.scheme.grade_pos Sig.1)) _)).trans hσS
    · exact (ofOrd_le_ofOrd.mpr (add_le_add_right
        (Nat.cast_le.mpr (q.scheme.scheme.grade_pos Θ)) _)).trans hσΘ
  -- pin the source of `Xi`
  obtain ⟨ξ, hξ, hEa, hτξ⟩ := source_pinned hbot hjN hcomm limitPart_stage hτa
  -- the source of `Σ` lies strictly above `ξ`
  have hSξ : ofOrd ξ < q.scheme.rows.E Θ Sig := by
    by_contra hle
    have h := hmono (not_lt.mp hle)
    rw [hτξ] at h
    have h1 : ofOrd (α.1 + ((1 : ℕ) : Ordinal.{0})) ≤ ofOrd α.1 := hτS.trans h
    rw [ofOrd_le_ofOrd] at h1
    exact absurd h1 (not_le.mpr (lt_add_of_pos_right _ (by norm_num)))
  rw [hEa]
  exact evr_succ_gt_of_gt_limit hξ hSξ j

/-! ## Hollow models -/

/-- **Stable identity in hollow models**: every actual stable label equals its ordinary label.
The literal `IsHollow` (no anchor at any threshold) is used; the finite-characteristic vacuity
of anchors above a bounded characteristic arity is not repaired here. -/
theorem stableValue_eq_label_of_hollow (hM : R.IsModel) (hh : R.IsHollow) {n : ℕ}
    {t : Fin n ↪ M} {p : S α.1 n} (hpt : R.eval t = some p) (Xi : Cell p.scheme.scheme) :
    R.stableValue t p Xi = p.label Xi := by
  by_cases htop : p.label Xi = ⊤
  · rcases R.hasStableValue_stableValue t p Xi with ⟨hlt, -⟩ | ⟨heq, -⟩
    · exfalso
      have hge := le_stableValue_of_top (R := R) hpt htop
      obtain ⟨j, hj⟩ := exists_nat_of_band hge hlt
      exact hh ⟨n, t, p, hpt, Xi, j + 1, isInfinityAnchor_of_stable hM hpt htop hj⟩
    · rw [heq, htop]
  · exact stableValue_of_ne_top hM.consistent hM.covering hpt htop

end VaughtConjecture.Knight
