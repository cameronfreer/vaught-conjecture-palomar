/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model
public import VaughtConjecture.Knight.Coface
public import VaughtConjecture.Knight.SuccLimitBandArithmetic

/-! # Reduction of models: Def. 3.2.1 under strict vertical reduction (#101)

Knight's §5.1 (Def. 5.1.1): for limit stages `α ≤ β`, a model `N` of `S^β` **reduces** to the
realization `S^{ι_{α,β}} ∘ N` of `S^α` — here `R.reduct h` (`TypeTower.Realization.reduct`),
whose labels are `reduceType` = strict truncation `truncExt α` of every label, rows and schemes
fixed.  This module audits Def. 3.2.1 at `α` for the reduct of an **arbitrary** model at `β`,
clause by clause (the diagnostic of #101; `docs/CONCORDANCE.md` §5.1):

* clauses (2) consistency and (3) covering are generic (`IsModel.consistent_reduct`,
  `IsModel.covering_reduct`, from `TypeTower/Basic.lean`);
* **(4)(a)(i) generalised saturation** (`IsModel.reduct_genSat`): reduction fixes schemes, so
  `ExtendsDomain (reduce p) D` is literally `ExtendsDomain p D`, and the reduction of a coface of
  `p` with domain `D` is a coface of `reduce p` with domain `D` (`RealizesSome.reduct`, from
  `typeMap_reduceType_comm`);
* **(4)(b) uniformity** (`IsModel.reduct_uniformity`): for a non-successor `γ < α` the band
  `[γ, γ + ω)` lies below `α` (`add_omega0_le_of_lt_isSuccLimit`: `α` is a limit), and
  `truncExt α` is the identity there (`truncExt_id_of_lt`);
* **(4)(c) high-grade dominance** (`IsModel.reduct_highGradeDominance`): `truncExt α` is
  inflationary (`truncExt_le_self`), so a label `> γ` stays `> γ`; the grade is untouched;
* **(4)(a)(ii) prescribed `−∞`-pattern** (`IsModel.reduct_bottomPattern`) — the clause flagged
  **at risk** in #101.  The α-level request gives `q'` respecting `D.rows` and extending the
  **truncated** `p`, `q' ∘ cellOf = truncExt α ∘ p.label`; to use the β-level clause one needs a
  respecting `q''` extending the **untruncated** `p` with the same `⊥`-pattern.  This holds for
  **arbitrary** models, by the bountifulness of `D` itself (Def. 2.5.14, a field of `SemScheme`)
  at the **positive** cutoff `γ = n + 1` (`StageType.exists_respects_extends_of_truncated`, via
  `Knight/Coface.lean`'s capped bountifulness engine `StageType.exists_respects_extends_capped`,
  of which the B4 lemma `exists_respects_extends` is the case `γ = ⊥`):
  - the capped-agreement premise `(q' ∧ γ) ↾ dom p = p ∧ γ` holds because `γ = n + 1 < ω ≤ α`:
    on a face cell with `p d < α` truncation is the identity, and on one with `p d ≥ α` both
    sides cap to `γ`;
  - `γ` is self-visible at the threshold `n + 1` of the full-grade pair `⟨n+1, n+1⟩`
    (`extVisibilityReplace_natCast_succ_self`: its finite part is `n + 1`);
  - the conclusion `q'' ∧ γ = q' ∧ γ` with `γ > ⊥` gives `q'' Θ = ⊥ ↔ q' Θ = ⊥` on **every**
    cell of `D` (a fortiori on `D^{≤ n}`), and `q'' ↾ dom p = p` literally.
  The β-level witness `q ∈ BottomPatternFamily D q''` then reduces to a member of
  `BottomPatternFamily D q'`, since `truncExt α` preserves and reflects `⊥`
  (`truncExt_eq_bot_iff`).

Hence **every clause of `IsModel` is preserved by reduction for arbitrary models**
(`IsModel.reduct`); nothing is receipt-only.  The intermediate predicate
`IsModelExceptBottomPattern` (all clauses but (a)(ii)) records what is preserved **without**
invoking bountifulness (`IsModel.reduct_exceptBottomPattern`); (a)(ii) is the only clause whose
transfer uses the semantics of `D` at all.

This is the reduction half of §5.1 only; the converse (that a model of `S^α` expands) is the
content of §5.3–5.5 and is not claimed (KVC-d23's stage-bounded `−∞`-pattern reroute is not
needed here: the faithful clause, with unbounded `q'`, transfers as it stands). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd TypeTower

/-! ### Ordinal and label preliminaries -/


/-- The finite part of a natural number is itself. -/
theorem finitePart_natCast (k : ℕ) : finitePart (k : Ordinal.{0}) = k := by
  have h := finitePart_limitPart_add_nat 0 k
  rwa [limitPart, Ordinal.zero_div, mul_zero, zero_add] at h

/-- The label `n + 1` is self-visible at the threshold `n + 1` (`γ = γ ⊔⁺_{n+1} (n+1)`, Lemma
2.2.4: its finite part is `n + 1`). -/
theorem extVisibilityReplace_natCast_succ_self (n : ℕ) :
    extVisibilityReplace (ofOrd (n + 1 : ℕ)) (n + 1) (n + 1) = ofOrd (n + 1 : ℕ) := by
  rw [extVisibilityReplace_self_iff]
  exact Or.inr (Or.inr ⟨_, rfl, (finitePart_natCast (n + 1)).symm.le⟩)

/-- Capping at a label `γ ≠ ⊥` preserves and reflects `⊥`. -/
theorem min_eq_bot_iff_of_ne_bot {x γ : ExtOrd} (hγ : γ ≠ ⊥) : min x γ = ⊥ ↔ x = ⊥ := by
  rw [min_eq_bot]
  exact or_iff_left hγ

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-- **The `−∞`-pattern transfers across truncation of the face.**  For `p : S β n` (any stage
`β`), `D` an extension domain of `dom p`, a limit `α`, and `q'` respecting `D.rows` and
extending the **truncated** `p` (`q' ∘ cellOf = truncExt α ∘ p.label`), there is `q''`
respecting `D.rows`, extending the **untruncated** `p`, with the same `⊥`-pattern as `q'` on
every cell of `D`.  This is `exists_respects_extends_capped` at the positive cutoff
`γ = n + 1`: the capped-agreement premise holds since `n + 1 < ω ≤ α` (on a face cell either
truncation is the identity, or both sides cap to `γ`), and `q'' ∧ γ = q' ∧ γ` with `γ > ⊥`
preserves and reflects `⊥`. -/
theorem exists_respects_extends_of_truncated {β : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {p : S β n} {D : SemScheme (n + 1)} (hD : ExtendsDomain p D)
    {q' : Cell D.scheme → ExtOrd} (hq' : RespectsSemantics D.rows q')
    (hext : ∀ d, q' (hD.cellOf d) = truncExt α (p.label d)) :
    ∃ q'' : Cell D.scheme → ExtOrd, RespectsSemantics D.rows q'' ∧
      (∀ d, q'' d = ⊥ ↔ q' d = ⊥) ∧ ∀ d, q'' (hD.cellOf d) = p.label d := by
  have hγα : ofOrd (n + 1 : ℕ) ≤ ofOrd α :=
    ofOrd_le_ofOrd.mpr
      ((Ordinal.natCast_lt_omega0 _).le.trans (Ordinal.omega0_le_of_isSuccLimit hα))
  have hne : ofOrd (n + 1 : ℕ) ≠ ⊥ := ofOrd_ne_bot _
  obtain ⟨q'', hq'', hcap, hext''⟩ := exists_respects_extends_capped hD hq'
    (extVisibilityReplace_natCast_succ_self n) (fun d => by
      rw [hext d]
      rcases le_or_gt (ofOrd α) (p.label d) with h | h
      · rw [truncExt_eq_top_of_ge h, min_eq_right le_top, min_eq_right (hγα.trans h)]
      · rw [truncExt_id_of_lt h])
  refine ⟨q'', hq'', fun d => ?_, hext''⟩
  rw [← min_eq_bot_iff_of_ne_bot (x := q'' d) hne, hcap d, min_eq_bot_iff_of_ne_bot hne]

end StageType

/-! ### Reducts of realizations: labels and realized families -/

namespace KnightRealization

universe w

variable {M : Type w} {n : ℕ} {α β : LimitStage}

/-- A label of the reduct is the reduction of a label of the original. -/
theorem eval_reduct_eq_some (h : α ≤ β) {R : KnightRealization β M} {t : Fin n ↪ M}
    {p' : S α.1 n} (hp' : (R.reduct h).eval t = some p') :
    ∃ p : S β.1 n, R.eval t = some p ∧ reduceType α.2 h p = p' := by
  have hp'' : (R.eval t).map (reduceType α.2 h) = some p' := hp'
  exact Option.map_eq_some_iff.mp hp''

/-- **Realized families reduce.**  If `R` realizes some member of `U` over `t` as a coface of
`p`, and reduction sends `U` into `U'`, then the reduct realizes some member of `U'` over `t`
as a coface of `reduce p` (the coface condition by `typeMap_reduceType_comm`). -/
theorem RealizesSome.reduct (h : α ≤ β) {R : KnightRealization β M} {t : Fin n ↪ M}
    {p : S β.1 n} {U : Set (S β.1 (n + 1))} {U' : Set (S α.1 (n + 1))}
    (hU : ∀ q ∈ U, reduceType α.2 h q ∈ U') (hR : R.RealizesSome t p U) :
    RealizesSome (R.reduct h) t (reduceType α.2 h p) U' := by
  obtain ⟨y, hy, q, hqU, hqc, hq⟩ := hR
  refine ⟨y, hy, reduceType α.2 h q, hU q hqU, ?_, ?_⟩
  · exact (typeMap_reduceType_comm α.2 h Fin.castSuccEmb q).trans
      (congrArg (Option.map (reduceType α.2 h)) hqc)
  · exact congrArg (Option.map (reduceType α.2 h)) hq

/-! ### Def. 3.2.1 under reduction, clause by clause -/

variable {R : KnightRealization β M}

/-- **(4)(a)(i) generalised saturation is preserved by reduction**: reduction fixes schemes, so
an extension domain of `reduce p` is one of `p`, and the reduction of a coface of `p` with
domain `D` is a coface of `reduce p` with domain `D`. -/
theorem IsModel.reduct_genSat (hR : R.IsModel) (h : α ≤ β) :
    ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), (R.reduct h).eval t = some p →
      ∀ D : SemScheme (n + 1), ExtendsDomain p D →
        RealizesSome (R.reduct h) t p (GenSatFamily D) := by
  intro n t p' hp' D hD
  obtain ⟨p, hp, rfl⟩ := eval_reduct_eq_some h hp'
  have hD' : ExtendsDomain p D := ⟨hD.visible, hD.restrict⟩
  exact (hR.genSat t p hp D hD').reduct h fun q hq => hq

/-- **(4)(b) uniformity is preserved by reduction**: for a non-successor `γ < α` the band
`[γ, γ + ω)` lies below the limit `α` (`add_omega0_le_of_lt_isSuccLimit`), where `truncExt α` is
the identity. -/
theorem IsModel.reduct_uniformity (hR : R.IsModel) (h : α ≤ β) :
    ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), (R.reduct h).eval t = some p →
      ∀ γ : Ordinal.{0}, IsNonSuccessor γ → γ < α.1 →
        RealizesSome (R.reduct h) t p (UniformityFamily γ) := by
  intro n t p' hp' γ hγ hγα
  obtain ⟨p, hp, rfl⟩ := eval_reduct_eq_some h hp'
  refine (hR.uniformity t p hp γ hγ (hγα.trans_le (show α.1 ≤ β.1 from h))).reduct h ?_
  rintro q ⟨Sig, h1, h2⟩
  have hlt : q.label Sig < ofOrd α.1 :=
    h2.trans_le (ofOrd_le_ofOrd.mpr (add_omega0_le_of_lt_isSuccLimit α.2 hγα))
  exact ⟨Sig, le_of_le_of_eq h1 (truncExt_id_of_lt hlt).symm,
    lt_of_eq_of_lt (truncExt_id_of_lt hlt) h2⟩

/-- **(4)(c) high-grade dominance is preserved by reduction**: `truncExt α` is inflationary
(`truncExt_le_self`) and grades are untouched. -/
theorem IsModel.reduct_highGradeDominance (hR : R.IsModel) (h : α ≤ β) :
    ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), (R.reduct h).eval t = some p →
      ∀ γ : Ordinal.{0}, γ < α.1 →
        RealizesSome (R.reduct h) t p (HighGradeDominanceFamily γ) := by
  intro n t p' hp' γ hγα
  obtain ⟨p, hp, rfl⟩ := eval_reduct_eq_some h hp'
  refine (hR.highGradeDominance t p hp γ (hγα.trans_le (show α.1 ≤ β.1 from h))).reduct h ?_
  rintro q ⟨Sig, hg, hl⟩
  exact ⟨Sig, hg, hl.trans_le (truncExt_le_self _ _)⟩

/-- **(4)(a)(ii) the prescribed `−∞`-pattern is preserved by reduction** (the clause flagged at
risk in #101): the α-level pattern source `q'` extends the truncated `p`; by bountifulness at
the cutoff `n + 1` (`StageType.exists_respects_extends_of_truncated`) there is a β-level
source `q''` extending `p` with the same `⊥`-pattern, and the β-level witness reduces to one
with the pattern of `q'`, since `truncExt α` preserves and reflects `⊥`. -/
theorem IsModel.reduct_bottomPattern (hR : R.IsModel) (h : α ≤ β) :
    ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), (R.reduct h).eval t = some p →
      ∀ (D : SemScheme (n + 1)) (hD : ExtendsDomain p D) (q' : Cell D.scheme → ExtOrd),
        RespectsSemantics D.rows q' → (∀ d, q' (hD.cellOf d) = p.label d) →
        RealizesSome (R.reduct h) t p (BottomPatternFamily D q') := by
  intro n t p' hp' D hD q' hq' hext
  obtain ⟨p, hp, rfl⟩ := eval_reduct_eq_some h hp'
  have hD' : ExtendsDomain p D := ⟨hD.visible, hD.restrict⟩
  obtain ⟨q'', hq'', hpat, hext''⟩ :=
    StageType.exists_respects_extends_of_truncated α.2 hD' hq' fun d => hext d
  refine (hR.bottomPattern t p hp D hD' q'' hq'' hext'').reduct h ?_
  rintro q ⟨hqD, hq⟩
  refine ⟨hqD, fun Θ => ?_⟩
  change truncExt α.1 (q.label (SemScheme.castCell hqD.symm Θ.1)) = ⊥ ↔ q' Θ.1 = ⊥
  rw [truncExt_eq_bot_iff, hq Θ, hpat]

/-! ### The partial predicate and the full theorem -/

variable (R) in
/-- **A model except for the `−∞`-pattern clause**: Def. 3.2.1 with clause (4)(a)(ii)
omitted.  This is what reduction preserves **without** appealing to the semantics of the
request domains (clauses (2), (3), (4)(a)(i), (b), (c) transfer by label arithmetic alone);
(4)(a)(ii) transfers too (`IsModel.reduct_bottomPattern`), but through bountifulness. -/
structure IsModelExceptBottomPattern : Prop where
  /-- The domain `M` is nonempty. -/
  nonempty : Nonempty M
  /-- Clause (2), consistency. -/
  consistent : R.IsExactParentConsistent
  /-- Clause (3), covering. -/
  covering : R.IsInitialSegmentCovering
  /-- Clause (4)(a)(i), generalised saturation. -/
  genSat : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S β.1 n), R.eval t = some p →
    ∀ D : SemScheme (n + 1), ExtendsDomain p D → R.RealizesSome t p (GenSatFamily D)
  /-- Clause (4)(b), uniformity. -/
  uniformity : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S β.1 n), R.eval t = some p →
    ∀ γ : Ordinal.{0}, IsNonSuccessor γ → γ < β.1 → R.RealizesSome t p (UniformityFamily γ)
  /-- Clause (4)(c), high-grade dominance. -/
  highGradeDominance : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S β.1 n), R.eval t = some p →
    ∀ γ : Ordinal.{0}, γ < β.1 → R.RealizesSome t p (HighGradeDominanceFamily γ)

/-- A model is a model except for the `−∞`-pattern clause. -/
theorem IsModel.exceptBottomPattern (hR : R.IsModel) : R.IsModelExceptBottomPattern :=
  ⟨hR.nonempty, hR.consistent, hR.covering, hR.genSat, hR.uniformity, hR.highGradeDominance⟩

/-- The partial predicate together with the `−∞`-pattern clause is modelhood. -/
theorem IsModelExceptBottomPattern.isModel (hR : R.IsModelExceptBottomPattern)
    (hb : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S β.1 n), R.eval t = some p →
      ∀ (D : SemScheme (n + 1)) (hD : ExtendsDomain p D) (q' : Cell D.scheme → ExtOrd),
        RespectsSemantics D.rows q' → (∀ d, q' (hD.cellOf d) = p.label d) →
        R.RealizesSome t p (BottomPatternFamily D q')) : R.IsModel :=
  ⟨hR.nonempty, hR.consistent, hR.covering, hR.genSat, hb, hR.uniformity,
    hR.highGradeDominance⟩

/-- **Reduction preserves every clause but (4)(a)(ii) by label arithmetic alone**: the reduct of
a model at `β` to a limit stage `α ≤ β` is a model except for the `−∞`-pattern clause. -/
theorem IsModel.reduct_exceptBottomPattern (hR : R.IsModel) (h : α ≤ β) :
    IsModelExceptBottomPattern (R.reduct h) :=
  ⟨hR.nonempty, hR.consistent_reduct h, hR.covering_reduct h, hR.reduct_genSat h,
    hR.reduct_uniformity h, hR.reduct_highGradeDominance h⟩

/-- **The reduct of a model is a model** (the reduction half of Knight's §5.1, for arbitrary
models at arbitrary limit stages `α ≤ β`): every clause of Def. 3.2.1 is preserved by strict
vertical reduction. -/
theorem IsModel.reduct (hR : R.IsModel) (h : α ≤ β) : IsModel (R.reduct h) :=
  (hR.reduct_exceptBottomPattern h).isModel (hR.reduct_bottomPattern h)

end KnightRealization

end VaughtConjecture.Knight
