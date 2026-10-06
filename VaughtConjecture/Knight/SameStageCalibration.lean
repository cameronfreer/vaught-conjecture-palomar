/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GuardActivation
public import VaughtConjecture.Knight.StableLiftCore
public import VaughtConjecture.Knight.Directedness
public import VaughtConjecture.Knight.FiniteOffset

/-! # Same-stage calibration from an attained stable marker and top-grade growth

The reviewer's assignment (2026-09-18, item 3): at the model's own stage, guard activation
cannot come from an ordinary label strictly below the cap (the marker is labelled `⊤`).  It
comes from the **stable labelling**: an attained marker `a` with ordinary label `⊤` and stable
value `α + j`, `0 < j`, together with top-grade growth, which supplies a cover with a
top-labelled full-scope cell of grade `N > j` — the cap — chosen **after** `j` and every other
offset are known.  In every coface the model realizes over that cover:

* the stable labelling is lawful on the same rows (`stableLiftRespects`), so the guard on the
  stable capped labelling reflects to the controller's row;
* the stable value of the marker is retained (`stableValue_mapCell`, along the cover and along
  the coface), and the stable values of the top-labelled grade-`N` cap and controller are at
  least `α + N > α + j` (`stable_ge_of_top`: at least `α` and `N`-visible), so the capped
  stable marker is `α + j` (`stable_guard_active`);
* the ordinary labelling reads back: the controller is labelled `⊤` (`exists_top_controller`),
  so `guarded_readback_at` transports the row's correctness to the ordinary labels, proper
  requests read exactly (`read_proper`) and, with the block-floor bound, top requests read
  literally `⊤` (`read_top_of_cutoffBound`).

**Explicit hypotheses, not asserted branches.**  The attained marker and top-grade growth are
hypotheses here: they are what the positive tight grade-defect branch supplies, and this module
does not claim them for the band-defect, zero-threshold, or bounded-top-grade branches, nor
does it use a threshold-vacuous infinity anchor.  The safe rows are supplied by the probe.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan Transform

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

/-! ## A top cap of high grade from top-grade growth -/

/-- **The cover with a top cap**: top-grade growth over a realized tuple supplies a realized
cover with a full-scope cell labelled `⊤` of grade above any prescribed bound; the root is a
face of the cover. -/
theorem exists_top_cap (hM : R.IsModel) (hg : R.HasTopGradeGrowth) {n : ℕ} {t : Fin n ↪ M}
    {p : S α.1 n} (hp : R.eval t = some p) (K : ℕ) :
    ∃ (m : ℕ) (u : Fin m ↪ M) (g : Fin n ↪ Fin m) (q : S α.1 m) (_hu : R.eval u = some q)
      (_hgu : g.trans u = t) (_hpq : typeMap g q = some p) (N : ℕ) (cap : Cell q.scheme.scheme),
      K < N ∧ q.scheme.scheme.cell cap = (Finset.univ, N) ∧ q.label cap = ⊤ := by
  obtain ⟨m, u, g, q, hu, hgu, hK⟩ := (hM.hasTopGradeGrowth_iff.mp hg) K t
  have hpq : typeMap g q = some p := by
    have h := hM.consistent u q g hu
    rw [hgu, hp] at h
    exact h.symm
  have hne : q.topGrades.Nonempty := by
    by_contra hno
    rw [Set.not_nonempty_iff_eq_empty] at hno
    have h0 : q.topGrade = 0 := by
      unfold StageType.topGrade
      rw [hno, csSup_empty]
      rfl
    omega
  have hmem : q.topGrade ∈ q.topGrades := Nat.sSup_mem hne q.topGrades_bddAbove
  obtain ⟨cap, hsc, hgr, hlab⟩ := hmem
  exact ⟨m, u, g, q, hu, hgu, hpq, q.topGrade, cap, hK, Prod.ext hsc hgr, hlab⟩

/-! ## Stable values of top-labelled cells of grade `N` -/

/-- The stage is its own limit part. -/
theorem limitPart_stage : limitPart α.1 = α.1 :=
  limitPart_eq_self_of_isNonSuccessor (Or.inr α.2)

/-- A proper ordinal at least `α` (a limit) and `N`-visible is at least `α + N`. -/
theorem stage_add_le_of_selfVis {γ : Ordinal.{0}} (hγ : α.1 ≤ γ) {N : ℕ}
    (hN : SelfVis N (ofOrd γ)) : α.1 + N ≤ γ := by
  rw [selfVis_ofOrd_iff] at hN
  have h1 : α.1 ≤ limitPart γ := by
    have := limitPart_mono hγ
    rwa [limitPart_stage] at this
  calc α.1 + (N : Ordinal.{0}) ≤ limitPart γ + (N : Ordinal.{0}) := add_le_add_left h1 _
    _ ≤ limitPart γ + finitePart γ := add_le_add_right (Nat.cast_le.mpr hN) _
    _ = γ := limitPart_add_finitePart γ

/-- **Stable values of top-labelled cells**: at a cell of grade `N` labelled `⊤`, the stable
value is `⊤` or a proper ordinal at least `α + N` (at least `α`, and `N`-visible by lawfulness
of the stable labelling). -/
theorem stable_ge_of_top (hM : R.IsModel) {m : ℕ} {u : Fin m ↪ M} {q : S α.1 m}
    (hu : R.eval u = some q) {Θ : Cell q.scheme.scheme} (hΘ : q.label Θ = ⊤) :
    ofOrd (α.1 + q.scheme.scheme.grade Θ) ≤ R.stableValue u q Θ := by
  have hα := le_stableValue_of_top (R := R) hu hΘ
  have hvis : SelfVis (q.scheme.scheme.grade Θ) (R.stableValue u q Θ) :=
    ((stableLiftRespects hM hu).orderly Θ).symm
  rcases ExtOrd.cases (R.stableValue u q Θ) with hb | ht | ⟨γ, hγ⟩
  · rw [hb] at hα; exact absurd hα (not_ofOrd_le_bot _)
  · rw [ht]; exact le_top
  · rw [hγ] at hα hvis ⊢
    exact ofOrd_le_ofOrd.mpr (stage_add_le_of_selfVis (ofOrd_le_ofOrd.mp hα) hvis)

/-- `α + j < α + N` for `j < N`. -/
theorem stage_add_lt {j N : ℕ} (h : j < N) : ofOrd (α.1 + j) < ofOrd (α.1 + N) :=
  ofOrd_lt_ofOrd.mpr (add_lt_add_right (Nat.cast_lt.mpr h) _)

/-! ## The controller and the stable guard in a realized coface -/

variable (hM : R.IsModel) {m : ℕ} {u : Fin m ↪ M} {q₀ : S α.1 m} (hu : R.eval u = some q₀)
  {N : ℕ} {cap : Cell q₀.scheme.scheme} (hcap : q₀.scheme.scheme.cell cap = (Finset.univ, N))
  (hcapl : q₀.label cap = ⊤)
  {y : M} {hy : y ∉ Set.range u} {Q : S α.1 (m + 1)} (hQ : R.eval (snoc u y hy) = some Q)

include hM hu hQ in
/-- A realized one-point extension is a coface (exact consistency). -/
theorem isCoface_realized : IsCoface q₀ Q := isCoface_of_consistent hM.consistent hu hQ

include hcap hcapl in
/-- **The top controller**: in a coface, availability from the top-labelled cap of grade `N`
toward the full-scope grade-`N` index gives a controller labelled `⊤`. -/
theorem exists_top_controller (hcof : IsCoface q₀ Q) :
    ∃ Θ : Cell Q.scheme.scheme, Q.scheme.scheme.cell Θ = (Finset.univ, N) ∧ Q.label Θ = ⊤ := by
  have hN : 0 < N := by
    have := q₀.scheme.scheme.grade_pos cap
    rwa [show q₀.scheme.scheme.grade cap = N from congrArg Prod.snd hcap] at this
  have hNm : N ≤ m := by
    have h := q₀.scheme.scheme.grade_le_card_scope cap
    rw [show q₀.scheme.scheme.grade cap = N from congrArg Prod.snd hcap] at h
    exact h.trans ((Finset.card_le_card (Finset.subset_univ _)).trans (Finset.card_fin _).le)
  have hmem : ((Finset.univ : Finset (Fin (m + 1))), N) ∈
      Plan.gradedPlan Q.scheme.scheme.plan := by
    refine Plan.mem_gradedPlan.mpr ⟨Q.scheme.scheme.isPlan.domain_mem, hN, ?_⟩
    rw [Finset.card_fin]
    exact hNm.trans (Nat.le_succ _)
  obtain ⟨Xi₀, hXi₀⟩ := Q.scheme.complete _ hmem
  have hg : Q.scheme.scheme.grade (mapCell hcof cap) = Q.scheme.scheme.grade Xi₀ := by
    rw [grade_mapCell hcof cap, show q₀.scheme.scheme.grade cap = N from congrArg Prod.snd hcap]
    exact (congrArg Prod.snd hXi₀).symm
  have hs : Q.scheme.scheme.scope (mapCell hcof cap) ⊆ Q.scheme.scheme.scope Xi₀ := by
    rw [show Q.scheme.scheme.scope Xi₀ = Finset.univ from congrArg Prod.fst hXi₀]
    exact Finset.subset_univ _
  obtain ⟨Θ, hΘ, hle⟩ := Q.respects.availability _ Xi₀ hs hg
  refine ⟨Θ, hΘ.trans hXi₀, ?_⟩
  rw [label_mapCell hcof cap, hcapl] at hle
  exact top_le_iff.mp hle

include hcap in
/-- The cap has grade `N`. -/
theorem grade_cap : q₀.scheme.scheme.grade cap = N := congrArg Prod.snd hcap

/-- A cell of grade at most `N` lies below a cell at `(univ, N)`. -/
theorem below_of_grade_le {Θ d : Cell Q.scheme.scheme}
    (hΘ : Q.scheme.scheme.cell Θ = (Finset.univ, N)) (hd : Q.scheme.scheme.grade d ≤ N) :
    GradedLe (Q.scheme.scheme.cell d) (Q.scheme.scheme.cell Θ) := by
  rw [hΘ]
  exact ⟨Finset.subset_univ _, hd⟩

include hM hu hQ in
/-- **Stable naturality along the realized coface**: the stable value of an old cell is
retained. -/
theorem stableValue_coface (hcof : IsCoface q₀ Q) (d : Cell q₀.scheme.scheme) :
    R.stableValue (snoc u y hy) Q (mapCell hcof d) = R.stableValue u q₀ d :=
  stableValue_mapCell hM.consistent hM.covering hu hQ (castSuccEmb_trans_snoc u y hy) hcof d

include hM hu hcap hcapl hQ in
/-- **Stable guard activation**: at any top-labelled controller `Θ` at `(univ, N)` of a realized
coface, the stable capped labelling satisfies the guard with the marker's offset `j < N`, for a
marker `a₀` (of grade at most `N`) whose stable value is `α + j`. -/
theorem stable_guard_active (hcof : IsCoface q₀ Q) {a₀ : Cell q₀.scheme.scheme} {j : ℕ}
    (hj : j < N) (hsa : R.stableValue u q₀ a₀ = ofOrd (α.1 + j))
    (hga : q₀.scheme.scheme.grade a₀ ≤ N) {Θ : Cell Q.scheme.scheme}
    (hΘ : Q.scheme.scheme.cell Θ = (Finset.univ, N)) (hΘl : Q.label Θ = ⊤) :
    Guard (D := Q.scheme.scheme.below (Q.scheme.scheme.cell Θ)) j
      ⟨mapCell hcof a₀, below_of_grade_le hΘ (by rw [grade_mapCell hcof a₀]; exact hga)⟩
      ⟨mapCell hcof cap, below_of_grade_le hΘ (by rw [grade_mapCell hcof cap, grade_cap hcap])⟩
      (fun d => min (R.stableValue (snoc u y hy) Q d.1) (R.stableValue (snoc u y hy) Q Θ)) := by
  have hsa' : R.stableValue (snoc u y hy) Q (mapCell hcof a₀) = ofOrd (α.1 + j) := by
    rw [stableValue_coface hM hu hQ hcof, hsa]
  have hcap' : Q.label (mapCell hcof cap) = ⊤ := by rw [label_mapCell hcof cap, hcapl]
  have hgc : Q.scheme.scheme.grade (mapCell hcof cap) = N := by
    rw [grade_mapCell hcof cap]; exact congrArg Prod.snd hcap
  have hgΘ : Q.scheme.scheme.grade Θ = N := congrArg Prod.snd hΘ
  have h1 : ofOrd (α.1 + j) ≤ R.stableValue (snoc u y hy) Q (mapCell hcof cap) := by
    have := stable_ge_of_top hM hQ hcap'
    rw [hgc] at this
    exact (stage_add_lt hj).le.trans this
  have h2 : ofOrd (α.1 + j) ≤ R.stableValue (snoc u y hy) Q Θ := by
    have := stable_ge_of_top hM hQ hΘl
    rw [hgΘ] at this
    exact (stage_add_lt hj).le.trans this
  refine ⟨α.1 + j, ?_, finitePart_limitPart_add_nat' limitPart_stage _⟩
  change min (min (R.stableValue (snoc u y hy) Q (mapCell hcof a₀))
    (R.stableValue (snoc u y hy) Q Θ)) (min (R.stableValue (snoc u y hy) Q (mapCell hcof cap))
    (R.stableValue (snoc u y hy) Q Θ)) = ofOrd (α.1 + j)
  rw [hsa', min_eq_left h2, min_eq_left (le_min h1 h2)]

/-! ## Readback in the ordinary labelling -/

/-- **Literal top readback**: from the cutoff lower bound at a top-labelled cap, a request with
offset `0` whose representative (the marker) is labelled `⊤` reads `⊤`. -/
theorem read_top_of_cutoffBound {D' : Type*} {grade : D' → ℕ} {Rt : FiniteReferenceData D' grade}
    {f : D' → ExtOrd} (hc : Rt.CutoffBound f) (ht : f Rt.trigger ≠ ⊥) (hcap : f Rt.cap = ⊤)
    {r : FiniteRequest D'} (hr : r ∈ Rt.requests) (h0 : r.offset = 0)
    (hmark : f (Rt.rep r.block) = ⊤) : f r.cell = ⊤ := by
  have h := hc ht r hr
  rw [hcap, hmark, h0, extVisibilityReplace_top, min_self, min_eq_left le_top] at h
  exact top_le_iff.mp h

include hM hu hcap hcapl hQ in
/-- **Same-stage readback from a safe row**: at a top-labelled controller `Θ` of a realized
coface whose row is safe for finite-value correctness and the cutoff lower bound (with the
transported marker and cap), the stable guard reflects and the ordinary labelling satisfies
both predicates uncapped. -/
theorem same_stage_readback (hcof : IsCoface q₀ Q) {a₀ : Cell q₀.scheme.scheme} {j : ℕ}
    (hj : j < N) (hsa : R.stableValue u q₀ a₀ = ofOrd (α.1 + j))
    (hga : q₀.scheme.scheme.grade a₀ ≤ N) {Θ : Cell Q.scheme.scheme}
    (hΘ : Q.scheme.scheme.cell Θ = (Finset.univ, N)) (hΘl : Q.label Θ = ⊤)
    (R' Rt : FiniteReferenceData (Q.scheme.scheme.below (Q.scheme.scheme.cell Θ))
      fun d => Q.scheme.scheme.grade d.1)
    (hsafe : Safe (D := Q.scheme.scheme.below (Q.scheme.scheme.cell Θ))
      (fun f => R'.Correct f ∧ Rt.CutoffBound f) j
      ⟨mapCell hcof a₀, below_of_grade_le hΘ (by rw [grade_mapCell hcof a₀]; exact hga)⟩
      ⟨mapCell hcof cap, below_of_grade_le hΘ (by rw [grade_mapCell hcof cap, grade_cap hcap])⟩
      (Q.scheme.rows.E Θ)) :
    R'.Correct (fun d => Q.label d.1) ∧ Rt.CutoffBound (fun d => Q.label d.1) := by
  have hΦ : ∀ f f' : Q.scheme.scheme.below (Q.scheme.scheme.cell Θ) → ExtOrd,
      TransformsTo (fun d => Q.scheme.scheme.grade d.1) f f' →
      (R'.Correct f ∧ Rt.CutoffBound f) → (R'.Correct f' ∧ Rt.CutoffBound f') :=
    fun _ _ h ⟨h1, h2⟩ => ⟨h1.transport h, h2.transport h⟩
  have h := guarded_correct_capped hΦ Q.respects (stableLiftRespects hM hQ) hj
    (show Q.scheme.scheme.grade (mapCell hcof cap) = N by
      rw [grade_mapCell hcof cap]; exact congrArg Prod.snd hcap)
    (show Q.scheme.scheme.grade (mapCell hcof a₀) ≤ N by rw [grade_mapCell hcof a₀]; exact hga)
    hsafe (stable_guard_active hM hu hcap hcapl hQ hcof hj hsa hga hΘ hΘl)
  have e : (fun d : Q.scheme.scheme.below (Q.scheme.scheme.cell Θ) =>
      min (Q.label d.1) (Q.label Θ)) = fun d => Q.label d.1 := by
    funext d
    rw [hΘl, min_eq_left le_top]
  rwa [e] at h

end VaughtConjecture.Knight
