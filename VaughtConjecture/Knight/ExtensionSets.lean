/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReductModel
public import VaughtConjecture.Knight.Reduction
public import VaughtConjecture.Knight.ActualOccurrence

/-! # Extension sets over a tuple: syntactic, realized, reduced

Three different sets of one-point extensions of a stage type `p : S α n` are in play, and the
Scott-process reading of the tower (Larson, Def. 3.1) must not identify them:

* the **syntactic coface fibre** `cofaceSet p = {q | IsCoface p q}`: every same-stage type
  restricting to `p` along the initial face, with no model in sight;
* the extensions **actually realized** over a tuple `t` in a realization `R`,
  `R.realizedExt t = {q | ∃ y ∉ range t, R (t⌢y) = some q}`;
* the **lower-stage extensions obtained by reducing higher-stage cofaces**,
  `reducedExt h p = reduceType '' cofaceSet p`, for `p` at the higher stage.

Laws proved here, unconditionally or under exact parent consistency / modelhood only:

* realized extensions are cofaces (`realizedExt_subset_cofaceSet`), and Knight's
  `RealizesSome` is nonemptiness of `realizedExt ∩ U` (`realizesSome_iff`);
* restriction along a coordinate embedding `e`, through `onePointProj e`, for each of the
  three sets (`cofaceSet_restrict`, `realizedExt_restrict`, `reducedExt_restrict`);
* reduction: the reduct realizes exactly the reductions of what `R` realizes
  (`realizedExt_reduct`, an equality), reduced cofaces are cofaces of the reduced type
  (`reducedExt_subset_cofaceSet`), and what a reduct realizes over `t` is the reduction of a
  higher-stage coface of the label of `t` (`realizedExt_reduct_subset_reducedExt`);
* class-wide eligibility: `eligible α p` is the set of extensions realized over some tuple of
  type `p` in some model; `eligible_subset_cofaceSet`, `realizedExt_subset_eligible`, and
  reduction maps eligible to eligible (`reduceType_mem_eligible`, via `IsModel.reduct`).

**What is not proved: the lifting clause.**  Larson's coherence condition (2b) for a Scott
process reads, for `α < β`, `E(V_{α+1,β} φ) ⊆ V_{α,β}[{ψ ∈ Φ^{n+1}_β | H(ψ, i_n) = φ}]`: every
extension asserted at the lower stage by the reduction of `φ` is the reduction of a
higher-stage coface of `φ`.  Its analogue here is `LiftingLaw h`:
`eligible α (reduceType p) ⊆ reducedExt h p` for every `p` at the higher stage, with the
realized strengthening `RealizedLiftingLaw h` (the lift is realized over the given tuple).
Nothing in this file supplies either: the tower's existential clauses (`genSat`,
`bottomPattern`, uniformity, dominance) assert realization of *some* member of prescribed
families only, and the converse inclusion `reducedExt ⊆ eligible` is likewise not asserted.
`RealizedLiftingLaw` is the form a cross-stage back-and-forth argument should consume directly:
it speaks only of tuples realized in a model.  `LiftingLaw` is its type-level shadow; passing
from one to the other (`LiftingLaw.of_realized`) needs every type to be realized in some model,
which is **not** to be added as a hypothesis merely to reach the all-types interface.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

universe w

variable {n : ℕ}

/-! ### The syntactic coface fibre -/

section Syntactic

variable {α : Ordinal.{0}}

/-- The syntactic coface fibre of `p`, as a set: every same-stage type restricting to `p` along
the initial face `Fin.castSuccEmb`. -/
def cofaceSet (p : S α n) : Set (S α (n + 1)) := {q | IsCoface p q}

@[simp] theorem mem_cofaceSet {p : S α n} {q : S α (n + 1)} :
    q ∈ cofaceSet p ↔ IsCoface p q := Iff.rfl

/-- The initial face of `onePointProj e` is `e` followed by the initial face. -/
theorem castSuccEmb_trans_onePointProj {m : ℕ} (e : Fin m ↪ Fin n) :
    Fin.castSuccEmb.trans (onePointProj e) = e.trans Fin.castSuccEmb :=
  Function.Embedding.ext fun i => onePointProj_castSucc e i

/-- **Restriction of cofaces**: a coface of `p` restricts along `onePointProj e`, when the face
is visible, to a coface of the restriction of `p` along `e`. -/
theorem cofaceSet_restrict {m : ℕ} (e : Fin m ↪ Fin n) {p : S α n} {p₀ : S α m}
    (hp : typeMap e p = some p₀) {q : S α (n + 1)} (hq : q ∈ cofaceSet p) {q₀ : S α (m + 1)}
    (hq₀ : typeMap (onePointProj e) q = some q₀) : q₀ ∈ cofaceSet p₀ := by
  have h1 : typeMap Fin.castSuccEmb q₀ = typeMap (Fin.castSuccEmb.trans (onePointProj e)) q :=
    typeMap_trans _ _ q q₀ hq₀
  have h3 : typeMap e p = typeMap (e.trans Fin.castSuccEmb) q := typeMap_trans e _ q p hq
  change typeMap Fin.castSuccEmb q₀ = some p₀
  rw [h1, castSuccEmb_trans_onePointProj, ← h3, hp]

end Syntactic

/-! ### Lower-stage extensions obtained by reducing higher-stage cofaces -/

section Reduced

variable {α β : LimitStage}

/-- The extensions of the reduced type obtained by **reducing higher-stage cofaces**: the image
under `reduceType` of the coface fibre of `p` at the higher stage `β`. -/
def reducedExt (h : α ≤ β) (p : S β.1 n) : Set (S α.1 (n + 1)) :=
  reduceType α.2 h '' cofaceSet p

/-- Reduced cofaces are cofaces of the reduced type (reduction commutes with restriction). -/
theorem reducedExt_subset_cofaceSet (h : α ≤ β) (p : S β.1 n) :
    reducedExt h p ⊆ cofaceSet (reduceType α.2 h p) := by
  rintro _ ⟨q, hq, rfl⟩
  change typeMap Fin.castSuccEmb (reduceType α.2 h q) = some (reduceType α.2 h p)
  rw [typeMap_reduceType_comm α.2 h, mem_cofaceSet.mp hq]
  rfl

/-- **Restriction of reduced extensions** along `onePointProj e`, when the face is visible. -/
theorem reducedExt_restrict (h : α ≤ β) {m : ℕ} (e : Fin m ↪ Fin n) {p : S β.1 n}
    {p₀ : S β.1 m} (hp : typeMap e p = some p₀) {q' : S α.1 (n + 1)} (hq' : q' ∈ reducedExt h p)
    {r : S α.1 (m + 1)} (hr : typeMap (onePointProj e) q' = some r) : r ∈ reducedExt h p₀ := by
  obtain ⟨q, hq, rfl⟩ := hq'
  rw [typeMap_reduceType_comm α.2 h] at hr
  rcases hq₀ : typeMap (onePointProj e) q with _ | q₀
  · rw [hq₀] at hr
    cases hr
  · rw [hq₀, Option.map_some, Option.some.injEq] at hr
    exact ⟨q₀, cofaceSet_restrict e hp hq hq₀, hr⟩

end Reduced

/-! ### Extensions actually realized over a tuple -/

namespace KnightRealization

variable {M : Type w} {α β : LimitStage}

/-- The extensions **actually realized** over `t` in `R`: the labels of the concatenations
`t⌢y`, `y` off `t`. -/
def realizedExt (R : KnightRealization α M) (t : Fin n ↪ M) : Set (S α.1 (n + 1)) :=
  {q | ∃ (y : M) (hy : y ∉ Set.range t), R.eval (snoc t y hy) = some q}

variable {R : KnightRealization α M} {t : Fin n ↪ M} {p : S α.1 n}

/-- Under exact parent consistency, realized extensions of a labelled tuple are cofaces of its
label. -/
theorem realizedExt_subset_cofaceSet (hR : R.IsExactParentConsistent) (hp : R.eval t = some p) :
    R.realizedExt t ⊆ cofaceSet p := by
  rintro q ⟨y, hy, hq⟩
  exact isCoface_of_consistent hR hp hq

/-- Knight's `RealizesSome` is nonemptiness of the realized coface set within `U`
(unconditional form). -/
theorem realizesSome_iff_nonempty (U : Set (S α.1 (n + 1))) :
    R.RealizesSome t p U ↔ (R.realizedExt t ∩ cofaceSet p ∩ U).Nonempty := by
  constructor
  · rintro ⟨y, hy, q, hU, hc, hq⟩
    exact ⟨q, ⟨⟨y, hy, hq⟩, hc⟩, hU⟩
  · rintro ⟨q, ⟨⟨y, hy, hq⟩, hc⟩, hU⟩
    exact ⟨y, hy, q, hU, hc, hq⟩

/-- Under exact parent consistency the coface condition is redundant: `RealizesSome` is
nonemptiness of `realizedExt ∩ U`. -/
theorem realizesSome_iff (hR : R.IsExactParentConsistent) (hp : R.eval t = some p)
    (U : Set (S α.1 (n + 1))) : R.RealizesSome t p U ↔ (R.realizedExt t ∩ U).Nonempty := by
  rw [realizesSome_iff_nonempty]
  constructor
  · rintro ⟨q, ⟨hq, -⟩, hU⟩
    exact ⟨q, hq, hU⟩
  · rintro ⟨q, hq, hU⟩
    exact ⟨q, ⟨hq, realizedExt_subset_cofaceSet hR hp hq⟩, hU⟩

/-- **Restriction of realized extensions**: under exact parent consistency, a realized extension
of `t` restricts along `onePointProj e`, when the face is visible, to a realized extension of
`e.trans t` (by the same witness point). -/
theorem realizedExt_restrict (hR : R.IsExactParentConsistent) {m : ℕ} (e : Fin m ↪ Fin n)
    (t : Fin n ↪ M) {q : S α.1 (n + 1)} (hq : q ∈ R.realizedExt t) {q₀ : S α.1 (m + 1)}
    (hq₀ : typeMap (onePointProj e) q = some q₀) : q₀ ∈ R.realizedExt (e.trans t) := by
  obtain ⟨y, hy, hq⟩ := hq
  obtain ⟨hy', _, heval⟩ := restrict_actual_extension hR e rfl hy hq hq₀
  exact ⟨y, hy', heval⟩

/-- **Reduction of realized extensions** (an equality): the reduct realizes over `t` exactly the
reductions of what `R` realizes over `t`. -/
theorem realizedExt_reduct (h : α ≤ β) (R : KnightRealization β M) (t : Fin n ↪ M) :
    KnightRealization.realizedExt (R.reduct h) t = reduceType α.2 h '' R.realizedExt t := by
  ext q'
  constructor
  · rintro ⟨y, hy, hq'⟩
    rw [TypeTower.Realization.reduct_eval] at hq'
    rcases hq : R.eval (snoc t y hy) with _ | q
    · rw [hq] at hq'
      cases hq'
    · rw [hq, Option.map_some] at hq'
      exact ⟨q, ⟨y, hy, hq⟩, Option.some_injective _ hq'⟩
  · rintro ⟨q, ⟨y, hy, hq⟩, rfl⟩
    exact ⟨y, hy, by rw [TypeTower.Realization.reduct_eval, hq]; rfl⟩

/-- What a reduct realizes over a labelled tuple is the reduction of a higher-stage coface of
the label (exact parent consistency at the higher stage). -/
theorem realizedExt_reduct_subset_reducedExt (h : α ≤ β) {R : KnightRealization β M}
    (hR : R.IsExactParentConsistent) {t : Fin n ↪ M} {p : S β.1 n} (hp : R.eval t = some p) :
    KnightRealization.realizedExt (R.reduct h) t ⊆ reducedExt h p := by
  rw [realizedExt_reduct]
  exact Set.image_mono (realizedExt_subset_cofaceSet hR hp)

end KnightRealization

/-! ### Class-wide eligibility and the unsupplied lifting clause -/

section Eligible

variable {α β : LimitStage}

/-- **Eligible extensions** of `p`: the extensions realized over some tuple of type `p` in some
model of `S^α` (carriers in `Type w`; countable models live in `Type`).  This is the
model-theoretic extension set, as opposed to the syntactic fibre `cofaceSet p`; nothing here
identifies the two. -/
def eligible (α : LimitStage) (p : S α.1 n) : Set (S α.1 (n + 1)) :=
  {q | ∃ (M : Type w) (R : KnightRealization α M) (t : Fin n ↪ M),
    R.IsModel ∧ R.eval t = some p ∧ q ∈ R.realizedExt t}

/-- Eligible extensions are cofaces. -/
theorem eligible_subset_cofaceSet (p : S α.1 n) : eligible.{w} α p ⊆ cofaceSet p := by
  rintro q ⟨M, R, t, hR, hp, hq⟩
  exact KnightRealization.realizedExt_subset_cofaceSet hR.consistent hp hq

/-- What a model realizes over a tuple of type `p` is eligible for `p`. -/
theorem KnightRealization.realizedExt_subset_eligible {M : Type w} {R : KnightRealization α M}
    (hR : R.IsModel) {t : Fin n ↪ M} {p : S α.1 n} (hp : R.eval t = some p) :
    R.realizedExt t ⊆ eligible.{w} α p :=
  fun _ hq => ⟨M, R, t, hR, hp, hq⟩

/-- **Reduction preserves eligibility**: the reduction of an eligible extension of `p` is an
eligible extension of the reduction of `p` (the reduct of a model is a model). -/
theorem reduceType_mem_eligible (h : α ≤ β) {p : S β.1 n} {q : S β.1 (n + 1)}
    (hq : q ∈ eligible.{w} β p) : reduceType α.2 h q ∈ eligible.{w} α (reduceType α.2 h p) := by
  obtain ⟨M, R, t, hR, hp, hq⟩ := hq
  refine ⟨M, R.reduct h, t, hR.reduct h, ?_, ?_⟩
  · rw [TypeTower.Realization.reduct_eval, hp]
    rfl
  · rw [KnightRealization.realizedExt_reduct]
    exact ⟨q, hq, rfl⟩

/-- Eligible extensions of a reduced type that are reductions of higher-stage cofaces: the
inclusion `reducedExt h p ∩ eligible α (reduceType p) ⊆ eligible` is trivial; the substantive
question is the **lifting clause** below. -/
theorem eligible_reduceType_subset_cofaceSet (h : α ≤ β) (p : S β.1 n) :
    eligible.{w} α (reduceType α.2 h p) ⊆ cofaceSet (reduceType α.2 h p) :=
  eligible_subset_cofaceSet _

/-- **The lifting clause (analogue of Larson's coherence condition (2b)), not supplied.**
Every eligible extension of the reduction of `p` is the reduction of a higher-stage coface of
`p`.  This is the existence clause a cross-stage back-and-forth argument must consume: nothing
in the tower's existential clauses supplies it, and it is stated here only so that its use is
visible. -/
def LiftingLaw (h : α ≤ β) : Prop :=
  ∀ {n : ℕ} (p : S β.1 n), eligible.{w} α (reduceType α.2 h p) ⊆ reducedExt h p

/-- The lifting clause, unfolded: for every eligible lower-stage extension `q'` of the reduced
type there is a higher-stage coface `q` of `p` reducing to `q'`. -/
theorem liftingLaw_iff (h : α ≤ β) :
    LiftingLaw.{w} h ↔ ∀ {n : ℕ} (p : S β.1 n) (q' : S α.1 (n + 1)),
      q' ∈ eligible.{w} α (reduceType α.2 h p) →
        ∃ q : S β.1 (n + 1), IsCoface p q ∧ reduceType α.2 h q = q' := by
  constructor
  · intro H n p q' hq'
    obtain ⟨q, hq, rfl⟩ := H p hq'
    exact ⟨q, hq, rfl⟩
  · intro H n p q' hq'
    obtain ⟨q, hq, rfl⟩ := H p q' hq'
    exact ⟨q, hq, rfl⟩

/-- **The realized lifting clause, not supplied**: the lift is realized over the given tuple.
For every model `R` at the higher stage and every tuple `t` of type `p`, every eligible
extension of the reduced type is realized over `t` by the reduct.  Strictly stronger than
`LiftingLaw` (`LiftingLaw.of_realized`). -/
def RealizedLiftingLaw (h : α ≤ β) : Prop :=
  ∀ {M : Type w} {R : KnightRealization β M}, R.IsModel → ∀ {n : ℕ} {t : Fin n ↪ M}
    {p : S β.1 n}, R.eval t = some p →
      eligible.{w} α (reduceType α.2 h p) ⊆ KnightRealization.realizedExt (R.reduct h) t

/-- The realized lifting clause implies the lifting clause, provided the type `p` is realized in
some model at the higher stage.  Consumers should use `RealizedLiftingLaw` directly rather than
assume this realizability to pass through `LiftingLaw`. -/
theorem LiftingLaw.of_realized (h : α ≤ β) (H : RealizedLiftingLaw.{w} h)
    (hreal : ∀ {n : ℕ} (p : S β.1 n), ∃ (M : Type w) (R : KnightRealization β M)
      (t : Fin n ↪ M), R.IsModel ∧ R.eval t = some p) : LiftingLaw.{w} h := by
  intro n p
  obtain ⟨M, R, t, hR, hp⟩ := hreal p
  exact (H hR hp).trans (KnightRealization.realizedExt_reduct_subset_reducedExt h hR.consistent hp)

end Eligible

end VaughtConjecture.Knight
