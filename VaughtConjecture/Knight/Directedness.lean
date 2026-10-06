/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Terminal
public import VaughtConjecture.DirectedNat

/-! # Model-internal directedness of labelled covers (#51 (1/3); §5.3)

Boundary 1 of #51: the ambient order theory of Knight's §5.3 cover arguments, stated for an
**arbitrary supplied model** (`IsModel` as a consumed hypothesis — no #121/#106/#42
construction machinery; that independence is exactly what this boundary tests).

The paper's Def. 5.3.9 and Lemma 5.3.10 quantify over "the finite subsets `A` of `M`" with
their labels `M(A)`, ordered by inclusion (Def. 3.2.8).  The rebuilt form of that index set is
the **labelled-cover poset** `KnightRealization.LabelledExt`: the labelled injective tuples of
the one realization `R`, preordered by *"is a visible face of, with the labels restricting
exactly"* — the same common-extension shape `StabilizesTo` (Def. 5.3.9, `Knight/Terminal.lean`)
already quantifies with.  Four results, one per headline of the boundary:

1. **Directedness** (`directed_labelledExt`, from the absorption lemma
   `exists_labelledExt_le`): any two labelled covers of a model have a common labelled
   extension.  The proof is *concatenate, cover, restrict*: concatenate the two tuples
   (`exists_common_tuple`, pure combinatorics of injective tuples), cover the concatenation by
   a labelled tuple (clause (3), `IsInitialSegmentCovering`), and read both labels back off the
   covering label by exact consistency (clause (2), `IsExactParentConsistent`).

2. **Dominating → coinitial upgrade** (`IsDominating.isCoinitial`,
   `isCoinitial_iff_isDominating` — the Cor. 5.3.8 shape).  A set of covers is **dominating**
   (`IsDominating`) when every labelled cover has a member above it — for a model this is
   exactly Def. 5.3.9's "dominating set of finite subsets", quantifying over arbitrary tuples
   (`isDominating_iff`); it is **coinitial** (`IsCoinitial`) when above every labelled
   cover it contains a whole principal tail.  Dominating does *not* imply coinitial in a
   directed preorder; the upgrade consumes the **Lemma 5.3.7 ratchet** in poset form
   (`IsRatcheted`: once the property is lost above a member it never returns — the "stays
   fixed or jumps to `≥ α + K^q`, irreversibly" content of the ratchet).  Instantiating
   `IsRatcheted` for the provisional-value sets `stableSet` *is* Lemma 5.3.7 proper
   (provisional-value row arithmetic over given types), deferred to the later boundaries of
   #51; the bridge `stabilizesTo_iff_isDominating` already identifies Def. 5.3.9's
   dominating form with poset domination of `stableSet`.

3. **Finite intersections of coinitial tails are coinitial** (`isCoinitial_biInter`,
   `isCoinitial_biInter_tail`; binary form `IsCoinitial.inter`).  Coinitial sets are
   closed under finite intersection — the filter fact behind Lemma 5.3.10's "sufficiently
   large cover" (one stabilization/escape tail per cell of the finite `dom p`, then one cover
   in the intersection); dominating sets are **not** so closed, which is why the Cor. 5.3.8
   upgrade is load-bearing.  Directedness enters through `isCoinitial_tail`: the
   principal tails themselves are coinitial, so the tails of a model generate a filter.

4. **Top-grade growth** (`StageType.topGrade_le_of_typeMap_eq_some`, `growthSet`,
   `HasTopGradeGrowth`, `HasTopGradeGrowth.isCoinitial_growthSet`).  `K^p` (`topGrade`,
   Def. 5.3.1) is weakly increasing along the cover order: exact restriction preserves the
   `∞`-label and the grade of a top cell into the bigger type, and availability
   (Def. 2.5.4(2)) + completeness (Def. 2.5.15) produce a full-scope `∞`-cell of the same
   grade there (`grade_mem_topGrades`).  Hence the growth sets `{q : K < K^q}` are upward
   closed, upward-closed sets are ratcheted for free (`isRatcheted_of_upwardClosed`), and the
   **growth branch** of Lemma 5.3.10's dichotomy — for every `K` the growth set is dominating
   (`HasTopGradeGrowth`, mirroring `StabilizesTo`'s dominating form;
   `hasTopGradeGrowth_iff` is the tuple-quantified reading) — upgrades to: *every
   sufficiently large cover has top grade `> K`* (the growth sets are coinitial).

## Cor. 5.3.8 without amalgamation

The printed Cor. 5.3.8 cites "amalgamation" for the dominating ↔ coinitial equivalence.  Here
the equivalence is **model-internal**: directedness of the labelled covers comes from clauses
(2) and (3) of Def. 3.2.1 alone (concatenate, cover, restrict), and the upgrade itself is pure
order theory over that poset.  No §4.3 completion, no `ExtendsDomain`, no #106 producer, and
no S-level amalgamation (Cor. 4.3.22 → 4.3.19) is touched (`docs/CONCORDANCE.md` §5.3).

## The falsification test of #51 — outcome

**The construction needs NO named-coface realization service — covering and exact consistency
suffice.**  Boundary 1 had to decide whether covering, consistency, the realized request
families, and `StabilizesTo` prove existence of the required sufficiently large labelled cover
without such a service; they do, and less was needed: every theorem in this module consumes
only clause (2) (exact consistency) and clause (3) (initial-segment covering) — each
realization-facing lemma is **stated with exactly those minimal hypotheses**
(`IsExactParentConsistent`, `IsInitialSegmentCovering`; covering alone for
`nonempty_labelledExt`), and the full-`IsModel` signatures are kept only as one-line
convenience wrappers delegating to the cores; the
four existential-closure clauses of `IsModel` are never consulted, no coface is manufactured,
and no realization service (named or otherwise) appears.  The "sufficiently large cover" of
Lemma 5.3.10 is a member of a finite intersection of coinitial sets over the model's **own**
labelled covers (headline 3), whose coinitiality is supplied by headlines 2 and 4.  The one
remaining §5.3 obligation feeding this route — that the provisional-value sets `stableSet` are
ratcheted (Lemma 5.3.7) — is a statement about *given* stage types under `typeMap` and exact
consistency, not about any extension producer; it is deferred to #51's later boundaries, not
to a serviced object.

Guardrails honoured: the `∨`-branching of prolongation stays classical control flow (no
`P ∨ ¬P` theorem is a milestone here); no exact-coface service; no global transitivity of `⇒`
(`TransformsTo` is not mentioned); no new fields on `SemScheme` or `IsModel`. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

/-! ### Concatenation of injective tuples

The combinatorial half of "concatenate, cover, restrict": two injective tuples embed jointly
into a single injective tuple, the first as its initial segment (`t` first, then the points of
`s` not on `t`).  Pure `Fin`/`Finset` bookkeeping; no realization is involved. -/

/-- Any two injective tuples `t`, `s` on `M` jointly embed into one injective tuple: `t` is an
initial segment, and `s` embeds via `g`. -/
theorem exists_common_tuple {M : Type w} {n m : ℕ} (t : Fin n ↪ M) (s : Fin m ↪ M) :
    ∃ (k : ℕ) (w : Fin (n + k) ↪ M) (g : Fin m ↪ Fin (n + k)),
      (Fin.castAddEmb k).trans w = t ∧ g.trans w = s := by
  classical
  set B : Finset M := Finset.univ.image s \ Finset.univ.image t with hBdef
  have hBt : ∀ b ∈ B, b ∉ Set.range t := by
    rintro b hb ⟨j, hj⟩
    exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
  let e : Fin B.card → M := fun j => (B.equivFin.symm j : M)
  have he : Function.Injective e := fun i j hij =>
    B.equivFin.symm.injective (Subtype.coe_injective hij)
  have hte : ∀ (a : Fin n) (b : Fin B.card), t a ≠ e b := by
    intro a b hab
    exact hBt _ (B.equivFin.symm b).2 ⟨a, hab⟩
  have hwinj : Function.Injective (Fin.append (⇑t) e) := by
    intro i j hij
    induction i using Fin.addCases with
    | left i₁ =>
      induction j using Fin.addCases with
      | left j₁ =>
        rw [Fin.append_left, Fin.append_left] at hij
        exact congrArg (Fin.castAdd B.card) (t.injective hij)
      | right j₁ =>
        rw [Fin.append_left, Fin.append_right] at hij
        exact absurd hij (hte i₁ j₁)
    | right i₁ =>
      induction j using Fin.addCases with
      | left j₁ =>
        rw [Fin.append_right, Fin.append_left] at hij
        exact absurd hij.symm (hte j₁ i₁)
      | right j₁ =>
        rw [Fin.append_right, Fin.append_right] at hij
        exact congrArg (Fin.natAdd n) (he hij)
  let w : Fin (n + B.card) ↪ M := ⟨Fin.append (⇑t) e, hwinj⟩
  have hw_left : ∀ j : Fin n, w (Fin.castAdd B.card j) = t j := fun j =>
    Fin.append_left (⇑t) e j
  have hw_right : ∀ j : Fin B.card, w (Fin.natAdd n j) = e j := fun j =>
    Fin.append_right (⇑t) e j
  have hmem : ∀ i : Fin m, (¬ ∃ j, t j = s i) → s i ∈ B := by
    intro i hi
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    intro hmem'
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem'
    exact hi ⟨j, hj⟩
  obtain ⟨g0, hg0⟩ : ∃ g0 : Fin m → Fin (n + B.card), ∀ i, w (g0 i) = s i := by
    refine ⟨fun i => if h : ∃ j, t j = s i then Fin.castAdd B.card h.choose
      else Fin.natAdd n (B.equivFin ⟨s i, hmem i h⟩), fun i => ?_⟩
    dsimp only
    by_cases h : ∃ j, t j = s i
    · rw [dite_eq_left h, hw_left]
      exact h.choose_spec
    · rw [dite_eq_right h, hw_right]
      exact congrArg Subtype.val (B.equivFin.symm_apply_apply _)
  refine ⟨B.card, w, ⟨g0, fun i j hij => s.injective (by rw [← hg0 i, ← hg0 j, hij])⟩, ?_, ?_⟩
  · ext j
    simp only [Function.Embedding.trans_apply, Fin.castAddEmb_apply]
    exact hw_left j
  · ext i
    exact hg0 i

/-! ### `K^p` is weakly increasing along exact restriction -/

namespace StageType

variable {α : Ordinal.{0}} {m n : ℕ}

/-- **`K^p` is weakly increasing along inclusion of covers** (the monotonicity behind
Lemma 5.3.10's dichotomy): if `p` is the exact restriction of `q`, then `K^p ≤ K^q`.  Exact
restriction preserves the `∞`-label and the grade of a witnessing top cell
(`label_mapCell`, `grade_mapCell`), and availability (Def. 2.5.4(2)) + completeness
(Def. 2.5.15) then produce a full-scope `∞`-cell of the same grade in `q`
(`grade_mem_topGrades`). -/
theorem topGrade_le_of_typeMap_eq_some {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) : p.topGrade ≤ q.topGrade := by
  by_cases hne : p.topGrades.Nonempty
  · obtain ⟨Θ, hsc, hgr, htop⟩ : p.topGrade ∈ p.topGrades :=
      Nat.sSup_mem hne p.topGrades_bddAbove
    have hmem : p.topGrade ∈ q.topGrades := by
      have hlab : q.label (mapCell h Θ) = ⊤ := by rw [label_mapCell h Θ, htop]
      have hmem' := grade_mem_topGrades hlab
      rwa [grade_mapCell h Θ, hgr] at hmem'
    exact le_csSup q.topGrades_bddAbove hmem
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    unfold topGrade
    rw [hne]
    simp [csSup_empty]

end StageType

/-! ### The labelled-cover poset -/

namespace KnightRealization

open StageType

variable {α : LimitStage} {M : Type w}

/-- A **labelled cover** of the realization `R`: an injective tuple together with its label
(the rebuilt form of Def. 3.2.8's "finite subset `A ∈ dom [M]` with its type `M(A)`" — on
tuples, as everywhere in this library). -/
structure LabelledExt (R : KnightRealization α M) where
  /-- The arity of the cover. -/
  arity : ℕ
  /-- The underlying injective tuple. -/
  tuple : Fin arity ↪ M
  /-- The label (stage type) the realization assigns to the tuple. -/
  type : S α.1 arity
  /-- The tuple is labelled, by `type`. -/
  eval_eq : R.eval tuple = some type

namespace LabelledExt

variable {R : KnightRealization α M}

/-- The order of the labelled-cover poset: `x ≤ y` iff the tuple of `x` is a **visible face**
of the tuple of `y` **with the labels restricting exactly** — some embedding carries `x`'s
tuple onto a sub-tuple of `y`'s and `typeMap` along it carries `y`'s label onto `x`'s.  This
is the paper's inclusion of labelled finite subsets, and the common-extension shape
`StabilizesTo` quantifies with.  A preorder, not a partial order: mutually comparable covers
are permutations of one another, not equal. -/
instance : Preorder (LabelledExt R) where
  le x y := ∃ f : Fin x.arity ↪ Fin y.arity,
    f.trans y.tuple = x.tuple ∧ typeMap f y.type = some x.type
  le_refl x := ⟨Function.Embedding.refl _, Function.Embedding.refl_trans _, typeMap_refl _⟩
  le_trans x y z := by
    rintro ⟨f, hft, hfp⟩ ⟨g, hgt, hgp⟩
    refine ⟨f.trans g, ?_, ?_⟩
    · rw [Function.Embedding.trans_assoc, hgt, hft]
    · rw [← typeMap_trans f g z.type y.type hgp]
      exact hfp

theorem le_def {x y : LabelledExt R} :
    x ≤ y ↔ ∃ f : Fin x.arity ↪ Fin y.arity,
      f.trans y.tuple = x.tuple ∧ typeMap f y.type = some x.type := Iff.rfl

/-- `K^p` is weakly increasing along the labelled-cover order. -/
theorem topGrade_mono {x y : LabelledExt R} (h : x ≤ y) :
    x.type.topGrade ≤ y.type.topGrade := by
  obtain ⟨f, -, hpq⟩ := h
  exact topGrade_le_of_typeMap_eq_some hpq

/-- The principal **tail** above a labelled cover: all labelled covers extending it. -/
def tail (x : LabelledExt R) : Set (LabelledExt R) := {y | x ≤ y}

@[simp] theorem mem_tail {x y : LabelledExt R} : y ∈ x.tail ↔ x ≤ y := Iff.rfl

end LabelledExt

variable {R : KnightRealization α M}

/-! ### Directedness: covering + consistency give common larger labelled covers -/

/-- **Absorption** (minimal hypotheses — clauses (2) and (3) suffice): above any labelled
cover there is a labelled cover containing any prescribed tuple.  *Concatenate*
(`exists_common_tuple`), *cover* (clause (3)), *restrict* (clause (2)).  No
existential-closure clause is consulted, and no coface is manufactured: the larger cover is
one of the realization's own. -/
theorem exists_labelledExt_le (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x : R.LabelledExt) {m : ℕ} (s : Fin m ↪ M) :
    ∃ y : R.LabelledExt, x ≤ y ∧ ∃ g : Fin m ↪ Fin y.arity, g.trans y.tuple = s := by
  obtain ⟨k, w, g0, hwt, hws⟩ := exists_common_tuple x.tuple s
  obtain ⟨k', u, hu, husome⟩ := hcov w
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp husome
  have htuple : ((Fin.castAddEmb k).trans (Fin.castAddEmb k')).trans u = x.tuple := by
    rw [Function.Embedding.trans_assoc, hu]
    exact hwt
  have htype : typeMap ((Fin.castAddEmb k).trans (Fin.castAddEmb k')) q = some x.type := by
    have h := hcons u q ((Fin.castAddEmb k).trans (Fin.castAddEmb k')) hq
    rw [htuple, x.eval_eq] at h
    exact h.symm
  refine ⟨⟨_, u, q, hq⟩, ⟨(Fin.castAddEmb k).trans (Fin.castAddEmb k'), htuple, htype⟩,
    g0.trans (Fin.castAddEmb k'), ?_⟩
  rw [Function.Embedding.trans_assoc, hu]
  exact hws

/-- Convenience wrapper of `exists_labelledExt_le` for a full model. -/
theorem IsModel.exists_labelledExt_le (hR : R.IsModel) (x : R.LabelledExt) {m : ℕ}
    (s : Fin m ↪ M) :
    ∃ y : R.LabelledExt, x ≤ y ∧ ∃ g : Fin m ↪ Fin y.arity, g.trans y.tuple = s :=
  KnightRealization.exists_labelledExt_le hR.consistent hR.covering x s

/-- **Headline 1 — model-internal directedness** (minimal hypotheses — clauses (2) and (3)
suffice): any two labelled covers have a common labelled extension.  Cor. 5.3.8's printed
"amalgamation" citation is replaced by this theorem; no §4.3, no `ExtendsDomain`, no
producer. -/
theorem directed_labelledExt (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x y : R.LabelledExt) :
    ∃ z : R.LabelledExt, x ≤ z ∧ y ≤ z := by
  obtain ⟨z, hxz, g, hg⟩ := exists_labelledExt_le hcons hcov x y.tuple
  refine ⟨z, hxz, g, hg, ?_⟩
  have h := hcons z.tuple z.type g z.eval_eq
  rw [hg, y.eval_eq] at h
  exact h.symm

/-- Convenience wrapper of `directed_labelledExt` for a full model. -/
theorem IsModel.directed_labelledExt (hR : R.IsModel) (x y : R.LabelledExt) :
    ∃ z : R.LabelledExt, x ≤ z ∧ y ≤ z :=
  KnightRealization.directed_labelledExt hR.consistent hR.covering x y

/-- A covering realization has labelled covers (clause (3) alone suffices: it labels an
extension of the empty tuple). -/
theorem nonempty_labelledExt (hcov : R.IsInitialSegmentCovering) : Nonempty R.LabelledExt := by
  obtain ⟨k, u, -, husome⟩ := hcov (Function.Embedding.ofIsEmpty : Fin 0 ↪ M)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp husome
  exact ⟨⟨_, u, q, hq⟩⟩

/-- Convenience wrapper of `nonempty_labelledExt` for a full model. -/
theorem IsModel.nonempty_labelledExt (hR : R.IsModel) : Nonempty R.LabelledExt :=
  KnightRealization.nonempty_labelledExt hR.covering

/-! ### Dominating and coinitial sets of covers (Def. 5.3.9 / Cor. 5.3.8 vocabulary) -/

/-- A set of labelled covers is **dominating** when every labelled cover has a member above it
(Def. 5.3.9's "dominating set"; for a model this quantification over labelled covers agrees
with quantification over arbitrary tuples, `isDominating_iff` — the form
`StabilizesTo` uses). -/
def IsDominating (D : Set R.LabelledExt) : Prop :=
  ∀ x : R.LabelledExt, ∃ y ∈ D, x ≤ y

/-- A set of labelled covers is **coinitial** when above every labelled cover it contains a
whole principal tail (Cor. 5.3.8's "coinitial set"): every cover has an extension past which
*all* covers are members.  Unlike dominating sets, coinitial sets are closed under finite
intersection (`IsCoinitial.inter`) — they form a filter with the tails
(`isCoinitial_tail`). -/
def IsCoinitial (D : Set R.LabelledExt) : Prop :=
  ∀ x : R.LabelledExt, ∃ y, x ≤ y ∧ y.tail ⊆ D

/-- The actual cover order supplies Mathlib's directed-order interface. -/
theorem labelledExt_isDirectedOrder (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) : IsDirectedOrder R.LabelledExt :=
  ⟨directed_labelledExt hcons hcov⟩

/-- Knight's coinitial tails are precisely eventual properties of the cover filter. -/
theorem isCoinitial_iff_eventually (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (D : Set R.LabelledExt) :
    IsCoinitial D ↔ ∀ᶠ x in Filter.atTop, x ∈ D := by
  let := nonempty_labelledExt hcov
  let := labelledExt_isDirectedOrder hcons hcov
  constructor
  · intro h
    obtain ⟨y, _, hy⟩ := h (Classical.arbitrary R.LabelledExt)
    exact Filter.eventually_atTop.mpr ⟨y, hy⟩
  · intro h x
    obtain ⟨y, hy⟩ := Filter.eventually_atTop.mp h
    obtain ⟨z, hxz, hyz⟩ := exists_ge_ge x y
    exact ⟨z, hxz, fun w hw => hy w (hyz.trans hw)⟩

/-- Knight's domination is frequent membership in the same filter, not eventual membership. -/
theorem isDominating_iff_frequently (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (D : Set R.LabelledExt) :
    IsDominating D ↔ ∃ᶠ x in Filter.atTop, x ∈ D := by
  let := nonempty_labelledExt hcov
  let := labelledExt_isDirectedOrder hcons hcov
  rw [Filter.frequently_atTop]
  exact forall_congr' fun x => exists_congr fun y => and_comm

/-- A coinitial set is dominating (the trivial half of Cor. 5.3.8). -/
theorem IsCoinitial.isDominating {D : Set R.LabelledExt} (hD : IsCoinitial D) :
    IsDominating D := fun x => by
  obtain ⟨y, hxy, hy⟩ := hD x
  exact ⟨y, hy (le_refl y), hxy⟩

/-- Domination over labelled covers is domination over **arbitrary tuples** — the
quantification `StabilizesTo` (Def. 5.3.9) uses (minimal hypotheses — clauses (2) and (3)
suffice).  Forward: absorb the tuple into a labelled cover (covering) and dominate it;
backward: apply to the cover's own tuple and read the label back (consistency). -/
theorem isDominating_iff (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {D : Set R.LabelledExt} :
    IsDominating D ↔
      ∀ {m : ℕ} (s : Fin m ↪ M), ∃ y ∈ D, ∃ g : Fin m ↪ Fin y.arity, g.trans y.tuple = s := by
  constructor
  · intro hD m s
    obtain ⟨k, u, hu, husome⟩ := hcov s
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp husome
    obtain ⟨y, hyD, f, hf, -⟩ := hD ⟨_, u, q, hq⟩
    have hf' : f.trans y.tuple = u := hf
    refine ⟨y, hyD, (Fin.castAddEmb k).trans f, ?_⟩
    rw [Function.Embedding.trans_assoc, hf']
    exact hu
  · intro h x
    obtain ⟨y, hyD, g, hg⟩ := h x.tuple
    refine ⟨y, hyD, g, hg, ?_⟩
    have h' := hcons y.tuple y.type g y.eval_eq
    rw [hg, x.eval_eq] at h'
    exact h'.symm

/-- Convenience wrapper of `isDominating_iff` for a full model. -/
theorem IsModel.isDominating_iff (hR : R.IsModel) {D : Set R.LabelledExt} :
    IsDominating D ↔
      ∀ {m : ℕ} (s : Fin m ↪ M), ∃ y ∈ D, ∃ g : Fin m ↪ Fin y.arity, g.trans y.tuple = s :=
  KnightRealization.isDominating_iff hR.consistent hR.covering

/-- The poset form of the **Lemma 5.3.7 ratchet**: once membership is lost above a member, it
never returns.  (Lemma 5.3.7's "on a larger cover the provisional value stays fixed or jumps
to `≥ α + K^q`, irreversibly", stripped to the consequence Cor. 5.3.8 consumes.  Instantiating
this for the provisional-value sets `stableSet` is Lemma 5.3.7 proper — provisional-value row
arithmetic over given types, one of #51's later boundaries.) -/
def IsRatcheted (D : Set R.LabelledExt) : Prop :=
  ∀ ⦃x⦄, x ∈ D → ∀ ⦃y⦄, x ≤ y → y ∉ D → ∀ ⦃z⦄, y ≤ z → z ∉ D

/-- An upward-closed set is (vacuously) ratcheted. -/
theorem isRatcheted_of_upwardClosed {D : Set R.LabelledExt}
    (h : ∀ ⦃x y : R.LabelledExt⦄, x ≤ y → x ∈ D → y ∈ D) : IsRatcheted D :=
  fun _ hx _ hxy hy => absurd (h hxy hx) hy

/-- **Headline 2 — the dominating → coinitial upgrade** (the substantive half of Cor. 5.3.8):
a dominating, ratcheted set of covers is coinitial.  Above any cover pick a member `y`; if
some `z ≥ y` were outside, the ratchet would keep every cover above `z` outside — but the set
dominates a cover above `z`.  Pure order theory over the poset of headline 1; the model enters
through domination (Def. 5.3.9) and, later, through the ratchet instance (Lemma 5.3.7). -/
theorem IsDominating.isCoinitial {D : Set R.LabelledExt} (hD : IsDominating D)
    (hr : IsRatcheted D) : IsCoinitial D := by
  intro x
  obtain ⟨y, hyD, hxy⟩ := hD x
  refine ⟨y, hxy, fun z hz => ?_⟩
  by_contra hzD
  obtain ⟨w, hwD, hzw⟩ := hD z
  exact hr hyD hz hzD hzw hwD

/-- **Cor. 5.3.8** (both halves, over the ratchet): a ratcheted set of covers is coinitial iff
it is dominating.  Proved from model-internal directedness vocabulary alone — the printed
"amalgamation" citation is not used (`directed_labelledExt` supplies everything the
surrounding filter arguments need). -/
theorem isCoinitial_iff_isDominating {D : Set R.LabelledExt} (hr : IsRatcheted D) :
    IsCoinitial D ↔ IsDominating D :=
  ⟨IsCoinitial.isDominating, fun hD => hD.isCoinitial hr⟩

/-! ### Finite intersections of coinitial tails -/

/-- Coinitial sets are closed under (binary) intersection: pass to a tail for the first set,
then a further tail for the second. -/
theorem IsCoinitial.inter {D E : Set R.LabelledExt} (hD : IsCoinitial D)
    (hE : IsCoinitial E) : IsCoinitial (D ∩ E) := by
  intro x
  obtain ⟨y, hxy, hyD⟩ := hD x
  obtain ⟨z, hyz, hzE⟩ := hE y
  exact ⟨z, hxy.trans hyz, fun w hw => ⟨hyD (hyz.trans hw), hzE hw⟩⟩

theorem isCoinitial_univ : IsCoinitial (Set.univ : Set R.LabelledExt) :=
  fun x => ⟨x, le_refl x, fun _ _ => Set.mem_univ _⟩

/-- Coinitial sets are closed under **finite** intersection (the filter fact of Cor. 5.3.8
that Lemma 5.3.10's "sufficiently large cover" selection needs — one coinitial set per cell of
the finite `dom p`; dominating sets are not so closed). -/
theorem isCoinitial_biInter {ι : Type*} (s : Finset ι) {D : ι → Set R.LabelledExt} :
    (∀ i ∈ s, IsCoinitial (D i)) → IsCoinitial (⋂ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using isCoinitial_univ
  | @insert a s ha ih =>
    intro h
    rw [Finset.set_biInter_insert]
    exact (h a (Finset.mem_insert_self a s)).inter
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Every principal tail is coinitial (minimal hypotheses — clauses (2) and (3) suffice; this
is where headline 1's directedness enters: the common extension of the base point and any
cover starts a tail inside the given tail).  With `IsCoinitial.inter`, the tails of the
labelled covers generate a filter. -/
theorem isCoinitial_tail (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x : R.LabelledExt) : IsCoinitial x.tail := by
  intro y
  obtain ⟨z, hxz, hyz⟩ := directed_labelledExt hcons hcov x y
  exact ⟨z, hyz, fun w hw => hxz.trans hw⟩

/-- Convenience wrapper of `isCoinitial_tail` for a full model. -/
theorem IsModel.isCoinitial_tail (hR : R.IsModel) (x : R.LabelledExt) :
    IsCoinitial x.tail :=
  KnightRealization.isCoinitial_tail hR.consistent hR.covering x

/-- **Headline 3 — finite intersections of coinitial tails are coinitial** (minimal
hypotheses — clauses (2) and (3) suffice). -/
theorem isCoinitial_biInter_tail (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {ι : Type*} (s : Finset ι)
    (x : ι → R.LabelledExt) : IsCoinitial (⋂ i ∈ s, (x i).tail) :=
  isCoinitial_biInter s fun i _ => isCoinitial_tail hcons hcov (x i)

/-- Convenience wrapper of `isCoinitial_biInter_tail` for a full model. -/
theorem IsModel.isCoinitial_biInter_tail (hR : R.IsModel) {ι : Type*} (s : Finset ι)
    (x : ι → R.LabelledExt) : IsCoinitial (⋂ i ∈ s, (x i).tail) :=
  KnightRealization.isCoinitial_biInter_tail hR.consistent hR.covering s x

/-! ### The stabilization sets of Def. 5.3.9 on the poset -/

/-- The **stabilization set** of a cell: the labelled covers extending `x` on which the
transported cell has provisional value `γ` (relationally, `IsProvisionalValue` — no chooser).
This is Def. 5.3.9's value set as a subset of the labelled-cover poset; `StabilizesTo` says
exactly that it is dominating (`stabilizesTo_iff_isDominating`).  Every member lies
above `x` by construction. -/
def stableSet (x : R.LabelledExt) (Xi : Cell x.type.scheme.scheme) (γ : ExtOrd) :
    Set R.LabelledExt :=
  {y | ∃ (f : Fin x.arity ↪ Fin y.arity) (_ : f.trans y.tuple = x.tuple)
    (hpq : typeMap f y.type = some x.type),
    y.type.IsProvisionalValue (mapCell hpq Xi) γ}

/-- **Def. 5.3.9's dominating form is poset domination** (minimal hypotheses — clauses (2)
and (3) suffice): the provisional values of `Ξ` stabilize to `γ` over `x` (`StabilizesTo`,
quantifying over arbitrary tuples) iff the stabilization set is dominating in the
labelled-cover poset.  This pins the ambient poset of the §5.3 arguments once: the coinitial
upgrade (headline 2) and tail intersections (headline 3) then apply to these sets as soon as
the Lemma 5.3.7 ratchet instance lands. -/
theorem stabilizesTo_iff_isDominating (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x : R.LabelledExt)
    (Xi : Cell x.type.scheme.scheme) (γ : ExtOrd) :
    R.StabilizesTo x.tuple x.type Xi γ ↔ IsDominating (stableSet x Xi γ) := by
  constructor
  · intro H x'
    obtain ⟨m', u, g, f, q, hpq, hq, hgu, hfu, hval⟩ := H x'.tuple
    refine ⟨⟨_, u, q, hq⟩, ⟨f, hfu, hpq, hval⟩, g, hgu, ?_⟩
    have h := hcons u q g hq
    rw [hgu, x'.eval_eq] at h
    exact h.symm
  · intro hD m s
    obtain ⟨k, u₀, hu₀, husome⟩ := hcov s
    obtain ⟨q₀, hq₀⟩ := Option.isSome_iff_exists.mp husome
    obtain ⟨z, hzD, e, he, -⟩ := hD ⟨_, u₀, q₀, hq₀⟩
    have he' : e.trans z.tuple = u₀ := he
    obtain ⟨f, hf, hpq, hval⟩ := hzD
    refine ⟨z.arity, z.tuple, (Fin.castAddEmb k).trans e, f, z.type, hpq, z.eval_eq, ?_,
      hf, hval⟩
    rw [Function.Embedding.trans_assoc, he']
    exact hu₀

/-- Convenience wrapper of `stabilizesTo_iff_isDominating` for a full model. -/
theorem IsModel.stabilizesTo_iff_isDominating (hR : R.IsModel) (x : R.LabelledExt)
    (Xi : Cell x.type.scheme.scheme) (γ : ExtOrd) :
    R.StabilizesTo x.tuple x.type Xi γ ↔ IsDominating (stableSet x Xi γ) :=
  KnightRealization.stabilizesTo_iff_isDominating hR.consistent hR.covering x Xi γ

/-! ### Top-grade growth -/

/-- The **growth set** at threshold `K`: the labelled covers whose label has top grade
(Def. 5.3.1's `K^p`) strictly above `K`.  Upward closed by `topGrade_mono`. -/
def growthSet (R : KnightRealization α M) (K : ℕ) : Set R.LabelledExt :=
  {y | K < y.type.topGrade}

theorem growthSet_upwardClosed {K : ℕ} :
    ∀ ⦃x y : R.LabelledExt⦄, x ≤ y → x ∈ R.growthSet K → y ∈ R.growthSet K :=
  fun _ _ h hx => lt_of_lt_of_le hx (LabelledExt.topGrade_mono h)

/-- The **growth branch** of Lemma 5.3.10's dichotomy, in dominating form (mirroring
`StabilizesTo`): for every `K` there are dominating covers of top grade `> K`.  The
alternative branch — `K^q` eventually constant — is Case 1 of Lemma 5.3.10 (no second witness
needed); the split between them is classical control flow in the consumer (#51 boundary 3),
never a theorem-milestone here. -/
def HasTopGradeGrowth (R : KnightRealization α M) : Prop :=
  ∀ K : ℕ, IsDominating (R.growthSet K)

/-- **Headline 4 — sufficiently large covers exhibit top-grade growth**: under the growth
branch, the growth sets are not merely dominating but **coinitial** — above every labelled
cover there is a cover past which *every* labelled cover has top grade `> K`.  The upgrade is
free of any ratchet hypothesis: monotonicity of `K^p` (`topGrade_le_of_typeMap_eq_some`) makes
the growth sets upward closed, and upward-closed dominating sets are coinitial.  This is what
Lemma 5.3.10(2b) intersects with the stabilization tails to select its larger cover and its
strictly-higher-grade full-scope `∞`-cell. -/
theorem HasTopGradeGrowth.isCoinitial_growthSet (h : R.HasTopGradeGrowth) (K : ℕ) :
    IsCoinitial (R.growthSet K) :=
  (h K).isCoinitial (isRatcheted_of_upwardClosed growthSet_upwardClosed)

/-- The tuple-quantified reading of the growth branch (the recon's Lean shape: "for every `K`,
every tuple has a labelled common extension `u` with type `q` and `K < K^q`"; minimal
hypotheses — clauses (2) and (3) suffice). -/
theorem hasTopGradeGrowth_iff (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) :
    R.HasTopGradeGrowth ↔
      ∀ (K : ℕ) {m : ℕ} (s : Fin m ↪ M),
        ∃ (m' : ℕ) (u : Fin m' ↪ M) (g : Fin m ↪ Fin m') (q : S α.1 m'),
          R.eval u = some q ∧ g.trans u = s ∧ K < q.topGrade := by
  constructor
  · intro h K m s
    obtain ⟨y, hyK, g, hg⟩ := ((isDominating_iff hcons hcov).mp (h K)) s
    exact ⟨y.arity, y.tuple, g, y.type, y.eval_eq, hg, hyK⟩
  · intro h K
    refine (isDominating_iff hcons hcov).mpr fun {m} s => ?_
    obtain ⟨m', u, g, q, hq, hgu, hK⟩ := h K s
    exact ⟨⟨_, u, q, hq⟩, hK, g, hgu⟩

/-- Convenience wrapper of `hasTopGradeGrowth_iff` for a full model. -/
theorem IsModel.hasTopGradeGrowth_iff (hR : R.IsModel) :
    R.HasTopGradeGrowth ↔
      ∀ (K : ℕ) {m : ℕ} (s : Fin m ↪ M),
        ∃ (m' : ℕ) (u : Fin m' ↪ M) (g : Fin m ↪ Fin m') (q : S α.1 m'),
          R.eval u = some q ∧ g.trans u = s ∧ K < q.topGrade :=
  KnightRealization.hasTopGradeGrowth_iff hR.consistent hR.covering

end KnightRealization

end VaughtConjecture.Knight
