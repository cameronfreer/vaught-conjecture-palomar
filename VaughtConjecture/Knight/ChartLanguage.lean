/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model
public import InfinitaryLogic.Scott.AtomicDiagram

/-! # Stage chart languages (#137)

At the terminal semantic boundary, a Knight stage type `p ∈ S^α_n` can be read as an ordinary
`n`-ary **relation symbol** — a *chart* — and a realization as an ordinary relational structure
in the resulting language.  This module defines that encoding at every limit stage and connects
exact face consistency to `InfinitaryLogic`'s standard atomic-diagram API:

* `stageLang α` — the relational chart language at the limit stage `α`
  (`Relations n := S α n`, no function symbols); countable when the stage is
  (`stageLang.countable_relations`);
* `stageStructureOf R` — the chart structure of a realization: `P_p(x̄)` iff `x̄` is injective
  and `R.eval x̄ = some p`;
* `stageStructureEquivOfIsIso` / `isIsoOfStageStructureEquiv` — realization isomorphisms
  correspond to chart-structure isomorphisms, in both directions.  The encoding *reflects*
  isomorphism without modelhood or transfer hypotheses: a language isomorphism of
  `stageStructureOf` structures already transports the complete `Option`-valued labelling;
* `HasCommonChart` and `sameAtomicType_of_commonChart` — a common full/projected chart implies
  equality of the complete atomic diagram (`SameAtomicType`).  Exact face consistency is
  precisely strong enough: invisible faces become *negative* atomic facts
  (`stageHolds_comp_iff_of_eval`), and repeated-coordinate projections are handled by the
  selector `σ`;
* `hasCommonChart_of_eval_eq_some` — two injective tuples literally evaluated to the same stage
  type carry a common (full) chart, so a producer theorem whose conclusion is an exact
  request-face equation already closes the certificate.

**Never identify** (#137): `S α n` is **not** a complete first-order
type — horizontal restriction is partial and request families are not Boolean completions; the
charts are *atomic relation symbols only*.  Equality of complete types does not replace
forth/back: the semantic consumer of this encoding is `InfinitaryLogic`'s `PotentialIso`
(`Knight/ChartKarp.lean`), whose compatibility field is exactly `SameAtomicType`.  No claim is
made that two occurrences of one chart have the same quantified extension behaviour — that is a
producer transfer theorem, not a consequence of this encoding. -/

@[expose] public section

namespace VaughtConjecture.Knight

open FirstOrder Language Structure TypeTower

universe w w'

/-- The relational chart language at a limit stage `α`, with one `n`-ary relation for each
stage type in `S α n`. -/
def stageLang (α : LimitStage) : Language.{0, 1} where
  Functions _ := Empty
  Relations n := S α.1 n

instance stageLang.isRelational (α : LimitStage) : (stageLang α).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

/-- A countable stage has a countable chart language. -/
theorem stageLang.countable_relations (α : LimitStage)
    (hα : α.1.card ≤ Cardinal.aleph0) : Countable (Σ n, (stageLang α).Relations n) := by
  let (n : ℕ) : Countable (S α.1 n) := StageType.countable_S hα n
  change Countable (Σ n, S α.1 n)
  infer_instance

/-- The relation `P_p` holds of a tuple in a stage chart structure. -/
abbrev StageHolds {α : LimitStage} {M : Type w} [(stageLang α).Structure M] {n : ℕ}
    (p : S α.1 n) (xs : Fin n → M) : Prop :=
  RelMap (L := stageLang α) (n := n) p xs

/-- The chart-language structure associated to a Knight realization: `P_p(x̄)` means that
`x̄` is injective and the realization labels it by `p`. -/
@[instance_reducible] noncomputable def stageStructureOf {α : LimitStage} {M : Type w}
    (R : KnightRealization α M) : (stageLang α).Structure M where
  funMap f := isEmptyElim f
  RelMap p xs := ∃ h : Function.Injective xs, R.eval ⟨xs, h⟩ = some p

theorem stageHolds_stageStructureOf {α : LimitStage} {M : Type w}
    (R : KnightRealization α M) {n : ℕ} (p : S α.1 n) (xs : Fin n → M) :
    @StageHolds α M (stageStructureOf R) n p xs ↔
      ∃ h : Function.Injective xs, R.eval ⟨xs, h⟩ = some p :=
  Iff.rfl

/-- An isomorphism of realizations induces an isomorphism of their stage chart structures. -/
def stageStructureEquivOfIsIso {α : LimitStage} {M : Type w} {N : Type w'}
    {R : KnightRealization α M} {R' : KnightRealization α N} {e : M ≃ N}
    (h : R.IsIso R' e) :
    @Language.Equiv (stageLang α) M N (stageStructureOf R) (stageStructureOf R') :=
  @Language.Equiv.mk (stageLang α) M N (stageStructureOf R) (stageStructureOf R') e
    (fun f => isEmptyElim f) fun {n} p xs => by
      change (∃ hi : Function.Injective (⇑e ∘ xs), R'.eval ⟨⇑e ∘ xs, hi⟩ = some p) ↔
        ∃ hi : Function.Injective xs, R.eval ⟨xs, hi⟩ = some p
      constructor
      · rintro ⟨hi, hp⟩
        exact ⟨hi.of_comp, (h ⟨xs, hi.of_comp⟩).symm.trans hp⟩
      · rintro ⟨hi, hp⟩
        exact ⟨e.injective.comp hi, (h ⟨xs, hi⟩).trans hp⟩

/-- The stage chart encoding reflects isomorphisms: an isomorphism of chart structures already
transports every `Option`-valued realization label.  No modelhood or transfer hypothesis is
needed. -/
theorem isIsoOfStageStructureEquiv {α : LimitStage} {M : Type w} {N : Type w'}
    {R : KnightRealization α M} {R' : KnightRealization α N}
    (e : @Language.Equiv (stageLang α) M N (stageStructureOf R) (stageStructureOf R')) :
    R.IsIso R'
      (@Language.Equiv.toEquiv (stageLang α) M N (stageStructureOf R) (stageStructureOf R') e) := by
  let instM : (stageLang α).Structure M := stageStructureOf R
  let instN : (stageLang α).Structure N := stageStructureOf R'
  let e' : M ≃[stageLang α] N := e
  intro n t
  let ee : M ≃ N := e'.toEquiv
  have key : ∀ p : S α.1 n,
      @StageHolds α N instN n p (⇑e' ∘ ⇑t) ↔ @StageHolds α M instM n p t :=
    fun p => StrongHomClass.map_rel e' p t
  change R'.eval (t.trans ee.toEmbedding) = R.eval t
  apply Option.ext
  intro p
  constructor
  · intro ht
    have htarget : @StageHolds α N instN n p (⇑e' ∘ ⇑t) := by
      refine ⟨e'.toEquiv.injective.comp t.injective, ?_⟩
      have he : (⟨⇑e' ∘ ⇑t, e'.toEquiv.injective.comp t.injective⟩ : Fin n ↪ N) =
          t.trans ee.toEmbedding := by ext i; rfl
      rwa [he]
    obtain ⟨hsrc, hsource⟩ := (key p).mp htarget
    have he : (⟨⇑t, hsrc⟩ : Fin n ↪ M) = t := by ext i; rfl
    rwa [he] at hsource
  · intro hs
    have hsource : @StageHolds α M instM n p t := ⟨t.injective, hs⟩
    obtain ⟨htgt, htarget⟩ := (key p).mpr hsource
    have he : (⟨⇑e' ∘ ⇑t, htgt⟩ : Fin n ↪ N) = t.trans ee.toEmbedding := by ext i; rfl
    rwa [he] at htarget

/-- Exact face consistency determines every relation atom on every (possibly repeated)
subtuple of a labelled injective tuple.  A visible face gives its unique pulled-back label;
an invisible face gives no label (a *negative* atomic fact), and a repeated subtuple satisfies
no chart relation.  Visible-face consistency alone would not prove the negative facts. -/
theorem stageHolds_comp_iff_of_eval {α : LimitStage} {M : Type w}
    {R : KnightRealization α M} (hR : R.IsExactParentConsistent)
    {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} (ht : R.eval t = some p)
    {m : ℕ} (q : S α.1 m) (f : Fin m → Fin n) :
    @StageHolds α M (stageStructureOf R) m q (t ∘ f) ↔
      ∃ hf : Function.Injective f, typeMap ⟨f, hf⟩ p = some q := by
  rw [stageHolds_stageStructureOf]
  constructor
  · rintro ⟨htf, hq⟩
    have hf : Function.Injective f := fun i j hij => htf (by simp [hij])
    refine ⟨hf, ?_⟩
    have hface := hR t p (⟨f, hf⟩ : Fin m ↪ Fin n) ht
    have he : (⟨t ∘ f, htf⟩ : Fin m ↪ M) = (⟨f, hf⟩ : Fin m ↪ Fin n).trans t := by
      ext i
      rfl
    rw [he] at hq
    exact hface.symm.trans hq
  · rintro ⟨hf, hq⟩
    have htf : Function.Injective (t ∘ f) := t.injective.comp hf
    refine ⟨htf, ?_⟩
    have hface := hR t p (⟨f, hf⟩ : Fin m ↪ Fin n) ht
    have he : (⟨t ∘ f, htf⟩ : Fin m ↪ M) = (⟨f, hf⟩ : Fin m ↪ Fin n).trans t := by
      ext i
      rfl
    rw [he]
    exact hface.trans hq

/-- Two labelled tuples carrying the same full chart have the same atomic chart-language type.
This includes equality atoms, repeated relation tuples, and invisible faces. -/
theorem sameAtomicType_of_eval_eq_some {α : LimitStage} {M : Type w} {N : Type w'}
    {R : KnightRealization α M} {R' : KnightRealization α N}
    (hR : R.IsExactParentConsistent) (hR' : R'.IsExactParentConsistent)
    {n : ℕ} {a : Fin n ↪ M} {b : Fin n ↪ N} {p : S α.1 n}
    (ha : R.eval a = some p) (hb : R'.eval b = some p) :
    @SameAtomicType (stageLang α) M (stageStructureOf R) n N (stageStructureOf R') a b := by
  intro idx
  cases idx with
  | eq i j =>
      simp only [AtomicIdx.holds]
      constructor <;> intro hij
      · exact congrArg b (a.injective hij)
      · exact congrArg a (b.injective hij)
  | rel q f =>
      exact (stageHolds_comp_iff_of_eval hR ha q f).trans
        (stageHolds_comp_iff_of_eval hR' hb q f).symm

/-- A common projected chart for two tuples: each tuple is the same coordinate projection of
an injective tuple carrying one common full chart.  The selector may repeat coordinates, so this
also covers arbitrary finite tuples rather than only embeddings. -/
def HasCommonChart {α : LimitStage} {M : Type w} {N : Type w'}
    (R : KnightRealization α M) (R' : KnightRealization α N) {n : ℕ}
    (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∃ (m : ℕ) (ta : Fin m ↪ M) (tb : Fin m ↪ N) (σ : Fin n → Fin m) (p : S α.1 m),
    R.eval ta = some p ∧ R'.eval tb = some p ∧ ta ∘ σ = a ∧ tb ∘ σ = b

/-- Two injective tuples evaluated as the same stage type have a common full chart.  Thus a
producer theorem whose conclusion is the literal request-face equation already closes the
chart certificate required by the semantic adapter. -/
theorem hasCommonChart_of_eval_eq_some {α : LimitStage} {M : Type w} {N : Type w'}
    {R : KnightRealization α M} {R' : KnightRealization α N}
    {n : ℕ} {a : Fin n ↪ M} {b : Fin n ↪ N} {p : S α.1 n}
    (ha : R.eval a = some p) (hb : R'.eval b = some p) :
    HasCommonChart R R' a b := by
  refine ⟨n, a, b, id, p, ha, hb, ?_, ?_⟩ <;> funext i <;> rfl

/-- Common projected charts determine the complete atomic diagram in the chart language. -/
theorem sameAtomicType_of_commonChart {α : LimitStage} {M : Type w} {N : Type w'}
    {R : KnightRealization α M} {R' : KnightRealization α N}
    (hR : R.IsExactParentConsistent) (hR' : R'.IsExactParentConsistent)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} (h : HasCommonChart R R' a b) :
    @SameAtomicType (stageLang α) M (stageStructureOf R) n N (stageStructureOf R') a b := by
  let instM : (stageLang α).Structure M := stageStructureOf R
  let instN : (stageLang α).Structure N := stageStructureOf R'
  obtain ⟨m, ta, tb, σ, p, hta, htb, ha, hb⟩ := h
  have hfull := (sameAtomicType_of_eval_eq_some hR hR' hta htb).relabel σ
  simpa only [ha, hb] using hfull

end VaughtConjecture.Knight
