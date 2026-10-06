/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Order.Lattice.Nat
public import VaughtConjecture.Knight.Model

/-! # Terminal invariants: provisional values, characteristic arity, anchors, hollowness

The invariants Knight reads off a model at (what will be) its stopping level (#48; parent #9):

* **provisional values** `p⁺` (Def. 5.3.1): for a stage type `p ∈ S^α_n`, the guess — made from
  `p` alone — at what an expansion to `S^{α+ω}` could assign to each cell labelled `∞`
  (`StageType.someProvisionalValue`, with the paper's `K^p` as `StageType.topGrade`);
* **stabilized values** (Def. 5.3.9, graph form): the value `M⁺(Ξ)` — `γ` if the provisional
  values of (the images of) `Ξ` are `γ` on a dominating set of labelled extensions, `∞`
  otherwise (`KnightRealization.StabilizesTo`, `HasStableValue`);
* **characteristic arity** (Def. 5.4.1): `K ∈ ω ∪ {∞}` with `α + K` the supremum of all
  stabilized values, `∞` if no finite `K` works (`KnightRealization.IsCharacteristicArity`
  in `IsLUB` form, `characteristicArity : ℕ∞`);
* **anchor at infinity** and **hollowness** (Def. 5.4.2): a cell minimal at infinity for the
  semantic rows of all high-grade `∞`-cells over all extensions
  (`KnightRealization.IsInfinityAnchor`, `HasInfinityAnchor`); `M` is **hollow** iff no anchor
  at infinity exists (`KnightRealization.IsHollow`).

All of it is proved isomorphism-invariant (the acceptance test of #48), through the single
bundled transport `IsIso.terminalProfile_eq` — see *One datum, one profile* below.

## Paper fidelity (the guardrails of #48)

These are transcriptions of Knight's §5.3–§5.4, **not** Knight-VC's cash-outs:

* `characteristicArity` is Def. 5.4.1 (supremum of the stabilized provisional values), **not**
  Knight-VC's `charArity` (the *distinguishing* arity: the supremum of arities at which tuples
  agreeing on proper faces receive different types) — banned identification 2 of
  `docs/TERMINOLOGY.md`.
* `IsHollow` is Def. 5.4.2 (no anchor at infinity), **not** orbit homogeneity (Knight-VC's
  `IsHollow`, since renamed `IsOrbitHomogeneous` there) — banned identification 1.  Orbit
  homogeneity and distinguishing arity are *not defined in this module at all* (`docs/DESIGN.md`
  §7: diagnostics only, never terminal invariants).
* `someProvisionalValue` is **cell-dependent**, as in Def. 5.3.1 — clause 2.(a) caps at `α + K^p`
  with `K^p` computed from `p`, clause 2.(b) reads the band index off the semantic row of a
  full-scope `∞`-cell of grade `K^p`.  Knight-VC's `topLiftType` applied a uniform cap
  (KVC-d3, sibling-only); that reroute is not re-imported.

Deviations / readings, recorded (`docs/CONCORDANCE.md` §5.3–§5.4):

* Def. 5.3.1 leaves clause 2 without a value when neither subclause applies; here the
  definition falls back to `⊤`, and `StageType.exists_provisionalBand` proves the fallback
  **unreachable** (clause 2 is total: availability of Def. 2.5.4(2) plus completeness of
  Def. 2.5.15 produce a full-scope `∞`-cell of grade `K^p` whose row decides `Ξ`), so
  `someProvisionalValue` never takes the value `⊤` (`someProvisionalValue_ne_top`) and is bounded by
  `α + K^p` (`someProvisionalValue_le`) — the paper's `p⁺(Ξ) ∈ {-∞} ∪ (α + ω) `.
* Lemma 5.3.2 (the band index is independent of the witnessing cell `Θ`) is a consistency
  theorem the paper needs for well-definedness; here the definition selects the **least** band
  index, so it is deterministic without that lemma, which can be proved later (#51)
  as `ProvisionalBand p Ξ i → ProvisionalBand p Ξ j → i = j` under `¬ ProvisionalCap`.
* Def. 5.3.9's "dominating (equivalently coinitial) set of finite subsets `A`" is transcribed
  on tuples: every tuple `s` admits a labelled common extension of `s` and the base tuple on
  which the transported provisional value is `γ` (`StabilizesTo`).  The equivalence of the
  dominating and coinitial readings (Cor. 5.3.8, via amalgamation) is a model theorem, not part
  of the definition.  Uniqueness of the stabilized value needs directedness of labelled
  extensions, i.e. the model axioms — a §5.3 lemma for #51, not assumed here.
* Def. 5.4.2's anchor is required to satisfy `p(∞̃) = ∞` (`IsInfinityAnchor.label_top`).  The
  printed definition does not state this clause, but it is implicit in the notation `∞̃`, in the
  surrounding Uniformity discussion (the candidate values are the `M⁺(Ξ)` of cells with
  `M(Ξ) = ∞`), and in the proof of Lemma 5.5.1 (which reads `M⁺(∞̃) ∈ [α, α+ω) ∪ {∞}`,
  excluding `M⁺(∞̃) < α` without comment).
* Def. 5.4.2 is framed "suppose `M` is a model of `S^α` of characteristic arity `K`,
  `0 < K ≤ ∞`"; the predicates here are stated for every Knight realization, and the framing
  hypothesis belongs to the consumers (the prolongation-or-defect split, #52).

## One datum, one profile (review requirement on #48)

Every invariant of this module is computed from **one level-owned datum**: the realization
`R : KnightRealization α M` itself (once histories land — #30/#31 — the terminal witness at the
stopping level `blockLevel (stopRank R)`, `Knight/Rank.lean`).  No invariant chooses its own
witness: `StabilizesTo`, `IsCharacteristicArity` and `IsInfinityAnchor` are intrinsic `∀`/`∃`
statements over the labelled tuples of the same `R`.  The derived invariants are bundled in a
single record, `TerminalProfile`, produced by the single function
`KnightRealization.terminalProfile`; characteristic arity and hollowness are its projections,
and isomorphism transport is proved **once**, for the profile
(`IsIso.terminalProfile_eq`, `terminalProfile_eq_of_iso`), with
`characteristicArity_eq_of_iso` and `isHollow_iff_of_iso` inherited as projections.  Knight-VC's
literal branch showed that independently chosen witnesses for the three terminal invariants are
a coherence trap; this module keeps a single source of truth.  **Core data** (finite cores,
Def. 7.3.1 — banned identification 3: a finite core is not a root type) belongs to §7; its
eventual shared owner is the **linked stop / terminal realization** (#31), not this record —
no promise is made that a chosen core becomes another `TerminalProfile` field.  `TerminalCode`
(#57) encodes the *classified branch*, built from this profile together with the core
information owned by the linked stop; whatever owns the core, it must be derived from the
shared datum, never an independently chosen witness.

## Review boundary: no canonical expansion is assumed

Knight's **literal** invariants are defined without silently assuming a canonical expansion:

* the definitions are functions of an **explicitly supplied level-owned datum** — the
  realization `R` (the terminal witness, once the block-step/history layer #30/#51 supplies
  it); nothing here presupposes that an expansion `M⁺` exists, is unique, or is canonical;
* no invariant is obtained by a noncanonical choice: `someProvisionalValue` is a deterministic
  rule on `p`'s own rows (`Classical` enters only as *decidability of the defining
  propositions*, never as a `Classical.choice`-selected witness; the branch value is uniquely
  characterized — cap, else the least band index), `characteristicArity` reads the unique `K`
  of `IsCharacteristicArity` (`IsCharacteristicArity.unique`), and Def. 5.3.9 enters only as
  a **graph** (`HasStableValue`), never as a chosen function;
* **deferred obligations (named, not proved here, no surrogate proved instead)**:
  1. *stabilized-value functionality* — for models, `HasStableValue` is single-valued
     (directedness of labelled extensions; Lemma 5.3.7 / Cor. 5.3.8) — **proved**:
     `HasStableValue.unique` (`Knight/ProvisionalRatchet.lean`);
  2. *band-index independence* (Lemma 5.3.2: the clause 2.(b) index does not depend on the
     witnessing `Θ`) — a consistency theorem, **proved**: `ProvisionalBand.unique`,
     `IsProvisionalValue.unique` (`Knight/ProvisionalUniqueness.lean`; the definition does
     not need it: the least index is selected);
  3. *witness-choice independence of the terminal profile* — **removed from the promised
     obligations** (review 2026-08-24): under selected-code fibre counting (#57 chooses one
     representative, stop witness, branch datum and code per class, and proves only that equal
     selected codes give isomorphic sources), no independence theorem is needed; the profile
     describes the one supplied realization.  Universal expansion uniqueness (Lemma 5.5.2)
     remains a mainline cut.

## What awaits histories (#30/#31)

Nothing here depends on the stopping rank: the invariants are defined at every limit stage,
which is exactly the paper's setting (Defs. 5.4.1/5.4.2 are stated for models of `S^α`).  The
*terminal* reading — the profile of the terminal witness at `stopLevel R` — needs the selected
history/linked-stop layer to produce that witness; the classifier (#53/#57) will consume
`terminalProfile` of linked stops.  The expansion operator `M⁺` as a stage-type family
(Def. 5.3.9 as an *object*, Lemma 5.3.10) stays proof-internal (#51,
`docs/CONCORDANCE.md` §5.3); this module only defines its value graph. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd VaughtConjecture.AmalgamationPlan
open CellScheme.restrictFace (toCell)

universe w w'

/-! ### Transport of cells along a restriction

`typeMap f q = some p` exhibits `p` as the `f`-restriction of `q`; the paper treats the domain
of `p` as a literal subset of the domain of `q`, and `mapCell` is that inclusion in the indexed
encoding: the cell of `q` underlying a cell of `p` (`toCell` after transporting along the
restriction equation).  Labels and grades are preserved (`label_mapCell`, `grade_mapCell`) —
the encoded form of Def. 3.2.5 ("`M(Ξ)` is the value taken by `p(Ξ)` for all relevant `p`"). -/

namespace StageType

variable {α : Ordinal.{0}} {m n : ℕ}

/-- If `typeMap f q = some p`, the range of `f` is a visible face of the plan of `q`. -/
theorem visible_of_typeMap_eq_some {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) : Finset.univ.image f ∈ q.scheme.scheme.plan :=
  (typeMap_isSome_iff f q).mp (by rw [h]; rfl)

/-- If `typeMap f q = some p`, then `p` is the face restriction of `q` along `f`. -/
theorem restrictFace_eq_of_typeMap_eq_some {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) : q.restrictFace f (visible_of_typeMap_eq_some h) = p := by
  have h' := typeMap_eq_some f q (visible_of_typeMap_eq_some h)
  rw [h'] at h
  exact Option.some_injective _ h

/-- The cell of `q` underlying a cell of its restriction `p` (the paper's `Ξ ∈ dom p ⊆ dom q`):
transport along the restriction equation, then the cell map `toCell` of the face
restriction. -/
noncomputable def mapCell {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (Xi : Cell p.scheme.scheme) : Cell q.scheme.scheme :=
  toCell q.scheme.scheme f (visible_of_typeMap_eq_some h)
    (SemScheme.castCell (congrArg StageType.scheme (restrictFace_eq_of_typeMap_eq_some h).symm)
      Xi)

/-- The label of the underlying cell is the label of the restricted cell (Def. 3.2.5: the
cells of `dom p` carry the same values in `q`). -/
theorem label_mapCell {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (Xi : Cell p.scheme.scheme) :
    q.label (mapCell h Xi) = p.label Xi := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some h, restrictFace_eq_of_typeMap_eq_some h⟩
  rfl

/-- The grade of the underlying cell is the grade of the restricted cell. -/
theorem grade_mapCell {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (Xi : Cell p.scheme.scheme) :
    q.scheme.scheme.grade (mapCell h Xi) = p.scheme.scheme.grade Xi := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some h, restrictFace_eq_of_typeMap_eq_some h⟩
  rfl

/-! ### The top grade `K^p` and the provisional values `p⁺` (Def. 5.3.1)

For `p ∈ S^α_n` the information relevant to expanding beyond `α` is: which cells carry `∞`,
and the semantic rows of the full-scope `∞`-cells of maximal grade.  `K^p` is that maximal
grade; `p⁺(Ξ)` is the value in `[α, α + K^p]` that the rows force, if any. -/

/-- The grades of full-scope cells labelled `∞`: the set whose supremum is the paper's `K^p`
(Def. 5.3.1 clause 2: "`K^p` is the greatest natural number such that for some
`Θ ∈ D^{A,K^p}`, `p(Θ) = ∞`"). -/
def topGrades (p : S α n) : Set ℕ :=
  {k | ∃ Θ : Cell p.scheme.scheme, p.scheme.scheme.scope Θ = Finset.univ ∧
    p.scheme.scheme.grade Θ = k ∧ p.label Θ = ⊤}

theorem topGrades_bddAbove (p : S α n) : BddAbove p.topGrades := by
  refine ⟨n, fun k hk => ?_⟩
  obtain ⟨Θ, hsc, rfl, -⟩ := hk
  have h1 := p.scheme.scheme.grade_le_card_scope Θ
  rw [hsc] at h1
  simpa using h1

/-- The paper's `K^p` (Def. 5.3.1): the greatest grade of a full-scope `∞`-cell (`0` when
there is none — under clause 2 the set is nonempty, `grade_mem_topGrades`). -/
noncomputable def topGrade (p : S α n) : ℕ := sSup p.topGrades

/-- If any cell of `p` is labelled `∞`, some full-scope cell of the same grade is labelled `∞`
(availability, Def. 2.5.4(2), against the full-scope cell of that grade provided by
completeness, Def. 2.5.15) — so the defining set of `K^p` is nonempty whenever clause 2 of
Def. 5.3.1 applies. -/
theorem grade_mem_topGrades {p : S α n} {Xi : Cell p.scheme.scheme} (hXi : p.label Xi = ⊤) :
    p.scheme.scheme.grade Xi ∈ p.topGrades := by
  have hmem : ((Finset.univ : Finset (Fin n)), p.scheme.scheme.grade Xi) ∈
      Plan.gradedPlan p.scheme.scheme.plan := by
    refine Plan.mem_gradedPlan.mpr
      ⟨p.scheme.scheme.isPlan.domain_mem, p.scheme.scheme.grade_pos Xi, ?_⟩
    have h1 := p.scheme.scheme.grade_le_card_scope Xi
    exact h1.trans (Finset.card_le_card (Finset.subset_univ _))
  obtain ⟨d, hd⟩ := p.scheme.complete _ hmem
  have hd' := Prod.ext_iff.mp hd
  have hscope : p.scheme.scheme.scope Xi ⊆ p.scheme.scheme.scope d := by
    rw [show p.scheme.scheme.scope d = Finset.univ from hd'.1]
    exact Finset.subset_univ _
  have hgrade : p.scheme.scheme.grade Xi = p.scheme.scheme.grade d := hd'.2.symm
  obtain ⟨Xi', hcell, hle⟩ := p.respects.availability Xi d hscope hgrade
  have hXi' := Prod.ext_iff.mp (hcell.trans hd)
  refine ⟨Xi', hXi'.1, hXi'.2, ?_⟩
  rw [hXi] at hle
  exact top_le_iff.mp hle

/-- Clause 2.(a) of Def. 5.3.1: some full-scope `∞`-cell `Θ` of grade `K^p` sees, below
itself, an `∞`-cell `Σ` with `E(Θ)(Σ) ⊔⁺_{K^p} K^p ≤ E(Θ)(Ξ)` — the evidence in `p` that
`M⁺(Ξ)` is at least `α + K^p`.  Then `p⁺(Ξ) = α + K^p`. -/
def ProvisionalCap (p : S α n) (Xi : Cell p.scheme.scheme) : Prop :=
  ∃ (Θ : Cell p.scheme.scheme)
    (hXi : GradedLe (p.scheme.scheme.cell Xi) (p.scheme.scheme.cell Θ))
    (Sig : p.scheme.scheme.below (p.scheme.scheme.cell Θ)),
    p.scheme.scheme.scope Θ = Finset.univ ∧ p.scheme.scheme.grade Θ = p.topGrade ∧
    p.label Θ = ⊤ ∧ p.label Sig.1 = ⊤ ∧
    extVisibilityReplace (p.scheme.rows.E Θ Sig) p.topGrade p.topGrade ≤
      p.scheme.rows.E Θ ⟨Xi, hXi⟩

/-- Clause 2.(b) of Def. 5.3.1: some full-scope `∞`-cell `Θ` of grade `K^p` has
`E(Θ)(Ξ) = E(Θ)(Ξ) ⊔⁺_{K^p} i` — the row pins the value `α + i`.  Then `p⁺(Ξ) = α + i`.
(Independence of `i` from `Θ` is Lemma 5.3.2, a consistency theorem — not needed here:
`someProvisionalValue` selects the least band index, and under `¬ ProvisionalCap` every witness
forces `i < K^p`, `ProvisionalBand.lt_topGrade`.) -/
def ProvisionalBand (p : S α n) (Xi : Cell p.scheme.scheme) (i : ℕ) : Prop :=
  ∃ (Θ : Cell p.scheme.scheme)
    (hXi : GradedLe (p.scheme.scheme.cell Xi) (p.scheme.scheme.cell Θ)),
    p.scheme.scheme.scope Θ = Finset.univ ∧ p.scheme.scheme.grade Θ = p.topGrade ∧
    p.label Θ = ⊤ ∧
    p.scheme.rows.E Θ ⟨Xi, hXi⟩ =
      extVisibilityReplace (p.scheme.rows.E Θ ⟨Xi, hXi⟩) p.topGrade i

/-- **A provisional value `p⁺(Ξ)`** (Def. 5.3.1, cell-dependent — not Knight-VC's uniform
`topLiftType` cap, KVC-d3): clause 1 keeps the label when it is not `∞`; clause 2.(a) caps at
`α + K^p`; clause 2.(b) reads the **least** band index off a witnessing row.  The final `⊤`
branch is unreachable (`exists_provisionalBand`, `someProvisionalValue_ne_top`): the paper leaves
clause 2 partial and the totality is availability + completeness.

This function is a **witness/chooser**, not the primary interface: the API works with the
relation `IsProvisionalValue` (Def. 5.3.1 as a graph), and this chooser only discharges its
totality (`isProvisionalValue_someProvisionalValue`).  Band-index independence (Lemma 5.3.2,
`ProvisionalBand.unique` in `Knight/ProvisionalUniqueness.lean`) makes the relation
single-valued, so the chooser computes *the* value (`isProvisionalValue_iff`). -/
noncomputable def someProvisionalValue (p : S α n) (Xi : Cell p.scheme.scheme) : ExtOrd :=
  open Classical in
  if p.label Xi = ⊤ then
    if p.ProvisionalCap Xi then ofOrd (α + p.topGrade)
    else if h : ∃ i, p.ProvisionalBand Xi i then ofOrd (α + Nat.find h)
    else ⊤
  else p.label Xi

theorem someProvisionalValue_of_ne_top {p : S α n} {Xi : Cell p.scheme.scheme}
    (h : p.label Xi ≠ ⊤) : p.someProvisionalValue Xi = p.label Xi := by
  unfold someProvisionalValue
  rw [ite_eq_right h]

theorem someProvisionalValue_of_cap {p : S α n} {Xi : Cell p.scheme.scheme}
    (htop : p.label Xi = ⊤) (hcap : p.ProvisionalCap Xi) :
    p.someProvisionalValue Xi = ofOrd (α + p.topGrade) := by
  unfold someProvisionalValue
  rw [ite_eq_left htop, ite_eq_left hcap]

/-- **Clause 2 of Def. 5.3.1 is total**: if `p(Ξ) = ∞` and clause 2.(a) does not apply, some
band witnesses clause 2.(b).  Proof: `K^p ∈ topGrades` (`grade_mem_topGrades` at `Ξ` plus
`Nat.sSup_mem`) provides a full-scope `∞`-cell `Θ` of grade `K^p` with `Ξ` below it; the row
value `E(Θ)(Ξ)` cannot be `-∞`, `∞`, or self-visible at `K^p` (each would fire clause 2.(a)
with `Σ := Ξ`), so it is an ordinal with finite part `< K^p`, and that finite part is the
band. -/
theorem exists_provisionalBand {p : S α n} {Xi : Cell p.scheme.scheme}
    (htop : p.label Xi = ⊤) (hcap : ¬ p.ProvisionalCap Xi) :
    ∃ i, p.ProvisionalBand Xi i := by
  have hmem := grade_mem_topGrades htop
  have hbdd := p.topGrades_bddAbove
  have hK : p.topGrade ∈ p.topGrades := Nat.sSup_mem ⟨_, hmem⟩ hbdd
  obtain ⟨Θ, hsc, hgr, hΘtop⟩ := hK
  have hXile : p.scheme.scheme.grade Xi ≤ p.topGrade := le_csSup hbdd hmem
  have hXimem : GradedLe (p.scheme.scheme.cell Xi) (p.scheme.scheme.cell Θ) := by
    refine ⟨?_, ?_⟩
    · change p.scheme.scheme.scope Xi ⊆ p.scheme.scheme.scope Θ
      rw [hsc]
      exact Finset.subset_univ _
    · change p.scheme.scheme.grade Xi ≤ p.scheme.scheme.grade Θ
      rw [hgr]
      exact hXile
  have hnotself :
      extVisibilityReplace (p.scheme.rows.E Θ ⟨Xi, hXimem⟩) p.topGrade p.topGrade ≠
        p.scheme.rows.E Θ ⟨Xi, hXimem⟩ := fun hself =>
    hcap ⟨Θ, hXimem, ⟨Xi, hXimem⟩, hsc, hgr, hΘtop, htop, le_of_eq hself⟩
  rcases ExtOrd.cases (p.scheme.rows.E Θ ⟨Xi, hXimem⟩) with hbot | htop' | ⟨β, hβ⟩
  · rw [hbot] at hnotself
    exact absurd rfl hnotself
  · rw [htop'] at hnotself
    exact absurd rfl hnotself
  · rw [hβ, extVisibilityReplace_ofOrd] at hnotself
    have hfp : finitePart β < p.topGrade := by
      by_contra hge
      exact hnotself (congrArg ofOrd ((visibilityReplace_self_iff β _).mpr (not_lt.mp hge)))
    refine ⟨finitePart β, Θ, hXimem, hsc, hgr, hΘtop, ?_⟩
    have hvr : visibilityReplace β p.topGrade (finitePart β) = β := by
      unfold visibilityReplace ordinalReplace
      rw [ite_eq_left hfp]
      exact decomposition β
    rw [hβ, extVisibilityReplace_ofOrd, hvr]

/-- Under `¬` clause 2.(a), every band index is `< K^p` (it is the finite part of an ordinal
row value that is not self-visible at `K^p`). -/
theorem ProvisionalBand.lt_topGrade {p : S α n} {Xi : Cell p.scheme.scheme} {i : ℕ}
    (h : p.ProvisionalBand Xi i) (htop : p.label Xi = ⊤) (hcap : ¬ p.ProvisionalCap Xi) :
    i < p.topGrade := by
  obtain ⟨Θ, hXimem, hsc, hgr, hΘtop, heq⟩ := h
  have hnotself :
      extVisibilityReplace (p.scheme.rows.E Θ ⟨Xi, hXimem⟩) p.topGrade p.topGrade ≠
        p.scheme.rows.E Θ ⟨Xi, hXimem⟩ := fun hself =>
    hcap ⟨Θ, hXimem, ⟨Xi, hXimem⟩, hsc, hgr, hΘtop, htop, le_of_eq hself⟩
  rcases ExtOrd.cases (p.scheme.rows.E Θ ⟨Xi, hXimem⟩) with hbot | htop' | ⟨β, hβ⟩
  · rw [hbot] at hnotself
    exact absurd rfl hnotself
  · rw [htop'] at hnotself
    exact absurd rfl hnotself
  · rw [hβ, extVisibilityReplace_ofOrd] at hnotself heq
    have hfp : finitePart β < p.topGrade := by
      by_contra hge
      exact hnotself (congrArg ofOrd ((visibilityReplace_self_iff β _).mpr (not_lt.mp hge)))
    have hβeq : β = limitPart β + (i : Ordinal) := by
      have h0 := ofOrd_inj.mp heq
      unfold visibilityReplace ordinalReplace at h0
      rwa [ite_eq_left hfp] at h0
    have hcast : (i : Ordinal.{0}) = (finitePart β : Ordinal.{0}) :=
      add_left_cancel (hβeq.symm.trans (decomposition β).symm)
    have : i = finitePart β := by exact_mod_cast hcast
    omega

/-- The band branch of `someProvisionalValue`: when `p(Ξ) = ∞` and clause 2.(a) fails, the value
is `α + i` for a band index `i < K^p`. -/
theorem someProvisionalValue_of_band {p : S α n} {Xi : Cell p.scheme.scheme}
    (htop : p.label Xi = ⊤) (hcap : ¬ p.ProvisionalCap Xi) :
    ∃ i, p.ProvisionalBand Xi i ∧ i < p.topGrade ∧
      p.someProvisionalValue Xi = ofOrd (α + i) := by
  have hex := exists_provisionalBand htop hcap
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex,
    (Nat.find_spec hex).lt_topGrade htop hcap, ?_⟩
  unfold someProvisionalValue
  rw [ite_eq_left htop, ite_eq_right hcap, dite_eq_left hex]

/-- **Def. 5.3.1 as a graph — the primary interface**: `v` is a provisional value of the cell
`Ξ` in `p`.  Clause 1 (`p(Ξ) < ∞`): `v = p(Ξ)`; clause 2.(a): `v = α + K^p`; clause 2.(b):
`v = α + i` for **some** band index `i`.  Stated relationally so that no noncanonical
selection enters the API: Lemma 5.3.2 (band-index independence of the witnessing `Θ`, a
consistency theorem, `ProvisionalBand.unique` in `Knight/ProvisionalUniqueness.lean`) makes the
relation single-valued (`IsProvisionalValue.unique`); `someProvisionalValue` (the least band
index) is a witness of totality (`isProvisionalValue_someProvisionalValue`) and computes the
unique value (`isProvisionalValue_iff`), but is not part of the primary interface. -/
def IsProvisionalValue (p : S α n) (Xi : Cell p.scheme.scheme) (v : ExtOrd) : Prop :=
  (p.label Xi ≠ ⊤ ∧ v = p.label Xi) ∨
  (p.label Xi = ⊤ ∧ p.ProvisionalCap Xi ∧ v = ofOrd (α + p.topGrade)) ∨
  (p.label Xi = ⊤ ∧ ¬ p.ProvisionalCap Xi ∧
    ∃ i, p.ProvisionalBand Xi i ∧ v = ofOrd (α + i))

/-- The chooser realizes the relation (totality witness; the choice — least band index — is
canonical only in the sense of being deterministic, and is not exposed by the relational
interface). -/
theorem isProvisionalValue_someProvisionalValue (p : S α n) (Xi : Cell p.scheme.scheme) :
    p.IsProvisionalValue Xi (p.someProvisionalValue Xi) := by
  by_cases htop : p.label Xi = ⊤
  · by_cases hcap : p.ProvisionalCap Xi
    · exact Or.inr (Or.inl ⟨htop, hcap, someProvisionalValue_of_cap htop hcap⟩)
    · obtain ⟨i, hband, -, hval⟩ := someProvisionalValue_of_band htop hcap
      exact Or.inr (Or.inr ⟨htop, hcap, i, hband, hval⟩)
  · exact Or.inl ⟨htop, someProvisionalValue_of_ne_top htop⟩

/-- Def. 5.3.1 is total: every cell has a provisional value. -/
theorem exists_isProvisionalValue (p : S α n) (Xi : Cell p.scheme.scheme) :
    ∃ v, p.IsProvisionalValue Xi v :=
  ⟨_, isProvisionalValue_someProvisionalValue p Xi⟩

/-- No provisional value is `∞` — the paper's codomain `{-∞} ∪ [0, α + ω)` of Def. 5.3.1. -/
theorem IsProvisionalValue.ne_top {p : S α n} {Xi : Cell p.scheme.scheme} {v : ExtOrd}
    (h : p.IsProvisionalValue Xi v) : v ≠ ⊤ := by
  rcases h with ⟨hne, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, i, -, rfl⟩
  · exact hne
  · exact ofOrd_ne_top _
  · exact ofOrd_ne_top _

/-- Every provisional value is `≤ α + K^p` (the conservative-estimate reading after
Def. 5.3.1). -/
theorem IsProvisionalValue.le {p : S α n} {Xi : Cell p.scheme.scheme} {v : ExtOrd}
    (h : p.IsProvisionalValue Xi v) : v ≤ ofOrd (α + p.topGrade) := by
  rcases h with ⟨hne, rfl⟩ | ⟨-, -, rfl⟩ | ⟨htop, hcap, i, hband, rfl⟩
  · rcases p.label_bound Xi with hlt | htop'
    · refine le_of_lt (hlt.trans_le (ofOrd_le_ofOrd.mpr ?_))
      simp
    · exact absurd htop' hne
  · exact le_rfl
  · rw [ofOrd_le_ofOrd]
    have hcast : (i : Ordinal.{0}) < (p.topGrade : Ordinal.{0}) := by
      exact_mod_cast hband.lt_topGrade htop hcap
    exact add_le_add (le_refl α) hcast.le

/-- `p⁺` never takes the value `∞` — the paper's codomain `{-∞} ∪ [0, α + ω)` of Def. 5.3.1
(clause 2 is total, `exists_provisionalBand`). -/
theorem someProvisionalValue_ne_top (p : S α n) (Xi : Cell p.scheme.scheme) :
    p.someProvisionalValue Xi ≠ ⊤ := by
  by_cases htop : p.label Xi = ⊤
  · by_cases hcap : p.ProvisionalCap Xi
    · rw [someProvisionalValue_of_cap htop hcap]
      exact ofOrd_ne_top _
    · obtain ⟨i, -, -, hval⟩ := someProvisionalValue_of_band htop hcap
      rw [hval]
      exact ofOrd_ne_top _
  · rw [someProvisionalValue_of_ne_top htop]
    exact htop

/-- `p⁺(Ξ) ≤ α + K^p` (the conservative-estimate reading after Def. 5.3.1). -/
theorem someProvisionalValue_le (p : S α n) (Xi : Cell p.scheme.scheme) :
    p.someProvisionalValue Xi ≤ ofOrd (α + p.topGrade) := by
  by_cases htop : p.label Xi = ⊤
  · by_cases hcap : p.ProvisionalCap Xi
    · rw [someProvisionalValue_of_cap htop hcap]
    · obtain ⟨i, -, hlt, hval⟩ := someProvisionalValue_of_band htop hcap
      rw [hval, ofOrd_le_ofOrd]
      have hcast : (i : Ordinal.{0}) < (p.topGrade : Ordinal.{0}) := by exact_mod_cast hlt
      exact add_le_add (le_refl α) hcast.le
  · rw [someProvisionalValue_of_ne_top htop]
    rcases p.label_bound Xi with hlt | htop'
    · refine le_of_lt (hlt.trans_le (ofOrd_le_ofOrd.mpr ?_))
      simp
    · exact absurd htop' htop

end StageType

/-! ### Stabilized values (Def. 5.3.9, graph form) and the terminal invariants -/

namespace KnightRealization

open StageType

variable {α : LimitStage} {M : Type w}

/-- **Def. 5.3.9, dominating form**: the provisional values of (the images of) the cell `Ξ` of
`p` — intended as the type of `R` at `t` — stabilize to `γ` on a dominating set of labelled
tuples: every tuple `s` admits a labelled common extension `u` of `s` and `t` whose type gives
the underlying cell of `Ξ` the provisional value `γ` (relationally, `IsProvisionalValue` — no
chooser is consulted; once Lemma 5.3.2 lands at #51 the relation is the function graph).
The paper's "dominating (equivalently
coinitial, Cor. 5.3.8) set of finite subsets `A` of `M`" — the equivalence and the uniqueness
of `γ` are model theorems (directedness of labelled extensions), for #51, not definitional
here. -/
def StabilizesTo (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n)
    (Xi : Cell p.scheme.scheme) (γ : ExtOrd) : Prop :=
  ∀ {m : ℕ} (s : Fin m ↪ M),
    ∃ (m' : ℕ) (u : Fin m' ↪ M) (g : Fin m ↪ Fin m') (f : Fin n ↪ Fin m')
      (q : S α.1 m') (hpq : typeMap f q = some p),
      R.eval u = some q ∧ g.trans u = s ∧ f.trans u = t ∧
      q.IsProvisionalValue (mapCell hpq Xi) γ

/-- **The value `M⁺(Ξ)` as a graph** (Def. 5.3.9): `M⁺(Ξ) = γ` iff either `γ < α + ω` and the
provisional values stabilize to `γ`, or `γ = ∞` and no value below `α + ω` stabilizes.  Total
by construction; functional only under the model axioms (see `StabilizesTo`). -/
def HasStableValue (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n)
    (Xi : Cell p.scheme.scheme) (γ : ExtOrd) : Prop :=
  (γ < ofOrd (α.1 + Ordinal.omega0) ∧ R.StabilizesTo t p Xi γ) ∨
  (γ = ⊤ ∧ ∀ δ : ExtOrd, δ < ofOrd (α.1 + Ordinal.omega0) → ¬ R.StabilizesTo t p Xi δ)

/-- The stabilized values realized in `R`: all values `M⁺(Ξ)`, over all cells `Ξ` of all
realized types (the index set of the supremum in Def. 5.4.1). -/
def stableSpectrum (R : KnightRealization α M) : Set ExtOrd :=
  {γ | ∃ (n : ℕ) (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p ∧
    ∃ Xi : Cell p.scheme.scheme, R.HasStableValue t p Xi γ}

/-! ### Characteristic arity (Def. 5.4.1) -/

/-- **Def. 5.4.1, fixed `K`**: `α + K` is the supremum of all stabilized values `M⁺(Ξ)`
(`IsLUB`: no completeness of `ExtOrd` is invoked, and "is the supremum" is read as "is the
least upper bound", not "is attained").  This is **not** Knight-VC's `charArity`
(distinguishing arity) — banned identification 2. -/
def IsCharacteristicArity (R : KnightRealization α M) (K : ℕ) : Prop :=
  IsLUB R.stableSpectrum (ofOrd (α.1 + K))

theorem IsCharacteristicArity.unique {R : KnightRealization α M} {K K' : ℕ}
    (h : R.IsCharacteristicArity K) (h' : R.IsCharacteristicArity K') : K = K' := by
  have hα : α.1 + (K : Ordinal.{0}) = α.1 + (K' : Ordinal.{0}) :=
    ofOrd_inj.mp (IsLUB.unique h h')
  exact_mod_cast add_left_cancel hα

/-- **The characteristic arity** `K ∈ ω ∪ {∞}` of `R` (Def. 5.4.1): the finite `K` with
`α + K` the supremum of the stabilized values, and `∞` when there is none.

**† provisional** (`docs/TERMINOLOGY.md`): a faithful transcription of Def. 5.4.1, but not
presented as settled until stabilized-value functionality (#51) and occurrence/witness-choice
independence (#31/#47/#57) are proved. -/
noncomputable def characteristicArity (R : KnightRealization α M) : ℕ∞ :=
  open Classical in
  if h : ∃ K : ℕ, R.IsCharacteristicArity K then (Nat.find h : ℕ∞) else ⊤

theorem characteristicArity_eq_coe {R : KnightRealization α M} {K : ℕ}
    (h : R.IsCharacteristicArity K) : R.characteristicArity = K := by
  classical
  have hex : ∃ K : ℕ, R.IsCharacteristicArity K := ⟨K, h⟩
  unfold characteristicArity
  rw [dite_eq_left hex]
  have hfind : Nat.find hex = K := IsCharacteristicArity.unique (Nat.find_spec hex) h
  rw [hfind]

theorem characteristicArity_eq_top {R : KnightRealization α M}
    (h : ∀ K : ℕ, ¬ R.IsCharacteristicArity K) : R.characteristicArity = ⊤ := by
  unfold characteristicArity
  rw [dite_eq_right (by rintro ⟨K, hK⟩; exact h K hK)]

/-! ### Anchors at infinity and hollowness (Def. 5.4.2) -/

/-- **Def. 5.4.2**: the cell `∞̃ := Xi` of `p` — intended as the type of `R` at `t` — is an
**anchor at infinity with threshold `K'`**, "minimal at infinity": it is labelled `∞` (implicit
in the paper's `∞̃`, see the module docstring), and in the type `q` of every labelled tuple
extending `t`, for every `∞`-cell `Θ` of grade `≥ K'` and every `∞`-cell `Σ` below `Θ`,

`E(Θ)(Σ) ⊔⁺_{K'} K' ≥ E(Θ)(∞̃)`, strictly when the grade of `Θ` exceeds `K'`.

(`M(Θ) = ∞` is read as the label of `Θ`, Def. 3.2.5: labels are preserved by restriction,
`label_mapCell`.) -/
def IsInfinityAnchor (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n)
    (Xi : Cell p.scheme.scheme) (K' : ℕ) : Prop :=
  p.label Xi = ⊤ ∧
  ∀ {m : ℕ} (s : Fin m ↪ M) (f : Fin n ↪ Fin m) (q : S α.1 m),
    f.trans s = t → R.eval s = some q →
    ∀ (hpq : typeMap f q = some p) (Θ : Cell q.scheme.scheme),
      K' ≤ q.scheme.scheme.grade Θ → q.label Θ = ⊤ →
      ∀ Sig : q.scheme.scheme.below (q.scheme.scheme.cell Θ), q.label Sig.1 = ⊤ →
      ∀ hXi : GradedLe (q.scheme.scheme.cell (mapCell hpq Xi)) (q.scheme.scheme.cell Θ),
        q.scheme.rows.E Θ ⟨mapCell hpq Xi, hXi⟩ ≤
          extVisibilityReplace (q.scheme.rows.E Θ Sig) K' K' ∧
        (K' < q.scheme.scheme.grade Θ →
          q.scheme.rows.E Θ ⟨mapCell hpq Xi, hXi⟩ <
            extVisibilityReplace (q.scheme.rows.E Θ Sig) K' K')

/-- The anchor is at infinity: `p(∞̃) = ∞`. -/
theorem IsInfinityAnchor.label_top {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
    {p : S α.1 n} {Xi : Cell p.scheme.scheme} {K' : ℕ}
    (h : R.IsInfinityAnchor t p Xi K') : p.label Xi = ⊤ := h.1

/-- `R` has an **anchor at infinity** (Def. 5.4.2): some cell of some realized type is minimal
at infinity at some threshold. -/
def HasInfinityAnchor (R : KnightRealization α M) : Prop :=
  ∃ (n : ℕ) (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p ∧
    ∃ (Xi : Cell p.scheme.scheme) (K' : ℕ), R.IsInfinityAnchor t p Xi K'

/-- **Hollowness** (Def. 5.4.2): `R` is hollow iff it has no anchor at infinity.  The paper
frames the definition for models of characteristic arity `K` with `0 < K ≤ ∞`; the framing
hypothesis belongs to the consumers (#52).  This is **not** orbit homogeneity (Knight-VC's
`IsHollow`, renamed `IsOrbitHomogeneous` there) — banned identification 1; orbit homogeneity
is deliberately not defined in this module. -/
def IsHollow (R : KnightRealization α M) : Prop := ¬ R.HasInfinityAnchor

/-! ### The terminal profile: one datum, one record

All terminal invariants are derived from the single level-owned datum `R` (no independently
chosen witnesses), and bundled in one record so that downstream consumers receive them
together; isomorphism transport is proved once, for the profile.  Core data (Def. 7.3.1, §7)
is owned by the linked stop / terminal realization (#31); `TerminalCode` (#57) encodes the
classified branch from this profile together with that core information. -/

/-- The **terminal profile** of a realization: its characteristic arity (Def. 5.4.1) and its
hollowness (Def. 5.4.2), derived together from the one underlying realization.  `TerminalCode`
(#57) encodes the *classified branch*: it is built from this profile together with the core
information owned by the linked stop / terminal realization (#31) — no promise that a chosen
core becomes a further field here. -/
structure TerminalProfile : Type where
  /-- The characteristic arity `K ∈ ω ∪ {∞}` (Def. 5.4.1). -/
  charArity : ℕ∞
  /-- Hollowness (Def. 5.4.2): no anchor at infinity. -/
  hollow : Prop

/-- The terminal profile of `R`: the single function producing all terminal invariants of the
one datum `R`. -/
noncomputable def terminalProfile (R : KnightRealization α M) : TerminalProfile :=
  { charArity := R.characteristicArity
    hollow := R.IsHollow }

@[simp] theorem terminalProfile_charArity (R : KnightRealization α M) :
    R.terminalProfile.charArity = R.characteristicArity := rfl

@[simp] theorem terminalProfile_hollow (R : KnightRealization α M) :
    R.terminalProfile.hollow = R.IsHollow := rfl

/-! ### Isomorphism transport (the acceptance test of #48)

An isomorphism `e : M ≃ N` of realizations moves labelled tuples bijectively and preserves
labels *on the nose* (`Realization.IsIso`), so every invariant of this module — each an
intrinsic statement over the labelled tuples of the one datum — transports.  The bundled
transport is `IsIso.terminalProfile_eq`; the invariant-level statements are its projections. -/

section Iso

variable {N : Type w'} {R : KnightRealization α M} {R₂ : KnightRealization α N} {e : M ≃ N}

private theorem trans_symm_trans {m : ℕ} (e : M ≃ N) (s : Fin m ↪ N) :
    (s.trans e.symm.toEmbedding).trans e.toEmbedding = s := by
  ext i
  simp

private theorem trans_trans_symm {m : ℕ} (e : M ≃ N) (s : Fin m ↪ M) :
    (s.trans e.toEmbedding).trans e.symm.toEmbedding = s := by
  ext i
  simp

theorem IsIso.stabilizesTo_iff (hi : Realization.IsIso R R₂ e) {n : ℕ} (t : Fin n ↪ M)
    (p : S α.1 n) (Xi : Cell p.scheme.scheme) (γ : ExtOrd) :
    R.StabilizesTo t p Xi γ ↔ R₂.StabilizesTo (t.trans e.toEmbedding) p Xi γ := by
  constructor
  · intro H m s
    obtain ⟨m', u, g, f, q, hpq, hq, hgu, hfu, hval⟩ := H (s.trans e.symm.toEmbedding)
    refine ⟨m', u.trans e.toEmbedding, g, f, q, hpq, (hi u).trans hq, ?_, ?_, hval⟩
    · rw [← Function.Embedding.trans_assoc, hgu, trans_symm_trans]
    · rw [← Function.Embedding.trans_assoc, hfu]
  · intro H m s
    obtain ⟨m', u, g, f, q, hpq, hq, hgu, hfu, hval⟩ := H (s.trans e.toEmbedding)
    refine ⟨m', u.trans e.symm.toEmbedding, g, f, q, hpq, ?_, ?_, ?_, hval⟩
    · have h := hi (u.trans e.symm.toEmbedding)
      rw [trans_symm_trans] at h
      exact h.symm.trans hq
    · rw [← Function.Embedding.trans_assoc, hgu, trans_trans_symm]
    · rw [← Function.Embedding.trans_assoc, hfu, trans_trans_symm]

theorem IsIso.hasStableValue_iff (hi : Realization.IsIso R R₂ e) {n : ℕ} (t : Fin n ↪ M)
    (p : S α.1 n) (Xi : Cell p.scheme.scheme) (γ : ExtOrd) :
    R.HasStableValue t p Xi γ ↔ R₂.HasStableValue (t.trans e.toEmbedding) p Xi γ := by
  unfold HasStableValue
  simp only [IsIso.stabilizesTo_iff hi]

theorem IsIso.stableSpectrum_eq (hi : Realization.IsIso R R₂ e) :
    R.stableSpectrum = R₂.stableSpectrum := by
  ext γ
  constructor
  · rintro ⟨n, t, p, hp, Xi, hM⟩
    exact ⟨n, t.trans e.toEmbedding, p, (hi t).trans hp, Xi,
      (IsIso.hasStableValue_iff hi t p Xi γ).mp hM⟩
  · rintro ⟨n, t, p, hp, Xi, hM⟩
    have hp' : R.eval (t.trans e.symm.toEmbedding) = some p := by
      have h := hi (t.trans e.symm.toEmbedding)
      rw [trans_symm_trans] at h
      exact h.symm.trans hp
    have hM' := IsIso.hasStableValue_iff hi (t.trans e.symm.toEmbedding) p Xi γ
    rw [trans_symm_trans] at hM'
    exact ⟨n, t.trans e.symm.toEmbedding, p, hp', Xi, hM'.mpr hM⟩

theorem IsIso.isCharacteristicArity_iff (hi : Realization.IsIso R R₂ e) (K : ℕ) :
    R.IsCharacteristicArity K ↔ R₂.IsCharacteristicArity K := by
  unfold IsCharacteristicArity
  rw [IsIso.stableSpectrum_eq hi]

theorem IsIso.characteristicArity_eq (hi : Realization.IsIso R R₂ e) :
    R.characteristicArity = R₂.characteristicArity := by
  by_cases h : ∃ K : ℕ, R.IsCharacteristicArity K
  · obtain ⟨K, hK⟩ := h
    rw [characteristicArity_eq_coe hK,
      characteristicArity_eq_coe ((IsIso.isCharacteristicArity_iff hi K).mp hK)]
  · rw [characteristicArity_eq_top (fun K hK => h ⟨K, hK⟩),
      characteristicArity_eq_top
        (fun K hK => h ⟨K, (IsIso.isCharacteristicArity_iff hi K).mpr hK⟩)]

theorem IsInfinityAnchor.of_isIso (hi : Realization.IsIso R R₂ e) {n : ℕ} {t : Fin n ↪ M}
    {p : S α.1 n} {Xi : Cell p.scheme.scheme} {K' : ℕ} (h : R.IsInfinityAnchor t p Xi K') :
    R₂.IsInfinityAnchor (t.trans e.toEmbedding) p Xi K' := by
  refine ⟨h.1, fun s f q hfs hq hpq Θ hgr hΘ Sig hSig hXi => ?_⟩
  have hfs' : f.trans (s.trans e.symm.toEmbedding) = t := by
    rw [← Function.Embedding.trans_assoc, hfs, trans_trans_symm]
  have hq' : R.eval (s.trans e.symm.toEmbedding) = some q := by
    have h' := hi (s.trans e.symm.toEmbedding)
    rw [trans_symm_trans] at h'
    exact h'.symm.trans hq
  exact h.2 (s.trans e.symm.toEmbedding) f q hfs' hq' hpq Θ hgr hΘ Sig hSig hXi

theorem IsIso.isInfinityAnchor_iff (hi : Realization.IsIso R R₂ e) {n : ℕ} (t : Fin n ↪ M)
    (p : S α.1 n) (Xi : Cell p.scheme.scheme) (K' : ℕ) :
    R.IsInfinityAnchor t p Xi K' ↔ R₂.IsInfinityAnchor (t.trans e.toEmbedding) p Xi K' := by
  refine ⟨IsInfinityAnchor.of_isIso hi, fun h => ?_⟩
  have h' := IsInfinityAnchor.of_isIso (Realization.IsIso.symm hi) h
  rwa [trans_trans_symm] at h'

theorem IsIso.hasInfinityAnchor_iff (hi : Realization.IsIso R R₂ e) :
    R.HasInfinityAnchor ↔ R₂.HasInfinityAnchor := by
  constructor
  · rintro ⟨n, t, p, hp, Xi, K', hA⟩
    exact ⟨n, t.trans e.toEmbedding, p, (hi t).trans hp, Xi, K',
      IsInfinityAnchor.of_isIso hi hA⟩
  · rintro ⟨n, t, p, hp, Xi, K', hA⟩
    have hp' : R.eval (t.trans e.symm.toEmbedding) = some p := by
      have h := hi (t.trans e.symm.toEmbedding)
      rw [trans_symm_trans] at h
      exact h.symm.trans hp
    have hA' := IsInfinityAnchor.of_isIso (Realization.IsIso.symm hi) hA
    exact ⟨n, t.trans e.symm.toEmbedding, p, hp', Xi, K', hA'⟩

theorem IsIso.isHollow_iff (hi : Realization.IsIso R R₂ e) : R.IsHollow ↔ R₂.IsHollow :=
  not_congr (IsIso.hasInfinityAnchor_iff hi)

/-- **The bundled transport**: the terminal profile is constant on isomorphism classes.  This
is the theorem proved once for the single datum; the invariant-level transports below are its
projections. -/
theorem IsIso.terminalProfile_eq (hi : Realization.IsIso R R₂ e) :
    R.terminalProfile = R₂.terminalProfile := by
  unfold terminalProfile
  rw [IsIso.characteristicArity_eq hi]
  congr 1
  exact propext (IsIso.isHollow_iff hi)

/-- The terminal profile is an isomorphism invariant. -/
theorem terminalProfile_eq_of_iso {R : KnightRealization α M} {R₂ : KnightRealization α N}
    (h : Nonempty (R.Iso R₂)) : R.terminalProfile = R₂.terminalProfile :=
  let ⟨i⟩ := h
  IsIso.terminalProfile_eq i.2

/-- **Characteristic arity is an isomorphism invariant** (projection of
`terminalProfile_eq_of_iso`). -/
theorem characteristicArity_eq_of_iso {R : KnightRealization α M}
    {R₂ : KnightRealization α N} (h : Nonempty (R.Iso R₂)) :
    R.characteristicArity = R₂.characteristicArity :=
  congrArg TerminalProfile.charArity (terminalProfile_eq_of_iso h)

/-- **Hollowness is an isomorphism invariant** (projection of `terminalProfile_eq_of_iso`). -/
theorem isHollow_iff_of_iso {R : KnightRealization α M} {R₂ : KnightRealization α N}
    (h : Nonempty (R.Iso R₂)) : R.IsHollow ↔ R₂.IsHollow :=
  iff_of_eq (congrArg TerminalProfile.hollow (terminalProfile_eq_of_iso h))

end Iso

end KnightRealization

end VaughtConjecture.Knight
