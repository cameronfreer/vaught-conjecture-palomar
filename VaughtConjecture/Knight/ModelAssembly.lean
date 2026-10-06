/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Coface
public import VaughtConjecture.Knight.Model

/-! # Modelhood assembly: `IsModel` from consistency + covering + copy servicing + candidates

#42, finite-block shortcut 1 (**model-clause requests leave the live scheduler**).  The four
existential-closure clauses of Def. 3.2.1(4) need no per-clause scheduling: each clause's
conclusion `RealizesSome t p U` factors as

* a **candidate**: some `q ∈ U` with `IsCoface p q` — pure `S`-level existence, no
  realization involved (`HasCandidates`); and
* **copy servicing**: the candidate, regarded as an exact-copy request at its tuple, is
  realized over a fresh point (`ServicesExactCopies` — the stopped-model projection of
  `CutoffCopyFair`, #42's terminology split; stated abstractly, with **no scheduler, no run,
  no construction state, and no fairness proof**).

The assembly theorem (`isModel_of_candidates`) is then: exact consistency (clause (2)) +
initial-segment covering (clause (3)) + copy servicing + candidate existence + `Nonempty M`
`⇒ IsModel`.  **Every clause decomposes this way — no clause resists** (the finding #42 asked
to record): `RealizesSome` is literally `∃ y hy q, q ∈ U ∧ IsCoface p q ∧ eval (t⌢y) = q`,
which is the candidate existential composed with exact-copy realization
(`ServicesExactCopies.realizesSome`).

## The candidate bundle, and what discharges

`HasCandidates` has one field per clause of Def. 3.2.1(4), each quantified over realized
`(t, p)` and stating exactly the candidate existence that clause requires:

* **(a)(i) `genSat`** — for each supplied extension domain `D` (`ExtendsDomain p D`), a
  coface of `p` in `GenSatFamily D`.  **Discharged** by the compiled
  `StageType.genSatFamily_nonempty` (bountifulness of `D` at cutoff `⊥`; `Knight/Coface.lean`).
* **(a)(ii) `bottomPattern`** — for `D` as above and a labelling `q'` respecting `D.rows`
  (no stage bound) and extending `p.label` along the face-cell map, a coface of `p` in
  `BottomPatternFamily D q'`.  **Discharged** by the compiled
  `StageType.bottomPatternFamily_nonempty` (the truncation of `q'` itself).
* **(b) `uniformity`** — for each non-successor `γ < α`, a coface of `p` with a cell labelled
  in `[γ, γ + ω)`.  **Open.**
* **(c) `highGradeDominance`** — for each `γ < α`, a coface of `p` with a cell of grade
  `n + 1` labelled strictly above `γ`.  **Open.**

`HasCandidates.of_band` is the smart constructor exposing the decomposition: it consumes
**only** the two open fields and fills (a)(i)/(a)(ii) from the compiled Coface lemmas;
`isModel_of_band_candidates` is the assembly theorem through it.

## Surviving obligations (the exact remaining unproved candidate constructors)

1. **The selected high/band candidate** (#42 "one exact-grade band candidate"): over a
   supplied extension domain, a coface with a cell of grade exactly `n + 1` labelled
   `limitPart γ + max (n + 1) (finitePart γ + 1)` — strictly above `γ` (discharging (c)) and,
   for non-successor `γ`, equal to `γ + (n + 1) ∈ [γ, γ + ω)` (discharging (b)).  One
   candidate serves **both** open fields.
2. **The `⊤`-flag production** (#42 unresolved producer obligation 1): the high-band case of
   that construction assumes a source grade-`(n + 1)` cell labelled `⊤`; nothing yet
   constructs that flag.  Until it exists, obligation 1 cannot close at every `γ < α`.

Nothing else remains: with those two, `HasCandidates` is total and modelhood of any stopped
structure reduces to clauses (2), (3) and the `CutoffCopyFair` projection — the properties
the one block recursion of #42's revised critical path produces.

**Quarantine.**  This module is *not* re-exported from the root (`VaughtConjecture.lean`); the
lakefile glob still compiles and audits it.  It enters the import cone when the block
recursion producing `ServicesExactCopies` lands. -/

@[expose] public section

namespace VaughtConjecture.Knight

namespace KnightRealization

universe w

variable {M : Type w} {n : ℕ} {α : LimitStage} {R : KnightRealization α M}

/-! ### Copy servicing: the `CutoffCopyFair` projection -/

/-- **Exact-copy servicing** (the stopped-model projection of `CutoffCopyFair`, #42): every
coface `q` of a realized type `p = R(t)`, regarded as an exact-copy request at `t`, is
realized in the structure — there is a fresh `y ∉ range t` with `R(t⌢y) = q` **exactly**.
This is the single semantic property the fair block recursion's stopped union is to provide;
it is stated abstractly here: no scheduler, no run, no construction state. -/
def ServicesExactCopies (R : KnightRealization α M) : Prop :=
  ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
    ∀ q : S α.1 (n + 1), IsCoface p q →
      ∃ (y : M) (hy : y ∉ Set.range t), R.eval (snoc t y hy) = some q

/-- The decomposition of `RealizesSome` (the conclusion of every clause of Def. 3.2.1(4)):
a candidate — some `q ∈ U` that is a coface of the realized `p` — plus exact-copy servicing
realize some member of `U` over `t` as a coface of `p`. -/
theorem ServicesExactCopies.realizesSome (hserv : R.ServicesExactCopies) {t : Fin n ↪ M}
    {p : S α.1 n} (hp : R.eval t = some p) {U : Set (S α.1 (n + 1))}
    (hcand : ∃ q ∈ U, IsCoface p q) : R.RealizesSome t p U := by
  obtain ⟨q, hqU, hqc⟩ := hcand
  obtain ⟨y, hy, hq⟩ := hserv t p hp q hqc
  exact ⟨y, hy, q, hqU, hqc, hq⟩

/-! ### The candidate-existence bundle -/

/-- **Candidate existence**, one field per clause of Def. 3.2.1(4): for each realized
`(t, p)`, each clause's request family contains a coface of `p` — pure `S`-level existence,
no realization in the conclusion.  Fields (a)(i)/(a)(ii) are discharged outright by the
compiled Coface lemmas (`HasCandidates.of_band`); fields (b)/(c) are the surviving
obligations — both expected from the single exact-grade band candidate of #42 (see the
module docstring). -/
structure HasCandidates (R : KnightRealization α M) : Prop where
  /-- (a)(i): a generalised-saturation candidate over each supplied extension domain. -/
  genSat : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
    ∀ D : SemScheme (n + 1), ExtendsDomain p D →
      ∃ q ∈ GenSatFamily (α := α.1) D, IsCoface p q
  /-- (a)(ii): a prescribed-`−∞`-pattern candidate for each faithful respecting labelling
  `q'` of a supplied extension domain extending `p`. -/
  bottomPattern : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
    ∀ (D : SemScheme (n + 1)) (hD : ExtendsDomain p D) (q' : Cell D.scheme → ExtOrd),
      RespectsSemantics D.rows q' → (∀ d, q' (hD.cellOf d) = p.label d) →
      ∃ q ∈ BottomPatternFamily (α := α.1) D q', IsCoface p q
  /-- (b): a uniformity candidate — a cell labelled in `[γ, γ + ω)` — for each non-successor
  `γ < α`.  **Open**: expected from the band candidate at value `γ + (n + 1)`. -/
  uniformity : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
    ∀ γ : Ordinal.{0}, Value.IsNonSuccessor γ → γ < α.1 →
      ∃ q ∈ UniformityFamily (α := α.1) γ, IsCoface p q
  /-- (c): a high-grade-dominance candidate — a cell of grade `n + 1` labelled above `γ` —
  for each `γ < α`.  **Open**: expected from the band candidate at value
  `limitPart γ + max (n + 1) (finitePart γ + 1)`; its high-band case is gated on the
  `⊤`-flag production (#42 unresolved producer obligation 1). -/
  highGradeDominance : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
    ∀ γ : Ordinal.{0}, γ < α.1 →
      ∃ q ∈ HighGradeDominanceFamily (α := α.1) γ, IsCoface p q

/-- **The (a)-clauses need no supplied candidates**: a candidate bundle from the two open
fields alone.  (a)(i) is `StageType.genSatFamily_nonempty` and (a)(ii) is
`StageType.bottomPatternFamily_nonempty` — bountifulness of the supplied extension domain at
cutoff `⊥`, then truncation to `α` (`Knight/Coface.lean`); neither consults the realization.
The two consumed hypotheses are exactly the surviving candidate constructors of #42. -/
theorem HasCandidates.of_band
    (huni : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
      ∀ γ : Ordinal.{0}, Value.IsNonSuccessor γ → γ < α.1 →
        ∃ q ∈ UniformityFamily (α := α.1) γ, IsCoface p q)
    (hhigh : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
      ∀ γ : Ordinal.{0}, γ < α.1 →
        ∃ q ∈ HighGradeDominanceFamily (α := α.1) γ, IsCoface p q) :
    R.HasCandidates where
  genSat _ p _ D hD := StageType.genSatFamily_nonempty α.2 p D hD
  bottomPattern _ _p _ _D hD q' hq' hext :=
    StageType.bottomPatternFamily_nonempty α.2 hD q' hq' hext
  uniformity := huni
  highGradeDominance := hhigh

/-! ### The assembly theorem -/

/-- **Modelhood assembly** (#42, finite-block shortcut 1): exact consistency + initial-segment
covering + exact-copy servicing + candidate existence + a nonempty carrier make a model.
Each clause of Def. 3.2.1(4) is its candidate field composed with
`ServicesExactCopies.realizesSome` — no per-clause scheduling, no tuple-readiness
bookkeeping. -/
theorem isModel_of_candidates (hM : Nonempty M) (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (hserv : R.ServicesExactCopies)
    (hcand : R.HasCandidates) : R.IsModel where
  nonempty := hM
  consistent := hcons
  covering := hcov
  genSat t p hp D hD := hserv.realizesSome hp (hcand.genSat t p hp D hD)
  bottomPattern t p hp D hD q' hq' hext :=
    hserv.realizesSome hp (hcand.bottomPattern t p hp D hD q' hq' hext)
  uniformity t p hp γ hns hγ := hserv.realizesSome hp (hcand.uniformity t p hp γ hns hγ)
  highGradeDominance t p hp γ hγ :=
    hserv.realizesSome hp (hcand.highGradeDominance t p hp γ hγ)

/-- Modelhood assembly through the smart constructor: only the two open candidate
constructors — the (b)/(c) band candidates — must be supplied beyond clauses (2), (3) and
copy servicing; the (a)-candidates come from the compiled Coface lemmas. -/
theorem isModel_of_band_candidates (hM : Nonempty M) (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (hserv : R.ServicesExactCopies)
    (huni : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
      ∀ γ : Ordinal.{0}, Value.IsNonSuccessor γ → γ < α.1 →
        ∃ q ∈ UniformityFamily (α := α.1) γ, IsCoface p q)
    (hhigh : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
      ∀ γ : Ordinal.{0}, γ < α.1 →
        ∃ q ∈ HighGradeDominanceFamily (α := α.1) γ, IsCoface p q) : R.IsModel :=
  isModel_of_candidates hM hcons hcov hserv (HasCandidates.of_band huni hhigh)

end KnightRealization

end VaughtConjecture.Knight
