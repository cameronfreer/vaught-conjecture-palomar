/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Tower

/-! # Knight models: the axioms of Def. 3.2.1, clause by clause

Knight's Def. 3.2.1: for `α ≤ ω₁` a limit ordinal, a **model of `S^α`** with (nonempty)
domain `M` is a partial function `𝓜` from finite tuples on `M` to `S^α` such that

1. **(arity)** `𝓜(x)` is undefined when `x` repeats an entry, and `𝓜(x) ∈ S^α_n` when it is
   defined on a non-repeating `n`-tuple;
2. **(consistency)** if `𝓜(x) ∈ S^α_n` and `f : m ↪ n`, then `𝓜(x ∘ f) = (S^α f)(𝓜(x))` when
   the right side exists, and is undefined when it does not;
3. **(covering)** every non-repeating tuple `a` has some `x` with `a⌢x ∈ dom 𝓜`;
4. **(existential closure)** if `𝓜(x) = p` with `x` an `n`-tuple, and `U` is a subset of the
   **cofaces** `(S^α ι_{n,n+1})⁻¹(p)` of one of four kinds — (a)(i) generalised saturation,
   (a)(ii) a prescribed `−∞`-pattern, (b) uniformity, (c) high-arity dominance — then there
   are `y ∈ M` and `q ∈ U` with `𝓜(x⌢y) = q`.

Here a Knight model is a `TypeTower.Realization` of the Knight tower `knightTower`
(`KnightRealization`) satisfying `IsModel`, which transcribes the clauses:

* clause (1) is **automatic** from the encoding: `eval : (Fin n ↪ M) → Option (S α n)` is
  only defined on injective tuples and lands in the stage types of the same arity;
* clause (2) is `IsExactParentConsistent` (the exact `Option` equality `eval (f.trans t) =
  typeMap f q`, decided in #38 — `docs/DESIGN.md` §4);
* clause (3) is `IsInitialSegmentCovering` (the paper-literal form; equivalent to the generic
  `IsCovering` for Knight realizations by `knightTower_permTotal`, #38);
* clause (4) is stated once per family — `genSat`, `bottomPattern`, `uniformity`,
  `highGradeDominance` — each saying that **some member of that family** is realized over the
  old tuple as a coface (`RealizesSome`): never universal service of an arbitrary coface.  The
  four families are `GenSatFamily`, `BottomPatternFamily`, `UniformityFamily`,
  `HighGradeDominanceFamily`, with their parameter side conditions stated as hypotheses of the
  corresponding clause.

The paper's inclusion `ι_{n,n+1} : n ↪ n+1` is `Fin.castSuccEmb` (definitionally
`Fin.castAddEmb 1`, the embedding used by `IsInitialSegmentCovering`), the concatenation
`x⌢y` is `snoc`, and the cofaces of `p` are `Coface p`.  In the paper's vocabulary "the arity
of a cell" is our **grade** (`docs/TERMINOLOGY.md`), so (c) asks for a cell of grade `n+1`.

Two sibling-only reroutes of Knight-VC are **not** re-imported (`docs/CONCORDANCE.md`):
KVC-d23 (the `−∞`-pattern clause restricted to stage-bounded proto-types) — here the pattern
source `q'` is any labelling respecting the semantics of `D`, with **no stage bound**, as in
the paper; and KVC-d24 (the dominance witness asked for full scope, forgetting its grade) —
here the witness has grade `n+1`.

Positive-arity domains and stage types are constructed in `Knight.Domain` (#41 (1/3): mute
domains, their one-point extension with the face equation `ExtendsDomain` asks for, and a stage
type on every domain, Prop. 4.3.24); `IsModel` is a predicate with no instance in this file —
existence of models is #41/#42.  Reduction of a
model to a lower limit stage preserves clauses (2) and (3) (`IsModel.consistent_reduct`,
`IsModel.covering_reduct`, from the generic lemmas); preservation of the four
existential-closure clauses — full modelhood of the reduct, `IsModel.reduct` — is proved in
`Knight/ReductModel.lean` (#101; the `−∞`-pattern clause transfers by bountifulness at the
cutoff `n + 1`). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower
open CellScheme.restrictFace (toCell)

universe w

/-! ### Knight realizations, concatenation, cofaces -/

/-- A **Knight realization** at the limit stage `α` on the carrier `M`: a realization of the
Knight tower, i.e. a partial labelling of the injective finite tuples of `M` by stage types
`S α n` (the raw data of Def. 3.2.1, clause (1) built in). -/
abbrev KnightRealization (α : LimitStage) (M : Type w) := knightTower.Realization α M

variable {M : Type w} {n : ℕ}

/-- The concatenation `t⌢y` of an injective `n`-tuple `t` with a point `y` not on it, as an
injective `(n+1)`-tuple: `y` sits at the last position (`Fin.snoc`). -/
def snoc (t : Fin n ↪ M) (y : M) (hy : y ∉ Set.range t) : Fin (n + 1) ↪ M :=
  ⟨Fin.snoc (α := fun _ => M) t y, Fin.snoc_injective_of_injective t.injective hy⟩

@[simp] theorem snoc_apply_castSucc (t : Fin n ↪ M) (y : M) (hy : y ∉ Set.range t)
    (i : Fin n) : snoc t y hy (Fin.castSucc i) = t i := by
  simp [snoc]

@[simp] theorem snoc_apply_last (t : Fin n ↪ M) (y : M) (hy : y ∉ Set.range t) :
    snoc t y hy (Fin.last n) = y := by
  simp [snoc]

/-- The old tuple is the initial segment of its concatenation: `(t⌢y) ∘ ι_{n,n+1} = t`. -/
@[simp] theorem castSuccEmb_trans_snoc (t : Fin n ↪ M) (y : M) (hy : y ∉ Set.range t) :
    Fin.castSuccEmb.trans (snoc t y hy) = t := by
  ext i
  exact snoc_apply_castSucc t y hy i

variable {α : Ordinal.{0}}

/-- `q` is a **coface** of `p` (Def. 3.2.1(4)): `q ∈ S^α_{n+1}` restricts along the inclusion
`ι_{n,n+1}` (`Fin.castSuccEmb`) to `p`, i.e. `q ∈ (S^α ι_{n,n+1})⁻¹(p)`.  Knight-VC:
`CompatibleExtensionFiber`. -/
def IsCoface (p : S α n) (q : S α (n + 1)) : Prop :=
  typeMap Fin.castSuccEmb q = some p

/-- The cofaces of `p`, bundled. -/
abbrev Coface (p : S α n) : Type 1 := {q : S α (n + 1) // IsCoface p q}

/-- A domain `D` on `n+1` **extends the domain of `p`** along the initial face: the initial
segment `Fin.castSuccEmb` is visible in `D`'s plan and `D⟨n,n⟩ = dom p`, i.e. the restriction
of `D` (with its associated semantics) to that face is `p`'s domain.  This is the side
condition on `D` in Def. 3.2.1(4)(a). -/
structure ExtendsDomain (p : S α n) (D : SemScheme (n + 1)) : Prop where
  /-- The initial segment is a visible face of `D`'s plan. -/
  visible : Finset.univ.image Fin.castSuccEmb ∈ D.scheme.plan
  /-- `D⟨n,n⟩ = dom p`. -/
  restrict : D.restrictFace Fin.castSuccEmb visible = p.scheme

/-- Transport of cells along an equality of domains (`Cell X.scheme = Fin X.scheme.card`). -/
def SemScheme.castCell {X Y : SemScheme n} (h : X = Y) : Cell X.scheme → Cell Y.scheme :=
  Fin.cast (congrArg (fun Z : SemScheme n => Z.scheme.card) h)

/-- Cell transport along a self-equality is the identity (proof irrelevance). -/
theorem SemScheme.castCell_self {n : ℕ} {X : SemScheme n} (h : X = X) (d : Cell X.scheme) :
    SemScheme.castCell h d = d := rfl

/-- The cell map `dom p → D` of an extension of domains: the cell `d` of `dom p = D⟨n,n⟩` as
a cell of `D` (through the cell map of the face restriction, `toCell`). -/
noncomputable def ExtendsDomain.cellOf {p : S α n} {D : SemScheme (n + 1)}
    (h : ExtendsDomain p D) (d : Cell p.scheme.scheme) : Cell D.scheme :=
  toCell D.scheme Fin.castSuccEmb h.visible (SemScheme.castCell h.restrict.symm d)

/-- The domain of a coface of `p` extends the domain of `p`. -/
theorem IsCoface.extendsDomain {p : S α n} {q : S α (n + 1)} (h : IsCoface p q) :
    ExtendsDomain p q.scheme := by
  have hvis : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan :=
    (typeMap_isSome_iff _ q).mp (by rw [h]; rfl)
  refine ⟨hvis, ?_⟩
  unfold IsCoface at h
  rw [typeMap_eq_some _ q hvis, Option.some.injEq] at h
  subst h
  rfl

/-! ### The four request families of Def. 3.2.1(4)

Each is a set of stage types on `(n+1)`-tuples; the clause for the family asks that some
member be realized over the old tuple *as a coface of `p`* (the paper's `U ⊆ (S^α
ι_{n,n+1})⁻¹(p)`), so the coface condition is stated alongside membership in `RealizesSome`.
The parameter side conditions (`ExtendsDomain`, `RespectsSemantics`, `IsNonSuccessor`, `γ <
α`) are hypotheses of the corresponding `IsModel` clause. -/

/-- **(a)(i) Generalised saturation**: the cofaces with domain `D` (for `D` a domain on `n+1`
with `D⟨n,n⟩ = dom p`, the side condition `ExtendsDomain p D`). -/
def GenSatFamily (D : SemScheme (n + 1)) : Set (S α (n + 1)) :=
  {q | q.scheme = D}

/-- **(a)(ii) Prescribed `−∞`-pattern**: for `D` as in (a)(i) and a labelling `q' : D → ExtOrd`
respecting the semantics of `D` (faithfully, with **no stage bound**) and extending `p`, the
cofaces `q` with domain `D` whose `−∞`-pattern on `D^{≤ n} = D⟨A, n⟩` — the cells of grade
`≤ n`, `D.scheme.below (univ, n)` — is that of `q'`: `q Θ = ⊥ ↔ q' Θ = ⊥`. -/
def BottomPatternFamily (D : SemScheme (n + 1)) (q' : Cell D.scheme → ExtOrd) :
    Set (S α (n + 1)) :=
  {q | ∃ h : q.scheme = D, ∀ Θ : D.scheme.below (Finset.univ, n),
    q.label (SemScheme.castCell h.symm Θ.1) = ⊥ ↔ q' Θ.1 = ⊥}

/-- **(b) Uniformity**: for a non-successor `γ` with `0 ≤ γ < α`, the cofaces with a cell
labelled in `[γ, γ + ω)`. -/
def UniformityFamily (γ : Ordinal.{0}) : Set (S α (n + 1)) :=
  {q | ∃ Sig : Cell q.scheme.scheme,
    ExtOrd.ofOrd γ ≤ q.label Sig ∧ q.label Sig < ExtOrd.ofOrd (γ + Ordinal.omega0)}

/-- **(c) High-grade dominance** (Knight: "high-arity"): for `γ < α`, the cofaces with a cell
of grade `n+1` labelled strictly above `γ`. -/
def HighGradeDominanceFamily (γ : Ordinal.{0}) : Set (S α (n + 1)) :=
  {q | ∃ Sig : Cell q.scheme.scheme,
    q.scheme.scheme.grade Sig = n + 1 ∧ ExtOrd.ofOrd γ < q.label Sig}

/-! ### Models -/

namespace KnightRealization

variable {α : LimitStage} (R : KnightRealization α M)

/-- `R` **realizes some member of `U` over `t` as a coface of `p`** (the conclusion of
Def. 3.2.1(4)): there are `y ∈ M` off `t` and `q ∈ U`, a coface of `p`, with
`R(t⌢y) = q`. -/
def RealizesSome (t : Fin n ↪ M) (p : S α.1 n) (U : Set (S α.1 (n + 1))) : Prop :=
  ∃ (y : M) (hy : y ∉ Set.range t) (q : S α.1 (n + 1)),
    q ∈ U ∧ IsCoface p q ∧ R.eval (snoc t y hy) = some q

/-- A **model of `S^α`** (Knight, Def. 3.2.1), clause by clause.  Clause (1) (arity) is
automatic from the encoding of `KnightRealization`; the carrier is required nonempty. -/
structure IsModel : Prop where
  /-- The domain `M` is nonempty.  Logically redundant — covering labels the empty tuple and
  clause (4)(b)/(c) at `0 < α` then produces a point (see `IsModel.infinite_carrier`) — but
  retained for fidelity to the paper's statement. -/
  nonempty : Nonempty M
  /-- Clause (2), consistency: the label of a face is the partial restriction of the label
  (exact `Option` equality, #38). -/
  consistent : R.IsExactParentConsistent
  /-- Clause (3), covering: every injective tuple is an initial segment of a labelled one. -/
  covering : R.IsInitialSegmentCovering
  /-- Clause (4)(a)(i), generalised saturation: for every domain `D` on `n+1` with
  `D⟨n,n⟩ = dom p`, some coface of `p` with domain `D` is realized over `t`. -/
  genSat : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
    ∀ D : SemScheme (n + 1), ExtendsDomain p D → R.RealizesSome t p (GenSatFamily D)
  /-- Clause (4)(a)(ii), prescribed `−∞`-pattern: for `D` as in (a)(i) and every labelling
  `q'` of `D` respecting its semantics (no stage bound) and extending `p` along the cell map
  of the initial face, some coface of `p` with domain `D` and the `−∞`-pattern of `q'` on
  `D^{≤ n}` is realized over `t`. -/
  bottomPattern : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
    ∀ (D : SemScheme (n + 1)) (hD : ExtendsDomain p D) (q' : Cell D.scheme → ExtOrd),
      RespectsSemantics D.rows q' → (∀ d, q' (hD.cellOf d) = p.label d) →
      R.RealizesSome t p (BottomPatternFamily D q')
  /-- Clause (4)(b), uniformity: for every non-successor `γ` (zero or a limit) below `α`, some
  coface of `p` with a label in `[γ, γ + ω)` is realized over `t`. -/
  uniformity : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
    ∀ γ : Ordinal.{0}, Value.IsNonSuccessor γ → γ < α.1 →
      R.RealizesSome t p (UniformityFamily γ)
  /-- Clause (4)(c), high-grade dominance: for every `γ < α`, some coface of `p` with a cell
  of grade `n+1` labelled above `γ` is realized over `t`. -/
  highGradeDominance : ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
    ∀ γ : Ordinal.{0}, γ < α.1 → R.RealizesSome t p (HighGradeDominanceFamily γ)

variable {R}

/-- Under exact consistency (clause (2)), the label of a concatenation `t⌢y` is automatically a
coface of the label of `t`: the coface condition in the existential-closure clauses is then
redundant, and is kept only to transcribe the paper's `U ⊆ (S^α ι_{n,n+1})⁻¹(p)`. -/
theorem isCoface_of_consistent (hR : R.IsExactParentConsistent) {t : Fin n ↪ M}
    {p : S α.1 n} {y : M} {hy : y ∉ Set.range t} {q : S α.1 (n + 1)}
    (hp : R.eval t = some p) (hq : R.eval (snoc t y hy) = some q) : IsCoface p q := by
  have h := hR (snoc t y hy) q Fin.castSuccEmb hq
  rw [castSuccEmb_trans_snoc, hp] at h
  exact h.symm

/-- A model is visible-face consistent (the generic hypothesis of the `TypeTower` theorems). -/
theorem IsModel.isVisibleFaceConsistent (h : R.IsModel) : R.IsVisibleFaceConsistent :=
  h.consistent.isVisibleFaceConsistent

/-- A model is covering in the generic sense. -/
theorem IsModel.isCovering (h : R.IsModel) : R.IsCovering :=
  h.covering.isCovering

/-- The reduct of a model to a lower limit stage is exactly consistent (clause (2) is preserved
under reduction; generic). -/
theorem IsModel.consistent_reduct (h : R.IsModel) {β : LimitStage} (hβ : β ≤ α) :
    (R.reduct hβ).IsExactParentConsistent :=
  h.consistent.reduct hβ

/-- The reduct of a model to a lower limit stage is initial-segment covering (clause (3) is
preserved under reduction; generic).  The existential-closure clauses are preserved too
(`IsModel.reduct`, `Knight/ReductModel.lean`). -/
theorem IsModel.covering_reduct (h : R.IsModel) {β : LimitStage} (hβ : β ≤ α) :
    (R.reduct hβ).IsInitialSegmentCovering :=
  h.covering.reduct hβ

/-! ### Every model is infinite

Clause (3) labels the empty tuple (an initial segment of some labelled tuple), and clause
(4)(c) at `γ = 0 < α` (or (4)(b) at the non-successor `0`) realizes a coface over every labelled
tuple — with a **fresh** point `y ∉ range t`.  So labelled injective tuples exist in every arity
beyond some `m`, and the carrier is infinite.  No domain construction (#41) is involved: the
model's own existential-closure clauses supply the new points (cf. `NoTop.lean`, which uses the
same two clauses and counting for `α = ω₁`). -/

/-- From a labelled `m`-tuple, a labelled `(m + k)`-tuple for every `k` (clause (4)(c) at `0`). -/
theorem IsModel.exists_labelled_add (h : R.IsModel) {m : ℕ} (t : Fin m ↪ M)
    (ht : (R.eval t).isSome) (k : ℕ) : ∃ s : Fin (m + k) ↪ M, (R.eval s).isSome := by
  induction k with
  | zero => exact ⟨t, ht⟩
  | succ k ih =>
    obtain ⟨s, hs⟩ := ih
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
    have h0 : (0 : Ordinal.{0}) < α.1 := by
      simpa [Ordinal.bot_eq_zero] using α.2.bot_lt
    obtain ⟨y, hy, q, -, -, hq⟩ := h.highGradeDominance s p hp 0 h0
    exact ⟨snoc s y hy, by rw [hq]; rfl⟩

/-- A labelled injective tuple of every sufficiently large arity. -/
theorem IsModel.exists_labelled_ge (h : R.IsModel) :
    ∃ m : ℕ, ∀ k : ℕ, ∃ s : Fin (m + k) ↪ M, (R.eval s).isSome := by
  obtain ⟨k, s, -, hs⟩ := h.covering (Function.Embedding.ofIsEmpty : Fin 0 ↪ M)
  exact ⟨0 + k, fun j => h.exists_labelled_add s hs j⟩

/-- **Every model of `S^α` is infinite** (any limit stage `α`): the ℕ-tier form of "`T` has no
finite models" (Prop. 3.3.5 / `HasNoFiniteModels` in `Knight/Sentence.lean`). -/
theorem IsModel.infinite_carrier (h : R.IsModel) : Infinite M := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  obtain ⟨m, hm⟩ := h.exists_labelled_ge
  letI := Fintype.ofFinite M
  obtain ⟨s, -⟩ := hm (Fintype.card M + 1)
  have := Fintype.card_le_of_embedding s
  simp only [Fintype.card_fin] at this
  omega

end KnightRealization

end VaughtConjecture.Knight
