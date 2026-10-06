/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Fin.Embedding
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Basic

/-! # Type towers

A *type tower* (partial by definition: restriction is only along visible faces) is the minimal abstraction of Knight's systems `S^α_n`:
for each level `α` (an element of a preordered type `Λ`, `Ordinal` in the
application) and arity `n`, a type of *stage-`α` types on `n`-tuples*, with

* a **partial horizontal restriction** `pull f : Ty α n → Option (Ty α m)` along
  each injection `f : Fin m ↪ Fin n` (only *visible* faces have restrictions —
  this partiality is a load-bearing feature, not an API defect);
* a **total vertical reduction** `reduce : α ≤ β → Ty β n → Ty α n`;
* functoriality of each, and commutation of the two.

Deliberate omissions (see `docs/DESIGN.md`): topology, total restriction along
every injection, one-point requests, model existence, characteristic arity,
hollowness, and any imagined language `L^α`.  Those enter only through the
Knight instance or through later, separately-justified interfaces.

Functoriality of `pull` is **conditional composition**, not ordinary
partial-map (Kleisli) composition: `pull_trans` constrains the composite only
when the intermediate face is visible, because a small face can be visible
while an intermediate one is not.

A *realization* of level `α` on a carrier `M` is a partial labelling of
injective finite tuples by stage-`α` types.  Two consistency notions are kept
(calibrated against Knight's Def. 3.2.1 in `docs/DESIGN.md` §4, #38):

* `IsVisibleFaceConsistent` — a visible face of a labelled tuple carries the
  restricted type (an invisible face receives no information *from this
  occurrence*); the weaker generic notion, the hypothesis of the generic
  theorems;
* `IsExactParentConsistent` — the face label *equals* the partial pullback, so
  an invisible face of a labelled tuple is unlabelled.  This is the paper's
  consistency clause (Def. 3.2.1(2)) and Knight-VC's
  `PaperExactModel.IsParentConsistent` (`eval (t.restrict f) = typeMap f q`).

Likewise two coverings: the generic `IsCovering` (every tuple is *some* face of a labelled
tuple) and the paper-literal `IsInitialSegmentCovering` (Def. 3.2.1(3): every tuple is an
*initial segment* of a labelled tuple).  Initial-segment covering implies covering; the
converse holds whenever `pull` is total along permutations (`TypeTower.PermTotal`) and the
realization is visible-face consistent (`IsCovering.toInitialSegment`) — in particular for
the Knight tower (`Knight.knightTower_permTotal`).

Exact implies visible-face; passing to the reduct preserves both, and covering.

Isomorphisms of realizations (`Realization.IsIso`, `Iso`: a bijection of carriers transporting
labels; `isoSetoid`), the push-forward `Realization.map` along a bijection (`IsIso.map_eq`: an
isomorphic realization *is* a push-forward), reduction of isomorphisms (`Iso.reduct`), and the
transport of all four predicates along isomorphisms (`IsIso.isExactParentConsistent_iff`, …)
close the file; they are the interface consumed by `Approximation/Prolongation.lean`. -/

@[expose] public section

namespace VaughtConjecture

universe u v w

/-- Every injection `f : Fin n ↪ Fin (n + k)` extends to a permutation of `Fin (n + k)` that
sends the initial segment `Fin.castAdd k i` to `f i`. -/
theorem exists_perm_castAdd_eq {n k : ℕ} (f : Fin n ↪ Fin (n + k)) :
    ∃ σ : Equiv.Perm (Fin (n + k)), ∀ i, σ (Fin.castAdd k i) = f i := by
  classical
  let e : {x // x ∈ Set.range (Fin.castAdd (n := n) k)} ≃ {x // x ∈ Set.range f} :=
    (Equiv.ofInjective (Fin.castAdd k) (Fin.castAdd_injective n k)).symm.trans
      (Equiv.ofInjective f f.injective)
  refine ⟨e.extendSubtype, fun i => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e _ ⟨i, rfl⟩]
  simp [e]

/-- A type tower over the levels `Λ`.  Restriction is partial; reduction is total. -/
structure TypeTower (Λ : Type v) [Preorder Λ] where
  /-- Stage-`α` types on `n`-tuples. -/
  Ty : Λ → ℕ → Type u
  /-- Partial horizontal restriction along an injection; `none` means the face is invisible. -/
  pull : ∀ {α : Λ} {m n : ℕ}, (Fin m ↪ Fin n) → Ty α n → Option (Ty α m)
  /-- Total vertical reduction (truncation) from level `β` down to `α ≤ β`. -/
  reduce : ∀ {α β : Λ}, α ≤ β → ∀ {n : ℕ}, Ty β n → Ty α n
  pull_refl : ∀ {α : Λ} {n : ℕ} (q : Ty α n), pull (Function.Embedding.refl (Fin n)) q = some q
  /-- Conditional composition: if the face `f` is visible, then restricting further along `g`
  through it agrees with restricting along the composite.  Nothing is asserted when `f` is
  invisible (the composite face may still be visible). -/
  pull_trans : ∀ {α : Λ} {k m n : ℕ} (f : Fin m ↪ Fin n) (g : Fin k ↪ Fin m)
    (r : Ty α n) (q : Ty α m), pull f r = some q → pull (g.trans f) r = pull g q
  reduce_refl : ∀ {α : Λ} {n : ℕ} (q : Ty α n), reduce le_rfl q = q
  reduce_trans : ∀ {α β γ : Λ} (hαβ : α ≤ β) (hβγ : β ≤ γ) {n : ℕ} (r : Ty γ n),
    reduce hαβ (reduce hβγ r) = reduce (hαβ.trans hβγ) r
  /-- Reduction does not change visibility, and commutes with restriction. -/
  pull_reduce : ∀ {α β : Λ} (h : α ≤ β) {m n : ℕ} (f : Fin m ↪ Fin n) (q : Ty β n),
    pull f (reduce h q) = (pull f q).map (reduce h)

namespace TypeTower

variable {Λ : Type v} [Preorder Λ] (T : TypeTower.{u} Λ)

/-- **Permutation-total pull**: restriction along every bijection `Fin n ≃ Fin n` is defined
(the whole tuple, re-ordered, is always a visible face).  Knight's tower has it
(`Knight.knightTower_permTotal`: the domain is a visible face of every plan, Lemma 2.4.3 /
`IsPlan.domain_mem`); it is the hypothesis under which initial-segment covering and generic
covering coincide (`Realization.IsCovering.toInitialSegment`). -/
def PermTotal : Prop :=
  ∀ {α : Λ} {n : ℕ} (σ : Fin n ≃ Fin n) (q : T.Ty α n), (T.pull σ.toEmbedding q).isSome

/-- A partial labelling of the injective finite tuples of `M` by stage-`α` types. -/
structure Realization (α : Λ) (M : Type w) where
  /-- The (partial) type of a tuple. -/
  eval : ∀ {n : ℕ}, (Fin n ↪ M) → Option (T.Ty α n)

namespace Realization

variable {T} {α β : Λ} {M : Type w}

/-- Two realizations with the same labels are equal. -/
@[ext]
theorem ext {R R' : T.Realization α M}
    (h : ∀ {n : ℕ} (t : Fin n ↪ M), R.eval t = R'.eval t) : R = R' := by
  cases R with
  | mk eval =>
    cases R' with
    | mk eval' =>
      simp only [Realization.mk.injEq]
      funext n t
      exact h t

/-- **Visible-face consistency**: whenever a tuple has a type and a face is visible in that
type, the face tuple carries the restricted type.  Invisible faces are unconstrained. -/
def IsVisibleFaceConsistent (R : T.Realization α M) : Prop :=
  ∀ ⦃m n : ℕ⦄ (t : Fin n ↪ M) (q : T.Ty α n) (f : Fin m ↪ Fin n) (p : T.Ty α m),
    R.eval t = some q → T.pull f q = some p → R.eval (f.trans t) = some p

/-- **Exact parent consistency**: whenever a tuple has a type, every face tuple carries exactly
the partial pullback — so an invisible face of a labelled tuple is unlabelled.  This is the
Knight-VC notion (`PaperExactModel.IsParentConsistent`). -/
def IsExactParentConsistent (R : T.Realization α M) : Prop :=
  ∀ ⦃m n : ℕ⦄ (t : Fin n ↪ M) (q : T.Ty α n) (f : Fin m ↪ Fin n),
    R.eval t = some q → R.eval (f.trans t) = T.pull f q

theorem IsExactParentConsistent.isVisibleFaceConsistent {R : T.Realization α M}
    (hR : R.IsExactParentConsistent) : R.IsVisibleFaceConsistent :=
  fun _ _ t q f _p hq hp => (hR t q f hq).trans hp

/-- **Covering** (generic): every injective finite tuple is a face of some labelled tuple. -/
def IsCovering (R : T.Realization α M) : Prop :=
  ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M),
    ∃ (m : ℕ) (s : Fin m ↪ M) (f : Fin n ↪ Fin m), f.trans s = t ∧ (R.eval s).isSome

/-- **Initial-segment covering** (Knight, Def. 3.2.1(3); Knight-VC
`PaperExactModel.IsInitialSegmentCovering`): every injective finite tuple is an *initial
segment* of some labelled tuple. -/
def IsInitialSegmentCovering (R : T.Realization α M) : Prop :=
  ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M),
    ∃ (k : ℕ) (s : Fin (n + k) ↪ M), (Fin.castAddEmb k).trans s = t ∧ (R.eval s).isSome

/-- Initial-segment covering is a covering. -/
theorem IsInitialSegmentCovering.isCovering {R : T.Realization α M}
    (hR : R.IsInitialSegmentCovering) : R.IsCovering := by
  intro n t
  obtain ⟨k, s, hst, hs⟩ := hR t
  exact ⟨n + k, s, Fin.castAddEmb k, hst, hs⟩

/-- Under permutation-total pull and visible-face consistency, generic covering is
initial-segment covering: re-order the covering tuple so that the given tuple becomes its
initial segment; the re-ordered tuple is labelled by the (total) pullback along the
permutation.  Exact parent consistency is not needed. -/
theorem IsCovering.toInitialSegment (hT : T.PermTotal) {R : T.Realization α M}
    (hR : R.IsVisibleFaceConsistent) (hc : R.IsCovering) : R.IsInitialSegmentCovering := by
  intro n t
  obtain ⟨m, s, f, hfs, hs⟩ := hc t
  have hnm : n ≤ m := by simpa using Fintype.card_le_of_embedding f
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  obtain ⟨σ, hσ⟩ := exists_perm_castAdd_eq f
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hT σ q)
  refine ⟨k, σ.toEmbedding.trans s, ?_, ?_⟩
  · ext i
    simp [← hfs, hσ]
  · rw [hR s q σ.toEmbedding p hq hp]
    rfl

/-- The **reduct** of a realization to a lower stage: truncate every label. -/
def reduct (h : α ≤ β) (R : T.Realization β M) : T.Realization α M where
  eval t := (R.eval t).map (T.reduce h)

@[simp]
theorem reduct_eval (h : α ≤ β) (R : T.Realization β M) {n : ℕ} (t : Fin n ↪ M) :
    (R.reduct h).eval t = (R.eval t).map (T.reduce h) := rfl

theorem reduct_refl (R : T.Realization α M) : R.reduct le_rfl = R := by
  cases R with
  | mk eval =>
    simp only [reduct, Realization.mk.injEq]
    funext n t
    cases eval t <;> simp [T.reduce_refl]

theorem reduct_reduct {γ : Λ} (hαβ : α ≤ β) (hβγ : β ≤ γ) (R : T.Realization γ M) :
    (R.reduct hβγ).reduct hαβ = R.reduct (hαβ.trans hβγ) := by
  cases R with
  | mk eval =>
    simp only [reduct, Realization.mk.injEq]
    funext n t
    cases eval t <;> simp [T.reduce_trans]

/-- Reduction preserves visible-face consistency. -/
theorem IsVisibleFaceConsistent.reduct (h : α ≤ β) {R : T.Realization β M}
    (hR : R.IsVisibleFaceConsistent) : (R.reduct h).IsVisibleFaceConsistent := by
  intro m n t q f p hq hp
  simp only [reduct_eval, Option.map_eq_some_iff] at hq ⊢
  obtain ⟨q', hq', rfl⟩ := hq
  rw [T.pull_reduce, Option.map_eq_some_iff] at hp
  obtain ⟨p', hp', rfl⟩ := hp
  exact ⟨p', hR t q' f p' hq' hp', rfl⟩

/-- Reduction preserves exact parent consistency. -/
theorem IsExactParentConsistent.reduct (h : α ≤ β) {R : T.Realization β M}
    (hR : R.IsExactParentConsistent) : (R.reduct h).IsExactParentConsistent := by
  intro m n t q f hq
  simp only [reduct_eval, Option.map_eq_some_iff] at hq
  obtain ⟨q', hq', rfl⟩ := hq
  rw [reduct_eval, hR t q' f hq', T.pull_reduce]

/-- Reduction preserves covering. -/
theorem IsCovering.reduct (h : α ≤ β) {R : T.Realization β M}
    (hR : R.IsCovering) : (R.reduct h).IsCovering := by
  intro n t
  obtain ⟨m, s, f, hfs, hs⟩ := hR t
  exact ⟨m, s, f, hfs, by simpa using hs⟩

/-- Reduction preserves initial-segment covering (the Knight model axiom, Def. 3.2.1(3)): the same
initial-segment witness, since reduction preserves definedness of labels. -/
theorem IsInitialSegmentCovering.reduct (h : α ≤ β) {R : T.Realization β M}
    (hR : R.IsInitialSegmentCovering) : (R.reduct h).IsInitialSegmentCovering := by
  intro n t
  obtain ⟨k, s, hs, hsome⟩ := hR t
  exact ⟨k, s, hs, by simpa using hsome⟩

/-! ### Dot-notation tests (#99)

The four predicates above take their leading `ℕ` binders strict-implicitly (`⦃m n⦄`) so that
dot-notation projections elaborate (with plain implicit binders Lean eagerly instantiates the
metavariables and the projections fail).  One `example` per predicate, as tests only. -/

section DotNotationTests

example (h : α ≤ β) {R : T.Realization β M} (hR : R.IsVisibleFaceConsistent) :
    (R.reduct h).IsVisibleFaceConsistent := hR.reduct h

example {R : T.Realization α M} (hR : R.IsExactParentConsistent) :
    R.IsVisibleFaceConsistent := hR.isVisibleFaceConsistent

example (h : α ≤ β) {R : T.Realization β M} (hR : R.IsCovering) :
    (R.reduct h).IsCovering := hR.reduct h

example {R : T.Realization α M} (hR : R.IsInitialSegmentCovering) :
    R.IsCovering := hR.isCovering

end DotNotationTests

/-! ### Isomorphisms of realizations

A bijection of carriers is an isomorphism of realizations when it transports labels: the label
of every injective tuple is the label of its image.  This is the generic form of Knight-VC's
`PaperExactModelIso` (`PORTING.md`), and the notion of "model of `S^ω` up to isomorphism" counted
by Prop. 3.3.5 (`Knight.Correspondence`). -/

section Iso

universe w'

variable {N : Type w'} {P : Type*}

/-- `e : M ≃ N` is an **isomorphism** from `R` to `R'`: every injective tuple of `M` and its image
under `e` carry the same label. -/
def IsIso (R : T.Realization α M) (R' : T.Realization α N) (e : M ≃ N) : Prop :=
  ∀ {n : ℕ} (t : Fin n ↪ M), R'.eval (t.trans e.toEmbedding) = R.eval t

/-- The isomorphisms from `R` to `R'` (bijections of carriers transporting labels). -/
def Iso (R : T.Realization α M) (R' : T.Realization α N) : Type (max w w') :=
  {e : M ≃ N // R.IsIso R' e}

theorem IsIso.refl (R : T.Realization α M) : R.IsIso R (Equiv.refl M) := fun t => by
  congr 1

theorem IsIso.symm {R : T.Realization α M} {R' : T.Realization α N} {e : M ≃ N}
    (h : R.IsIso R' e) : R'.IsIso R e.symm := fun t => by
  rw [← h (t.trans e.symm.toEmbedding)]
  congr 1
  ext i
  simp

theorem IsIso.trans {R : T.Realization α M} {R' : T.Realization α N} {R'' : T.Realization α P}
    {e : M ≃ N} {e' : N ≃ P} (h : R.IsIso R' e) (h' : R'.IsIso R'' e') :
    R.IsIso R'' (e.trans e') := fun t => by
  rw [← h t, ← h' (t.trans e.toEmbedding)]
  congr 1

/-- The identity isomorphism. -/
def Iso.refl (R : T.Realization α M) : R.Iso R := ⟨Equiv.refl M, IsIso.refl R⟩

/-- The inverse of an isomorphism. -/
def Iso.symm {R : T.Realization α M} {R' : T.Realization α N} (i : R.Iso R') : R'.Iso R :=
  ⟨i.1.symm, IsIso.symm i.2⟩

/-- Composition of isomorphisms. -/
def Iso.trans {R : T.Realization α M} {R' : T.Realization α N} {R'' : T.Realization α P}
    (i : R.Iso R') (i' : R'.Iso R'') : R.Iso R'' :=
  ⟨i.1.trans i'.1, IsIso.trans i.2 i'.2⟩

variable (T α M) in
/-- **Realizations up to isomorphism**: the ambient equivalence relation "`R` and `R'` are
isomorphic" on the stage-`α` realizations on the carrier `M`. -/
def isoSetoid : Setoid (T.Realization α M) where
  r R R' := Nonempty (R.Iso R')
  iseqv :=
    { refl := fun R => ⟨Iso.refl R⟩
      symm := fun ⟨i⟩ => ⟨i.symm⟩
      trans := fun ⟨i⟩ ⟨i'⟩ => ⟨i.trans i'⟩ }

theorem isoSetoid_r_iff {R R' : T.Realization α M} :
    (isoSetoid T α M).r R R' ↔ Nonempty (R.Iso R') := Iff.rfl

/-! #### Transport along a carrier bijection

`R.map e` is the push-forward of `R` along `e : M ≃ N`: the labelling of `N` in which the image
tuple `t.trans e` carries the label of `t`.  It is the canonical realization on `N` isomorphic to
`R` (`isIso_map`), and it commutes with reduction (`reduct_map`).  This is the generic form of
Knight-VC's identity-carrier re-indexing; it is what lets a prolongation target on any carrier be
moved onto the carrier of the source (`Approximation/Prolongation.lean`). -/

/-- Push a realization forward along a bijection of carriers:
`(R.map e).eval s = R.eval (s ∘ e⁻¹)`. -/
def map (e : M ≃ N) (R : T.Realization α M) : T.Realization α N where
  eval s := R.eval (s.trans e.symm.toEmbedding)

@[simp]
theorem map_eval (e : M ≃ N) (R : T.Realization α M) {n : ℕ} (s : Fin n ↪ N) :
    (R.map e).eval s = R.eval (s.trans e.symm.toEmbedding) := rfl

/-- `e` is an isomorphism from `R` to its push-forward `R.map e`. -/
theorem isIso_map (e : M ≃ N) (R : T.Realization α M) : R.IsIso (R.map e) e := fun t => by
  simp only [map_eval]
  congr 1
  ext i
  simp

/-- The push-forward as an isomorphism `R ≅ R.map e`. -/
def Iso.map (e : M ≃ N) (R : T.Realization α M) : R.Iso (R.map e) := ⟨e, isIso_map e R⟩

/-- The push-forward of `R` along an isomorphism `R ≅ R'` is `R'` itself: `R.map e = R'`.  So an
isomorphism class on a fixed carrier is an orbit of `map` under the carrier's bijections, and a
realization isomorphic to `R` on any carrier is a push-forward of `R`. -/
theorem IsIso.map_eq {R : T.Realization α M} {R' : T.Realization α N} {e : M ≃ N}
    (h : R.IsIso R' e) : R.map e = R' := by
  refine Realization.ext fun s => ?_
  rw [map_eval, ← h (s.trans e.symm.toEmbedding)]
  congr 1
  ext i
  simp

theorem map_symm_map (e : M ≃ N) (R : T.Realization α M) : (R.map e).map e.symm = R :=
  IsIso.map_eq (IsIso.symm (isIso_map e R))

@[simp]
theorem reduct_map (h : α ≤ β) (e : M ≃ N) (R : T.Realization β M) :
    (R.map e).reduct h = (R.reduct h).map e := rfl

/-! #### Isomorphism and reduction

An isomorphism of stage-`β` realizations is an isomorphism of their stage-`α` reducts along the
same bijection (Knight-VC's `PaperExactModelIso.truncTo`). -/

theorem IsIso.reduct (h : α ≤ β) {R : T.Realization β M} {R' : T.Realization β N} {e : M ≃ N}
    (hi : R.IsIso R' e) : (R.reduct h).IsIso (R'.reduct h) e := fun t => by
  simp only [reduct_eval, hi t]

/-- Reduce an isomorphism of stage-`β` realizations to stage `α ≤ β`. -/
def Iso.reduct (h : α ≤ β) {R : T.Realization β M} {R' : T.Realization β N} (i : R.Iso R') :
    (R.reduct h).Iso (R'.reduct h) := ⟨i.1, IsIso.reduct h i.2⟩

/-! #### Transport of the consistency and covering predicates

Each of the four predicates of `Realization` is invariant under isomorphism: the one-directional
transports `IsIso.isVisibleFaceConsistent` etc. and the `iff` forms. -/

/-- Under `h : R.IsIso R' e`, a tuple of `N` pulled back along `e⁻¹` and pushed forward again is
itself; this is the computation behind every transport below. -/
theorem IsIso.eval_trans_symm {R : T.Realization α M} {R' : T.Realization α N} {e : M ≃ N}
    (h : R.IsIso R' e) {n : ℕ} (s : Fin n ↪ N) :
    R.eval (s.trans e.symm.toEmbedding) = R'.eval s :=
  h.symm s

theorem IsIso.isVisibleFaceConsistent {R : T.Realization α M} {R' : T.Realization α N} {e : M ≃ N}
    (h : R.IsIso R' e) (hR : R.IsVisibleFaceConsistent) : R'.IsVisibleFaceConsistent := by
  intro m n s q f p hq hp
  have hs : R.eval (s.trans e.symm.toEmbedding) = some q := by rw [h.eval_trans_symm, hq]
  have := hR (s.trans e.symm.toEmbedding) q f p hs hp
  rw [← h.eval_trans_symm]
  convert this using 2
  ext i
  simp

theorem IsIso.isVisibleFaceConsistent_iff {R : T.Realization α M} {R' : T.Realization α N}
    {e : M ≃ N} (h : R.IsIso R' e) :
    R.IsVisibleFaceConsistent ↔ R'.IsVisibleFaceConsistent :=
  ⟨h.isVisibleFaceConsistent, IsIso.isVisibleFaceConsistent (IsIso.symm h)⟩

theorem IsIso.isExactParentConsistent {R : T.Realization α M} {R' : T.Realization α N}
    {e : M ≃ N} (h : R.IsIso R' e) (hR : R.IsExactParentConsistent) :
    R'.IsExactParentConsistent := by
  intro m n s q f hq
  have hs : R.eval (s.trans e.symm.toEmbedding) = some q := by rw [h.eval_trans_symm, hq]
  have := hR (s.trans e.symm.toEmbedding) q f hs
  rw [← h.eval_trans_symm]
  convert this using 2
  ext i
  simp

theorem IsIso.isExactParentConsistent_iff {R : T.Realization α M} {R' : T.Realization α N}
    {e : M ≃ N} (h : R.IsIso R' e) :
    R.IsExactParentConsistent ↔ R'.IsExactParentConsistent :=
  ⟨h.isExactParentConsistent, IsIso.isExactParentConsistent (IsIso.symm h)⟩

theorem IsIso.isCovering {R : T.Realization α M} {R' : T.Realization α N} {e : M ≃ N}
    (h : R.IsIso R' e) (hR : R.IsCovering) : R'.IsCovering := by
  intro n s
  obtain ⟨m, u, f, hfu, hu⟩ := hR (s.trans e.symm.toEmbedding)
  refine ⟨m, u.trans e.toEmbedding, f, ?_, by rwa [h u]⟩
  ext i
  have := congrArg (fun v : Fin n ↪ M => e (v i)) hfu
  simpa using this

theorem IsIso.isCovering_iff {R : T.Realization α M} {R' : T.Realization α N} {e : M ≃ N}
    (h : R.IsIso R' e) : R.IsCovering ↔ R'.IsCovering :=
  ⟨h.isCovering, IsIso.isCovering (IsIso.symm h)⟩

theorem IsIso.isInitialSegmentCovering {R : T.Realization α M} {R' : T.Realization α N}
    {e : M ≃ N} (h : R.IsIso R' e) (hR : R.IsInitialSegmentCovering) :
    R'.IsInitialSegmentCovering := by
  intro n s
  obtain ⟨k, u, hu, hsome⟩ := hR (s.trans e.symm.toEmbedding)
  refine ⟨k, u.trans e.toEmbedding, ?_, by rwa [h u]⟩
  ext i
  have := congrArg (fun v : Fin n ↪ M => e (v i)) hu
  simpa using this

theorem IsIso.isInitialSegmentCovering_iff {R : T.Realization α M} {R' : T.Realization α N}
    {e : M ≃ N} (h : R.IsIso R' e) :
    R.IsInitialSegmentCovering ↔ R'.IsInitialSegmentCovering :=
  ⟨h.isInitialSegmentCovering, IsIso.isInitialSegmentCovering (IsIso.symm h)⟩

end Iso

end Realization

end TypeTower

end VaughtConjecture
