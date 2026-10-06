/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Scott.GradedMatching

/-! # Projected finite-template extension systems

Exact labels belong to independent source and target template types. Compatibility is a
separate relation, not equality of these labels. Matching receipts retain finite covers and
selectors, so tuples may repeat coordinates or be empty. Extension retains the entire root
cover literally. Only the BF comparison, not an isomorphism, is concluded.
-/

@[expose] public section

namespace VaughtConjecture.ModelTheory

open FirstOrder Language

universe u v w w' r s t

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- Ranked receipts up to a specified budget, with explicit atomic and extension evidence.
No seed is built into the laws: the comparison theorem requires an actual initial receipt. -/
structure RankedMatchingFamily (L : Language.{u, v}) (M : Type w) (N : Type w')
    [L.IsRelational] [L.Structure M] [L.Structure N] (height : Ordinal) where
  Receipt : Ordinal → (n : ℕ) → (Fin n → M) → (Fin n → N) → Type r
  atomic : ∀ {n a b}, Receipt 0 n a b → SameAtomicType (L := L) a b
  lower : ∀ {α β n a b}, β ≤ α → α ≤ height → Receipt α n a b →
    Nonempty (Receipt β n a b)
  forth : ∀ {α n a b}, α + 1 ≤ height → Receipt (α + 1) n a b → ∀ x : M,
    ∃ y : N, Nonempty (Receipt α (n + 1) (Fin.snoc a x) (Fin.snoc b y))
  back : ∀ {α n a b}, α + 1 ≤ height → Receipt (α + 1) n a b → ∀ y : N,
    ∃ x : M, Nonempty (Receipt α (n + 1) (Fin.snoc a x) (Fin.snoc b y))

namespace RankedMatchingFamily

/-- A receipt family compares its explicitly matched tuples at the requested budget.
The library owns the ordinal induction; the local family supplies its laws and seed. -/
theorem bfEquiv_of_nonempty {height : Ordinal}
    (F : RankedMatchingFamily.{u, v, w, w', r} L M N height)
    {α : Ordinal} (hα : α ≤ height) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (seed : Nonempty (F.Receipt α n a b)) : BFEquiv (L := L) α n a b :=
  bfEquiv_of_nonempty_gradedReceipt F.Receipt F.atomic F.lower F.forth F.back hα seed

/-- The data-valued seed form of the comparison theorem. -/
theorem bfEquiv {height : Ordinal}
    (F : RankedMatchingFamily.{u, v, w, w', r} L M N height)
    {α : Ordinal} (hα : α ≤ height) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (seed : F.Receipt α n a b) : BFEquiv (L := L) α n a b :=
  F.bfEquiv_of_nonempty hα ⟨seed⟩

end RankedMatchingFamily

/-- Exact template labels for finite embedded covers. The labeling relation may have many
values or none; totality is not silently assumed. -/
structure FiniteCoverPresentation (M : Type w) where
  Template : Ordinal.{0} → ℕ → Type s
  allowed : ∀ {α k}, Template α k → Prop
  realizes : ∀ {α k}, (Fin k ↪ M) → Template α k → Prop
  realizes_allowed : ∀ {α k} {a : Fin k ↪ M} {p : Template α k},
    realizes a p → allowed p

namespace FiniteCoverPresentation

/-- An actual matched finite cover with a common, possibly noninjective tuple selector. -/
structure Receipt (C : FiniteCoverPresentation.{w, s} M)
    (D : FiniteCoverPresentation.{w', t} N)
    (compatible : ∀ α k, C.Template α k → D.Template α k → Prop)
    (α : Ordinal) (n : ℕ) (a : Fin n → M) (b : Fin n → N) where
  size : ℕ
  source : Fin size ↪ M
  target : Fin size ↪ N
  selector : Fin n → Fin size
  sourceValue : C.Template α size
  targetValue : D.Template α size
  source_exact : C.realizes source sourceValue
  target_exact : D.realizes target targetValue
  projected : compatible α size sourceValue targetValue
  source_root : source ∘ selector = a
  target_root : target ∘ selector = b

/-- A received cover extends a matched root cover by literal embedding equations.
The new point can already belong to the old cover. -/
structure Extension (C : FiniteCoverPresentation.{w, s} M)
    (D : FiniteCoverPresentation.{w', t} N)
    (compatible : ∀ α k, C.Template α k → D.Template α k → Prop)
    (α : Ordinal) {k : ℕ} (source : Fin k ↪ M) (target : Fin k ↪ N) where
  size : ℕ
  sourceCover : Fin size ↪ M
  targetCover : Fin size ↪ N
  root : Fin k ↪ Fin size
  point : Fin size
  sourceValue : C.Template α size
  targetValue : D.Template α size
  source_exact : C.realizes sourceCover sourceValue
  target_exact : D.realizes targetCover targetValue
  projected : compatible α size sourceValue targetValue
  source_retained : root.trans sourceCover = source
  target_retained : root.trans targetCover = target

namespace Extension

/-- Compose the old selector with the retained root and append the distinguished point. -/
def receipt {C : FiniteCoverPresentation.{w, s} M} {D : FiniteCoverPresentation.{w', t} N}
    {compatible : ∀ α k, C.Template α k → D.Template α k → Prop}
    {α β : Ordinal} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (seed : Receipt C D compatible β n a b)
    (e : Extension C D compatible α seed.source seed.target) :
    Receipt C D compatible α (n + 1)
      (Fin.snoc a (e.sourceCover e.point)) (Fin.snoc b (e.targetCover e.point)) where
  size := e.size
  source := e.sourceCover
  target := e.targetCover
  selector := Fin.snoc (e.root ∘ seed.selector) e.point
  sourceValue := e.sourceValue
  targetValue := e.targetValue
  source_exact := e.source_exact
  target_exact := e.target_exact
  projected := e.projected
  source_root := by
    rw [Fin.comp_snoc]
    congr 1
    exact (congrArg (fun f : Fin seed.size ↪ M => f ∘ seed.selector)
      e.source_retained).trans seed.source_root
  target_root := by
    rw [Fin.comp_snoc]
    congr 1
    exact (congrArg (fun f : Fin seed.size ↪ N => f ∘ seed.selector)
      e.target_retained).trans seed.target_root

end Extension
end FiniteCoverPresentation

/-- Projected finite-template extension laws. Exact source and target values need not even
have the same type. Lowering preserves the cover while allowing different exact labels;
forth and back receive larger covers with literally retained roots and lose one level. -/
structure ProjectedExtensionSystem (L : Language.{u, v}) (M : Type w) (N : Type w')
    [L.IsRelational] [L.Structure M] [L.Structure N] (height : Ordinal) where
  source : FiniteCoverPresentation.{w, s} M
  target : FiniteCoverPresentation.{w', t} N
  compatible : ∀ α k, source.Template α k → target.Template α k → Prop
  atomic : ∀ {k} {a : Fin k ↪ M} {b : Fin k ↪ N}
    {p : source.Template 0 k} {q : target.Template 0 k},
    source.realizes a p → target.realizes b q → compatible 0 k p q →
      ∀ idx : L.AtomicIdx k, idx.holds (a : Fin k → M) ↔ idx.holds (b : Fin k → N)
  lower : ∀ {α β k} {a : Fin k ↪ M} {b : Fin k ↪ N}
    {p : source.Template α k} {q : target.Template α k}, β ≤ α → α ≤ height →
    source.realizes a p → target.realizes b q → compatible α k p q →
      ∃ (p' : source.Template β k) (q' : target.Template β k),
        source.realizes a p' ∧ target.realizes b q' ∧ compatible β k p' q'
  forth : ∀ {α k} {a : Fin k ↪ M} {b : Fin k ↪ N}
    {p : source.Template (α + 1) k} {q : target.Template (α + 1) k}, α + 1 ≤ height →
    source.realizes a p → target.realizes b q → compatible (α + 1) k p q →
      ∀ x : M, ∃ e : FiniteCoverPresentation.Extension source target compatible α a b,
        e.sourceCover e.point = x
  back : ∀ {α k} {a : Fin k ↪ M} {b : Fin k ↪ N}
    {p : source.Template (α + 1) k} {q : target.Template (α + 1) k}, α + 1 ≤ height →
    source.realizes a p → target.realizes b q → compatible (α + 1) k p q →
      ∀ y : N, ∃ e : FiniteCoverPresentation.Extension source target compatible α a b,
        e.targetCover e.point = y

namespace ProjectedExtensionSystem

variable {height : Ordinal}

/-- The cover receipt type, exposed for constructing an explicit initial match. -/
abbrev Receipt (S : ProjectedExtensionSystem.{u, v, w, w', s, t} L M N height)
    (α : Ordinal) (n : ℕ) (a : Fin n → M) (b : Fin n → N) :=
  FiniteCoverPresentation.Receipt S.source S.target S.compatible α n a b

/-- Convert finite covers and selectors to a tuple receipt family, without ordinal recursion. -/
def toRankedMatchingFamily
    (S : ProjectedExtensionSystem.{u, v, w, w', s, t} L M N height) :
    RankedMatchingFamily L M N height where
  Receipt := S.Receipt
  atomic := by
    intro n a b seed idx
    have h := S.atomic seed.source_exact seed.target_exact seed.projected
      (idx.pushforward seed.selector)
    rw [← AtomicIdx.holds_comp_eq_holds_pushforward,
      ← AtomicIdx.holds_comp_eq_holds_pushforward, seed.source_root, seed.target_root] at h
    exact h
  lower := by
    intro α β n a b hβα hα seed
    obtain ⟨p, q, hp, hq, hpq⟩ := S.lower hβα hα
      seed.source_exact seed.target_exact seed.projected
    exact ⟨{
      size := seed.size
      source := seed.source
      target := seed.target
      selector := seed.selector
      sourceValue := p
      targetValue := q
      source_exact := hp
      target_exact := hq
      projected := hpq
      source_root := seed.source_root
      target_root := seed.target_root }⟩
  forth := by
    intro α n a b hα seed x
    obtain ⟨e, hx⟩ := S.forth hα seed.source_exact seed.target_exact seed.projected x
    refine ⟨e.targetCover e.point, ?_⟩
    rw [← hx]
    exact ⟨e.receipt seed⟩
  back := by
    intro α n a b hα seed y
    obtain ⟨e, hy⟩ := S.back hα seed.source_exact seed.target_exact seed.projected y
    refine ⟨e.sourceCover e.point, ?_⟩
    rw [← hy]
    exact ⟨e.receipt seed⟩

/-- An explicit projected initial match gives BF equivalence at its budget. -/
theorem bfEquiv (S : ProjectedExtensionSystem.{u, v, w, w', s, t} L M N height)
    {α : Ordinal} (hα : α ≤ height) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (seed : S.Receipt α n a b) : BFEquiv (L := L) α n a b :=
  S.toRankedMatchingFamily.bfEquiv hα seed

end ProjectedExtensionSystem
end VaughtConjecture.ModelTheory
