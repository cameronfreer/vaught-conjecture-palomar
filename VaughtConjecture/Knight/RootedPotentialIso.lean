/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ChartKarp

/-! # Root-preserving isomorphisms from potential isomorphisms

For a member pair `(a, b)` of a potential isomorphism `P`, the tails `(c, d)` such that
`(a ⧺ c, b ⧺ d) ∈ P` form a potential isomorphism in the original language. The pinned
library's `PotentialIso.countable_toEquiv_graph` returns an isomorphism whose every graph pair
occurs in one of these tails. For a root coordinate `a i`, its occurrence in a tail is equal
to the corresponding root coordinate in the concatenated tuple; atomic equality forces its
image to be `b i`. No named predicates or expanded structures are needed.

Roots are arbitrary tuples, so repeated coordinates and the empty root require no separate
construction. The root must belong to the given family; this does not assert extension of
an arbitrary finite partial isomorphism.

This module carries no chart-chain vocabulary: the fair-chain adapters stay in
`Knight/RootedKarp.lean`, and the direct selected-chart consumer
(`Knight/SelectedCommonCharts.lean`) imports this module without the chain module. -/

@[expose] public section

namespace VaughtConjecture.Knight

open FirstOrder Language Structure TypeTower

universe u v w w'

/-! ## Rooted tail families in the original language -/

section Generic

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- The potential isomorphism rooted at a member pair `(a, b)`, in the original language:
the tails whose concatenation with the root belongs to the family. No closure of the original
family under restrictions or reindexing is assumed. -/
noncomputable def rootedPotentialIso (P : PotentialIso L M N) {k : ℕ} {a : Fin k → M}
    {b : Fin k → N} (hab : (⟨k, a, b⟩ : Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ P.family) :
    PotentialIso L M N :=
  PotentialIso.ofExtensionFamily
    (fun n c d => (⟨k + n, Fin.append a c, Fin.append b d⟩ :
      Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ P.family)
    (by rw [Fin.append_elim0, Fin.append_elim0]; exact hab)
    (fun h => by
      simpa only [Function.comp_def, Fin.append_right] using
        (P.compatible _ h).relabel (Fin.natAdd k))
    (fun h m => by
      obtain ⟨n', hn'⟩ := P.forth _ h m
      exact ⟨n', by rw [Fin.append_snoc, Fin.append_snoc]; exact hn'⟩)
    (fun h n' => by
      obtain ⟨m, hm⟩ := P.back _ h n'
      exact ⟨m, by rw [Fin.append_snoc, Fin.append_snoc]; exact hm⟩)

/-- **Root-preserving countable back-and-forth.** On countable carriers, a potential
isomorphism yields an isomorphism extending any member pair literally. The graph specification
is applied to the rooted tail family, not directly to the original unrooted family. -/
theorem exists_equiv_of_mem {M N : Type w} [L.Structure M] [L.Structure N]
    [Countable M] [Countable N] (P : PotentialIso L M N) {k : ℕ} {a : Fin k → M}
    {b : Fin k → N} (hab : (⟨k, a, b⟩ : Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ P.family) :
    ∃ e : M ≃[L] N, ∀ i, e (a i) = b i := by
  obtain ⟨e, he⟩ := (rootedPotentialIso P hab).countable_toEquiv_graph
  refine ⟨e, fun i => ?_⟩
  obtain ⟨p, hp, j, hj, hj'⟩ := he (a i)
  have hmem : (⟨k + p.1, Fin.append a p.2.1, Fin.append b p.2.2⟩ :
      Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ P.family := hp
  have heq := P.compatible _ hmem (.eq (Fin.natAdd k j) (Fin.castAdd p.1 i))
  simp only [AtomicIdx.holds, Fin.append_right, Fin.append_left] at heq
  exact hj'.symm.trans (heq.mp hj)

end Generic

/-! ## The Knight-level consumers -/

section Knight

variable {α : LimitStage} {M N : Type w}
variable {R : KnightRealization α M} {R' : KnightRealization α N}

/-- The Karp bridge, root-preserving: on countable carriers a potential isomorphism of the stage
chart structures yields a realization isomorphism extending any member pair. -/
theorem exists_iso_of_potentialIso_mem [Countable M] [Countable N]
    (P : @PotentialIso (stageLang α) (stageLang.isRelational α) M N
      (stageStructureOf R) (stageStructureOf R'))
    {k : ℕ} {a : Fin k → M} {b : Fin k → N}
    (hab : (⟨k, a, b⟩ : Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈
      @PotentialIso.family (stageLang α) _ M N (stageStructureOf R) (stageStructureOf R') P) :
    ∃ e : R.Iso R', ∀ i, e.1 (a i) = b i := by
  let instM : (stageLang α).Structure M := stageStructureOf R
  let instN : (stageLang α).Structure N := stageStructureOf R'
  obtain ⟨e, he⟩ := exists_equiv_of_mem P hab
  exact ⟨⟨e.toEquiv, isIsoOfStageStructureEquiv e⟩, he⟩

/-- On countable carriers, a common-chart family with empty pair and one-point forth/back yields
a realization isomorphism extending any member pair. -/
theorem exists_iso_of_commonCharts_mem [Countable M] [Countable N]
    (hR : R.IsExactParentConsistent) (hR' : R'.IsExactParentConsistent)
    (family : Set (Σ n : ℕ, (Fin n → M) × (Fin n → N)))
    (empty_mem : (⟨0, Fin.elim0, Fin.elim0⟩ : Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ family)
    (commonChart : ∀ x ∈ family, HasCommonChart R R' x.2.1 x.2.2)
    (forth : ∀ x ∈ family, ∀ m : M,
      ∃ n' : N, (⟨x.1 + 1, Fin.snoc x.2.1 m, Fin.snoc x.2.2 n'⟩ :
        Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ family)
    (back : ∀ x ∈ family, ∀ n' : N,
      ∃ m : M, (⟨x.1 + 1, Fin.snoc x.2.1 m, Fin.snoc x.2.2 n'⟩ :
        Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ family)
    {k : ℕ} {a : Fin k → M} {b : Fin k → N}
    (hab : (⟨k, a, b⟩ : Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ family) :
    ∃ e : R.Iso R', ∀ i, e.1 (a i) = b i :=
  exists_iso_of_potentialIso_mem
    (potentialIsoOfCommonCharts hR hR' family empty_mem commonChart forth back) hab

end Knight

end VaughtConjecture.Knight
