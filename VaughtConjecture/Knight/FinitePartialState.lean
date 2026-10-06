/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteTupleGeometry
public import VaughtConjecture.TypeTower.RealizationExtension

/-! # Finite partial diagrams and literal master installation

Fresh one-point and arbitrarily padded extensions preserve consistency and all old
master labels, including invisible faces. No request census or infinite run is imported. -/

@[expose] public section

namespace VaughtConjecture.Knight
open TypeTower Value ExtOrd
universe w
namespace FixedHeight
open KnightRealization
variable {M : Type w} {β : LimitStage}

/-! ### 4. The minimal partial state -/

/-- `A'` **extends** `A`: every evaluation of `A` is an evaluation of `A'` (labels never
change, only `none` becomes `some`).  The order of the ω-step (shape shared with
`origin/e7/partial-density`). -/
def Extends (A A' : KnightRealization β M) : Prop :=
  Realization.Extends A A'

theorem Extends.refl (A : KnightRealization β M) : Extends A A :=
  fun _ _ _ h => h

theorem Extends.trans {A A' A'' : KnightRealization β M}
    (h : Extends A A') (h' : Extends A' A'') : Extends A A'' :=
  fun _ t Q hQ => h' t Q (h t Q hQ)

/-- **The mute seed**: the empty realization, evaluating nothing. -/
def emptySeed (β : LimitStage) (M : Type w) : KnightRealization β M where
  eval _ := none

@[simp] theorem emptySeed_eval {n : ℕ} (t : Fin n ↪ M) :
    (emptySeed β M).eval t = none := rfl

/-- The points a partial state has touched. -/
def UsedPoints (A : KnightRealization β M) : Set M :=
  {x | ∃ (n : ℕ) (s : Fin n ↪ M), ((A.eval s).isSome ∧ x ∈ Set.range s)}

/-- `y` is **fresh** for `A`: on no evaluated tuple. -/
def FreshFor (A : KnightRealization β M) (y : M) : Prop :=
  y ∉ UsedPoints A

/-- **The minimal partial state** of the fixed-height lane: exactly consistent where
defined, finitely many used points.  Nothing else — no receipt, failure certificate, Karp
trace, or source link (the #47 independence contract), and no source/lift stratum (contrast
`origin/e7/partial-density`'s `PartialCandidate`). -/
structure IsPartialState (A : KnightRealization β M) : Prop where
  /-- Exactly consistent where defined. -/
  consistent : A.IsExactParentConsistent
  /-- Finitely many used points (so a fresh occurrence always exists, `exists_fresh`). -/
  finite : (UsedPoints A).Finite

/-- **A mute initial partial seed is legitimate**: the empty realization is a partial state
(vacuously consistent, no used points).  The no-go (`IsModel.exists_realized_nonmute`)
constrains the completed limit, not the start. -/
theorem isPartialState_emptySeed : IsPartialState (emptySeed β M) where
  consistent := by
    intro m n t q f hq
    simp at hq
  finite := by
    have : UsedPoints (emptySeed β M) = ∅ := by
      ext x
      simp [UsedPoints]
    rw [this]
    exact Set.finite_empty

/-- The seed is mute-only in the strongest sense: it realizes nothing at all. -/
theorem emptySeed_eval_ne {n : ℕ} (t : Fin n ↪ M) (Q : S β.1 n) :
    (emptySeed β M).eval t ≠ some Q := by simp

/-- **A fresh occurrence always exists** over a finite partial state on an infinite carrier:
the ω-step chooses the occurrence jointly with the request. -/
theorem exists_fresh [Infinite M] {A : KnightRealization β M}
    (hfin : (UsedPoints A).Finite) {n : ℕ} (t : Fin n ↪ M) :
    ∃ y : M, y ∉ Set.range t ∧ FreshFor A y := by
  obtain ⟨y, hy⟩ := (hfin.union (Set.finite_range t)).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hy
  exact ⟨y, hy.2, hy.1⟩

/-! ### The one-event extension

Adapted from `origin/e7/partial-density` (the factor-through-`w` closure), WITHOUT the
source/lift stratum: here overlaps between the new faces and the old commitments are
excluded by freshness of the occurrence, not arbitrated by a source. -/

open Classical in
/-- **The one-event extension**: adjoin the faces of one labelled tuple to a partial
realization.  `A`-values win; new tuples factoring through `w` receive the pull of `W`. -/
noncomputable def extendByEvent (A : KnightRealization β M) {N : ℕ} (w : Fin N ↪ M)
    (W : S β.1 N) : KnightRealization β M where
  eval {n} t :=
    match A.eval t with
    | some Q => some Q
    | none =>
      if h : ∃ f : Fin n ↪ Fin N, f.trans w = t then typeMap h.choose W else none

section ExtendByEvent

variable {A : KnightRealization β M} {N : ℕ} {w : Fin N ↪ M} {W : S β.1 N}

theorem extendByEvent_eval_of_eval {n : ℕ} {t : Fin n ↪ M} {Q : S β.1 n}
    (h : A.eval t = some Q) : (extendByEvent A w W).eval t = some Q := by
  simp [extendByEvent, h]

theorem extendByEvent_eval_factor {n : ℕ} {t : Fin n ↪ M} (hA : A.eval t = none)
    {f : Fin n ↪ Fin N} (hf : f.trans w = t) :
    (extendByEvent A w W).eval t = typeMap f W := by
  have hex : ∃ g : Fin n ↪ Fin N, g.trans w = t := ⟨f, hf⟩
  obtain rfl : hex.choose = f := emb_factor_unique hex.choose_spec hf
  simp [extendByEvent, hA, hex]

theorem extendByEvent_eval_of_not {n : ℕ} {t : Fin n ↪ M} (hA : A.eval t = none)
    (hex : ¬ ∃ f : Fin n ↪ Fin N, f.trans w = t) :
    (extendByEvent A w W).eval t = none := by
  simp [extendByEvent, hA, hex]

/-- Inversion at an `A`-undefined tuple: a value can only come from a factor. -/
theorem extendByEvent_eval_none_inv {n : ℕ} {t : Fin n ↪ M} {Q : S β.1 n}
    (hA : A.eval t = none) (hQ : (extendByEvent A w W).eval t = some Q) :
    ∃ f : Fin n ↪ Fin N, f.trans w = t ∧ typeMap f W = some Q := by
  by_cases hex : ∃ f : Fin n ↪ Fin N, f.trans w = t
  · obtain ⟨f, hf⟩ := hex
    exact ⟨f, hf, by rw [← extendByEvent_eval_factor hA hf (W := W)]; exact hQ⟩
  · rw [extendByEvent_eval_of_not hA hex] at hQ
    exact absurd hQ (by simp)

/-- The one-event extension extends. -/
theorem extends_extendByEvent : Extends A (extendByEvent A w W) :=
  fun _ _ _ h => extendByEvent_eval_of_eval h

/-- At an `A`-defined tuple the extension's value is `A`'s value. -/
theorem extendByEvent_eval_some_of_some {n : ℕ} {t : Fin n ↪ M} {Q' Q : S β.1 n}
    (hAt : A.eval t = some Q') (hQ : (extendByEvent A w W).eval t = some Q) :
    A.eval t = some Q := by
  rw [Option.some.inj ((extendByEvent_eval_of_eval hAt).symm.trans hQ)] at hAt
  exact hAt

/-- The used points of the extension are the old ones and the event's. -/
theorem usedPoints_extendByEvent_subset :
    UsedPoints (extendByEvent A w W) ⊆ UsedPoints A ∪ Set.range w := by
  rintro x ⟨n, s, hs, hx⟩
  cases hAs : A.eval s with
  | some Q => exact Or.inl ⟨n, s, by rw [hAs]; rfl, hx⟩
  | none =>
    obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨g, hg, -⟩ := extendByEvent_eval_none_inv hAs hQ
    obtain ⟨i, hi⟩ := hx
    refine Or.inr ⟨g i, ?_⟩
    rw [← hg] at hi
    exact hi

end ExtendByEvent

/-! ### The freshness preservation theorem

One coface event at a fresh occurrence preserves the partial state.  In
`origin/e7/partial-density` the analogous preservation is arbitrated by the source; here
there is no source, and every overlap between the new faces and the old commitments is
excluded by freshness: a face of the new tuple avoiding the fresh point is a face of the old
base `t`, where `A`'s own exact consistency at `t` supplies the identical value. -/

section Preservation

variable {A : KnightRealization β M} {n : ℕ} {t : Fin n ↪ M} {y : M} {hy : y ∉ Set.range t}

/-- A factor of the fresh concatenation avoiding the fresh point avoids the last index. -/
theorem last_notMem_of_fresh_face {k : ℕ} {g : Fin k ↪ Fin (n + 1)}
    (h : y ∉ Set.range (g.trans (snoc t y hy))) :
    Fin.last n ∉ Set.range g := fun ⟨i, hi⟩ => h ⟨i, by
      change (snoc t y hy) (g i) = y
      rw [hi]
      exact snoc_apply_last t y hy⟩

/-- A fresh point is on no evaluated tuple. -/
theorem notMem_range_of_freshFor (hfresh : FreshFor A y) {k : ℕ} {u : Fin k ↪ M}
    {Q : S β.1 k} (hu : A.eval u = some Q) : y ∉ Set.range u :=
  fun hr => hfresh ⟨k, u, by rw [hu]; rfl, hr⟩

/-- The fresh concatenation is unevaluated. -/
theorem eval_snoc_none_of_fresh (hfresh : FreshFor A y) : A.eval (snoc t y hy) = none := by
  cases h : A.eval (snoc t y hy) with
  | none => rfl
  | some Q =>
    exact absurd ⟨Fin.last n, snoc_apply_last t y hy⟩ (notMem_range_of_freshFor hfresh h)

variable {p : S β.1 n} {q : S β.1 (n + 1)}

/-- The event itself is evaluated by the extension. -/
theorem extendByEvent_eval_self {N : ℕ} {w : Fin N ↪ M} {W : S β.1 N}
    (hA : A.eval w = none) : (extendByEvent A w W).eval w = some W := by
  have hrefl : (Function.Embedding.refl (Fin N)).trans w = w := by
    ext i
    rfl
  rw [extendByEvent_eval_factor hA hrefl]
  exact typeMap_refl W

/-- **The freshness preservation theorem**: a coface event over an evaluated base at a fresh
occurrence preserves exact consistency. -/
theorem extendByEvent_consistent (hA : A.IsExactParentConsistent)
    (ht : A.eval t = some p) (hfresh : FreshFor A y) (hq : IsCoface p q) :
    (extendByEvent A (snoc t y hy) q).IsExactParentConsistent := by
  intro k m u Q f hQ
  change (extendByEvent A (snoc t y hy) q).eval (f.trans u) = typeMap f Q
  cases hAu : A.eval u with
  | some Q' =>
    have hAuQ : A.eval u = some Q := extendByEvent_eval_some_of_some hAu hQ
    have hface : A.eval (f.trans u) = typeMap f Q := hA u Q f hAuQ
    cases hTM : typeMap f Q with
    | some V =>
      rw [hTM] at hface
      exact extendByEvent_eval_of_eval hface
    | none =>
      rw [hTM] at hface
      by_cases hex : ∃ g : Fin k ↪ Fin (n + 1), g.trans (snoc t y hy) = f.trans u
      · obtain ⟨g, hg⟩ := hex
        have hyu : y ∉ Set.range (f.trans u) := fun ⟨i, hi⟩ =>
          notMem_range_of_freshFor hfresh hAuQ ⟨f i, hi⟩
        obtain ⟨g₀, rfl⟩ := exists_factor_castSucc g (last_notMem_of_fresh_face (hg ▸ hyu))
        have hgt : (g₀.trans Fin.castSuccEmb).trans (snoc t y hy) = g₀.trans t :=
          trans_factor (castSuccEmb_trans_snoc t y hy) g₀
        have hnone : typeMap g₀ p = none := by
          have hbase : A.eval (g₀.trans t) = typeMap g₀ p := hA t p g₀ ht
          rw [hgt.symm.trans hg, hface] at hbase
          exact hbase.symm
        have hval : typeMap (g₀.trans Fin.castSuccEmb) q = none := by
          rw [← typeMap_trans g₀ Fin.castSuccEmb q p hq]
          exact hnone
        rw [extendByEvent_eval_factor hface hg, hval]
      · exact extendByEvent_eval_of_not hface hex
  | none =>
    obtain ⟨g, hg, hgQ⟩ := extendByEvent_eval_none_inv hAu hQ
    have hcomp : (f.trans g).trans (snoc t y hy) = f.trans u := trans_factor hg f
    have hfQ : typeMap f Q = typeMap (f.trans g) q := typeMap_trans f g q Q hgQ
    cases hAft : A.eval (f.trans u) with
    | some V =>
      have hyu : y ∉ Set.range (f.trans u) := notMem_range_of_freshFor hfresh hAft
      obtain ⟨h₀, hfac⟩ := exists_factor_castSucc (f.trans g)
        (last_notMem_of_fresh_face (hcomp ▸ hyu))
      have heq : h₀.trans t = f.trans u := by
        rw [← hcomp, hfac]
        exact (trans_factor (castSuccEmb_trans_snoc t y hy) h₀).symm
      have hbase : A.eval (h₀.trans t) = typeMap h₀ p := hA t p h₀ ht
      rw [heq, hAft] at hbase
      have hval : typeMap (f.trans g) q = some V := by
        rw [hfac, ← typeMap_trans h₀ Fin.castSuccEmb q p hq]
        exact hbase.symm
      exact (extendByEvent_eval_of_eval hAft).trans (hfQ.trans hval).symm
    | none =>
      exact (extendByEvent_eval_factor hAft hcomp).trans hfQ.symm

/-- **The one-event step**: a coface event over an evaluated base at a fresh occurrence
takes a partial state to a partial state, extends it, and realizes the coface. -/
theorem IsPartialState.stepCoface (hA : IsPartialState A) (ht : A.eval t = some p)
    (hfresh : FreshFor A y) (hq : IsCoface p q) :
    IsPartialState (extendByEvent A (snoc t y hy) q) ∧
      Extends A (extendByEvent A (snoc t y hy) q) ∧
      (extendByEvent A (snoc t y hy) q).eval (snoc t y hy) = some q :=
  ⟨⟨extendByEvent_consistent hA.consistent ht hfresh hq,
      ((hA.finite.union (Set.finite_range _)).subset usedPoints_extendByEvent_subset)⟩,
    extends_extendByEvent,
    extendByEvent_eval_self (eval_snoc_none_of_fresh hfresh)⟩

end Preservation
/-- The master's faces are evaluated (exact consistency): a request base over a face of the
master is automatically applicable. -/
theorem face_eval_of_master {A : KnightRealization β M} (hA : A.IsExactParentConsistent)
    {N : ℕ} {w : Fin N ↪ M} {P : S β.1 N} (hw : A.eval w = some P) {n : ℕ}
    {g : Fin n ↪ Fin N} {p : S β.1 n} (hface : typeMap g P = some p) :
    A.eval (g.trans w) = some p := by
  rw [hA w P g hw]
  exact hface

/-- **The master-relative completion gate, compiled**: given a pinned master coface — the
supply's output for a requested `q` over the face `(g, p)` of the evaluated master
`(w, P)` — ONE master event at a fresh occurrence extends the master literally AND installs
the requested coface over the face, in the same step: the face event is not a separate
commitment but a FACE of the master event, so no cross-event consistency question arises.
Everything here is compiled; the supply (`PinnedCofaceSupply`) is a theorem from the coatom
receiver (`Knight/CoatomHenkinBridge.lean`). -/
theorem stepMaster [Infinite M] {A : KnightRealization β M} (hA : IsPartialState A)
    {N : ℕ} {w : Fin N ↪ M} {P : S β.1 N} (hw : A.eval w = some P)
    {n : ℕ} {g : Fin n ↪ Fin N} {p : S β.1 n} (_hface : typeMap g P = some p)
    {Q : S β.1 (N + 1)} (hQ : IsCoface P Q) {q : S β.1 (n + 1)}
    (hq : typeMap (extendFace g) Q = some q) :
    ∃ (A' : KnightRealization β M) (y : M) (hyw : y ∉ Set.range w)
      (hyt : y ∉ Set.range (g.trans w)),
      Extends A A' ∧ IsPartialState A' ∧
        A'.eval (snoc w y hyw) = some Q ∧
        A'.eval (snoc (g.trans w) y hyt) = some q := by
  obtain ⟨y, hyw, hfresh⟩ := exists_fresh hA.finite w
  have hyt : y ∉ Set.range (g.trans w) := fun ⟨i, hi⟩ => hyw ⟨g i, hi⟩
  obtain ⟨hA', hext, hself⟩ := hA.stepCoface (hy := hyw) hw hfresh hQ
  refine ⟨_, y, hyw, hyt, hext, hA', hself, ?_⟩
  rw [← extendFace_trans_snoc g hyw hyt]
  rw [hA'.consistent _ Q (extendFace g) hself]
  exact hq

/-- **Master discipline**: every evaluated tuple of the state factors through the single
master tuple (the shape a master-relative run maintains — the seed satisfies it vacuously,
and a `stepMaster` chain preserves it for the new master). -/
def MasteredBy (A : KnightRealization β M) {N : ℕ} (w : Fin N ↪ M) : Prop :=
  ∀ ⦃n : ℕ⦄ (s : Fin n ↪ M), (A.eval s).isSome → ∃ f : Fin n ↪ Fin N, f.trans w = s

/-- Under master discipline every used point is on the master. -/
theorem usedPoints_subset_of_masteredBy {A : KnightRealization β M} {N : ℕ}
    {w : Fin N ↪ M} (hM : MasteredBy A w) : UsedPoints A ⊆ Set.range w := by
  rintro x ⟨n, s, hs, i, hi⟩
  obtain ⟨f, rfl⟩ := hM s hs
  exact ⟨f i, hi⟩

/-- **Straddling covers disappear under master discipline**: any injective tuple of points
on the master is a face of the master, hence covered by the master's own evaluation — no
cross-event amalgamation is involved.  (Initial-segment form follows generically from
permutation totality, `knightTower_permTotal` + `IsCovering.toInitialSegment`.) -/
theorem covering_of_masteredBy {A : KnightRealization β M} {N : ℕ} {w : Fin N ↪ M}
    (hw : (A.eval w).isSome) {n : ℕ} (t : Fin n ↪ M) (ht : ∀ i, t i ∈ Set.range w) :
    ∃ (m : ℕ) (s : Fin m ↪ M) (f : Fin n ↪ Fin m), f.trans s = t ∧ (A.eval s).isSome := by
  have hf : ∀ i, w ((ht i).choose) = t i := fun i => (ht i).choose_spec
  refine ⟨N, w, ⟨fun i => (ht i).choose, fun i j hij => ?_⟩, ?_, hw⟩
  · apply t.injective
    rw [← hf i, ← hf j]
    exact congrArg w hij
  · ext i
    exact hf i

section Append
variable {A : KnightRealization β M}

/-- A fresh block of any finite size exists over a finite state (all points fresh, off the
master, and pairwise distinct). -/
theorem exists_fresh_block [Infinite M] (hfin : (UsedPoints A).Finite) {N : ℕ}
    (w : Fin N ↪ M) (m : ℕ) :
    ∃ ys : Fin m ↪ M, (∀ j, FreshFor A (ys j)) ∧ ∀ j, ys j ∉ Set.range w := by
  have hinf : (UsedPoints A ∪ Set.range ⇑w).Finite := hfin.union (Set.finite_range w)
  have hcinf : Infinite ↥(UsedPoints A ∪ Set.range ⇑w)ᶜ := hinf.infinite_compl.to_subtype
  set e : ℕ ↪ ↥(UsedPoints A ∪ Set.range ⇑w)ᶜ :=
    Infinite.natEmbedding ↥(UsedPoints A ∪ Set.range ⇑w)ᶜ with he
  refine ⟨(Fin.valEmbedding.trans e).trans (Function.Embedding.subtype _),
    fun j => ?_, fun j => ?_⟩
  · exact fun hu => (e j.val).2 (Or.inl hu)
  · exact fun hr => (e j.val).2 (Or.inr hr)

/-- **The padded freshness preservation theorem**: one master event appending a fresh block,
labelled by any type whose initial face is the master's label, preserves exact
consistency.  (The one-point `extendByEvent_consistent` is the case `m = 1` up to
reindexing; both are kept.) -/
theorem extendByEvent_consistent_append (hA : A.IsExactParentConsistent)
    {N : ℕ} {w : Fin N ↪ M} {P : S β.1 N} (hw : A.eval w = some P)
    {m : ℕ} {ys : Fin m ↪ M} (hfresh : ∀ j, FreshFor A (ys j))
    (hdisj : ∀ j, ys j ∉ Set.range w)
    {W : S β.1 (N + m)} (hW : typeMap (Fin.castAddEmb m) W = some P) :
    (extendByEvent A (appendEmb w ys hdisj) W).IsExactParentConsistent := by
  set w' : Fin (N + m) ↪ M := appendEmb w ys hdisj with hw'
  -- an `A`-evaluated tuple avoids the fresh block, so its factors avoid the new indices
  have hval : ∀ {j : ℕ} (g : Fin j ↪ Fin (N + m)) {u : Fin j ↪ M}, g.trans w' = u →
      (∀ jj, ys jj ∉ Set.range u) → ∀ i, (g i).val < N := by
    intro j g u hg hu i
    induction hgi : g i using Fin.addCases with
    | left i' => exact hgi ▸ (Fin.castAdd_lt _ i' : (Fin.castAdd m i').val < N)
    | right j' =>
      refine absurd ⟨i, ?_⟩ (hu j')
      rw [← hg]
      change w' (g i) = ys j'
      rw [hgi]
      exact appendEmb_natAdd w ys hdisj j'
  intro k j u Q f hQ
  change (extendByEvent A w' W).eval (f.trans u) = typeMap f Q
  cases hAu : A.eval u with
  | some Q' =>
    have hAuQ : A.eval u = some Q := extendByEvent_eval_some_of_some hAu hQ
    have hface : A.eval (f.trans u) = typeMap f Q := hA u Q f hAuQ
    cases hTM : typeMap f Q with
    | some V =>
      rw [hTM] at hface
      exact extendByEvent_eval_of_eval hface
    | none =>
      rw [hTM] at hface
      by_cases hex : ∃ g : Fin k ↪ Fin (N + m), g.trans w' = f.trans u
      · obtain ⟨g, hg⟩ := hex
        have hyu : ∀ jj, ys jj ∉ Set.range (f.trans u) := fun jj ⟨i, hi⟩ =>
          notMem_range_of_freshFor (hfresh jj) hAuQ ⟨f i, hi⟩
        obtain ⟨g₀, rfl⟩ := exists_factor_castAdd g (hval g hg hyu)
        have hgt : (g₀.trans (Fin.castAddEmb m)).trans w' = g₀.trans w :=
          trans_factor (castAddEmb_trans_appendEmb w ys hdisj) g₀
        have hnone : typeMap g₀ P = none := by
          have hbase : A.eval (g₀.trans w) = typeMap g₀ P := hA w P g₀ hw
          rw [hgt.symm.trans hg, hface] at hbase
          exact hbase.symm
        have hvalW : typeMap (g₀.trans (Fin.castAddEmb m)) W = none := by
          rw [← typeMap_trans g₀ (Fin.castAddEmb m) W P hW]
          exact hnone
        rw [extendByEvent_eval_factor hface hg, hvalW]
      · exact extendByEvent_eval_of_not hface hex
  | none =>
    obtain ⟨g, hg, hgQ⟩ := extendByEvent_eval_none_inv hAu hQ
    have hcomp : (f.trans g).trans w' = f.trans u := trans_factor hg f
    have hfQ : typeMap f Q = typeMap (f.trans g) W := typeMap_trans f g W Q hgQ
    cases hAft : A.eval (f.trans u) with
    | some V =>
      have hyu : ∀ jj, ys jj ∉ Set.range (f.trans u) := fun jj hr =>
        notMem_range_of_freshFor (hfresh jj) hAft hr
      obtain ⟨h₀, hfac⟩ := exists_factor_castAdd (f.trans g) (hval (f.trans g) hcomp hyu)
      have heq : h₀.trans w = f.trans u := by
        rw [← hcomp, hfac]
        exact (trans_factor (castAddEmb_trans_appendEmb w ys hdisj) h₀).symm
      have hbase : A.eval (h₀.trans w) = typeMap h₀ P := hA w P h₀ hw
      rw [heq, hAft] at hbase
      have hvalW : typeMap (f.trans g) W = some V := by
        rw [hfac, ← typeMap_trans h₀ (Fin.castAddEmb m) W P hW]
        exact hbase.symm
      exact (extendByEvent_eval_of_eval hAft).trans (hfQ.trans hvalW).symm
    | none =>
      exact (extendByEvent_eval_factor hAft hcomp).trans hfQ.symm

/-- The padded event tuple is unevaluated when the block is nonempty. -/
theorem eval_appendEmb_none {N m : ℕ} {w : Fin N ↪ M} {ys : Fin (m + 1) ↪ M}
    (hfresh : ∀ j, FreshFor A (ys j)) (hdisj : ∀ j, ys j ∉ Set.range w) :
    A.eval (appendEmb w ys hdisj) = none := by
  cases h : A.eval (appendEmb w ys hdisj) with
  | none => rfl
  | some Q =>
    exact absurd ⟨Fin.natAdd N 0, appendEmb_natAdd w ys hdisj 0⟩
      (notMem_range_of_freshFor (hfresh 0) h)

end Append
/-- A fresh block with a PRESCRIBED designated point: the padding is fresh, the designated
last coordinate is a given fresh point (carrier-point ABSORPTION is thereby the same
theorem as request servicing: covering a not-yet-used point designates it). -/
theorem exists_fresh_block_with [Infinite M] {A : KnightRealization β M}
    (hfin : (UsedPoints A).Finite) {N : ℕ} (w : Fin N ↪ M) (k : ℕ) {x : M}
    (hx : FreshFor A x) (hxw : x ∉ Set.range w) :
    ∃ ys : Fin (k + 1) ↪ M, (∀ j, FreshFor A (ys j)) ∧ (∀ j, ys j ∉ Set.range w) ∧
      ys (Fin.last k) = x := by
  have hinf : (UsedPoints A ∪ (Set.range ⇑w ∪ {x})).Finite :=
    hfin.union ((Set.finite_range w).union (Set.finite_singleton x))
  have : Infinite ↥(UsedPoints A ∪ (Set.range ⇑w ∪ {x}))ᶜ := hinf.infinite_compl.to_subtype
  set e : ℕ ↪ ↥(UsedPoints A ∪ (Set.range ⇑w ∪ {x}))ᶜ :=
    Infinite.natEmbedding ↥(UsedPoints A ∪ (Set.range ⇑w ∪ {x}))ᶜ with he
  set b : Fin k → M := fun j => (e j.val).val with hb
  have hbinj : Function.Injective b := fun j j' hjj =>
    Fin.val_injective (e.injective (Subtype.ext hjj))
  have hbx : x ∉ Set.range b := fun ⟨j, hj⟩ => (e j.val).2 (Or.inr (Or.inr hj))
  refine ⟨⟨Fin.snoc b x, Fin.snoc_injective_of_injective hbinj hbx⟩, fun j => ?_, fun j => ?_,
    by simp⟩
  · induction j using Fin.lastCases with
    | last =>
      change FreshFor A (Fin.snoc (α := fun _ => M) b x (Fin.last k))
      rw [Fin.snoc_last]
      exact hx
    | cast j =>
      change FreshFor A (Fin.snoc (α := fun _ => M) b x (Fin.castSucc j))
      rw [Fin.snoc_castSucc]
      exact fun hu => (e j.val).2 (Or.inl hu)
  · induction j using Fin.lastCases with
    | last =>
      change Fin.snoc (α := fun _ => M) b x (Fin.last k) ∉ Set.range ⇑w
      rw [Fin.snoc_last]
      exact hxw
    | cast j =>
      change Fin.snoc (α := fun _ => M) b x (Fin.castSucc j) ∉ Set.range ⇑w
      rw [Fin.snoc_castSucc]
      exact fun hr => (e j.val).2 (Or.inr (Or.inl hr))

/-- **The padded master step**: a fresh block labelled by any type whose initial face is
the master's label yields a partial state extending the old one, with the padded event
evaluated. -/
theorem stepMasterPadded [Infinite M] {A : KnightRealization β M} (hA : IsPartialState A)
    {N : ℕ} {w : Fin N ↪ M} {P : S β.1 N} (hw : A.eval w = some P)
    {k : ℕ} {ys : Fin (k + 1) ↪ M} (hfresh : ∀ j, FreshFor A (ys j))
    (hdisj : ∀ j, ys j ∉ Set.range w)
    {W : S β.1 (N + (k + 1))} (hW : typeMap (Fin.castAddEmb (k + 1)) W = some P) :
    Extends A (extendByEvent A (appendEmb w ys hdisj) W) ∧
      IsPartialState (extendByEvent A (appendEmb w ys hdisj) W) ∧
      (extendByEvent A (appendEmb w ys hdisj) W).eval (appendEmb w ys hdisj) = some W :=
  ⟨extends_extendByEvent,
    ⟨extendByEvent_consistent_append hA.consistent hw hfresh hdisj hW,
      (hA.finite.union (Set.finite_range _)).subset usedPoints_extendByEvent_subset⟩,
    extendByEvent_eval_self (eval_appendEmb_none hfresh hdisj)⟩

/-- **Master discipline persists** under the padded master event: everything old factors
through the old master, hence through the initial face of the new one; everything new
factors through the new master directly. -/
theorem masteredBy_extendByEvent_append {A : KnightRealization β M} {N m : ℕ}
    {w : Fin N ↪ M} {ys : Fin m ↪ M} {hdisj : ∀ j, ys j ∉ Set.range w}
    {W : S β.1 (N + m)} (hM : MasteredBy A w) :
    MasteredBy (extendByEvent A (appendEmb w ys hdisj) W) (appendEmb w ys hdisj) := by
  intro j s hs
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hs
  cases hAs : A.eval s with
  | some Q' =>
    obtain ⟨f, rfl⟩ := hM s (by rw [hAs]; rfl)
    exact ⟨f.trans (Fin.castAddEmb m),
      trans_factor (castAddEmb_trans_appendEmb w ys hdisj) f⟩
  | none =>
    obtain ⟨g, hg, -⟩ := extendByEvent_eval_none_inv hAs hQ
    exact ⟨g, hg⟩

/-- **Covering is serviced under master discipline**: a tuple on the master is an initial
segment of a labelled tuple — the generic cover from `covering_of_masteredBy`, re-ordered
by permutation totality (the per-tuple content of `IsCovering.toInitialSegment`). -/
theorem initialSegmentCover_of_mastered {A : KnightRealization β M}
    (hcons : A.IsExactParentConsistent) {N : ℕ} {tup : Fin N ↪ M}
    (hw : (A.eval tup).isSome) {n : ℕ} (t : Fin n ↪ M)
    (ht : ∀ i, t i ∈ Set.range tup) :
    ∃ (k : ℕ) (s : Fin (n + k) ↪ M),
      (Fin.castAddEmb k).trans s = t ∧ (A.eval s).isSome := by
  obtain ⟨m, s, f, hfs, hs⟩ := covering_of_masteredBy hw t ht
  have hnm : n ≤ m := by simpa using Fintype.card_le_of_embedding f
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  obtain ⟨σ, hσ⟩ := exists_perm_castAdd_eq f
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (knightTower_permTotal σ q)
  refine ⟨k, σ.toEmbedding.trans s, ?_, ?_⟩
  · ext i
    simp [← hfs, hσ]
  · rw [hcons.isVisibleFaceConsistent s q σ.toEmbedding p hq hp]
    rfl

end FixedHeight
end VaughtConjecture.Knight
