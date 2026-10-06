/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.StableBandFiniteLawful

/-! # Structural stable lift

Synchronization, lawful stable labels, and the stable realization with its literal
reduct, evaluation, consistency and covering equations. No occurrence supply or
modelhood construction for the stable candidate is imported. The model-facing names
remain definitional compatibility wrappers around the consistency-and-covering core.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd StageType

universe w

namespace KnightRealization

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}
/-- **The synchronizing cover** (the "sufficiently large cover" of Lemma 5.3.10, made exact):
above any realized tuple there is a labelled cover at which every cell with a proper stable
value carries it as its provisional value, and every nonstabilizing `∞`-cell has provisional
value strictly above `α + K`.  This is the occurrence-map adapter of the finite eventual
condition `RootedCover.eventually_syncValues`: the rooted covers of the root form a nonempty
directed preorder, so the condition has a witness, and the rooted cover's own embedding
(`RootedCover.emb`) is the required face.

`K` is only the escape threshold for the nonstabilizing `∞`-cells; no bound on the proper
stable values is needed for synchronization itself (that bound enters only the later jump
argument, `stableLiftRespects_of_consistent`). -/
theorem exists_syncCover' (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) (K : ℕ) :
    ∃ (y : R.LabelledExt) (f : Fin n ↪ Fin y.arity) (_ : f.trans y.tuple = t)
      (hpq : typeMap f y.type = some p),
      ∀ Xi : Cell p.scheme.scheme,
        (R.stableValue t p Xi ≠ ⊤ →
          y.type.someProvisionalValue (mapCell hpq Xi) = R.stableValue t p Xi) ∧
        (p.label Xi = ⊤ → R.stableValue t p Xi = ⊤ →
          ofOrd (α.1 + K) < y.type.someProvisionalValue (mapCell hpq Xi)) := by
  let x : R.LabelledExt := ⟨n, t, p, hpt⟩
  have := RootedCover.isDirectedOrder hcons hcov x
  obtain ⟨y, hy⟩ := (RootedCover.eventually_syncValues hcons hcov x K).exists
  exact ⟨y.1, RootedCover.emb y, RootedCover.emb_trans y, RootedCover.emb_typeMap y, hy⟩

set_option linter.unusedVariables false in
/-- The synchronizing cover, in its original interface.  The stable-value bound `hK` was never
used; it is retained only for compatibility (see `exists_syncCover'`). -/
theorem exists_syncCover (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) (K : ℕ)
    (hK : ∀ Xi : Cell p.scheme.scheme,
      R.stableValue t p Xi ≠ ⊤ → R.stableValue t p Xi ≤ ofOrd (α.1 + K)) :
    ∃ (y : R.LabelledExt) (f : Fin n ↪ Fin y.arity) (_ : f.trans y.tuple = t)
      (hpq : typeMap f y.type = some p),
      ∀ Xi : Cell p.scheme.scheme,
        (R.stableValue t p Xi ≠ ⊤ →
          y.type.someProvisionalValue (mapCell hpq Xi) = R.stableValue t p Xi) ∧
        (p.label Xi = ⊤ → R.stableValue t p Xi = ⊤ →
          ofOrd (α.1 + K) < y.type.someProvisionalValue (mapCell hpq Xi)) :=
  exists_syncCover' hcons hcov hpt K

/-- **Gate 3, the decisive theorem — Lemma 5.3.10's semantic half**: stable
labels respect their unchanged semantics. Monotone natural observations on a
finite coordinate set synchronize, and one sufficiently high jump reconstructs
their completed-band supremum from a lawful finite observation.

Only source exact parent consistency and initial-segment covering are used.
The finite-vector argument is shared and topology-free; the occurrence-level
synchronizing-cover interface remains available for its other clients.
Successor modelhood is a separate result. -/
theorem stableLiftRespects_of_consistent (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) :
    RespectsSemantics p.scheme.rows (fun Xi => R.stableValue t p Xi) :=
  stableLiftRespects_of_finiteJump hcons hcov hpt

/-- Gate 3 in its original interface: the source is a model. -/
theorem stableLiftRespects (hR : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) :
    RespectsSemantics p.scheme.rows (fun Xi => R.stableValue t p Xi) :=
  stableLiftRespects_of_consistent hR.consistent hR.covering hpt

/-! ### Gates 4–6: the stable type, the realization, the model clauses

The stable type and the stabilized realization are built from exact parent consistency and
initial-segment covering of the source alone (`stableLiftTypeOf`, `stableLiftOf`); the
model-hypothesis names `stableLiftType`, `stableLift` are definitional wrappers, so every
existing statement about them is unchanged. -/

/-- **Gate 4: the stable lift of a realized type** — same scheme and rows, labels the stable
values; a genuine stage type of `S^{α+ω}` by gate 3.  Consistency-and-covering form. -/
noncomputable def stableLiftTypeOf (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n)
    (hpt : R.eval t = some p) : S (α.1 + Ordinal.omega0) n where
  scheme := p.scheme
  label Xi := R.stableValue t p Xi
  label_bound Xi := by
    rcases R.hasStableValue_stableValue t p Xi with ⟨hlt, -⟩ | ⟨heq, -⟩
    · exact Or.inl hlt
    · exact Or.inr heq
  respects := stableLiftRespects_of_consistent hcons hcov hpt

/-- **Gate 4** in its original interface: the source is a model. -/
noncomputable def stableLiftType (hR : R.IsModel) {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n)
    (hpt : R.eval t = some p) : S (α.1 + Ordinal.omega0) n :=
  stableLiftTypeOf hR.consistent hR.covering t p hpt

/-- Stable values truncate to the source labels. -/
theorem truncExt_stableValue (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) (Xi : Cell p.scheme.scheme) :
    truncExt α.1 (R.stableValue t p Xi) = p.label Xi := by
  by_cases htop : p.label Xi = ⊤
  · rw [truncExt_eq_top_of_ge (le_stableValue_of_top hpt htop), htop]
  · rw [stableValue_of_ne_top hcons hcov hpt htop]
    exact truncExt_id_of_lt ((p.label_bound Xi).resolve_right htop)

section Of
variable (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering)

/-- The stable lift reduces literally to the source type. -/
theorem reduceType_stableLiftTypeOf {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) (hle : α.1 ≤ α.1 + Ordinal.omega0) :
    reduceType α.2 hle (stableLiftTypeOf hcons hcov t p hpt) = p :=
  StageType.ext rfl (heq_of_eq (funext fun Xi => truncExt_stableValue hcons hcov hpt Xi))

/-- **The stabilized realization `M⁺`**: label exactly the source-defined tuples, by their
stable lifts.  Consistency-and-covering form. -/
noncomputable def stableLiftOf : KnightRealization α.nextBlock M where
  eval {_n} t :=
    match h : R.eval t with
    | none => none
    | some p => some (stableLiftTypeOf hcons hcov t p h)

theorem stableLiftOf_eval_none {n : ℕ} {t : Fin n ↪ M}
    (h : R.eval t = none) : (stableLiftOf hcons hcov).eval t = none := by
  change (match h' : R.eval t with
    | none => none
    | some p => some (stableLiftTypeOf hcons hcov t p h')) = none
  split
  · rfl
  · next p' h' => rw [h] at h'; cases h'

theorem stableLiftOf_eval_some {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (h : R.eval t = some p) :
    (stableLiftOf hcons hcov).eval t = some (stableLiftTypeOf hcons hcov t p h) := by
  change (match h' : R.eval t with
    | none => none
    | some p => some (stableLiftTypeOf hcons hcov t p h')) = _
  split
  · next h' => rw [h] at h'; cases h'
  · next p' h' =>
      have : p' = p := Option.some_injective _ (h'.symm.trans h)
      subst this
      rfl

/-- The inverse eval equation. -/
theorem stableLiftOf_eval_eq_some {n : ℕ} {t : Fin n ↪ M}
    {q : S α.nextBlock.1 n} (h : (stableLiftOf hcons hcov).eval t = some q) :
    ∃ (p : S α.1 n) (hp : R.eval t = some p), q = stableLiftTypeOf hcons hcov t p hp := by
  by_cases hs : (R.eval t).isSome
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
    refine ⟨p, hp, ?_⟩
    rw [stableLiftOf_eval_some hcons hcov hp] at h
    exact (Option.some_injective _ h).symm
  · rw [Option.not_isSome_iff_eq_none] at hs
    rw [stableLiftOf_eval_none hcons hcov hs] at h
    cases h

/-- **The reduct of the stabilized realization is literally the source.** -/
theorem stableLiftOf_reduct : (stableLiftOf hcons hcov).reduct α.le_nextBlock = R := by
  apply Realization.ext
  intro n t
  rw [Realization.reduct_eval]
  by_cases hs : (R.eval t).isSome
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
    rw [stableLiftOf_eval_some hcons hcov hp, hp]
    change some (reduceType α.2 α.le_nextBlock (stableLiftTypeOf hcons hcov t p hp)) = some p
    exact congrArg some (reduceType_stableLiftTypeOf hcons hcov hp α.le_nextBlock)
  · rw [Option.not_isSome_iff_eq_none] at hs
    rw [stableLiftOf_eval_none hcons hcov hs, hs]
    rfl

/-- **Exact parent consistency of the stabilized realization** (gate 2's face naturality at
the level of evaluations). -/
theorem stableLiftOf_consistent : (stableLiftOf hcons hcov).IsExactParentConsistent := by
  intro m n t q' f hq'
  obtain ⟨p, hp, rfl⟩ := stableLiftOf_eval_eq_some hcons hcov hq'
  have hRf := hcons t p f hp
  change (stableLiftOf hcons hcov).eval (f.trans t) =
    typeMap f (stableLiftTypeOf hcons hcov t p hp)
  by_cases hr : Finset.univ.image f ∈ p.scheme.scheme.plan
  · -- the face is visible: both sides are the stable lift of the restricted type
    have hRf' : R.eval (f.trans t) = some (p.restrictFace f hr) := by
      rw [hRf]
      exact typeMap_eq_some f p hr
    rw [stableLiftOf_eval_some hcons hcov hRf',
      typeMap_eq_some f (stableLiftTypeOf hcons hcov t p hp) hr]
    congr 1
    refine StageType.ext rfl (heq_of_eq (funext fun Xi => ?_))
    have hpq : typeMap f p = some (p.restrictFace f hr) := typeMap_eq_some f p hr
    exact (stableValue_mapCell hcons hcov hRf' hp (rfl : f.trans t = f.trans t) hpq Xi).symm
  · -- the face is invisible: both sides are undefined
    have h3 : typeMap f p = none := by
      by_contra hne
      obtain ⟨q'', hq''⟩ := Option.ne_none_iff_exists'.mp hne
      exact hr ((typeMap_isSome_iff f p).mp (by rw [hq'']; rfl))
    have h4 : typeMap f (stableLiftTypeOf hcons hcov t p hp) = none := by
      by_contra hne
      obtain ⟨q'', hq''⟩ := Option.ne_none_iff_exists'.mp hne
      exact hr ((typeMap_isSome_iff f (stableLiftTypeOf hcons hcov t p hp)).mp
        (by rw [hq'']; rfl))
    have hRf' : R.eval (f.trans t) = none := by
      rw [hRf]
      exact h3
    rw [stableLiftOf_eval_none hcons hcov hRf']
    exact h4.symm

/-- Covering of the stabilized realization. -/
theorem stableLiftOf_covering : (stableLiftOf hcons hcov).IsInitialSegmentCovering := by
  intro n t
  obtain ⟨k, s, hs, hsome⟩ := hcov t
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨k, s, hs, ?_⟩
  rw [stableLiftOf_eval_some hcons hcov hp]
  rfl

end Of

/-! #### The model-hypothesis interface, as definitional wrappers -/

/-- The stable lift reduces literally to the source type. -/
theorem reduceType_stableLiftType (hR : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) (hle : α.1 ≤ α.1 + Ordinal.omega0) :
    reduceType α.2 hle (stableLiftType hR t p hpt) = p :=
  reduceType_stableLiftTypeOf hR.consistent hR.covering hpt hle

/-- **The stabilized realization `M⁺`**, in its original interface: the source is a model. -/
noncomputable def stableLift (hR : R.IsModel) : KnightRealization α.nextBlock M :=
  stableLiftOf hR.consistent hR.covering

theorem stableLift_eval_none (hR : R.IsModel) {n : ℕ} {t : Fin n ↪ M}
    (h : R.eval t = none) : (stableLift hR).eval t = none :=
  stableLiftOf_eval_none hR.consistent hR.covering h

theorem stableLift_eval_some (hR : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (h : R.eval t = some p) :
    (stableLift hR).eval t = some (stableLiftType hR t p h) :=
  stableLiftOf_eval_some hR.consistent hR.covering h

/-- The inverse eval equation. -/
theorem stableLift_eval_eq_some (hR : R.IsModel) {n : ℕ} {t : Fin n ↪ M}
    {q : S α.nextBlock.1 n} (h : (stableLift hR).eval t = some q) :
    ∃ (p : S α.1 n) (hp : R.eval t = some p), q = stableLiftType hR t p hp :=
  stableLiftOf_eval_eq_some hR.consistent hR.covering h

/-- **The reduct of the stabilized realization is literally the source.** -/
theorem stableLift_reduct (hR : R.IsModel) :
    (stableLift hR).reduct α.le_nextBlock = R :=
  stableLiftOf_reduct hR.consistent hR.covering

/-- **Exact parent consistency of the stabilized realization** (gate 2's face naturality at
the level of evaluations). -/
theorem stableLift_consistent (hR : R.IsModel) :
    (stableLift hR).IsExactParentConsistent :=
  stableLiftOf_consistent hR.consistent hR.covering

/-- Covering of the stabilized realization. -/
theorem stableLift_covering (hR : R.IsModel) :
    (stableLift hR).IsInitialSegmentCovering :=
  stableLiftOf_covering hR.consistent hR.covering

end KnightRealization

end VaughtConjecture.Knight
