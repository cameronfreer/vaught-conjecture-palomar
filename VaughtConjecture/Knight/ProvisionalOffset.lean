/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.StableValue
public import VaughtConjecture.Knight.ProvisionalLeastLift

/-! # Provisional offsets on the rooted covers of an occurrence

Fix an actual labelled cover `x` and a cell `Ξ` of its type.  The **rooted covers** of `x` are
the labelled covers above `x` in the cover order (`RootedCover x`); each carries a unique
embedding of `x` (`RootedCover.emb`, by `LabelledExt.emb_unique`), hence an actual transport
of `Ξ` (`RootedCover.cell`) and a provisional value there (`RootedCover.value`).  The
least lawful finite lift makes that value monotone along rooted covers (`value_mono`).

For a top cell the provisional value is `α + j` with a natural offset `j`
(`RootedCover.offset`), so the offsets form a monotone natural-valued observation on a
nonempty directed preorder, and the generic theory of `DirectedNat` applies:

* stabilization to `α + k` is exactly eventual constancy of the offset at `k`
  (`stabilizesTo_iff_eventually_offset_eq`);
* the stable value is `⊤` exactly when the offsets escape every finite bound
  (`stableValue_eq_top_iff_tendsto`);
* `stableValue_dichotomy` packages the two cases, and
  `exists_stabilizesTo_of_bddAbove` is the bounded case used by `AnchorStable` and
  `DefectFiniteWitness`;
* `eventually_syncValues` is **finite synchronization** as one eventual condition in the
  rooted-cover filter: every cell eventually reads its proper stable value literally, and every
  stable top eventually escapes a prescribed finite threshold strictly.  Its occurrence-level
  adapter is `exists_syncCover'` (`StableLiftCore`).

Directedness of the rooted covers needs exact parent consistency and initial-segment covering
of the source; the consistency-only uniqueness theorems of `ProvisionalRatchet` are consumed
here, not strengthened. -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd StageType Filter

universe w

namespace KnightRealization

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-- The rooted covers of `x`: labelled covers above `x` in the cover order. -/
abbrev RootedCover (x : R.LabelledExt) := {y : R.LabelledExt // x ≤ y}

namespace RootedCover

variable {x : R.LabelledExt}

instance : Nonempty (RootedCover x) := ⟨⟨x, le_rfl⟩⟩

/-- Rooted covers are directed, from directedness of the cover order. -/
theorem isDirectedOrder (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering)
    (x : R.LabelledExt) : IsDirectedOrder (RootedCover x) :=
  ⟨fun y z => by
    obtain ⟨w, hyw, hzw⟩ := directed_labelledExt hcons hcov y.1 z.1
    exact ⟨⟨w, y.2.trans hyw⟩, hyw, hzw⟩⟩

/-! ### The transport of the root and of a fixed cell -/

/-- The embedding of `x` into a rooted cover. -/
noncomputable def emb (y : RootedCover x) : Fin x.arity ↪ Fin y.1.arity := y.2.choose

theorem emb_trans (y : RootedCover x) : (emb y).trans y.1.tuple = x.tuple := y.2.choose_spec.1

theorem emb_typeMap (y : RootedCover x) : typeMap (emb y) y.1.type = some x.type :=
  y.2.choose_spec.2

/-- The embedding is determined by the tuples. -/
theorem emb_eq (y : RootedCover x) {f : Fin x.arity ↪ Fin y.1.arity}
    (hf : f.trans y.1.tuple = x.tuple) : emb y = f :=
  LabelledExt.emb_unique (emb_trans y) hf

/-- The actual transport of a cell of `x` into a rooted cover. -/
noncomputable def cell (y : RootedCover x) (Xi : Cell x.type.scheme.scheme) :
    Cell y.1.type.scheme.scheme :=
  mapCell (emb_typeMap y) Xi

/-- The transported cell along any embedding realizing the cover relation. -/
theorem cell_eq (y : RootedCover x) {f : Fin x.arity ↪ Fin y.1.arity}
    (hf : typeMap f y.1.type = some x.type) (hft : f.trans y.1.tuple = x.tuple)
    (Xi : Cell x.type.scheme.scheme) : cell y Xi = mapCell hf Xi := by
  have h : ∀ (g : Fin x.arity ↪ Fin y.1.arity) (hg : typeMap g y.1.type = some x.type),
      g = f → mapCell hg Xi = mapCell hf Xi := by
    rintro g hg rfl
    rfl
  exact h (emb y) (emb_typeMap y) (emb_eq y hft)

/-- Transport composes along rooted covers. -/
theorem cell_trans {y z : RootedCover x} {g : Fin y.1.arity ↪ Fin z.1.arity}
    (hgt : g.trans z.1.tuple = y.1.tuple) (hg : typeMap g z.1.type = some y.1.type)
    (Xi : Cell x.type.scheme.scheme) : cell z Xi = mapCell hg (cell y Xi) := by
  have hpz : typeMap ((emb y).trans g) z.1.type = some x.type := by
    rw [← typeMap_trans (emb y) g z.1.type y.1.type hg]
    exact emb_typeMap y
  have hft : ((emb y).trans g).trans z.1.tuple = x.tuple := by
    rw [Function.Embedding.trans_assoc, hgt, emb_trans]
  rw [cell_eq z hpz hft]
  exact mapCell_trans hg (emb_typeMap y) hpz Xi

theorem label_cell (y : RootedCover x) (Xi : Cell x.type.scheme.scheme) :
    y.1.type.label (cell y Xi) = x.type.label Xi :=
  label_mapCell (emb_typeMap y) Xi

/-! ### The provisional value along rooted covers -/

/-- The provisional value of the transported cell. -/
noncomputable def value (y : RootedCover x) (Xi : Cell x.type.scheme.scheme) : ExtOrd :=
  y.1.type.someProvisionalValue (cell y Xi)

theorem isProvisionalValue_value (y : RootedCover x) (Xi : Cell x.type.scheme.scheme) :
    y.1.type.IsProvisionalValue (cell y Xi) (value y Xi) :=
  isProvisionalValue_someProvisionalValue _ _

/-- **The ratchet along rooted covers**: leastness of the lawful finite lift
proves monotonicity at the limit stage, without the old ratchet theorem. -/
theorem value_mono (Xi : Cell x.type.scheme.scheme) :
    Monotone fun y : RootedCover x => value y Xi := by
  intro y z h
  obtain ⟨g, hgt, hg⟩ := (h : y.1 ≤ z.1)
  change y.1.type.someProvisionalValue (cell y Xi) ≤
    z.1.type.someProvisionalValue (cell z Xi)
  rw [cell_trans hgt hg Xi]
  exact provisional_le_mapCell_of_least α.2 hg (cell y Xi)

/-- A rooted cover whose transported provisional value is `γ` lies in the stable set. -/
theorem mem_stableSet (y : RootedCover x) (Xi : Cell x.type.scheme.scheme) :
    y.1 ∈ stableSet x Xi (value y Xi) :=
  ⟨emb y, emb_trans y, emb_typeMap y, isProvisionalValue_value y Xi⟩

/-! ### Top cells: the natural offset -/

section Top

variable (Xi : Cell x.type.scheme.scheme) (htop : x.type.label Xi = ⊤)

include htop in
theorem exists_offset (y : RootedCover x) : ∃ j : ℕ, value y Xi = ofOrd (α.1 + j) :=
  someProvisionalValue_top_form (by rw [label_cell]; exact htop)

/-- The natural offset of the transported top cell's provisional value. -/
noncomputable def offset (y : RootedCover x) : ℕ := (exists_offset Xi htop y).choose

theorem value_eq_offset (y : RootedCover x) :
    value y Xi = ofOrd (α.1 + offset Xi htop y) :=
  (exists_offset Xi htop y).choose_spec

theorem offset_le_of_value_le {y : RootedCover x} {K : ℕ}
    (h : value y Xi ≤ ofOrd (α.1 + K)) : offset Xi htop y ≤ K := by
  rw [value_eq_offset Xi htop y, ofOrd_le_ofOrd] at h
  exact Nat.cast_le.mp (le_of_add_le_add_left h)

theorem offset_eq_of_value_eq {y : RootedCover x} {k : ℕ}
    (h : value y Xi = ofOrd (α.1 + k)) : offset Xi htop y = k := by
  have := (value_eq_offset Xi htop y).symm.trans h
  rw [ofOrd_inj] at this
  exact Nat.cast_injective (add_left_cancel this)

/-- **Monotonicity of the offset**, from the ratchet. -/
theorem offset_mono : Monotone (offset Xi htop) := by
  intro y z h
  have := value_mono Xi h
  change value y Xi ≤ value z Xi at this
  rw [value_eq_offset Xi htop y, value_eq_offset Xi htop z, ofOrd_le_ofOrd] at this
  exact Nat.cast_le.mp (le_of_add_le_add_left this)

/-! ### Stabilization is eventual constancy; stable top is escape -/

variable (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering)

include hcons hcov in
/-- An eventually constant offset stabilizes. -/
theorem stabilizesTo_of_eventually {k : ℕ} (h : ∀ᶠ y in atTop, offset Xi htop y = k) :
    R.StabilizesTo x.tuple x.type Xi (ofOrd (α.1 + k)) := by
  have := isDirectedOrder hcons hcov x
  rw [stabilizesTo_iff_isDominating hcons hcov x Xi]
  intro a
  obtain ⟨i, hi⟩ := eventually_atTop.mp h
  obtain ⟨w, haw, hiw⟩ := directed_labelledExt hcons hcov a i.1
  let w' : RootedCover x := ⟨w, i.2.trans hiw⟩
  have hw : value w' Xi = ofOrd (α.1 + k) := by
    rw [value_eq_offset Xi htop w', hi w' hiw]
  exact ⟨w, hw ▸ mem_stableSet w' Xi, haw⟩

include hcons hcov in
/-- Escaping offsets stabilize to no proper value. -/
theorem not_stabilizesTo_of_tendsto (h : Tendsto (offset Xi htop) atTop atTop)
    {δ : ExtOrd} (hs : R.StabilizesTo x.tuple x.type Xi δ) : False := by
  have := isDirectedOrder hcons hcov x
  -- the stabilized value is read off one rooted cover
  obtain ⟨m, u, g, f, q, hpq, hu, -, hfu, hval⟩ := hs x.tuple
  let y : RootedCover x := ⟨⟨m, u, q, hu⟩, f, hfu, hpq⟩
  have hδ : δ = ofOrd (α.1 + offset Xi htop y) := by
    rw [← value_eq_offset Xi htop y, isProvisionalValue_iff.mp hval]
    exact congrArg _ (cell_eq y hpq hfu Xi).symm
  -- beyond some rooted cover every offset exceeds it
  obtain ⟨i, hi⟩ := tendsto_atTop_atTop.mp h (offset Xi htop y + 1)
  obtain ⟨m', u', g', f', q', hpq', hu', hgu', hfu', hval'⟩ := hs i.1.tuple
  let z : RootedCover x := ⟨⟨m', u', q', hu'⟩, f', hfu', hpq'⟩
  have hiz : i ≤ z := by
    refine ⟨g', hgu', ?_⟩
    have hc := hcons u' q' g' hu'
    rw [hgu', i.1.eval_eq] at hc
    exact hc.symm
  have hz : offset Xi htop z = offset Xi htop y := by
    apply offset_eq_of_value_eq Xi htop
    rw [← hδ, isProvisionalValue_iff.mp hval']
    exact congrArg _ (cell_eq z hpq' hfu' Xi)
  have := hi z hiz
  omega

include hcons hcov in
/-- **Stabilization is eventual constancy of the offset.** -/
theorem stabilizesTo_iff_eventually_offset_eq (k : ℕ) :
    R.StabilizesTo x.tuple x.type Xi (ofOrd (α.1 + k)) ↔
      ∀ᶠ y in atTop, offset Xi htop y = k := by
  have := isDirectedOrder hcons hcov x
  refine ⟨fun hs => ?_, stabilizesTo_of_eventually Xi htop hcons hcov⟩
  rcases DirectedNat.eventually_constant_or_tendsto (offset_mono Xi htop) with ⟨k', hk'⟩ | ht
  · have hk : ofOrd (α.1 + k) = ofOrd (α.1 + k') :=
      StabilizesTo.unique_of_consistent hcons hs
        (stabilizesTo_of_eventually Xi htop hcons hcov hk')
    rw [ofOrd_inj] at hk
    obtain rfl : k = k' := Nat.cast_injective (add_left_cancel hk)
    exact hk'
  · exact (not_stabilizesTo_of_tendsto Xi htop hcons hcov ht hs).elim

include hcons hcov in
/-- **The bounded case**: bounded offsets stabilize at an attained offset. -/
theorem exists_stabilizesTo_of_bddAbove (hb : BddAbove (Set.range (offset Xi htop))) :
    ∃ i : RootedCover x, R.StabilizesTo x.tuple x.type Xi (ofOrd (α.1 + offset Xi htop i)) := by
  have := isDirectedOrder hcons hcov x
  obtain ⟨i, hi⟩ := DirectedNat.eventually_eq_of_bddAbove (offset_mono Xi htop) hb
  exact ⟨i, stabilizesTo_of_eventually Xi htop hcons hcov hi⟩

include hcons hcov in
/-- **Stable top is escape**: the stable value is `⊤` iff the offsets exceed every bound. -/
theorem stableValue_eq_top_iff_tendsto :
    R.stableValue x.tuple x.type Xi = ⊤ ↔ Tendsto (offset Xi htop) atTop atTop := by
  have := isDirectedOrder hcons hcov x
  constructor
  · intro htopv
    rcases DirectedNat.eventually_constant_or_tendsto (offset_mono Xi htop) with ⟨k, hk⟩ | ht
    · have hs : R.StabilizesTo x.tuple x.type Xi (ofOrd (α.1 + k)) :=
        stabilizesTo_of_eventually Xi htop hcons hcov hk
      have hval : R.stableValue x.tuple x.type Xi = ofOrd (α.1 + k) :=
        stableValue_of_stabilizesTo hcons hcov x.eval_eq (ofOrd_lt_ofOrd.mpr
          ((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 k))) hs
      rw [htopv] at hval
      exact absurd hval.symm (ofOrd_ne_top _)
    · exact ht
  · intro ht
    rcases R.hasStableValue_stableValue x.tuple x.type Xi with ⟨-, hs⟩ | ⟨heq, -⟩
    · exact (not_stabilizesTo_of_tendsto Xi htop hcons hcov ht hs).elim
    · exact heq

include hcons hcov in
/-- **The dichotomy**: the offset is eventually constant at the stable value's offset, or it
escapes every bound and the stable value is `⊤`. -/
theorem stableValue_dichotomy :
    (∃ k : ℕ, (∀ᶠ y in atTop, offset Xi htop y = k) ∧
      R.stableValue x.tuple x.type Xi = ofOrd (α.1 + k)) ∨
    (Tendsto (offset Xi htop) atTop atTop ∧ R.stableValue x.tuple x.type Xi = ⊤) := by
  have := isDirectedOrder hcons hcov x
  rcases DirectedNat.eventually_constant_or_tendsto (offset_mono Xi htop) with ⟨k, hk⟩ | ht
  · refine Or.inl ⟨k, hk, ?_⟩
    exact stableValue_of_stabilizesTo hcons hcov x.eval_eq (ofOrd_lt_ofOrd.mpr
      ((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 k)))
      (stabilizesTo_of_eventually Xi htop hcons hcov hk)
  · exact Or.inr ⟨ht, (stableValue_eq_top_iff_tendsto Xi htop hcons hcov).mpr ht⟩

end Top

/-! ### Finite synchronization in the rooted-cover filter -/

/-- **Finite synchronization, as an eventual condition on rooted covers.**  Eventually every
cell of `x` with a proper stable value carries it as its provisional value, and every source-top
cell with stable value `⊤` has provisional value strictly above `α + K`.  The threshold `K` only
bounds the required escape: a proper stable value is read exactly even when it lies above
`α + K`.  Top cells use `stableValue_dichotomy`; non-top cells, including bottom, are literal at
every rooted cover.  The cell family is finite, so the conditions intersect in the filter. -/
theorem eventually_syncValues (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x : R.LabelledExt) (K : ℕ) :
    ∀ᶠ y : RootedCover x in atTop, ∀ Xi : Cell x.type.scheme.scheme,
      (R.stableValue x.tuple x.type Xi ≠ ⊤ →
        value y Xi = R.stableValue x.tuple x.type Xi) ∧
      (x.type.label Xi = ⊤ → R.stableValue x.tuple x.type Xi = ⊤ →
        ofOrd (α.1 + K) < value y Xi) := by
  have := isDirectedOrder hcons hcov x
  refine eventually_all.mpr fun Xi => ?_
  by_cases htop : x.type.label Xi = ⊤
  · rcases stableValue_dichotomy Xi htop hcons hcov with ⟨k, hk, hval⟩ | ⟨ht, hsv⟩
    · -- a proper stable value: the offset is eventually its plateau
      refine hk.mono fun y hy => ⟨fun _ => ?_, fun _ hsv => ?_⟩
      · rw [value_eq_offset Xi htop y, hy, hval]
      · exact absurd (hval.symm.trans hsv) (ofOrd_ne_top _)
    · -- a stable top: the offset eventually exceeds `K`
      refine (ht.eventually (eventually_gt_atTop K)).mono fun y hy => ?_
      refine ⟨fun hne => absurd hsv hne, fun _ _ => ?_⟩
      rw [value_eq_offset Xi htop y, ofOrd_lt_ofOrd]
      exact (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hy)
  · -- a non-top label is literal at every rooted cover, including bottom
    refine Eventually.of_forall fun y => ⟨fun _ => ?_, fun h => absurd h htop⟩
    rw [stableValue_of_ne_top hcons hcov x.eval_eq htop]
    change y.1.type.someProvisionalValue (cell y Xi) = x.type.label Xi
    rw [someProvisionalValue_of_ne_top (by rw [label_cell]; exact htop), label_cell]

end RootedCover

end KnightRealization

end VaughtConjecture.Knight
