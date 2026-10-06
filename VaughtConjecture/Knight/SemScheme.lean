/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Semantics

/-! # Knight's domains with their associated semantics: bountiful, complete, coded

Knight's Def. 2.6.1 (a *domain* on `P̂`) is a finite set of cells
`⟨B, j, P↾B, D, E, ⌜Ξ⌝⟩` from which the semantics `E` is **recoverable** (the coding described
after Def. 2.6.2, Prop. 2.6.3(2)); Knight-VC's `Sem.Domain` kept cells bare and the semantics a free field, so
"associated semantics" became a model-relative `Prop` there and §2.6 was never formalized
(KVC-d11).  The faithful, coding-free rendering (#88) is to let the **scheme own its rows**:

* `Semantics.IsBountiful` (Def. 2.5.14), `CellScheme.IsComplete` (Def. 2.5.15) and
  `Semantics.IsCoded` (the coding convention of Lemma 2.5.13) are the three properties of
  the associated semantics;
* `SemScheme n` is a *domain with its associated semantics* (Def. 2.6.1) in record form: a
  cell scheme over `Fin n` together with coded, consistent, bountiful rows, the scheme
  complete.  Association is by representation, not by the paper's coding theorem: a cell is
  carried *dependently* with its scheme (`Cell D` is indexed by `D : SemScheme n`), so the pair
  `(D, Ξ)` determines `E`; a bare cell index does **not** decode its scheme.  This replaces
  Prop. 2.6.3(2) by a representation change rather than proving it literally, and there is no
  separate `D_A`.  The codes `⌜Ξ⌝` are therefore unnecessary.  The disjointness clause
  Prop. 2.6.3(6) (cells of two domains are disjoint outside their overlap) is *inapplicable* to
  indexed cell types — literal intersection of `Cell D` and `Cell D'` has no meaning — and its
  mathematical role (well-defined unions of domains) must be discharged by explicit overlap /
  amalgamation maps when amalgams are constructed (#41);
* `Countable (SemScheme n)` (Prop. 2.6.3(4)) comes from countably many coded schemes — a
  `SemScheme` injects into `Σ D, (Sig : Cell D) → D.below (D.cell Sig) → codedLabels`, with
  `codedLabels = {⊥} ∪ {ofOrd (ω·i + j)}` countable — and **not** from any stage bound;
* `SemScheme.restrictFace` (Prop. 2.6.3(3)/(5), horizontal restriction): the restricted
  scheme is isomorphic to the original on every lower set `below ⟨B,j⟩` with `B ⊆ range f`
  (`CellScheme.restrictFace.belowEquiv`), and all four properties are statements about
  lower sets, so they transport along that isomorphism
  (`RespectsSemanticsBelow.restrictFace` / `.of_restrictFace`).

This is PR 1 of #88; the faithful stage types over `SemScheme` are PR 2. -/

@[expose] public section

namespace VaughtConjecture.Knight

open VaughtConjecture.AmalgamationPlan

open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-! ### Lower sets: the inclusion along the graded preorder -/

/-- The inclusion of lower sets along the graded preorder: `D.below X ⊆ D.below Y` when
`X ≤ Y` (the paper's `D⟨C,i⟩ ⊆ D⟨B,j⟩` for `⟨C,i⟩ ≤ ⟨B,j⟩`). -/
def CellScheme.below.mono {X Y : Finset ι × ℕ} (h : GradedLe X Y) (d : D.below X) :
    D.below Y :=
  ⟨d.1, d.2.trans h⟩

@[simp] theorem CellScheme.below.mono_val {X Y : Finset ι × ℕ} (h : GradedLe X Y)
    (d : D.below X) : (CellScheme.below.mono (D := D) h d).1 = d.1 := rfl

/-- **Restriction of respect**: a labelling respecting the restricted semantics `E⟨B,j⟩` restricts
along `D⟨C,i⟩ ⊆ D⟨B,j⟩` to one respecting `E⟨C,i⟩`.  Availability restricts because the ambient
witness has exactly the graded index of the request, hence lies in the smaller lower set. -/
theorem RespectsSemanticsBelow.mono {sem : Semantics D} {CI BJ : Finset ι × ℕ} (h : GradedLe CI BJ)
    {q : D.below BJ → ExtOrd} (hq : RespectsSemanticsBelow sem BJ q) :
    RespectsSemanticsBelow sem CI (fun d => q (CellScheme.below.mono h d)) where
  orderly d := hq.orderly (CellScheme.below.mono h d)
  locality d := hq.locality (CellScheme.below.mono h d)
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, he, hv⟩ :=
      hq.availability (CellScheme.below.mono h Sig) (CellScheme.below.mono h Xi₀) hs hg
    have hm : GradedLe (D.cell Xi.1) CI := by rw [he]; exact Xi₀.2
    exact ⟨⟨Xi.1, hm⟩, he, hv⟩

/-! ### Bountiful, complete, coded -/

/-- A semantics is **bountiful** (Knight, Def. 2.5.14; stated for a consistent semantics):
whenever `⟨C,i⟩ ≺ ⟨B,j⟩` in `P̂`, `p` is a labelling of `D⟨C,i⟩` respecting `E⟨C,i⟩`, `q` a
labelling of `D⟨B,j⟩` respecting `E⟨B,j⟩`, `γ` a label with `γ = γ ⊔⁺_j j`, and
`(q ∧ γ) ↾ D⟨C,i⟩ = p ∧ γ`, then there is `q'` on `D⟨B,j⟩` respecting `E⟨B,j⟩` with
`q' ∧ γ = q ∧ γ` and `q' ↾ D⟨C,i⟩ = p`.  Here `D⟨B,j⟩ = D.below BJ`, the inclusion is
`below.mono`, respect of `E⟨B,j⟩` is `RespectsSemanticsBelow`, and `∧ γ` is the pointwise
`min · γ`; the pairs range over the graded plan `P̂`. -/
def Semantics.IsBountiful (sem : Semantics D) : Prop :=
  ∀ (CI BJ : Finset ι × ℕ), CI ∈ Plan.gradedPlan D.plan → BJ ∈ Plan.gradedPlan D.plan →
    (h : GradedLe CI BJ) → CI ≠ BJ →
    ∀ (p : D.below CI → ExtOrd) (q : D.below BJ → ExtOrd) (γ : ExtOrd),
      RespectsSemanticsBelow sem CI p → RespectsSemanticsBelow sem BJ q →
      extVisibilityReplace γ BJ.2 BJ.2 = γ →
      (∀ d : D.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) →
      ∃ q' : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ q' ∧
        (∀ d : D.below BJ, min (q' d) γ = min (q d) γ) ∧
        (∀ d : D.below CI, q' (CellScheme.below.mono h d) = p d)

/-- A cell scheme is **complete** (Knight, Def. 2.5.15): every graded pair `⟨B,j⟩ ∈ P̂` is
the graded index of some cell (`D^{B,j} ≠ ∅`). -/
def CellScheme.IsComplete (D : CellScheme A) : Prop :=
  ∀ BJ ∈ Plan.gradedPlan D.plan, ∃ d : Cell D, D.cell d = BJ

/-- A label is **coded at grade `k`** (the coding convention of Knight, Lemma 2.5.13 /
Def. 2.6): it is `⊥` or an ordinal `ω·i + j` with `j ≤ k + 1` (no `⊤`). -/
def ExtOrd.IsCodedLabel (k : ℕ) (x : ExtOrd) : Prop :=
  x = ⊥ ∨ ∃ i j : ℕ, j ≤ k + 1 ∧ x = ofOrd (Ordinal.omega0 * i + j)

/-- The set of all coded labels (at any grade): `⊥` and the ordinals `ω·i + j`. -/
def ExtOrd.codedLabels : Set ExtOrd :=
  insert ⊥ (Set.range fun ij : ℕ × ℕ => ofOrd (Ordinal.omega0 * ij.1 + ij.2))

theorem ExtOrd.codedLabels_countable : ExtOrd.codedLabels.Countable :=
  (Set.countable_range _).insert _

theorem ExtOrd.IsCodedLabel.mem_codedLabels {k : ℕ} {x : ExtOrd} (h : IsCodedLabel k x) :
    x ∈ codedLabels := by
  rcases h with rfl | ⟨i, j, -, rfl⟩
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨(i, j), rfl⟩

/-- A semantics is **coded** (Knight, Lemma 2.5.13: "if `a(Σ) = k`, the range of `E(Σ)` is
contained in `{−∞} ∪ {ωi + j : i ∈ ω, 0 ≤ j ≤ k+1}`"): every value of the row of a cell `Sig`
is a coded label at the grade of `Sig`. -/
def Semantics.IsCoded (sem : Semantics D) : Prop :=
  ∀ (Sig : Cell D) (d : D.below (D.cell Sig)), ExtOrd.IsCodedLabel (D.grade Sig) (sem.E Sig d)

/-! ### Domains with their associated semantics -/

/-- A *domain with its associated semantics* (Knight, Def. 2.6.1) in record form: a cell
scheme over `Fin n` that **owns its rows** — coded (Lemma 2.5.13), consistent (Def. 2.5.12),
bountiful (Def. 2.5.14), the scheme complete (Def. 2.5.15).  Association is by representation
(the semantics is a field of the scheme, and a cell is carried dependently with its scheme),
not by the paper's literal coding theorem Prop. 2.6.3(2).  Only the empty scheme is constructed
in this file (`emptyType` at arity 0, `Knight.Type`); positive-arity domains (mute domains and
their one-point extension, `SemScheme.nonempty`) are in `Knight.Domain` (#41 (1/3)), amalgams
are not on the runway (#41 PR 2 is the fixed-domain coface experiment; the non-mute domain
producer is #106).  Inhabitants of `S α n` at every arity and limit stage are `StageType.nonempty`
(`Knight.Domain`). -/
structure SemScheme (n : ℕ) where
  /-- The cell scheme. -/
  scheme : CellScheme (ι := Fin n) Finset.univ
  /-- The associated semantics: the rows of the scheme. -/
  rows : Semantics scheme
  /-- The rows are coded (Lemma 2.5.13). -/
  rows_coded : rows.IsCoded
  /-- The rows are consistent (Def. 2.5.12). -/
  consistent : rows.IsConsistent
  /-- The rows are bountiful (Def. 2.5.14). -/
  bountiful : rows.IsBountiful
  /-- The scheme is complete (Def. 2.5.15). -/
  complete : scheme.IsComplete

namespace SemScheme

variable {n : ℕ}

/-- Extensionality: two domains are equal when their schemes and rows agree (`rows` depends
on `scheme`, hence `HEq`); the `Prop` fields follow by proof irrelevance. -/
@[ext]
theorem ext {D₁ D₂ : SemScheme n} (h_scheme : D₁.scheme = D₂.scheme)
    (h_rows : HEq D₁.rows D₂.rows) : D₁ = D₂ := by
  obtain ⟨s₁, r₁, _, _, _, _⟩ := D₁
  obtain ⟨s₂, r₂, _, _, _, _⟩ := D₂
  subst h_scheme
  obtain rfl := eq_of_heq h_rows
  rfl

/-- There are countably many domains with associated semantics (Knight, Prop. 2.6.3(4)):
a domain is its (countable, `CellScheme.countable_fin`) scheme together with finitely many
row values in the countable set of coded labels (`ExtOrd.codedLabels_countable`).  No stage
bound is involved. -/
instance countable : Countable (SemScheme n) := by
  have := ExtOrd.codedLabels_countable.to_subtype
  let g : SemScheme n → Σ D : CellScheme (ι := Fin n) Finset.univ,
      (Sig : Cell D) → D.below (D.cell Sig) → ExtOrd.codedLabels :=
    fun X => ⟨X.scheme, fun Sig d => ⟨X.rows.E Sig d, (X.rows_coded Sig d).mem_codedLabels⟩⟩
  have hinj : Function.Injective g := by
    rintro ⟨s₁, r₁, _, _, _, _⟩ ⟨s₂, r₂, _, _, _, _⟩ h
    obtain rfl : s₁ = s₂ := congrArg Sigma.fst h
    rw [Sigma.mk.injEq, heq_eq_eq] at h
    obtain rfl : r₁ = r₂ := Semantics.ext
      (funext fun Sig => funext fun d => congrArg Subtype.val (congrFun (congrFun h.2 Sig) d))
    rfl
  exact hinj.countable

end SemScheme

/-! ### Transport along face restriction

For `D` a scheme on `Fin n`, `f : Fin m ↪ Fin n` with visible range, and `D' := D.restrictFace
f hr`: a graded pair `BJ' = (B', j)` of `Fin m` pushes forward to `(f[B'], j)`, and the lower
set `D'.below BJ'` is in bijection with `D.below (f[B'], j)` via `toCell` — every cell of `D`
below `(f[B'], j)` has scope inside `f[B'] ⊆ range f`, hence is visible.  Respect of the
restricted semantics transports both ways along this bijection. -/

namespace CellScheme.restrictFace

variable {m n : ℕ} (D : CellScheme (ι := Fin n) Finset.univ) (f : Fin m ↪ Fin n)
  (hr : Finset.univ.image f ∈ D.plan)

/-- The push-forward of a graded pair of `Fin m` along `f`: `(B', j) ↦ (f[B'], j)`. -/
def pushGraded (BJ' : Finset (Fin m) × ℕ) : Finset (Fin n) × ℕ := (BJ'.1.image f, BJ'.2)

theorem pushGraded_injective : Function.Injective (pushGraded f) := by
  rintro ⟨B, j⟩ ⟨C, k⟩ h
  simp only [pushGraded, Prod.mk.injEq] at h
  obtain ⟨hB, rfl⟩ := h
  rw [Finset.image_injective f.injective hB]

theorem gradedLe_pushGraded_iff {X Y : Finset (Fin m) × ℕ} :
    GradedLe (pushGraded f X) (pushGraded f Y) ↔ GradedLe X Y := by
  simp only [GradedLe, pushGraded, Finset.image_subset_image_iff f.injective]

/-- The graded index of a restricted cell pushes forward to that of the underlying cell. -/
theorem pushGraded_cell (i : Cell (D.restrictFace f hr)) :
    pushGraded f ((D.restrictFace f hr).cell i) = D.cell (toCell D f hr i) :=
  Prod.ext (image_scope_restrictFace D f hr i) rfl

/-- Membership in the graded plan of the restriction: `BJ' ∈ P̂'` iff its push-forward is
in `P̂`. -/
theorem mem_gradedPlan_restrictFace {BJ' : Finset (Fin m) × ℕ} :
    BJ' ∈ Plan.gradedPlan (D.restrictFace f hr).plan ↔
      pushGraded f BJ' ∈ Plan.gradedPlan D.plan := by
  simp only [Plan.mem_gradedPlan, Plan.MemGraded, pushGraded, mem_restrictFace_plan,
    Finset.card_image_of_injective _ f.injective]

/-- A restricted cell lies below `BJ'` iff its underlying cell lies below the push-forward
of `BJ'`. -/
theorem gradedLe_cell_pushGraded_iff {BJ' : Finset (Fin m) × ℕ}
    (i : Cell (D.restrictFace f hr)) :
    GradedLe ((D.restrictFace f hr).cell i) BJ' ↔
      GradedLe (D.cell (toCell D f hr i)) (pushGraded f BJ') := by
  rw [← pushGraded_cell, gradedLe_pushGraded_iff]

variable {BJ' : Finset (Fin m) × ℕ} {BJ : Finset (Fin n) × ℕ}

/-- The lower set below `BJ'` in the restriction maps into the lower set below the
push-forward `BJ` of `BJ'` in `D`, by the cell map `toCell` (the general form of `belowMap`;
the target index is any `BJ` propositionally equal to the push-forward, so that `belowMap`
itself is the instance `BJ = D.cell (toCell Sig)`, `pushGraded_cell`). -/
noncomputable def belowMapGraded (hBJ : pushGraded f BJ' = BJ)
    (d : (D.restrictFace f hr).below BJ') : D.below BJ :=
  ⟨toCell D f hr d.1, hBJ ▸ (gradedLe_cell_pushGraded_iff D f hr d.1).mp d.2⟩

@[simp] theorem belowMapGraded_val (hBJ : pushGraded f BJ' = BJ)
    (d : (D.restrictFace f hr).below BJ') :
    (belowMapGraded D f hr hBJ d).1 = toCell D f hr d.1 := rfl

theorem belowMapGraded_injective (hBJ : pushGraded f BJ' = BJ) :
    Function.Injective (belowMapGraded D f hr hBJ) := fun a b h => by
  have h' := congrArg Subtype.val h
  simp only [belowMapGraded_val] at h'
  exact Subtype.ext (toCell_injective D f hr h')

/-- Every cell of `D` below `(f[B'], j)` is visible, hence comes from a restricted cell below
`BJ'`. -/
theorem belowMapGraded_surjective (hBJ : pushGraded f BJ' = BJ) :
    Function.Surjective (belowMapGraded D f hr hBJ) := by
  subst hBJ
  rintro ⟨e, he⟩
  have hvis : D.scope e ⊆ Finset.univ.image f :=
    he.1.trans (Finset.image_subset_image (Finset.subset_univ _))
  obtain ⟨i, rfl⟩ := exists_toCell_eq D f hr hvis
  exact ⟨⟨i, (gradedLe_cell_pushGraded_iff D f hr i).mpr he⟩, rfl⟩

theorem belowMapGraded_bijective (hBJ : pushGraded f BJ' = BJ) :
    Function.Bijective (belowMapGraded D f hr hBJ) :=
  ⟨belowMapGraded_injective D f hr hBJ, belowMapGraded_surjective D f hr hBJ⟩

/-- The lower set below `BJ'` in the restriction is **in bijection** with the lower set
below its push-forward `(f[B'], j)` in `D` (Prop. 2.6.3(3): the restriction is isomorphic to
the original on every `D⟨B,j⟩` with `B ⊆ range f`).  The forward map is `toCell` on
underlying cells; at `BJ = D.cell (toCell Sig)` (`pushGraded_cell`) it is `belowMap`. -/
noncomputable def belowEquiv (hBJ : pushGraded f BJ' = BJ) :
    (D.restrictFace f hr).below BJ' ≃ D.below BJ :=
  Equiv.ofBijective _ (belowMapGraded_bijective D f hr hBJ)

@[simp] theorem belowEquiv_apply_val (hBJ : pushGraded f BJ' = BJ)
    (d : (D.restrictFace f hr).below BJ') :
    (belowEquiv D f hr hBJ d).1 = toCell D f hr d.1 := rfl

/-- `belowMap` is the bijection `belowEquiv` at the index of the underlying cell. -/
theorem belowMap_eq_belowEquiv (Sig : Cell (D.restrictFace f hr)) :
    belowMap D f hr Sig = belowEquiv D f hr (pushGraded_cell D f hr Sig) := rfl

/-- `belowMap` is bijective (the cell-level form of `belowMapGraded_bijective`). -/
theorem belowMap_bijective (Sig : Cell (D.restrictFace f hr)) :
    Function.Bijective (belowMap D f hr Sig) :=
  belowMapGraded_bijective D f hr (pushGraded_cell D f hr Sig)

theorem toCell_belowEquiv_symm_val (hBJ : pushGraded f BJ' = BJ) (e : D.below BJ) :
    toCell D f hr ((belowEquiv D f hr hBJ).symm e).1 = e.1 :=
  congrArg Subtype.val ((belowEquiv D f hr hBJ).apply_symm_apply e)

theorem belowEquiv_symm_mk (hBJ : pushGraded f BJ' = BJ) (c : Cell (D.restrictFace f hr))
    (hc : GradedLe (D.cell (toCell D f hr c)) BJ) :
    (belowEquiv D f hr hBJ).symm ⟨toCell D f hr c, hc⟩ =
      ⟨c, (gradedLe_cell_pushGraded_iff D f hr c).mpr (hBJ ▸ hc)⟩ :=
  (belowEquiv D f hr hBJ).symm_apply_eq.mpr rfl

/-- The bijections commute with the inclusions of lower sets. -/
theorem belowEquiv_mono {X Y : Finset (Fin m) × ℕ} (h : GradedLe X Y)
    (d : (D.restrictFace f hr).below X) :
    belowEquiv D f hr (BJ' := Y) rfl (CellScheme.below.mono h d) =
      CellScheme.below.mono ((gradedLe_pushGraded_iff f).mpr h)
        (belowEquiv D f hr (BJ' := X) rfl d) :=
  rfl

theorem belowEquiv_symm_mono {X Y : Finset (Fin m) × ℕ} (h : GradedLe X Y)
    (e : D.below (pushGraded f X)) :
    (belowEquiv D f hr (BJ' := Y) rfl).symm
        (CellScheme.below.mono ((gradedLe_pushGraded_iff f).mpr h) e) =
      CellScheme.below.mono h ((belowEquiv D f hr (BJ' := X) rfl).symm e) := by
  apply (belowEquiv D f hr (BJ' := Y) rfl).injective
  rw [Equiv.apply_symm_apply, belowEquiv_mono, Equiv.apply_symm_apply]

end CellScheme.restrictFace

section RestrictFace

open CellScheme.restrictFace

variable {m n : ℕ} {D : CellScheme (ι := Fin n) Finset.univ} {f : Fin m ↪ Fin n}
  {hr : Finset.univ.image f ∈ D.plan} {BJ' : Finset (Fin m) × ℕ} {BJ : Finset (Fin n) × ℕ}

/-- Respect of the restricted semantics `E⟨B,j⟩` transports **from `D` to the restriction**
along `belowEquiv`: if `r` on `D.below (f[B'], j)` respects `sem` there, then `r ∘ belowEquiv`
on `D'.below BJ'` respects `sem.restrictFace f hr` there.  Orderliness and locality are read
off the underlying cells (`TransformsTo.reindex` along `belowMap`); the availability witness
is pulled back through the bijection. -/
theorem RespectsSemanticsBelow.restrictFace {sem : Semantics D} (hBJ : pushGraded f BJ' = BJ)
    {r : D.below BJ → ExtOrd} (h : RespectsSemanticsBelow sem BJ r) :
    RespectsSemanticsBelow (sem.restrictFace f hr) BJ' (r ∘ belowEquiv D f hr hBJ) where
  orderly d := h.orderly (belowEquiv D f hr hBJ d)
  locality Sig := (h.locality (belowEquiv D f hr hBJ Sig)).reindex (belowMap D f hr Sig.1)
  availability Sig Xi₀ hscope hgrade := by
    have hscope' : D.scope (toCell D f hr Sig.1) ⊆ D.scope (toCell D f hr Xi₀.1) := by
      rw [← image_scope_restrictFace D f hr Sig.1, ← image_scope_restrictFace D f hr Xi₀.1]
      exact Finset.image_subset_image hscope
    obtain ⟨Xi', hcell, hle⟩ :=
      h.availability (belowEquiv D f hr hBJ Sig) (belowEquiv D f hr hBJ Xi₀) hscope' hgrade
    refine ⟨(belowEquiv D f hr hBJ).symm Xi', ?_, ?_⟩
    · rw [cell_eq, cell_eq]
      apply CellScheme.pullCell_congr
      rw [toCell_belowEquiv_symm_val]
      exact hcell
    · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hle

/-- Respect of the restricted semantics `E⟨B,j⟩` transports **from the restriction to `D`**
along `belowEquiv`: if `r'` on `D'.below BJ'` respects `sem.restrictFace f hr` there, then
`r' ∘ (belowEquiv).symm` on `D.below (f[B'], j)` respects `sem` there.  Locality at a cell
`Sig = toCell c` of `D` is locality at `c` in the restriction, reindexed along the inverse
bijection `D.below (cell (toCell c)) ≃ D'.below (cell c)`. -/
theorem RespectsSemanticsBelow.of_restrictFace {sem : Semantics D} (hBJ : pushGraded f BJ' = BJ)
    {r' : (D.restrictFace f hr).below BJ' → ExtOrd}
    (h : RespectsSemanticsBelow (sem.restrictFace f hr) BJ' r') :
    RespectsSemanticsBelow sem BJ (r' ∘ (belowEquiv D f hr hBJ).symm) where
  orderly e := by
    simpa only [Function.comp_apply, grade_restrictFace, toCell_belowEquiv_symm_val] using
      h.orderly ((belowEquiv D f hr hBJ).symm e)
  locality := by
    rintro ⟨s, hs⟩
    -- the cell `s` is visible: write it as `toCell c`
    have hvis : D.scope s ⊆ Finset.univ.image f := by
      subst hBJ
      exact hs.1.trans (Finset.image_subset_image (Finset.subset_univ _))
    obtain ⟨c, rfl⟩ := exists_toCell_eq D f hr hvis
    have hcB : GradedLe ((D.restrictFace f hr).cell c) BJ' :=
      (gradedLe_cell_pushGraded_iff D f hr c).mpr (hBJ ▸ hs)
    have hψ : (belowEquiv D f hr hBJ).symm ⟨toCell D f hr c, hs⟩ = ⟨c, hcB⟩ :=
      belowEquiv_symm_mk D f hr hBJ c hs
    -- the inverse bijection below `toCell c`
    set ψc := (belowEquiv D f hr (pushGraded_cell D f hr c)).symm with hψc
    have key := (h.locality ⟨c, hcB⟩).reindex ψc
    have h1 : ((fun d : (D.restrictFace f hr).below ((D.restrictFace f hr).cell c) =>
          (D.restrictFace f hr).grade d.1) ∘ ψc) =
        fun d : D.below (D.cell (toCell D f hr c)) => D.grade d.1 := by
      funext d
      simp only [Function.comp_apply, grade_restrictFace, hψc, toCell_belowEquiv_symm_val]
    have h2 : ((sem.restrictFace f hr).E c ∘ ψc) = sem.E (toCell D f hr c) := by
      funext d
      simp only [Function.comp_apply, Semantics.restrictFace_E, belowMap_eq_belowEquiv, hψc,
        Equiv.apply_symm_apply]
    have h3 : ((fun d => min (r' (CellScheme.below.incl ⟨c, hcB⟩ d)) (r' ⟨c, hcB⟩)) ∘ ψc) =
        fun d : D.below (D.cell (toCell D f hr c)) =>
          min ((r' ∘ (belowEquiv D f hr hBJ).symm)
              (CellScheme.below.incl ⟨toCell D f hr c, hs⟩ d))
            ((r' ∘ (belowEquiv D f hr hBJ).symm) ⟨toCell D f hr c, hs⟩) := by
      funext d
      have e1 : (belowEquiv D f hr hBJ).symm (CellScheme.below.incl ⟨toCell D f hr c, hs⟩ d) =
          CellScheme.below.incl ⟨c, hcB⟩ (ψc d) := by
        apply (belowEquiv D f hr hBJ).injective
        rw [Equiv.apply_symm_apply]
        apply Subtype.ext
        show d.1 = toCell D f hr (ψc d).1
        rw [hψc, toCell_belowEquiv_symm_val]
      show min (r' (CellScheme.below.incl ⟨c, hcB⟩ (ψc d))) (r' ⟨c, hcB⟩) =
        min (r' ((belowEquiv D f hr hBJ).symm (CellScheme.below.incl ⟨toCell D f hr c, hs⟩ d)))
          (r' ((belowEquiv D f hr hBJ).symm ⟨toCell D f hr c, hs⟩))
      rw [e1, hψ]
    rwa [h1, h2, h3] at key
  availability Sig Xi₀ hscope hgrade := by
    have hscope' : (D.restrictFace f hr).scope ((belowEquiv D f hr hBJ).symm Sig).1 ⊆
        (D.restrictFace f hr).scope ((belowEquiv D f hr hBJ).symm Xi₀).1 := by
      intro x hx
      simp only [scope_restrictFace, Finset.mem_filter, Finset.mem_univ, true_and,
        toCell_belowEquiv_symm_val] at hx ⊢
      exact hscope hx
    have hgrade' : (D.restrictFace f hr).grade ((belowEquiv D f hr hBJ).symm Sig).1 =
        (D.restrictFace f hr).grade ((belowEquiv D f hr hBJ).symm Xi₀).1 := by
      simp only [grade_restrictFace, toCell_belowEquiv_symm_val]
      exact hgrade
    obtain ⟨Xi', hcell, hle⟩ := h.availability _ _ hscope' hgrade'
    refine ⟨belowEquiv D f hr hBJ Xi', ?_, ?_⟩
    · rw [belowEquiv_apply_val, ← pushGraded_cell, hcell, pushGraded_cell,
        toCell_belowEquiv_symm_val]
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hle

end RestrictFace

/-! ### Face restriction of a domain with its associated semantics -/

namespace SemScheme

open CellScheme.restrictFace

variable {m n : ℕ}

/-- Horizontal restriction of a domain with its associated semantics to a visible face
(Knight, Prop. 2.6.3(3)/(5); Def. 3.1.5): the face restriction of the scheme with the rows
read at the underlying visible cells (`Semantics.restrictFace`).  Coding is read off the
underlying cells (grades are preserved); completeness lifts a graded pair through
`pushGraded` and `exists_toCell_eq`; consistency and bountifulness are statements about lower
sets and transport along the bijections `belowEquiv`
(`RespectsSemanticsBelow.restrictFace` / `.of_restrictFace`). -/
noncomputable def restrictFace (X : SemScheme n) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ X.scheme.plan) : SemScheme m where
  scheme := X.scheme.restrictFace f hr
  rows := X.rows.restrictFace f hr
  rows_coded Sig d := X.rows_coded (toCell X.scheme f hr Sig) (belowMap X.scheme f hr Sig d)
  consistent Sig :=
    (X.consistent (toCell X.scheme f hr Sig)).restrictFace (pushGraded_cell X.scheme f hr Sig)
  bountiful CI' BJ' hCI' hBJ' h hne p' q' γ hp' hq' hγ hagree := by
    obtain ⟨q₀, hq₀, hq₀γ, hq₀p⟩ := X.bountiful (pushGraded f CI') (pushGraded f BJ')
      ((mem_gradedPlan_restrictFace X.scheme f hr).mp hCI')
      ((mem_gradedPlan_restrictFace X.scheme f hr).mp hBJ')
      ((gradedLe_pushGraded_iff f).mpr h) (fun e => hne (pushGraded_injective f e))
      (p' ∘ (belowEquiv X.scheme f hr rfl).symm) (q' ∘ (belowEquiv X.scheme f hr rfl).symm) γ
      (hp'.of_restrictFace rfl) (hq'.of_restrictFace rfl) hγ
      (fun e => by
        rw [Function.comp_apply, Function.comp_apply, belowEquiv_symm_mono]
        exact hagree _)
    refine ⟨q₀ ∘ belowEquiv X.scheme f hr rfl, hq₀.restrictFace rfl, fun d => ?_, fun d => ?_⟩
    · rw [Function.comp_apply, hq₀γ, Function.comp_apply, Equiv.symm_apply_apply]
    · rw [Function.comp_apply, belowEquiv_mono, hq₀p, Function.comp_apply,
        Equiv.symm_apply_apply]
  complete BJ' hBJ' := by
    obtain ⟨d, hd⟩ := X.complete _ ((mem_gradedPlan_restrictFace X.scheme f hr).mp hBJ')
    have hvis : X.scheme.scope d ⊆ Finset.univ.image f := by
      change (X.scheme.cell d).1 ⊆ _
      rw [hd]
      exact Finset.image_subset_image (Finset.subset_univ _)
    obtain ⟨i, rfl⟩ := exists_toCell_eq X.scheme f hr hvis
    exact ⟨i, pushGraded_injective f ((pushGraded_cell X.scheme f hr i).trans hd)⟩

@[simp] theorem restrictFace_scheme (X : SemScheme n) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ X.scheme.plan) :
    (X.restrictFace f hr).scheme = X.scheme.restrictFace f hr := rfl

@[simp] theorem restrictFace_rows (X : SemScheme n) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ X.scheme.plan) :
    (X.restrictFace f hr).rows = X.rows.restrictFace f hr := rfl

end SemScheme

end VaughtConjecture.Knight
