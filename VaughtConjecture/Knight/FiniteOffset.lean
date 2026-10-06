/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Terminal

/-! # The finite-offset kernel: `mapCell` calculus and the row invariant (#51 (2/3))

The **unconditional kernel** of the master-spine experiment (#51; guide §5.1–5.3), split out
of `Knight/Spine.lean` so that the finished mathematics is exported from the root while the
not-yet-inhabited spine skeleton stays outside the import cone.  Everything here is a
theorem about *given* stage types under exact restriction — no spine, no scheduler, no
model-existence input.

## Contents

* **Transport of `TransformsTo` across a bijection of cells** (`TransformsTo.of_equiv`):
  Def. 2.3.9 mentions its cells only through the grade function and the two labellings, so
  the relation transports along any bijection commuting with the three.
* **The `mapCell` functor calculus**: identity and composition laws (`mapCell_refl`,
  `mapCell_trans`), injectivity, the scope equation, the lower-set bijection below an
  old-face cell (`belowCellEquiv`) and the row-reading equation (`rows_E_mapCell`) — the
  laws of `Knight/Terminal.lean`'s `mapCell` needed by any coherence bookkeeping over the
  labelled-cover order.
* **The finite offset assignment** (`FiniteOffset`, guide §5.1): a *partial* map `η` on the
  source-`⊤` cells of a stage type, sending an assigned occurrence class to the target
  value `α + (i+1)` and keeping an unassigned class **genuinely `⊤`** (`offsetLabel`,
  `offsetLabel_eq_top_iff`); the target labelling is strictly bounded at the next block
  `α + ω` (`offsetLabel_lt_or_top`), while the source type keeps its structural source-stage
  bound.  Coherent restriction (`comap`, functorial by the `mapCell` laws) and extension
  (`extend`, `extendFresh` — newly seen classes unassigned, the selected controller
  assigned) with their `comap`/`extend` compatibility laws.
* **The finite-offset row invariant** (`RowLaw`): the locality clause of Def. 2.5.4 at the
  target labelling, demanded at every source-`⊤` controller.  Proper controllers are free
  (`RowObligation.of_ne_top`); **case 1 of the three source-row cases** (old-face
  inheritance) is an *equivalence* (`rowObligation_comap_iff`); `RowLaw.of_extension`
  reduces any install to its newborn obligations.
* **The band condition and the exact residue** (`Banded`, `offsetLabel_orderly`,
  `RowLaw.rowObligation_all`): with the row law and the band condition the target labelling
  satisfies orderliness and locality — `RespectsSemantics` **minus availability**
  (Def. 2.5.4(2)), which is therefore the single missing property for `offsetLabel` to be a
  genuine stage-`(α + ω)` labelling; that availability residue is the provisional-band /
  companion mathematics of #51's remaining boundaries.  No `SelectiveRowSupply` or
  unrestricted-semantics premise appears anywhere: the source rows are fields of
  `SemScheme`, consumed through `p.respects` alone.

The consumer experiment — spine states, the two install constructors, the preservation
lemmas along the idle/install trace, and the open producer obligations — is
`Knight/Spine.lean` (not root-exported; see its docstring for the honest status). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd
open CellScheme.restrictFace (toCell belowMap toCell_strictMono toCell_injective
  exists_toCell_eq scope_toCell_subset image_scope_restrictFace gradedLe_restrictFace_iff
  toCell_cast_eq_of_emb)

universe w

/-! ### Transport of `TransformsTo` across a bijection of cells

The transformation relation of Def. 2.3.9 mentions its family of cells only through the grade
function and the two labellings, so it transports across any bijection commuting with the
three.  This is the reindexing engine of the row-invariant transports below (the `reindex` of
`Knight/Transform.lean` is the one-sided pullback special case). -/

namespace Transform

theorem TransformsTo.of_equiv {D D' : Type*} {grade : D → ℕ} {grade' : D' → ℕ}
    {p q : D → ExtOrd} {p' q' : D' → ExtOrd} (e : D' ≃ D)
    (hg : ∀ d, grade (e d) = grade' d) (hp : ∀ d, p (e d) = p' d)
    (hq : ∀ d, q (e d) = q' d) (h : TransformsTo grade' p' q') : TransformsTo grade p q := by
  obtain ⟨g, σ, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨g, σ, h1, h2, h3, h4, h5, fun d => ?_⟩
  have h6' := h6 (e.symm d)
  rw [← hq (e.symm d), ← hp (e.symm d), ← hg (e.symm d), e.apply_symm_apply] at h6'
  exact h6'

end Transform

/-! ### The `mapCell` calculus

`Knight/Terminal.lean` introduces `mapCell h : Cell p → Cell q` for an exact restriction
`h : typeMap f q = some p` (with `label_mapCell`, `grade_mapCell`).  The spine's coherence
bookkeeping needs its functor laws (`mapCell_refl`, `mapCell_trans`), its injectivity, its
scope equation, and the induced bijection of the lower sets below a cell together with the
row-reading equation — all proved by the substitution pattern of `label_mapCell` (replace `p`
by the literal face restriction; `mapCell` is then definitionally `toCell`). -/

namespace StageType

variable {α : Ordinal.{0}} {k m n : ℕ}

/-- `mapCell` is injective (`toCell` is an order embedding and the cell transport is a
`Fin.cast`). -/
theorem mapCell_injective {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) : Function.Injective (mapCell h) := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some h, restrictFace_eq_of_typeMap_eq_some h⟩
  intro a b hab
  have := toCell_injective q.scheme.scheme f (visible_of_typeMap_eq_some h) hab
  exact Fin.ext (congrArg Fin.val this)

/-- The scope of the underlying cell is the `f`-image of the scope of the restricted cell. -/
theorem scope_mapCell {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (d : Cell p.scheme.scheme) :
    q.scheme.scheme.scope (mapCell h d) = (p.scheme.scheme.scope d).image f := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some h, restrictFace_eq_of_typeMap_eq_some h⟩
  exact (image_scope_restrictFace q.scheme.scheme f hr d).symm

/-- The graded preorder below the image of the face is that of the face: `mapCell` preserves
and reflects `GradedLe` of cell contents. -/
theorem gradedLe_mapCell_iff {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) {a b : Cell p.scheme.scheme} :
    GradedLe (q.scheme.scheme.cell (mapCell h a)) (q.scheme.scheme.cell (mapCell h b)) ↔
      GradedLe (p.scheme.scheme.cell a) (p.scheme.scheme.cell b) := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some h, restrictFace_eq_of_typeMap_eq_some h⟩
  exact (gradedLe_restrictFace_iff q.scheme.scheme f hr).symm

/-- **Identity law**: the cell map of the identity restriction is the identity. -/
theorem mapCell_refl {p : S α n}
    (h : typeMap (Function.Embedding.refl (Fin n)) p = some p) (d : Cell p.scheme.scheme) :
    mapCell h d = d := by
  have hvis := visible_of_typeMap_eq_some h
  have hcard : (p.scheme.scheme.restrictFace (Function.Embedding.refl (Fin n)) hvis).card
      = p.scheme.scheme.card :=
    congrArg (fun w : S α n => w.scheme.scheme.card) (restrictFace_eq_of_typeMap_eq_some h)
  have hvis_e : ∀ c : Fin p.scheme.scheme.card, p.scheme.scheme.scope (id c) ⊆
      Finset.univ.image (Function.Embedding.refl (Fin n)) := by
    intro c
    have : Finset.univ.image (Function.Embedding.refl (Fin n)) =
        (Finset.univ : Finset (Fin n)) := by
      simp [Function.Embedding.coe_refl]
    rw [this]
    exact Finset.subset_univ _
  have key := toCell_cast_eq_of_emb p.scheme.scheme (Function.Embedding.refl (Fin n)) hvis
    strictMono_id hvis_e hcard d
  calc mapCell h d
      = toCell p.scheme.scheme (Function.Embedding.refl (Fin n)) hvis
          (Fin.cast hcard.symm d) := by
        unfold mapCell
        congr 1
    _ = d := key

/-- **Composition law**: the cell map of a composite restriction is the composite of the cell
maps (the two strictly monotone enumerations of the `f.trans g`-visible cells agree). -/
theorem mapCell_trans {z : S α n} {y : S α m} {x : S α k} {g : Fin m ↪ Fin n}
    {f : Fin k ↪ Fin m} (hzy : typeMap g z = some y) (hyx : typeMap f y = some x)
    (hzx : typeMap (f.trans g) z = some x) (d : Cell x.scheme.scheme) :
    mapCell hzx d = mapCell hzy (mapCell hyx d) := by
  obtain ⟨hg, rfl⟩ : ∃ hr, z.restrictFace g hr = y :=
    ⟨visible_of_typeMap_eq_some hzy, restrictFace_eq_of_typeMap_eq_some hzy⟩
  obtain ⟨hf, rfl⟩ : ∃ hr, (z.restrictFace g hg).restrictFace f hr = x :=
    ⟨visible_of_typeMap_eq_some hyx, restrictFace_eq_of_typeMap_eq_some hyx⟩
  set D := z.scheme.scheme with hD
  have hvis : Finset.univ.image (f.trans g) ∈ D.plan := visible_of_typeMap_eq_some hzx
  set e : Fin ((D.restrictFace g hg).restrictFace f hf).card → Cell D :=
    fun c => toCell D g hg (toCell (D.restrictFace g hg) f hf c) with he_def
  have he : StrictMono e :=
    (toCell_strictMono D g hg).comp (toCell_strictMono (D.restrictFace g hg) f hf)
  have hvis_e : ∀ c, D.scope (e c) ⊆ Finset.univ.image (f.trans g) := by
    intro c
    have h1 : ((D.restrictFace g hg).scope (toCell (D.restrictFace g hg) f hf c)).image g
        = D.scope (e c) :=
      image_scope_restrictFace D g hg _
    rw [← h1]
    have h2 : (D.restrictFace g hg).scope (toCell (D.restrictFace g hg) f hf c) ⊆
        Finset.univ.image f :=
      scope_toCell_subset (D.restrictFace g hg) f hf _
    calc ((D.restrictFace g hg).scope (toCell (D.restrictFace g hg) f hf c)).image g
        ⊆ (Finset.univ.image f).image g := Finset.image_subset_image h2
      _ = Finset.univ.image (f.trans g) := by
          rw [Finset.image_image]; rfl
  have hcard : (D.restrictFace (f.trans g) hvis).card
      = ((D.restrictFace g hg).restrictFace f hf).card :=
    congrArg (fun w : S α k => w.scheme.scheme.card) (restrictFace_eq_of_typeMap_eq_some hzx)
  have key := toCell_cast_eq_of_emb D (f.trans g) hvis he hvis_e hcard d
  calc mapCell hzx d
      = toCell D (f.trans g) hvis (Fin.cast hcard.symm d) := by
        unfold mapCell
        congr 1
    _ = e d := key
    _ = mapCell hzy (mapCell hyx d) := rfl

/-- The transport of the lower set below a face cell `Ξ` into the lower set below its
underlying cell `mapCell h Ξ` (the `mapCell` form of `belowMap`). -/
noncomputable def belowMapCell {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (Xi : Cell p.scheme.scheme)
    (x : p.scheme.scheme.below (p.scheme.scheme.cell Xi)) :
    q.scheme.scheme.below (q.scheme.scheme.cell (mapCell h Xi)) :=
  ⟨mapCell h x.1, (gradedLe_mapCell_iff h).mpr x.2⟩

@[simp] theorem belowMapCell_val {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (Xi : Cell p.scheme.scheme)
    (x : p.scheme.scheme.below (p.scheme.scheme.cell Xi)) :
    (belowMapCell h Xi x).1 = mapCell h x.1 := rfl

/-- `belowMapCell` is a bijection: the cells of `q` below an old-face cell all lie inside the
face (their scopes are contained in the image of `f`), so they are themselves old-face cells,
below the restricted cell.  This is what makes case 1 of the three source-row cases (old-face
inheritance) an equivalence rather than a one-sided transport. -/
theorem belowMapCell_bijective {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (Xi : Cell p.scheme.scheme) :
    Function.Bijective (belowMapCell h Xi) := by
  constructor
  · intro a b hab
    have hval := congrArg Subtype.val hab
    rw [belowMapCell_val, belowMapCell_val] at hval
    exact Subtype.ext (mapCell_injective h hval)
  · obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
      ⟨visible_of_typeMap_eq_some h, restrictFace_eq_of_typeMap_eq_some h⟩
    rintro ⟨d, hd⟩
    have hdvis : q.scheme.scheme.scope d ⊆ Finset.univ.image f :=
      hd.1.trans (scope_toCell_subset q.scheme.scheme f hr Xi)
    obtain ⟨i, rfl⟩ := exists_toCell_eq q.scheme.scheme f hr hdvis
    have hle : GradedLe ((q.scheme.scheme.restrictFace f hr).cell i)
        ((q.scheme.scheme.restrictFace f hr).cell Xi) :=
      (gradedLe_restrictFace_iff q.scheme.scheme f hr).mpr hd
    exact ⟨⟨i, hle⟩, rfl⟩

/-- The lower-set bijection below an old-face cell. -/
noncomputable def belowCellEquiv {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (Xi : Cell p.scheme.scheme) :
    p.scheme.scheme.below (p.scheme.scheme.cell Xi) ≃
      q.scheme.scheme.below (q.scheme.scheme.cell (mapCell h Xi)) :=
  Equiv.ofBijective _ (belowMapCell_bijective h Xi)

@[simp] theorem belowCellEquiv_apply {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (Xi : Cell p.scheme.scheme)
    (x : p.scheme.scheme.below (p.scheme.scheme.cell Xi)) :
    belowCellEquiv h Xi x = belowMapCell h Xi x := rfl

/-- **The rows of an exact restriction are read at the underlying cells**: the semantic row of
an old-face cell, transported below, is the row of the restricted cell (Def. 3.1.5, the
`mapCell` form of `restrictFace_rows_E`). -/
theorem rows_E_mapCell {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (Xi : Cell p.scheme.scheme)
    (x : p.scheme.scheme.below (p.scheme.scheme.cell Xi)) :
    q.scheme.rows.E (mapCell h Xi) (belowMapCell h Xi x) = p.scheme.rows.E Xi x := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some h, restrictFace_eq_of_typeMap_eq_some h⟩
  rfl

/-- No old-face cell is full-scope in the extension when the face misses a coordinate
(the case `f = ι_{n,n+1}`): the two newborn controllers of a fresh install are automatically
outside the old face. -/
theorem mapCell_ne_of_scope_univ {q : S α (n + 1)} {p : S α n}
    (h : typeMap (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) q = some p)
    {Xi : Cell q.scheme.scheme} (hXi : q.scheme.scheme.scope Xi = Finset.univ)
    (d : Cell p.scheme.scheme) : mapCell h d ≠ Xi := by
  intro he
  have hscope := scope_mapCell h d
  rw [he, hXi] at hscope
  have hlast : Fin.last n ∈ (p.scheme.scheme.scope d).image Fin.castSuccEmb := by
    rw [← hscope]; exact Finset.mem_univ _
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hlast
  exact absurd hi (Fin.ne_last_of_lt (Fin.castSucc_lt_last i))

end StageType

/-! ### The finite offset assignment `η` (guide §5.1)

One block step over a source type `p ∈ S^α_n` retains a **partial** offset assignment on the
source-`⊤` cells: `η(c) = i` means the occurrence class of `c` is to receive the proper value
`α + (i+1)` at the next block, while an **undefined** `η(c)` means the class remains genuinely
`⊤` — the distinction between "undefined" and "offset `0`" is essential (`α + 1` versus `⊤`).
Proper source values are never touched.  The induced **target labelling** is `offsetLabel`;
its stage bound at `α + ω` is `offsetLabel_lt_or_top`.

The assignment is spine-private data: the public projections read only the induced labelling
and the row facts, never `η` itself. -/

open StageType

variable {α : Ordinal.{0}} {k m n : ℕ}

/-- A **finite offset assignment** on a source type `p : S α n`: a partial assignment of
finite offsets to cells, defined only on source-`⊤` cells (`top_of_assigned`).  `η c = none`
means the occurrence class of `c` keeps its source value (in particular a `⊤` cell remains
genuinely `⊤`). -/
structure FiniteOffset (p : S α n) : Type where
  /-- The partial offset: `some i` sends a source-`⊤` cell to `α + (i+1)`; `none` keeps the
  source value. -/
  η : Cell p.scheme.scheme → Option ℕ
  /-- Offsets are assigned only to source-`⊤` cells. -/
  top_of_assigned : ∀ c i, η c = some i → p.label c = ⊤

namespace FiniteOffset

variable {p : S α n}

theorem ext {ν₁ ν₂ : FiniteOffset p} (h : ∀ c, ν₁.η c = ν₂.η c) : ν₁ = ν₂ := by
  obtain ⟨η₁, h₁⟩ := ν₁
  obtain ⟨η₂, h₂⟩ := ν₂
  have : η₁ = η₂ := funext h
  subst this
  rfl

/-- The empty assignment: every class keeps its source value. -/
def empty (p : S α n) : FiniteOffset p where
  η _ := none
  top_of_assigned _ _ h := nomatch h

@[simp] theorem empty_η (c : Cell p.scheme.scheme) : (empty p).η c = none := rfl

/-- The **target labelling** induced by an offset assignment: proper source values are kept,
an assigned `⊤` class receives `α + (i+1)`, an unassigned class keeps its source value — in
particular an unassigned `⊤` class remains genuinely `⊤`. -/
def offsetLabel (ν : FiniteOffset p) (c : Cell p.scheme.scheme) : ExtOrd :=
  (ν.η c).elim (p.label c) fun i => ofOrd (α + (i + 1 : ℕ))

theorem offsetLabel_of_unassigned {ν : FiniteOffset p} {c : Cell p.scheme.scheme}
    (h : ν.η c = none) : ν.offsetLabel c = p.label c := by
  unfold offsetLabel
  rw [h, Option.elim_none]

theorem offsetLabel_of_assigned {ν : FiniteOffset p} {c : Cell p.scheme.scheme} {i : ℕ}
    (h : ν.η c = some i) : ν.offsetLabel c = ofOrd (α + (i + 1 : ℕ)) := by
  unfold offsetLabel
  rw [h, Option.elim_some]

/-- A cell that is not source-`⊤` is unassigned. -/
theorem η_eq_none_of_ne_top {ν : FiniteOffset p} {c : Cell p.scheme.scheme}
    (hc : p.label c ≠ ⊤) : ν.η c = none := by
  cases hη : ν.η c with
  | none => rfl
  | some i => exact absurd (ν.top_of_assigned c i hη) hc

/-- Proper source values are kept by the target labelling. -/
theorem offsetLabel_of_ne_top {ν : FiniteOffset p} {c : Cell p.scheme.scheme}
    (hc : p.label c ≠ ⊤) : ν.offsetLabel c = p.label c :=
  offsetLabel_of_unassigned (η_eq_none_of_ne_top hc)

/-- **Undefined = genuinely `⊤`**: the target labelling is `⊤` exactly on the unassigned
source-`⊤` classes. -/
theorem offsetLabel_eq_top_iff {ν : FiniteOffset p} {c : Cell p.scheme.scheme} :
    ν.offsetLabel c = ⊤ ↔ p.label c = ⊤ ∧ ν.η c = none := by
  cases hη : ν.η c with
  | none => simp [offsetLabel_of_unassigned hη]
  | some i =>
    simp only [offsetLabel_of_assigned hη]
    exact iff_of_false (ofOrd_ne_top _) (by simp)

/-- **The stage bound at the next block**: the target labelling is strictly bounded at
`α + ω` (or `⊤`) — a stage-`(α+ω)` labelling, never a weakened source-stage one.  (The
above-source values `α + (i+1)` live only here, at the target stage; the source type `p`
itself keeps its strict source-stage bound.) -/
theorem offsetLabel_lt_or_top (ν : FiniteOffset p) (c : Cell p.scheme.scheme) :
    ν.offsetLabel c < ofOrd (α + Ordinal.omega0) ∨ ν.offsetLabel c = ⊤ := by
  cases hη : ν.η c with
  | none =>
    rw [offsetLabel_of_unassigned hη]
    rcases p.label_bound c with hlt | htop
    · exact Or.inl (lt_of_lt_of_le hlt
        (ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right (zero_le : (0 : Ordinal.{0}) ≤ _))))
    · exact Or.inr htop
  | some i =>
    rw [offsetLabel_of_assigned hη]
    refine Or.inl (ofOrd_lt_ofOrd.mpr ?_)
    rw [add_lt_add_iff_left]
    exact Ordinal.natCast_lt_omega0 _

/-! ### Coherent restriction and extension of offset assignments

Along an exact restriction `typeMap f q = some p` the offsets transport by reading `η` at the
underlying cells (`comap`); the laws `comap_refl`/`comap_comap` make the transport functorial
(the `mapCell` calculus above).  In the other direction, `extend` prolongs an assignment to a
larger type with every **newly seen class unassigned** — "a class introduced without a finite
offset is thereafter kept unassigned" — and `comap_extend` says the old classes keep their
offsets: this is the *genuinely coherent types* discipline of the spine order. -/

/-- Restriction of an offset assignment to an exact face: read `η` at the underlying cells. -/
noncomputable def comap {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (ν : FiniteOffset q) : FiniteOffset p where
  η d := ν.η (mapCell h d)
  top_of_assigned d i hi := by
    have htop := ν.top_of_assigned _ i hi
    rwa [label_mapCell h d] at htop

@[simp] theorem comap_η {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (ν : FiniteOffset q) (d : Cell p.scheme.scheme) :
    (ν.comap h).η d = ν.η (mapCell h d) := rfl

/-- The target labelling commutes with coherent restriction. -/
theorem offsetLabel_comap {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (ν : FiniteOffset q) (d : Cell p.scheme.scheme) :
    (ν.comap h).offsetLabel d = ν.offsetLabel (mapCell h d) := by
  cases hη : ν.η (mapCell h d) with
  | none =>
    have hc : (ν.comap h).η d = none := hη
    rw [offsetLabel_of_unassigned hc, offsetLabel_of_unassigned hη, label_mapCell h d]
  | some i =>
    have hc : (ν.comap h).η d = some i := hη
    rw [offsetLabel_of_assigned hc, offsetLabel_of_assigned hη]

theorem comap_refl {ν : FiniteOffset p}
    (h : typeMap (Function.Embedding.refl (Fin n)) p = some p) : ν.comap h = ν :=
  ext fun d => by rw [comap_η, mapCell_refl h d]

theorem comap_comap {z : S α n} {y : S α m} {x : S α k} {g : Fin m ↪ Fin n} {f : Fin k ↪ Fin m}
    (hzy : typeMap g z = some y) (hyx : typeMap f y = some x)
    (hzx : typeMap (f.trans g) z = some x) (ν : FiniteOffset z) :
    (ν.comap hzy).comap hyx = ν.comap hzx :=
  ext fun d => by rw [comap_η, comap_η, comap_η, mapCell_trans hzy hyx hzx d]

open Classical in
/-- Extension of an offset assignment along an exact extension: old classes keep their
offsets, **newly seen classes are unassigned**. -/
noncomputable def extend {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (ν : FiniteOffset p) : FiniteOffset q where
  η Xi := if hd : ∃ d, mapCell h d = Xi then ν.η hd.choose else none
  top_of_assigned Xi i hi := by
    by_cases hd : ∃ d, mapCell h d = Xi
    · rw [dite_eq_left hd] at hi
      have htop := ν.top_of_assigned _ i hi
      rw [← hd.choose_spec, label_mapCell]
      exact htop
    · rw [dite_eq_right hd] at hi
      simp at hi

theorem extend_η_of_eq {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (ν : FiniteOffset p) {Xi : Cell q.scheme.scheme}
    {d : Cell p.scheme.scheme} (hd : mapCell h d = Xi) : (ν.extend h).η Xi = ν.η d := by
  have hex : ∃ d', mapCell h d' = Xi := ⟨d, hd⟩
  change (if hd' : ∃ d', mapCell h d' = Xi then ν.η hd'.choose else none) = ν.η d
  rw [dite_eq_left hex]
  exact congrArg ν.η (mapCell_injective h (hex.choose_spec.trans hd.symm))

theorem extend_η_of_notMem {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (ν : FiniteOffset p) {Xi : Cell q.scheme.scheme}
    (hd : ¬ ∃ d, mapCell h d = Xi) : (ν.extend h).η Xi = none := by
  change (if hd' : ∃ d', mapCell h d' = Xi then ν.η hd'.choose else none) = none
  rw [dite_eq_right hd]

/-- Old classes keep their offsets across an extension. -/
theorem comap_extend {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (ν : FiniteOffset p) : (ν.extend h).comap h = ν :=
  ext fun d => by rw [comap_η, extend_η_of_eq h ν rfl]

theorem extend_empty {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) : (empty p).extend h = empty q :=
  ext fun Xi => by
    by_cases hd : ∃ d, mapCell h d = Xi
    · obtain ⟨d, hd⟩ := hd
      rw [extend_η_of_eq h _ hd, empty_η, empty_η]
    · rw [extend_η_of_notMem h _ hd, empty_η]

/-- The fresh-install extension of an offset assignment across a coface (`f = ι_{n,n+1}`):
old classes keep their offsets, the **selected controller** `σ` receives the requested offset
`k`, and every other new class — the **companion** included — is unassigned. -/
noncomputable def extendFresh {q : S α (n + 1)} {p : S α n}
    (h : typeMap (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) q = some p) (ν : FiniteOffset p)
    (σ : Cell q.scheme.scheme) (hσ : q.label σ = ⊤) (k : ℕ) : FiniteOffset q where
  η Xi := if Xi = σ then some k else (ν.extend h).η Xi
  top_of_assigned Xi i hi := by
    by_cases hXi : Xi = σ
    · rw [hXi]; exact hσ
    · rw [ite_eq_right hXi] at hi
      exact (ν.extend h).top_of_assigned Xi i hi

theorem extendFresh_η_selected {q : S α (n + 1)} {p : S α n}
    (h : typeMap (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) q = some p) (ν : FiniteOffset p)
    (σ : Cell q.scheme.scheme) (hσ : q.label σ = ⊤) (k : ℕ) :
    (ν.extendFresh h σ hσ k).η σ = some k := ite_eq_left rfl

theorem extendFresh_η_of_ne {q : S α (n + 1)} {p : S α n}
    (h : typeMap (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) q = some p) (ν : FiniteOffset p)
    (σ : Cell q.scheme.scheme) (hσ : q.label σ = ⊤) (k : ℕ) {Xi : Cell q.scheme.scheme}
    (hXi : Xi ≠ σ) : (ν.extendFresh h σ hσ k).η Xi = (ν.extend h).η Xi := ite_eq_right hXi

/-- Old classes keep their offsets across a fresh install: the selected controller is
full-support, hence never an old-face cell. -/
theorem comap_extendFresh {q : S α (n + 1)} {p : S α n}
    (h : typeMap (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) q = some p) (ν : FiniteOffset p)
    {σ : Cell q.scheme.scheme} (hσfull : q.scheme.scheme.scope σ = Finset.univ)
    (hσ : q.label σ = ⊤) (k : ℕ) : (ν.extendFresh h σ hσ k).comap h = ν :=
  ext fun d => by
    rw [comap_η, extendFresh_η_of_ne h ν σ hσ k (mapCell_ne_of_scope_univ h hσfull d),
      extend_η_of_eq h ν rfl]

end FiniteOffset

/-! ### The finite-offset row invariant (guide §5.2–5.3; the spine's private invariant)

The **row obligation** at a controlling cell `Ξ` is the locality clause of Def. 2.5.4 read at
the *target* labelling: the source semantic row of `Ξ` transforms (Def. 2.3.9) to the target
labelling of the cells below `Ξ`, capped at the target value of `Ξ`.  The **row law** demands
it at every source-`⊤` controller.  Proper-valued controllers are easier and are discharged
unconditionally (`RowObligation.of_ne_top`): a proper cap does not see the new band, so their
source locality witnesses are inherited verbatim — hence the row law at source-`⊤`
controllers is exactly the locality clause of "`offsetLabel` respects the source rows".

Three transports drive the bounded row induction:

* `RowObligation.of_ne_top` — proper controllers, free;
* `rowObligation_comap_iff` — **case 1 of the three source-row cases** (old-face
  inheritance): below an old-face cell the extension and the face have the *same* cells,
  rows, and target values (`belowCellEquiv`, `rows_E_mapCell`, `offsetLabel_comap`), so the
  obligation transports both ways;
* `RowLaw.of_extension` — the install-step engine: to extend the row law across an exact
  extension only the **newborn** obligations are owed; old-face controllers inherit theirs.

What is **not** proved here — deliberately: the newborn obligations themselves.  For a fresh
install they are the selected/companion witnesses (cases 2 and 3 of the three source-row
cases), consumed as data of the install; for a source-cover install they are the
Lemma-5.3.7-shaped facts about provisional values on larger covers (#51's remaining
boundaries).  `RowObligation.of_unassigned` discharges them in the offset-free situation
(newly absorbed source regions with no assigned class in sight), which is also the base of
the induction (`rowLaw_empty`) and the post-limit restart. -/

namespace FiniteOffset

variable {p : S α n}

/-- The **row obligation** at a controlling cell `Ξ`: the source semantic row of `Ξ`
transforms (Def. 2.3.9) to the target labelling below `Ξ`, capped at the target value of `Ξ`
(the locality clause of Def. 2.5.4 at the target labelling). -/
def RowObligation (ν : FiniteOffset p) (Xi : Cell p.scheme.scheme) : Prop :=
  Transform.TransformsTo
    (fun d : p.scheme.scheme.below (p.scheme.scheme.cell Xi) => p.scheme.scheme.grade d.1)
    (p.scheme.rows.E Xi)
    (fun d => min (ν.offsetLabel d.1) (ν.offsetLabel Xi))

/-- The **finite-offset row invariant**: the row obligation at every source-`⊤` controller
(the row law of guide §5.2; proper controllers are free, `RowObligation.of_ne_top`). -/
def RowLaw (ν : FiniteOffset p) : Prop :=
  ∀ Xi : Cell p.scheme.scheme, p.label Xi = ⊤ → ν.RowObligation Xi

/-- An obligation whose target agrees pointwise with the source target is the source locality
clause. -/
theorem RowObligation.of_target_eq {ν : FiniteOffset p} {Xi : Cell p.scheme.scheme}
    (hmin : ∀ d : p.scheme.scheme.below (p.scheme.scheme.cell Xi),
      min (ν.offsetLabel d.1) (ν.offsetLabel Xi) = min (p.label d.1) (p.label Xi)) :
    ν.RowObligation Xi :=
  Transform.TransformsTo.of_equiv (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) hmin
    (p.respects.locality Xi)

/-- **Proper controllers are free**: at a controller with a proper source value, the target
cap does not see the new band (assigned cells sit at or above `α`, strictly above every
proper cap), so the source locality witness discharges the obligation unconditionally. -/
theorem RowObligation.of_ne_top {ν : FiniteOffset p} {Xi : Cell p.scheme.scheme}
    (hXi : p.label Xi ≠ ⊤) : ν.RowObligation Xi := by
  refine of_target_eq fun d => ?_
  rw [offsetLabel_of_ne_top hXi]
  cases hd : ν.η d.1 with
  | none => rw [offsetLabel_of_unassigned hd]
  | some i =>
    have hdtop : p.label d.1 = ⊤ := ν.top_of_assigned _ i hd
    rw [offsetLabel_of_assigned hd, hdtop]
    have h1 : p.label Xi ≤ ofOrd (α + (i + 1 : ℕ)) := by
      rcases p.label_bound Xi with hlt | htop
      · exact le_of_lt (lt_of_lt_of_le hlt
          (ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right (zero_le : (0 : Ordinal.{0}) ≤ _))))
      · exact absurd htop hXi
    rw [min_eq_right h1, min_eq_right le_top]

/-- An obligation is free when the controller and every cell below it are unassigned: the
target labelling agrees with the source there, and source locality applies. -/
theorem RowObligation.of_unassigned {ν : FiniteOffset p} {Xi : Cell p.scheme.scheme}
    (hXi : ν.η Xi = none)
    (hb : ∀ d : p.scheme.scheme.below (p.scheme.scheme.cell Xi), ν.η d.1 = none) :
    ν.RowObligation Xi :=
  of_target_eq fun d => by
    rw [offsetLabel_of_unassigned hXi, offsetLabel_of_unassigned (hb d)]

/-- The row law of a wholly unassigned assignment (the base of the bounded row induction, and
the post-limit restart: at a new block base the invariant re-initializes from the model data
alone). -/
theorem RowLaw.of_forall_none {ν : FiniteOffset p} (h : ∀ c, ν.η c = none) : ν.RowLaw :=
  fun Xi _ => RowObligation.of_unassigned (h Xi) fun d => h d.1

/-- The empty assignment satisfies the row law. -/
theorem rowLaw_empty : (empty p).RowLaw :=
  RowLaw.of_forall_none fun _ => rfl

/-! #### Case 1: old-face inheritance across an exact restriction -/

/-- **Case 1 of the three source-row cases, as an equivalence**: below an old-face cell the
extension and the face carry the same cells, the same semantic rows, and — under coherent
offsets — the same target values, so the row obligation holds in the extension at
`mapCell h d` iff it holds on the face at `d`. -/
theorem rowObligation_comap_iff {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (ν : FiniteOffset q) (d : Cell p.scheme.scheme) :
    (ν.comap h).RowObligation d ↔ ν.RowObligation (mapCell h d) := by
  constructor
  · intro hob
    refine Transform.TransformsTo.of_equiv (belowCellEquiv h d) ?_ ?_ ?_ hob
    · intro x
      exact grade_mapCell h x.1
    · intro x
      exact rows_E_mapCell h d x
    · intro x
      rw [offsetLabel_comap h ν x.1, offsetLabel_comap h ν d]
      rfl
  · intro hob
    refine Transform.TransformsTo.of_equiv (belowCellEquiv h d).symm ?_ ?_ ?_ hob
    all_goals intro y
    all_goals
      have h1 : (belowMapCell h d ((belowCellEquiv h d).symm y)).1 = y.1 :=
        congrArg Subtype.val ((belowCellEquiv h d).apply_symm_apply y)
    · rw [belowMapCell_val] at h1
      rw [← h1, grade_mapCell]
    · have h2 := rows_E_mapCell h d ((belowCellEquiv h d).symm y)
      rw [show belowMapCell h d ((belowCellEquiv h d).symm y) = y from
        (belowCellEquiv h d).apply_symm_apply y] at h2
      exact h2.symm
    · rw [belowMapCell_val] at h1
      rw [offsetLabel_comap h ν ((belowCellEquiv h d).symm y).1, offsetLabel_comap h ν d, h1]

/-- The row law restricts to every exact face under coherent offsets (the "visible
restriction preserves it" clause of the bounded row induction). -/
theorem RowLaw.comap {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) {ν : FiniteOffset q} (hlaw : ν.RowLaw) :
    (ν.comap h).RowLaw := fun d hd =>
  (rowObligation_comap_iff h ν d).mpr
    (hlaw (mapCell h d) (by rw [label_mapCell h d]; exact hd))

/-- **The install-step engine of the bounded row induction**: to extend the row law across an
exact extension, only the newborn obligations are owed — every old-face controller inherits
its obligation from the face (case 1). -/
theorem RowLaw.of_extension {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) {ν : FiniteOffset q} (hface : (ν.comap h).RowLaw)
    (hnew : ∀ Xi : Cell q.scheme.scheme, q.label Xi = ⊤ → (¬ ∃ d, mapCell h d = Xi) →
      ν.RowObligation Xi) :
    ν.RowLaw := by
  intro Xi hXi
  by_cases hd : ∃ d, mapCell h d = Xi
  · obtain ⟨d, rfl⟩ := hd
    have hpd : p.label d = ⊤ := by rw [← label_mapCell h d]; exact hXi
    exact (rowObligation_comap_iff h ν d).mp (hface d hpd)
  · exact hnew Xi hXi hd

/-! #### The band condition and the exact residue

Orderliness (Def. 2.3.4) of the target labelling is not free: an assigned cell of grade `K`
receives `α + (i+1)`, whose finite part is `i+1`, and self-visibility at `K` demands
`K ≤ i+1`.  This is the **band condition** `Banded` — the finite offsets are tied to the
grades, which is why the paper's newborn controllers are *grade-one* (any offset serves
grade `1`).  Both transports preserve it.

With the row law and the band condition in hand, the target labelling satisfies
**orderliness** (`offsetLabel_orderly`) and **locality at every controller**
(`RowLaw.rowObligation_all` — proper controllers free, source-`⊤` controllers by the law).
These are two of the three clauses of `RespectsSemantics`: the single missing property for
`offsetLabel` to be a genuine stage-`(α+ω)` labelling is **availability** (Def. 2.5.4(2)) —
an unassigned `⊤` cell must be dominated at every larger scope of its grade, which the
assignment can break by lowering the dominating cell to a band value.  That availability
residue is exactly the provisional-band/companion mathematics of the remaining #51
boundaries (the companion controller exists to supply the dominating literal top cell), and
no analogue of an "unrestricted source semantics" premise appears anywhere: the source rows
are fields of `SemScheme`, consumed through `p.respects` alone. -/

/-- The **band condition**: an assigned cell's grade is at most its offset plus one — the
grade/offset compatibility that makes the target labelling orderly (`offsetLabel_orderly`).
Grade-one controllers satisfy it for every offset. -/
def Banded (ν : FiniteOffset p) : Prop :=
  ∀ c i, ν.η c = some i → p.scheme.scheme.grade c ≤ i + 1

theorem banded_empty : (empty p).Banded := fun _ _ h => nomatch h

theorem Banded.comap {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) {ν : FiniteOffset q} (hb : ν.Banded) : (ν.comap h).Banded := by
  intro d i hi
  have := hb (mapCell h d) i hi
  rwa [grade_mapCell h d] at this

theorem Banded.extend {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) {ν : FiniteOffset p} (hb : ν.Banded) : (ν.extend h).Banded := by
  intro Xi i hi
  by_cases hd : ∃ d, mapCell h d = Xi
  · obtain ⟨d, rfl⟩ := hd
    rw [extend_η_of_eq h ν rfl] at hi
    rw [grade_mapCell h d]
    exact hb d i hi
  · rw [extend_η_of_notMem h ν hd] at hi
    simp at hi

theorem Banded.extendFresh {q : S α (n + 1)} {p : S α n}
    (h : typeMap (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) q = some p) {ν : FiniteOffset p}
    (hb : ν.Banded) {σ : Cell q.scheme.scheme} (hσ : q.label σ = ⊤) (k : ℕ)
    (hσg : q.scheme.scheme.grade σ ≤ k + 1) : (ν.extendFresh h σ hσ k).Banded := by
  intro Xi i hi
  by_cases hXi : Xi = σ
  · rw [hXi, extendFresh_η_selected h ν σ hσ k] at hi
    obtain rfl : k = i := Option.some_inj.mp hi
    rw [hXi]
    exact hσg
  · rw [extendFresh_η_of_ne h ν σ hσ k hXi] at hi
    exact Banded.extend h hb Xi i hi

/-- **Orderliness of the target labelling** (Def. 2.3.4), from the band condition: unassigned
cells inherit the source's orderliness; an assigned cell's value `α + (i+1)` has finite part
`i+1 ≥` its grade, so self-visibility does not trigger. -/
theorem offsetLabel_orderly (hα : Order.IsSuccLimit α) {ν : FiniteOffset p}
    (hb : ν.Banded) : Transform.IsOrderly p.scheme.scheme.grade ν.offsetLabel := by
  intro c
  cases hη : ν.η c with
  | none =>
    rw [offsetLabel_of_unassigned hη]
    exact p.respects.orderly c
  | some i =>
    rw [offsetLabel_of_assigned hη]
    have hl : limitPart α = α :=
      le_antisymm (limitPart_le α) (succLimit_le_limitPart hα le_rfl)
    have hfp : finitePart (α + (i + 1 : ℕ)) = i + 1 := by
      conv_lhs => rw [← hl]
      exact finitePart_limitPart_add_nat α (i + 1)
    refine ((extVisibilityReplace_self_iff _ _).mpr
      (Or.inr (Or.inr ⟨α + (i + 1 : ℕ), rfl, ?_⟩))).symm
    rw [hfp]
    exact hb c i hη

/-- **Locality at every controller** from the row law: proper controllers are free
(`RowObligation.of_ne_top`), source-`⊤` controllers are the law.  Together with
`offsetLabel_orderly` this is `RespectsSemantics` minus availability — the isolated exact
residue of the construction (see the section docstring). -/
theorem RowLaw.rowObligation_all {ν : FiniteOffset p} (h : ν.RowLaw)
    (Xi : Cell p.scheme.scheme) : ν.RowObligation Xi := by
  by_cases hXi : p.label Xi = ⊤
  · exact h Xi hXi
  · exact RowObligation.of_ne_top hXi

end FiniteOffset

end VaughtConjecture.Knight
