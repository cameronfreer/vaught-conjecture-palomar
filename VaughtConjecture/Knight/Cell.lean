/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import VaughtConjecture.AmalgamationPlan.Plan
public import VaughtConjecture.Knight.Value

/-! # Knight's cell schemes: cells, scopes, grades

Ported from Knight-VC `KnightVC/Semantics.lean` @ f7c7847d (`Sem.GradedLe`, `Sem.Domain`,
`Sem.Domain.arity`, `Sem.Domain.restrict`) and `KnightVC/TypeSpaceCountable.lean`
(`countable_Iic_ordinal`, `countable_boundedExtOrd`, `countable_SemDomain`,
`finite_domRestrict`), with Knight-VC's `Domain` renamed `CellScheme`, `arity` renamed
`grade`, and `restrict` renamed `below` (see `docs/TERMINOLOGY.md`: *domain* is reserved for
the carrier of a model, *arity* for tuples and characteristic arity).

A **cell scheme** on a finite set `A` (Knight's "domain" `D` of a type, Defs. 2.4.*/2.5.*) is
a support plan `P` on `A` together with a finite family of **cells**, each cell carrying a
**scope** (a visible face `B ∈ P`, the finite subset the cell sees) and a **grade**
`0 < j ≤ |B|` (Knight's "arity" of the cell), i.e. a point of the graded plan `P̂`
(`Plan.gradedPlan`).  The cells are indexed canonically by `Fin card`, so that two schemes with
the same plan, size and cell data are definitionally equal; `Cell D` is that index type.

* `GradedLe X Y` is the product preorder on graded indices, `X.1 ⊆ Y.1 ∧ X.2 ≤ Y.2`
  (cf. Def. 2.5.1);
* `D.below BJ` is the **lower set** of cells whose graded index lies below `BJ` (Knight-VC's
  `restrict`; this is not a face restriction of the scheme — that lives in the type space,
  see `docs/DESIGN.md` §4).  It is finite, and the **semantic row** of a cell `Sig` is a
  labelling of `D.below (D.cell Sig)` (`Knight.Semantics`).

Countability (the inputs to `Countable (S α n)` for countable `α`, Knight-VC
`countable_S`, assembled in `Knight.Type`): the cell schemes over `Fin n` form a
countable type (`CellScheme.countable_fin`), and the labels bounded at a countable stage `α`,
`{x : ExtOrd // x ≤ ofOrd α ∨ x = ⊤}`, form a countable set (`ExtOrd.countable_bounded`, via
`Ordinal.countable_Iic_of_card_le_aleph0`), as do the strictly bounded labels
`{x : ExtOrd // x < ofOrd α ∨ x = ⊤}` of the stage types (`ExtOrd.countable_bounded_lt`).

**Face restriction** (the scheme part of Knight-VC's `typeMap`, which inlines it; Knight,
Def. 3.1.5): for a scheme `D` on `Fin n` and an injection `f : Fin m ↪ Fin n` whose range is a
visible face (`hr`), `D.restrictFace f hr` is the scheme on `Fin m` whose plan is the pullback
plan `{C ⊆ Fin m | f[C] ∈ D.plan}` (`Plan.pullbackPlan`) and whose cells are the cells of `D`
**visible through `f`** (scope inside the range of `f`, `D.visibleCells f`), each with its scope
pulled back along `f` and its grade kept (`D.pullCell f`), enumerated in increasing order
(`Finset.orderEmbOfFin`, so that the restriction is canonical).  The enumeration is the cell map
`CellScheme.restrictFace.toCell : Cell (D.restrictFace f hr) ↪o Cell D`; the graded preorder is
reflected (`gradedLe_restrictFace_iff`), so rows transport (`Knight.Semantics`).  The laws of
restriction (`Knight.Type`: `typeMap_refl`, `typeMap_trans`) all reduce to one fact,
`restrictFace.toCell_cast_eq_of_emb`: any strictly monotone enumeration of exactly the visible
cells is `toCell` up to `Fin.cast`. -/

@[expose] public section

namespace VaughtConjecture.Knight

open VaughtConjecture.AmalgamationPlan
open scoped Cardinal

variable {ι : Type*}

/-- The product preorder on graded indices `(B, j)` (cf. Knight, Def. 2.5.1): `X ≤ Y` iff the
scope of `X` is contained in that of `Y` and the grade of `X` is at most that of `Y`. -/
def GradedLe (X Y : Finset ι × ℕ) : Prop :=
  X.1 ⊆ Y.1 ∧ X.2 ≤ Y.2

theorem GradedLe.refl (X : Finset ι × ℕ) : GradedLe X X :=
  ⟨Finset.Subset.refl _, le_rfl⟩

theorem GradedLe.trans {X Y Z : Finset ι × ℕ} (hXY : GradedLe X Y) (hYZ : GradedLe Y Z) :
    GradedLe X Z :=
  ⟨hXY.1.trans hYZ.1, hXY.2.trans hYZ.2⟩

variable [DecidableEq ι]

/-- A **cell scheme** on the finite set `A` (Knight's "domain" of a type, Defs. 2.4.*/2.5.*):
a support plan `plan` on `A` and `card` cells, the `d`-th cell having graded index
`cell d = (scope, grade)` in the graded plan `P̂`.  The cells are indexed by `Fin card`, so
schemes with the same `plan`, `card` and `cell` are definitionally equal. -/
structure CellScheme (A : Finset ι) where
  /-- The support plan of the scheme. -/
  plan : Finset (Finset ι)
  /-- `plan` is a support plan on `A`. -/
  isPlan : Plan.IsPlan A plan
  /-- The number of cells. -/
  card : ℕ
  /-- The graded index (scope, grade) of each cell. -/
  cell : Fin card → (Finset ι × ℕ)
  /-- Every cell's graded index lies in the graded plan `P̂`. -/
  cell_mem : ∀ d : Fin card, cell d ∈ Plan.gradedPlan plan

/-- The cells of a scheme `D`: the canonical index type `Fin D.card`. -/
abbrev Cell {A : Finset ι} (D : CellScheme A) : Type := Fin D.card

namespace CellScheme

variable {A : Finset ι} (D : CellScheme A)

/-- The **scope** of a cell: the visible face it sees. -/
def scope (d : Cell D) : Finset ι := (D.cell d).1

/-- The **grade** of a cell (Knight's "arity" of the cell): its graded index `j`. -/
def grade (d : Cell D) : ℕ := (D.cell d).2

@[simp] theorem cell_eq (d : Cell D) : D.cell d = (D.scope d, D.grade d) := rfl

/-- The scope of a cell is a visible face of the plan. -/
theorem scope_mem_plan (d : Cell D) : D.scope d ∈ D.plan :=
  (Plan.mem_gradedPlan.mp (D.cell_mem d)).1

/-- The grade of a cell is positive. -/
theorem grade_pos (d : Cell D) : 0 < D.grade d :=
  (Plan.mem_gradedPlan.mp (D.cell_mem d)).2.1

/-- The grade of a cell is at most the size of its scope. -/
theorem grade_le_card_scope (d : Cell D) : D.grade d ≤ (D.scope d).card :=
  (Plan.mem_gradedPlan.mp (D.cell_mem d)).2.2

/-- The lower set of cells whose graded index lies below `BJ` (Knight-VC's `restrict`;
Def. 2.5.2 style).  This is a lower set in the graded preorder `GradedLe`, not a face
restriction of the scheme.  The semantic row of a cell `Sig` lives on `D.below (D.cell Sig)`. -/
def below (BJ : Finset ι × ℕ) : Type :=
  { d : Cell D // GradedLe (D.cell d) BJ }

/-- `D.below BJ` is finite: a subtype of the finite index type `Cell D`.  (Stated explicitly
because `below` is not reducible.) -/
instance finite_below (BJ : Finset ι × ℕ) : Finite (D.below BJ) := by
  unfold below
  exact Subtype.finite

/-- The cell schemes over `Fin n` form a countable type: all data fields are `Finset`/`ℕ`
data (`isPlan` and `cell_mem` are proofs), so the scheme injects into
`Finset (Finset (Fin n)) × Σ c, (Fin c → Finset (Fin n) × ℕ)`. -/
instance countable_fin (n : ℕ) :
    Countable (CellScheme (ι := Fin n) (Finset.univ : Finset (Fin n))) := by
  let f : CellScheme (ι := Fin n) (Finset.univ : Finset (Fin n)) →
      Finset (Finset (Fin n)) × (Σ c : ℕ, Fin c → (Finset (Fin n) × ℕ)) :=
    fun d => (d.plan, ⟨d.card, d.cell⟩)
  have hinj : Function.Injective f := by
    rintro ⟨p1, ip1, c1, cl1, cm1⟩ ⟨p2, ip2, c2, cl2, cm2⟩ h
    simp only [f, Prod.mk.injEq, Sigma.mk.injEq] at h
    obtain ⟨hp, hc, hcl⟩ := h
    subst hp; subst hc
    simp only [heq_eq_eq] at hcl
    subst hcl
    rfl
  exact hinj.countable

end CellScheme

/-! ### Countability of bounded labels -/

/-- Ordinals `≤ α` form a countable set when `α.card ≤ ℵ₀`: `Set.Iic α ⊆ Set.Iio (α + 1)` and
`#(Set.Iio (α + 1)) = lift (α + 1).card ≤ ℵ₀` (`Cardinal.mk_Iio_ordinal`). -/
theorem Ordinal.countable_Iic_of_card_le_aleph0 {α : Ordinal.{0}} (hα : α.card ≤ ℵ₀) :
    (Set.Iic α).Countable := by
  rw [← Set.countable_coe_iff, ← Cardinal.mk_le_aleph0_iff]
  have hsucc : (Order.succ α).card ≤ ℵ₀ := by
    rw [Order.succ_eq_add_one, Ordinal.card_add, Ordinal.card_one]
    exact Cardinal.add_le_aleph0.mpr ⟨hα, Cardinal.one_le_aleph0⟩
  calc #(Set.Iic α) ≤ #(Set.Iio (Order.succ α)) :=
        Cardinal.mk_le_mk_of_subset
          (fun β hβ => Set.mem_Iio.mpr (Order.lt_succ_iff.mpr (Set.mem_Iic.mp hβ)))
    _ = Cardinal.lift.{1} (Order.succ α).card := Cardinal.mk_Iio_ordinal _
    _ ≤ ℵ₀ := by rw [Cardinal.lift_le_aleph0]; exact hsucc

/-- The labels non-strictly bounded at a countable stage `α` (`x ≤ ofOrd α ∨ x = ⊤`) form a
countable type: they lie in `{⊤, ⊥} ∪ ofOrd '' Set.Iic α`.  (The stage types use the strict
bound, `ExtOrd.countable_bounded_lt` below.) -/
theorem ExtOrd.countable_bounded {α : Ordinal.{0}} (hα : α.card ≤ ℵ₀) :
    Countable {x : ExtOrd // x ≤ ExtOrd.ofOrd α ∨ x = ⊤} := by
  have key : {x : ExtOrd | x ≤ ExtOrd.ofOrd α ∨ x = ⊤}
      ⊆ insert ⊤ (insert ⊥ (ExtOrd.ofOrd '' Set.Iic α)) := by
    rintro x (hle | htop)
    · rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ ⟨β, ExtOrd.ofOrd_le_ofOrd.mp hle, rfl⟩)
    · exact Set.mem_insert_iff.mpr (Or.inl htop)
  have hc : (insert (⊤ : ExtOrd) (insert ⊥ (ExtOrd.ofOrd '' Set.Iic α))).Countable :=
    (((Ordinal.countable_Iic_of_card_le_aleph0 hα).image _).insert _).insert _
  exact (hc.mono key).to_subtype

/-- The labels **strictly** bounded at a countable stage `α` (`x < ofOrd α ∨ x = ⊤`, the label
bound of a stage-`α` type under the strict convention of #84) form a countable type: they
inject into the non-strictly bounded labels of `ExtOrd.countable_bounded`. -/
theorem ExtOrd.countable_bounded_lt {α : Ordinal.{0}} (hα : α.card ≤ ℵ₀) :
    Countable {x : ExtOrd // x < ExtOrd.ofOrd α ∨ x = ⊤} := by
  have := ExtOrd.countable_bounded hα
  exact Function.Injective.countable
    (f := fun x : {x : ExtOrd // x < ExtOrd.ofOrd α ∨ x = ⊤} =>
      (⟨x.1, x.2.imp le_of_lt id⟩ : {x : ExtOrd // x ≤ ExtOrd.ofOrd α ∨ x = ⊤}))
    fun _ _ h => Subtype.ext (Subtype.mk.inj h)

/-! ### Face restriction of a cell scheme -/

namespace CellScheme

variable {m n : ℕ} (D : CellScheme (ι := Fin n) Finset.univ) (f : Fin m ↪ Fin n)

/-- The cells of `D` **visible through** `f`: those whose scope lies in the range of `f`. -/
def visibleCells : Finset (Cell D) :=
  Finset.univ.filter (fun d => D.scope d ⊆ Finset.univ.image f)

theorem mem_visibleCells {d : Cell D} :
    d ∈ D.visibleCells f ↔ D.scope d ⊆ Finset.univ.image f := by
  simp [visibleCells]

/-- The graded index of a cell of `D` pulled back along `f`: the preimage of its scope under
`f`, with the same grade. -/
def pullCell (d : Cell D) : Finset (Fin m) × ℕ :=
  (Finset.univ.filter (fun i => f i ∈ D.scope d), D.grade d)

/-- The pulled-back graded index depends only on the graded index of the cell. -/
theorem pullCell_congr {a b : Cell D} (h : D.cell a = D.cell b) :
    D.pullCell f a = D.pullCell f b := by
  have hs : D.scope a = D.scope b := congrArg Prod.fst h
  have hg : D.grade a = D.grade b := congrArg Prod.snd h
  unfold pullCell
  rw [hs, hg]

/-- The pulled-back scope maps back onto the original scope when the latter is visible. -/
theorem image_pullCell_fst {d : Cell D} (hd : D.scope d ⊆ Finset.univ.image f) :
    (D.pullCell f d).1.image f = D.scope d := by
  ext x
  simp only [pullCell, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun ⟨i, hi, hix⟩ => hix ▸ hi, fun hx => ?_⟩
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hd hx)
  exact ⟨i, hx, rfl⟩

theorem card_pullCell_fst {d : Cell D} (hd : D.scope d ⊆ Finset.univ.image f) :
    (D.pullCell f d).1.card = (D.scope d).card := by
  rw [← Finset.card_image_of_injective _ f.injective, image_pullCell_fst D f hd]

/-- The graded preorder is reflected by pulling back visible cells. -/
theorem gradedLe_pullCell_iff {a b : Cell D} (ha : D.scope a ⊆ Finset.univ.image f) :
    GradedLe (D.pullCell f a) (D.pullCell f b) ↔ GradedLe (D.cell a) (D.cell b) := by
  simp only [GradedLe, pullCell, cell_eq]
  refine and_congr_left' ⟨fun h x hx => ?_, fun h i hi => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (ha hx)
    exact (Finset.mem_filter.mp (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩))).2
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h (Finset.mem_filter.mp hi).2⟩

/-- The **face restriction** of a cell scheme along `f : Fin m ↪ Fin n` whose range is a
visible face (Knight, Def. 3.1.5; the scheme part of Knight-VC `typeMap`): the pullback plan
`{C ⊆ Fin m | f[C] ∈ D.plan}`, and the cells of `D` visible through `f`, pulled back along `f`
and enumerated in increasing order. -/
noncomputable def restrictFace (hr : Finset.univ.image f ∈ D.plan) :
    CellScheme (ι := Fin m) Finset.univ where
  plan := (Finset.univ : Finset (Fin m)).powerset.filter (fun C => C.image f ∈ D.plan)
  isPlan := Plan.pullback_isPlan_fin f D.isPlan hr
  card := (D.visibleCells f).card
  cell i := D.pullCell f ((D.visibleCells f).orderEmbOfFin rfl i)
  cell_mem i := by
    have hvis := (D.mem_visibleCells f).mp ((D.visibleCells f).orderEmbOfFin_mem rfl i)
    refine Plan.mem_gradedPlan.mpr ⟨?_, D.grade_pos _, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
        by rw [image_pullCell_fst D f hvis]; exact D.scope_mem_plan _⟩
    · rw [card_pullCell_fst D f hvis]; exact D.grade_le_card_scope _

variable (hr : Finset.univ.image f ∈ D.plan)

theorem restrictFace_plan :
    (D.restrictFace f hr).plan =
      (Finset.univ : Finset (Fin m)).powerset.filter (fun C => C.image f ∈ D.plan) := rfl

/-- The plan of the restriction is the (defined) pullback plan. -/
theorem pullbackPlan_eq_restrictFace_plan :
    Plan.pullbackPlan f D.plan = some (D.restrictFace f hr).plan :=
  Plan.pullbackPlan_eq_some f hr

/-- Membership in the restricted plan: a face of `Fin m` is visible iff its image is. -/
theorem mem_restrictFace_plan {C : Finset (Fin m)} :
    C ∈ (D.restrictFace f hr).plan ↔ C.image f ∈ D.plan := by
  simp [restrictFace_plan]

theorem card_restrictFace : (D.restrictFace f hr).card = (D.visibleCells f).card := rfl

namespace restrictFace

/-- The cell map of a face restriction: the `i`-th cell of `D.restrictFace f hr` is the `i`-th
visible cell of `D` in increasing order (Knight-VC: `canonEquivFin` of the visible subtype). -/
noncomputable def toCell : Cell (D.restrictFace f hr) ↪o Cell D :=
  (D.visibleCells f).orderEmbOfFin (D.card_restrictFace f hr).symm

theorem scope_toCell_subset (i : Cell (D.restrictFace f hr)) :
    D.scope (toCell D f hr i) ⊆ Finset.univ.image f :=
  (D.mem_visibleCells f).mp ((D.visibleCells f).orderEmbOfFin_mem _ i)

theorem toCell_strictMono : StrictMono (toCell D f hr) := (toCell D f hr).strictMono

theorem toCell_injective : Function.Injective (toCell D f hr) := (toCell D f hr).injective

/-- Every visible cell of `D` is hit by the cell map. -/
theorem exists_toCell_eq {d : Cell D} (hd : D.scope d ⊆ Finset.univ.image f) :
    ∃ i, toCell D f hr i = d := by
  have hmem : d ∈ Set.range (toCell D f hr) := by
    rw [toCell, Finset.range_orderEmbOfFin]; exact (D.mem_visibleCells f).mpr hd
  exact hmem

theorem cell_eq (i : Cell (D.restrictFace f hr)) :
    (D.restrictFace f hr).cell i = D.pullCell f (toCell D f hr i) := rfl

@[simp] theorem scope_restrictFace (i : Cell (D.restrictFace f hr)) :
    (D.restrictFace f hr).scope i =
      Finset.univ.filter (fun j => f j ∈ D.scope (toCell D f hr i)) := rfl

@[simp] theorem grade_restrictFace (i : Cell (D.restrictFace f hr)) :
    (D.restrictFace f hr).grade i = D.grade (toCell D f hr i) := rfl

/-- The image under `f` of a restricted scope is the original scope. -/
theorem image_scope_restrictFace (i : Cell (D.restrictFace f hr)) :
    ((D.restrictFace f hr).scope i).image f = D.scope (toCell D f hr i) :=
  image_pullCell_fst D f (scope_toCell_subset D f hr i)

/-- The graded preorder of the restriction is the graded preorder of `D` on the visible
cells. -/
theorem gradedLe_restrictFace_iff {i j : Cell (D.restrictFace f hr)} :
    GradedLe ((D.restrictFace f hr).cell i) ((D.restrictFace f hr).cell j) ↔
      GradedLe (D.cell (toCell D f hr i)) (D.cell (toCell D f hr j)) :=
  gradedLe_pullCell_iff D f (scope_toCell_subset D f hr i)

/-- Knight-VC `gradedLe_pullback_to_orig`. -/
theorem gradedLe_of_restrictFace {i j : Cell (D.restrictFace f hr)}
    (h : GradedLe ((D.restrictFace f hr).cell i) ((D.restrictFace f hr).cell j)) :
    GradedLe (D.cell (toCell D f hr i)) (D.cell (toCell D f hr j)) :=
  (gradedLe_restrictFace_iff D f hr).mp h

/-- Transport of the lower set below a restricted cell `Sig` into the lower set below
`toCell Sig` in `D` (the index map of the semantic rows). -/
noncomputable def belowMap (Sig : Cell (D.restrictFace f hr)) :
    (D.restrictFace f hr).below ((D.restrictFace f hr).cell Sig) →
      D.below (D.cell (toCell D f hr Sig)) :=
  fun d => ⟨toCell D f hr d.1, gradedLe_of_restrictFace D f hr d.2⟩

@[simp] theorem belowMap_val (Sig : Cell (D.restrictFace f hr))
    (d : (D.restrictFace f hr).below ((D.restrictFace f hr).cell Sig)) :
    (belowMap D f hr Sig d).1 = toCell D f hr d.1 := rfl

/-! The canonical enumeration is determined by its range: any strictly monotone `e : Fin k → Cell D`
whose range is exactly the visible cells is `toCell` up to `Fin.cast`.  This is the one fact
behind the restriction laws. -/

section Emb

variable {k : ℕ} {e : Fin k → Cell D}

theorem visibleCells_eq_image_of_emb (hvis : ∀ c, D.scope (e c) ⊆ Finset.univ.image f)
    (hsurj : ∀ d, D.scope d ⊆ Finset.univ.image f → ∃ c, e c = d) :
    D.visibleCells f = Finset.univ.image e := by
  ext d
  rw [mem_visibleCells, Finset.mem_image]
  exact ⟨fun hd => (hsurj d hd).imp fun c hc => ⟨Finset.mem_univ _, hc⟩,
    fun ⟨c, _, hc⟩ => hc ▸ hvis c⟩

theorem card_restrictFace_of_emb (he : StrictMono e)
    (hvis : ∀ c, D.scope (e c) ⊆ Finset.univ.image f)
    (hsurj : ∀ d, D.scope d ⊆ Finset.univ.image f → ∃ c, e c = d) :
    (D.restrictFace f hr).card = k := by
  rw [card_restrictFace, visibleCells_eq_image_of_emb D f hvis hsurj,
    Finset.card_image_of_injective _ he.injective, Finset.card_univ, Fintype.card_fin]

theorem toCell_cast_eq_of_emb (he : StrictMono e)
    (hvis : ∀ c, D.scope (e c) ⊆ Finset.univ.image f)
    (hk : (D.restrictFace f hr).card = k) (c : Fin k) :
    toCell D f hr (Fin.cast hk.symm c) = e c := by
  have hk' : (D.visibleCells f).card = k := hk
  rw [Finset.orderEmbOfFin_unique hk' (fun c => (D.mem_visibleCells f).mpr (hvis c)) he, toCell,
    Finset.orderEmbOfFin_eq_orderEmbOfFin_iff, Fin.val_cast]

end Emb

end restrictFace

end CellScheme

end VaughtConjecture.Knight
