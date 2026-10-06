/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedSuccessor
public import VaughtConjecture.Knight.GrowthFiniteReflection
public import VaughtConjecture.Knight.AmbientGradeCharts
public import VaughtConjecture.Knight.SupportLadderBottomReflection

/-! # Complete-field recognition from the maximal leaf chart on the growth successor rows

On the actual one-scope grade-two growth rows (`GrowthPaddedSuccessor`), an **arbitrary** lawful
section `p` below `(A, 2)` is recognized by the chart of its maximal ceiling leaf.  No admission,
selected display, bottom-pattern class or hidden-original completion of `p` is assumed, and no
probe interface is introduced: the chart is extracted from lawfulness alone
(`AmbientGradeCharts.exists_chart`), and its owner is necessarily a leaf.

Write `B_p f` for the finite maximum of `p` over the shadows of the complete field `f`
(`shadowSup`), `M₂ p` for its maximum over the ceiling leaves (`leafSup`) and `M₁ p` for its
maximum over the spare rungs (`spareSup`).  With `a` the maximal leaf and `σ` its chart:

* **Complete-field recognition** (`recognition`): `σ (a f) = min (B_p f) (M₂ p)` for **every**
  complete field `f`, present, hidden or future — the shadows of every field are installed —
  because the native row reads the field as the finite maximum of its shadow columns
  (`source_shadow_sup`) and a monotone bottom-preserving chart commutes with finite maxima.
* **Finite bottom reflection** (`bottom_reflection`): when `M₂ p ≠ ⊥`, `σ (a f) = ⊥` forces
  `a f = ⊥`, on the ladder's tracked values only (`SupportLadderRows.bottom_reflection_image`
  on the actual ladder restriction of `p`, whose lawfulness is derived in `ladder_lawful`, with
  the spare rung reading the ceiling).  Nothing global about `σ` is asserted.
* **The reconstructed complete vector is admitted** (`exists_admitted`): the transported
  state `(state a).map σ` is `Growth.Admitted X 2` by `Admitted.map_on_profile`, and its
  profile is `f ↦ min (B_p f) (M₂ p)`; at `M₂ p = ⊥` it is the zero state.
* **Readouts** (`present_readback`, `present_readback_of_grade_two`, `leafSup_le_spareSup`):
  every present original cell reads `min (B_p (field d)) (M₂ p)` below `M₂ p`, exactly so at
  grade two, and `M₂ p ≤ M₁ p` through the maximal leaf's birth spare.

Grade one (the uncapped values `B_p f` themselves and the grade-one original vector) needs the
maximal spare chart of the checked base and is not treated here.  Mixed scopes are not treated
here. -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GrowthLeafRecognition

open Transform Value ExtOrd Growth GrowthHigherSources GrowthPaddedSuccessor
open SupportLadderRows LadderScalarRendering SharpWitnessComposition

noncomputable section

theorem card_pos {ι : Type*} {A : Finset ι} (h : 2 ≤ A.card) : 0 < A.card := by omega

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "Ωc" => carrier I X T hA hB hC
local notation "Occ" => CellScheme.below (carrier I X T hA hB hC) (A, 2)
local notation "cellΩ" => CellScheme.cell (carrier I X T hA hB hC)
local notation "gradeΩ" => CellScheme.grade (carrier I X T hA hB hC)
local notation "Eρ" => Semantics.E (rows I X T hA hB hC)
local notation "Rows" => rows I X T hA hB hC
local notation "src" => source I X T hA hB hC
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)
local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)
local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)
local notation "ceil" => RecursiveRungRendering.ceiling Fld 2
local notation "lowerΩ" => LadderWeightedSuccessor.Input.lower (input I X T hA hB hC)

theorem rungs_pos : 0 < rungs := Nat.succ_pos _

/-! ## Occurrences below `(A, 2)` -/

theorem cell_old (x : Cell lowerΩ) :
    cellΩ (GrowthPaddedSuccessor.old I X T hA hB hC x) = CellScheme.cell lowerΩ x :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _

theorem cell_added (v : Pt) :
    cellΩ (GrowthPaddedSuccessor.old I X T hA hB hC
      (RelativeLadderLayer.added I.boundary (card_pos hA) v)) = (A, 1) := by
  rw [cell_old]
  exact RelativeLadderLayer.added_index I.boundary (card_pos hA) v

/-- A padded point of the checked base as an occurrence of the successor. -/
def ladderAt (v : Pt) : Occ :=
  ⟨GrowthPaddedSuccessor.old I X T hA hB hC (RelativeLadderLayer.added I.boundary (card_pos hA) v),
    by rw [cell_added]; exact ⟨Finset.Subset.refl _, Nat.le_succ 1⟩⟩

/-- A ceiling leaf as an occurrence of the successor. -/
def leafAt (a : Catalogue X 2) : Occ :=
  ⟨GrowthPaddedSuccessor.leaf I X T hA hB hC a, by
    rw [GrowthPaddedSuccessor.leaf_index]; exact GradedLe.refl _⟩

/-- A present original cell as an occurrence of the successor. -/
def originalAt (d : Cell I.boundary) (hd : GradedLe (I.boundary.cell d) (A, 2)) : Occ :=
  ⟨GrowthPaddedSuccessor.original I X T hA hB hC d, by
    rw [GrowthPaddedSuccessor.original_index]; exact hd⟩

theorem cell_ladderAt (v : Pt) : cellΩ (ladderAt I X T hA hB hC v).1 = (A, 1) :=
  cell_added I X T hA hB hC v

theorem grade_ladderAt (v : Pt) : gradeΩ (ladderAt I X T hA hB hC v).1 = 1 :=
  congrArg Prod.snd (cell_ladderAt I X T hA hB hC v)

theorem grade_leafAt (a : Catalogue X 2) : gradeΩ (leafAt I X T hA hB hC a).1 = 2 :=
  congrArg Prod.snd (GrowthPaddedSuccessor.leaf_index I X T hA hB hC a)

/-- Every occurrence of index `(A, 2)` is a ceiling leaf: the inherited cells are separated. -/
theorem eq_leaf_of_index (c : Cell Ωc) (hc : cellΩ c = (A, 2)) :
    ∃ a : Catalogue X 2, c = GrowthPaddedSuccessor.leaf I X T hA hB hC a := by
  rcases GrowthPaddedSuccessor.cell_cases I X T hA hB hC c with ⟨x, hx⟩ | ⟨a, ha⟩
  · exfalso
    apply LadderWeightedSuccessor.Input.separation (input I X T hA hB hC) x
    rw [← cell_old I X T hA hB hC x, ← hx, hc]
    exact GradedLe.refl _
  · exact ⟨a, ha⟩

/-! ## The finite maxima -/

variable (p : CellScheme.below (carrier I X T hA hB hC) (A, 2) → ExtOrd)

/-- The maximum of `p` over the shadows of a complete field. -/
def shadowSup (f : Fld) : ExtOrd :=
  (Finset.univ : Finset (Catalogue X 1)).sup fun b => p (ladderAt I X T hA hB hC (shadow b f))

/-- The maximum of `p` over the spare rungs. -/
def spareSup : ExtOrd :=
  (Finset.univ : Finset (Catalogue X 1)).sup fun b =>
    p (ladderAt I X T hA hB hC (SupportLadderRows.leaf (rungs_pos I) b))

/-- The maximum of `p` over the ceiling leaves. -/
def leafSup : ExtOrd :=
  (Finset.univ : Finset (Catalogue X 2)).sup fun a => p (leafAt I X T hA hB hC a)

theorem le_leafSup (a : Catalogue X 2) :
    p (leafAt I X T hA hB hC a) ≤ leafSup I X T hA hB hC p :=
  Finset.le_sup (f := fun a => p (leafAt I X T hA hB hC a)) (Finset.mem_univ a)

theorem le_spareSup (b : Catalogue X 1) :
    p (ladderAt I X T hA hB hC (SupportLadderRows.leaf (rungs_pos I) b)) ≤
      spareSup I X T hA hB hC p :=
  Finset.le_sup
    (f := fun b => p (ladderAt I X T hA hB hC (SupportLadderRows.leaf (rungs_pos I) b)))
    (Finset.mem_univ b)

/-- Finite maxima commute with capping. -/
theorem cap_sup {Y : Type*} [Fintype Y] (g : Y → ExtOrd) (h : ExtOrd) :
    min (Finset.univ.sup g) h = Finset.univ.sup fun y => min (g y) h :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x => min x h)
    (fun _ _ hxy => min_le_min_right _ hxy) (min_bot_left _)

/-! ## The native rows on the padded base -/

theorem rank_le_rungs (a : Catalogue X 1) (f : Fld) : ranks₁ a f ≤ rungs :=
  (RelativeLadderLayer.rank_bound (fields X 1) a f).le

/-- The retained padded source of a leaf is the ceiling-filled table on its birth anchor. -/
theorem source_ladder (a : Catalogue X 2) (v : Pt) :
    src a (ladderAt I X T hA hB hC v).1 =
      SupportLadderRows.image ranks₁ (baseAnchor X a)
        (LadderScalarRendering.level (LadderScalarRendering.values (fields X 2 a)) ceil) v := by
  change (input I X T hA hB hC).source a ((input I X T hA hB hC).old
    (RelativeLadderLayer.added I.boundary (card_pos hA) v)) = _
  rw [LadderWeightedSuccessor.Input.source_old]
  change RelativeLadderLayer.image I.boundary (card_pos hA) (GrowthOrderedBase.field I)
    (fields X 1) (baseAnchor X a)
    (LadderScalarRendering.level (LadderScalarRendering.values (fields X 2 a)) ceil)
    (RelativeLadderLayer.added I.boundary (card_pos hA) v) = _
  rw [RelativeLadderLayer.image, RelativeLadderLayer.rankIndex_added]
  rfl

/-- The birth anchor's own shadow of `f` is indexed by the rank of `f`. -/
theorem index_shadow_self (a : Catalogue X 1) (f : Fld) :
    SupportLadderRows.index (H := rungs) ranks₁ a (shadow a f) = ranks₁ a f := by
  change min (FiniteProfileControllers.cut rungs (ranks₁ a) (ranks₁ a)) (ranks₁ a f) = _
  rw [FiniteProfileControllers.cut_refl]
  exact min_eq_right (rank_le_rungs I X a f)

/-- The complete-field readback of a leaf's row through its own birth shadow. -/
theorem source_shadow_birth (a : Catalogue X 2) (f : Fld) :
    src a (ladderAt I X T hA hB hC (shadow (baseAnchor X a) f)).1 = fields X 2 a f := by
  rw [source_ladder, SupportLadderRows.image, index_shadow_self, baseAnchor_ranks,
    field_readback]

/-- **Shadow recognition of the native row**: the finite maximum of a leaf's source over the
shadows of `f` is its original `f`-column. -/
theorem source_shadow_sup (a : Catalogue X 2) (f : Fld) :
    ((Finset.univ : Finset (Catalogue X 1)).sup fun b =>
      src a (ladderAt I X T hA hB hC (shadow b f)).1) = fields X 2 a f := by
  have he := SupportLadderRows.readout_image (H := rungs) (rank_le_rungs I X) (baseAnchor X a)
    (level_mono (values_bound (anchor_bound X a))) f
  simp only [SupportLadderRows.readout] at he
  rw [show Fintype.ofFinite (Catalogue X 1) = (inferInstance : Fintype (Catalogue X 1)) from
    Subsingleton.elim _ _] at he
  simp only [source_ladder]
  rw [he, baseAnchor_ranks, field_readback]

/-- The birth spare of a leaf reads the ceiling. -/
theorem source_spare (a : Catalogue X 2) :
    src a (ladderAt I X T hA hB hC (SupportLadderRows.leaf (rungs_pos I) (baseAnchor X a))).1 =
      ceil := by
  rw [source_ladder, SupportLadderRows.image, SupportLadderRows.index_leaf,
    FiniteProfileControllers.cut_refl, LadderScalarRendering.level]
  apply ite_eq_left
  exact lt_of_le_of_lt (values_card_le (fields X 2 a)) (Nat.lt_succ_self _)

/-! ## The ladder restriction of an arbitrary lawful section -/

variable {p}

/-- The row of an occurrence known to be a leaf. -/
theorem row_of_eq_leaf {c : Cell Ωc} (a : Catalogue X 2)
    (hc : c = GrowthPaddedSuccessor.leaf I X T hA hB hC a) (d : CellScheme.below Ωc (cellΩ c)) :
    Eρ c d = src a d.1 := by
  subst hc
  exact GrowthPaddedSuccessor.leaf_row I X T hA hB hC a d

/-- A padded point below a padded owner. -/
def ladderBelow (c v : Pt) : CellScheme.below Ωc (cellΩ (ladderAt I X T hA hB hC c).1) :=
  ⟨(ladderAt I X T hA hB hC v).1, by
    rw [cell_ladderAt, cell_ladderAt]
    exact GradedLe.refl _⟩

/-- A padded point of the checked base below a padded owner of the checked base. -/
def lowerBelow (c v : Pt) : CellScheme.below lowerΩ
    (CellScheme.cell lowerΩ (RelativeLadderLayer.added I.boundary (card_pos hA) c)) :=
  ⟨RelativeLadderLayer.added I.boundary (card_pos hA) v, by
    change GradedLe ((RelativeLadderLayer.carrier I.boundary (card_pos hA)).cell
      (RelativeLadderLayer.added I.boundary (card_pos hA) v))
      ((RelativeLadderLayer.carrier I.boundary (card_pos hA)).cell
        (RelativeLadderLayer.added I.boundary (card_pos hA) c))
    rw [RelativeLadderLayer.added_index, RelativeLadderLayer.added_index]
    exact GradedLe.refl _⟩

/-- The checked base's row of a padded owner at a padded argument is the actual ladder row. -/
theorem lower_row_ladder (c v : Pt) :
    Semantics.E (input I X T hA hB hC).lowerRows
      (RelativeLadderLayer.added I.boundary (card_pos hA) c) (lowerBelow I X T hA hB hC c v) =
      SupportLadderRows.row ranks₁ c v := by
  rw [GrowthPaddedSuccessor.lower_rows_literal, RelativeLadderLayer.row_added]
  change SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ c)
    (RelativeLadderLayer.rankIndex I.boundary (card_pos hA) (GrowthOrderedBase.field I)
      (fields X 1) (SupportLadderRows.parent c)
      (RelativeLadderLayer.added I.boundary (card_pos hA) v)) = _
  rw [RelativeLadderLayer.rankIndex_added]
  rfl

/-- The inherited row of a padded owner at a padded argument is the actual ladder row. -/
theorem row_ladder (c v : Pt) :
    Eρ (ladderAt I X T hA hB hC c).1 (ladderBelow I X T hA hB hC c v) =
      SupportLadderRows.row ranks₁ c v := by
  have h1 := GrowthPaddedSuccessor.inherited_row I X T hA hB hC
    (RelativeLadderLayer.added I.boundary (card_pos hA) c) (lowerBelow I X T hA hB hC c v)
  exact h1.trans (lower_row_ladder I X T hA hB hC c v)

/-- **The ladder restriction of an arbitrary lawful section is a lawful ladder table.**  No
whole-ambient extension, synchronization or normalization assumption is used. -/
theorem ladder_lawful (hp : RespectsSemanticsBelow Rows (A, 2) p) :
    Lawful ranks₁ (fun v => p (ladderAt I X T hA hB hC v)) := by
  constructor
  · intro v
    have hv := hp.orderly (ladderAt I X T hA hB hC v)
    change p _ = extVisibilityReplace (p _) (gradeΩ (ladderAt I X T hA hB hC v).1)
      (gradeΩ (ladderAt I X T hA hB hC v).1) at hv
    rw [grade_ladderAt] at hv
    exact hv.symm
  · intro c
    have ht := (hp.locality (ladderAt I X T hA hB hC c)).reindex (ladderBelow I X T hA hB hC c)
    have hr : Eρ (ladderAt I X T hA hB hC c).1 ∘ ladderBelow I X T hA hB hC c =
        SupportLadderRows.row ranks₁ c := funext fun v => row_ladder I X T hA hB hC c v
    have hg : ((fun d : CellScheme.below Ωc (cellΩ (ladderAt I X T hA hB hC c).1) =>
        gradeΩ d.1) ∘ ladderBelow I X T hA hB hC c) = fun _ => 1 :=
      funext fun v => grade_ladderAt I X T hA hB hC v
    have hq : ((fun d : CellScheme.below Ωc (cellΩ (ladderAt I X T hA hB hC c).1) =>
        min (p (CellScheme.below.incl (ladderAt I X T hA hB hC c) d))
          (p (ladderAt I X T hA hB hC c))) ∘ ladderBelow I X T hA hB hC c) =
        fun v => min (p (ladderAt I X T hA hB hC v)) (p (ladderAt I X T hA hB hC c)) :=
      funext fun v => rfl
    rw [hr, hg, hq] at ht
    exact ht

/-! ## The maximal leaf chart -/

/-- The catalogue is nonempty: the zero state is admitted and canonical. -/
def zeroMember (j : ℕ) (hj : 1 ≤ j) : Catalogue X j :=
  Growth.zeroMember X j hj

/-- **The maximal leaf chart of an arbitrary lawful section**: a ceiling leaf attaining `M₂ p`,
whose chart through grade two is bounded by `M₂ p` and reads every occurrence below `(A, 2)`
capped at `M₂ p`.  Extracted from lawfulness alone. -/
theorem exists_leaf_chart (hp : RespectsSemanticsBelow Rows (A, 2) p) :
    ∃ (a : Catalogue X 2) (σ : ExtOrd → ExtOrd), Witness (gTop 2) σ ∧
      p (leafAt I X T hA hB hC a) = leafSup I X T hA hB hC p ∧
      (∀ x, σ x ≤ leafSup I X T hA hB hC p) ∧
      ∀ z : Occ, σ (src a z.1) = min (p z) (leafSup I X T hA hB hC p) := by
  obtain ⟨Ch⟩ := AmbientGradeCharts.exists_chart hp
    ⟨leafAt I X T hA hB hC (zeroMember I X 2 (by decide)), leaf_index I X T hA hB hC _⟩
  obtain ⟨a, ha⟩ := eq_leaf_of_index I X T hA hB hC Ch.owner.1 Ch.index
  have howner : Ch.owner = leafAt I X T hA hB hC a := Subtype.ext ha
  have hmax : p (leafAt I X T hA hB hC a) = leafSup I X T hA hB hC p := by
    apply le_antisymm (le_leafSup I X T hA hB hC p a)
    apply Finset.sup_le
    intro b _
    rw [← howner]
    exact Ch.dominates _ (grade_leafAt I X T hA hB hC b)
  refine ⟨a, Ch.shift, Ch.witness, hmax, fun x => (Ch.bounded x).trans_eq (by rw [howner, hmax]),
    fun z => ?_⟩
  have hz : GradedLe (cellΩ z.1) (cellΩ Ch.owner.1) := by rw [Ch.index]; exact z.2
  have hr := Ch.read ⟨z.1, hz⟩
  have e := row_of_eq_leaf I X T hA hB hC a ha ⟨z.1, hz⟩
  have hr' : Ch.shift (src a z.1) =
      min (p (CellScheme.below.incl Ch.owner ⟨z.1, hz⟩)) (p Ch.owner) := by
    rw [← e]
    exact hr
  have h1 : CellScheme.below.incl Ch.owner ⟨z.1, hz⟩ = z := Subtype.ext rfl
  have h2 : p Ch.owner = leafSup I X T hA hB hC p := by rw [howner]; exact hmax
  rw [hr', h1, h2]

/-! ## Recognition and finite bottom reflection -/

theorem exists_zero_admitted (h : leafSup I X T hA hB hC p = ⊥) :
    ∃ S : State I.right.scheme I.left.scheme, Admitted X 2 S ∧
      ∀ f, S.profile f = min (shadowSup I X T hA hB hC p f) (leafSup I X T hA hB hC p) :=
  ⟨zero, zero_admitted X 2, fun f => by rw [h, min_bot_right]; cases f <;> rfl⟩

section Chart

variable {a : Catalogue X 2} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop 2) σ)
  (hread : ∀ z : CellScheme.below (carrier I X T hA hB hC) (A, 2),
    σ (source I X T hA hB hC a z.1) = min (p z) (leafSup I X T hA hB hC p))

include hσ hread

/-- **Complete-field recognition**: on every complete field — present, hidden or future — the
chart reads the leaf's numerical value as the shadow maximum capped at `M₂ p`. -/
theorem recognition (f : Fld) :
    σ (fields X 2 a f) = min (shadowSup I X T hA hB hC p f) (leafSup I X T hA hB hC p) := by
  rw [← source_shadow_sup I X T hA hB hC a f,
    Finset.apply_sup_eq_sup_comp_of_linearOrder σ hσ.mono hσ.bot, shadowSup, cap_sup]
  congr 1
  funext b
  exact hread _

omit hσ in
/-- The maximal leaf's chart reads the ceiling as `M₂ p`. -/
theorem read_ceiling (hmax : p (leafAt I X T hA hB hC a) = leafSup I X T hA hB hC p) :
    σ ceil = leafSup I X T hA hB hC p := by
  have h := hread (leafAt I X T hA hB hC a)
  change σ (src a (GrowthPaddedSuccessor.leaf I X T hA hB hC a)) = _ at h
  rw [GrowthPaddedSuccessor.source_ceiling] at h
  rw [h, hmax, min_self]

omit hσ in
/-- `M₂ p ≤ M₁ p`: the maximal leaf's birth spare reads the ceiling. -/
theorem leafSup_le_spareSup (hmax : p (leafAt I X T hA hB hC a) = leafSup I X T hA hB hC p) :
    leafSup I X T hA hB hC p ≤ spareSup I X T hA hB hC p := by
  have h := hread (ladderAt I X T hA hB hC
    (SupportLadderRows.leaf (rungs_pos I) (baseAnchor X a)))
  rw [source_spare, read_ceiling I X T hA hB hC hread hmax] at h
  exact (min_eq_right_iff.mp h.symm).trans (le_spareSup I X T hA hB hC p _)

/-- Every present original cell reads the recognized value below `M₂ p`. -/
theorem present_readback (d : Cell I.boundary) (hd : GradedLe (I.boundary.cell d) (A, 2)) :
    min (p (originalAt I X T hA hB hC d hd)) (leafSup I X T hA hB hC p) =
      min (shadowSup I X T hA hB hC p (GrowthOrderedBase.field I d))
        (leafSup I X T hA hB hC p) := by
  rw [← recognition I X T hA hB hC hσ hread, ← hread (originalAt I X T hA hB hC d hd)]
  change σ (src a (GrowthPaddedSuccessor.original I X T hA hB hC d)) = _
  rw [GrowthPaddedSuccessor.original_readback]

/-- **Finite bottom reflection on every complete field**, from the maximal leaf's actual ladder
restriction.  Reflection is asserted only on the leaf's tracked values. -/
theorem bottom_reflection (hp : RespectsSemanticsBelow Rows (A, 2) p)
    (hmax : p (leafAt I X T hA hB hC a) = leafSup I X T hA hB hC p)
    (hne : leafSup I X T hA hB hC p ≠ ⊥) (f : Fld) :
    σ (fields X 2 a f) = ⊥ → fields X 2 a f = ⊥ := by
  have hCne : ceil ≠ ⊥ := fun hz =>
    hne (by rw [← read_ceiling I X T hA hB hC hread hmax, hz, hσ.bot])
  have : Nonempty (Catalogue X 1) := ⟨zeroMember I X 1 le_rfl⟩
  have h0 : LadderScalarRendering.level (LadderScalarRendering.values (fields X 2 a)) ceil 0 =
      ⊥ := level_zero _ _
  have hf : ∀ i, 0 < i → i ≤ rungs →
      LadderScalarRendering.level (LadderScalarRendering.values (fields X 2 a)) ceil i ≠ ⊥ :=
    fun i hi _ => level_pos (bot_not_values _) (values_bound (anchor_bound X a)) hCne hi
  have hspare : σ (LadderScalarRendering.level (LadderScalarRendering.values (fields X 2 a))
      ceil rungs) = leafSup I X T hA hB hC p := by
    have h := source_spare I X T hA hB hC a
    rw [source_ladder, SupportLadderRows.image, SupportLadderRows.index_leaf,
      FiniteProfileControllers.cut_refl] at h
    rw [h]
    exact read_ceiling I X T hA hB hC hread hmax
  have hread' : ∀ v : Pt, σ (SupportLadderRows.image ranks₁ (baseAnchor X a)
      (LadderScalarRendering.level (LadderScalarRendering.values (fields X 2 a)) ceil) v) =
      min (p (ladderAt I X T hA hB hC v)) (leafSup I X T hA hB hC p) := fun v => by
    rw [← source_ladder]
    exact hread _
  have hrefl := SupportLadderRows.bottom_reflection_image (rank_le_rungs I X) (rungs_pos I)
    (ladder_lawful I X T hA hB hC hp) (baseAnchor X a) h0 hf hne hread' hspare
    (shadow (baseAnchor X a) f)
  rw [SupportLadderRows.image, index_shadow_self, baseAnchor_ranks, field_readback] at hrefl
  exact hrefl.mp

/-- **The recognized complete vector is admitted at grade two.** -/
theorem exists_admitted (hp : RespectsSemanticsBelow Rows (A, 2) p)
    (hmax : p (leafAt I X T hA hB hC a) = leafSup I X T hA hB hC p) :
    ∃ S : State I.right.scheme I.left.scheme, Admitted X 2 S ∧
      ∀ f, S.profile f = min (shadowSup I X T hA hB hC p f) (leafSup I X T hA hB hC p) := by
  by_cases hne : leafSup I X T hA hB hC p = ⊥
  · exact exists_zero_admitted I X T hA hB hC hne
  refine ⟨(state X a).map σ, ?_, fun f => ?_⟩
  · refine Admitted.map_on_profile X (state_admitted X a) hσ (by decide) fun f hz => ?_
    rw [state_profile] at hz ⊢
    exact bottom_reflection I X T hA hB hC hσ hread hp hmax hne f hz
  · rw [State.profile_map, state_profile]
    exact recognition I X T hA hB hC hσ hread f

end Chart

/-- Grade-two original cells are read exactly: availability puts them below a leaf. -/
theorem present_readback_of_grade_two (hp : RespectsSemanticsBelow Rows (A, 2) p)
    {a : Catalogue X 2} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop 2) σ)
    (hread : ∀ z : Occ, σ (src a z.1) = min (p z) (leafSup I X T hA hB hC p))
    (d : Cell I.boundary) (hd : GradedLe (I.boundary.cell d) (A, 2))
    (hg : I.boundary.grade d = 2) :
    p (originalAt I X T hA hB hC d hd) =
      min (shadowSup I X T hA hB hC p (GrowthOrderedBase.field I d))
        (leafSup I X T hA hB hC p) := by
  rw [← present_readback I X T hA hB hC hσ hread d hd]
  symm
  apply min_eq_left
  have hgrade : gradeΩ (originalAt I X T hA hB hC d hd).1 =
      gradeΩ (leafAt I X T hA hB hC a).1 := by
    rw [grade_leafAt]
    change (cellΩ (GrowthPaddedSuccessor.original I X T hA hB hC d)).2 = 2
    rw [GrowthPaddedSuccessor.original_index]
    exact hg
  obtain ⟨e, he, hle⟩ := hp.availability (originalAt I X T hA hB hC d hd)
    (leafAt I X T hA hB hC a) (by
      change CellScheme.scope Ωc (originalAt I X T hA hB hC d hd).1 ⊆
        (cellΩ (leafAt I X T hA hB hC a).1).1
      rw [leafAt, GrowthPaddedSuccessor.leaf_index]
      exact (originalAt I X T hA hB hC d hd).2.1) hgrade
  obtain ⟨b, hb⟩ := eq_leaf_of_index I X T hA hB hC e.1
    (he.trans (GrowthPaddedSuccessor.leaf_index I X T hA hB hC a))
  have heb : e = leafAt I X T hA hB hC b := Subtype.ext hb
  rw [heb] at hle
  exact hle.trans (le_leafSup I X T hA hB hC p b)

/-- **The headline**: an arbitrary lawful section of the one-scope growth successor rows is
recognized by its maximal leaf chart — complete-field recognition on every field, finite bottom
reflection when the leaf maximum is positive, an admitted complete vector, and the readouts. -/
theorem recognize (hp : RespectsSemanticsBelow Rows (A, 2) p) :
    ∃ (a : Catalogue X 2) (σ : ExtOrd → ExtOrd), Witness (gTop 2) σ ∧
      p (leafAt I X T hA hB hC a) = leafSup I X T hA hB hC p ∧
      (∀ z : Occ, σ (src a z.1) = min (p z) (leafSup I X T hA hB hC p)) ∧
      (∀ f, σ (fields X 2 a f) =
        min (shadowSup I X T hA hB hC p f) (leafSup I X T hA hB hC p)) ∧
      (leafSup I X T hA hB hC p ≠ ⊥ → ∀ f, σ (fields X 2 a f) = ⊥ → fields X 2 a f = ⊥) ∧
      leafSup I X T hA hB hC p ≤ spareSup I X T hA hB hC p := by
  obtain ⟨a, σ, hσ, hmax, -, hread⟩ := exists_leaf_chart I X T hA hB hC hp
  exact ⟨a, σ, hσ, hmax, hread, recognition I X T hA hB hC hσ hread,
    fun hne => bottom_reflection I X T hA hB hC hσ hread hp hmax hne,
    leafSup_le_spareSup I X T hA hB hC hread hmax⟩

end
end VaughtConjecture.Knight.GrowthLeafRecognition
