/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthMixedRestriction
public import VaughtConjecture.Knight.LiftingCalculus

/-! # The grade-one mixed case on the replicated growth carrier

On the replicated growth carrier over **any** installed layer `P` (the grade-one lower domain is
the literal padded base on every layer, through `P.baseMap`), for an eligible mixed scope `U`
(`U = A` or `Mixed B C U`, `U` in the plan) and an **arbitrary** lawful section `p` below
`(U, 1)`:

* **Recognition** (`exists_spare_chart`, `shadowSup_eq_spare`, `original_readback_one`): the
  maximal spare copy at `U` carries a chart `τ` through grade one reading every padded copy
  exactly and every present original as the rank-coded source of its field; the uncapped
  complete-field vector `B_p f` is `τ (source rungs (rank_a f))` on every field, present, hidden
  or future.
* **Extension** (`extension`, `extension_lawful`, `extension_original`, `extension_auxiliary`,
  `extension_restrict`): the section `τ ∘ ladderRow (spare a)` on the padded base — hidden
  originals receive their recognized field values, every auxiliary receives the value of its
  actual `U`-copy — is lawful on the base (`RelativeLadderLayer.ladder_respects` transported
  by finite bottom reflection), hence on `P` (`base_respects`), hence duplicated on the whole
  replicated carrier (`ScopeReplicationLifting.duplicate_lawful`); it restricts to `p` literally.
* **Uniqueness** (`eq_of_restriction`): two lawful sections below `(A, 1)` agreeing on the
  `U`-copies agree everywhere: auxiliaries by `ScopeReplicationRestriction.auxiliary_eq`,
  originals through the full-scope recognition of each.
* **The capped lift** (`cappedLift`, `cappedLift_built`): `ExtensionInjectivity` gives
  `CoatomBoundaryExtension.CappedLift` for `(U, 1) ≤ (A, 1)` at every permitted cap, bottom and
  top included, on every installed layer and in particular on every built carrier.

The zero section, literal top, unused rungs and long tips are covered: nothing is assumed of `p`
beyond lawfulness, and no admission or activation hypothesis enters. -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GrowthMixedGradeOne

open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
open SupportLadderRows LadderScalarRendering SharpWitnessComposition
open GrowthPaddedContract ScopeReplicationCarrier

noncomputable section

theorem one_le_card {ι : Type*} {A B C U : Finset ι} (hA : 2 ≤ A.card)
    (hm : U = A ∨ Mixed B C U) : 1 ≤ U.card := by
  rcases hm with rfl | hm
  · omega
  · exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr
      (fun h => hm.1 (h ▸ Finset.empty_subset _)))

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  {k : ℕ} (P : Layer I X T hA hB hC k)

local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)
local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)
local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)
local notation "spare" => SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I)
local notation "Base" => GrowthPaddedContract.base I X T hA hB hC
local notation "BaseRows" => GrowthPaddedContract.baseRows I X T hA hB hC
local notation "Carrier" => GrowthReplicatedRows.carrier P
local notation "Rows" => GrowthReplicatedRows.rows P
local notation "eraseP" => GrowthReplicatedRows.erase P
local notation "coverP" => GrowthReplicatedRows.proper_covered P
local notation "addedB" => RelativeLadderLayer.added I.boundary (GrowthLeafRecognition.card_pos hA)
local notation "oldB" => RelativeLadderLayer.old I.boundary (GrowthLeafRecognition.card_pos hA)
local notation "ladderRow₁" =>
  RelativeLadderLayer.ladderRow I.boundary (GrowthLeafRecognition.card_pos hA)
    (GrowthOrderedBase.field I) (fields X 1)

/-! ## The grade-one geometry of an installed layer -/

theorem base_added_cell (v : Pt) : CellScheme.cell Base (addedB v) = (A, 1) :=
  RelativeLadderLayer.added_index I.boundary (GrowthLeafRecognition.card_pos hA) v

theorem base_old_cell (d : Cell I.boundary) : CellScheme.cell Base (oldB d) = I.boundary.cell d :=
  RelativeLadderLayer.old_index I.boundary (GrowthLeafRecognition.card_pos hA) d

theorem carrier_added_cell (v : Pt) : P.carrier.cell (P.baseMap (addedB v)) = (A, 1) :=
  (P.base_index _).trans (base_added_cell I X T hA hB hC v)

theorem carrier_old_cell (d : Cell I.boundary) :
    P.carrier.cell (P.baseMap (oldB d)) = I.boundary.cell d :=
  (P.base_index _).trans (base_old_cell I X T hA hB hC d)

/-- Every cell of grade at most one is a base cell. -/
theorem eq_baseMap_of_grade_le_one (c : Cell P.carrier) (hc : P.carrier.grade c ≤ 1) :
    ∃ b, c = P.baseMap b := by
  rcases P.cases c with h | ⟨_, hg, _⟩
  · exact h
  · omega

/-- Every full-scope grade-one cell is the image of a padded point. -/
theorem eq_added_of_full_one (c : Cell P.carrier) (hc : P.carrier.cell c = (A, 1)) :
    ∃ v : Pt, c = P.baseMap (addedB v) := by
  obtain ⟨b, rfl⟩ := eq_baseMap_of_grade_le_one I X T hA hB hC P c
    (by change (P.carrier.cell _).2 ≤ 1; rw [hc])
  rcases RelativeLadderLayer.cell_cases I.boundary (GrowthLeafRecognition.card_pos hA) b with
    ⟨d, rfl⟩ | ⟨v, rfl⟩
  · exfalso
    apply GrowthOrderedBase.proper I hB hC d
    exact (congrArg Prod.fst (carrier_old_cell I X T hA hB hC P d)).symm.trans
      (congrArg Prod.fst hc)
  · exact ⟨v, rfl⟩

/-! ## Occurrences at an eligible mixed scope -/

variable (U : Finset ι) (hU : U ∈ P.carrier.plan) (hm : U = A ∨ Mixed B C U)

theorem scope_added (v : Pt) : P.carrier.scope (P.baseMap (addedB v)) = A := by
  change (P.carrier.cell _).1 = A
  rw [carrier_added_cell]

theorem grade_added (v : Pt) : P.carrier.grade (P.baseMap (addedB v)) = 1 := by
  change (P.carrier.cell _).2 = 1
  rw [carrier_added_cell]

include hm in
theorem grade_added_le (v : Pt) : P.carrier.grade (P.baseMap (addedB v)) ≤ U.card := by
  rw [grade_added]; exact one_le_card hA hm

/-- The copy at `U` of a padded point. -/
def ladderAt (v : Pt) : CellScheme.below Carrier (U, 1) :=
  ⟨atScope P.carrier B C U hU hm (P.baseMap (addedB v)) (scope_added I X T hA hB hC P v)
      (grade_added_le I X T hA hB hC P U hm v), by
    rw [atScope_index, grade_added]
    exact GradedLe.refl _⟩

theorem ladder_index (v : Pt) :
    CellScheme.cell Carrier (ladderAt I X T hA hB hC P U hU hm v).1 = (U, 1) := by
  unfold ladderAt
  rw [atScope_index, grade_added]

theorem erase_ladder (v : Pt) :
    eraseP (ladderAt I X T hA hB hC P U hU hm v).1 = P.baseMap (addedB v) :=
  erase_atScope P.carrier B C U hU hm (P.baseMap (addedB v)) (scope_added I X T hA hB hC P v)
    (grade_added_le I X T hA hB hC P U hm v)

/-- A padded copy below a padded copy. -/
def ladderBelow (c v : Pt) :
    CellScheme.below Carrier (CellScheme.cell Carrier (ladderAt I X T hA hB hC P U hU hm c).1) :=
  ⟨(ladderAt I X T hA hB hC P U hU hm v).1, by
    rw [ladder_index, ladder_index]; exact GradedLe.refl _⟩

/-- The inherited row of a padded copy at a padded copy is the actual ladder row. -/
theorem row_ladder (c v : Pt) :
    Semantics.E Rows (ladderAt I X T hA hB hC P U hU hm c).1
      (ladderBelow I X T hA hB hC P U hU hm c v) = SupportLadderRows.row ranks₁ c v := by
  have hv : GradedLe (CellScheme.cell Base (addedB v)) (CellScheme.cell Base (addedB c)) := by
    rw [base_added_cell, base_added_cell]; exact GradedLe.refl _
  have h1 : Semantics.E Rows (ladderAt I X T hA hB hC P U hU hm c).1
      (ladderBelow I X T hA hB hC P U hU hm c v) =
      P.rows.E (P.baseMap (addedB c)) ⟨P.baseMap (⟨addedB v, hv⟩ :
        CellScheme.below Base (CellScheme.cell Base (addedB c))).1,
        by simpa only [P.base_index] using hv⟩ :=
    P.rows.E_congr (erase_ladder I X T hA hB hC P U hU hm c)
      (erase_ladder I X T hA hB hC P U hU hm v)
  rw [h1, P.base_row (addedB c) ⟨addedB v, hv⟩]
  have h2 : ladderRow₁ c (addedB v) = SupportLadderRows.row ranks₁ c v := by
    change SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ c)
      (RelativeLadderLayer.rankIndex I.boundary (GrowthLeafRecognition.card_pos hA)
        (GrowthOrderedBase.field I) (fields X 1) (SupportLadderRows.parent c) (addedB v)) = _
    rw [RelativeLadderLayer.rankIndex_added]
    rfl
  exact (RelativeLadderLayer.row_added I.boundary I.rows (GrowthLeafRecognition.card_pos hA)
    (GrowthOrderedBase.field I) (fields X 1) (GrowthOrderedBase.proper I hB hC) c
    ⟨addedB v, hv⟩).trans h2

/-- The inherited row of a padded copy at a present original is the rank-coded source. -/
theorem row_ladder_original (v : Pt) (z : CellScheme.below Carrier (U, 1)) (d : Cell I.boundary)
    (hz : eraseP z.1 = P.baseMap (oldB d)) :
    Semantics.E Rows (ladderAt I X T hA hB hC P U hU hm v).1
      ⟨z.1, by rw [ladder_index]; exact z.2⟩ =
      SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ v)
        (ranks₁ (SupportLadderRows.parent v) (GrowthOrderedBase.field I d)) := by
  have hgd : I.boundary.grade d ≤ 1 := by
    have he := erase_grade P.carrier B C z.1
    change P.carrier.grade (eraseP z.1) = CellScheme.grade Carrier z.1 at he
    rw [hz] at he
    have h1 := congrArg Prod.snd (carrier_old_cell I X T hA hB hC P d)
    change P.carrier.grade (P.baseMap (oldB d)) = I.boundary.grade d at h1
    have h2 : CellScheme.grade Carrier z.1 ≤ 1 := z.2.2
    omega
  have hd : GradedLe (CellScheme.cell Base (oldB d)) (CellScheme.cell Base (addedB v)) := by
    rw [base_old_cell, base_added_cell]
    exact ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan d), hgd⟩
  have h1 : Semantics.E Rows (ladderAt I X T hA hB hC P U hU hm v).1
      ⟨z.1, by rw [ladder_index]; exact z.2⟩ =
      P.rows.E (P.baseMap (addedB v)) ⟨P.baseMap (⟨oldB d, hd⟩ :
        CellScheme.below Base (CellScheme.cell Base (addedB v))).1,
        by simpa only [P.base_index] using hd⟩ :=
    P.rows.E_congr (erase_ladder I X T hA hB hC P U hU hm v) hz
  rw [h1, P.base_row (addedB v) ⟨oldB d, hd⟩]
  have h2 : ladderRow₁ v (oldB d) = SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ v)
      (ranks₁ (SupportLadderRows.parent v) (GrowthOrderedBase.field I d)) := by
    change SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ v)
      (RelativeLadderLayer.rankIndex I.boundary (GrowthLeafRecognition.card_pos hA)
        (GrowthOrderedBase.field I) (fields X 1) (SupportLadderRows.parent v) (oldB d)) = _
    rw [RelativeLadderLayer.rankIndex_old]
  exact (RelativeLadderLayer.row_added I.boundary I.rows (GrowthLeafRecognition.card_pos hA)
    (GrowthOrderedBase.field I) (fields X 1) (GrowthOrderedBase.proper I hB hC) v
    ⟨oldB d, hd⟩).trans h2

/-! ## Recognition at grade one -/

variable {p : CellScheme.below (GrowthReplicatedRows.carrier P) (U, 1) → ExtOrd}

theorem ladder_lawful (hp : RespectsSemanticsBelow Rows (U, 1) p) :
    Lawful ranks₁ (fun v => p (ladderAt I X T hA hB hC P U hU hm v)) := by
  constructor
  · intro v
    have hv := hp.orderly (ladderAt I X T hA hB hC P U hU hm v)
    change p _ = extVisibilityReplace (p _) (CellScheme.cell Carrier _).2
      (CellScheme.cell Carrier _).2 at hv
    rw [ladder_index] at hv
    exact hv.symm
  · intro c
    have ht := (hp.locality (ladderAt I X T hA hB hC P U hU hm c)).reindex
      (ladderBelow I X T hA hB hC P U hU hm c)
    exact transformsTo_congr
      (funext fun v => congrArg Prod.snd (ladder_index I X T hA hB hC P U hU hm v))
      (funext fun v => row_ladder I X T hA hB hC P U hU hm c v) rfl ht

variable (p)

/-- The maximum of `p` over the copies at `U` of the shadows of a field. -/
def shadowSup (f : Fld) : ExtOrd :=
  (Finset.univ : Finset (Catalogue X 1)).sup fun b =>
    p (ladderAt I X T hA hB hC P U hU hm (shadow b f))

/-- The maximum of `p` over the copies at `U` of the spare rungs. -/
def spareSup : ExtOrd :=
  (Finset.univ : Finset (Catalogue X 1)).sup fun b =>
    p (ladderAt I X T hA hB hC P U hU hm (spare b))

variable {p}

theorem ladder_le_spareSup (hp : RespectsSemanticsBelow Rows (U, 1) p) (v : Pt) :
    p (ladderAt I X T hA hB hC P U hU hm v) ≤ spareSup I X T hA hB hC P U hU hm p :=
  ((ladder_lawful I X T hA hB hC P U hU hm hp).le_parent
    (GrowthLeafRecognition.rank_le_rungs I X) (GrowthLeafRecognition.rungs_pos I) v).trans
    (Finset.le_sup (f := fun b => p (ladderAt I X T hA hB hC P U hU hm (spare b)))
      (Finset.mem_univ _))

/-- Availability bounds every grade-one value at `U` by the spare maximum. -/
theorem grade_one_le (hp : RespectsSemanticsBelow Rows (U, 1) p)
    (z : CellScheme.below Carrier (U, 1)) (hz : CellScheme.grade Carrier z.1 = 1) :
    p z ≤ spareSup I X T hA hB hC P U hU hm p := by
  let a₀ := GrowthLeafRecognition.zeroMember I X 1 le_rfl
  obtain ⟨w, hw, hzw⟩ := hp.availability z (ladderAt I X T hA hB hC P U hU hm (spare a₀))
    (by change CellScheme.scope Carrier z.1 ⊆ (CellScheme.cell Carrier _).1
        rw [ladder_index]; exact z.2.1)
    (hz.trans (congrArg Prod.snd (ladder_index I X T hA hB hC P U hU hm _)).symm)
  have hw' := hw.trans (ladder_index I X T hA hB hC P U hU hm _)
  have hei := ScopeReplicationCharts.erase_index P.carrier B C coverP hm w.1 hw'
  obtain ⟨v, hv⟩ := eq_added_of_full_one I X T hA hB hC P _ hei
  have he : p w = p (ladderAt I X T hA hB hC P U hU hm v) :=
    GrowthReplicatedRows.copy_eq P hp w _
      (by change (CellScheme.cell Carrier w.1).1 ⊆ (CellScheme.cell Carrier _).1
          rw [hw', ladder_index])
      (hv.trans (erase_ladder I X T hA hB hC P U hU hm v).symm)
  exact hzw.trans (he.trans_le (ladder_le_spareSup I X T hA hB hC P U hU hm hp v))

/-- **The maximal spare chart at `U`**: it reads every padded copy exactly and every present
original as the rank-coded source of its field. -/
theorem exists_spare_chart (hp : RespectsSemanticsBelow Rows (U, 1) p) :
    ∃ (a : Catalogue X 1) (τ : ExtOrd → ExtOrd), Witness (gTop 1) τ ∧
      p (ladderAt I X T hA hB hC P U hU hm (spare a)) = spareSup I X T hA hB hC P U hU hm p ∧
      (∀ x, τ x ≤ spareSup I X T hA hB hC P U hU hm p) ∧
      (∀ v : Pt, τ (SupportLadderRows.row ranks₁ (spare a) v) =
        p (ladderAt I X T hA hB hC P U hU hm v)) ∧
      ∀ (z : CellScheme.below Carrier (U, 1)) (d : Cell I.boundary),
        eraseP z.1 = P.baseMap (oldB d) →
        τ (SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field I d))) = p z := by
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Catalogue X 1))
    (fun b => p (ladderAt I X T hA hB hC P U hU hm (spare b)))
    ⟨GrowthLeafRecognition.zeroMember I X 1 le_rfl, Finset.mem_univ _⟩
  let c := ladderAt I X T hA hB hC P U hU hm (spare a)
  have hpc : p c = spareSup I X T hA hB hC P U hU hm p :=
    le_antisymm (Finset.le_sup (f := fun b => p (ladderAt I X T hA hB hC P U hU hm (spare b)))
      (Finset.mem_univ a)) (Finset.sup_le hmax)
  let self : CellScheme.below Carrier (CellScheme.cell Carrier c.1) := ⟨c.1, GradedLe.refl _⟩
  obtain ⟨τ, hτ, hb, hr⟩ := exists_bounded_exact_capped_witness
    (c := self) (fun d => d.2.2) (hp.orderly c).symm (hp.locality c)
  have hgrade : CellScheme.grade Carrier c.1 = 1 :=
    congrArg Prod.snd (ladder_index I X T hA hB hC P U hU hm _)
  refine ⟨a, τ, hgrade ▸ hτ, hpc, fun x => (hb x).trans_eq hpc, ?_, ?_⟩
  · intro v
    have h := hr (ladderBelow I X T hA hB hC P U hU hm (spare a) v)
    rw [row_ladder] at h
    exact h.trans (min_eq_left
      ((ladder_le_spareSup I X T hA hB hC P U hU hm hp v).trans_eq hpc.symm))
  · intro z d hz
    have hg : CellScheme.grade Carrier z.1 = 1 := by
      have h1 : CellScheme.grade Carrier z.1 ≤ 1 := z.2.2
      have h2 := CellScheme.grade_pos Carrier z.1
      omega
    let e : CellScheme.below Carrier (CellScheme.cell Carrier c.1) :=
      ⟨z.1, by rw [ladder_index]; exact z.2⟩
    have h := hr e
    rw [row_ladder_original I X T hA hB hC P U hU hm (spare a) z d hz,
      SupportLadderRows.ceiling_leaf] at h
    exact h.trans (min_eq_left
      ((grade_one_le I X T hA hB hC P U hU hm hp z hg).trans_eq hpc.symm))

section Chart

variable {a : Catalogue X 1} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop 1) τ)
  (hread : ∀ v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1),
    τ (SupportLadderRows.row (RelativeLadderLayer.ranks (fields X 1))
      (SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I) a) v) =
        p (ladderAt I X T hA hB hC P U hU hm v))

include hτ hread

/-- **Uncapped complete-field recognition at `U`**, on every field. -/
theorem shadowSup_eq_spare (f : Fld) :
    shadowSup I X T hA hB hC P U hU hm p f =
      τ (SupportLadderRows.source rungs (ranks₁ a f)) := by
  have he := SupportLadderRows.readout_image (H := rungs)
    (GrowthLeafRecognition.rank_le_rungs I X) a (SupportLadderRows.source_mono rungs) f
  simp only [SupportLadderRows.readout] at he
  rw [show Fintype.ofFinite (Catalogue X 1) = (inferInstance : Fintype (Catalogue X 1)) from
    Subsingleton.elim _ _] at he
  rw [← he, Finset.apply_sup_eq_sup_comp_of_linearOrder τ hτ.mono hτ.bot, shadowSup]
  congr 1
  funext b
  rw [Function.comp_apply, ← hread, GrowthSpareRecognition.row_spare]
  rfl

/-- **Finite bottom reflection** on every ladder value of the maximal spare, when `M₁ p ≠ ⊥`. -/
theorem spare_bottom_reflection (hp : RespectsSemanticsBelow Rows (U, 1) p)
    (hmax : p (ladderAt I X T hA hB hC P U hU hm (spare a)) =
      spareSup I X T hA hB hC P U hU hm p)
    (hne : spareSup I X T hA hB hC P U hU hm p ≠ ⊥) (v : Pt) :
    τ (SupportLadderRows.row ranks₁ (spare a) v) = ⊥ ↔
      SupportLadderRows.row ranks₁ (spare a) v = ⊥ := by
  have : Nonempty (Catalogue X 1) := ⟨GrowthLeafRecognition.zeroMember I X 1 le_rfl⟩
  have hread' (w : Pt) : τ (SupportLadderRows.row ranks₁ (spare a) w) =
      min (p (ladderAt I X T hA hB hC P U hU hm w)) (spareSup I X T hA hB hC P U hU hm p) := by
    rw [hread, min_eq_left (ladder_le_spareSup I X T hA hB hC P U hU hm hp w)]
  have hdiag : τ (SupportLadderRows.row ranks₁ (spare a) (spare a)) =
      spareSup I X T hA hB hC P U hU hm p := (hread _).trans hmax
  exact SupportLadderRows.bottom_reflection (GrowthLeafRecognition.rank_le_rungs I X)
    (GrowthLeafRecognition.rungs_pos I) (ladder_lawful I X T hA hB hC P U hU hm hp)
    (spare a) hτ.bot hne hread' hdiag v

end Chart

/-- **Exact readback of present originals at `U`**: uncapped. -/
theorem original_readback_one (hp : RespectsSemanticsBelow Rows (U, 1) p)
    (z : CellScheme.below Carrier (U, 1)) (d : Cell I.boundary)
    (hz : eraseP z.1 = P.baseMap (oldB d)) :
    p z = shadowSup I X T hA hB hC P U hU hm p (GrowthOrderedBase.field I d) := by
  obtain ⟨a, τ, hτ, -, -, hread, horig⟩ := exists_spare_chart I X T hA hB hC P U hU hm hp
  exact (horig z d hz).symm.trans
    (shadowSup_eq_spare I X T hA hB hC P U hU hm hτ hread _).symm

/-! ## The lawful extension to the full scope -/

section Extension

variable {a : Catalogue X 1} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop 1) τ)
  (hp : RespectsSemanticsBelow (GrowthReplicatedRows.rows P) (U, 1) p)
  (hmax : p (ladderAt I X T hA hB hC P U hU hm (SupportLadderRows.leaf
    (GrowthLeafRecognition.rungs_pos I) a)) = spareSup I X T hA hB hC P U hU hm p)
  (hb : ∀ x, τ x ≤ spareSup I X T hA hB hC P U hU hm p)
  (hread : ∀ v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1),
    τ (SupportLadderRows.row (RelativeLadderLayer.ranks (fields X 1))
      (SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I) a) v) =
        p (ladderAt I X T hA hB hC P U hU hm v))

include hτ hp hmax hb hread

/-- The chart transports the spare's whole ladder row on the padded base. -/
theorem base_section_lawful :
    RespectsSemanticsBelow BaseRows (A, 1) (fun d => τ (ladderRow₁ (spare a) d.1)) := by
  have hlad := RelativeLadderLayer.ladder_respects I.boundary I.rows
    (GrowthLeafRecognition.card_pos hA) (GrowthOrderedBase.field I) (fields X 1)
    (GrowthOrderedBase.proper I hB hC) (GrowthOrderedBase.anchor_lawful I X T) (spare a)
  by_cases hne : spareSup I X T hA hB hC P U hU hm p = ⊥
  · have hz : ∀ x, τ x = ⊥ := fun x => le_bot_iff.mp ((hb x).trans_eq hne)
    simp only [hz]
    exact respectsBelow_bot _ (A, 1)
  · refine map_respects_of_bottom_reflection hlad (fun d => d.2.2) (boundedMap_of_witness hτ)
      fun d => ?_
    rcases RelativeLadderLayer.cell_cases I.boundary (GrowthLeafRecognition.card_pos hA) d.1 with
      ⟨e, he⟩ | ⟨v, hv⟩
    · rw [he, GrowthSpareRecognition.ladderRow_spare_old I X hA a e,
        ← GrowthLeafRecognition.index_shadow_self I X a, ← GrowthSpareRecognition.row_spare I X a]
      exact spare_bottom_reflection I X T hA hB hC P U hU hm hτ hread hp hmax hne _
    · rw [hv, GrowthSpareRecognition.ladderRow_spare_added I X hA a v]
      exact spare_bottom_reflection I X T hA hB hC P U hU hm hτ hread hp hmax hne v

end Extension

/-- The extension's values on the installed layer: the chart's reading of the spare's row at
base cells, `⊥` elsewhere (no other cell lies below grade one). -/
def layerSection (a : Catalogue X 1) (τ : ExtOrd → ExtOrd) (c : Cell P.carrier) : ExtOrd := by
  classical
  exact if h : ∃ b, c = P.baseMap b then τ (ladderRow₁ (spare a) h.choose) else ⊥

theorem layerSection_baseMap (a : Catalogue X 1) (τ : ExtOrd → ExtOrd) (b : Cell Base) :
    layerSection I X T hA hB hC P a τ (P.baseMap b) = τ (ladderRow₁ (spare a) b) := by
  classical
  unfold layerSection
  split_ifs with h
  · exact congrArg (fun x => τ (ladderRow₁ (spare a) x)) (P.base_mono.injective h.choose_spec.symm)
  · exact absurd ⟨b, rfl⟩ h

section Extension

variable {a : Catalogue X 1} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop 1) τ)
  (hp : RespectsSemanticsBelow (GrowthReplicatedRows.rows P) (U, 1) p)
  (hmax : p (ladderAt I X T hA hB hC P U hU hm (SupportLadderRows.leaf
    (GrowthLeafRecognition.rungs_pos I) a)) = spareSup I X T hA hB hC P U hU hm p)
  (hb : ∀ x, τ x ≤ spareSup I X T hA hB hC P U hU hm p)
  (hread : ∀ v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1),
    τ (SupportLadderRows.row (RelativeLadderLayer.ranks (fields X 1))
      (SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I) a) v) =
        p (ladderAt I X T hA hB hC P U hU hm v))

include hτ hp hmax hb hread

/-- The layer section is lawful through grade one on the installed layer. -/
theorem layerSection_lawful :
    RespectsSemanticsBelow P.rows (A, 1) (fun d => layerSection I X T hA hB hC P a τ d.1) := by
  have hbase := base_section_lawful I X T hA hB hC P U hU hm hτ hp hmax hb hread
  have h := P.base_respects (addedB (spare a)) (layerSection I X T hA hB hC P a τ)
  have hrhs : RespectsSemanticsBelow BaseRows (CellScheme.cell Base (addedB (spare a)))
      (fun d => layerSection I X T hA hB hC P a τ (P.baseMap d.1)) := by
    have hc := GradeCutLayerRows.cast_respects Base BaseRows
      (base_added_cell I X T hA hB hC (spare a)).symm hbase
    have he : (fun d : CellScheme.below Base (CellScheme.cell Base (addedB (spare a))) =>
        τ (ladderRow₁ (spare a) d.1)) =
        fun d => layerSection I X T hA hB hC P a τ (P.baseMap d.1) :=
      funext fun d => (layerSection_baseMap I X T hA hB hC P a τ d.1).symm
    rw [← he]
    exact hc
  have hlhs := h.mpr hrhs
  have hc := GradeCutLayerRows.cast_respects P.carrier P.rows
    (carrier_added_cell I X T hA hB hC P (spare a)) hlhs
  exact hc

end Extension

/-! ## The extension on the replicated carrier -/

/-- **The extension**: the layer section duplicated to every scope copy. -/
def extension (a : Catalogue X 1) (τ : ExtOrd → ExtOrd) :
    CellScheme.below Carrier (A, 1) → ExtOrd :=
  ScopeReplicationLifting.duplicate P.carrier B C (fun d => layerSection I X T hA hB hC P a τ d.1)

theorem extension_val (a : Catalogue X 1) (τ : ExtOrd → ExtOrd)
    (z : CellScheme.below Carrier (A, 1)) :
    extension I X T hA hB hC P a τ z = layerSection I X T hA hB hC P a τ (eraseP z.1) := rfl

/-- Hidden and present originals receive the chart's reading of their rank-coded field. -/
theorem extension_original (a : Catalogue X 1) (τ : ExtOrd → ExtOrd)
    (z : CellScheme.below Carrier (A, 1)) (d : Cell I.boundary)
    (hz : eraseP z.1 = P.baseMap (oldB d)) :
    extension I X T hA hB hC P a τ z =
      τ (SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field I d))) := by
  rw [extension_val, hz, layerSection_baseMap, GrowthSpareRecognition.ladderRow_spare_old I X hA]

/-- Every auxiliary copy receives the chart's reading of its prototype's ladder row. -/
theorem extension_auxiliary (a : Catalogue X 1) (τ : ExtOrd → ExtOrd)
    (z : CellScheme.below Carrier (A, 1)) (v : Pt) (hz : eraseP z.1 = P.baseMap (addedB v)) :
    extension I X T hA hB hC P a τ z = τ (SupportLadderRows.row ranks₁ (spare a) v) := by
  rw [extension_val, hz, layerSection_baseMap, GrowthSpareRecognition.ladderRow_spare_added I X hA]

theorem A_mem_plan : A ∈ P.carrier.plan := by
  have h := P.carrier.scope_mem_plan
    (P.baseMap (addedB (spare (GrowthLeafRecognition.zeroMember I X 1 le_rfl))))
  rwa [scope_added] at h

include hU in
theorem le_full : GradedLe ((U, 1) : Finset ι × ℕ) (A, 1) :=
  ⟨P.carrier.isPlan.subset_of_mem hU, le_rfl⟩

section Extension

variable {a : Catalogue X 1} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop 1) τ)
  (hp : RespectsSemanticsBelow (GrowthReplicatedRows.rows P) (U, 1) p)
  (hmax : p (ladderAt I X T hA hB hC P U hU hm (SupportLadderRows.leaf
    (GrowthLeafRecognition.rungs_pos I) a)) = spareSup I X T hA hB hC P U hU hm p)
  (hb : ∀ x, τ x ≤ spareSup I X T hA hB hC P U hU hm p)
  (hread : ∀ v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1),
    τ (SupportLadderRows.row (RelativeLadderLayer.ranks (fields X 1))
      (SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I) a) v) =
        p (ladderAt I X T hA hB hC P U hU hm v))
  (horig : ∀ (z : CellScheme.below (GrowthReplicatedRows.carrier P) (U, 1)) (d : Cell I.boundary),
    GrowthReplicatedRows.erase P z.1 = P.baseMap (RelativeLadderLayer.old I.boundary
      (GrowthLeafRecognition.card_pos hA) d) →
    τ (SupportLadderRows.source (RelativeLadderLayer.rungs (X := Field I.right.scheme
      I.left.scheme)) (RelativeLadderLayer.ranks (fields X 1) a (GrowthOrderedBase.field I d))) =
      p z)

include hτ hp hmax hb hread

/-- **The extension is lawful** through grade one on the whole replicated carrier. -/
theorem extension_lawful :
    RespectsSemanticsBelow Rows (A, 1) (extension I X T hA hB hC P a τ) :=
  ScopeReplicationLifting.duplicate_lawful P.carrier B C coverP P.rows
    (layerSection_lawful I X T hA hB hC P U hU hm hτ hp hmax hb hread)

omit hτ hmax hb in
include horig in
/-- **Literal retention**: the extension restricts to `p` on every occurrence below `(U, 1)`. -/
theorem extension_restrict (z : CellScheme.below Carrier (U, 1)) :
    extension I X T hA hB hC P a τ (CellScheme.below.mono (le_full I X T hA hB hC P U hU) z) =
      p z := by
  have hg : P.carrier.grade (eraseP z.1) ≤ 1 := by
    rw [erase_grade]; exact z.2.2
  obtain ⟨b, hb⟩ := eq_baseMap_of_grade_le_one I X T hA hB hC P _ hg
  rcases RelativeLadderLayer.cell_cases I.boundary (GrowthLeafRecognition.card_pos hA) b with
    ⟨d, rfl⟩ | ⟨v, rfl⟩
  · rw [extension_original I X T hA hB hC P a τ _ d hb]
    exact horig z d hb
  · rw [extension_auxiliary I X T hA hB hC P a τ _ v hb, hread]
    refine (GrowthReplicatedRows.copy_eq P hp z (ladderAt I X T hA hB hC P U hU hm v) ?_
      (hb.trans (erase_ladder I X T hA hB hC P U hU hm v).symm)).symm
    change CellScheme.scope Carrier z.1 ⊆ (CellScheme.cell Carrier _).1
    rw [ladder_index]
    exact z.2.1

end Extension

include hm in
/-- **Existence**: every lawful section below `(U, 1)` extends lawfully to `(A, 1)`. -/
theorem lawfulExtension :
    ExtensionInjectivity.LawfulExtension Rows (le_full I X T hA hB hC P U hU) := by
  intro p hp
  obtain ⟨a, τ, hτ, hmax, hb, hread, horig⟩ := exists_spare_chart I X T hA hB hC P U hU hm hp
  exact ⟨extension I X T hA hB hC P a τ,
    extension_lawful I X T hA hB hC P U hU hm hτ hp hmax hb hread,
    extension_restrict I X T hA hB hC P U hU hm hp hread horig⟩

/-! ## Uniqueness -/

include hm in
/-- **Restriction injectivity**: lawful sections below `(A, 1)` agreeing on the copies at `U`
agree everywhere — auxiliaries individually, originals through their full-scope recognition. -/
theorem eq_of_restriction {r r' : CellScheme.below Carrier (A, 1) → ExtOrd}
    (hr : RespectsSemanticsBelow Rows (A, 1) r) (hr' : RespectsSemanticsBelow Rows (A, 1) r')
    (hag : ∀ z : CellScheme.below Carrier (U, 1),
      r (CellScheme.below.mono (le_full I X T hA hB hC P U hU) z) =
        r' (CellScheme.below.mono (le_full I X T hA hB hC P U hU) z))
    (z : CellScheme.below Carrier (A, 1)) : r z = r' z := by
  have hAm := A_mem_plan I X T hA hB hC P
  have haux (w : CellScheme.below Carrier (A, 1)) (hw : P.carrier.scope (eraseP w.1) = A) :
      r w = r' w :=
    ScopeReplicationRestriction.auxiliary_eq P.carrier B C coverP P.rows hU hm
      (one_le_card hA hm) hAm (Or.inl rfl) (by omega)
      (P.carrier.isPlan.subset_of_mem hU) hr hr' hag w hw
  have hg : P.carrier.grade (eraseP z.1) ≤ 1 := by
    rw [erase_grade]; exact z.2.2
  obtain ⟨b, hb⟩ := eq_baseMap_of_grade_le_one I X T hA hB hC P _ hg
  rcases RelativeLadderLayer.cell_cases I.boundary (GrowthLeafRecognition.card_pos hA) b with
    ⟨d, rfl⟩ | ⟨v, rfl⟩
  · rw [original_readback_one I X T hA hB hC P A hAm (Or.inl rfl) hr z d hb,
      original_readback_one I X T hA hB hC P A hAm (Or.inl rfl) hr' z d hb]
    apply Finset.sup_congr rfl
    intro c _
    apply haux
    rw [erase_ladder]
    exact scope_added I X T hA hB hC P _
  · apply haux
    rw [hb]
    exact scope_added I X T hA hB hC P v

include hm in
theorem restrictionInjective :
    ExtensionInjectivity.RestrictionInjective Rows (le_full I X T hA hB hC P U hU) :=
  fun _ _ hr hr' hag => eq_of_restriction I X T hA hB hC P U hU hm hr hr' hag

/-! ## The grade-one mixed capped lift -/

include hm in
/-- One extension on the fixed installed layer preserves every compatible cap and ambient. -/
theorem allCapsExtension :
    ExtensionInjectivity.AllCapsExtension Rows (le_full I X T hA hB hC P U hU) :=
  ExtensionInjectivity.allCapsExtension_of_extension_injective
    (lawfulExtension I X T hA hB hC P U hU hm) (restrictionInjective I X T hA hB hC P U hU hm)

include hm in
/-- **The same-grade mixed capped lift at grade one**, on every installed layer, at every
permitted cap, bottom and top included. -/
theorem cappedLift :
    CoatomBoundaryExtension.CappedLift Rows (le_full I X T hA hB hC P U hU) :=
  (allCapsExtension I X T hA hB hC P U hU hm).cappedLift

/-- The lift on the built carrier of any height, for a plan scope. -/
theorem cappedLift_built (t : ℕ) (ht : t + 2 ≤ A.card) {V : Finset ι} (hV : V ∈ I.boundary.plan)
    (hmV : V = A ∨ Mixed B C V) :
    CoatomBoundaryExtension.CappedLift
      (GrowthReplicatedRows.rows (GrowthPaddedIteration.build I X T hA hB hC t ht))
      (le_full I X T hA hB hC (GrowthPaddedIteration.build I X T hA hB hC t ht) V
        (by rw [GrowthPaddedIteration.build_plan]; exact hV)) :=
  cappedLift I X T hA hB hC _ V (by rw [GrowthPaddedIteration.build_plan]; exact hV) hmV

end
end VaughtConjecture.Knight.GrowthMixedGradeOne
