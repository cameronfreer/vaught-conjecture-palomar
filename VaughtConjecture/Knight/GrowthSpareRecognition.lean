/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthLeafRecognition
public import VaughtConjecture.Knight.GradePrefixProjection
public import VaughtConjecture.Knight.RelativeLadderAmbient

/-! # Grade-one recognition from the maximal spare chart, and the two-grade projection

`GrowthLeafRecognition` recognizes the **capped** vector `min (B_p f) (M₂ p)` from the maximal
leaf chart.  The mixed extension needs the **uncapped** shadow vector `B_p f` at grade one:
grade-one values above `M₂ p` must survive literally.  This module supplies it on the same
installed rows, again for an arbitrary lawful section `p` below `(A, 2)`, and combines the two
grades.

* **The base restriction** (`oldAt`, `base_lawful`): `p` restricted to the checked padded base
  below `(A, 1)` is lawful for the base rows (the inherited rows are literal, availability at
  grade one stays inside the base).
* **The maximal spare chart** (`exists_spare_chart`, from `RelativeLadderLayer.exists_leaf_chart`
  on the base): a spare rung attaining `M₁ p` whose chart `τ` through grade one reads every
  padded point **exactly** (uncapped) and every present grade-one original as the rank-coded
  source of its field.
* **Uncapped recognition** (`shadowSup_eq_spare`): `B_p f = τ (source rungs (rank_a f))` for every
  complete field, present, hidden or future; hence `present_readback_of_grade_one`.
* **Finite bottom reflection** (`spare_bottom_reflection`) on the rank-coded values when
  `M₁ p ≠ ⊥`, from `SupportLadderRows.bottom_reflection` on the ladder restriction.
* **Lawfulness and admission of `B_p` at grade one** (`private_uncapped_lawful`,
  `donor_uncapped_lawful`, `uncapped_visible`, `uncapped_shared`, `admitted_one`): the rank-coded
  original vectors are lawful (`RelativeLadderLayer.rank_respects`) and the chart transports them
  by finite reflection; admission at grade one additionally needs the activation grade to lie
  above one (`1 < X.req.N`, explicit: the correctness clause is not transported by a grade-one
  chart, and grade one is below activation in the intended regime).
* **The two-grade hidden-original projection** (`gradeHeight`, `private_projection_lawful`,
  `donor_projection_lawful`, `two_grade_projection`): the section `d ↦ min (B_p (field d))
  (H (grade d))` with `H 1 = ⊤` and `H 2 = M₂ p` is lawful below grade two on each original
  scheme (`GradePrefixProjection.respectsBelow`, antitone heights), and every present original
  reads it exactly: grade-one values uncapped, grade-two values at the leaf maximum.

Everything stays on the actual one-scope carrier; replication, mixed extension and lifting are not
touched. -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GrowthSpareRecognition

open Transform Value ExtOrd Growth GrowthHigherSources GrowthPaddedSuccessor GrowthLeafRecognition
open SupportLadderRows LadderScalarRendering SharpWitnessComposition CappedDonor.Ref

noncomputable section

theorem one_le_two_index {ι : Type*} {A : Finset ι} : GradedLe ((A, 1) : Finset ι × ℕ) (A, 2) :=
  ⟨Finset.Subset.refl _, Nat.le_succ 1⟩

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
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)
local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)
local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)
local notation "lowerΩ" => LadderWeightedSuccessor.Input.lower (input I X T hA hB hC)
local notation "BaseRows" => LadderWeightedSuccessor.Input.lowerRows (input I X T hA hB hC)
local notation "Low" =>
  CellScheme.below (LadderWeightedSuccessor.Input.lower (input I X T hA hB hC)) (A, 1)
local notation "spare" => SupportLadderRows.leaf (rungs_pos I)

/-! ## The base restriction of an arbitrary lawful section -/

/-- A cell of the checked base below `(A, 1)` as an occurrence of the successor. -/
def oldAt (x : Low) : Occ :=
  ⟨GrowthPaddedSuccessor.old I X T hA hB hC x.1, by
    rw [cell_old]; exact x.2.trans one_le_two_index⟩

theorem cell_oldAt (x : Low) : cellΩ (oldAt I X T hA hB hC x).1 = CellScheme.cell lowerΩ x.1 :=
  cell_old I X T hA hB hC x.1

theorem grade_oldAt (x : Low) : gradeΩ (oldAt I X T hA hB hC x).1 = CellScheme.grade lowerΩ x.1 :=
  congrArg Prod.snd (cell_oldAt I X T hA hB hC x)

variable {p : CellScheme.below (carrier I X T hA hB hC) (A, 2) → ExtOrd}

/-- **The base restriction is lawful for the base rows.**  Inherited rows are literal; availability
at grade one stays inside the base since every index-`(A, 2)` occurrence is a leaf. -/
theorem base_lawful (hp : RespectsSemanticsBelow Rows (A, 2) p) :
    RespectsSemanticsBelow BaseRows (A, 1) (fun x => p (oldAt I X T hA hB hC x)) := by
  refine ⟨fun x => ?_, fun c => ?_, fun c v hs hg => ?_⟩
  · have h := hp.orderly (oldAt I X T hA hB hC x)
    change p _ = extVisibilityReplace (p _) (gradeΩ (oldAt I X T hA hB hC x).1)
      (gradeΩ (oldAt I X T hA hB hC x).1) at h
    rw [grade_oldAt] at h
    exact h
  · let e := SeparatedSourceLayerCarrier.ownerEquiv lowerΩ
      (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty))
      2 (by decide) hA (input I X T hA hB hC).separation c.1
    have ht := (hp.locality (oldAt I X T hA hB hC c)).reindex e
    have hg : ((fun d : CellScheme.below Ωc (cellΩ (oldAt I X T hA hB hC c).1) =>
        gradeΩ d.1) ∘ e) = fun d => CellScheme.grade lowerΩ d.1 := by
      funext d
      change gradeΩ (GrowthPaddedSuccessor.old I X T hA hB hC d.1) = _
      exact congrArg Prod.snd (cell_old I X T hA hB hC d.1)
    have hr : (Eρ (oldAt I X T hA hB hC c).1 ∘ e) = Semantics.E BaseRows c.1 :=
      funext fun d => GrowthPaddedSuccessor.inherited_row I X T hA hB hC c.1 d
    have hq : ((fun d : CellScheme.below Ωc (cellΩ (oldAt I X T hA hB hC c).1) =>
        min (p (CellScheme.below.incl (oldAt I X T hA hB hC c) d))
          (p (oldAt I X T hA hB hC c))) ∘ e) =
        fun d => min (p (oldAt I X T hA hB hC (CellScheme.below.incl c d)))
          (p (oldAt I X T hA hB hC c)) :=
      funext fun d => rfl
    rw [hg, hr, hq] at ht
    exact ht
  · obtain ⟨w, hw, hle⟩ := hp.availability (oldAt I X T hA hB hC c) (oldAt I X T hA hB hC v)
      (by
        change (cellΩ (oldAt I X T hA hB hC c).1).1 ⊆ (cellΩ (oldAt I X T hA hB hC v).1).1
        rw [cell_oldAt, cell_oldAt]; exact hs)
      (by rw [grade_oldAt, grade_oldAt]; exact hg)
    rw [cell_oldAt] at hw
    have hne : cellΩ w.1 ≠ (A, 2) := by
      rw [hw]
      intro h
      have h2 := congrArg Prod.snd h
      have h1 := v.2.2
      change CellScheme.grade lowerΩ v.1 ≤ 1 at h1
      change CellScheme.grade lowerΩ v.1 = 2 at h2
      omega
    obtain ⟨y, hy⟩ := SourceLayerCarrier.old_occurrence lowerΩ
      (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty)) 2 (by decide) hA
      w.1 hne
    have hcy : CellScheme.cell lowerΩ y = CellScheme.cell lowerΩ v.1 := by
      rw [← hw, hy]; exact (cell_old I X T hA hB hC y).symm
    refine ⟨⟨y, hcy ▸ v.2⟩, hcy, ?_⟩
    have hwy : w = oldAt I X T hA hB hC ⟨y, hcy ▸ v.2⟩ := Subtype.ext hy
    rw [hwy] at hle
    exact hle

/-! ## The maximal spare chart -/

/-- The spare rung of an anchor as an occurrence of the base. -/
def spareLow (a : Catalogue X 1) : Low :=
  ⟨RelativeLadderLayer.added I.boundary (card_pos hA) (spare a), by
    change GradedLe ((RelativeLadderLayer.carrier I.boundary (card_pos hA)).cell _) _
    rw [RelativeLadderLayer.added_index]; exact GradedLe.refl _⟩

/-- A padded point as an occurrence of the base. -/
def ladderLow (v : Pt) : Low :=
  ⟨RelativeLadderLayer.added I.boundary (card_pos hA) v, by
    change GradedLe ((RelativeLadderLayer.carrier I.boundary (card_pos hA)).cell _) _
    rw [RelativeLadderLayer.added_index]; exact GradedLe.refl _⟩

/-- A present grade-one original as an occurrence of the base. -/
def originalLow (d : Cell I.boundary) (hd : GradedLe (I.boundary.cell d) (A, 1)) : Low :=
  ⟨RelativeLadderLayer.old I.boundary (card_pos hA) d, by
    change GradedLe ((RelativeLadderLayer.carrier I.boundary (card_pos hA)).cell _) _
    rw [RelativeLadderLayer.old_index]; exact hd⟩

theorem oldAt_ladderLow (v : Pt) :
    oldAt I X T hA hB hC (ladderLow I X T hA hB hC v) = ladderAt I X T hA hB hC v := rfl

theorem oldAt_originalLow (d : Cell I.boundary) (hd : GradedLe (I.boundary.cell d) (A, 1)) :
    oldAt I X T hA hB hC (originalLow I X T hA hB hC d hd) =
      originalAt I X T hA hB hC d (hd.trans one_le_two_index) := rfl

/-- The ladder row of a spare at a padded point is the actual ladder row. -/
theorem ladderRow_spare_added (a : Catalogue X 1) (v : Pt) :
    RelativeLadderLayer.ladderRow I.boundary (card_pos hA) (GrowthOrderedBase.field I) (fields X 1)
      (spare a) (RelativeLadderLayer.added I.boundary (card_pos hA) v) =
      SupportLadderRows.row ranks₁ (spare a) v := by
  change SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ (spare a))
    (RelativeLadderLayer.rankIndex I.boundary (card_pos hA) (GrowthOrderedBase.field I)
      (fields X 1) (SupportLadderRows.parent (spare a))
      (RelativeLadderLayer.added I.boundary (card_pos hA) v)) = _
  rw [RelativeLadderLayer.rankIndex_added]
  rfl

/-- The ladder row of a spare at an original is the rank-coded source of its field. -/
theorem ladderRow_spare_old (a : Catalogue X 1) (d : Cell I.boundary) :
    RelativeLadderLayer.ladderRow I.boundary (card_pos hA) (GrowthOrderedBase.field I) (fields X 1)
      (spare a) (RelativeLadderLayer.old I.boundary (card_pos hA) d) =
      SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field I d)) := by
  change SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ (spare a))
    (RelativeLadderLayer.rankIndex I.boundary (card_pos hA) (GrowthOrderedBase.field I)
      (fields X 1) (SupportLadderRows.parent (spare a))
      (RelativeLadderLayer.old I.boundary (card_pos hA) d)) = _
  rw [RelativeLadderLayer.rankIndex_old, SupportLadderRows.ceiling_leaf]
  rfl

/-- The spare's row at a padded point is the rank-coded source at the point's index. -/
theorem row_spare (a : Catalogue X 1) (v : Pt) :
    SupportLadderRows.row ranks₁ (spare a) v =
      SupportLadderRows.source rungs (SupportLadderRows.index ranks₁ a v) := by
  rw [SupportLadderRows.row, SupportLadderRows.ceiling_leaf]
  rfl

/-- **The maximal spare chart**: a spare rung attaining `M₁ p`, with a chart through grade one,
bounded by `M₁ p`, reading every padded point exactly and every present grade-one original as the
rank-coded source of its field.  Extracted from lawfulness alone. -/
theorem exists_spare_chart (hp : RespectsSemanticsBelow Rows (A, 2) p) :
    ∃ (a : Catalogue X 1) (τ : ExtOrd → ExtOrd), Witness (gTop 1) τ ∧
      p (ladderAt I X T hA hB hC (spare a)) = spareSup I X T hA hB hC p ∧
      (∀ x, τ x ≤ spareSup I X T hA hB hC p) ∧
      (∀ v : Pt, τ (SupportLadderRows.row ranks₁ (spare a) v) = p (ladderAt I X T hA hB hC v)) ∧
      ∀ (d : Cell I.boundary) (hd : GradedLe (I.boundary.cell d) (A, 1)),
        τ (SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field I d))) =
          p (originalAt I X T hA hB hC d (hd.trans one_le_two_index)) := by
  obtain ⟨a, τ, hτ, hb, hr⟩ := RelativeLadderLayer.exists_leaf_chart I.boundary I.rows
    (card_pos hA) (GrowthOrderedBase.field I) (fields X 1) (GrowthOrderedBase.proper I hB hC)
    (zeroMember I X 1 le_rfl) (base_lawful I X T hA hB hC hp)
  have hleaf : RelativeLadderLayer.leafOccurrence I.boundary (card_pos hA) a =
      spareLow I X T hA hB hC a := rfl
  have hread (v : Pt) : τ (SupportLadderRows.row ranks₁ (spare a) v) =
      p (ladderAt I X T hA hB hC v) := by
    have h := hr (ladderLow I X T hA hB hC v)
    rw [← ladderRow_spare_added I X hA a v]
    exact h
  have hmax : p (ladderAt I X T hA hB hC (spare a)) = spareSup I X T hA hB hC p := by
    apply le_antisymm (le_spareSup I X T hA hB hC p a)
    apply Finset.sup_le
    intro b _
    rw [← hread]
    exact hb _
  refine ⟨a, τ, hτ, hmax, fun x => (hb x).trans_eq hmax, hread, fun d hd => ?_⟩
  have h := hr (originalLow I X T hA hB hC d hd)
  rw [← ladderRow_spare_old I X hA a d]
  exact h

/-! ## Uncapped recognition of the complete shadow vector -/

section Chart

variable {a : Catalogue X 1} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop 1) τ)
  (hread : ∀ v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
    (Q := Catalogue X 1),
    τ (SupportLadderRows.row (RelativeLadderLayer.ranks (fields X 1))
      (SupportLadderRows.leaf (rungs_pos I) a) v) = p (ladderAt I X T hA hB hC v))

include hτ hread

/-- **Uncapped complete-field recognition**: every shadow maximum is the chart's reading of the
rank-coded source of that field, present, hidden or future. -/
theorem shadowSup_eq_spare (f : Fld) :
    shadowSup I X T hA hB hC p f = τ (SupportLadderRows.source rungs (ranks₁ a f)) := by
  have he := SupportLadderRows.readout_image (H := rungs) (rank_le_rungs I X) a
    (SupportLadderRows.source_mono rungs) f
  simp only [SupportLadderRows.readout] at he
  rw [show Fintype.ofFinite (Catalogue X 1) = (inferInstance : Fintype (Catalogue X 1)) from
    Subsingleton.elim _ _] at he
  rw [← he, Finset.apply_sup_eq_sup_comp_of_linearOrder τ hτ.mono hτ.bot, shadowSup]
  congr 1
  funext b
  rw [Function.comp_apply, ← hread, row_spare]
  rfl

omit hτ in
/-- The spare reads `M₁ p`. -/
theorem read_spare (hmax : p (ladderAt I X T hA hB hC (spare a)) = spareSup I X T hA hB hC p) :
    τ (SupportLadderRows.source rungs rungs) = spareSup I X T hA hB hC p := by
  rw [← hmax, ← hread, row_spare, SupportLadderRows.index_leaf,
    FiniteProfileControllers.cut_refl]

/-- **Finite bottom reflection on the rank-coded values** of every field, when `M₁ p ≠ ⊥`. -/
theorem spare_bottom_reflection (hp : RespectsSemanticsBelow Rows (A, 2) p)
    (hmax : p (ladderAt I X T hA hB hC (spare a)) = spareSup I X T hA hB hC p)
    (hne : spareSup I X T hA hB hC p ≠ ⊥) (f : Fld) :
    τ (SupportLadderRows.source rungs (ranks₁ a f)) = ⊥ ↔
      SupportLadderRows.source rungs (ranks₁ a f) = ⊥ := by
  have : Nonempty (Catalogue X 1) := ⟨zeroMember I X 1 le_rfl⟩
  have hread' (v : Pt) : τ (SupportLadderRows.row ranks₁ (spare a) v) =
      min (p (ladderAt I X T hA hB hC v)) (spareSup I X T hA hB hC p) := by
    rw [hread]
    refine (min_eq_left ?_).symm
    rw [← hmax, ← hread, ← hread]
    exact hτ.mono (by
      rw [row_spare, row_spare, SupportLadderRows.index_leaf, FiniteProfileControllers.cut_refl]
      exact SupportLadderRows.source_mono rungs (SupportLadderRows.index_le a v))
  have hdiag : τ (SupportLadderRows.row ranks₁ (spare a) (spare a)) =
      spareSup I X T hA hB hC p := by
    rw [hread]; exact hmax
  have h := SupportLadderRows.bottom_reflection (rank_le_rungs I X) (rungs_pos I)
    (ladder_lawful I X T hA hB hC hp) (spare a) hτ.bot hne hread' hdiag (shadow a f)
  rwa [row_spare, index_shadow_self] at h

end Chart

/-- **Exact readback of present grade-one originals**: uncapped. -/
theorem present_readback_of_grade_one (hp : RespectsSemanticsBelow Rows (A, 2) p)
    (d : Cell I.boundary) (hd : GradedLe (I.boundary.cell d) (A, 1)) :
    p (originalAt I X T hA hB hC d (hd.trans one_le_two_index)) =
      shadowSup I X T hA hB hC p (GrowthOrderedBase.field I d) := by
  obtain ⟨a, τ, hτ, -, -, hread, horig⟩ := exists_spare_chart I X T hA hB hC hp
  rw [← horig d hd, shadowSup_eq_spare I X T hA hB hC hτ hread]

/-! ## Lawfulness and admission of the uncapped vector at grade one -/

theorem profile_inl (S : State I.right.scheme I.left.scheme) (d : Cell I.right.scheme) :
    S.profile (Sum.inl d) = S.privateValues d := rfl

theorem profile_inr (S : State I.right.scheme I.left.scheme) (d : Cell I.left.scheme) :
    S.profile (Sum.inr d) = S.donorValues d := rfl

/-- The uncapped shadow vector, as a growth state. -/
def uncapped (p : Occ → ExtOrd) : State I.right.scheme I.left.scheme :=
  ⟨fun d => shadowSup I X T hA hB hC p (Sum.inl d), fun d => shadowSup I X T hA hB hC p (Sum.inr d)⟩

theorem uncapped_profile (p : Occ → ExtOrd) (f : Fld) :
    (uncapped I X T hA hB hC p).profile f = shadowSup I X T hA hB hC p f := by
  cases f <;> rfl

section Admission

variable (hp : RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) p) {a : Catalogue X 1}
  {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop 1) τ)
  (hmax : p (ladderAt I X T hA hB hC (SupportLadderRows.leaf (rungs_pos I) a)) =
    spareSup I X T hA hB hC p)
  (hb : ∀ x, τ x ≤ spareSup I X T hA hB hC p)
  (hread : ∀ v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
    (Q := Catalogue X 1),
    τ (SupportLadderRows.row (RelativeLadderLayer.ranks (fields X 1))
      (SupportLadderRows.leaf (rungs_pos I) a) v) = p (ladderAt I X T hA hB hC v))

include hp hτ hmax hb hread

/-- The transported rank-coded original vector on either original scheme is lawful through grade
one; at `M₁ p = ⊥` every value is `⊥`. -/
theorem uncapped_values_lawful {ιS : Type*} [DecidableEq ιS] {S : Finset ιS}
    {DS : CellScheme S} (semS : Semantics DS) (emb : Cell DS → Fld)
    (hlaw : RespectsSemanticsBelow semS (S, 1) (fun d => fields X 1 a (emb d.1))) :
    RespectsSemanticsBelow semS (S, 1) (fun d => shadowSup I X T hA hB hC p (emb d.1)) := by
  have hcoded := RelativeLadderLayer.rank_respects DS semS emb (fields X 1) a hlaw rungs
  have he : (fun d : DS.below (S, 1) => shadowSup I X T hA hB hC p (emb d.1)) =
      fun d => τ (SupportLadderRows.source rungs (ranks₁ a (emb d.1))) :=
    funext fun d => shadowSup_eq_spare I X T hA hB hC hτ hread (emb d.1)
  rw [he]
  by_cases hne : spareSup I X T hA hB hC p = ⊥
  · have hz : ∀ x, τ x = ⊥ := fun x => le_bot_iff.mp ((hb x).trans_eq hne)
    simp only [hz]
    exact respectsBelow_bot semS (S, 1)
  · exact map_respects_of_bottom_reflection hcoded (fun d => d.2.2) (boundedMap_of_witness hτ)
      (fun d => spare_bottom_reflection I X T hA hB hC hτ hread hp hmax hne (emb d.1))

/-- The uncapped vector is lawful on the private scheme through grade one. -/
theorem private_uncapped_lawful :
    RespectsSemanticsBelow I.right.rows (Finset.univ, 1)
      (fun d => (uncapped I X T hA hB hC p).privateValues d.1) :=
  uncapped_values_lawful I X T hA hB hC hp hτ hmax hb hread I.right.rows Sum.inl (by
    have h := (state_admitted X a).private_lawful
    have he : (fun d : I.right.scheme.below (Finset.univ, 1) => (state X a).privateValues d.1) =
        fun d => fields X 1 a (Sum.inl d.1) :=
      funext fun d => congrFun (state_profile X a) (Sum.inl d.1)
    rw [he] at h
    exact h)

/-- The uncapped vector is lawful on the donor scheme through grade one. -/
theorem donor_uncapped_lawful :
    RespectsSemanticsBelow I.left.rows (Finset.univ, 1)
      (fun d => (uncapped I X T hA hB hC p).donorValues d.1) :=
  uncapped_values_lawful I X T hA hB hC hp hτ hmax hb hread I.left.rows Sum.inr (by
    have h := (state_admitted X a).donor_lawful
    have he : (fun d : I.left.scheme.below (Finset.univ, 1) => (state X a).donorValues d.1) =
        fun d => fields X 1 a (Sum.inr d.1) :=
      funext fun d => congrFun (state_profile X a) (Sum.inr d.1)
    rw [he] at h
    exact h)

omit hp hmax hb in
/-- Every uncapped value is one-visible. -/
theorem uncapped_visible (f : Fld) : SelfVis 1 (shadowSup I X T hA hB hC p f) := by
  rw [shadowSup_eq_spare I X T hA hB hC hτ hread]
  exact selfVis_map hτ le_rfl (SupportLadderRows.source_visible _ _)

omit hp hmax hb in
/-- The uncapped vector agrees on the root: the anchor's fields do, hence their ranks. -/
theorem uncapped_shared (d : I.left.scheme.below X.root) :
    (uncapped I X T hA hB hC p).donorValues d.1 =
      (uncapped I X T hA hB hC p).privateValues (X.κ d).1 := by
  change shadowSup I X T hA hB hC p (Sum.inr d.1) = shadowSup I X T hA hB hC p (Sum.inl (X.κ d).1)
  rw [shadowSup_eq_spare I X T hA hB hC hτ hread, shadowSup_eq_spare I X T hA hB hC hτ hread]
  have hv : fields X 1 a (Sum.inr d.1) = fields X 1 a (Sum.inl (X.κ d).1) := by
    rw [← state_profile X a]
    exact (state_admitted X a).shared d
  simp only [RelativeLadderLayer.ranks, fieldRank, hv]

/-- **Admission of the uncapped vector at grade one.**  The correctness clause is vacuous below the
activation grade; a grade-one chart does not transport it, so `1 < X.req.N` is explicit. -/
theorem admitted_one (hN : 1 < X.req.N) : Admitted X 1 (uncapped I X T hA hB hC p) where
  private_lawful := private_uncapped_lawful I X T hA hB hC hp hτ hmax hb hread
  donor_lawful := donor_uncapped_lawful I X T hA hB hC hp hτ hmax hb hread
  visible f := by rw [uncapped_profile]; exact uncapped_visible I X T hA hB hC hτ hread f
  shared := uncapped_shared I X T hA hB hC hτ hread
  correct h := absurd h (by omega)

end Admission

/-- **The uncapped shadow vector is admitted at grade one**, for every lawful section, below the
activation grade. -/
theorem exists_admitted_one (hp : RespectsSemanticsBelow Rows (A, 2) p) (hN : 1 < X.req.N) :
    ∃ S : State I.right.scheme I.left.scheme, Admitted X 1 S ∧
      ∀ f, S.profile f = shadowSup I X T hA hB hC p f := by
  obtain ⟨a, τ, hτ, hmax, hb, hread, -⟩ := exists_spare_chart I X T hA hB hC hp
  exact ⟨uncapped I X T hA hB hC p, admitted_one I X T hA hB hC hp hτ hmax hb hread hN,
    uncapped_profile I X T hA hB hC p⟩

/-! ## The two-grade hidden-original projection -/

/-- The height at each grade: uncapped through grade one, the leaf maximum above. -/
def gradeHeight (p : CellScheme.below (carrier I X T hA hB hC) (A, 2) → ExtOrd) (j : ℕ) :
    ExtOrd :=
  if j ≤ 1 then ⊤ else leafSup I X T hA hB hC p

theorem gradeHeight_antitone (p : CellScheme.below (carrier I X T hA hB hC) (A, 2) → ExtOrd) :
    Antitone (gradeHeight I X T hA hB hC p) := by
  intro j k hjk
  unfold gradeHeight
  split_ifs with hk hj hj
  · exact le_rfl
  · exact absurd (hjk.trans hk) hj
  · exact le_top
  · exact le_rfl

theorem gradeHeight_one (p : CellScheme.below (carrier I X T hA hB hC) (A, 2) → ExtOrd) :
    gradeHeight I X T hA hB hC p 1 = ⊤ := by
  unfold gradeHeight; rfl

theorem gradeHeight_two (p : CellScheme.below (carrier I X T hA hB hC) (A, 2) → ExtOrd) :
    gradeHeight I X T hA hB hC p 2 = leafSup I X T hA hB hC p := by
  unfold gradeHeight; rfl

/-- Lawfulness below grade zero is vacuous: every cell has positive grade. -/
theorem respectsBelow_zero {ιS : Type*} [DecidableEq ιS] {S : Finset ιS} {DS : CellScheme S}
    (semS : Semantics DS) (r : DS.below (S, 0) → ExtOrd) :
    RespectsSemanticsBelow semS (S, 0) r := by
  have hno (d : DS.below (S, 0)) : False := by
    have h1 := d.2.2
    have h2 := DS.grade_pos d.1
    change DS.grade d.1 ≤ 0 at h1
    omega
  exact ⟨fun d => (hno d).elim, fun d => (hno d).elim, fun d => (hno d).elim⟩

/-- **The projected section on one original scheme is lawful through grade two**, from the
uncapped grade-one section and the capped grade-two section. -/
theorem projection_lawful {ιS : Type*} [DecidableEq ιS] {S : Finset ιS} {DS : CellScheme S}
    (semS : Semantics DS) (ρ : Cell DS → ExtOrd)
    (h₁ : RespectsSemanticsBelow semS (S, 1) (fun d => ρ d.1))
    (h₂ : RespectsSemanticsBelow semS (S, 2)
      (fun d => min (ρ d.1) (leafSup I X T hA hB hC p))) :
    RespectsSemanticsBelow semS (S, 2)
      (fun d => min (ρ d.1) (gradeHeight I X T hA hB hC p (DS.grade d.1))) := by
  apply GradePrefixProjection.respectsBelow (gradeHeight_antitone I X T hA hB hC p)
  intro j hj
  change j ≤ 2 at hj
  rcases Nat.lt_or_ge j 1 with h0 | h1
  · have hj0 : j = 0 := by omega
    subst hj0
    exact respectsBelow_zero semS _
  rcases Nat.lt_or_ge j 2 with h1' | h2
  · have hj1 : j = 1 := by omega
    subst hj1
    rw [gradeHeight_one]
    have he : (fun d : DS.below (S, 1) => min (ρ d.1) (⊤ : ExtOrd)) = fun d => ρ d.1 :=
      funext fun d => min_eq_left le_top
    rw [he]
    exact h₁
  · have hj2 : j = 2 := by omega
    subst hj2
    rw [gradeHeight_two]
    exact h₂

/-- **The two-grade hidden-original projection.**  For every lawful section `p` below `(A, 2)`:
the projection `d ↦ min (B_p (field d)) (H (grade d))`, uncapped at grade one and capped at the
leaf maximum at grade two, is lawful through grade two on the private and on the donor scheme,
and every present original reads it exactly. -/
theorem two_grade_projection (hp : RespectsSemanticsBelow Rows (A, 2) p) :
    RespectsSemanticsBelow I.right.rows (Finset.univ, 2) (fun d =>
      min (shadowSup I X T hA hB hC p (Sum.inl d.1))
        (gradeHeight I X T hA hB hC p (I.right.scheme.grade d.1))) ∧
    RespectsSemanticsBelow I.left.rows (Finset.univ, 2) (fun d =>
      min (shadowSup I X T hA hB hC p (Sum.inr d.1))
        (gradeHeight I X T hA hB hC p (I.left.scheme.grade d.1))) ∧
    (∀ (d : Cell I.boundary) (hd : GradedLe (I.boundary.cell d) (A, 1)),
      p (originalAt I X T hA hB hC d (hd.trans one_le_two_index)) =
        shadowSup I X T hA hB hC p (GrowthOrderedBase.field I d)) ∧
    ∀ (d : Cell I.boundary) (hd : GradedLe (I.boundary.cell d) (A, 2)),
      I.boundary.grade d = 2 →
      p (originalAt I X T hA hB hC d hd) =
        min (shadowSup I X T hA hB hC p (GrowthOrderedBase.field I d))
          (leafSup I X T hA hB hC p) := by
  obtain ⟨a₁, τ, hτ, hmax₁, hb, hread₁, -⟩ := exists_spare_chart I X T hA hB hC hp
  obtain ⟨a₂, σ, hσ, hmax₂, -, hread₂⟩ := exists_leaf_chart I X T hA hB hC hp
  obtain ⟨S₂, hS₂, hS₂p⟩ := exists_admitted I X T hA hB hC hσ hread₂ hp hmax₂
  refine ⟨?_, ?_, present_readback_of_grade_one I X T hA hB hC hp,
    present_readback_of_grade_two I X T hA hB hC hp hσ hread₂⟩
  · apply projection_lawful I X T hA hB hC (p := p) I.right.rows
      (fun c => shadowSup I X T hA hB hC p (Sum.inl c))
    · exact private_uncapped_lawful I X T hA hB hC hp hτ hmax₁ hb hread₁
    · have h := hS₂.private_lawful
      have he : (fun d : I.right.scheme.below (Finset.univ, 2) => S₂.privateValues d.1) =
          fun d => min (shadowSup I X T hA hB hC p (Sum.inl d.1)) (leafSup I X T hA hB hC p) :=
        funext fun d => hS₂p (Sum.inl d.1)
      rw [he] at h
      exact h
  · apply projection_lawful I X T hA hB hC (p := p) I.left.rows
      (fun c => shadowSup I X T hA hB hC p (Sum.inr c))
    · exact donor_uncapped_lawful I X T hA hB hC hp hτ hmax₁ hb hread₁
    · have h := hS₂.donor_lawful
      have he : (fun d : I.left.scheme.below (Finset.univ, 2) => S₂.donorValues d.1) =
          fun d => min (shadowSup I X T hA hB hC p (Sum.inr d.1)) (leafSup I X T hA hB hC p) :=
        funext fun d => hS₂p (Sum.inr d.1)
      rw [he] at h
      exact h

/-! ## On the whole ordered boundary

The same conclusions on `I.rows`, the native catalogue's whole ordered boundary, without
reconstructing and gluing the two faces: the anchor's boundary lawfulness
(`GrowthOrderedBase.anchor_lawful`, `GrowthHigherSources.boundary_lawful_at`) feeds the generic
transports directly.  Root agreement of the grade-dependent projection follows from the uncapped
root agreement and root-grade preservation (`RootAttachment.grade`).  None of this uses the
admission hypothesis `1 < X.req.N`. -/

section Boundary

variable (hp : RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) p) {a : Catalogue X 1}
  {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop 1) τ)
  (hmax : p (ladderAt I X T hA hB hC (SupportLadderRows.leaf (rungs_pos I) a)) =
    spareSup I X T hA hB hC p)
  (hb : ∀ x, τ x ≤ spareSup I X T hA hB hC p)
  (hread : ∀ v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
    (Q := Catalogue X 1),
    τ (SupportLadderRows.row (RelativeLadderLayer.ranks (fields X 1))
      (SupportLadderRows.leaf (rungs_pos I) a) v) = p (ladderAt I X T hA hB hC v))

include hp hτ hmax hb hread

/-- **Uncapped grade-one lawfulness on the whole ordered boundary.** -/
theorem boundary_uncapped_lawful :
    RespectsSemanticsBelow I.rows (A, 1)
      (fun d => shadowSup I X T hA hB hC p (GrowthOrderedBase.field I d.1)) :=
  uncapped_values_lawful I X T hA hB hC hp hτ hmax hb hread I.rows (GrowthOrderedBase.field I)
    (GrowthOrderedBase.anchor_lawful I X T a)

/-- **The two-grade projection on the whole ordered boundary**, from the uncapped grade-one
section and any admitted grade-two state with the capped profile. -/
theorem boundary_projection_lawful {S₂ : State I.right.scheme I.left.scheme}
    (hS₂ : Admitted X 2 S₂)
    (hS₂p : ∀ f, S₂.profile f = min (shadowSup I X T hA hB hC p f) (leafSup I X T hA hB hC p)) :
    RespectsSemanticsBelow I.rows (A, 2) (fun d =>
      min (shadowSup I X T hA hB hC p (GrowthOrderedBase.field I d.1))
        (gradeHeight I X T hA hB hC p (I.boundary.grade d.1))) := by
  apply projection_lawful I X T hA hB hC (p := p) I.rows
    (fun c => shadowSup I X T hA hB hC p (GrowthOrderedBase.field I c))
  · exact boundary_uncapped_lawful I X T hA hB hC hp hτ hmax hb hread
  · have h := boundary_lawful_at I X T hS₂
    have he : (fun d : I.boundary.below (A, 2) => S₂.profile (GrowthOrderedBase.field I d.1)) =
        fun d => min (shadowSup I X T hA hB hC p (GrowthOrderedBase.field I d.1))
          (leafSup I X T hA hB hC p) :=
      funext fun d => hS₂p _
    rw [he] at h
    exact h

omit hp hmax hb in
/-- **Root agreement of the grade-dependent projection**: uncapped root agreement together with
root-grade preservation. -/
theorem projection_shared (d : I.left.scheme.below X.root) :
    min (shadowSup I X T hA hB hC p (Sum.inr d.1))
        (gradeHeight I X T hA hB hC p (I.left.scheme.grade d.1)) =
      min (shadowSup I X T hA hB hC p (Sum.inl (X.κ d).1))
        (gradeHeight I X T hA hB hC p (I.right.scheme.grade (X.κ d).1)) := by
  rw [T.grade d]
  exact congrArg (fun x => min x _) (uncapped_shared I X T hA hB hC hτ hread d)

end Boundary

/-- **The headline on the whole ordered boundary.**  For every lawful section `p` below `(A, 2)`:
the uncapped shadow vector is lawful through grade one on `I.rows`; the two-grade projection is
lawful through grade two on `I.rows`; the projection agrees on the root; every present original
reads it exactly.  No admission hypothesis is used. -/
theorem boundary_two_grade_projection (hp : RespectsSemanticsBelow Rows (A, 2) p) :
    RespectsSemanticsBelow I.rows (A, 1)
      (fun d => shadowSup I X T hA hB hC p (GrowthOrderedBase.field I d.1)) ∧
    RespectsSemanticsBelow I.rows (A, 2) (fun d =>
      min (shadowSup I X T hA hB hC p (GrowthOrderedBase.field I d.1))
        (gradeHeight I X T hA hB hC p (I.boundary.grade d.1))) ∧
    (∀ d : I.left.scheme.below X.root,
      min (shadowSup I X T hA hB hC p (Sum.inr d.1))
          (gradeHeight I X T hA hB hC p (I.left.scheme.grade d.1)) =
        min (shadowSup I X T hA hB hC p (Sum.inl (X.κ d).1))
          (gradeHeight I X T hA hB hC p (I.right.scheme.grade (X.κ d).1))) ∧
    (∀ (d : Cell I.boundary) (hd : GradedLe (I.boundary.cell d) (A, 1)),
      p (originalAt I X T hA hB hC d (hd.trans one_le_two_index)) =
        shadowSup I X T hA hB hC p (GrowthOrderedBase.field I d)) ∧
    ∀ (d : Cell I.boundary) (hd : GradedLe (I.boundary.cell d) (A, 2)),
      I.boundary.grade d = 2 →
      p (originalAt I X T hA hB hC d hd) =
        min (shadowSup I X T hA hB hC p (GrowthOrderedBase.field I d))
          (leafSup I X T hA hB hC p) := by
  obtain ⟨a₁, τ, hτ, hmax₁, hb, hread₁, -⟩ := exists_spare_chart I X T hA hB hC hp
  obtain ⟨a₂, σ, hσ, hmax₂, -, hread₂⟩ := exists_leaf_chart I X T hA hB hC hp
  obtain ⟨S₂, hS₂, hS₂p⟩ := exists_admitted I X T hA hB hC hσ hread₂ hp hmax₂
  exact ⟨boundary_uncapped_lawful I X T hA hB hC hp hτ hmax₁ hb hread₁,
    boundary_projection_lawful I X T hA hB hC hp hτ hmax₁ hb hread₁ hS₂ hS₂p,
    projection_shared I X T hA hB hC hτ hread₁,
    present_readback_of_grade_one I X T hA hB hC hp,
    present_readback_of_grade_two I X T hA hB hC hp hσ hread₂⟩

end
end VaughtConjecture.Knight.GrowthSpareRecognition
