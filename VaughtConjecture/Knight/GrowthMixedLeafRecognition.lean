/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthLeafRecognition
public import VaughtConjecture.Knight.GrowthReplicatedRows
public import VaughtConjecture.Knight.ScopeReplicationCharts

/-! # Grade-two recognition directly on an actual mixed scope

Extract the maximal chart on the mixed lower domain itself. The old full-scope
carrier is used only to name source prototypes and reuse their row identities;
no lawful section or extension on that carrier is assumed. Hidden and future
fields are read through the complete physical shadow family at this scope.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthMixedLeafRecognition
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
open SupportLadderRows LadderScalarRendering SharpWitnessComposition
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev layer := GrowthPaddedContract.initial I X T hA hB hC
abbrev carrier := GrowthReplicatedRows.carrier (layer I X T hA hB hC)
abbrev rows := GrowthReplicatedRows.rows (layer I X T hA hB hC)
abbrev erase := GrowthReplicatedRows.erase (layer I X T hA hB hC)

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U) (hu : 2 ≤ U.card)

def place (c : Cell (GrowthPaddedSuccessor.carrier I X T hA hB hC))
    (hc : (GrowthPaddedSuccessor.carrier I X T hA hB hC).scope c = A)
    (hg : (GrowthPaddedSuccessor.carrier I X T hA hB hC).grade c ≤ 2) :
    (carrier I X T hA hB hC).below (U, 2) :=
  ⟨ScopeReplicationCarrier.atScope (GrowthPaddedSuccessor.carrier I X T hA hB hC)
      B C U hU hm c hc (hg.trans hu),
    (ScopeReplicationCarrier.atScope_index (GrowthPaddedSuccessor.carrier I X T hA hB hC)
      B C U hU hm c hc (hg.trans hu)) ▸ ⟨le_rfl, hg⟩⟩

theorem at_index (c) (hc) (hg) :
    (carrier I X T hA hB hC).cell (place I X T hA hB hC U hU hm hu c hc hg).1 =
      (U, (GrowthPaddedSuccessor.carrier I X T hA hB hC).grade c) :=
  ScopeReplicationCarrier.atScope_index (GrowthPaddedSuccessor.carrier I X T hA hB hC)
    B C U hU hm c hc (hg.trans hu)

theorem erase_at (c) (hc) (hg) :
    erase I X T hA hB hC (place I X T hA hB hC U hU hm hu c hc hg).1 = c :=
  ScopeReplicationCarrier.erase_atScope (GrowthPaddedSuccessor.carrier I X T hA hB hC)
    B C U hU hm c hc (hg.trans hu)

local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)
local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)
local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)
local notation "ceil" => RecursiveRungRendering.ceiling Fld 2
local notation "Occ" => CellScheme.below (carrier I X T hA hB hC) (U, 2)
local notation "Rows" => rows I X T hA hB hC

def ladderAt (v : Pt) : Occ :=
  place I X T hA hB hC U hU hm hu (GrowthLeafRecognition.ladderAt I X T hA hB hC v).1
    (congrArg Prod.fst (GrowthLeafRecognition.cell_ladderAt I X T hA hB hC v))
    ((GrowthLeafRecognition.grade_ladderAt I X T hA hB hC v).le.trans (by decide))

def leafAt (a : Catalogue X 2) : Occ :=
  place I X T hA hB hC U hU hm hu (GrowthPaddedSuccessor.leaf I X T hA hB hC a)
    (congrArg Prod.fst (GrowthPaddedSuccessor.leaf_index I X T hA hB hC a))
    (congrArg Prod.snd (GrowthPaddedSuccessor.leaf_index I X T hA hB hC a)).le

theorem ladder_index (v : Pt) :
    (carrier I X T hA hB hC).cell (ladderAt I X T hA hB hC U hU hm hu v).1 = (U, 1) := by
  exact (at_index I X T hA hB hC U hU hm hu _ _ _).trans
    (congrArg (fun j => (U, j)) (GrowthLeafRecognition.grade_ladderAt I X T hA hB hC v))

theorem leaf_index (a : Catalogue X 2) :
    (carrier I X T hA hB hC).cell (leafAt I X T hA hB hC U hU hm hu a).1 = (U, 2) := by
  exact (at_index I X T hA hB hC U hU hm hu _ _ _).trans
    (congrArg (fun j => (U, j))
      (congrArg Prod.snd (GrowthPaddedSuccessor.leaf_index I X T hA hB hC a)))

theorem erase_ladder (v : Pt) :
    erase I X T hA hB hC (ladderAt I X T hA hB hC U hU hm hu v).1 =
      (GrowthLeafRecognition.ladderAt I X T hA hB hC v).1 := erase_at _ _ _ _ _ _ _ _ _ _ _ _ _

theorem erase_leaf (a : Catalogue X 2) :
    erase I X T hA hB hC (leafAt I X T hA hB hC U hU hm hu a).1 =
      GrowthPaddedSuccessor.leaf I X T hA hB hC a := erase_at _ _ _ _ _ _ _ _ _ _ _ _ _

def source (a : Catalogue X 2) (d : Cell (carrier I X T hA hB hC)) : ExtOrd :=
  GrowthPaddedSuccessor.source I X T hA hB hC a (erase I X T hA hB hC d)

theorem source_ladder (a : Catalogue X 2) (v : Pt) :
    source I X T hA hB hC a (ladderAt I X T hA hB hC U hU hm hu v).1 =
      SupportLadderRows.image ranks₁ (GrowthPaddedSuccessor.baseAnchor X a)
        (LadderScalarRendering.level (values (fields X 2 a)) ceil) v := by
  rw [source, erase_ladder]
  exact GrowthLeafRecognition.source_ladder I X T hA hB hC a v

theorem source_shadow_sup (a : Catalogue X 2) (f : Fld) :
    Finset.univ.sup (fun b : Catalogue X 1 =>
      source I X T hA hB hC a (ladderAt I X T hA hB hC U hU hm hu (shadow b f)).1) =
      fields X 2 a f := by
  simp only [source, erase_ladder]
  exact GrowthLeafRecognition.source_shadow_sup I X T hA hB hC a f

def ladderBelow (c v : Pt) : (carrier I X T hA hB hC).below
    ((carrier I X T hA hB hC).cell (ladderAt I X T hA hB hC U hU hm hu c).1) :=
  ⟨(ladderAt I X T hA hB hC U hU hm hu v).1,
    by rw [ladder_index, ladder_index]; exact GradedLe.refl _⟩

theorem row_ladder (c v : Pt) :
    Semantics.E Rows (ladderAt I X T hA hB hC U hU hm hu c).1
      (ladderBelow I X T hA hB hC U hU hm hu c v) = SupportLadderRows.row ranks₁ c v := by
  change (GrowthPaddedSuccessor.rows I X T hA hB hC).E _ _ = _
  exact ((GrowthPaddedSuccessor.rows I X T hA hB hC).E_congr
    (erase_ladder I X T hA hB hC U hU hm hu c)
    (erase_ladder I X T hA hB hC U hU hm hu v)).trans
      (GrowthLeafRecognition.row_ladder I X T hA hB hC c v)

variable (p : (carrier I X T hA hB hC).below (U, 2) → ExtOrd)

def shadowSup (f : Fld) : ExtOrd :=
  Finset.univ.sup fun b : Catalogue X 1 => p (ladderAt I X T hA hB hC U hU hm hu (shadow b f))

def leafSup : ExtOrd :=
  Finset.univ.sup fun a : Catalogue X 2 => p (leafAt I X T hA hB hC U hU hm hu a)

def spareSup : ExtOrd :=
  Finset.univ.sup fun b : Catalogue X 1 => p (ladderAt I X T hA hB hC U hU hm hu
    (SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I) b))

variable {p}

theorem ladder_lawful (hp : RespectsSemanticsBelow Rows (U, 2) p) :
    SupportLadderRows.Lawful ranks₁ (fun v => p (ladderAt I X T hA hB hC U hU hm hu v)) := by
  constructor
  · intro v
    have hv := hp.orderly (ladderAt I X T hA hB hC U hU hm hu v)
    change p _ = extVisibilityReplace (p _)
      ((carrier I X T hA hB hC).cell _).2 ((carrier I X T hA hB hC).cell _).2 at hv
    rw [ladder_index] at hv
    exact hv.symm
  · intro c
    have ht := (hp.locality (ladderAt I X T hA hB hC U hU hm hu c)).reindex
      (ladderBelow I X T hA hB hC U hU hm hu c)
    exact transformsTo_congr
      (funext fun v => congrArg Prod.snd (ladder_index I X T hA hB hC U hU hm hu v))
      (funext fun v => row_ladder I X T hA hB hC U hU hm hu c v) rfl ht

/-- The maximal chart is extracted at `(U,2)`, not from a postulated full
extension. Its erased owner is an existing catalogue leaf. -/
theorem exists_leaf_chart (hp : RespectsSemanticsBelow Rows (U, 2) p) :
    ∃ (a : Catalogue X 2) (σ : ExtOrd → ExtOrd), Witness (gTop 2) σ ∧
      p (leafAt I X T hA hB hC U hU hm hu a) = leafSup I X T hA hB hC U hU hm hu p ∧
      (∀ x, σ x ≤ leafSup I X T hA hB hC U hU hm hu p) ∧
      ∀ z : Occ, σ (source I X T hA hB hC a z.1) =
        min (p z) (leafSup I X T hA hB hC U hU hm hu p) := by
  obtain ⟨Ch⟩ := AmbientGradeCharts.exists_chart hp
    ⟨leafAt I X T hA hB hC U hU hm hu (GrowthLeafRecognition.zeroMember I X 2 (by decide)),
      leaf_index I X T hA hB hC U hU hm hu _⟩
  have hi := ScopeReplicationCharts.chart_prototype_index
    (GrowthPaddedSuccessor.carrier I X T hA hB hC) B C
    (GrowthReplicatedRows.proper_covered (layer I X T hA hB hC))
    (GrowthPaddedSuccessor.rows I X T hA hB hC) Ch hm
  obtain ⟨a, ha⟩ := GrowthLeafRecognition.eq_leaf_of_index I X T hA hB hC _ hi
  have he : p Ch.owner = p (leafAt I X T hA hB hC U hU hm hu a) :=
    GrowthReplicatedRows.copy_eq (layer I X T hA hB hC) hp Ch.owner
      (leafAt I X T hA hB hC U hU hm hu a)
      (by change ((carrier I X T hA hB hC).cell Ch.owner.1).1 ⊆ _
          rw [Ch.index]; exact (congrArg Prod.fst (leaf_index I X T hA hB hC U hU hm hu a)).ge)
      (ha.trans (erase_leaf I X T hA hB hC U hU hm hu a).symm)
  have hmax : p Ch.owner = leafSup I X T hA hB hC U hU hm hu p := by
    apply le_antisymm
    · rw [he]; exact Finset.le_sup (f := fun b => p (leafAt I X T hA hB hC U hU hm hu b))
        (Finset.mem_univ a)
    · exact Finset.sup_le fun b _ => Ch.dominates _
        (congrArg Prod.snd (leaf_index I X T hA hB hC U hU hm hu b))
  refine ⟨a, Ch.shift, Ch.witness, he.symm.trans hmax,
    fun x => (Ch.bounded x).trans_eq hmax, fun z => ?_⟩
  have hr := ScopeReplicationCharts.read_erased
    (GrowthPaddedSuccessor.carrier I X T hA hB hC) B C
    (GrowthReplicatedRows.proper_covered (layer I X T hA hB hC))
    (GrowthPaddedSuccessor.rows I X T hA hB hC) Ch z
  have hs := GrowthLeafRecognition.row_of_eq_leaf I X T hA hB hC a ha
    (ScopeReplicationCarrier.belowErase _ B C
      (GrowthReplicatedRows.proper_covered (layer I X T hA hB hC)) Ch.owner.1
      (Ch.occurrence z z.2.2))
  exact (congrArg Ch.shift hs.symm).trans
    (hr.trans (congrArg (fun x => min (p z) x) hmax))

theorem source_spare (a : Catalogue X 2) :
    source I X T hA hB hC a (ladderAt I X T hA hB hC U hU hm hu
      (SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I)
        (GrowthPaddedSuccessor.baseAnchor X a))).1 = ceil := by
  rw [source, erase_ladder]
  exact GrowthLeafRecognition.source_spare I X T hA hB hC a

theorem source_ceiling (a : Catalogue X 2) :
    source I X T hA hB hC a (leafAt I X T hA hB hC U hU hm hu a).1 = ceil := by
  rw [source, erase_leaf]
  exact GrowthPaddedSuccessor.source_ceiling I X T hA hB hC a

section Chart
variable {a : Catalogue X 2} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop 2) σ)
  (hread : ∀ z : (carrier I X T hA hB hC).below (U, 2),
    σ (source I X T hA hB hC a z.1) =
      min (p z) (leafSup I X T hA hB hC U hU hm hu p))

include hσ hread
theorem recognition (f : Fld) :
    σ (fields X 2 a f) = min (shadowSup I X T hA hB hC U hU hm hu p f)
      (leafSup I X T hA hB hC U hU hm hu p) := by
  rw [← source_shadow_sup I X T hA hB hC U hU hm hu a f,
    Finset.apply_sup_eq_sup_comp_of_linearOrder σ hσ.mono hσ.bot, shadowSup,
    GrowthLeafRecognition.cap_sup]
  congr 1
  funext b
  exact hread _

omit hσ in
theorem read_ceiling
    (hmax : p (leafAt I X T hA hB hC U hU hm hu a) = leafSup I X T hA hB hC U hU hm hu p) :
    σ ceil = leafSup I X T hA hB hC U hU hm hu p := by
  have h := hread (leafAt I X T hA hB hC U hU hm hu a)
  rw [source_ceiling] at h
  rw [h, hmax, min_self]

omit hσ in
theorem leafSup_le_spareSup
    (hmax : p (leafAt I X T hA hB hC U hU hm hu a) = leafSup I X T hA hB hC U hU hm hu p) :
    leafSup I X T hA hB hC U hU hm hu p ≤ spareSup I X T hA hB hC U hU hm hu p := by
  have h := hread (ladderAt I X T hA hB hC U hU hm hu
    (SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I)
      (GrowthPaddedSuccessor.baseAnchor X a)))
  rw [source_spare, read_ceiling I X T hA hB hC U hU hm hu hread hmax] at h
  exact (min_eq_right_iff.mp h.symm).trans
    (Finset.le_sup (f := fun b : Catalogue X 1 => p (ladderAt I X T hA hB hC U hU hm hu
      (SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I) b))) (Finset.mem_univ _))

/-- Reflection is proved on every complete field, using the actual mixed
ladder restriction and the birth spare. No global reflection is required. -/
theorem bottom_reflection (hp : RespectsSemanticsBelow Rows (U, 2) p)
    (hmax : p (leafAt I X T hA hB hC U hU hm hu a) = leafSup I X T hA hB hC U hU hm hu p)
    (hne : leafSup I X T hA hB hC U hU hm hu p ≠ ⊥) (f : Fld) :
    σ (fields X 2 a f) = ⊥ → fields X 2 a f = ⊥ := by
  have hCne : ceil ≠ ⊥ := fun hz =>
    hne (by rw [← read_ceiling I X T hA hB hC U hU hm hu hread hmax, hz, hσ.bot])
  have : Nonempty (Catalogue X 1) := ⟨GrowthLeafRecognition.zeroMember I X 1 le_rfl⟩
  have h0 : LadderScalarRendering.level (values (fields X 2 a)) ceil 0 = ⊥ := level_zero _ _
  have hf : ∀ i, 0 < i → i ≤ rungs →
      LadderScalarRendering.level (values (fields X 2 a)) ceil i ≠ ⊥ :=
    fun i hi _ => level_pos (bot_not_values _) (values_bound (anchor_bound X a)) hCne hi
  have hspare : σ (LadderScalarRendering.level (values (fields X 2 a)) ceil rungs) =
      leafSup I X T hA hB hC U hU hm hu p := by
    have h := source_spare I X T hA hB hC U hU hm hu a
    rw [source_ladder, SupportLadderRows.image, SupportLadderRows.index_leaf,
      FiniteProfileControllers.cut_refl] at h
    rw [h]
    exact read_ceiling I X T hA hB hC U hU hm hu hread hmax
  have hread' : ∀ v : Pt,
      σ (SupportLadderRows.image ranks₁ (GrowthPaddedSuccessor.baseAnchor X a)
        (LadderScalarRendering.level (values (fields X 2 a)) ceil) v) =
      min (p (ladderAt I X T hA hB hC U hU hm hu v))
        (leafSup I X T hA hB hC U hU hm hu p) := fun v => by
    rw [← source_ladder]
    exact hread _
  have hrefl := SupportLadderRows.bottom_reflection_image (GrowthLeafRecognition.rank_le_rungs I X)
    (GrowthLeafRecognition.rungs_pos I) (ladder_lawful I X T hA hB hC U hU hm hu hp)
    (GrowthPaddedSuccessor.baseAnchor X a) h0 hf hne hread' hspare
    (shadow (GrowthPaddedSuccessor.baseAnchor X a) f)
  rw [SupportLadderRows.image, GrowthLeafRecognition.index_shadow_self,
    GrowthPaddedSuccessor.baseAnchor_ranks, field_readback] at hrefl
  exact hrefl.mp

/-- Any visible original occurrence is read correctly below the local grade-two
maximum. This deliberately does not clip a lower prescribed value literally. -/
theorem original_readback (z : Occ) (d : Cell I.boundary)
    (hz : erase I X T hA hB hC z.1 = GrowthPaddedSuccessor.original I X T hA hB hC d) :
    min (p z) (leafSup I X T hA hB hC U hU hm hu p) =
      min (shadowSup I X T hA hB hC U hU hm hu p (GrowthOrderedBase.field I d))
        (leafSup I X T hA hB hC U hU hm hu p) := by
  rw [← recognition I X T hA hB hC U hU hm hu hσ hread, ← hread z]
  change σ (GrowthPaddedSuccessor.source I X T hA hB hC a (erase I X T hA hB hC z.1)) = _
  rw [hz, GrowthPaddedSuccessor.original_readback]

end Chart

/-- Every lawful mixed grade-two section has an admitted complete capped
shadow vector. The zero-maximum case is supplied independently. -/
theorem exists_admitted (hp : RespectsSemanticsBelow Rows (U, 2) p) :
    ∃ S : State I.right.scheme I.left.scheme, Admitted X 2 S ∧
      ∀ f, S.profile f = min (shadowSup I X T hA hB hC U hU hm hu p f)
        (leafSup I X T hA hB hC U hU hm hu p) := by
  by_cases hzero : leafSup I X T hA hB hC U hU hm hu p = ⊥
  · exact ⟨zero, zero_admitted X 2, fun f => by rw [hzero, min_bot_right]; cases f <;> rfl⟩
  obtain ⟨a, σ, hσ, hmax, -, hread⟩ := exists_leaf_chart I X T hA hB hC U hU hm hu hp
  refine ⟨(state X a).map σ, ?_, fun f => ?_⟩
  · refine Admitted.map_on_profile X (state_admitted X a) hσ (by decide) fun f hz => ?_
    rw [state_profile] at hz ⊢
    exact bottom_reflection I X T hA hB hC U hU hm hu hσ hread hp hmax hzero f hz
  · rw [State.profile_map, state_profile]
    exact recognition I X T hA hB hC U hU hm hu hσ hread f

/-- Availability bounds every actual grade-two value by the local leaf maximum,
including original occurrences and copies at smaller mixed scopes. -/
theorem grade_two_le (hp : RespectsSemanticsBelow Rows (U, 2) p) (z : Occ)
    (hz : (carrier I X T hA hB hC).grade z.1 = 2) :
    p z ≤ leafSup I X T hA hB hC U hU hm hu p := by
  let a₀ := GrowthLeafRecognition.zeroMember I X 2 (by decide)
  obtain ⟨w, hw, hzw⟩ := hp.availability z (leafAt I X T hA hB hC U hU hm hu a₀)
    (by
      change (carrier I X T hA hB hC).scope z.1 ⊆ ((carrier I X T hA hB hC).cell _).1
      rw [leaf_index]; exact z.2.1)
    (hz.trans (congrArg Prod.snd (leaf_index I X T hA hB hC U hU hm hu a₀)).symm)
  have hw' := hw.trans (leaf_index I X T hA hB hC U hU hm hu a₀)
  have hei := ScopeReplicationCharts.erase_index (GrowthPaddedSuccessor.carrier I X T hA hB hC)
    B C (GrowthReplicatedRows.proper_covered (layer I X T hA hB hC)) hm w.1 hw'
  obtain ⟨b, hb⟩ := GrowthLeafRecognition.eq_leaf_of_index I X T hA hB hC _ hei
  have hew : p w = p (leafAt I X T hA hB hC U hU hm hu b) :=
    GrowthReplicatedRows.copy_eq (layer I X T hA hB hC) hp w _
      (by
        change ((carrier I X T hA hB hC).cell w.1).1 ⊆
          ((carrier I X T hA hB hC).cell _).1
        rw [hw', leaf_index])
      (hb.trans (erase_leaf I X T hA hB hC U hU hm hu b).symm)
  exact hzw.trans (hew.trans_le
    (Finset.le_sup (f := fun b => p (leafAt I X T hA hB hC U hU hm hu b)) (Finset.mem_univ b)))

/-- Exact original readback on grade two. Lower grades deliberately retain only
the capped conclusion of `original_readback`. -/
theorem original_readback_two (hp : RespectsSemanticsBelow Rows (U, 2) p)
    {a : Catalogue X 2} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop 2) σ)
    (hread : ∀ z : Occ, σ (source I X T hA hB hC a z.1) =
      min (p z) (leafSup I X T hA hB hC U hU hm hu p))
    (z : Occ) (d : Cell I.boundary)
    (hz : erase I X T hA hB hC z.1 = GrowthPaddedSuccessor.original I X T hA hB hC d)
    (hg : (carrier I X T hA hB hC).grade z.1 = 2) :
    p z = min (shadowSup I X T hA hB hC U hU hm hu p (GrowthOrderedBase.field I d))
      (leafSup I X T hA hB hC U hU hm hu p) := by
  have h := original_readback I X T hA hB hC U hU hm hu hσ hread z d hz
  rwa [min_eq_left (grade_two_le I X T hA hB hC U hU hm hu hp z hg)] at h

end
end VaughtConjecture.Knight.GrowthMixedLeafRecognition
