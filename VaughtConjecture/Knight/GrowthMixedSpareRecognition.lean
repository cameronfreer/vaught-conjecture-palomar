/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthMixedLeafRecognition
public import VaughtConjecture.Knight.GrowthSpareRecognition

/-! # Uncapped recognition on an actual mixed scope

The spare chart is extracted locally, before any hidden original is assigned
a value. Its rank-coded boundary is lawful on the whole ordered boundary.
Together with the independent grade-two leaf chart this gives lawful original
prefixes without a full-scope extension or an admission hypothesis on the input.
The one-scope argument is due to the V-C checkpoint d667dfd; the local assembly
follows growth3 and keeps the installed rows unchanged.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthMixedSpareRecognition
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources GrowthMixedLeafRecognition
open SupportLadderRows LadderScalarRendering SharpWitnessComposition
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)
local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)
local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)
local notation "spare" => SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I)
local notation "Native" => GrowthPaddedSuccessor.carrier I X T hA hB hC
local notation "Carrier" => carrier I X T hA hB hC
local notation "Rows" => rows I X T hA hB hC

theorem eq_ladder_of_index (c : Cell Native) (hc : CellScheme.cell Native c = (A, 1)) :
    ∃ v : Pt, c = (GrowthLeafRecognition.ladderAt I X T hA hB hC v).1 := by
  rcases GrowthPaddedSuccessor.cell_cases I X T hA hB hC c with ⟨d, rfl⟩ | ⟨a, rfl⟩
  · rw [GrowthLeafRecognition.cell_old] at hc
    rcases RelativeLadderLayer.cell_cases I.boundary (GrowthLeafRecognition.card_pos hA) d with
      ⟨e, rfl⟩ | ⟨v, rfl⟩
    · rw [RelativeLadderLayer.old_index] at hc
      exact (GrowthOrderedBase.proper I hB hC e (congrArg Prod.fst hc)).elim
    · exact ⟨v, rfl⟩
  · have h := (congrArg Prod.snd (GrowthPaddedSuccessor.leaf_index I X T hA hB hC a)).symm.trans
      (congrArg Prod.snd hc)
    exact (by omega : False).elim

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U) (hu : 2 ≤ U.card)
local notation "Occ" => CellScheme.below (carrier I X T hA hB hC) (U, 2)
variable {p : CellScheme.below (carrier I X T hA hB hC) (U, 2) → ExtOrd}

theorem ladder_le_spareSup (hp : RespectsSemanticsBelow Rows (U, 2) p) (v : Pt) :
    p (ladderAt I X T hA hB hC U hU hm hu v) ≤ spareSup I X T hA hB hC U hU hm hu p :=
  ((ladder_lawful I X T hA hB hC U hU hm hu hp).le_parent
    (GrowthLeafRecognition.rank_le_rungs I X) (GrowthLeafRecognition.rungs_pos I) v).trans
    (Finset.le_sup (f := fun b => p (ladderAt I X T hA hB hC U hU hm hu (spare b)))
      (Finset.mem_univ _))

theorem grade_one_le (hp : RespectsSemanticsBelow Rows (U, 2) p) (z : Occ)
    (hz : CellScheme.grade Carrier z.1 = 1) : p z ≤ spareSup I X T hA hB hC U hU hm hu p := by
  let a₀ := GrowthLeafRecognition.zeroMember I X 1 le_rfl
  obtain ⟨w, hw, hzw⟩ := hp.availability z (ladderAt I X T hA hB hC U hU hm hu (spare a₀))
    (by change CellScheme.scope Carrier z.1 ⊆ (CellScheme.cell Carrier _).1
        rw [ladder_index]; exact z.2.1)
    (hz.trans (congrArg Prod.snd (ladder_index I X T hA hB hC U hU hm hu _)).symm)
  have hw' := hw.trans (ladder_index I X T hA hB hC U hU hm hu _)
  have hei := ScopeReplicationCharts.erase_index Native B C
    (GrowthReplicatedRows.proper_covered (layer I X T hA hB hC)) hm w.1 hw'
  obtain ⟨v, hv⟩ := eq_ladder_of_index I X T hA hB hC _ hei
  have he : p w = p (ladderAt I X T hA hB hC U hU hm hu v) :=
    GrowthReplicatedRows.copy_eq (layer I X T hA hB hC) hp w _
      (by change (CellScheme.cell Carrier w.1).1 ⊆ (CellScheme.cell Carrier _).1
          rw [hw', ladder_index])
      (hv.trans (erase_ladder I X T hA hB hC U hU hm hu v).symm)
  exact hzw.trans (he.trans_le (ladder_le_spareSup I X T hA hB hC U hU hm hu hp v))

theorem row_ladder_original (v : Pt) (z : Occ) (d : Cell I.boundary)
    (hz : erase I X T hA hB hC z.1 = GrowthPaddedSuccessor.original I X T hA hB hC d)
    (hg : CellScheme.grade Carrier z.1 ≤ 1) :
    Semantics.E Rows (ladderAt I X T hA hB hC U hU hm hu v).1
      ⟨z.1, by rw [ladder_index]; exact ⟨z.2.1, hg⟩⟩ =
      SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ v)
        (ranks₁ (SupportLadderRows.parent v) (GrowthOrderedBase.field I d)) := by
  have hgd : I.boundary.grade d ≤ 1 := by
    have he := ScopeReplicationCarrier.erase_grade Native B C z.1
    change CellScheme.grade Native (erase I X T hA hB hC z.1) = CellScheme.grade Carrier z.1 at he
    rw [hz] at he
    have hi := congrArg Prod.snd (GrowthPaddedSuccessor.original_index I X T hA hB hC d)
    exact hi.ge.trans (he.le.trans hg)
  let e : (GrowthPaddedContract.base I X T hA hB hC).below
      ((GrowthPaddedContract.base I X T hA hB hC).cell
        (RelativeLadderLayer.added I.boundary (GrowthLeafRecognition.card_pos hA) v)) :=
    ⟨RelativeLadderLayer.old I.boundary (GrowthLeafRecognition.card_pos hA) d, by
      rw [RelativeLadderLayer.old_index, RelativeLadderLayer.added_index]
      exact ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan d), hgd⟩⟩
  change (GrowthPaddedSuccessor.rows I X T hA hB hC).E _ _ = _
  refine ((GrowthPaddedSuccessor.rows I X T hA hB hC).E_congr
    (hd := by rw [GrowthPaddedSuccessor.original_index, GrowthLeafRecognition.cell_ladderAt]
              exact ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan d), hgd⟩)
    (erase_ladder I X T hA hB hC U hU hm hu v) hz).trans ?_
  refine (GrowthPaddedSuccessor.inherited_row I X T hA hB hC _ e).trans ?_
  rw [RelativeLadderLayer.row_added]
  change SupportLadderRows.source _ (RelativeLadderLayer.rankIndex _ _ _ _ _ _) = _
  rw [RelativeLadderLayer.rankIndex_old]
  rfl

/-- The actual maximal spare supplies an uncapped chart, directly at U. -/
theorem exists_spare_chart (hp : RespectsSemanticsBelow Rows (U, 2) p) :
    ∃ (a : Catalogue X 1) (τ : ExtOrd → ExtOrd), Witness (gTop 1) τ ∧
      p (ladderAt I X T hA hB hC U hU hm hu (spare a)) =
        spareSup I X T hA hB hC U hU hm hu p ∧
      (∀ x, τ x ≤ spareSup I X T hA hB hC U hU hm hu p) ∧
      (∀ v : Pt, τ (SupportLadderRows.row ranks₁ (spare a) v) =
        p (ladderAt I X T hA hB hC U hU hm hu v)) ∧
      ∀ (z : Occ) (d : Cell I.boundary),
        erase I X T hA hB hC z.1 = GrowthPaddedSuccessor.original I X T hA hB hC d →
        CellScheme.grade Carrier z.1 = 1 →
        τ (SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field I d))) = p z := by
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Catalogue X 1))
    (fun b => p (ladderAt I X T hA hB hC U hU hm hu (spare b)))
    ⟨GrowthLeafRecognition.zeroMember I X 1 le_rfl, Finset.mem_univ _⟩
  let c := ladderAt I X T hA hB hC U hU hm hu (spare a)
  have hpc : p c = spareSup I X T hA hB hC U hU hm hu p :=
    le_antisymm (Finset.le_sup (f := fun b => p (ladderAt I X T hA hB hC U hU hm hu (spare b)))
      (Finset.mem_univ a)) (Finset.sup_le hmax)
  let self : CellScheme.below Carrier (CellScheme.cell Carrier c.1) := ⟨c.1, GradedLe.refl _⟩
  obtain ⟨τ, hτ, hb, hr⟩ := exists_bounded_exact_capped_witness
    (c := self) (fun d => d.2.2) (hp.orderly c).symm (hp.locality c)
  have hgrade : CellScheme.grade Carrier c.1 = 1 :=
    congrArg Prod.snd (ladder_index I X T hA hB hC U hU hm hu _)
  refine ⟨a, τ, hgrade ▸ hτ, hpc, fun x => (hb x).trans_eq hpc, ?_, ?_⟩
  · intro v
    have h := hr (ladderBelow I X T hA hB hC U hU hm hu (spare a) v)
    rw [row_ladder] at h
    exact h.trans (min_eq_left
      ((ladder_le_spareSup I X T hA hB hC U hU hm hu hp v).trans_eq hpc.symm))
  · intro z d hz hg
    let e : CellScheme.below Carrier (CellScheme.cell Carrier c.1) :=
      ⟨z.1, by rw [ladder_index]; exact ⟨z.2.1, hg.le⟩⟩
    have h := hr e
    rw [row_ladder_original I X T hA hB hC U hU hm hu (spare a) z d hz hg.le,
      SupportLadderRows.ceiling_leaf] at h
    exact h.trans (min_eq_left ((grade_one_le I X T hA hB hC U hU hm hu hp z hg).trans_eq hpc.symm))

section Chart
variable {a : Catalogue X 1} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop 1) τ)
  (hread : ∀ v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1),
    τ (SupportLadderRows.row (RelativeLadderLayer.ranks (fields X 1))
      (SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I) a) v) =
        p (ladderAt I X T hA hB hC U hU hm hu v))

include hτ hread
theorem shadowSup_eq_spare (f : Fld) :
    shadowSup I X T hA hB hC U hU hm hu p f =
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

theorem spare_bottom_reflection (hp : RespectsSemanticsBelow Rows (U, 2) p)
    (hmax : p (ladderAt I X T hA hB hC U hU hm hu (spare a)) =
      spareSup I X T hA hB hC U hU hm hu p)
    (hne : spareSup I X T hA hB hC U hU hm hu p ≠ ⊥) (f : Fld) :
    τ (SupportLadderRows.source rungs (ranks₁ a f)) = ⊥ ↔
      SupportLadderRows.source rungs (ranks₁ a f) = ⊥ := by
  have : Nonempty (Catalogue X 1) := ⟨GrowthLeafRecognition.zeroMember I X 1 le_rfl⟩
  have hread' (v : Pt) : τ (SupportLadderRows.row ranks₁ (spare a) v) =
      min (p (ladderAt I X T hA hB hC U hU hm hu v))
        (spareSup I X T hA hB hC U hU hm hu p) := by
    rw [hread, min_eq_left (ladder_le_spareSup I X T hA hB hC U hU hm hu hp v)]
  have hdiag : τ (SupportLadderRows.row ranks₁ (spare a) (spare a)) =
      spareSup I X T hA hB hC U hU hm hu p := (hread _).trans hmax
  have h := SupportLadderRows.bottom_reflection (GrowthLeafRecognition.rank_le_rungs I X)
    (GrowthLeafRecognition.rungs_pos I) (ladder_lawful I X T hA hB hC U hU hm hu hp)
    (spare a) hτ.bot hne hread' hdiag (shadow a f)
  rwa [GrowthSpareRecognition.row_spare, GrowthLeafRecognition.index_shadow_self] at h
end Chart

theorem original_readback_one (hp : RespectsSemanticsBelow Rows (U, 2) p)
    (z : Occ) (d : Cell I.boundary)
    (hz : erase I X T hA hB hC z.1 = GrowthPaddedSuccessor.original I X T hA hB hC d)
    (hg : CellScheme.grade Carrier z.1 = 1) :
    p z = shadowSup I X T hA hB hC U hU hm hu p (GrowthOrderedBase.field I d) := by
  obtain ⟨a, τ, hτ, -, -, hread, horig⟩ := exists_spare_chart I X T hA hB hC U hU hm hu hp
  exact (horig z d hz hg).symm.trans
    (shadowSup_eq_spare I X T hA hB hC U hU hm hu hτ hread _).symm

/-- Lawfulness on the whole literal original boundary, including hidden owners.
No activation bound or admitted completion of the physical section is required. -/
theorem boundary_one (hp : RespectsSemanticsBelow Rows (U, 2) p) :
    RespectsSemanticsBelow I.rows (A, 1)
      (fun d => shadowSup I X T hA hB hC U hU hm hu p (GrowthOrderedBase.field I d.1)) := by
  obtain ⟨a, τ, hτ, hmax, hb, hread, -⟩ := exists_spare_chart I X T hA hB hC U hU hm hu hp
  have hl := RelativeLadderLayer.rank_respects I.boundary I.rows (GrowthOrderedBase.field I)
    (fields X 1) a (GrowthHigherSources.anchor_lawful_at I X T a) rungs
  have he : (fun d : I.boundary.below (A, 1) =>
      shadowSup I X T hA hB hC U hU hm hu p (GrowthOrderedBase.field I d.1)) =
      fun d => τ (SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field I d.1))) :=
    funext fun d => shadowSup_eq_spare I X T hA hB hC U hU hm hu hτ hread _
  rw [he]
  by_cases hz : spareSup I X T hA hB hC U hU hm hu p = ⊥
  · have ht : ∀ x, τ x = ⊥ := fun x => le_bot_iff.mp ((hb x).trans_eq hz)
    simp only [ht]
    exact respectsBelow_bot I.rows (A, 1)
  · exact map_respects_of_bottom_reflection hl (fun d => d.2.2) (boundedMap_of_witness hτ)
      (fun d => spare_bottom_reflection I X T hA hB hC U hU hm hu
        hτ hread hp hmax hz (GrowthOrderedBase.field I d.1))

theorem boundary_two (hp : RespectsSemanticsBelow Rows (U, 2) p) :
    RespectsSemanticsBelow I.rows (A, 2) (fun d =>
      min (shadowSup I X T hA hB hC U hU hm hu p (GrowthOrderedBase.field I d.1))
        (leafSup I X T hA hB hC U hU hm hu p)) := by
  obtain ⟨S, hs, he⟩ := exists_admitted I X T hA hB hC U hU hm hu hp
  have hl := GrowthHigherSources.boundary_lawful_at I X T hs
  simpa only [he] using hl

def height (p : Occ → ExtOrd) (j : ℕ) : ExtOrd :=
  if j ≤ 1 then ⊤ else leafSup I X T hA hB hC U hU hm hu p

theorem height_antitone (p : Occ → ExtOrd) : Antitone (height I X T hA hB hC U hU hm hu p) := by
  intro i j hij
  unfold height
  split_ifs with hj hi hi
  · exact le_rfl
  · exact absurd (hij.trans hj) hi
  · exact le_top
  · exact le_rfl

/-- One lawful original projection, retaining grade-one values above the leaf
maximum. The common root is already identified in the ordered boundary. -/
theorem boundary_projection (hp : RespectsSemanticsBelow Rows (U, 2) p) :
    RespectsSemanticsBelow I.rows (A, 2) (fun d =>
      min (shadowSup I X T hA hB hC U hU hm hu p (GrowthOrderedBase.field I d.1))
        (height I X T hA hB hC U hU hm hu p (I.boundary.grade d.1))) := by
  apply GradePrefixProjection.respectsBelow (sem := I.rows) (BJ := (A, 2))
    (ρ := fun d => shadowSup I X T hA hB hC U hU hm hu p (GrowthOrderedBase.field I d))
    (height_antitone I X T hA hB hC U hU hm hu p)
  intro j hj
  change j ≤ 2 at hj
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact GrowthSpareRecognition.respectsBelow_zero I.rows _
  · simpa only [height, ite_eq_left (le_refl (1 : ℕ)), min_top_right] using
      boundary_one I X T hA hB hC U hU hm hu hp
  · exact boundary_two I X T hA hB hC U hU hm hu hp

theorem original_readback (hp : RespectsSemanticsBelow Rows (U, 2) p)
    (z : Occ) (d : Cell I.boundary)
    (hz : erase I X T hA hB hC z.1 = GrowthPaddedSuccessor.original I X T hA hB hC d) :
    p z = min (shadowSup I X T hA hB hC U hU hm hu p (GrowthOrderedBase.field I d))
      (height I X T hA hB hC U hU hm hu p (I.boundary.grade d)) := by
  have hg : I.boundary.grade d = CellScheme.grade Carrier z.1 := by
    have he := ScopeReplicationCarrier.erase_grade Native B C z.1
    change CellScheme.grade Native (erase I X T hA hB hC z.1) =
      CellScheme.grade Carrier z.1 at he
    rw [hz] at he
    exact (congrArg Prod.snd (GrowthPaddedSuccessor.original_index I X T hA hB hC d)).symm.trans he
  have hc : CellScheme.grade Carrier z.1 = 1 ∨ CellScheme.grade Carrier z.1 = 2 := by
    have hpos := CellScheme.grade_pos Carrier z.1
    have hle := z.2.2
    change CellScheme.grade Carrier z.1 ≤ 2 at hle
    omega
  rcases hc with h1 | h2
  · rw [height, hg, h1, ite_eq_left le_rfl, min_top_right]
    exact original_readback_one I X T hA hB hC U hU hm hu hp z d hz h1
  · obtain ⟨a, σ, hσ, -, -, hread⟩ := exists_leaf_chart I X T hA hB hC U hU hm hu hp
    rw [height, hg, h2, ite_eq_right (by decide : ¬ (2 : ℕ) ≤ 1)]
    exact original_readback_two I X T hA hB hC U hU hm hu hp hσ hread z d hz h2

end
end VaughtConjecture.Knight.GrowthMixedSpareRecognition
