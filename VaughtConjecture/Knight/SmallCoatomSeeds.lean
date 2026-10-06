/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalOneCoatom
public import VaughtConjecture.Knight.CoatomSeedInstallation

/-! # Constructed seeds for the two small coatom arities

All receipts are derived from the actual compatible legal inputs. No new
catalogue is designed and no output lawfulness or lifting premise is supplied.
-/
@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.SmallCoatomSeeds
open Transform Value ExtOrd AmalgamationPlan AmalgamatedBoundaryPlan SemSchemeBoundaryInput
open CoatomBoundaryExtension CoatomSeedInstallation
noncomputable section

private def bottomProfile {ι X : Type*} [DecidableEq ι] [Fintype X]
    {A : Finset ι} {D : CellScheme A} (sem : Semantics D) (j : ℕ) (occ : Cell D → X) :
    CanonicalFieldLayer.Profile sem j X occ := by
  refine ⟨fun _ => ⊥, ⟨?_, ?_, ?_⟩, rfl, fun _ => bot_ne_top⟩
  · intro d
    exact (extVisibilityReplace_bot _ _).symm
  · intro c
    simpa only [Function.comp_apply, min_self] using TransformsTo.to_bot (sem.E c)
  · intro _ b _ _
    exact ⟨b, rfl, le_rfl⟩

section One
variable {s : Step (Finset.univ : Finset (Fin 2))} {m : ℕ} (I : Input s m 1 1)
abbrev oneHeight : 1 ≤ (Finset.univ : Finset (Fin 2)).card := by simp
theorem oneGrade (d : Cell I.boundary) : I.boundary.grade d ≤ 1 := by
  simpa only [max_self] using I.grade_le d

def one : Seed I where
  scheme := CanonicalOneCoatom.scheme I.rows oneHeight
  rows := CanonicalOneCoatom.rows I.rows oneHeight I.proper (oneGrade I)
  plan := rfl
  boundary := OrderEmbedding.ofStrictMono (CanonicalOneCoatom.old I.rows oneHeight)
    (SourceLayerCarrier.old_order _ _ _ _ _)
  index d := SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)
  exhaustive B hB z hz := by
    have hn : (CanonicalOneCoatom.scheme I.rows oneHeight).cell z ≠ (Finset.univ, 1) :=
      fun he => hB (by
        change ((CanonicalOneCoatom.scheme I.rows oneHeight).cell z).1 ⊆ B at hz
        simpa only [he] using hz)
    obtain ⟨d, hd⟩ := SourceLayerCarrier.old_occurrence I.boundary
      (CanonicalFieldLayer.Profile I.rows 1 (Cell I.boundary) id) 1 (by decide) oneHeight z hn
    exact ⟨d, hd.symm⟩
  row c d := CanonicalFieldLayer.inherited_row I.rows 1 (Cell I.boundary) id (by decide)
    oneHeight I.proper (oneGrade I) c d
  consistent := CanonicalFieldLayer.consistent I.rows 1 (Cell I.boundary) id (by decide)
    oneHeight I.proper (oneGrade I) I.consistent
  coded := CanonicalSeedCoding.fieldLayer I.rows 1 (Cell I.boundary) id (by decide)
    oneHeight I.proper (oneGrade I) I.coded
  bountiful := by
    apply CanonicalOneCoatom.bountiful I.rows oneHeight I.proper (oneGrade I)
      (CoatomRecursiveInput.oldLifts I) I.left_visible I.right_visible
      (fun h => Finset.notMem_erase s.a Finset.univ (h.symm ▸ s.ha))
      (fun h => Finset.notMem_erase s.b Finset.univ (h.symm ▸ s.hb))
      (by rw [I.card_left]) (by rw [I.card_right]) I.intersection_visible
      (fun _ hC hCA => I.proper_scope_cover hC hCA)
    intro C hC hCA hCc
    exact I.complete_proper (Plan.mem_gradedPlan.mpr ⟨hC, (by decide : 0 < 1), hCc⟩) hCA
  grade := (CanonicalFieldLayer.data I.rows 1 (Cell I.boundary) id (by decide)
    oneHeight I.proper (oneGrade I)).max_grade
  complete J hJ hj := by
    have hj1 : J.2 = 1 := by have := (Plan.mem_gradedPlan.mp hJ).2.1; omega
    by_cases hfull : J.1 = Finset.univ
    · let q := bottomProfile I.rows 1 id
      exact ⟨(CanonicalFieldLayer.controller I.rows 1 (Cell I.boundary) id
        (by decide) oneHeight q).1,
        (CanonicalFieldLayer.controller I.rows 1 (Cell I.boundary) id
          (by decide) oneHeight q).2.trans (Prod.ext hfull.symm hj1.symm)⟩
    · obtain ⟨d, hd⟩ := I.complete_proper hJ hfull
      exact ⟨CanonicalOneCoatom.old I.rows oneHeight d,
        (SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)).trans hd⟩
  extend_whole _ hp := CanonicalOneCoatom.exists_whole I.rows oneHeight I.proper (oneGrade I) hp
end One

section Two
variable {s : Step (Finset.univ : Finset (Fin 3))} {m : ℕ} (I : Input s m 2 2)
abbrev twoHeight : 2 ≤ (Finset.univ : Finset (Fin 3)).card := by simp
theorem twoGrade (d : Cell I.boundary) : I.boundary.grade d ≤ 2 := by
  simpa only [max_self] using I.grade_le d

def two : Seed I where
  scheme := CanonicalPairLocalSections.carrier I.rows twoHeight
  rows := CanonicalPairLocalSections.semantics I.rows twoHeight I.proper
  plan := rfl
  boundary := CanonicalRecursiveInventory.boundary I.rows 2 twoHeight
  index := CanonicalRecursiveInventory.boundary_cell I.rows 2 twoHeight
  exhaustive B hB z hz := by
    rcases RecursiveSourceCarrier.classify I.boundary (CanonicalRecursiveInventory.Profile I.rows)
      2 twoHeight z with ⟨d, hd⟩ | ⟨j, _, _, he⟩
    · exact ⟨d, hd⟩
    · exact False.elim (hB (by
        change ((CanonicalPairLocalSections.carrier I.rows twoHeight).cell z).1 ⊆ B at hz
        have he' : (CanonicalPairLocalSections.carrier I.rows twoHeight).cell z =
            (Finset.univ, j) := he
        simpa only [he'] using hz))
  row c d := GradeCutPairRows.old_row I.boundary _ _ 1 2 (by decide)
    (CanonicalPairLocalSections.one_le twoHeight) (by decide) twoHeight I.proper (by decide)
    I.rows (CanonicalPairLocalSections.smallRows I.rows twoHeight I.proper) c d
  consistent := CanonicalPairBoundary.consistent I.rows 1 2 (by decide)
    (CanonicalPairLocalSections.one_le twoHeight) (by decide) twoHeight I.proper (by decide)
    I.consistent
  coded := CanonicalSeedCoding.pair I.rows twoHeight I.proper I.coded
  bountiful := by
    apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
      (CanonicalRecursiveCoverage.grade_bound I.rows 2 twoHeight (twoGrade I)) (by decide : 0 < 2)
    intro C B j hC hB hj hCB
    apply CanonicalPairLowerLifting.lower_lift I.rows I.proper twoHeight
      (CoatomRecursiveInput.oldLifts I) I.left_visible I.right_visible
      (fun h => Finset.notMem_erase s.a Finset.univ (h.symm ▸ s.ha))
      (fun h => Finset.notMem_erase s.b Finset.univ (h.symm ▸ s.hb))
      (by rw [I.card_left]) (by rw [I.card_right]) I.intersection_visible
      (fun _ hC hCA => I.proper_scope_cover hC hCA) _ hC hB ⟨hCB, le_rfl⟩ hj
    intro C hC hCA i hi hiC _
    exact I.complete_proper (Plan.mem_gradedPlan.mpr ⟨hC, hi, hiC⟩) hCA
  grade := CanonicalRecursiveCoverage.grade_bound I.rows 2 twoHeight (twoGrade I)
  complete := CanonicalRecursiveCoverage.complete_through I.rows 2 twoHeight
    (fun _ hJ hproper => I.complete_proper hJ hproper)
  extend_whole _ hp := CanonicalPairBoundary.exists_whole I.rows 1 2 (by decide)
    (CanonicalPairLocalSections.one_le twoHeight) (by decide) twoHeight I.proper (by decide) hp
end Two

end
end VaughtConjecture.Knight.SmallCoatomSeeds
