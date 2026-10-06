/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedFaces
public import VaughtConjecture.Knight.AmalgamatedBoundaryPlan
public import VaughtConjecture.Knight.CappedLiftComposition

/-! # Exhaustive lifting through target grade two on the padded LOW carrier

A proper plan scope must be contained in an original face. This hypothesis is
proved below for a binary two-coface plan; no mixed-prescription theorem is
inferred from the two original-face endpoints.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedPairLift
open Transform Value ExtOrd CappedDonor LowOnly AmalgamationPlan CoatomBoundaryExtension
open LowOnlyPaddedSuccessor LowOnlyPaddedFaces LowOnlyPaddedCharts
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem donor_two : CappedLift (rows I F hroot hA hB hC)
    (show GradedLe (B, 2) (A, 2) from ⟨hB.subset, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  let e := fullEquiv I.left I.placeLeft I.imageLeft (donorFace I F hroot hA hB hC) 2
  obtain ⟨r, hr, hread, hcap⟩ := LowOnlyPaddedOriginalLifts.donor_lift I F hroot hA hB hC
    ((full_respects_iff I.left I.placeLeft I.imageLeft
      (donorFace I F hroot hA hB hC) 2 p).mp hp) hq hγ (fun d => hag (e d))
  refine ⟨r, hr, hcap, ?_⟩
  intro d
  obtain ⟨x, rfl⟩ := e.surjective d
  exact hread x

theorem donor_one : CappedLift (rows I F hroot hA hB hC)
    (show GradedLe (B, 1) (A, 1) from ⟨hB.subset, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  let e := lowerEquiv I F hroot hA hB hC
  let f := fullEquiv I.left I.placeLeft I.imageLeft (donorFace I F hroot hA hB hC) 1
  have hq' : RespectsSemanticsBelow (input I F hroot hA hB hC).lowerRows
      (A, 1) (q ∘ e) := by
    apply (lower_respects_iff I F hroot hA hB hC _).mpr
    simpa only [e, Function.comp_def, Equiv.apply_symm_apply] using hq
  obtain ⟨r, hr, hread, hcap⟩ := LowOnlyOrderedLadder.donor_lift I F hroot (by omega) hB hC
    ((full_respects_iff I.left I.placeLeft I.imageLeft
      (donorFace I F hroot hA hB hC) 1 p).mp hp) hq' hγ (fun d => hag (f d))
  refine ⟨r ∘ e.symm, (lower_respects_iff I F hroot hA hB hC r).mp hr, ?_, ?_⟩
  · intro d
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (e.symm d)
  · intro d
    obtain ⟨x, rfl⟩ := f.surjective d
    change r (e.symm (e (Family.donorAt F I.boundary (by omega)
      (LowOnlyOrderedLadder.donorIncl I) x))) = p (f x)
    rw [Equiv.symm_apply_apply]
    exact hread x

theorem private_two : CappedLift (rows I F hroot hA hB hC)
    (show GradedLe (C, 2) (A, 2) from ⟨hC.subset, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  let e := fullEquiv I.right I.placeRight I.imageRight (privateFace I F hroot hA hB hC) 2
  obtain ⟨r, hr, hread, hcap⟩ := LowOnlyPaddedOriginalLifts.private_lift I F hroot hA hB hC
    ((full_respects_iff I.right I.placeRight I.imageRight
      (privateFace I F hroot hA hB hC) 2 p).mp hp) hq hγ (fun d => hag (e d))
  refine ⟨r, hr, hcap, ?_⟩
  intro d
  obtain ⟨x, rfl⟩ := e.surjective d
  exact hread x

theorem private_one : CappedLift (rows I F hroot hA hB hC)
    (show GradedLe (C, 1) (A, 1) from ⟨hC.subset, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  let e := lowerEquiv I F hroot hA hB hC
  let f := fullEquiv I.right I.placeRight I.imageRight (privateFace I F hroot hA hB hC) 1
  have hq' : RespectsSemanticsBelow (input I F hroot hA hB hC).lowerRows
      (A, 1) (q ∘ e) := by
    apply (lower_respects_iff I F hroot hA hB hC _).mpr
    simpa only [e, Function.comp_def, Equiv.apply_symm_apply] using hq
  obtain ⟨r, hr, hread, hcap⟩ := LowOnlyOrderedLadder.private_lift I F hroot (by omega) hB hC
    ((full_respects_iff I.right I.placeRight I.imageRight
      (privateFace I F hroot hA hB hC) 1 p).mp hp) hq' hγ (fun d => hag (f d))
  refine ⟨r ∘ e.symm, (lower_respects_iff I F hroot hA hB hC r).mp hr, ?_, ?_⟩
  · intro d
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (e.symm d)
  · intro d
    obtain ⟨x, rfl⟩ := f.surjective d
    change r (e.symm (e (Family.privateAt F I.boundary (by omega)
      (LowOnlyOrderedLadder.privateIncl I) x))) = p (f x)
    rw [Equiv.symm_apply_apply]
    exact hread x

variable (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)

include hcover in
theorem same_grade {S T : Finset ι} {j : ℕ}
    (hS : (S, j) ∈ Plan.gradedPlan R) (hT : (T, j) ∈ Plan.gradedPlan R)
    (hj : j ≤ 2) (hST : S ⊆ T) :
    CappedLift (rows I F hroot hA hB hC)
      (show GradedLe (S, j) (T, j) from ⟨hST, le_rfl⟩) := by
  by_cases ht : T = A
  · subst T
    by_cases hs : S = A
    · subst S; exact lift_refl
    have hjpos := (Plan.mem_gradedPlan.mp hS).2.1
    have hcases : j = 1 ∨ j = 2 := by omega
    rcases hcover S (Plan.mem_gradedPlan.mp hS).1 hs with hb | hc
    · have hBj : (B, j) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
        ⟨I.leftPlan_le I.leftScheme.isPlan.domain_mem, hjpos,
          (Plan.mem_gradedPlan.mp hS).2.2.trans (Finset.card_le_card hb)⟩
      have hl := inherited_lift I F hroot hA hB hC hS hBj
        (show GradedLe (S, j) (B, j) from ⟨hb, le_rfl⟩) (Or.inl (Finset.Subset.refl _))
      have hu : CappedLift (rows I F hroot hA hB hC)
          (show GradedLe (B, j) (A, j) from ⟨hB.subset, le_rfl⟩) := by
        rcases hcases with rfl | rfl
        · exact donor_one I F hroot hA hB hC
        · exact donor_two I F hroot hA hB hC
      exact hl.comp hu
    · have hCj : (C, j) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
        ⟨I.rightPlan_le I.rightScheme.isPlan.domain_mem, hjpos,
          (Plan.mem_gradedPlan.mp hS).2.2.trans (Finset.card_le_card hc)⟩
      have hl := inherited_lift I F hroot hA hB hC hS hCj
        (show GradedLe (S, j) (C, j) from ⟨hc, le_rfl⟩) (Or.inr (Finset.Subset.refl _))
      have hu : CappedLift (rows I F hroot hA hB hC)
          (show GradedLe (C, j) (A, j) from ⟨hC.subset, le_rfl⟩) := by
        rcases hcases with rfl | rfl
        · exact private_one I F hroot hA hB hC
        · exact private_two I F hroot hA hB hC
      exact hl.comp hu
  · exact inherited_lift I F hroot hA hB hC hS hT ⟨hST, le_rfl⟩
      (hcover T (Plan.mem_gradedPlan.mp hT).1 ht)

include hcover in
/-- Every permitted pair through target grade two, including equal indices
and grade changes. No completeness at any unfilled higher index is claimed. -/
theorem lift {U V : Finset ι × ℕ}
    (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V) (hgrade : V.2 ≤ 2) :
    CappedLift (rows I F hroot hA hB hC) h := by
  rcases U with ⟨S, i⟩
  rcases V with ⟨T, j⟩
  have hTi : (T, i) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
    ⟨(Plan.mem_gradedPlan.mp hV).1, (Plan.mem_gradedPlan.mp hU).2.1,
      h.2.trans (Plan.mem_gradedPlan.mp hV).2.2⟩
  exact (same_grade I F hroot hA hB hC hcover hU hTi (h.2.trans hgrade) h.1).raise_target
    (h := h.1) h.2

/-- The intended binary coface plan supplies coverage by construction.
This does not assert coverage for a larger plan containing new mixed scopes. -/
theorem cover_two_cofaces (s : AmalgamatedBoundaryPlan.Step A)
    (hR : R = s.plan) (hleft : B = A.erase s.a) (hright : C = A.erase s.b) :
    ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C := by
  intro S hS hs
  rw [hR] at hS
  rcases Finset.mem_union.mp hS with hS | hS
  · rcases Finset.mem_union.mp hS with hl | hr
    · exact Or.inl (hleft ▸ s.left_plan.subset_of_mem hl)
    · exact Or.inr (hright ▸ s.right_plan.subset_of_mem hr)
  · exact False.elim (hs (Finset.mem_singleton.mp hS))

theorem lift_two_cofaces (s : AmalgamatedBoundaryPlan.Step A)
    (hR : R = s.plan) (hleft : B = A.erase s.a) (hright : C = A.erase s.b)
    {U V : Finset ι × ℕ} (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V) (hgrade : V.2 ≤ 2) :
    CappedLift (rows I F hroot hA hB hC) h :=
  lift I F hroot hA hB hC (cover_two_cofaces s hR hleft hright) hU hV h hgrade

include hcover in
/-- Completeness only through the installed height; retained proper owners
at higher grades are not removed or bounded by two. -/
theorem complete_through_two {J : Finset ι × ℕ}
    (hJ : J ∈ Plan.gradedPlan R) (hj : J.2 ≤ 2) :
    ∃ d, (carrier I F hroot hA hB hC).cell d = J := by
  rcases J with ⟨T, j⟩
  by_cases ht : T = A
  · subst T
    have hp := (Plan.mem_gradedPlan.mp hJ).2.1
    have hc : j = 1 ∨ j = 2 := by omega
    rcases hc with rfl | rfl
    · obtain ⟨a, _⟩ := F.exists_rank_anchor (by decide : 1 ≤ 1) (F.zero_admissible 1)
      let v : RelativeLadderLayer.Point (X := Field I.left I.right) (Q := F.Anchor 1) :=
        (a, .inl ⟨0, Nat.succ_pos _⟩)
      refine ⟨old I F hroot hA hB hC (RelativeLadderLayer.added I.boundary (by omega) v), ?_⟩
      exact (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans
        (RelativeLadderLayer.added_index I.boundary (by omega) v)
    · obtain ⟨a, _⟩ := F.exists_rank_anchor (by decide : 1 ≤ 2) (F.zero_admissible 2)
      exact ⟨leaf I F hroot hA hB hC a, leaf_index I F hroot hA hB hC a⟩
  · obtain ⟨d, hd⟩ := (I.occupied_iff hJ).mpr (hcover T (Plan.mem_gradedPlan.mp hJ).1 ht)
    exact ⟨original I F hroot hA hB hC d, (original_index I F hroot hA hB hC d).trans hd⟩

end
end VaughtConjecture.Knight.LowOnlyPaddedPairLift
