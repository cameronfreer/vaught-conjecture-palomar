/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorOrdinarySections
public import VaughtConjecture.Knight.CanonicalRecursiveFace
public import VaughtConjecture.Knight.CanonicalRecursiveInitialized
public import VaughtConjecture.Knight.CanonicalRecursiveCoding

/-! # Ordinary scope lifting from the actual legal input faces

Derive the semantic inputs to the grade recurrence from two compatible legal
schemes, on the same rows used by `WholeDonorOrdinarySections`. In the two-facet
case this gives unrestricted lifting through the constructed height, not an
existential replacement carrier. It does not yet iterate over missing scopes.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.WholeDonorOrdinaryLift
open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension
open WholeDonorOrdinarySections
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
variable {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)
variable (hBA : B ≠ A) (hCA : C ≠ A)

theorem left_mem : B ∈ I.boundary.plan :=
  I.leftPlan_le I.leftScheme.isPlan.domain_mem

theorem right_mem : C ∈ I.boundary.plan :=
  I.rightPlan_le I.rightScheme.isPlan.domain_mem

theorem overlap_mem : B ∩ C ∈ I.boundary.plan := by
  apply I.leftPlan_le
  exact Finset.mem_image.mpr ⟨_, I.visibleLeft, I.intersection⟩

variable (n : ℕ) (hA : n + 3 ≤ A.card)

def leftFace : ExactSemanticFace I.leftRows (rows I hBA hCA n hA) :=
  CanonicalRecursiveFace.face I.leftFace
    (fun h => hBA (Finset.Subset.antisymm (I.isPlan.subset_of_mem (left_mem I)) h))
    (proper_boundary I hBA hCA) n hA

def rightFace : ExactSemanticFace I.rightRows (rows I hBA hCA n hA) :=
  CanonicalRecursiveFace.face I.rightFace
    (fun h => hCA (Finset.Subset.antisymm (I.isPlan.subset_of_mem (right_mem I)) h))
    (proper_boundary I hBA hCA) n hA

theorem left_order : StrictMono (leftFace I hBA hCA n hA).map :=
  CanonicalRecursiveFace.map_order I.leftFace _ _ n hA I.left_order

theorem right_order : StrictMono (rightFace I hBA hCA n hA).map :=
  CanonicalRecursiveFace.map_order I.rightFace _ _ n hA I.right_order

theorem coded : (rows I hBA hCA n hA).IsCoded :=
  CanonicalRecursiveCoding.coded I.rows (proper_boundary I hBA hCA) I.coded n hA

/-- The final-grade geometry on the actual inventory: when the private scope
has size N and the donor is smaller, all grade-N owners are literal private
full-scope owners. No row of an absent private owner is used in this argument. -/
theorem final_grade_private {N : ℕ} (hN : n + 3 < N) (hB : B.card = N) (hC : C.card < N)
    (d : Cell (carrier I n hA)) (hd : (carrier I n hA).grade d = N) :
    (carrier I n hA).cell d = (B, N) := by
  rcases RecursiveSourceCarrier.classify I.boundary (CanonicalRecursiveInventory.Profile I.rows)
    (n + 3) hA d with ⟨d, rfl⟩ | ⟨j, _, hj, he⟩
  · have hg : I.boundary.grade d = N := by
      change ((carrier I n hA).cell (original I n hA d)).2 = N at hd
      rw [CanonicalRecursiveInventory.boundary_cell] at hd
      exact hd
    rw [CanonicalRecursiveInventory.boundary_cell]
    rcases covered I d with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · have hs : I.leftScheme.scope c ⊆ B :=
        I.leftScheme.isPlan.subset_of_mem (I.leftScheme.scope_mem_plan c)
      have hc : N ≤ (I.leftScheme.scope c).card := by
        have he : I.leftScheme.grade c = N :=
          (congrArg Prod.snd (I.leftFace.index c)).symm.trans hg
        exact he ▸ I.leftScheme.grade_le_card_scope c
      have he := Finset.eq_of_subset_of_card_le hs (hB.trans_le hc)
      exact (I.leftFace.index c).trans (Prod.ext he
        ((congrArg Prod.snd (I.leftFace.index c)).symm.trans hg))
    · have he : I.rightScheme.grade c = N :=
        (congrArg Prod.snd (I.rightFace.index c)).symm.trans hg
      have hc := (I.rightScheme.grade_le_card_scope c).trans (Finset.card_le_card
        (I.rightScheme.isPlan.subset_of_mem (I.rightScheme.scope_mem_plan c)))
      exact (Nat.not_le_of_gt hC (he ▸ hc)).elim
  · have he' : j = N := (congrArg Prod.snd he).symm.trans hd
    exact (Nat.not_le_of_gt hN (he' ▸ hj)).elim

variable {CI BJ : Finset ι × ℕ}

/-- Every target contained in either input retains that input's original-cap
lifting, including equality of indices and arbitrary lawful local ambients. -/
theorem inherited_lift (hCI : CI ∈ Plan.gradedPlan R) (hBJ : BJ ∈ Plan.gradedPlan R)
    (h : GradedLe CI BJ) (hscope : BJ.1 ⊆ B ∨ BJ.1 ⊆ C) :
    CappedLift (rows I hBA hCA n hA) h := by
  have hn : ¬ A ⊆ BJ.1 := by
    intro ha
    rcases hscope with hb | hc
    · exact hBA (Finset.Subset.antisymm (I.isPlan.subset_of_mem (left_mem I)) (ha.trans hb))
    · exact hCA (Finset.Subset.antisymm (I.isPlan.subset_of_mem (right_mem I)) (ha.trans hc))
  apply CanonicalRecursiveBoundaryTransport.proper_lift I.rows
    (proper_boundary I hBA hCA) n hA h hn
  by_cases he : CI = BJ
  · subst BJ; exact lift_refl
  · exact I.inherited_lift hCI hBJ h he hscope

variable (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)

include hcover in
theorem old_lifts : CanonicalCoatomBountiful.OldLifts I.rows := by
  intro CI BJ hCI hBJ hBJne h
  by_cases he : CI = BJ
  · subst BJ; exact lift_refl
  · exact I.inherited_lift hCI hBJ h he (hcover BJ.1 (Plan.mem_gradedPlan.mp hBJ).1 hBJne)

include hcover in
/-- Proper owner existence is supplied by input completeness, not a new
completeness assumption about the prospective ordinary output. -/
theorem proper_complete {S : Finset ι} (hS : S ∈ I.boundary.plan) (hSA : S ≠ A)
    {j : ℕ} (hj : 0 < j) (hjS : j ≤ S.card) : ∃ d, I.boundary.cell d = (S, j) := by
  change S ∈ R at hS
  exact (I.occupied_iff (J := (S, j)) (Plan.mem_gradedPlan.mpr ⟨hS, hj, hjS⟩)).mpr
    (hcover S hS hSA)

include hcover in
theorem complete_through (J : Finset ι × ℕ)
    (hJ : J ∈ Plan.gradedPlan (carrier I n hA).plan) (hj : J.2 ≤ n + 3) :
    ∃ d, (carrier I n hA).cell d = J :=
  CanonicalRecursiveCoverage.complete_through I.rows (n + 3) hA
    (fun _ hJ hJA => proper_complete I hcover (Plan.mem_gradedPlan.mp hJ).1 hJA
      (Plan.mem_gradedPlan.mp hJ).2.1 (Plan.mem_gradedPlan.mp hJ).2.2) J hJ hj

include hcover in
/-- Constructed initialization and recurrence on these exact rows. Both input
facets must reach the constructed height; no same-grade owner is fabricated. -/
theorem ready (hBcard : n + 3 ≤ B.card) (hCcard : n + 3 ≤ C.card) :
    CanonicalRecursiveRecurrence.Ready I.rows (proper_boundary I hBA hCA) n hA :=
  CanonicalRecursiveInitialized.ready I.rows (proper_boundary I hBA hCA) I.consistent
    (old_lifts I hcover) (left_mem I) (right_mem I) hBA hCA (overlap_mem I) hcover n hA
    hBcard hCcard (fun _ hS hSA _ hj hjS _ => proper_complete I hcover hS hSA hj hjS)

include hcover in
/-- No serving controller, prescribed-owner alignment, selected-ambient
assumption or output-lawfulness hypothesis remains in this actual scope lift. -/
theorem lift (hBcard : n + 3 ≤ B.card) (hCcard : n + 3 ≤ C.card)
    (hCI : CI ∈ Plan.gradedPlan R) (hBJ : BJ ∈ Plan.gradedPlan R)
    (h : GradedLe CI BJ) (hgrade : BJ.2 ≤ n + 3) :
    CappedLift (rows I hBA hCA n hA) h :=
  CanonicalRecursiveInitialized.lift I.rows (proper_boundary I hBA hCA) I.consistent
    (old_lifts I hcover) (left_mem I) (right_mem I) hBA hCA (overlap_mem I) hcover n hA
    hBcard hCcard (fun _ hS hSA _ hj hjS _ => proper_complete I hcover hS hSA hj hjS)
    hCI hBJ h hgrade

end
end VaughtConjecture.Knight.WholeDonorOrdinaryLift
