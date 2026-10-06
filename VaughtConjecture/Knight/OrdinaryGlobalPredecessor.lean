/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryProperPredecessor

/-! # The ordinary global predecessor, stopping below the final gate

Complete every proper scope first, then add full-scope grades through N-1.
Retained private grade-N owners are never subjected to a grade-(N-1) bound.
This module treats N = n+4, using the initialized recursive seed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryGlobalPredecessor
open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension
open SourcePrefixRows OrbitPrefixSupport OrdinaryProperPredecessor
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
variable {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)
variable (n : ℕ) {G : Finset ExtOrd} {θ : ExtOrd}
variable (X : Completed I (n + 4) G θ) (hcard : A.card = n + 5)

include hcard in
omit [DecidableEq ι] in
theorem height : n + 3 ≤ A.card := by omega
abbrev carrier := CanonicalRecursiveContract.carrier X.state.rows n (height n hcard)
abbrev rows := CanonicalRecursiveSemantics.rows X.state.rows (proper I X) n (height n hcard)
abbrev old := CanonicalRecursiveInventory.boundary X.state.rows (n + 3) (height n hcard)
def original : Cell I.boundary ↪o Cell (carrier I n X hcard) :=
  X.state.original.trans (old I n X hcard)

theorem original_index (d : Cell I.boundary) :
    (carrier I n X hcard).cell (original I n X hcard d) = I.boundary.cell d :=
  (CanonicalRecursiveInventory.boundary_cell _ _ _ _).trans (X.state.index d)

theorem original_row (c : Cell I.boundary) (d : I.boundary.below (I.boundary.cell c)) :
    (rows I n X hcard).E (original I n X hcard c) ⟨original I n X hcard d.1, by
      rw [original_index, original_index]; exact d.2⟩ = I.rows.E c d :=
  (CanonicalRecursiveLiteralRows.row X.state.rows (proper I X) n (height n hcard)
    (X.state.original c)
      ⟨X.state.original d.1, by rw [X.state.index, X.state.index]; exact d.2⟩).trans
    (X.state.row c d)

theorem plan : (carrier I n X hcard).plan = R :=
  (CanonicalRecursiveBoundaryTransport.plan_eq _ _ _).trans X.state.plan

theorem consistent : (rows I n X hcard).IsConsistent :=
  CanonicalRecursiveSemantics.consistent _ (proper I X) X.state.consistent n (height n hcard)

theorem coded : (rows I n X hcard).IsCoded :=
  CanonicalRecursiveCoding.coded _ (proper I X) X.state.coded n (height n hcard)

/-- The full scope is stopped below N. Proper grade-N cells are retained. -/
theorem coverage (d : Cell (carrier I n X hcard)) :
    (∃ c, old I n X hcard c = d) ∨
      (carrier I n X hcard).scope d = A ∧ (carrier I n X hcard).grade d ≤ n + 3 := by
  rcases RecursiveSourceCarrier.classify X.state.carrier
    (CanonicalRecursiveInventory.Profile X.state.rows) (n + 3) (height n hcard) d with
    ⟨c, rfl⟩ | ⟨j, _, hj, he⟩
  · exact Or.inl ⟨c, rfl⟩
  · refine Or.inr ⟨congrArg Prod.fst he, ?_⟩
    change ((carrier I n X hcard).cell d).2 ≤ _
    rw [he]
    exact hj

theorem grade_bound (d : Cell (carrier I n X hcard)) : (carrier I n X hcard).grade d ≤ n + 4 := by
  rcases coverage I n X hcard d with ⟨c, rfl⟩ | ⟨_, hg⟩
  · change ((carrier I n X hcard).cell (old I n X hcard c)).2 ≤ _
    rw [CanonicalRecursiveInventory.boundary_cell]
    have hs := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨X.state.carrier.isPlan.subset_of_mem (X.state.carrier.scope_mem_plan c), proper I X c⟩)
    have hg := X.state.carrier.grade_le_card_scope c
    change X.state.carrier.grade c ≤ _
    omega
  · omega

theorem complete {J : Finset ι × ℕ} (hJ : J ∈ Plan.gradedPlan R)
    (hscope : J.1 ≠ A ∨ J.2 ≤ n + 3) : ∃ d, (carrier I n X hcard).cell d = J := by
  rcases hscope with hJA | hj
  · obtain ⟨d, hd⟩ := OrdinaryProperPredecessor.complete I X hJ hJA
    exact ⟨old I n X hcard d, (CanonicalRecursiveInventory.boundary_cell _ _ _ _).trans hd⟩
  · exact CanonicalRecursiveCoverage.complete_through X.state.rows (n + 3)
      (height n hcard) (ready I X).complete J
      (by rwa [CanonicalRecursiveBoundaryTransport.plan_eq, X.state.plan]) hj

theorem proper_lift {CI BJ : Finset ι × ℕ} (hCI : CI ∈ Plan.gradedPlan R)
    (hBJ : BJ ∈ Plan.gradedPlan R) (hJA : BJ.1 ≠ A) (h : GradedLe CI BJ) :
    CappedLift (rows I n X hcard) h := by
  apply CanonicalRecursiveBoundaryTransport.proper_lift _ (proper I X) n (height n hcard) h
    (fun hs => hJA (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hBJ).1) hs))
  exact lifts I X CI BJ (by rwa [X.state.plan]) (by rwa [X.state.plan]) hJA h

/-- The binary facets are derived from this completed raw plan. The small
donor is not incorrectly used as the second tall facet. -/
theorem lower_lift {CI BJ : Finset ι × ℕ} (hCI : CI ∈ Plan.gradedPlan R)
    (hBJ : BJ ∈ Plan.gradedPlan R) (h : GradedLe CI BJ) (hj : BJ.2 ≤ n + 3) :
    CappedLift (rows I n X hcard) h := by
  obtain ⟨s, hs⟩ := AmalgamatedBoundaryPlan.exists_step X.state.carrier.isPlan
    (by omega : 2 ≤ A.card)
  have hL := OrdinaryPlanScopeStep.left_height s (k := n + 4) hcard
  have hR := OrdinaryPlanScopeStep.right_height s (k := n + 4) hcard
  exact CanonicalRecursiveInitialized.lift X.state.rows (proper I X) X.state.consistent
    (lifts I X) (OrdinaryRawScope.left_mem s hs.symm) (OrdinaryRawScope.right_mem s hs.symm)
    (OrdinaryPlanScopeStep.left_proper s) (OrdinaryPlanScopeStep.right_proper s)
    (OrdinaryRawScope.overlap_mem s hs.symm) (OrdinaryRawScope.coverage s hs.symm)
    n (height n hcard) (by omega) (by omega)
    (fun S hS hSA j hj hjS _ => (ready I X).complete (S, j)
      (Plan.mem_gradedPlan.mpr ⟨hS, hj, hjS⟩) hSA)
    (by rwa [X.state.plan]) (by rwa [X.state.plan]) h hj

def leftFace (hBA : B ≠ A) : ExactSemanticFace I.leftRows (rows I n X hcard) :=
  CanonicalRecursiveFace.face (OrdinaryProperPredecessor.leftFace I X)
    (fun h => hBA (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (WholeDonorOrdinaryLift.left_mem I)) h))
    (proper I X) n (height n hcard)

def rightFace (hCA : C ≠ A) : ExactSemanticFace I.rightRows (rows I n X hcard) :=
  CanonicalRecursiveFace.face (OrdinaryProperPredecessor.rightFace I X)
    (fun h => hCA (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (WholeDonorOrdinaryLift.right_mem I)) h))
    (proper I X) n (height n hcard)

theorem left_order (hBA : B ≠ A) : StrictMono (leftFace I n X hcard hBA).map :=
  (old I n X hcard).strictMono.comp (OrdinaryProperPredecessor.left_order I X)

theorem right_order (hCA : C ≠ A) : StrictMono (rightFace I n X hcard hCA).map :=
  (old I n X hcard).strictMono.comp (OrdinaryProperPredecessor.right_order I X)

theorem below_old (c : Cell X.state.carrier)
    (d : (carrier I n X hcard).below ((carrier I n X hcard).cell (old I n X hcard c))) :
    ∃ e : X.state.carrier.below (X.state.carrier.cell c), old I n X hcard e.1 = d.1 := by
  rcases coverage I n X hcard d.1 with ⟨e, he⟩ | ⟨hs, _⟩
  · refine ⟨⟨e, ?_⟩, he⟩
    have hd := d.2
    rw [← he, CanonicalRecursiveInventory.boundary_cell,
      CanonicalRecursiveInventory.boundary_cell] at hd
    exact hd
  · have hd := d.2.1
    change (carrier I n X hcard).scope d.1 ⊆
      ((carrier I n X hcard).cell (old I n X hcard c)).1 at hd
    rw [hs, CanonicalRecursiveInventory.boundary_cell] at hd
    exact (proper I X c (Finset.Subset.antisymm
      (X.state.carrier.isPlan.subset_of_mem (X.state.carrier.scope_mem_plan c)) hd)).elim

/-- The decoder classification survives the final recursion as well as every
proper-scope installation. No shortness is imposed on inherited original rows. -/
theorem classification : OrderedScopeRelocation.OwnerClassification
    (rows I n X hcard) (original I n X hcard) := by
  intro z
  rcases coverage I n X hcard z with ⟨c, rfl⟩ | ⟨hs, _⟩
  · rcases X.state.classification c with hshort | horig
    · left
      intro d
      obtain ⟨e, he⟩ := below_old I n X hcard c d
      have hd : d = ⟨old I n X hcard e.1, by
          rw [CanonicalRecursiveInventory.boundary_cell,
            CanonicalRecursiveInventory.boundary_cell]; exact e.2⟩ := Subtype.ext he.symm
      rw [hd, CanonicalRecursiveLiteralRows.row]
      change SharpWitnessComposition.Short
        ((carrier I n X hcard).cell (old I n X hcard c)).2 _
      rw [CanonicalRecursiveInventory.boundary_cell]
      exact hshort e
    · right
      intro d
      obtain ⟨e, he⟩ := below_old I n X hcard c d
      obtain ⟨x, hx⟩ := horig e
      exact ⟨x, (congrArg (old I n X hcard) hx).trans he⟩
  · exact Or.inl ((CanonicalRecursiveSemantics.state X.state.rows
      (proper I X) n (height n hcard)).full_short z hs)

theorem nonprivate_mute (hB : B.card = n + 4) (hC : C.card < n + 4)
    (d : Cell (carrier I n X hcard)) (hg : (carrier I n X hcard).grade d = n + 4)
    (hd : (carrier I n X hcard).scope d ≠ B) :
    (rows I n X hcard).E d ⟨d, GradedLe.refl _⟩ = ⊥ := by
  rcases coverage I n X hcard d with ⟨c, rfl⟩ | ⟨_, hb⟩
  · have hc : X.state.carrier.grade c = n + 4 := by
      simpa only [CellScheme.grade, CanonicalRecursiveInventory.boundary_cell] using hg
    have hscope : X.state.carrier.scope c ≠ B := by
      simpa only [CellScheme.scope, CanonicalRecursiveInventory.boundary_cell] using hd
    exact (CanonicalRecursiveLiteralRows.row X.state.rows (proper I X) n (height n hcard)
      c ⟨c, GradedLe.refl _⟩).trans
      (OrdinaryProperPredecessor.nonprivate_mute I X hcard hB hC c hc hscope)
  · omega

variable (hG : ∀ z ∈ G, SelfVis (n + 4) z) (hθ : SelfVis (n + 4) θ)
variable (htθ : θ ≠ ⊤) (hθG : θ ∈ G)
variable {p : Cell I.boundary → ExtOrd} (hp : RespectsSemantics I.rows p) (hb : ∀ d, p d ≤ θ)

def render : Cell (carrier I n X hcard) → ExtOrd :=
  (CanonicalRecursiveSemantics.state X.state.rows (proper I X) n (height n hcard)).sectionOf
    (height n hcard) ((X.state.lawful hp hb).toBelow (A, A.card))
    (fun d => ne_top_of_le_ne_top htθ (X.state.bound hp hb d)) G θ

include hG hθ in
theorem readback (d : Cell I.boundary) :
    render I n X hcard htθ hp hb (original I n X hcard d) = p d :=
  ((CanonicalRecursiveSemantics.state X.state.rows (proper I X) n (height n hcard)).section_boundary
    (height n hcard) _ _ (fun z hz => selfVis_mono (hG z hz) (by omega))
    (selfVis_mono hθ (by omega)) (X.state.original d)).trans (X.state.readback hp hb d)

include hG hθ in
theorem lawful : RespectsSemantics (rows I n X hcard) (render I n X hcard htθ hp hb) := by
  apply ((CanonicalRecursiveSemantics.state X.state.rows
    (proper I X) n (height n hcard)).section_lawful
    (height n hcard) _ _ (fun z hz => selfVis_mono (hG z hz) (by omega))
    (selfVis_mono hθ (by omega))).toRespects
  intro d
  exact ⟨(carrier I n X hcard).isPlan.subset_of_mem ((carrier I n X hcard).scope_mem_plan d),
    (grade_bound I n X hcard d).trans (by omega)⟩

include hθ in
theorem bound (d : Cell (carrier I n X hcard)) : render I n X hcard htθ hp hb d ≤ θ :=
  (CanonicalRecursiveSemantics.state X.state.rows (proper I X) n (height n hcard)).section_bound
    (height n hcard) _ _ (selfVis_mono hθ (by omega)) (X.state.bound hp hb) d

include hG hθG in
theorem supported (d : Cell (carrier I n X hcard)) :
    Supported (n + 4) (G : Set ExtOrd) p (render I n X hcard htθ hp hb d) :=
  ((CanonicalRecursiveSemantics.state X.state.rows
    (proper I X) n (height n hcard)).section_supported
    (height n hcard) _ _ (by omega) hθG d).substitute hG (X.state.support hp hb)

include hG hθ in
theorem agreement {q : Cell I.boundary → ExtOrd} (hq : RespectsSemantics I.rows q)
    (hqb : ∀ d, q d ≤ θ) {γ : ExtOrd} (hγ : γ ∈ G) (hγθ : γ ≤ θ) (he : Agree p q γ) :
    Agree (render I n X hcard htθ hp hb) (render I n X hcard htθ hq hqb) γ :=
  (CanonicalRecursiveSemantics.state X.state.rows (proper I X) n (height n hcard)).section_agreement
    (height n hcard) _ _ _ _ (fun z hz => selfVis_mono (hG z hz) (by omega))
    (selfVis_mono hθ (by omega)) hγ hγθ (X.state.agreement hp hb hq hqb hγ hγθ he)

end
end VaughtConjecture.Knight.OrdinaryGlobalPredecessor
