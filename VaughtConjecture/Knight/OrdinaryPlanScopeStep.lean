/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryScopeOperator

/-! # The ordinary operation on an actual binary plan step

The two facets are the plan's actual erased facets, not the original small donor
substituted for an as-yet-unconstructed facet. Coverage and both height bounds
are derived here. The two legal facet schemes and their literal common face
are inputs to this local operation; global scope relocation and iteration still
have to construct those inputs coherently.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryPlanScopeStep
open AmalgamationPlan Transform Value ExtOrd AmalgamatedBoundaryPlan OrdinaryScopeOperator
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (s : Step A)

theorem left_proper : A.erase s.a ≠ A :=
  fun he => Finset.notMem_erase s.a A (he.symm ▸ s.ha)

theorem right_proper : A.erase s.b ≠ A :=
  fun he => Finset.notMem_erase s.b A (he.symm ▸ s.hb)

/-- Includes the empty scope; no positive-grade witness is needed for coverage. -/
theorem coverage (T : Finset ι) (hT : T ∈ s.plan) (hTA : T ≠ A) :
    T ⊆ A.erase s.a ∨ T ⊆ A.erase s.b := by
  rcases Finset.mem_union.mp hT with hT | hT
  · rcases Finset.mem_union.mp hT with hT | hT
    · exact Or.inl (s.left_plan.subset_of_mem hT)
    · exact Or.inr (s.right_plan.subset_of_mem hT)
  · exact (hTA (Finset.mem_singleton.mp hT)).elim

theorem left_height {k : ℕ} (hcard : A.card = k + 1) : (A.erase s.a).card = k := by
  rw [Finset.card_erase_of_mem s.ha, hcard]
  omega

theorem right_height {k : ℕ} (hcard : A.card = k + 1) : (A.erase s.b).card = k := by
  rw [Finset.card_erase_of_mem s.hb, hcard]
  omega

variable {m nL nR : ℕ}
variable (I : WholeDonorBoundary.Input A (A.erase s.a) (A.erase s.b) s.plan m nL nR)
variable (k : ℕ) (hk : 0 < k) (hcard : A.card = k + 1)

/-- The constructed lower operation on this precise plan step. -/
def lower : OrdinaryScopeOperator.Core I.rows k :=
  OrdinaryScopeOperator.build I (hBA := left_proper s) (hCA := right_proper s)
    (hcover := coverage s) k hk hcard (left_height s hcard).ge (right_height s hcard).ge

/-- The same operation, closed with a zero highest row. -/
def completed : OrdinaryScopeOperator.Core I.rows (k + 1) := (lower s I k hk hcard).finish hk hcard

theorem complete : (completed s I k hk hcard).carrier.IsComplete :=
  (lower s I k hk hcard).finish_complete hk hcard

def leftFace : ExactSemanticFace I.leftRows (completed s I k hk hcard).rows :=
  (completed s I k hk hcard).face I.leftFace
    (fun h => Finset.notMem_erase s.a A (h s.ha))

def rightFace : ExactSemanticFace I.rightRows (completed s I k hk hcard).rows :=
  (completed s I k hk hcard).face I.rightFace
    (fun h => Finset.notMem_erase s.b A (h s.hb))

theorem left_order : StrictMono (leftFace s I k hk hcard).map :=
  (completed s I k hk hcard).face_order I.leftFace _ I.left_order

theorem right_order : StrictMono (rightFace s I k hk hcard).map :=
  (completed s I k hk hcard).face_order I.rightFace _ I.right_order

/-- Every highest-grade label is forced bottom, including in arbitrary lawful
sections used by a later scope's lifting request. -/
theorem highest_inactive {p : Cell (completed s I k hk hcard).carrier → ExtOrd}
    (hp : RespectsSemantics (completed s I k hk hcard).rows p)
    (d : Cell (completed s I k hk hcard).carrier)
    (hd : (completed s I k hk hcard).carrier.grade d = k + 1) : p d = ⊥ :=
  (lower s I k hk hcard).finish_highest_inactive hk hcard hp d hd

/-- A literal ordered input face also retains its selected values. -/
theorem render_left {p : Cell I.boundary → ExtOrd} (hp : RespectsSemantics I.rows p)
    (ht : ∀ d, p d ≠ ⊤) {G : Finset ExtOrd} {θ : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis (k + 1) z) (hθ : SelfVis (k + 1) θ)
    (d : Cell I.leftScheme) :
    (completed s I k hk hcard).render hp ht G θ ((leftFace s I k hk hcard).map d) =
      p (I.leftFace.map d) :=
  (completed s I k hk hcard).readback hp ht hG hθ (I.leftFace.map d)

theorem render_right {p : Cell I.boundary → ExtOrd} (hp : RespectsSemantics I.rows p)
    (ht : ∀ d, p d ≠ ⊤) {G : Finset ExtOrd} {θ : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis (k + 1) z) (hθ : SelfVis (k + 1) θ)
    (d : Cell I.rightScheme) :
    (completed s I k hk hcard).render hp ht G θ ((rightFace s I k hk hcard).map d) =
      p (I.rightFace.map d) :=
  (completed s I k hk hcard).readback hp ht hG hθ (I.rightFace.map d)

end
end VaughtConjecture.Knight.OrdinaryPlanScopeStep
