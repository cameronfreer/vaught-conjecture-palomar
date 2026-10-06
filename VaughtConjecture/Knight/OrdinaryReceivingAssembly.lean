/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryReceivingSources
public import VaughtConjecture.Knight.OrdinaryPredecessorSupply
public import VaughtConjecture.Knight.OrdinaryFinalBountiful
public import VaughtConjecture.Knight.OrdinaryFinalInstallation

/-! # Constructed legal ordinary receiving carrier

Compose KVC's actual scope predecessor (`8ab4f5e`) with V-C's final pair
theorem (`4eb4e3e`) and the stage-correct weighted/apex installer. Neither
predecessor existence nor output bountifulness is an input. The input consists
of the two literal legal schemes, their attached plan, and reference data
whose face is that same literal overlap. The final threshold is at least four.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryReceivingAssembly
open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref
open SourcePrefixRows OrbitPrefixSupport SharpWitnessComposition
noncomputable section

variable {I : Type*} [Fintype I] {nP n : ℕ}
variable {B T : Finset (Fin (n + 5))} {plan : Finset (Finset (Fin (n + 5)))}
variable (W : WholeDonorBoundary.Input Finset.univ B T plan nP (n + 4) (nP + 1))
variable (R : Ref I nP (n + 4) (n + 4) W.right W.left)
variable (hunion : (Finset.univ : Finset (Fin (n + 5))) = B ∪ T)
variable (hface : ∀ i : Cell W.common.scheme,
  ∃ d : W.right.scheme.below (R.A, R.KA),
    d.1 = W.shared.g i ∧ (R.face d).1 = W.shared.f i)

include W in
theorem private_card : B.card = n + 4 :=
  OrdinaryFinalBountiful.card_S W.placeLeft W.imageLeft

include W in
theorem request_card : T.card = nP + 1 :=
  OrdinaryFinalBountiful.card_S W.placeRight W.imageRight

include W in
theorem private_ne : B ≠ Finset.univ := by
  intro he
  have h := private_card W
  rw [he, Finset.card_univ, Fintype.card_fin] at h
  omega

include R in
theorem request_ne : T ≠ Finset.univ := by
  intro he
  have h := request_card W
  rw [he, Finset.card_univ, Fintype.card_fin] at h
  have := R.arity_lt
  omega

abbrev grid : Finset ExtOrd :=
  PairedSlotComparison.sourceGrid (n + 4) (Fintype.card (Field W.right W.left))

abbrev ceiling : ExtOrd := CanonicalFieldLayer.ceiling (n + 4) (Field W.right W.left)

/-- The global predecessor is built on the given literal boundary. -/
def predecessor : OrdinaryPredecessorSupply.Output W (n + 4) (grid W) (ceiling W) :=
  OrdinaryPredecessorSupply.build W n (private_ne W) (request_ne W R) hunion
    (Finset.card_fin _) (private_card W) ((request_card W) ▸ R.arity_lt)
    (fun _ hz => PairedSlotComparison.sourceGrid_visible hz)
    (PairedSlotComparison.sourceGrid_visible
      (PairedSlotComparison.sourceGrid_endpoint le_rfl))
    (ofOrd_ne_top _) (PairedSlotComparison.sourceGrid_endpoint le_rfl)

abbrev lower (a : OrdinaryFinalCatalogue.Member R) : Cell (predecessor W R hunion).carrier →
    ExtOrd :=
  (predecessor W R hunion).render
    (OrdinaryReceivingSources.boundary_lawful W R hface a)
    (OrdinaryReceivingSources.boundary_bound W R hface a)

theorem lower_private (a : OrdinaryFinalCatalogue.Member R) (d : Cell W.left.scheme) :
    lower W R hunion hface a ((predecessor W R hunion).leftFace.map d) = a.val (.priv d) := by
  exact (congrArg (lower W R hunion hface a)
    ((predecessor W R hunion).left_map d)).trans
      (((predecessor W R hunion).readback _ _ _).trans
        (OrdinaryReceivingSources.boundary_private W R a d))

theorem lower_request (a : OrdinaryFinalCatalogue.Member R) (d : Cell W.right.scheme) :
    lower W R hunion hface a ((predecessor W R hunion).rightFace.map d) = a.val (.req d) := by
  exact (congrArg (lower W R hunion hface a)
    ((predecessor W R hunion).right_map d)).trans
      (((predecessor W R hunion).readback _ _ _).trans
        (OrdinaryReceivingSources.boundary_request W R hface a d))

/-- All final sources use the same fixed grid and ceiling on the same predecessor. -/
def input : FinalGateLayer.Input (predecessor W R hunion).carrier (n + 4)
    (Field W.right W.left) (OrdinaryFinalCatalogue.Member R) := by
  let O := predecessor W R hunion
  refine OrdinaryFinalCatalogue.install R O.rows (by simp) ?_
    (lower W R hunion hface) (fun a => (O.lawful _ _).toBelow _) (fun a d _ => O.bound _ _ d) ?_
  · intro d hd
    have hs : O.carrier.scope d = Finset.univ :=
      Finset.Subset.antisymm (Finset.subset_univ _) hd.1
    exact (not_le_of_gt (O.full_below d hs)) hd.2
  · intro a b h hh hab d _
    exact O.agreement _ _ _ _ hh (CanonicalFieldLayer.grid_bound _ _ hh)
      (OrdinaryReceivingSources.boundary_agreement W R hface hab) d

theorem lower_support (a : OrdinaryFinalCatalogue.Member R)
    (d : Cell (predecessor W R hunion).carrier) :
    Supported (n + 4) ((grid W) : Set ExtOrd) a.val (lower W R hunion hface a d) :=
  ((predecessor W R hunion).support _ _ d).substitute
    (fun _ hz => PairedSlotComparison.sourceGrid_visible hz)
    (OrdinaryReceivingSources.boundary_support W R hface a _)

/-- New owners have own-grade short rows; every argument of any other owner
is an original field. This derives the decoder's long-row alternative. -/
theorem owners (a : OrdinaryFinalCatalogue.Member R)
    (c : (predecessor W R hunion).carrier.below (Finset.univ, n + 4)) :
    (∀ d, Short ((predecessor W R hunion).carrier.grade c.1)
      ((predecessor W R hunion).rows.E c.1 d)) ∨
    (∀ d : (predecessor W R hunion).carrier.below
        ((predecessor W R hunion).carrier.cell c.1),
      ∃ f : Field W.right W.left, lower W R hunion hface a d.1 = a.val f) := by
  rcases (predecessor W R hunion).classification c.1 with hs | ho
  · exact Or.inl hs
  · right
    intro d
    obtain ⟨x, hx⟩ := ho d
    obtain ⟨f, hf⟩ := OrdinaryReceivingSources.boundary_field W R hface a x
    refine ⟨f, ?_⟩
    rw [← hx]
    exact ((predecessor W R hunion).readback _ _ x).trans hf

theorem predecessor_lift (CI BJ : Finset (Fin (n + 5)) × ℕ)
    (hi : CI ∈ Plan.gradedPlan (predecessor W R hunion).carrier.plan)
    (hj : BJ ∈ Plan.gradedPlan (predecessor W R hunion).carrier.plan)
    (h : GradedLe CI BJ) (hne : ¬ GradedLe (Finset.univ, n + 4) BJ) :
    CoatomBoundaryExtension.CappedLift (predecessor W R hunion).rows h := by
  rw [(predecessor W R hunion).plan] at hi hj
  by_cases hs : BJ.1 = Finset.univ
  · exact (predecessor W R hunion).lower_lift CI BJ hi hj h (by
      by_contra hn
      exact hne ⟨hs ▸ Finset.Subset.refl _, by omega⟩)
  · exact (predecessor W R hunion).proper_lift CI BJ hi hj hs h

/-- Exhaustive final-layer lifting, with the predecessor clauses discharged. -/
theorem bountiful : (input W R hunion hface).rows.IsBountiful :=
  OrdinaryFinalBountiful.bountiful R (input W R hunion hface) W.placeLeft W.imageLeft
    (predecessor W R hunion).leftFace (fun _ _ => rfl) rfl rfl
    (fun a d _ => lower_support W R hunion hface a d) (owners W R hunion hface)
    (lower_private W R hunion hface) (Finset.card_fin _)
    (predecessor W R hunion).mute (predecessor_lift W R hunion)

theorem complete_before_final (J : Finset (Fin (n + 5)) × ℕ)
    (hJ : J ∈ Plan.gradedPlan (predecessor W R hunion).carrier.plan)
    (hg : J.2 ≤ n + 4) (hne : J ≠ (Finset.univ, n + 4)) :
    ∃ d, (predecessor W R hunion).carrier.cell d = J := by
  apply (predecessor W R hunion).complete J
  · rwa [(predecessor W R hunion).plan] at hJ
  · by_cases hs : J.1 = Finset.univ
    · right
      by_contra hn
      exact hne (Prod.ext hs (by omega))
    · exact Or.inl hs

/-- The complete coded legal scheme, including its mute full-grade apex. -/
def semScheme : SemScheme (n + 5) :=
  OrdinaryFinalInstallation.semScheme R (input W R hunion hface)
    (predecessor W R hunion).grade_bound (predecessor W R hunion).consistent
    (predecessor W R hunion).coded (bountiful W R hunion hface)
    (complete_before_final W R hunion) (fun _ _ => rfl) rfl
    (fun a d _ => lower_support W R hunion hface a d)

end
end VaughtConjecture.Knight.OrdinaryReceivingAssembly
