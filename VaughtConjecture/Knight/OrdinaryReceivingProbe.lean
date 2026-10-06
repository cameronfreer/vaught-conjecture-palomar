/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryReceivingAssembly

/-! # The installed ordinary receiving probe and its selected display

Both input semantic schemes are literal ordered restrictions of the constructed
legal carrier. Its selected display retains both inputs, keeps a named grade-N
gate top, and satisfies the stage bound at every auxiliary. Every lawful whole
section retaining the private labels and that gate's positivity reads the
donor back below the actual cut. Model realization is deliberately separate.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryReceivingProbe
open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref
open OrdinaryReceivingAssembly
noncomputable section

variable {I : Type*} [Fintype I] {nP n : ℕ}
variable {B T : Finset (Fin (n + 5))} {plan : Finset (Finset (Fin (n + 5)))}
variable (W : WholeDonorBoundary.Input Finset.univ B T plan nP (n + 4) (nP + 1))
variable (R : Ref I nP (n + 4) (n + 4) W.right W.left)
variable (hunion : (Finset.univ : Finset (Fin (n + 5))) = B ∪ T)
variable (hface : ∀ i : Cell W.common.scheme,
  ∃ d : W.right.scheme.below (R.A, R.KA),
    d.1 = W.shared.g i ∧ (R.face d).1 = W.shared.f i)

abbrev privateFace : ExactSemanticFace W.leftRows (semScheme W R hunion hface).rows :=
  OrdinaryFinalInstallation.originalFace R (input W R hunion hface)
    (predecessor W R hunion).grade_bound W.left W.placeLeft W.imageLeft (private_ne W)
    (predecessor W R hunion).leftFace

abbrev requestFace : ExactSemanticFace W.rightRows (semScheme W R hunion hface).rows :=
  OrdinaryFinalInstallation.originalFace R (input W R hunion hface)
    (predecessor W R hunion).grade_bound W.right W.placeRight W.imageRight (request_ne W R)
    (predecessor W R hunion).rightFace

theorem private_order : StrictMono (privateFace W R hunion hface).map :=
  OrdinaryFinalInstallation.originalFace_order R (input W R hunion hface)
    (predecessor W R hunion).grade_bound W.left W.placeLeft W.imageLeft (private_ne W)
    (predecessor W R hunion).leftFace (predecessor W R hunion).left_order

theorem request_order : StrictMono (requestFace W R hunion hface).map :=
  OrdinaryFinalInstallation.originalFace_order R (input W R hunion hface)
    (predecessor W R hunion).grade_bound W.right W.placeRight W.imageRight (request_ne W R)
    (predecessor W R hunion).rightFace (predecessor W R hunion).right_order

theorem private_plan : Plan.restrictPlan (semScheme W R hunion hface).scheme.plan B =
    W.left.scheme.plan.image (Finset.image W.placeLeft) := by
  change Plan.restrictPlan (predecessor W R hunion).carrier.plan B = _
  rw [(predecessor W R hunion).plan]
  exact W.planLeft

theorem request_plan : Plan.restrictPlan (semScheme W R hunion hface).scheme.plan T =
    W.right.scheme.plan.image (Finset.image W.placeRight) := by
  change Plan.restrictPlan (predecessor W R hunion).carrier.plan T = _
  rw [(predecessor W R hunion).plan]
  exact W.planRight

theorem private_visible : Finset.univ.image W.placeLeft ∈
    (semScheme W R hunion hface).scheme.plan :=
  OrderedFaceRestriction.visible W.left _ W.placeLeft W.imageLeft
    (private_plan W R hunion hface)

theorem request_visible : Finset.univ.image W.placeRight ∈
    (semScheme W R hunion hface).scheme.plan :=
  OrderedFaceRestriction.visible W.right _ W.placeRight W.imageRight
    (request_plan W R hunion hface)

/-- Ordered exact semantic faces identify the restriction as a semantic scheme,
including every row, not just its cell inventory. -/
theorem restrict_of_ordered_face {m k : ℕ} (P : SemScheme m) (S : SemScheme k)
    (f : Fin m ↪ Fin k) {U : Finset (Fin k)} (hf : Finset.univ.image f = U)
    (E : ExactSemanticFace (PointImageSemantics.rows P.scheme f hf P.rows) S.rows)
    (ho : StrictMono E.map)
    (hp : Plan.restrictPlan S.scheme.plan U = P.scheme.plan.image (Finset.image f)) :
    S.restrictFace f (OrderedFaceRestriction.visible P S.scheme f hf hp) = P := by
  have he := OrderedFaceRestriction.scheme_eq P S.scheme S.rows f hf E ho hp
  refine SemScheme.ext_of_components (congrArg CellScheme.plan he)
    (OrderedFaceRestriction.card_face P S.scheme S.rows f hf E ho hp)
    (fun c => CellScheme.cell_cast_of_eq he c) (fun c d => ?_)
  exact OrderedFaceRestriction.row_eq P S.scheme S.rows f hf E ho hp c d

theorem private_restrict : (semScheme W R hunion hface).restrictFace W.placeLeft
    (private_visible W R hunion hface) = W.left :=
  restrict_of_ordered_face W.left _ W.placeLeft W.imageLeft (privateFace W R hunion hface)
    (private_order W R hunion hface) (private_plan W R hunion hface)

theorem request_restrict : (semScheme W R hunion hface).restrictFace W.placeRight
    (request_visible W R hunion hface) = W.right :=
  restrict_of_ordered_face W.right _ W.placeRight W.imageRight (requestFace W R hunion hface)
    (request_order W R hunion hface) (request_plan W R hunion hface)

/-- The cell map of the literal private restriction is the installed private map. -/
theorem private_toCell (d : Cell W.left.scheme) :
    CellScheme.restrictFace.toCell (semScheme W R hunion hface).scheme W.placeLeft
      (private_visible W R hunion hface)
      (SemScheme.castCell (private_restrict W R hunion hface).symm d) =
        (privateFace W R hunion hface).map d :=
  OrderedFaceRestriction.toCell_eq W.left _ _ W.placeLeft W.imageLeft
    (privateFace W R hunion hface) (private_order W R hunion hface)
    (private_plan W R hunion hface) d

/-- The donor restriction uses the actual installed map, also for noninitial faces. -/
theorem request_toCell (d : Cell W.right.scheme) :
    CellScheme.restrictFace.toCell (semScheme W R hunion hface).scheme W.placeRight
      (request_visible W R hunion hface)
      (SemScheme.castCell (request_restrict W R hunion hface).symm d) =
        (requestFace W R hunion hface).map d :=
  OrderedFaceRestriction.toCell_eq W.right _ _ W.placeRight W.imageRight
    (requestFace W R hunion hface) (request_order W R hunion hface)
    (request_plan W R hunion hface) d

abbrev gate (a : OrdinaryFinalCatalogue.Member R) :
    Cell (semScheme W R hunion hface).scheme :=
  OrdinaryFinalInstallation.marked R (input W R hunion hface) a

abbrev apex : Cell (semScheme W R hunion hface).scheme :=
  FinalGateApex.apex (input W R hunion hface) (Finset.card_fin _)

theorem gate_grade (a : OrdinaryFinalCatalogue.Member R) :
    (semScheme W R hunion hface).scheme.grade (gate W R hunion hface a) = n + 4 := by
  exact congrArg Prod.snd
    ((FinalGateApex.old_index (input W R hunion hface) (Finset.card_fin _)
      ((input W R hunion hface).added a true)).trans
        ((input W R hunion hface).added_index a true))

/-- The model's bottom-pattern test needs a lawful raw display, not a stage type. -/
theorem exists_raw_display :
    ∃ (a : OrdinaryFinalCatalogue.Member R) (r : Cell (semScheme W R hunion hface).scheme → ExtOrd),
      RespectsSemantics (semScheme W R hunion hface).rows r ∧
      (∀ d, r ((requestFace W R hunion hface).map d) = R.p d) ∧
      (∀ d, r ((privateFace W R hunion hface).map d) = R.vact d) ∧
      r (gate W R hunion hface a) = ⊤ ∧ r (apex W R hunion hface) = ⊥ :=
  OrdinaryFinalInstallation.exists_installed_raw_display R (input W R hunion hface)
    (predecessor W R hunion).grade_bound (fun _ _ => rfl) rfl
    (fun _ hz => CanonicalFieldLayer.grid_short _ _ hz)
    (fun a d _ => lower_support W R hunion hface a d) (owners W R hunion hface)
    (predecessor W R hunion).rightFace.map (predecessor W R hunion).leftFace.map
    (lower_request W R hunion hface) (lower_private W R hunion hface)

/-- A lawful selected display with literal original labels, a top marked gate,
a bottom apex and stage bounds at every physical auxiliary. -/
theorem exists_display (α : LimitStage)
    (hP : ∀ d, R.p d ≠ ⊤ → R.p d < ofOrd α.1)
    (hC : ∀ d, R.vact d ≠ ⊤ → R.vact d < ofOrd α.1) :
    ∃ (a : OrdinaryFinalCatalogue.Member R) (r : Cell (semScheme W R hunion hface).scheme → ExtOrd),
      RespectsSemantics (semScheme W R hunion hface).rows r ∧
      (∀ d, r d < ofOrd α.1 ∨ r d = ⊤) ∧
      (∀ d, r ((requestFace W R hunion hface).map d) = R.p d) ∧
      (∀ d, r ((privateFace W R hunion hface).map d) = R.vact d) ∧
      r (gate W R hunion hface a) = ⊤ ∧ r (apex W R hunion hface) = ⊥ :=
  OrdinaryFinalInstallation.exists_installed_display R (input W R hunion hface)
    (predecessor W R hunion).grade_bound α hP hC (fun _ _ => rfl) rfl
    (fun _ hz => CanonicalFieldLayer.grid_short _ _ hz)
    (fun a d _ => lower_support W R hunion hface a d) (owners W R hunion hface)
    (predecessor W R hunion).rightFace.map (predecessor W R hunion).leftFace.map
    (lower_request W R hunion hface) (lower_private W R hunion hface)

/-- Arbitrary lawful physical sections: no chart, admission, synchronization
or selected-family coverage is supplied by the caller. -/
theorem capped_readback {q : Cell (semScheme W R hunion hface).scheme → ExtOrd}
    (hq : RespectsSemantics (semScheme W R hunion hface).rows q)
    (hretain : ∀ d, q ((privateFace W R hunion hface).map d) = R.vact d)
    (a : OrdinaryFinalCatalogue.Member R) (hgate : q (gate W R hunion hface a) ≠ ⊥)
    (d : Cell W.right.scheme) :
    min (q ((requestFace W R hunion hface).map d)) (R.cut R.vactL) =
      min (R.p d) (R.cut R.vactL) :=
  OrdinaryFinalInstallation.capped_readback R (input W R hunion hface)
    (predecessor W R hunion).grade_bound (fun _ _ => rfl) rfl
    (predecessor W R hunion).rightFace.map (predecessor W R hunion).leftFace.map
    (fun d => congrArg Prod.snd ((predecessor W R hunion).rightFace.index d))
    (fun d => congrArg Prod.snd ((predecessor W R hunion).leftFace.index d))
    (lower_request W R hunion hface) (lower_private W R hunion hface) hq hretain a hgate d

theorem readback_below {q : Cell (semScheme W R hunion hface).scheme → ExtOrd}
    (hq : RespectsSemantics (semScheme W R hunion hface).rows q)
    (hretain : ∀ d, q ((privateFace W R hunion hface).map d) = R.vact d)
    (a : OrdinaryFinalCatalogue.Member R) (hgate : q (gate W R hunion hface a) ≠ ⊥)
    {δ : ExtOrd} (hδ : δ ≤ R.cut R.vactL) (d : Cell W.right.scheme) :
    min (q ((requestFace W R hunion hface).map d)) δ = min (R.p d) δ :=
  GradeTailRestoration.cap_below (capped_readback W R hunion hface hq hretain a hgate d) hδ

/-- The selected type has both literal ordered input types as restrictions.
The preceding display theorem also records the named gate and mute apex. -/
theorem exists_selected_type (α : LimitStage)
    (hP : ∀ d, R.p d < ofOrd α.1 ∨ R.p d = ⊤)
    (hC : ∀ d, R.vact d < ofOrd α.1 ∨ R.vact d = ⊤) :
    ∃ t : S α.1 (n + 5), t.scheme = semScheme W R hunion hface ∧
      typeMap W.placeRight t = some (⟨W.right, R.p, hP, R.p_respects⟩ : S α.1 (nP + 1)) ∧
      typeMap W.placeLeft t = some (⟨W.left, R.vact, hC, R.vact_respects⟩ : S α.1 (n + 4)) ∧
      ∃ g : Cell t.scheme.scheme, t.scheme.scheme.grade g = n + 4 ∧ t.label g = ⊤ := by
  obtain ⟨a, r, hr, hb, hp, hc, hg, -⟩ := exists_display W R hunion hface α
    (fun d hd => (hP d).resolve_right hd) (fun d hd => (hC d).resolve_right hd)
  let t : S α.1 (n + 5) := ⟨semScheme W R hunion hface, r, hb, hr⟩
  refine ⟨t, rfl, ?_, ?_, gate W R hunion hface a, gate_grade W R hunion hface a, hg⟩
  · exact typeMap_of_pointImage_face t ⟨W.right, R.p, hP, R.p_respects⟩
      W.placeRight W.imageRight (requestFace W R hunion hface)
      (request_order W R hunion hface) (request_plan W R hunion hface) hp
  · exact typeMap_of_pointImage_face t ⟨W.left, R.vact, hC, R.vact_respects⟩
      W.placeLeft W.imageLeft (privateFace W R hunion hface)
      (private_order W R hunion hface) (private_plan W R hunion hface) hc

end
end VaughtConjecture.Knight.OrdinaryReceivingProbe
