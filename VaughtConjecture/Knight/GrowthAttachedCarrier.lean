/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthReplicatedLegal
public import VaughtConjecture.Knight.WholeDonorAttachment

/-! # The legal growth carrier attached to an actual private context

Reuse the ordered one-new-point attachment with the donor on the left and
the private context on the right, as required by the growth catalogue. The
existing literal root attachment is used directly. Proper-face geometry and
height are derived from strict donor arity and the actual private cap grade.

This constructs the legal scheme and literal face receipts. It does not
assert a stage-bounded selected display or a model receiving theorem.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthAttachedCarrier
open AmalgamationPlan Transform Value ExtOrd Growth
open CellScheme.restrictFace
noncomputable section
variable {n J : ℕ}
  (C : SemScheme J) (P : SemScheme (n + 1)) (Q : SemScheme n)
  (e : Fin n ↪ Fin J)
  (hvC : Finset.univ.image e ∈ C.scheme.plan)
  (hvP : Finset.univ.image Fin.castSuccEmb ∈ P.scheme.plan)
  (hC : C.restrictFace e hvC = Q)
  (hP : P.restrictFace Fin.castSuccEmb hvP = Q)

/-- The same constructed attachment plan, in the growth family's orientation. -/
def boundary : WholeDonorBoundary.Input Finset.univ
    (WholeDonorAttachment.donorScope e) WholeDonorAttachment.privateScope
    (WholeDonorAttachment.plan e C P Q hvC hvP hC hP) n (n + 1) J where
  isPlan := (WholeDonorAttachment.plan_spec e C P Q hvC hvP hC hP).1
  left := P
  right := C
  common := Q
  placeLeft := onePointProj e
  placeRight := Fin.castSuccEmb
  imageLeft := rfl
  imageRight := rfl
  commonLeft := Fin.castSuccEmb
  commonRight := e
  visibleLeft := hvP
  visibleRight := hvC
  faceLeft := hP
  faceRight := hC
  commute := (WholeDonorAttachment.commute e).symm
  intersection := (WholeDonorAttachment.root_right_image e).trans
    ((WholeDonorAttachment.intersection e).symm.trans (Finset.inter_comm _ _))
  planLeft := (WholeDonorAttachment.plan_spec e C P Q hvC hvP hC hP).2.2.2.2
  planRight := (WholeDonorAttachment.plan_spec e C P Q hvC hvP hC hP).2.2.1

variable (X : RelativeData C.scheme C.rows P.scheme P.rows)
  (T : RootAttachment Q Fin.castSuccEmb hvP hP e hvC hC X)
  (hsmall : n + 1 < X.req.N)

theorem threshold_le_arity : X.req.N ≤ J := by
  have hg := C.scheme.grade_le_card_scope X.req.C
  have hc := Finset.card_le_card (Finset.subset_univ (C.scheme.scope X.req.C))
  rw [X.grade_C] at hg
  simpa only [Finset.card_univ, Fintype.card_fin] using hg.trans hc

include hsmall in
theorem donor_arity_lt : n + 1 < J :=
  hsmall.trans_le (threshold_le_arity C P X)

include hsmall in
theorem height : 2 ≤ (Finset.univ : Finset (Fin (J + 1))).card := by
  have := donor_arity_lt C P X hsmall
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

include hsmall in
theorem donor_proper : WholeDonorAttachment.donorScope e ⊂ Finset.univ :=
  Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,
    WholeDonorAttachment.donor_proper e (donor_arity_lt C P X hsmall)⟩

theorem private_proper : WholeDonorAttachment.privateScope (N := J) ⊂ Finset.univ :=
  Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, WholeDonorAttachment.private_proper⟩

local notation "I" => boundary C P Q e hvC hvP hC hP
local notation "hA" => height C P X hsmall
local notation "hB" => donor_proper C P e X hsmall
local notation "hD" => private_proper (J := J)

/-- No supplied plan, occurrence alignment, coverage or carrier lift is needed. -/
abbrev semScheme : SemScheme (J + 1) :=
  GrowthReplicatedLegal.semScheme I X T hA hB hD hsmall

abbrev donorFace := GrowthReplicatedLegal.donor I X T hA hB hD hsmall
abbrev privateFace := GrowthReplicatedLegal.privateFace I X T hA hB hD hsmall

local notation "E" => semScheme C P Q e hvC hvP hC hP X T hsmall

theorem donor_visible : Finset.univ.image (onePointProj e) ∈ (E).scheme.plan :=
  GrowthReplicatedLegal.donor_visible I X T hA hB hD hsmall

theorem private_visible : Finset.univ.image Fin.castSuccEmb ∈ (E).scheme.plan :=
  GrowthReplicatedLegal.private_visible I X T hA hB hD hsmall

theorem restrict_donor :
    (E).restrictFace (onePointProj e) (donor_visible C P Q e hvC hvP hC hP X T hsmall) = P :=
  GrowthReplicatedLegal.restrict_donor I X T hA hB hD hsmall

theorem restrict_private :
    (E).restrictFace Fin.castSuccEmb (private_visible C P Q e hvC hvP hC hP X T hsmall) = C :=
  GrowthReplicatedLegal.restrict_private I X T hA hB hD hsmall

theorem donor_occurrence (d : Cell P.scheme) :
    toCell (E).scheme (onePointProj e) (donor_visible C P Q e hvC hvP hC hP X T hsmall)
      (SemScheme.castCell (restrict_donor C P Q e hvC hvP hC hP X T hsmall).symm d) =
      (donorFace C P Q e hvC hvP hC hP X T hsmall).map d :=
  GrowthReplicatedLegal.donor_occurrence I X T hA hB hD hsmall d

theorem private_occurrence (d : Cell C.scheme) :
    toCell (E).scheme Fin.castSuccEmb (private_visible C P Q e hvC hvP hC hP X T hsmall)
      (SemScheme.castCell (restrict_private C P Q e hvC hvP hC hP X T hsmall).symm d) =
      (privateFace C P Q e hvC hvP hC hP X T hsmall).map d :=
  GrowthReplicatedLegal.private_occurrence I X T hA hB hD hsmall d

end
end VaughtConjecture.Knight.GrowthAttachedCarrier
