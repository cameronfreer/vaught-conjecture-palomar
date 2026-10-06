/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthAttachedCarrier
public import VaughtConjecture.Knight.HollowGrowthAdmission

/-! # The constructed legal carrier of an acquired hollow-growth input

The model-acquired scalar input now supplies the actual legal scheme on the
private context plus one fresh point, not an interface asserting its existence.
Both original schemes are literal ordered restrictions, and the model-domain
extension uses exactly the installed private occurrence map.

Selected-display stage bounds, physical readback and the model's receiving
application remain separate consumers of this concrete carrier.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.HollowGrowthTemplate.Input
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor
noncomputable section
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}
  {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {q : S α.1 (n + 1)} {Nmin : ℕ}
  {D : HollowGrowthReference.Data (W := W) t p (donorRequests q) (n + 1) Nmin}
  (I : Input q D)

/-- All attachment, geometry and carrier-legality premises are constructed. -/
abbrev legalCarrier : SemScheme (D.context.arity + 1) :=
  GrowthAttachedCarrier.semScheme D.context.type.scheme q.scheme p.scheme D.face
    I.hvC I.hvP I.hC I.hP I.relative I.attachment I.donor_arity_lt

abbrev privateFace :=
  GrowthAttachedCarrier.privateFace D.context.type.scheme q.scheme p.scheme D.face
    I.hvC I.hvP I.hC I.hP I.relative I.attachment I.donor_arity_lt

abbrev donorFace :=
  GrowthAttachedCarrier.donorFace D.context.type.scheme q.scheme p.scheme D.face
    I.hvC I.hvP I.hC I.hP I.relative I.attachment I.donor_arity_lt

theorem private_visible : Finset.univ.image Fin.castSuccEmb ∈ I.legalCarrier.scheme.plan :=
  GrowthAttachedCarrier.private_visible D.context.type.scheme q.scheme p.scheme D.face
    I.hvC I.hvP I.hC I.hP I.relative I.attachment I.donor_arity_lt

theorem donor_visible : Finset.univ.image (onePointProj D.face) ∈ I.legalCarrier.scheme.plan :=
  GrowthAttachedCarrier.donor_visible D.context.type.scheme q.scheme p.scheme D.face
    I.hvC I.hvP I.hC I.hP I.relative I.attachment I.donor_arity_lt

theorem restrict_private :
    I.legalCarrier.restrictFace Fin.castSuccEmb I.private_visible = D.context.type.scheme :=
  GrowthAttachedCarrier.restrict_private D.context.type.scheme q.scheme p.scheme D.face
    I.hvC I.hvP I.hC I.hP I.relative I.attachment I.donor_arity_lt

theorem restrict_donor :
    I.legalCarrier.restrictFace (onePointProj D.face) I.donor_visible = q.scheme :=
  GrowthAttachedCarrier.restrict_donor D.context.type.scheme q.scheme p.scheme D.face
    I.hvC I.hvP I.hC I.hP I.relative I.attachment I.donor_arity_lt

theorem extendsDomain : ExtendsDomain D.context.type I.legalCarrier :=
  ⟨I.private_visible, I.restrict_private⟩

theorem extendsDomain_cellOf (d : Cell D.context.type.scheme.scheme) :
    I.extendsDomain.cellOf d = I.privateFace.map d :=
  GrowthAttachedCarrier.private_occurrence D.context.type.scheme q.scheme p.scheme D.face
    I.hvC I.hvP I.hC I.hP I.relative I.attachment I.donor_arity_lt d

theorem donor_occurrence (d : Cell q.scheme.scheme) :
    CellScheme.restrictFace.toCell I.legalCarrier.scheme (onePointProj D.face) I.donor_visible
      (SemScheme.castCell I.restrict_donor.symm d) = I.donorFace.map d :=
  GrowthAttachedCarrier.donor_occurrence D.context.type.scheme q.scheme p.scheme D.face
    I.hvC I.hvP I.hC I.hP I.relative I.attachment I.donor_arity_lt d

theorem cap_grade : I.legalCarrier.scheme.grade (I.privateFace.map D.cap) =
    D.context.type.topGrade :=
  (congrArg Prod.snd (I.privateFace.index D.cap)).trans D.cap_grade

/-- Coface consistency retains the actual cap and every reference literally;
the pattern clause is not needed for this fact. -/
theorem coface_private {r : S α.1 (D.context.arity + 1)}
    (hr : r.scheme = I.legalCarrier) (hco : IsCoface D.context.type r)
    (d : Cell D.context.type.scheme.scheme) :
    r.label (SemScheme.castCell hr.symm (I.privateFace.map d)) = D.context.type.label d := by
  obtain ⟨s, v, hb, hv⟩ := r
  dsimp only at hr
  subst s
  rw [← I.extendsDomain_cellOf d]
  exact hco.label_cellOf d

end
end VaughtConjecture.Knight.HollowGrowthTemplate.Input
