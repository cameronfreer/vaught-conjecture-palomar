/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HollowGrowthCarrier
public import VaughtConjecture.Knight.ActualOccurrence

/-! # Generalized saturation on the constructed hollow-growth carrier

The legal domain extends the actual private type, so clause (4)(a)(i)
realizes it directly. No selected display, stage bound or bottom-pattern
request is required for this realization. Coface consistency retains the
whole private face, in particular its top cap. Donor restriction recovers
an actual fresh tuple on the donor's exact scheme.

This file deliberately does not assert that its donor labels are the
requested labels: that is the separate arbitrary-section readback theorem.
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

/-- Actual realization, without a selected-display or pattern hypothesis. -/
theorem realizes_carrier (hM : W.IsModel) :
    W.RealizesSome D.context.tuple D.context.type (GenSatFamily I.legalCarrier) :=
  hM.genSat D.context.tuple D.context.type D.context.eval_eq I.legalCarrier I.extendsDomain

theorem coface_cap_top {r : S α.1 (D.context.arity + 1)}
    (hr : r.scheme = I.legalCarrier) (hco : IsCoface D.context.type r) :
    r.label (SemScheme.castCell hr.symm (I.privateFace.map D.cap)) = ⊤ :=
  (I.coface_private hr hco D.cap).trans D.cap_top

/-- The donor restriction has its literal scheme and installed occurrence
readouts, before any correctness or equality of donor labels is asserted. -/
theorem donor_restriction {r : S α.1 (D.context.arity + 1)}
    (hr : r.scheme = I.legalCarrier) :
    ∃ s : S α.1 (n + 1), typeMap (onePointProj D.face) r = some s ∧
      ∃ he : s.scheme = q.scheme, ∀ d : Cell q.scheme.scheme,
        s.label (SemScheme.castCell he.symm d) =
          r.label (SemScheme.castCell hr.symm (I.donorFace.map d)) := by
  obtain ⟨s, hs, he, hmap⟩ := exists_restriction_with_map (onePointProj D.face)
    I.donor_visible I.restrict_donor I.donorFace.map I.donor_occurrence hr
  refine ⟨s, hs, he, ?_⟩
  intro d
  rw [← hmap d, label_mapCell]

/-- Generalized saturation and exact parent consistency supply an actual
donor tuple, fresh over the public root and on the requested exact scheme.
No equality with the requested labelling is concluded here. -/
theorem exists_donor_occurrence (hM : W.IsModel) :
    ∃ (y : M) (hy : y ∉ Set.range D.context.tuple)
      (r : S α.1 (D.context.arity + 1)) (hr : r.scheme = I.legalCarrier),
      IsCoface D.context.type r ∧
      W.eval (snoc D.context.tuple y hy) = some r ∧
      ∃ (hyRoot : y ∉ Set.range t) (s : S α.1 (n + 1)),
        typeMap (onePointProj D.face) r = some s ∧
        W.eval (snoc t y hyRoot) = some s ∧
        ∃ he : s.scheme = q.scheme, ∀ d : Cell q.scheme.scheme,
          s.label (SemScheme.castCell he.symm d) =
            r.label (SemScheme.castCell hr.symm (I.donorFace.map d)) := by
  obtain ⟨y, hy, r, hr, hco, heval⟩ := I.realizes_carrier hM
  obtain ⟨s, hproj, he, hread⟩ := I.donor_restriction hr
  obtain ⟨hyRoot, _, hev⟩ :=
    restrict_actual_extension hM.consistent D.face D.face_tuple hy heval hproj
  exact ⟨y, hy, r, hr, hco, heval, hyRoot, s, hproj, hev, he, hread⟩

end
end VaughtConjecture.Knight.HollowGrowthTemplate.Input
