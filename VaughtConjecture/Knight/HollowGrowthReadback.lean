/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HollowGrowthRealization
public import VaughtConjecture.Knight.GrowthCappedReadback

/-! # Exact hollow donor readback on the constructed legal carrier

On the legal carrier of an acquired hollow-growth input, any lawful section retaining the
actual private labels on the installed private occurrences reads the requested donor labels
on every installed donor occurrence, tops included (`donor_readback_of_section`).  This is
the positive-cap theorem `GrowthCappedReadback.full_correct` on the attached boundary:
admission of the recognized state at the activation grade is derived from the section,
its private bottom class is the actual one, and `exact_of_correct` reads the donor.

Every coface of the actual private context on this carrier retains the private labels
(`coface_private`), so its donor face is literally the requested donor
(`coface_donor_readback`). The exact-receiving module composes this with actual donor
occurrence and root descent. No
supplied admission, synchronization, chart or readback hypothesis; no carrier change. -/

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

/-- **Exact hollow donor readback.**  A lawful section of the legal carrier's rows that
retains the actual private labels reads the requested donor labels on every installed donor
occurrence, tops included. -/
theorem donor_readback_of_section {v : Cell I.legalCarrier.scheme → ExtOrd}
    (hv : RespectsSemantics I.legalCarrier.rows v)
    (hpriv : ∀ d, v (I.privateFace.map d) = D.context.type.label d) (d : Cell q.scheme.scheme) :
    v (I.donorFace.map d) = q.label d := by
  have hc := GrowthCappedReadback.full_correct
    (GrowthAttachedCarrier.boundary D.context.type.scheme q.scheme p.scheme D.face
      I.hvC I.hvP I.hC I.hP)
    I.relative I.attachment
    (GrowthAttachedCarrier.height D.context.type.scheme q.scheme I.relative I.donor_arity_lt)
    (GrowthAttachedCarrier.donor_proper D.context.type.scheme q.scheme D.face I.relative
      I.donor_arity_lt)
    (GrowthAttachedCarrier.private_proper (J := D.context.arity)) _ _ I.donor_arity_lt
    (by omega) hv _ I.actual_inClass (I.relative.cap_ne_bot I.actual_inClass) hpriv
  exact congrFun (I.exact_of_correct hc) d

/-- Every coface of the actual private context on the legal carrier reads the requested
donor literally on its installed donor face. -/
theorem coface_donor_readback {r : S α.1 (D.context.arity + 1)}
    (hr : r.scheme = I.legalCarrier) (hco : IsCoface D.context.type r)
    (d : Cell q.scheme.scheme) :
    r.label (SemScheme.castCell hr.symm (I.donorFace.map d)) = q.label d := by
  have hpriv := I.coface_private hr hco
  obtain ⟨E, v, hb, hv⟩ := r
  dsimp only at hr
  subst E
  exact I.donor_readback_of_section hv hpriv d

end

end VaughtConjecture.Knight.HollowGrowthTemplate.Input
