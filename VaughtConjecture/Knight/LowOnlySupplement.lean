/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowSeparatorPaired

/-! # Two supplementary lemmas on the LOW-only family

Both are consequences of the existing family; neither discharges the admissibility of a serving
profile, and nothing about the cutoff, the non-top maximum, the source gap, or the future fields
is weakened or removed.

* **Projection** (`project`): every compatible pair of lawful current sections of the two original
  schemes, literally equal on the current common root, is the current projection of an admitted
  state with cutoff bottom and every future field bottom.  The LOW clause is vacuous because the
  cutoff is bottom, so this records only that LOW imposes no restriction on the current
  projection; it says nothing about the admissibility of any serving profile with a positive
  cutoff.
* **Conditional selected-controller readback** (`Certified`, `certified_of_admissible`,
  `certified_readback`): the readback calculation of `donor_top_readback` uses only the inequality
  `e ≤ evr (u d) K K` at each donor top, where `e` is the private frontier.  That inequality is
  isolated as an explicit certificate on a state; an admitted state whose LOW clause is active
  carries it (`certified_of_admissible`), and a chart reading the owner and low source as top
  reads every donor top as top from the certificate alone (`certified_readback`).  The
  certificate is a hypothesis of the readback, not a conclusion about serving profiles.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.LowSeparator

open Transform Value ExtOrd AmalgamationPlan CappedDonor SharpWitnessComposition LowOnly

variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

section Projection

/-- **Current-boundary projection.**  Lawful current sections `u`, `v` of the two original
schemes, literally equal on the current common root, are the current projection of an admitted
state with cutoff `⊥` and every future field `⊥` (`FutureEq` with the zero state). -/
theorem project {j : ℕ} {u : P.scheme.below (effC n j) → ExtOrd}
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u)
    (hv : RespectsSemanticsBelow C.rows (effC n j) v)
    (hface : ∀ a : P.scheme.below (faceIndex F.root.A j),
      u (CellScheme.below.mono (faceIndex_le F.root.A j) a) =
        v (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a))) :
    ∃ S : State P C, F.Admissible j S ∧ S.lowerP j = u ∧ S.lowerC j = v ∧ S.b = ⊥ ∧
      (Family.zero : State P C).FutureEq j S :=
  ⟨(Family.zero : State P C).replace u v ⊥,
    ⟨(F.zero_admissible j).toSource.replace F hu hv ⊥ hface, selfVis_bot _,
      fun _ hm => (not_lt_bot hm).elim⟩,
    State.replace_lowerP _ _ _ _, State.replace_lowerC _ _ _ _, rfl,
    State.replace_future _ _ _ _⟩

end Projection

section Certificate

/-- **The readback certificate of a state**: at every donor top the private frontier
`min (v c) (evr (v r) K K)` lies below the `K`-replacement of the donor-top source.  This is
exactly what the readback calculation consumes; the LOW clause of an admitted state supplies the
stronger `max b e ≤ u d`. -/
def Certified (S : State P C) : Prop :=
  ∀ d, F.p d = ⊤ →
    min (S.v F.gap.c) (extVisibilityReplace (S.v F.gap.r.1) K K) ≤
      extVisibilityReplace (S.u d) K K

/-- An admitted state whose LOW clause is active is certified. -/
theorem certified_of_admissible {S : State P C} (hS : F.Admissible K S)
    (hm : F.maximum S < S.b) : Certified F S := by
  intro d hd
  have hlow := hS.low le_rfl hm d hd
  change max S.b (min (S.v F.gap.c) (extVisibilityReplace (S.v F.gap.r.1) K K)) ≤ S.u d at hlow
  exact ((le_max_right _ _).trans hlow).trans (TopSupport.le_evr_self _ _)

/-- **Conditional selected-controller readback**: a chart reading the owner and the low source of
a certified state as top reads every donor top as top.  The certificate is a hypothesis; nothing
here shows that a serving profile is admitted. -/
theorem certified_readback {S : State P C} (hS : Certified F S) {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop K) σ) (hc : σ (S.v F.gap.c) = ⊤) (hr : σ (S.v F.gap.r.1) = ⊤)
    (d : Cell P.scheme) (hd : F.p d = ⊤) : σ (S.u d) = ⊤ := by
  have h1 := hσ.mono (hS d hd)
  rw [hσ.mono.map_min, hσ.comm_gTop _ le_rfl, hσ.comm_gTop _ le_rfl, hc, hr,
    extVisibilityReplace_top, min_self] at h1
  by_contra hne
  exact TopSupport.evr_ne_top hne K K (top_le_iff.mp h1)

/-- `donor_top_readback` is the composite of the two lemmas above. -/
theorem donor_top_readback' {S : State P C} (hS : F.Admissible K S) (hm : F.maximum S < S.b)
    {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop K) σ) (hc : σ (S.v F.gap.c) = ⊤)
    (hr : σ (S.v F.gap.r.1) = ⊤) (d : Cell P.scheme) (hd : F.p d = ⊤) : σ (S.u d) = ⊤ :=
  certified_readback F (certified_of_admissible F hS hm) hσ hc hr d hd

end Certificate

end VaughtConjecture.Knight.LowSeparator
