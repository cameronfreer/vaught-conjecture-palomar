/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepChart
public import VaughtConjecture.Knight.LowOnlySupplement

/-! # The paired LOW separator on the actual higher rows

For native grades at least three, an arbitrary lawful section that keeps the
private gap owner and low source top and strictly separates the two specified
leaves reads every donor top literally. The serving member and chart are
constructed from that section. The strict physical separator is still an
explicit premise; no model realization or bountifulness is asserted.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedStepReadback
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedStepRows LowOnlyPaddedStepDecode
open LowOnlyPaddedStepChart
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n k : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n}
  {F : LowOnly.Family I.left I.right (k + 1)}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)
  (S : State I.left I.right) (hS : F.Admissible (k + 1) S)
  (hcan : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) (k + 1))
  (hlt : LowSeparator.cutoffCut (k + 1) (LowSeparator.donorField F) S.profile < S.b)

def selectedAnchor : F.Anchor (k + 1) := ⟨S.profile, hcan, S, hS, rfl⟩

def partnerAnchor : F.Anchor (k + 1) :=
  ⟨(LowSeparator.partnerState F S).profile, LowSeparator.partnerState_mem F hcan,
    LowSeparator.partnerState F S,
    LowSeparator.partnerState_admissible F hS hlt (Nat.succ_pos k), rfl⟩

def donorTopAt (d : Cell I.left.scheme) (hd : F.p d = ⊤) :
    (carrier P hnext).below (A, k + 1) :=
  donorAt P hnext ⟨d, Finset.subset_univ _, le_min (F.top_grade d hd) (gradeC_le d)⟩

/-- The raw selected row really separates the two installed leaves. This
does not assert the additional literal-top receipts of a realized display. -/
theorem selected_separates :
    source P hk hnext (selectedAnchor S hS hcan)
        (leafAt P hnext (partnerAnchor S hS hcan hlt)).1 <
      source P hk hnext (selectedAnchor S hS hcan)
        (leafAt P hnext (selectedAnchor S hS hcan)).1 := by
  change source P hk hnext (selectedAnchor S hS hcan)
      (controller P hnext (partnerAnchor S hS hcan hlt)).1 <
    source P hk hnext (selectedAnchor S hS hcan)
      (controller P hnext (selectedAnchor S hS hcan)).1
  rw [source_new, source_ceiling]
  change SourcePrefixRows.cut (LowSeparator.grid (k + 1)) S.profile
    (LowSeparator.partnerState F S).profile < LowSeparator.ceiling (k + 1)
  rw [LowSeparator.partnerState_profile, LowSeparator.cut_partner (k + 1)
    (LowSeparator.donorField F) LowSeparator.cutoffField hcan hlt]
  exact LowSeparator.cutoffCut_lt_ceiling (k + 1) (LowSeparator.donorField F) hcan

/-- All chart receipts are derived from lawfulness on the installed carrier.
Only the two original top receipts and the named-leaf comparison are supplied. -/
theorem donor_top_of_separator
    {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q)
    (hc : q (privateAt P hnext (F.gap.cC le_rfl)) = ⊤)
    (hr : q (privateAt P hnext (F.gap.rC le_rfl)) = ⊤)
    (hsep : q (leafAt P hnext (partnerAnchor S hS hcan hlt)) <
      q (leafAt P hnext (selectedAnchor S hS hcan)))
    (d : Cell I.left.scheme) (hd : F.p d = ⊤) : q (donorTopAt P hnext d hd) = ⊤ := by
  obtain ⟨a, σ, hσ, hread⟩ := exists_top_chart P hk hnext hq
    ⟨privateAt P hnext (F.gap.cC le_rfl),
      (private_grade P hnext (F.gap.cC le_rfl)).trans F.gap.c_grade, hc⟩
  have hc' : σ ((state F a).v F.gap.c) = ⊤ := by
    have he := hread (privateAt P hnext (F.gap.cC le_rfl))
    rw [source_private] at he
    exact he.trans hc
  have hr' : σ ((state F a).v F.gap.r.1) = ⊤ := by
    have he := hread (privateAt P hnext (F.gap.rC le_rfl))
    rw [source_private] at he
    exact he.trans hr
  have hs' := hread (leafAt P hnext (selectedAnchor S hS hcan))
  have ht' := hread (leafAt P hnext (partnerAnchor S hS hcan hlt))
  change σ (source P hk hnext a (controller P hnext (selectedAnchor S hS hcan)).1) = _ at hs'
  change σ (source P hk hnext a (controller P hnext (partnerAnchor S hS hcan hlt)).1) = _ at ht'
  rw [source_new] at hs' ht'
  have hsep' : σ (SourcePrefixRows.cut (LowSeparator.grid (X := Field I.left I.right) (k + 1))
      (state F a).profile (LowSeparator.partnerState F S).profile) <
      σ (SourcePrefixRows.cut (LowSeparator.grid (X := Field I.left I.right) (k + 1))
        (state F a).profile S.profile) := by
    simpa only [state_profile, Family.fields, selectedAnchor, partnerAnchor] using
      ht'.trans_lt (hsep.trans_eq hs'.symm)
  have htop := LowSeparator.serving_readback F (state_admissible F a) hcan hlt
    hσ hsep' hc' hr' d hd
  have he := hread (donorTopAt P hnext d hd)
  exact he.symm.trans ((congrArg σ (source_donor P hk hnext a
    ⟨d, Finset.subset_univ _, le_min (F.top_grade d hd) (gradeC_le d)⟩)).trans htop)

end
end VaughtConjecture.Knight.LowOnlyPaddedStepReadback
