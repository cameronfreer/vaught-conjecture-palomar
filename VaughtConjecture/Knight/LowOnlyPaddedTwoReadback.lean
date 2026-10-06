/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepReadback

/-! # Paired-separator readback on the unchanged grade-two seed

The grade-two installer has weighted-source rows with an empty weighted-node
type. Its actual leaf equations supply the same paired readback as the higher
recursive steps. The strict physical separator remains an explicit premise.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedTwoReadback
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedSuccessor LowOnlyPaddedDecode LowOnlyPaddedContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right 2)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

def leafAt (a : F.Anchor 2) : (carrier I F hroot hA hB hC).below (A, 2) :=
  ⟨leaf I F hroot hA hB hC a, by rw [leaf_index]; exact GradedLe.refl _⟩

theorem source_leaf (a b : F.Anchor 2) :
    source I F hroot hA hB hC a (leafAt I F hroot hA hB hC b).1 =
      SourcePrefixRows.cut (LowSeparator.grid (X := Field I.left I.right) 2) a.val b.val := by
  let J := input I F hroot hA hB hC
  change WeightedSourcePrefixLayer.master J.data J.weight
    (J.controller (a, none)) (J.controller (b, none)).1 = _
  rw [WeightedSourcePrefixLayer.master_new]
  simp only [LadderWeightedSuccessor.Input.data, LadderWeightedSuccessor.Input.weight,
    LadderWeightedSuccessor.Input.member_controller, LadderWeightedSuccessor.Input.nodeWeight]
  exact min_eq_left (SourcePrefixRows.cut_le
    (fun z hz => CanonicalFieldLayer.grid_bound 2 (Field I.left I.right) hz) _ _)

theorem exists_top_chart {q : (carrier I F hroot hA hB hC).below (A, 2) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) q)
    (htop : ∃ d, (carrier I F hroot hA hB hC).grade d.1 = 2 ∧ q d = ⊤) :
    ∃ a : F.Anchor 2, ∃ σ : ExtOrd → ExtOrd,
      Witness (gTop 2) σ ∧ ∀ d, σ (source I F hroot hA hB hC a d.1) = q d := by
  obtain ⟨a, σ, M, hσ, hM, hread⟩ := LowOnlyPaddedCharts.exists_chart I F hroot hA hB hC hq
  obtain ⟨d, hd, htop⟩ := htop
  have hMt : M = ⊤ := top_le_iff.mp (htop ▸ hM d hd)
  exact ⟨a, σ, hσ, fun d => (hread d).trans (by rw [hMt, min_top_right])⟩

theorem source_private (a : F.Anchor 2) (d : I.right.scheme.below (effC n 2)) :
    source I F hroot hA hB hC a (privateAt I F hroot hA hB hC d).1 = (state F a).v d.1 :=
  (original_readback I F hroot hA hB hC a (I.rightFace.map d.1)).trans
    ((congrFun (state_profile F a).symm _).trans
      (field_private I F hroot
        (LowOnlyRecursiveCoverage.admissible_down F (by decide) (by decide)
          (state_admissible F a)) d.1))

theorem source_donor (a : F.Anchor 2) (d : I.left.scheme.below (effC n 2)) :
    source I F hroot hA hB hC a (donorAt I F hroot hA hB hC d).1 = (state F a).u d.1 :=
  (original_readback I F hroot hA hB hC a (I.leftFace.map d.1)).trans
    ((congrFun (state_profile F a).symm _).trans
      ((field_read I (state F a) (I.leftFace.map d.1)).trans
        (I.paste_left (state F a).u (state F a).v d.1)))

variable (S : State I.left I.right) (hS : F.Admissible 2 S)
  (hcan : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) 2)
  (hlt : LowSeparator.cutoffCut 2 (LowSeparator.donorField F) S.profile < S.b)

def selectedAnchor : F.Anchor 2 := ⟨S.profile, hcan, S, hS, rfl⟩
def partnerAnchor : F.Anchor 2 :=
  ⟨(LowSeparator.partnerState F S).profile, LowSeparator.partnerState_mem F hcan,
    LowSeparator.partnerState F S, LowSeparator.partnerState_admissible F hS hlt (by decide), rfl⟩

theorem selected_separates :
    source I F hroot hA hB hC (selectedAnchor I F S hS hcan)
        (leafAt I F hroot hA hB hC (partnerAnchor I F S hS hcan hlt)).1 <
      source I F hroot hA hB hC (selectedAnchor I F S hS hcan)
        (leafAt I F hroot hA hB hC (selectedAnchor I F S hS hcan)).1 := by
  rw [source_leaf, source_leaf, SourcePrefixRows.cut_refl
    (PairedSlotComparison.sourceGrid_endpoint le_rfl)
    (fun z hz => CanonicalFieldLayer.grid_bound 2 (Field I.left I.right) hz)]
  change SourcePrefixRows.cut (LowSeparator.grid 2) S.profile
    (LowSeparator.partnerState F S).profile < LowSeparator.ceiling 2
  rw [LowSeparator.partnerState_profile, LowSeparator.cut_partner 2
    (LowSeparator.donorField F) LowSeparator.cutoffField hcan hlt]
  exact LowSeparator.cutoffCut_lt_ceiling 2 (LowSeparator.donorField F) hcan

/-- Arbitrary lawful grade-two sections supply their own admitted serving
source and chart. No synchronization or selected-ambient assumption is used. -/
theorem donor_top_of_separator
    {q : (carrier I F hroot hA hB hC).below (A, 2) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) q)
    (hc : q (privateAt I F hroot hA hB hC (F.gap.cC le_rfl)) = ⊤)
    (hr : q (privateAt I F hroot hA hB hC (F.gap.rC le_rfl)) = ⊤)
    (hsep : q (leafAt I F hroot hA hB hC (partnerAnchor I F S hS hcan hlt)) <
      q (leafAt I F hroot hA hB hC (selectedAnchor I F S hS hcan)))
    (d : I.left.scheme.below (effC n 2)) (hd : F.p d.1 = ⊤) :
    q (donorAt I F hroot hA hB hC d) = ⊤ := by
  have hg : (carrier I F hroot hA hB hC).grade
      (privateAt I F hroot hA hB hC (F.gap.cC le_rfl)).1 = 2 :=
    (congrArg Prod.snd ((original_index I F hroot hA hB hC _).trans
      (I.rightFace.index _))).trans F.gap.c_grade
  obtain ⟨a, σ, hσ, hread⟩ := exists_top_chart I F hroot hA hB hC hq ⟨_, hg, hc⟩
  have hc' : σ ((state F a).v F.gap.c) = ⊤ := by
    have he := hread (privateAt I F hroot hA hB hC (F.gap.cC le_rfl))
    rw [source_private] at he
    exact he.trans hc
  have hr' : σ ((state F a).v F.gap.r.1) = ⊤ := by
    have he := hread (privateAt I F hroot hA hB hC (F.gap.rC le_rfl))
    rw [source_private] at he
    exact he.trans hr
  have hs' := hread (leafAt I F hroot hA hB hC (selectedAnchor I F S hS hcan))
  have ht' := hread (leafAt I F hroot hA hB hC (partnerAnchor I F S hS hcan hlt))
  rw [source_leaf] at hs' ht'
  have hsep' : σ (SourcePrefixRows.cut (LowSeparator.grid (X := Field I.left I.right) 2)
      (state F a).profile (LowSeparator.partnerState F S).profile) <
      σ (SourcePrefixRows.cut (LowSeparator.grid (X := Field I.left I.right) 2)
        (state F a).profile S.profile) := by
    simpa only [state_profile, Family.fields, selectedAnchor, partnerAnchor] using
      ht'.trans_lt (hsep.trans_eq hs'.symm)
  have htop := LowSeparator.serving_readback F (state_admissible F a) hcan hlt
    hσ hsep' hc' hr' d.1 hd
  exact (hread (donorAt I F hroot hA hB hC d)).symm.trans
    ((congrArg σ (source_donor I F hroot hA hB hC a d)).trans htop)

end
end VaughtConjecture.Knight.LowOnlyPaddedTwoReadback
