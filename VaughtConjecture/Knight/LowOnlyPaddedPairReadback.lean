/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedSelectedPair

/-! # Arbitrary-section readback for the constructed whole paired display

All native grades at least two use the same actual occurrence interface.
Serving charts and admission follow from lawfulness; the two private top
receipts and strict leaf comparison remain the only readback inputs.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedPairReadback
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedEndpoints
open LowOnlyPaddedRestriction LowOnlyPaddedRenderChart LowOnlyPaddedSelectedChart
open LowOnlyPaddedSelectedPair
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

def originalAt (t : ℕ) (ht : t + 2 ≤ A.card) (d : I.boundary.below (A, t + 2)) :
    (build I F hroot hA hB hC t ht).carrier.below (A, t + 2) :=
  ⟨original I F hroot hA hB hC t ht d.1, by rw [original_index]; exact d.2⟩

def privateIncl {j : ℕ} (d : I.right.scheme.below (effC n j)) : I.boundary.below (A, j) :=
  ⟨I.rightFace.map d.1, I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
    (congrArg Prod.snd (I.rightFace.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩

def donorIncl {j : ℕ} (d : I.left.scheme.below (effC n j)) : I.boundary.below (A, j) :=
  ⟨I.leftFace.map d.1, I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
    (congrArg Prod.snd (I.leftFace.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩

variable {F}

theorem native_top_chart (t : ℕ) (F : LowOnly.Family I.left I.right (t + 2))
    (hroot : ∀ i : Cell I.common.scheme,
      ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
        a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
    (ht : t + 2 ≤ A.card)
    {q : (build I F hroot hA hB hC t ht).carrier.below (A, t + 2) → ExtOrd}
    (hq : RespectsSemanticsBelow (build I F hroot hA hB hC t ht).rows (A, t + 2) q)
    (htop : ∃ d, (build I F hroot hA hB hC t ht).carrier.grade d.1 = t + 2 ∧ q d = ⊤) :
    ∃ a : F.Anchor (t + 2), ∃ σ : ExtOrd → ExtOrd,
      Witness (gTop (t + 2)) σ ∧
      ∀ d, σ (nativeSource I F hroot hA hB hC t ht a d.1) = q d := by
  cases t with
  | zero => exact LowOnlyPaddedTwoReadback.exists_top_chart I F hroot hA hB hC hq htop
  | succ t => exact LowOnlyPaddedStepChart.exists_top_chart _ _ _ hq htop

theorem native_readback (t : ℕ) (F : LowOnly.Family I.left I.right (t + 2))
    (hroot : ∀ i : Cell I.common.scheme,
      ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
        a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
    (ht : t + 2 ≤ A.card) (a : F.Anchor (t + 2))
    (hlt : LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField F) (state F a).profile <
      (state F a).b)
    {q : (build I F hroot hA hB hC t ht).carrier.below (A, t + 2) → ExtOrd}
    (hq : RespectsSemanticsBelow (build I F hroot hA hB hC t ht).rows (A, t + 2) q)
    (hc : q (originalAt I F hroot hA hB hC t ht (privateIncl I (F.gap.cC le_rfl))) = ⊤)
    (hr : q (originalAt I F hroot hA hB hC t ht (privateIncl I (F.gap.rC le_rfl))) = ⊤)
    (hsep : q (leafAt I F hroot hA hB hC t ht (partner t rfl a hlt)) <
      q (leafAt I F hroot hA hB hC t ht a))
    (d : I.left.scheme.below (effC n (t + 2))) (hd : F.p d.1 = ⊤) :
    q (originalAt I F hroot hA hB hC t ht (donorIncl I d)) = ⊤ := by
  have hg : (build I F hroot hA hB hC t ht).carrier.grade
      (originalAt I F hroot hA hB hC t ht (privateIncl I (F.gap.cC le_rfl))).1 = t + 2 :=
    (congrArg Prod.snd ((original_index I F hroot hA hB hC t ht _).trans
      (I.rightFace.index _))).trans F.gap.c_grade
  obtain ⟨b, σ, hσ, hread⟩ := native_top_chart I hA hB hC t F hroot ht hq ⟨_, hg, hc⟩
  have hv (e : I.right.scheme.below (effC n (t + 2))) :
      σ ((state F b).v e.1) = q (originalAt I F hroot hA hB hC t ht (privateIncl I e)) := by
    have he := hread (originalAt I F hroot hA hB hC t ht (privateIncl I e))
    have hs := (native_source_original I F hroot hA hB hC t ht b (I.rightFace.map e.1)).trans
      ((congrFun (state_profile F b).symm _).trans
        (field_private I F hroot
          (LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega)
            (state_admissible F b)) e.1))
    exact (congrArg σ hs).symm.trans he
  have hs := hread (leafAt I F hroot hA hB hC t ht a)
  have hp := hread (leafAt I F hroot hA hB hC t ht (partner t rfl a hlt))
  rw [source_leaf] at hs hp
  have hcmp : σ (SourcePrefixRows.cut (LowSeparator.grid (X := Field I.left I.right) (t + 2))
      (state F b).profile (LowSeparator.partnerState F (state F a)).profile) <
      σ (SourcePrefixRows.cut (LowSeparator.grid (X := Field I.left I.right) (t + 2))
        (state F b).profile (state F a).profile) := by
    simpa only [state_profile, Family.fields, partner] using hp.trans_lt (hsep.trans_eq hs.symm)
  have htop := LowSeparator.serving_readback F (state_admissible F b)
    (by rw [state_profile]; exact a.property.1) hlt hσ hcmp
    ((hv (F.gap.cC le_rfl)).trans hc) ((hv (F.gap.rC le_rfl)).trans hr) d.1 hd
  have he := hread (originalAt I F hroot hA hB hC t ht (donorIncl I d))
  have hs := (native_source_original I F hroot hA hB hC t ht b (I.leftFace.map d.1)).trans
    ((congrFun (state_profile F b).symm _).trans (field_donor I (state F b) d.1))
  exact he.symm.trans ((congrArg σ hs).trans htop)

theorem whole_readback (t : ℕ) (F : LowOnly.Family I.left I.right (t + 2))
    (hroot : ∀ i : Cell I.common.scheme,
      ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
        a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
    (ht : t + 2 ≤ A.card) (r : ℕ) (hheight : t + r + 2 ≤ A.card)
    (a : F.Anchor (t + 2))
    (hlt : LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField F) (state F a).profile <
      (state F a).b)
    {q : Cell (build I F hroot hA hB hC (t + r) hheight).carrier → ExtOrd}
    (hq : RespectsSemantics (build I F hroot hA hB hC (t + r) hheight).rows q)
    (hc : q (original I F hroot hA hB hC (t + r) hheight (I.rightFace.map F.gap.c)) = ⊤)
    (hr : q (original I F hroot hA hB hC (t + r) hheight (I.rightFace.map F.gap.r.1)) = ⊤)
    (hsep : q (belowEquiv I F hroot hA hB hC t ht (A, t + 2) le_rfl r hheight
        (leafAt I F hroot hA hB hC t ht (partner t rfl a hlt))).1 <
      q (belowEquiv I F hroot hA hB hC t ht (A, t + 2) le_rfl r hheight
        (leafAt I F hroot hA hB hC t ht a)).1)
    (d : Cell I.left.scheme) (hd : F.p d = ⊤) :
    q (original I F hroot hA hB hC (t + r) hheight (I.leftFace.map d)) = ⊤ := by
  have hm (e : I.boundary.below (A, t + 2)) :
      q (belowEquiv I F hroot hA hB hC t ht (A, t + 2) le_rfl r hheight
        (originalAt I F hroot hA hB hC t ht e)).1 =
      q (original I F hroot hA hB hC (t + r) hheight e.1) :=
    congrArg q (belowEquiv_original I F hroot hA hB hC t ht (A, t + 2) le_rfl r hheight e)
  let d' : I.left.scheme.below (effC n (t + 2)) :=
    ⟨d, Finset.subset_univ _, le_min (F.top_grade d hd) (gradeC_le d)⟩
  exact (hm (donorIncl I d')).symm.trans
    (native_readback I hA hB hC t F hroot ht a hlt
      (whole_pullback I F hroot hA hB hC t ht (A, t + 2) le_rfl r hheight hq)
      ((hm (privateIncl I (F.gap.cC le_rfl))).trans hc)
      ((hm (privateIncl I (F.gap.rC le_rfl))).trans hr) hsep d' hd)

end
end VaughtConjecture.Knight.LowOnlyPaddedPairReadback
