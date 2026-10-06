/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedFiniteCertificate
public import VaughtConjecture.Knight.LowOnlyPaddedLegal

/-! # Stage-bounded exact-readback data on the legal LOW scheme

The constructed legal carrier, literal ordered faces, bounded whole display,
and arbitrary-section certificate are composed here. A subsequent model
application must still produce the received tuple and its finite-cut receipts.
No realization of a selected display is inferred from bottom patterns alone.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedLegalCertificate
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedIteration LowOnlyPaddedInstallation LowOnlyPaddedEndpoints
noncomputable section
variable {l m n K : ℕ} {B C : Finset (Fin l)} {R : Finset (Finset (Fin l))}
  (I : WholeDonorBoundary.Input Finset.univ B C R m n n)
  (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ (Finset.univ : Finset (Fin l)).card)
  (hB : B ⊂ Finset.univ) (hC : C ⊂ Finset.univ)
  (hcover : ∀ S ∈ R, S ≠ Finset.univ → S ⊆ B ∨ S ⊆ C)

local notation "E" => LowOnlyPaddedLegal.semScheme I F hroot hA hB hC hcover
local notation "donor" => LowOnlyPaddedLegal.donor I F hroot hA hB hC hcover
local notation "priv" => LowOnlyPaddedLegal.privateFace I F hroot hA hB hC hcover

/-- A raw supported display and exact readback certificate, before imposing a stage bound. -/
theorem exists_supported_certificate {S : State I.left I.right}
    (hS : F.Admissible (Finset.univ : Finset (Fin l)).card S)
    (hdonor : S.u = F.p) (hc : S.v F.gap.c = ⊤) (hr : S.v F.gap.r.1 = ⊤)
    (hactive : LowSeparator.cutoffCut K (LowSeparator.donorField F) S.profile < S.b) :
    ∃ w : Cell (E).scheme → ExtOrd,
      RespectsSemantics (E).rows w ∧
      (∀ d, w ((donor).map d) = F.p d) ∧
      (∀ d, w ((priv).map d) = S.v d) ∧
      (∀ d, OrbitPrefixSupport.Supported (Finset.univ : Finset (Fin l)).card
        ({⊤} : Set ExtOrd) S.profile (w d)) ∧
      ∀ q : Cell (E).scheme → ExtOrd,
        RespectsSemantics (E).rows q →
        (∀ d, q ((priv).map d) = S.v d) →
        ∀ δ, LowSeparator.cutoffCut K (LowSeparator.donorField F) S.profile < δ →
          (∀ d, min (q d) δ = min (w d) δ) →
          ∀ d, q ((donor).map d) = F.p d := by
  obtain ⟨w, hw, ho, hsupp, hread⟩ :=
    LowOnlyPaddedFiniteCertificate.certificate I hA hB hC F hroot hS hdonor hc hactive
  have hdmap (d : Cell I.left.scheme) : (donor).map d =
      original I F hroot hA hB hC ((Finset.univ : Finset (Fin l)).card - 2) (by omega)
        (I.leftFace.map d) :=
    face_map I F hroot hA hB hC I.leftFace hB.not_ge _ _ d
  have hcmap (d : Cell I.right.scheme) : (priv).map d =
      original I F hroot hA hB hC ((Finset.univ : Finset (Fin l)).card - 2) (by omega)
        (I.rightFace.map d) :=
    face_map I F hroot hA hB hC I.rightFace hC.not_ge _ _ d
  refine ⟨w, hw, ?_, ?_, hsupp, ?_⟩
  · intro d
    exact (congrArg w (hdmap d)).trans ((ho (I.leftFace.map d)).trans
      ((field_donor I S d).trans (congrFun hdonor d)))
  · intro d
    exact (congrArg w (hcmap d)).trans ((ho (I.rightFace.map d)).trans
      (field_private I F hroot
        (LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega) hS) d))
  · intro q hq hp δ hδ hcap d
    exact (congrArg q (hdmap d)).trans (hread q hq
      (((congrArg q (hcmap F.gap.c)).symm.trans (hp F.gap.c)).trans hc)
      (((congrArg q (hcmap F.gap.r.1)).symm.trans (hp F.gap.r.1)).trans hr) δ hδ hcap d)

/-- Exact finite readback on the same legal scheme as the stage-bounded
display. All data on both ordered faces are literal. -/
theorem exists_bounded_certificate {S : State I.left I.right}
    (hS : F.Admissible (Finset.univ : Finset (Fin l)).card S)
    (hdonor : S.u = F.p) (hc : S.v F.gap.c = ⊤) (hr : S.v F.gap.r.1 = ⊤)
    (hactive : LowSeparator.cutoffCut K (LowSeparator.donorField F) S.profile < S.b)
    {α : Ordinal.{0}} (hα : limitPart α = α)
    (hbound : ∀ f, S.profile f ≠ ⊤ → S.profile f < ofOrd α) :
    ∃ w : Cell (E).scheme → ExtOrd,
      RespectsSemantics (E).rows w ∧
      (∀ d, w ((donor).map d) = F.p d) ∧
      (∀ d, w ((priv).map d) = S.v d) ∧
      (∀ d, w d ≠ ⊤ → w d < ofOrd α) ∧
      ∀ q : Cell (E).scheme → ExtOrd,
        RespectsSemantics (E).rows q →
        (∀ d, q ((priv).map d) = S.v d) →
        ∀ δ, LowSeparator.cutoffCut K (LowSeparator.donorField F) S.profile < δ →
          (∀ d, min (q d) δ = min (w d) δ) →
          ∀ d, q ((donor).map d) = F.p d := by
  obtain ⟨w, hw, hd, hp, hsupp, hread⟩ :=
    exists_supported_certificate I F hroot hA hB hC hcover hS hdonor hc hr hactive
  exact ⟨w, hw, hd, hp, fun d hd =>
    CappedDonor.Ref.supported_top_lt_limit hα hbound (hsupp d) hd, hread⟩

end
end VaughtConjecture.Knight.LowOnlyPaddedLegalCertificate
