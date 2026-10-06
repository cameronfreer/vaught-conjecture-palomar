/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryReceivingProbe
public import VaughtConjecture.Knight.WholeDonorAttachedPredecessor
public import VaughtConjecture.Knight.CappedDonorFace

/-! # The legal ordinary receiver from literal common-face reference data

KVC's attachment (`daefcbe`) supplies the input plan, occurrences and union.
V-C's literal `commonFace` receipt supplies the catalogue face identification.
Thus the probe requires no attached-plan or shared-source premise from the
model consumer. Its remaining inputs are the actual two schemes, their literal
root restrictions and the acquired reference data. Model realization is separate.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryAttachedReceiving
open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref
open CellScheme.restrictFace SemSchemeBoundaryInput
noncomputable section

private theorem faceMap_cast {m k : ℕ} (D : SemScheme k) (Q : SemScheme m)
    (f : Fin m ↪ Fin k) (hv : Finset.univ.image f ∈ D.scheme.plan)
    (he : D.restrictFace f hv = Q) (d : Cell Q.scheme) :
    faceMap D Q f hv he d = toCell D.scheme f hv (SemScheme.castCell he.symm d) := by
  subst Q
  rfl

private theorem common_alignment {m N : ℕ} (C : SemScheme N) (P : SemScheme (m + 1))
    (Q : SemScheme m) (e : Fin m ↪ Fin N)
    (hvC : Finset.univ.image e ∈ C.scheme.plan)
    (hvP : Finset.univ.image Fin.castSuccEmb ∈ P.scheme.plan)
    (hC : C.restrictFace e hvC = Q) (hP : P.restrictFace Fin.castSuccEmb hvP = Q)
    {AP : Finset (Fin (m + 1))} {AC : Finset (Fin N)} {k : ℕ}
    (φ : P.scheme.below (AP, k) ≃ C.scheme.below (AC, k))
    (hAP : AP = Finset.univ.image Fin.castSuccEmb) (hAC : AC = Finset.univ.image e)
    (hk : k = m) (hφ : HEq φ (commonFace Fin.castSuccEmb hvP hP e hvC hC m))
    (i : Cell Q.scheme) :
    ∃ d : P.scheme.below (AP, k),
      d.1 = faceMap P Q Fin.castSuccEmb hvP hP i ∧
      (φ d).1 = faceMap C Q e hvC hC i := by
  subst AP AC k
  have he : φ = commonFace Fin.castSuccEmb hvP hP e hvC hC m := eq_of_heq hφ
  subst φ
  let q : Q.scheme.below (Finset.univ, m) := ⟨i, Finset.subset_univ _, gradeC_le i⟩
  let d := bP Fin.castSuccEmb hvP m (castBelow hP.symm (Finset.univ, m) q)
  refine ⟨d, ?_, ?_⟩
  · change toCell P.scheme Fin.castSuccEmb hvP
      (castBelow hP.symm (Finset.univ, m) q).1 = _
    rw [castBelow_val]
    exact (faceMap_cast P Q Fin.castSuccEmb hvP hP i).symm
  · rw [commonFace_apply, Equiv.symm_apply_apply, castBelow_castBelow_symm]
    change toCell C.scheme e hvC (castBelow hC.symm (Finset.univ, m) q).1 = _
    rw [castBelow_val]
    exact (faceMap_cast C Q e hvC hC i).symm

variable {I : Type*} [Fintype I] {nP n : ℕ}
variable (C : SemScheme (n + 4)) (P : SemScheme (nP + 1)) (Q : SemScheme nP)
variable (e : Fin nP ↪ Fin (n + 4))
variable (hvC : Finset.univ.image e ∈ C.scheme.plan)
variable (hvP : Finset.univ.image Fin.castSuccEmb ∈ P.scheme.plan)
variable (hC : C.restrictFace e hvC = Q) (hP : P.restrictFace Fin.castSuccEmb hvP = Q)
variable (R : Ref I nP (n + 4) (n + 4) P C)
variable (hA : R.A = Finset.univ.image Fin.castSuccEmb) (hA' : R.A' = Finset.univ.image e)
variable (hK : R.KA = nP)
variable (hface : HEq R.face (commonFace Fin.castSuccEmb hvP hP e hvC hC nP))

abbrev boundary := WholeDonorAttachment.input e C P Q hvC hvP hC hP

include hA hA' hK hface in
/-- The source-face equation is derived from the literal reference identification. -/
theorem alignment (i : Cell Q.scheme) :
    ∃ d : P.scheme.below (R.A, R.KA),
      d.1 = (boundary C P Q e hvC hvP hC hP).shared.g i ∧
      (R.face d).1 = (boundary C P Q e hvC hvP hC hP).shared.f i :=
  common_alignment C P Q e hvC hvP hC hP R.face hA hA' hK hface i

local notation "W" => boundary C P Q e hvC hvP hC hP
local notation "hf" => alignment C P Q e hvC hvP hC hP R hA hA' hK hface

/-- The complete legal scheme is constructed from the literal reference context. -/
abbrev semScheme : SemScheme (n + 5) :=
  OrdinaryReceivingAssembly.semScheme W R (WholeDonorAttachment.union e) hf

abbrev privateFace := OrdinaryReceivingProbe.privateFace W R (WholeDonorAttachment.union e) hf
abbrev requestFace := OrdinaryReceivingProbe.requestFace W R (WholeDonorAttachment.union e) hf
abbrev gate := OrdinaryReceivingProbe.gate W R (WholeDonorAttachment.union e) hf

theorem private_visible : Finset.univ.image Fin.castSuccEmb ∈
    (semScheme C P Q e hvC hvP hC hP R hA hA' hK hface).scheme.plan :=
  OrdinaryReceivingProbe.private_visible W R (WholeDonorAttachment.union e) hf

theorem request_visible : Finset.univ.image (onePointProj e) ∈
    (semScheme C P Q e hvC hvP hC hP R hA hA' hK hface).scheme.plan :=
  OrdinaryReceivingProbe.request_visible W R (WholeDonorAttachment.union e) hf

theorem private_restrict :
    (semScheme C P Q e hvC hvP hC hP R hA hA' hK hface).restrictFace Fin.castSuccEmb
      (private_visible C P Q e hvC hvP hC hP R hA hA' hK hface) = C :=
  OrdinaryReceivingProbe.private_restrict W R (WholeDonorAttachment.union e) hf

theorem request_restrict :
    (semScheme C P Q e hvC hvP hC hP R hA hA' hK hface).restrictFace (onePointProj e)
      (request_visible C P Q e hvC hvP hC hP R hA hA' hK hface) = P :=
  OrdinaryReceivingProbe.request_restrict W R (WholeDonorAttachment.union e) hf

/-- Literal restriction transports use exactly the installed private occurrences. -/
theorem private_toCell (d : Cell C.scheme) :
    toCell (semScheme C P Q e hvC hvP hC hP R hA hA' hK hface).scheme Fin.castSuccEmb
      (private_visible C P Q e hvC hvP hC hP R hA hA' hK hface)
      (SemScheme.castCell (private_restrict C P Q e hvC hvP hC hP R hA hA' hK hface).symm d) =
        (privateFace C P Q e hvC hvP hC hP R hA hA' hK hface).map d :=
  OrdinaryReceivingProbe.private_toCell W R (WholeDonorAttachment.union e) hf d

/-- The donor map also agrees literally, without an initial-segment assumption. -/
theorem request_toCell (d : Cell P.scheme) :
    toCell (semScheme C P Q e hvC hvP hC hP R hA hA' hK hface).scheme (onePointProj e)
      (request_visible C P Q e hvC hvP hC hP R hA hA' hK hface)
      (SemScheme.castCell (request_restrict C P Q e hvC hvP hC hP R hA hA' hK hface).symm d) =
        (requestFace C P Q e hvC hvP hC hP R hA hA' hK hface).map d :=
  OrdinaryReceivingProbe.request_toCell W R (WholeDonorAttachment.union e) hf d

theorem gate_grade (a : OrdinaryFinalCatalogue.Member R) :
    (semScheme C P Q e hvC hvP hC hP R hA hA' hK hface).scheme.grade
      (gate C P Q e hvC hvP hC hP R hA hA' hK hface a) = n + 4 :=
  OrdinaryReceivingProbe.gate_grade W R (WholeDonorAttachment.union e) hf a

/-- A raw lawful bottom-pattern witness with literal inputs and a named top gate. -/
theorem exists_raw_display :
    ∃ (a : OrdinaryFinalCatalogue.Member R)
      (r : Cell (semScheme C P Q e hvC hvP hC hP R hA hA' hK hface).scheme → ExtOrd),
      RespectsSemantics (semScheme C P Q e hvC hvP hC hP R hA hA' hK hface).rows r ∧
      (∀ d, r ((requestFace C P Q e hvC hvP hC hP R hA hA' hK hface).map d) = R.p d) ∧
      (∀ d, r ((privateFace C P Q e hvC hvP hC hP R hA hA' hK hface).map d) = R.vact d) ∧
      r (gate C P Q e hvC hvP hC hP R hA hA' hK hface a) = ⊤ := by
  obtain ⟨a, r, hr, hp, hc, hg, -⟩ := OrdinaryReceivingProbe.exists_raw_display W R
    (WholeDonorAttachment.union e) hf
  exact ⟨a, r, hr, hp, hc, hg⟩

/-- Selected labels remain literal, and the positive pattern has a named grade-N gate. -/
theorem exists_display (α : LimitStage)
    (hpb : ∀ d, R.p d ≠ ⊤ → R.p d < ofOrd α.1)
    (hcb : ∀ d, R.vact d ≠ ⊤ → R.vact d < ofOrd α.1) :
    ∃ (a : OrdinaryFinalCatalogue.Member R)
      (r : Cell (semScheme C P Q e hvC hvP hC hP R hA hA' hK hface).scheme → ExtOrd),
      RespectsSemantics (semScheme C P Q e hvC hvP hC hP R hA hA' hK hface).rows r ∧
      (∀ d, r d < ofOrd α.1 ∨ r d = ⊤) ∧
      (∀ d, r ((requestFace C P Q e hvC hvP hC hP R hA hA' hK hface).map d) = R.p d) ∧
      (∀ d, r ((privateFace C P Q e hvC hvP hC hP R hA hA' hK hface).map d) = R.vact d) ∧
      r (gate C P Q e hvC hvP hC hP R hA hA' hK hface a) = ⊤ := by
  obtain ⟨a, r, hr, hb, hp, hc, hg, -⟩ := OrdinaryReceivingProbe.exists_display W R
    (WholeDonorAttachment.union e) hf α hpb hcb
  exact ⟨a, r, hr, hb, hp, hc, hg⟩

/-- The model consumer only needs actual private retention and one positive gate. -/
theorem readback_below
    {q : Cell (semScheme C P Q e hvC hvP hC hP R hA hA' hK hface).scheme → ExtOrd}
    (hq : RespectsSemantics (semScheme C P Q e hvC hvP hC hP R hA hA' hK hface).rows q)
    (hretain : ∀ d,
      q ((privateFace C P Q e hvC hvP hC hP R hA hA' hK hface).map d) = R.vact d)
    (a : OrdinaryFinalCatalogue.Member R)
    (hg : q (gate C P Q e hvC hvP hC hP R hA hA' hK hface a) ≠ ⊥)
    {δ : ExtOrd} (hδ : δ ≤ R.cut R.vactL) (d : Cell P.scheme) :
    min (q ((requestFace C P Q e hvC hvP hC hP R hA hA' hK hface).map d)) δ =
      min (R.p d) δ :=
  OrdinaryReceivingProbe.readback_below W R (WholeDonorAttachment.union e) hf
    hq hretain a hg hδ d

end
end VaughtConjecture.Knight.OrdinaryAttachedReceiving
