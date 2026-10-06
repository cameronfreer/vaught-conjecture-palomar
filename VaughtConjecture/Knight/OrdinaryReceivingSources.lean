/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryFinalCatalogue
public import VaughtConjecture.Knight.WholeDonorOrdinarySections

/-! # Ordinary catalogue sources on the literal two-face boundary

All fields are present at the final cutoff. Admission therefore supplies two
lawful whole input sections, agreeing on the literal common face. Pasting them
uses the actual ordered boundary; no auxiliary agreement or lawful extension
is assumed. The face identification below is purely an occurrence equation.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryReceivingSources
open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref
open OrdinaryFinalCatalogue SourcePrefixRows OrbitPrefixSupport
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)

theorem private_lawful (a : OrdinaryFinalCatalogue.Member R) :
    RespectsSemantics C.rows (fun d => a.val (.priv d)) := by
  obtain ⟨st, hs, -, -, he⟩ := a.property.2
  have h := hs.v_respects.toRespects (fun d => (present_priv_iff N d).mpr (gradeC_le d))
  convert h using 1
  funext d
  rw [← he, profile_present]
  rfl

theorem request_lawful (a : OrdinaryFinalCatalogue.Member R) :
    RespectsSemantics P.rows (fun d => a.val (.req d)) := by
  obtain ⟨st, hs, -, -, he⟩ := a.property.2
  have h := hs.u_respects.toRespects (fun d => (present_req_iff N d).mpr (req_grade_le R d))
  convert h using 1
  funext d
  rw [← he, profile_present]
  rfl

theorem face_agreement (a : OrdinaryFinalCatalogue.Member R) (d : P.scheme.below (R.A, R.KA)) :
    a.val (.priv (R.face d).1) = a.val (.req d.1) := by
  obtain ⟨st, hs, -, -, he⟩ := a.property.2
  rw [← he, profile_present, profile_present]
  exact (hs.face d (req_grade_le R d.1)).symm

variable {ι : Type*} [DecidableEq ι] {A B T : Finset ι} {plan : Finset (Finset ι)}
variable (W : WholeDonorBoundary.Input A B T plan nP N (nP + 1))
variable (R : Ref I nP N N W.right W.left)
variable (hface : ∀ i : Cell W.common.scheme,
  ∃ d : W.right.scheme.below (R.A, R.KA),
    d.1 = W.shared.g i ∧ (R.face d).1 = W.shared.f i)

include hface in
theorem shared (a : OrdinaryFinalCatalogue.Member R) (i : Cell W.common.scheme) :
    a.val (.priv (W.shared.f i)) = a.val (.req (W.shared.g i)) := by
  obtain ⟨d, hd, he⟩ := hface i
  rw [← hd, ← he]
  exact face_agreement R a d

def boundary (a : OrdinaryFinalCatalogue.Member R) : Cell W.boundary → ExtOrd :=
  W.paste (fun d => a.val (.priv d)) (fun d => a.val (.req d))

theorem boundary_private (a : OrdinaryFinalCatalogue.Member R) (d : Cell W.left.scheme) :
    boundary W R a (W.leftFace.map d) = a.val (.priv d) :=
  W.paste_left _ _ d

include hface in
theorem boundary_request (a : OrdinaryFinalCatalogue.Member R) (d : Cell W.right.scheme) :
    boundary W R a (W.rightFace.map d) = a.val (.req d) :=
  W.paste_right _ _ (shared W R hface a) d

include hface in
theorem boundary_lawful (a : OrdinaryFinalCatalogue.Member R) :
    RespectsSemantics W.rows (boundary W R a) :=
  W.paste_respects (private_lawful R a) (request_lawful R a) (shared W R hface a)

include hface in
theorem boundary_bound (a : OrdinaryFinalCatalogue.Member R) (d : Cell W.boundary) :
    boundary W R a d ≤ CanonicalFieldLayer.ceiling N (Field W.right W.left) :=
  WholeDonorOrdinarySections.paste_bound W (fun _ => member_bound R a _)
    (fun _ => member_bound R a _) (shared W R hface a) d

include hface in
theorem boundary_agreement {a b : OrdinaryFinalCatalogue.Member R} {h : ExtOrd}
    (hab : Agree a.val b.val h) :
    Agree (boundary W R a) (boundary W R b) h :=
  WholeDonorOrdinarySections.paste_agreement W (shared W R hface a) (shared W R hface b)
    (fun _ => hab _) (fun _ => hab _)

include hface in
theorem boundary_field (a : OrdinaryFinalCatalogue.Member R) (d : Cell W.boundary) :
    ∃ f : Field W.right W.left, boundary W R a d = a.val f := by
  rcases WholeDonorOrdinarySections.covered W d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact ⟨.priv c, boundary_private W R a c⟩
  · exact ⟨.req c, boundary_request W R hface a c⟩

include hface in
theorem boundary_support (a : OrdinaryFinalCatalogue.Member R) (G : Set ExtOrd)
    (d : Cell W.boundary) :
    Supported N G a.val (boundary W R a d) := by
  obtain ⟨f, hf⟩ := boundary_field W R hface a d
  rw [hf]
  exact supported_field N G a.val f

end
end VaughtConjecture.Knight.OrdinaryReceivingSources
