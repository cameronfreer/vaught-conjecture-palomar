/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HollowGrowthTemplate
public import VaughtConjecture.Knight.GrowthScalarLedger

/-! # Constructed hollow-growth input, admission and stage-bounded decoding

The relative template is acquired from the model. Its root attachment is
literal, its bottom class is actual, and its original actual pair is admitted
at every cutoff. The supported decoder is defined at all ordinal arguments;
this is not yet a lawful physical display or a receiving theorem.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.HollowGrowthTemplate
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor
open CellScheme.restrictFace Transform
noncomputable section
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}
  {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} (q : S α.1 (n + 1)) {Nmin : ℕ}
  (D : HollowGrowthReference.Data (W := W) t p (donorRequests q) (n + 1) Nmin)

/-- Receipts of the constructed scalar input, not a physical-probe interface. -/
structure Input where
  donor_type : typeMap Fin.castSuccEmb q = some p
  hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan
  hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme
  hvC : Finset.univ.image D.face ∈ D.context.type.scheme.scheme.plan
  hC : D.context.type.scheme.restrictFace D.face hvC = p.scheme
  relative : RelativeData D.context.type.scheme.scheme D.context.type.scheme.rows
    q.scheme.scheme q.scheme.rows
  req_eq : relative.req = requests q D
  top_eq : relative.top = (Finset.univ, n + 1)
  attachment : Growth.RootAttachment p.scheme Fin.castSuccEmb hvP hP D.face hvC hC relative
  class_eq : HEq relative.ZA {d : D.context.type.scheme.scheme.below
    (D.context.type.scheme.scheme.cell D.cap) | D.context.type.label d.1 = ⊥}

theorem exists_input (hn : 0 < n) (hq : IsCoface p q) : Nonempty (Input q D) := by
  obtain ⟨hvP, hP, hvC, hC, X, hreq, htop, ⟨R⟩, hclass⟩ := exists_template q D hn hq
  exact ⟨⟨hq, hvP, hP, hvC, hC, X, hreq, htop, R, hclass⟩⟩

/-- A model supplies every scalar input; no reference or template existence
assumption is left. Positive root arity remains explicit. -/
theorem acquire (hM : W.IsModel) (hg : W.HasTopGradeGrowth) (hh : W.IsHollow)
    (hn : 0 < n) (hp : W.eval t = some p) (hq : IsCoface p q) (floor : ℕ) :
    ∃ D : HollowGrowthReference.Data (W := W) t p (donorRequests q) (n + 1) floor,
      Nonempty (Input q D) := by
  obtain ⟨D⟩ := HollowGrowthReference.exists_data hM hg hh t p hp
    (donorRequests q) (donorRequests_ok q) (n + 1) floor
  exact ⟨D, exists_input q D hn hq⟩

def actual : Growth.State D.context.type.scheme.scheme q.scheme.scheme :=
  ⟨D.context.type.label, q.label⟩

namespace Input
variable {q D} (I : Input q D)

private theorem inClass_iff_of_heq {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {DA : CellScheme A} {B C : Finset ι × ℕ} (hBC : B = C)
    {ZA : Set (DA.below B)} {ZC : Set (DA.below C)} (hZ : HEq ZA ZC)
    (u : Cell DA → ExtOrd) : InClass ZA u ↔ InClass ZC u := by
  subst C
  rw [eq_of_heq hZ]

/-- The relation is tested on the entire actual private bottom class below
the cap, not a selected or synchronized subclass. -/
theorem inClass_iff (u : Cell D.context.type.scheme.scheme → ExtOrd) :
    InClass I.relative.ZA u ↔ ∀ d : D.context.type.scheme.scheme.below
      (D.context.type.scheme.scheme.cell D.cap),
      u d.1 = ⊥ ↔ D.context.type.label d.1 = ⊥ :=
  inClass_iff_of_heq (congrArg (fun r => D.context.type.scheme.scheme.cell r.C) I.req_eq)
    I.class_eq u

theorem actual_inClass : InClass I.relative.ZA D.context.type.label :=
  (I.inClass_iff _).mpr (fun _ => Iff.rfl)

theorem donor_arity_lt : n + 1 < I.relative.req.N := by
  rw [I.req_eq]
  exact (requests q D).R_lt_N

theorem threshold_above_floor : Nmin < I.relative.req.N := by
  rw [I.req_eq]
  exact (le_max_right _ _).trans_lt D.large

/-- The complete actual pair, including both future vectors, is admitted at
every nominal cutoff. No upward-admission lemma is used. -/
theorem actual_admitted (j : ℕ) : Growth.Admitted I.relative j (actual q D) where
  private_lawful := D.context.type.respects.toBelow _
  donor_lawful := q.respects.toBelow _
  visible f := by
    cases f with
    | inl d =>
      have hv : SelfVis (D.context.type.scheme.scheme.grade d) (D.context.type.label d) :=
        (D.context.type.respects.orderly d).symm
      exact hv.mono (D.context.type.scheme.scheme.grade_pos d)
    | inr d =>
      have hv : SelfVis (q.scheme.scheme.grade d) (q.label d) := (q.respects.orderly d).symm
      exact hv.mono (q.scheme.scheme.grade_pos d)
  shared a := by
    change q.label a.1 = D.context.type.label (I.relative.κ a).1
    let b : q.scheme.scheme.below (Finset.univ.image Fin.castSuccEmb, n) :=
      ⟨a.1, I.attachment.root_eq ▸ a.2⟩
    have hP' : q.restrictFace Fin.castSuccEmb I.hvP = p :=
      restrictFace_eq_of_typeMap_eq_some I.donor_type
    have hC' : D.context.type.restrictFace D.face I.hvC = p :=
      restrictFace_eq_of_typeMap_eq_some D.face_type
    have hface := (congrArg D.context.type.label
      (commonFace_val Fin.castSuccEmb I.hvP I.hP D.face I.hvC I.hC n b)).trans
      ((StageType.label_castCell hC'.symm _).trans
      ((StageType.label_castCell hP' _).trans
        (congrArg q.label (toCell_belowEquiv_symm_val _ _ _ _ b))))
    exact hface.symm.trans (congrArg D.context.type.label (I.attachment.occurrence a)).symm
  correct _ _ := by
    change I.relative.req.Correct (I.relative.req.sec D.context.type.label) q.label
    exact I.req_eq.symm ▸ actual_correct q D

theorem actual_proper_bound (f : Growth.Field D.context.type.scheme.scheme q.scheme.scheme)
    (hf : (actual q D).profile f ≠ ⊤) : (actual q D).profile f < ofOrd α.1 := by
  cases f with
  | inl d => exact (D.context.type.label_bound d).resolve_right hf
  | inr d => exact (q.label_bound d).resolve_right hf

/-- Correctness, if extracted from the eventual physical rows over this actual
private face, reads the entire donor literally. It is not assumed extracted. -/
theorem exact_of_correct {v : Cell q.scheme.scheme → ExtOrd}
    (h : I.relative.req.Correct (I.relative.req.sec D.context.type.label) v) : v = q.label := by
  rw [I.req_eq] at h
  exact (correct_iff_eq_actual q D v).mp h

/-- Canonical insertion for the actual complete state, with an exact decoder
whose every proper output lies below the original stage. This includes unused
decoder inputs, but does not assert lawfulness on any newly installed rows. -/
theorem exists_bounded_decoder {j : ℕ} (hj : 1 ≤ j) :
    ∃ a : Growth.Catalogue I.relative j, ∃ δ : ExtOrd → ExtOrd,
      Witness (gTop j) δ ∧
      (∀ f, δ (a.1 f) = (actual q D).profile f) ∧
      (∀ x, OrbitPrefixSupport.Supported j ({⊤} : Set ExtOrd) (actual q D).profile (δ x)) ∧
      ∀ x, δ x ≠ ⊤ → δ x < ofOrd α.1 := by
  obtain ⟨S, hS, hcan, δ, hw, hread, _, hsupp⟩ :=
    Growth.exists_supported_decoder I.relative hj (I.actual_admitted j)
  refine ⟨⟨S.profile, hcan, S, hS, rfl⟩, δ, hw, hread, hsupp, ?_⟩
  intro x hx
  exact CappedDonor.Ref.supported_top_lt_limit
    (limitPart_eq_self_of_isNonSuccessor (Or.inr α.2))
    (actual_proper_bound (q := q) (D := D)) (hsupp x) hx

end Input
end
end VaughtConjecture.Knight.HollowGrowthTemplate
