/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthReplicatedOccurrences

/-! # Physical correctness with a positive, possibly proper private cap

Recognition at the activation grade gives a capped admitted state. It need
not be the uncapped vector. Every original agrees with that state below the
grade maximum, which dominates the actual private cap. Correctness depends
only on these cap readings, so it transfers back to the actual originals.
No top-cap or supplied-admission hypothesis is needed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherMixed
noncomputable section

namespace Requests
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  (r : Requests DA DQ)

/-- Correctness depends only on the donor cap readings, active references and
the marker when a high request is present. Internal source choices need not agree. -/
theorem correct_of_observed_readings
    {s s' : DA.below (DA.cell r.C) → ExtOrd} {v v' : Cell DQ → ExtOrd}
    (hobs : ∀ d, d ∈ r.Z ∨ d ∈ r.F ∨ d ∈ r.T →
      min (v d) (s r.capCell) = min (v' d) (s' r.capCell))
    (href : ∀ d ∈ r.F, r.tOf s d = r.tOf s' d)
    (hmark : r.T.Nonempty → r.dOf s = r.dOf s')
    (h : r.Correct s v) : r.Correct s' v' := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    exact (hobs d (Or.inl hd)).symm.trans (h.1 d hd)
  · intro d hd
    exact (hobs d (Or.inr (Or.inl hd))).symm.trans
      ((h.2.1 d hd).trans (href d hd))
  · intro d hd
    calc
      r.dOf s' = r.dOf s := (hmark ⟨d, hd⟩).symm
      _ ≤ min (v d) (s r.capCell) := h.2.2 d hd
      _ = min (v' d) (s' r.capCell) := hobs d (Or.inr (Or.inr hd))

/-- Correctness reads only the private and donor vectors below its own
visible cap. Agreement is required on the actual cap domain, not future cells. -/
theorem correct_of_cap_agreement
    {s s' : DA.below (DA.cell r.C) → ExtOrd} {v v' : Cell DQ → ExtOrd}
    (hoff : ∀ f ∈ r.F, r.off f ≤ r.N)
    (hvis : SelfVis r.N (s' r.capCell)) (hc : s r.capCell = s' r.capCell)
    (hs : ∀ d, min (s d) (s' r.capCell) = min (s' d) (s' r.capCell))
    (hv : ∀ d, min (v d) (s' r.capCell) = min (v' d) (s' r.capCell))
    (h : r.Correct s v) : r.Correct s' v' := by
  have href (f) (hf : f ∈ r.F) : r.tOf s f = r.tOf s' f := by
    unfold tOf
    rw [hc, ← evr_min_of_selfVis hvis le_rfl (hoff f hf), hs,
      evr_min_of_selfVis hvis le_rfl (hoff f hf)]
  have hmark : r.dOf s = r.dOf s' := by
    unfold dOf
    rw [hc, ← evr_min_of_selfVis hvis le_rfl r.R_lt_N.le, hs,
      evr_min_of_selfVis hvis le_rfl r.R_lt_N.le]
  exact r.correct_of_observed_readings (fun d _ => by rw [hc]; exact hv d)
    href (fun _ => hmark) h

/-- Calibration of an exact request is a reference value strictly below
the private cap. Zero requests instead use positivity of that cap. -/
theorem Correct.read_exact
    {s : DA.below (DA.cell r.C) → ExtOrd} {v : Cell DQ → ExtOrd}
    (h : r.Correct s v) (hpos : s r.capCell ≠ ⊥) {d : Cell DQ} {a : ExtOrd}
    (hcal : (d ∈ r.Z ∧ a = ⊥) ∨
      (d ∈ r.F ∧ r.tOf s d = a ∧ a < s r.capCell)) : v d = a := by
  rcases hcal with ⟨hd, rfl⟩ | ⟨hd, he, hl⟩
  · exact eq_of_min_eq_of_lt' (h.1 d hd) (bot_lt_iff_ne_bot.mpr hpos)
  · exact eq_of_min_eq_of_lt' ((h.2.1 d hd).trans he) hl

/-- A calibrated high marker gives a strict lower bound, independently of
any singleton exact-read receipt. -/
theorem Correct.read_high
    {s : DA.below (DA.cell r.C) → ExtOrd} {v : Cell DQ → ExtOrd}
    (h : r.Correct s v) {d : Cell DQ} (hd : d ∈ r.T) {a : ExtOrd}
    (ha : a < r.dOf s) : a < v d :=
  ha.trans_le ((h.2.2 d hd).trans (min_le_left _ _))

end Requests

namespace GrowthCappedReadback
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (t : ℕ) (ht : t + 2 ≤ A.card)
  (U : Finset ι) (j : ℕ) (hBU : B ⊆ U) (hCU : C ⊆ U)
  (hU : U ∈ R) (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (hj : j ≤ U.card) (hj0 : 1 ≤ j) (hjt : j ≤ t + 2)
  (hsmall : n + 1 < X.req.N) (hN : X.req.N ≤ j)
  {p : CellScheme.below (carrier I X T hA hB hC t ht) (U, j) → ExtOrd}

open GrowthReplicatedReadback
local notation "Rows" => rows I X T hA hB hC t ht
local notation "H" => gradeMax I X T hA hB hC t ht U j p X.req.N

include hU hm hj hjt hsmall hN in
/-- Lower original heights dominate the activation-grade maximum. -/
theorem maximum_le_height (hp : RespectsSemanticsBelow Rows (U, j) p)
    (k : ℕ) (hk : k ≤ X.req.N) :
    H ≤ height I X T hA hB hC t ht U j p k := by
  have he : height I X T hA hB hC t ht U j p X.req.N = H := by
    simp only [height, ite_eq_right (by omega : ¬ X.req.N ≤ 1), ite_eq_left hN]
  rw [← he]
  exact height_antitone I X T hA hB hC t ht U hU hm j hj hp hjt hk

include hU hm hj hj0 hjt hsmall in
theorem cap_le_maximum (hp : RespectsSemanticsBelow Rows (U, j) p) :
    p (privateAt I X T hA hB hC t ht U j hCU X.req.C (cap_grade_le I X j hN)) ≤ H := by
  rw [private_readback I X T hA hB hC t ht U j hCU hU hm hj hj0 hjt hp,
    X.grade_C, height, ite_eq_right (by omega : ¬ X.req.N ≤ 1), ite_eq_left hN]
  exact min_le_right _ _

section State
variable {S : State I.right.scheme I.left.scheme} (hS : Admitted X X.req.N S)
  (hprof : ∀ f, S.profile f = min
    (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p f)
    (gradeMax I X T hA hB hC t ht U j p X.req.N))

include hjt hsmall hS hprof in
theorem private_capped (hp : RespectsSemanticsBelow Rows (U, j) p)
    (d : Cell I.right.scheme) (hd : I.right.scheme.grade d ≤ X.req.N) :
    S.privateValues d =
      min (p (privateAt I X T hA hB hC t ht U j hCU d (hd.trans hN))) H := by
  rw [private_readback I X T hA hB hC t ht U j hCU hU hm hj hj0 hjt hp,
    min_assoc, min_eq_right (maximum_le_height I X T hA hB hC t ht U j hU hm hj hjt
      hsmall hN hp _ hd)]
  exact (GrowthOrderedBase.field_private I X T hS d).symm.trans (hprof _)

include hjt hsmall hprof in
theorem donor_capped (hp : RespectsSemanticsBelow Rows (U, j) p)
    (d : Cell I.left.scheme) :
    S.donorValues d =
      min (p (donorAt I X T hA hB hC t ht U j hBU d
        ((donor_grade_le I X d).trans hN))) H := by
  rw [donor_readback_height I X T hA hB hC t ht U j hBU hU hm hj hj0 hjt hp,
    min_assoc, min_eq_right (maximum_le_height I X T hA hB hC t ht U j hU hm hj hjt
      hsmall hN hp _ (donor_grade_le I X d))]
  exact (GrowthOrderedBase.field_donor I S d).symm.trans (hprof _)

end State

include hU hm hj hj0 hjt hsmall in
/-- The actual private and donor readings satisfy correctness whenever the
private cap is positive and its bottom class is the template class. -/
theorem physical_correct (hp : RespectsSemanticsBelow Rows (U, j) p)
    (hcap : p (privateAt I X T hA hB hC t ht U j hCU X.req.C
      (cap_grade_le I X j hN)) ≠ ⊥)
    (hclass : ∀ d : I.right.scheme.below (I.right.scheme.cell X.req.C),
      p (privateAt I X T hA hB hC t ht U j hCU d.1
        ((grade_le_of_below_cap I X d).trans hN)) = ⊥ ↔ d ∈ X.ZA) :
    X.req.Correct
      (fun d => p (privateAt I X T hA hB hC t ht U j hCU d.1
        ((grade_le_of_below_cap I X d).trans hN)))
      (fun d => p (donorAt I X T hA hB hC t ht U j hBU d
        ((donor_grade_le I X d).trans hN))) := by
  obtain ⟨S, hS, he⟩ := exists_admitted_at I X T hA hB hC t ht U hU hm j hj hj0 hp
    X.req.N (by omega) hN (hN.trans hjt)
  have hbound := cap_le_maximum I X T hA hB hC t ht U j hCU hU hm hj hj0 hjt hsmall hN hp
  have hpos : H ≠ ⊥ := fun hz => hcap (le_bot_iff.mp (hbound.trans_eq hz))
  have hpriv := private_capped I X T hA hB hC t ht U j hCU hU hm hj hj0 hjt
    hsmall hN hS he hp
  have hdon := donor_capped I X T hA hB hC t ht U j hBU hU hm hj hj0 hjt
    hsmall hN he hp
  have hc : S.privateValues X.req.C =
      p (privateAt I X T hA hB hC t ht U j hCU X.req.C (cap_grade_le I X j hN)) := by
    rw [hpriv _ X.grade_C.le, min_eq_left hbound]
  have hin : InClass X.ZA S.privateValues := by
    intro d
    rw [hpriv d.1 (grade_le_of_below_cap I X d)]
    constructor
    · intro h
      exact (hclass d).mp (eq_of_min_eq_of_lt' h (bot_lt_iff_ne_bot.mpr hpos))
    · intro h
      rw [(hclass d).mpr h, min_eq_left bot_le]
  have hvis : SelfVis X.req.N
      (p (privateAt I X T hA hB hC t ht U j hCU X.req.C (cap_grade_le I X j hN))) := by
    rw [← hc]
    have ho := (hS.private_lawful.orderly (Growth.capAt X le_rfl X.req.capCell)).symm
    change SelfVis (I.right.scheme.grade X.req.C) (S.privateValues X.req.C) at ho
    rwa [X.grade_C] at ho
  apply X.req.correct_of_cap_agreement X.off_lt hvis hc _ _ (hS.correct le_rfl hin)
  · intro d
    change min (S.privateValues d.1)
      (p (privateAt I X T hA hB hC t ht U j hCU X.req.C (cap_grade_le I X j hN))) = _
    rw [hpriv d.1 (grade_le_of_below_cap I X d), min_assoc, min_eq_right hbound]
    rfl
  · intro d
    change min (S.donorValues d)
      (p (privateAt I X T hA hB hC t ht U j hCU X.req.C (cap_grade_le I X j hN))) = _
    rw [hdon d, min_assoc, min_eq_right hbound]
    rfl

section Full
variable {v : Cell (carrier I X T hA hB hC t ht) → ExtOrd}

include hsmall in
/-- Correctness on the full physical carrier with any positive retained
private cap. The cap may be proper in an independently lawful stable labelling. -/
theorem full_correct (hfull : A.card ≤ t + 2)
    (hv : RespectsSemantics (rows I X T hA hB hC t ht) v)
    (lab : Cell I.right.scheme → ExtOrd) (hclass : InClass X.ZA lab)
    (hcap : lab X.req.C ≠ ⊥)
    (hpriv : ∀ d, v ((GrowthReplicatedRows.privateFace I X T hA hB hC t ht).map d) = lab d) :
    X.req.Correct (X.req.sec lab)
      (fun d => v ((GrowthReplicatedRows.donorFace I X T hA hB hC t ht).map d)) := by
  have hN := threshold_le_card I X hC
  have hprivate (d : Cell I.right.scheme) (hd : I.right.scheme.grade d ≤ A.card) :
      v (privateAt I X T hA hB hC t ht A A.card hC.subset d hd).1 = lab d := by
    rw [← privateFace_map I X T hA hB hC t ht d hd]
    exact hpriv d
  have h := physical_correct I X T hA hB hC t ht A A.card hB.subset hC.subset
    (A_mem I X T hA hB hC t ht) (Or.inl rfl) le_rfl (by omega) hfull hsmall hN
    (hv.toBelow (A, A.card)) (by rw [hprivate]; exact hcap)
    (fun d => by rw [hprivate]; exact hclass d)
  have hps : (fun d : I.right.scheme.below (I.right.scheme.cell X.req.C) =>
      v (privateAt I X T hA hB hC t ht A A.card hC.subset d.1
        ((grade_le_of_below_cap I X d).trans hN)).1) = X.req.sec lab :=
    funext fun d => hprivate d.1 _
  have hds : (fun d : Cell I.left.scheme =>
      v (donorAt I X T hA hB hC t ht A A.card hB.subset d
        ((donor_grade_le I X d).trans hN)).1) =
      fun d => v ((GrowthReplicatedRows.donorFace I X T hA hB hC t ht).map d) :=
    funext fun d => congrArg v (donorFace_map I X T hA hB hC t ht d _).symm
  rw [hps, hds] at h
  exact h

end Full
end GrowthCappedReadback
end
end VaughtConjecture.Knight
