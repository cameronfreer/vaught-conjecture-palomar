/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingLadderBaseCut
public import VaughtConjecture.Knight.ReceivingCatalogueConsistency

/-! # Constructed grade-one charts and low cuts on the receiving catalogue

All source, row and rank hypotheses of the long-ladder cut theorem are
discharged here on the unchanged catalogue-derived carrier. Arbitrary lawful
lower ambients are allowed. Replacement-anchor construction, and consequently
the grade-one scope-raising lift, are not conclusions of this module.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingGradeOnePhysicalChart
open Transform Value ExtOrd CappedDonor CappedDonor.Ref ReceivingLadderCarrier
open ReceivingCatalogueSources SharpWitnessComposition
noncomputable section

variable {I : Type*} [Fintype I] {nP K : ℕ} {P : SemScheme (nP + 1)}
  {C : SemScheme 2} {R : Ref I nP 2 2 P C} (L : R.LowRef K)
  (hC : C.scheme.plan = privatePlan) (request : Cell P.scheme)

local notation "D" => carrier L hC
local notation "E" => semantics L hC request
local notation "ℓ" => rungs (P := P) (C := C)

def privateAt (d : C.scheme.below (effC 2 1)) : (D).below (Finset.univ, 1) :=
  ⟨old C.scheme hC d.1, by
    rw [old_index]
    exact ⟨Finset.subset_univ _, d.2.2⟩⟩

def lowerSource (a : Controller L) (d : Cell D) : ExtOrd :=
  SupportLadderRows.source ℓ
    (lowerIndex C.scheme hC privateField (.field (.req request)) (ranks L) a d)

theorem lowerSource_private (a : Controller L) (d : C.scheme.below (effC 2 1)) :
    lowerSource L hC request a (privateAt L hC d).1 =
      SupportLadderRows.source ℓ (ranks L a (privateField d.1)) := by
  simp only [lowerSource, privateAt, lowerIndex, view_old]

/-- These are actual lawful leaf rows, not supplied whole completions. -/
theorem source_lawful (a : Controller L) :
    RespectsSemanticsBelow E (Finset.univ, 1) (fun d => lowerSource L hC request a d.1) := by
  have hpos : 0 < ℓ := Nat.succ_pos _
  let v := SupportLadderRows.leaf (X := TField P C) hpos a
  have hc := ReceivingCatalogueConsistency.consistent L hC request
    (added C.scheme hC (.ladder true v))
  have hi : (D).cell (added C.scheme hC (.ladder true v)) = (Finset.univ, 1) :=
    added_index C.scheme hC _
  have hh := hc.mono (show GradedLe (Finset.univ, 1)
      ((D).cell (added C.scheme hC (.ladder true v))) from hi ▸ GradedLe.refl _)
  convert hh using 1
  funext d
  rw [ReceivingCatalogueConsistency.row_ladder]
  change lowerSource L hC request a d.1 =
    ladderRow C.scheme hC privateField (.field (.req request)) (ranks L) v d.1
  simp only [lowerSource, ladderRow, v, SupportLadderRows.ceiling_leaf]
  rfl

/-- From an actual active private occurrence, construct a faithful exact
lower chart and its first reaching rank. Every physical source reading below
that cut is short; every ambient reading below the cap lies below the cut.
The cut is strictly before the spare long tip, even for literal-top ambients. -/
theorem exists_active_private_cut
    {q : (D).below (Finset.univ, 1) → ExtOrd}
    (hq : RespectsSemanticsBelow E (Finset.univ, 1) q)
    (c : C.scheme.below (effC 2 1)) {γ : ExtOrd}
    (hpos : ⊥ < γ) (hactive : γ ≤ q (privateAt L hC c)) :
    ∃ a : Controller L, ∃ σ k, Witness (gTop 1) σ ∧
      (∀ d, σ (lowerSource L hC request a d.1) = q d) ∧
      0 < k ∧ k ≤ ranks L a (privateField c.1) ∧ k < ℓ ∧
      γ ≤ σ (SupportLadderRows.source ℓ k) ∧
      (∀ i, i < k → σ (SupportLadderRows.source ℓ i) < γ) ∧
      (∀ d : Cell D, lowerSource L hC request a d < SupportLadderRows.source ℓ k →
        Short 1 (lowerSource L hC request a d)) ∧
      ∀ d, q d < γ → lowerSource L hC request a d.1 < SupportLadderRows.source ℓ k := by
  obtain ⟨a, σ, hσ, _, hread⟩ := ReceivingLadderBaseCut.exists_chart
    C.scheme hC privateField (.field (.req request)) (ranks L) (Nat.succ_pos _)
    (fun a f => (rank_bound L a f).le) true E
    (ReceivingLadderSemantics.hasLadderRows _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) hq
  have hact : γ ≤ σ (SupportLadderRows.source ℓ (ranks L a (privateField c.1))) := by
    have he : σ (lowerSource L hC request a (privateAt L hC c).1) = q (privateAt L hC c) :=
      hread (privateAt L hC c)
    rw [lowerSource_private] at he
    exact hactive.trans_eq he.symm
  obtain ⟨k, hkpos, hkc, hk, hminimal, hshort, hlow⟩ :=
    ReceivingLadderBaseCut.exists_first_cut hσ hpos (rank_bound L a (privateField c.1)) hact
  refine ⟨a, σ, k, hσ, hread, hkpos, hkc,
    hkc.trans_lt (rank_bound L a (privateField c.1)), hk, hminimal, ?_, ?_⟩
  · intro d hd
    exact hshort _ hd
  · intro d hd
    apply hlow
    exact (hread d).trans_lt hd

/-- The inactive grade-one branch requires no predecessor theorem or new
source: capping the actual ambient restores the entire private prescription.
This includes bottom cap with a bottom prescription. -/
theorem exists_inactive_lift
    {p : C.scheme.below (effC 2 1) → ExtOrd}
    {q : (D).below (Finset.univ, 1) → ExtOrd}
    (hq : RespectsSemanticsBelow E (Finset.univ, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (privateAt L hC d)) γ = min (p d) γ)
    (hbound : ∀ d, p d ≤ γ) :
    ∃ w : (D).below (Finset.univ, 1) → ExtOrd,
      RespectsSemanticsBelow E (Finset.univ, 1) w ∧
      (∀ d, w (privateAt L hC d) = p d) ∧
      ∀ d, min (w d) γ = min (q d) γ := by
  refine ⟨fun d => min (q d) γ, hq.cap hγ, ?_, ?_⟩
  · intro d
    exact (hag d).trans (min_eq_left (hbound d))
  · intro d
    exact min_assoc _ _ _ |>.trans (congrArg (min (q d)) (min_self γ))

/-- Top-cap agreement is literal and is discharged on the same carrier.
No properness restriction is imposed on any prescribed lower value. -/
theorem exists_top_cap_lift
    {p : C.scheme.below (effC 2 1) → ExtOrd}
    {q : (D).below (Finset.univ, 1) → ExtOrd}
    (hq : RespectsSemanticsBelow E (Finset.univ, 1) q)
    (hag : ∀ d, min (q (privateAt L hC d)) ⊤ = min (p d) ⊤) :
    ∃ w : (D).below (Finset.univ, 1) → ExtOrd,
      RespectsSemanticsBelow E (Finset.univ, 1) w ∧
      (∀ d, w (privateAt L hC d) = p d) ∧
      ∀ d, min (w d) ⊤ = min (q d) ⊤ :=
  exists_inactive_lift L hC request hq (by simp only [SelfVis, extVisibilityReplace_top])
    hag (fun _ => le_top)

end
end VaughtConjecture.Knight.ReceivingGradeOnePhysicalChart
