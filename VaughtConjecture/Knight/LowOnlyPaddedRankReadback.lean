/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowSeparatorRank
public import VaughtConjecture.Knight.LowOnlyPaddedContract
public import VaughtConjecture.Knight.LowOnlyDonorOrderedLift

/-! # Actual padded rank-tip readback at grade one

The two anchors are constructed in the existing admitted catalogue. Only their
rank profiles are identified with the selected vector and its rank partner;
their normalized numerical values need not equal those vectors. An arbitrary
lawful section supplies its own serving leaf and monotone rank table.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedRankReadback
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LadderScalarRendering LowOnlyPaddedContract LowSeparator
noncomputable section

section Partner
variable {n : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C 1)

def partnerState (S : State P C) : State P C := ⟨S.u, S.v, F.maximum S⟩

theorem partner_profile (S : State P C) :
    (partnerState F S).profile =
      LowSeparatorRank.rankPartner (donorField F) cutoffField S.profile := by
  classical
  funext d
  rcases d with d | d | d
  · exact (Function.update_of_ne (by simp) _ _).symm
  · exact (Function.update_of_ne (by simp) _ _).symm
  · cases d
    exact (maximum_eq_donorMax F S).trans
      (LowSeparatorRank.rankPartner_apply_self (donorField F) cutoffField S.profile).symm

theorem partner_admissible {S : State P C} (hS : F.Admissible 1 S) :
    F.Admissible 1 (partnerState F S) where
  lawfulP := hS.lawfulP
  lawfulC := hS.lawfulC
  shared := hS.shared
  futureP := hS.futureP
  futureC := hS.futureC
  cutoff := by
    change SelfVis 1 (F.maximum S)
    rw [maximum_eq_donorMax]
    rcases donorMax_cases (donorField F) S.profile with hz | ⟨d, _, hd⟩
    · rw [hz]; exact selfVis_bot 1
    · rw [← hd]; exact LowOnlyRecursiveCharts.profile_visible_one F le_rfl hS d
  low _ hm _ _ := (lt_irrefl (F.maximum S) hm).elim

/-- The existing catalogue contains both rank anchors, literal-top selected
fields included. No raw vector is identified with its canonical normalization. -/
theorem exists_anchors {S : State P C} (hS : F.Admissible 1 S) :
    ∃ a b : F.Anchor 1,
      RelativeLadderLayer.ranks (F.fields 1) a = fieldRank S.profile ∧
      RelativeLadderLayer.ranks (F.fields 1) b =
        fieldRank (LowSeparatorRank.rankPartner (donorField F) cutoffField S.profile) := by
  obtain ⟨a, ha⟩ := F.exists_rank_anchor le_rfl hS
  obtain ⟨b, hb⟩ := F.exists_rank_anchor le_rfl (partner_admissible F hS)
  exact ⟨a, b, funext ha, (funext hb).trans (congrArg fieldRank (partner_profile F S))⟩
end Partner

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right 1)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "D" => RelativeLadderLayer.carrier I.boundary hA
  (X := Field I.left I.right) (Q := F.Anchor 1)
local notation "E" => RelativeLadderLayer.rows I.boundary I.rows hA
  (field I) (F.fields 1) (proper I hB hC)
local notation "H" => RelativeLadderLayer.rungs (X := Field I.left I.right)

def originalAt (d : I.boundary.below (A, 1)) : (D).below (A, 1) :=
  ⟨RelativeLadderLayer.old I.boundary hA d.1, by rw [RelativeLadderLayer.old_index]; exact d.2⟩

include hroot in
/-- Strict comparison of the actual spare tips activates the serving source.
The source, chart and LOW instance are all derived from actual lawfulness. -/
theorem donor_top_of_separator {S : State I.left I.right}
    (hlt : donorMax (donorField F) S.profile < S.b)
    {qs qt : F.Anchor 1}
    (hqs : RelativeLadderLayer.ranks (F.fields 1) qs = fieldRank S.profile)
    (hqt : RelativeLadderLayer.ranks (F.fields 1) qt =
      fieldRank (LowSeparatorRank.rankPartner (donorField F) cutoffField S.profile))
    {q : (D).below (A, 1) → ExtOrd} (hq : RespectsSemanticsBelow E (A, 1) q)
    (hsep : q (RelativeLadderLayer.leafOccurrence I.boundary hA qt) <
      q (RelativeLadderLayer.leafOccurrence I.boundary hA qs))
    (hc : q (originalAt I F hA (privateIncl I (F.gap.cC le_rfl))) = ⊤)
    (hr : q (originalAt I F hA (privateIncl I (F.gap.rC le_rfl))) = ⊤)
    (d : I.left.scheme.below (effC n 1)) (hd : F.p d.1 = ⊤) :
    q (originalAt I F hA (donorIncl I d)) = ⊤ := by
  obtain ⟨a, τ, hτ, _, hread⟩ := RelativeLadderLayer.exists_leaf_chart I.boundary I.rows hA
    (field I) (F.fields 1) (proper I hB hC) qs hq
  let g : ℕ → ExtOrd := τ ∘ SupportLadderRows.source H
  have hg : Monotone g := hτ.mono.comp (SupportLadderRows.source_mono H)
  have he (x : (D).below (A, 1)) :
      q x = g (RelativeLadderLayer.rankIndex I.boundary hA (field I) (F.fields 1) a x.1) := by
    have hx := hread x
    change τ (SupportLadderRows.source
      (SupportLadderRows.ceiling (RelativeLadderLayer.ranks (F.fields 1))
        (SupportLadderRows.leaf (Nat.succ_pos _) a))
      (RelativeLadderLayer.rankIndex I.boundary hA (field I) (F.fields 1) a x.1)) = q x at hx
    rw [SupportLadderRows.ceiling_leaf] at hx
    exact hx.symm
  have htip (b : F.Anchor 1) : q (RelativeLadderLayer.leafOccurrence I.boundary hA b) =
      g (FiniteProfileControllers.cut H (RelativeLadderLayer.ranks (F.fields 1) a)
        (RelativeLadderLayer.ranks (F.fields 1) b)) :=
    (he _).trans (congrArg g
      ((RelativeLadderLayer.rankIndex_added I.boundary hA (field I) (F.fields 1) a
        (SupportLadderRows.leaf (Nat.succ_pos _) b)).trans
        (SupportLadderRows.index_leaf (profile := RelativeLadderLayer.ranks (F.fields 1))
          (Nat.succ_pos _) a b)))
  have hcut : FiniteProfileControllers.cut H (RelativeLadderLayer.ranks (F.fields 1) a)
      (RelativeLadderLayer.ranks (F.fields 1) qt) <
      FiniteProfileControllers.cut H (RelativeLadderLayer.ranks (F.fields 1) a)
        (RelativeLadderLayer.ranks (F.fields 1) qs) := by
    apply lt_of_not_ge
    intro hh
    exact (not_lt.mpr (hg hh)) ((htip qt).symm.trans_lt (hsep.trans_eq (htip qs)))
  rw [hqs, hqt] at hcut
  obtain ⟨hlo, hb⟩ := LowSeparatorRank.activation_of_cut_lt (donorField F) cutoffField hlt
    (Nat.le_succ _) hcut
  have hact := LowSeparatorRank.activation_of_source (donorField F) cutoffField a.val hlo hb
  have hm : F.maximum (state F a) < (state F a).b := by
    rw [maximum_eq_donorMax]
    change donorMax (donorField F) (state F a).profile < (state F a).profile cutoffField
    simpa only [state_profile, Family.fields] using hact
  have hv (e : I.right.scheme.below (effC n 1)) :
      q (originalAt I F hA (privateIncl I e)) =
        g (fieldRank (state F a).profile (Sum.inr (Sum.inl e.1))) := by
    apply (he _).trans
    apply congrArg g
    apply (RelativeLadderLayer.rankIndex_old I.boundary hA (field I) (F.fields 1) a _).trans
    change fieldRank (F.fields 1 a) (field I (I.rightFace.map e.1)) = _
    rw [← state_profile]
    exact congrArg (LadderScalarRendering.rank (values (state F a).profile))
      (field_private I F hroot (state_admissible F a) e.1)
  have hu : q (originalAt I F hA (donorIncl I d)) =
      g (fieldRank (state F a).profile (Sum.inl d.1)) := by
    apply (he _).trans
    apply congrArg g
    apply (RelativeLadderLayer.rankIndex_old I.boundary hA (field I) (F.fields 1) a _).trans
    change fieldRank (F.fields 1 a) (field I (I.leftFace.map d.1)) = _
    rw [← state_profile]
    exact congrArg (LadderScalarRendering.rank (values (state F a).profile))
      (field_donor I (state F a) d.1)
  rw [hv] at hc hr
  rw [hu]
  rcases min_le_iff.mp (LowSeparatorRank.low_min_le F (state_admissible F a) hm d.1 hd) with hh | hh
  · exact top_le_iff.mp (hc ▸ hg (rank_mono (values (state F a).profile) hh))
  · exact top_le_iff.mp (hr ▸ hg (rank_mono (values (state F a).profile) hh))

include hroot in
/-- The selected grade-one display on the actual base: both original sections
are literal, the selected tip is top, and the partner tip is the non-top donor
maximum. This is section supply, not model realization of the comparison. -/
theorem exists_separated_display {S : State I.left I.right} (hS : F.Admissible 1 S)
    (hlt : donorMax (donorField F) S.profile < S.b) :
    ∃ qs qt : F.Anchor 1,
      RelativeLadderLayer.ranks (F.fields 1) qs = fieldRank S.profile ∧
      RelativeLadderLayer.ranks (F.fields 1) qt =
        fieldRank (LowSeparatorRank.rankPartner (donorField F) cutoffField S.profile) ∧
      ∃ q : (D).below (A, 1) → ExtOrd, RespectsSemanticsBelow E (A, 1) q ∧
        (∀ d, q (originalAt I F hA d) = S.profile (field I d.1)) ∧
        q (RelativeLadderLayer.leafOccurrence I.boundary hA qt) =
          donorMax (donorField F) S.profile ∧
        q (RelativeLadderLayer.leafOccurrence I.boundary hA qs) = ⊤ := by
  obtain ⟨qs, qt, hqs, hqt⟩ := exists_anchors F hS
  let q : (D).below (A, 1) → ExtOrd := fun d =>
    RelativeLadderLayer.renderWith I.boundary hA (field I) (F.fields 1) qs S.profile ⊤ d.1
  refine ⟨qs, qt, hqs, hqt, q,
    RelativeLadderLayer.renderWith_respects I.boundary I.rows hA (field I) (F.fields 1)
      (proper I hB hC) qs S.profile (congrFun hqs) (fun _ => le_top)
      (LowOnlyRecursiveCharts.profile_visible_one F le_rfl hS) (extVisibilityReplace_top 1 1)
      (boundary_lawful I F hroot S hS), ?_, ?_, ?_⟩
  · intro d
    exact RelativeLadderLayer.renderWith_old I.boundary hA (field I) (F.fields 1)
      qs S.profile ⊤ (congrFun hqs) d.1
  · change LadderScalarRendering.level (values S.profile) ⊤
      (RelativeLadderLayer.rankIndex I.boundary hA (field I) (F.fields 1) qs
        (RelativeLadderLayer.added I.boundary hA (SupportLadderRows.leaf (Nat.succ_pos _) qt))) = _
    rw [RelativeLadderLayer.rankIndex_added]
    exact LowSeparatorRank.render_tip_partner (donorField F) cutoffField
      (RelativeLadderLayer.ranks (F.fields 1)) (Nat.succ_pos _) hlt
      (Nat.le_succ _) hqs hqt ⊤
  · change LadderScalarRendering.level (values S.profile) ⊤
      (RelativeLadderLayer.rankIndex I.boundary hA (field I) (F.fields 1) qs
        (RelativeLadderLayer.added I.boundary hA (SupportLadderRows.leaf (Nat.succ_pos _) qs))) = _
    rw [RelativeLadderLayer.rankIndex_added]
    exact LowSeparatorRank.render_tip_self (RelativeLadderLayer.ranks (F.fields 1))
      (Nat.succ_pos _) S.profile (Nat.lt_succ_self _) qs ⊤

end
end VaughtConjecture.Knight.LowOnlyPaddedRankReadback
