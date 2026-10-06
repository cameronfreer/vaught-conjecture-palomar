/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthCompleteFields
public import VaughtConjecture.Knight.CappedDonorFace
public import VaughtConjecture.Knight.CappedDonorReceiving
public import VaughtConjecture.Knight.PartialSections

/-! # Filtered literal common roots for growth repairs

Restriction identities supply the actual cutoff bijections and lawfulness
transport. Compatibility with a supplied relative datum is an explicit literal
occurrence identity, not an assumption of filtered lawfulness.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.Growth
open Transform Value ExtOrd AmalgamationPlan CappedDonor
noncomputable section

section Nominal
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

def cutoffEquiv (B : Finset ι) (j : ℕ) :
    D.below (B, min j B.card) ≃ D.below (B, j) where
  toFun d := ⟨d.1, d.2.1, (le_min_iff.mp d.2.2).1⟩
  invFun d := ⟨d.1, d.2.1, le_min d.2.2
    ((D.grade_le_card_scope d.1).trans (Finset.card_le_card d.2.1))⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cutoff_respects {sem : Semantics D} (B : Finset ι) (j : ℕ)
    (p : D.below (B, min j B.card) → ExtOrd) :
    RespectsSemanticsBelow sem (B, min j B.card) p ↔
      RespectsSemanticsBelow sem (B, j) (p ∘ (cutoffEquiv B j).symm) :=
  respects_iff_of_equiv (cutoffEquiv B j) (fun _ => rfl) (fun _ _ => Iff.rfl)
    (fun _ _ _ => rfl) p

/-- Original-scheme lifting at a nominal cutoff, including an empty filtered
root. The output remains on the actual full original lower domain. -/
theorem extend_cutoff {sem : Semantics D} (hb : sem.IsBountiful)
    {B : Finset ι} (hB : B ∈ D.plan) {j : ℕ}
    {p : D.below (B, j) → ExtOrd} {q : D.below (A, j) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (B, j) p)
    (hq : RespectsSemanticsBelow sem (A, j) q)
    {γ : ExtOrd} (hγ : SelfVis j γ)
    (hag : ∀ d, min (q (CellScheme.below.mono
      (show GradedLe (B, j) (A, j) from ⟨D.isPlan.subset_of_mem hB, le_rfl⟩) d)) γ =
        min (p d) γ) :
    ∃ q', RespectsSemanticsBelow sem (A, j) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      ∀ d, q' (CellScheme.below.mono
        (show GradedLe (B, j) (A, j) from ⟨D.isPlan.subset_of_mem hB, le_rfl⟩) d) = p d := by
  by_cases hz : 0 < min j B.card
  · have hsub := D.isPlan.subset_of_mem hB
    have hp' : RespectsSemanticsBelow sem (B, min j B.card)
        (p ∘ cutoffEquiv B j) := (cutoff_respects B j _).mpr hp
    have hq' : RespectsSemanticsBelow sem (A, min j A.card)
        (q ∘ cutoffEquiv A j) := (cutoff_respects A j _).mpr hq
    obtain ⟨r, hr, hcap, hread⟩ := hb.extend
      (Plan.mem_gradedPlan.mpr ⟨hB, hz, min_le_right _ _⟩)
      (Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem,
        hz.trans_le (min_le_min_left j (Finset.card_le_card hsub)), min_le_right _ _⟩)
      ⟨hsub, min_le_min_left j (Finset.card_le_card hsub)⟩ hp' hq'
      (hγ.mono (min_le_left _ _)) (fun d => hag (cutoffEquiv B j d))
    exact ⟨r ∘ (cutoffEquiv A j).symm, (cutoff_respects A j r).mp hr,
      fun d => hcap ((cutoffEquiv A j).symm d),
      fun d => hread ((cutoffEquiv B j).symm d)⟩
  · refine ⟨q, hq, fun _ => rfl, fun d => ?_⟩
    exact (hz ((D.grade_pos d.1).trans_le ((cutoffEquiv B j).symm d).2.2)).elim
end Nominal

variable {n J r : ℕ} {P : SemScheme (n + 1)} {C : SemScheme J}
  (F : SemScheme r) (fP : Fin r ↪ Fin (n + 1))
  (hvP : Finset.univ.image fP ∈ P.scheme.plan) (hP : P.restrictFace fP hvP = F)
  (fC : Fin r ↪ Fin J) (hvC : Finset.univ.image fC ∈ C.scheme.plan)
  (hC : C.restrictFace fC hvC = F)

abbrev rootMap (j : ℕ) := commonFace fP hvP hP fC hvC hC j

theorem rootMap_grade (j : ℕ) (a : P.scheme.below (Finset.univ.image fP, j)) :
    C.scheme.grade (rootMap F fP hvP hP fC hvC hC j a).1 = P.scheme.grade a.1 :=
  commonFace_grade fP hvP hP fC hvC hC j a

theorem rootMap_lawful (j : ℕ) (p : C.scheme.below (Finset.univ.image fC, j) → ExtOrd) :
    RespectsSemanticsBelow C.rows (Finset.univ.image fC, j) p ↔
      RespectsSemanticsBelow P.rows (Finset.univ.image fP, j)
        (fun a => p (rootMap F fP hvP hP fC hvC hC j a)) :=
  commonFace_respects fP hvP hP fC hvC hC j p

/-- The actual relative-data occurrence map, constructed from literal face
restrictions and containment of the private root in the cap's lower domain. -/
def literalKappa (c : Cell C.scheme)
    (hc : GradedLe (Finset.univ.image fC, r) (C.scheme.cell c)) :
    P.scheme.below (Finset.univ.image fP, r) → C.scheme.below (C.scheme.cell c) :=
  fun a => CellScheme.below.mono hc (rootMap F fP hvP hP fC hvC hC r a)

theorem literalKappa_grade (c : Cell C.scheme)
    (hc : GradedLe (Finset.univ.image fC, r) (C.scheme.cell c))
    (a : P.scheme.below (Finset.univ.image fP, r)) :
    C.scheme.grade (literalKappa F fP hvP hP fC hvC hC c hc a).1 = P.scheme.grade a.1 :=
  rootMap_grade F fP hvP hP fC hvC hC r a

theorem literalKappa_lawful (c : Cell C.scheme)
    (hc : GradedLe (Finset.univ.image fC, r) (C.scheme.cell c))
    {s : C.scheme.below (C.scheme.cell c) → ExtOrd}
    (hs : RespectsSemanticsBelow C.rows (C.scheme.cell c) s) :
    RespectsSemanticsBelow P.rows (Finset.univ.image fP, r)
      (fun a => s (literalKappa F fP hvP hP fC hvC hC c hc a)) :=
  (rootMap_lawful F fP hvP hP fC hvC hC r _).mp (hs.mono hc)

/-- Only actual literal geometry is supplied. Grade preservation and all
filtered transports below are derived, not fields of this record. -/
structure RootAttachment (X : RelativeData C.scheme C.rows P.scheme P.rows) where
  root_eq : X.root = (Finset.univ.image fP, r)
  occurrence : ∀ a : P.scheme.below X.root,
    (X.κ a).1 = (rootMap F fP hvP hP fC hvC hC r
      ⟨a.1, root_eq ▸ a.2⟩).1

namespace RootAttachment
variable {F fP hvP hP fC hvC hC}
  {X : RelativeData C.scheme C.rows P.scheme P.rows}
  (R : RootAttachment F fP hvP hP fC hvC hC X)

include R in
theorem grade (a : P.scheme.below X.root) : C.scheme.grade (X.κ a).1 = P.scheme.grade a.1 := by
  rw [R.occurrence a]
  exact rootMap_grade _ _ _ _ _ _ _ _ _

def full {j : ℕ} (a : P.scheme.below (Finset.univ.image fP, j)) :
    P.scheme.below X.root :=
  ⟨a.1, R.root_eq.symm ▸ show GradedLe (P.scheme.cell a.1)
      (Finset.univ.image fP, r) from ⟨a.2.1, by
    change P.scheme.grade a.1 ≤ r
    have h := (P.scheme.grade_le_card_scope a.1).trans (Finset.card_le_card a.2.1)
    simpa only [Finset.card_image_of_injective _ fP.injective, Finset.card_univ,
      Fintype.card_fin] using h⟩⟩

theorem at_occurrence {j : ℕ} (a : P.scheme.below (Finset.univ.image fP, j)) :
    (rootMap F fP hvP hP fC hvC hC j a).1 = (X.κ (R.full a)).1 := by
  rw [R.occurrence]
  exact commonFace_val_congr _ _ _ _ _ _ _ _ _ rfl

def filtered {j : ℕ} (a : P.scheme.below X.root) (hj : P.scheme.grade a.1 ≤ j) :
    P.scheme.below (Finset.univ.image fP, j) :=
  ⟨a.1, (show GradedLe (P.scheme.cell a.1) (Finset.univ.image fP, r) from
    R.root_eq ▸ a.2).1, hj⟩

theorem at_full {j : ℕ} (a : P.scheme.below X.root) (hj : P.scheme.grade a.1 ≤ j) :
    R.full (R.filtered a hj) = a := rfl

end RootAttachment
end
end VaughtConjecture.Knight.Growth
