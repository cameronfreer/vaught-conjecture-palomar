/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FinalGateLayer
public import VaughtConjecture.Knight.CoatomBoundaryExtension
public import VaughtConjecture.Knight.ExactSemanticFace
public import VaughtConjecture.Knight.SingleFaceTailRestoration

/-! # Exact predecessor lifting transport past the final gate layer

Any graded target excluding the new full grade-N index has exactly its old
occurrences and rows. The actual lower-domain equivalence transports arbitrary
local sections and original-cap lifting, not just selected source vectors.
This includes every proper-scope target and every target of grade below N.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.FinalGateLayer.Input
open Transform Value ExtOrd CoatomBoundaryExtension
noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]
variable {A : Finset ι} {D : CellScheme A} {N : ℕ} (F : Input D N X Q)

/-- All occurrences below a target that excludes the added index are old. -/
def inheritedBelow (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, N) J) :
    D.below J ≃ F.carrier.below J :=
  Equiv.ofBijective (fun d => ⟨F.old d.1, by rw [F.old_index]; exact d.2⟩) ⟨by
    intro d e he
    exact Subtype.ext (F.old_strictMono.injective (congrArg Subtype.val he)), by
    intro d
    have hn : F.carrier.cell d.1 ≠ (A, N) := fun he => hJ (he ▸ d.2)
    obtain ⟨e, he⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N
      F.positive F.height d.1 hn
    have hd : GradedLe (D.cell e) J := by simpa only [he, F.old_index] using d.2
    exact ⟨⟨e, hd⟩, Subtype.ext he.symm⟩⟩

theorem inheritedBelow_respects_iff (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, N) J)
    (p : F.carrier.below J → ExtOrd) :
    RespectsSemanticsBelow F.rows J p ↔
      RespectsSemanticsBelow F.sem J (p ∘ F.inheritedBelow J hJ) := by
  have h := respects_iff_of_equiv (sem' := F.sem) (sem := F.rows)
    (F.inheritedBelow J hJ)
    (fun d => (congrArg Prod.snd (F.old_index d.1)).symm)
    (fun d e => ?_) (fun c d hd => ?_) (p ∘ F.inheritedBelow J hJ)
  · have he : (p ∘ F.inheritedBelow J hJ) ∘ (F.inheritedBelow J hJ).symm = p := by
      funext d
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rw [he] at h
    exact h.symm
  · change D.scope d.1 ⊆ D.scope e.1 ↔
      (F.carrier.cell (F.old d.1)).1 ⊆ (F.carrier.cell (F.old e.1)).1
    rw [F.old_index, F.old_index]
    rfl
  · exact (F.inherited_row c.1 d).symm

/-- Old lifting clauses transport on their actual target-local domains.
No bountifulness of the extended output is assumed. -/
theorem inherited_lift {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hJ : ¬ GradedLe (A, N) J) (hlift : CappedLift F.sem h) : CappedLift F.rows h := by
  let hI : ¬ GradedLe (A, N) I := fun he => hJ (he.trans h)
  let eI := F.inheritedBelow I hI
  let eJ := F.inheritedBelow J hJ
  have hm (d : D.below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  intro p q γ hp hq hγ hag
  obtain ⟨r, hr, hcaps, hread⟩ := hlift (p ∘ eI) (q ∘ eJ) γ
    ((F.inheritedBelow_respects_iff I hI p).mp hp)
    ((F.inheritedBelow_respects_iff J hJ q).mp hq) hγ (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm, ?_, ?_, ?_⟩
  · apply (F.inheritedBelow_respects_iff J hJ _).mpr
    have he : (r ∘ eJ.symm) ∘ eJ = r := by
      funext d
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact he.symm ▸ hr
  · intro d
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcaps (eJ.symm d)
  · intro d
    have he : eJ.symm (CellScheme.below.mono h d) =
        CellScheme.below.mono h (eI.symm d) := by
      apply eJ.injective
      rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply]
    rw [Function.comp_apply, he, hread]
    exact congrArg p (eI.apply_symm_apply d)

/-- The predecessor's lower-grade lift is the restoration clause on the
installed carrier, even when old proper grade-N owners remain present. -/
theorem lower_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 < N)
    (hlift : CappedLift F.sem h) : CappedLift F.rows h :=
  F.inherited_lift h (fun he => not_le_of_gt hJ he.2) hlift

/-- Literal restoration above an owner cap on the installed rows. Only the
predecessor's lower-grade lifting clause is consumed. -/
theorem restore {S : Finset ι} (hS : S ⊆ A)
    (hlift : CappedLift F.sem
      (show GradedLe (S, N - 1) (A, N - 1) from ⟨hS, le_rfl⟩))
    {p : F.carrier.below (S, N) → ExtOrd}
    (hp : RespectsSemanticsBelow F.rows (S, N) p)
    {u : F.carrier.below (A, N) → ExtOrd}
    (hu : RespectsSemanticsBelow F.rows (A, N) u)
    {M : ExtOrd} (hM : SelfVis N M)
    (hread : ∀ e, u (CellScheme.below.mono
      (show GradedLe (S, N) (A, N) from ⟨hS, le_rfl⟩) e) = min (p e) M)
    (hhigh : ∀ e : F.carrier.below (S, N), F.carrier.grade e.1 = N → p e ≤ M) :
    ∃ r : F.carrier.below (A, N) → ExtOrd,
      RespectsSemanticsBelow F.rows (A, N) r ∧
      (∀ e, r (CellScheme.below.mono
        (show GradedLe (S, N) (A, N) from ⟨hS, le_rfl⟩) e) = p e) ∧
      (∀ d, min (r d) M = min (u d) M) ∧
      ∀ d, N - 1 < F.carrier.grade d.1 → r d ≤ M := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt F.positive)
  exact SingleFaceTailRestoration.exists_restore F.rows hS
    (F.lower_lift (show GradedLe (S, j) (A, j) from ⟨hS, le_rfl⟩)
      (Nat.lt_succ_self j) hlift) hp hu hM hread hhigh

/-- The complementary inactive branch needs no catalogue repair. -/
theorem lift_inactive {S : Finset ι} (hS : S ⊆ A)
    (hlift : CappedLift F.sem
      (show GradedLe (S, N - 1) (A, N - 1) from ⟨hS, le_rfl⟩))
    {p : F.carrier.below (S, N) → ExtOrd}
    (hp : RespectsSemanticsBelow F.rows (S, N) p)
    {q : F.carrier.below (A, N) → ExtOrd}
    (hq : RespectsSemanticsBelow F.rows (A, N) q)
    {γ : ExtOrd} (hγ : SelfVis N γ)
    (hag : ∀ e, min (q (CellScheme.below.mono
      (show GradedLe (S, N) (A, N) from ⟨hS, le_rfl⟩) e)) γ = min (p e) γ)
    (hhigh : ∀ e : F.carrier.below (S, N), F.carrier.grade e.1 = N → p e ≤ γ) :
    ∃ r : F.carrier.below (A, N) → ExtOrd,
      RespectsSemanticsBelow F.rows (A, N) r ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ e, r (CellScheme.below.mono
        (show GradedLe (S, N) (A, N) from ⟨hS, le_rfl⟩) e) = p e := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt F.positive)
  exact SingleFaceTailRestoration.exists_inactive F.rows hS
    (F.lower_lift (show GradedLe (S, j) (A, j) from ⟨hS, le_rfl⟩)
      (Nat.lt_succ_self j) hlift) hp hq hγ hag hhigh

/-- A proper original semantic face stays occurrence-exact after the final
installation, with its full lower domains and long rows unchanged. -/
def inheritedFace {S : Finset ι} {D₀ : CellScheme S} {sem₀ : Semantics D₀}
    (hS : S ⊆ A) (hne : S ≠ A) (E : ExactSemanticFace sem₀ F.sem) :
    ExactSemanticFace sem₀ F.rows where
  map := ⟨F.old ∘ E.map, F.old_strictMono.injective.comp E.map.injective⟩
  index d := (F.old_index (E.map d)).trans (E.index d)
  exhaustive z hz := by
    obtain ⟨d, hd⟩ := F.proper_occurrence hS hne
      (⟨z, hz, le_rfl⟩ : F.carrier.below (S, F.carrier.grade z))
    obtain ⟨e, he⟩ := E.exhaustive d.1 d.2.1
    exact ⟨e, (congrArg F.old he).trans hd.symm⟩
  row c d := (F.inherited_row (E.map c) (E.belowMap c d)).trans (E.row c d)

theorem inheritedFace_order {S : Finset ι} {D₀ : CellScheme S} {sem₀ : Semantics D₀}
    (hS : S ⊆ A) (hne : S ≠ A) (E : ExactSemanticFace sem₀ F.sem)
    (hE : StrictMono E.map) : StrictMono (F.inheritedFace hS hne E).map :=
  F.old_strictMono.comp hE

end
end VaughtConjecture.Knight.FinalGateLayer.Input
