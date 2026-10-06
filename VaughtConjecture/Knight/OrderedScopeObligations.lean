/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrderedScopeSections

/-! # Lifting and owner classification after scope installation

Previously completed targets keep their complete lower domains. The new scope
uses the local operator's proved bountifulness. No bountifulness of the ambient
partial carrier is assumed. These are the per-step receipts for scope iteration,
not a claim that every scope has already been completed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrderedScopeRelocation
open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}
variable {D : CellScheme A} (sem : Semantics D) (hB : B ∈ D.plan) {k : ℕ}
variable (S : OrdinaryScopeOperator.Core (ScopeBoundary.rows D B hB sem) k)
variable (hsep : Separated (D := D) (B := B))
local notation "K" => carrier sem hB S
local notation "l" => old sem hB S
local notation "r" => localCell sem hB S

def retainedFace {C : Finset ι} {E : CellScheme C} {semE : Semantics E}
    (F : ExactSemanticFace semE sem) (hC : ¬ B ⊆ C) :
    ExactSemanticFace semE (rows sem hB S hsep) where
  map := F.map.trans ⟨l, (old_order sem hB S).injective⟩
  index d := (old_index sem hB S _).trans (F.index d)
  exhaustive z hz := by
    rcases classify sem hB S z with ⟨d, rfl⟩ | he
    · have hd : D.scope d ⊆ C := by
        simpa only [CellScheme.scope, old_index] using hz
      obtain ⟨e, rfl⟩ := F.exhaustive d hd
      exact ⟨e, rfl⟩
    · exact False.elim (hC (he ▸ hz))
  row c d := (row_old sem hB S hsep (F.map c) (F.belowMap c d)).trans (F.row c d)

theorem retainedFace_order {C : Finset ι} {E : CellScheme C} {semE : Semantics E}
    (F : ExactSemanticFace semE sem) (hC : ¬ B ⊆ C) (hF : StrictMono F.map) :
    StrictMono (retainedFace sem hB S hsep F hC).map := (old_order sem hB S).comp hF

/-- All earlier targets not containing this new scope are literally unchanged. -/
def oldLower (J : Finset ι × ℕ) (hJ : ¬ B ⊆ J.1) : D.below J ≃ (K).below J :=
  Equiv.ofBijective (fun d => ⟨l d.1, by rw [old_index]; exact d.2⟩) ⟨by
    intro d e h
    exact Subtype.ext ((old_order sem hB S).injective (congrArg Subtype.val h)), by
    intro z
    rcases classify sem hB S z.1 with ⟨d, hd⟩ | hd
    · refine ⟨⟨d, ?_⟩, Subtype.ext hd⟩
      simpa only [← hd, old_index] using z.2
    · exact False.elim (hJ (hd ▸ z.2.1))⟩

theorem oldLower_respects (J : Finset ι × ℕ) (hJ : ¬ B ⊆ J.1)
    (p : D.below J → ExtOrd) :
    RespectsSemanticsBelow sem J p ↔
      RespectsSemanticsBelow (rows sem hB S hsep) J (p ∘ (oldLower sem hB S J hJ).symm) :=
  respects_iff_of_equiv (oldLower sem hB S J hJ)
    (fun d => (congrArg Prod.snd (old_index sem hB S d.1)).symm)
    (fun d e => by
      change D.scope d.1 ⊆ D.scope e.1 ↔ ((K).cell (l d.1)).1 ⊆ ((K).cell (l e.1)).1
      rw [old_index, old_index]; rfl)
    (fun c d _ => (row_old sem hB S hsep c.1 d).symm) p

theorem oldLower_pullback (J : Finset ι × ℕ) (hJ : ¬ B ⊆ J.1)
    (q : (K).below J → ExtOrd) :
    RespectsSemanticsBelow (rows sem hB S hsep) J q ↔
      RespectsSemanticsBelow sem J (q ∘ oldLower sem hB S J hJ) := by
  have h := oldLower_respects sem hB S hsep J hJ (q ∘ oldLower sem hB S J hJ)
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h.symm

theorem old_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : ¬ B ⊆ J.1)
    (hb : CappedLift sem h) : CappedLift (rows sem hB S hsep) h := by
  have hI : ¬ B ⊆ I.1 := fun hi => hJ (hi.trans h.1)
  let eJ := oldLower sem hB S J hJ
  let eI := oldLower sem hB S I hI
  intro p q γ hp hq hγ hc
  apply bountiful_of_equiv (sem' := rows sem hB S hsep) (sem := sem)
    h h eJ.symm eI.symm ?_ ?_ ?_ hb rfl p q γ hp hq hγ hc
  · intro d
    apply eJ.injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact (congrArg Subtype.val (eI.apply_symm_apply d)).symm
  · exact oldLower_pullback sem hB S hsep J hJ
  · exact oldLower_pullback sem hB S hsep I hI

theorem local_lift {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hI : I ∈ Plan.gradedPlan D.plan) (hJ : J ∈ Plan.gradedPlan D.plan) (hJB : J.1 ⊆ B) :
    CappedLift (rows sem hB S hsep) h := by
  by_cases he : I = J
  · subst J; exact lift_refl
  · have memLocal : ∀ T ∈ Plan.gradedPlan D.plan, T.1 ⊆ B →
        T ∈ Plan.gradedPlan S.carrier.plan := by
      intro T hT hTB
      obtain ⟨hp, hg, hc⟩ := Plan.mem_gradedPlan.mp hT
      rw [S.plan]
      exact Plan.mem_gradedPlan.mpr
        ⟨Finset.mem_inter.mpr ⟨hp, Finset.mem_powerset.mpr hTB⟩, hg, hc⟩
    exact (localFace sem hB S hsep).lift hJB (memLocal I hI (h.1.trans hJB))
      (memLocal J hJ hJB) h he S.bountiful

/-- Installation preserves old completeness and adds the newly completed indices. -/
theorem complete_at (J : Finset ι × ℕ)
    (h : (∃ d : Cell D, D.cell d = J) ∨ ∃ d : Cell S.carrier, S.carrier.cell d = J) :
    ∃ d : Cell K, (K).cell d = J := by
  rcases h with ⟨d, hd⟩ | ⟨d, hd⟩
  · exact ⟨l d, (old_index sem hB S d).trans hd⟩
  · exact ⟨r d, (local_index sem hB S d).trans hd⟩

/-- The selected-display decoder needs this alternative, not global shortness. -/
def OwnerClassification {X : Type*} (original : X → Cell D) : Prop :=
  ∀ c : Cell D, (∀ d, SharpWitnessComposition.Short (D.grade c) (sem.E c d)) ∨
    ∀ d : D.below (D.cell c), ∃ x, original x = d.1

theorem ownerClassification {X : Type*} (original : X → Cell D)
    (hc : OwnerClassification sem original) :
    OwnerClassification (rows sem hB S hsep) (l ∘ original) := by
  intro z
  rcases classify sem hB S z with ⟨c, rfl⟩ | hz
  · rcases hc c with hshort | horiginal
    · left
      intro d
      obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
      change SharpWitnessComposition.Short ((K).cell (l c)).2
        ((rows sem hB S hsep).E (l c) _)
      rw [row_old, old_index]
      exact hshort e
    · right
      intro d
      obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
      obtain ⟨x, hx⟩ := horiginal e
      exact ⟨x, congrArg l hx⟩
  · obtain ⟨c, rfl⟩ := local_exhaustive sem hB S z (subset_of_eq hz)
    have hc : S.carrier.scope c = B := by
      simpa only [CellScheme.scope, local_index] using hz
    left
    intro d
    obtain ⟨e, rfl⟩ := (localBelow sem hB S c).surjective d
    change SharpWitnessComposition.Short ((K).cell (r c)).2
      ((rows sem hB S hsep).E (r c) _)
    rw [row_local, local_index]
    exact S.short c hc e

/-- The initial inventory is itself the original-field inventory, regardless
of the lengths of any of its rows. -/
theorem ownerClassification_initial : OwnerClassification sem (id : Cell D → Cell D) :=
  fun _ => Or.inr (fun d => ⟨d.1, rfl⟩)

/-- A later incomparable or larger scope remains separated from all installed
owners. This is the separation invariant used by increasing-scope iteration. -/
theorem separated_next {C : Finset ι} (hc : Separated (D := D) (B := C))
    (hCB : ¬ C ⊆ B) : Separated (D := K) (B := C) := by
  intro z hz
  rcases classify sem hB S z with ⟨d, rfl⟩ | hd
  · apply hc d
    simpa only [CellScheme.scope, old_index] using hz
  · exact hCB (hd ▸ hz)

theorem separated_next_of_card {C : Finset ι} (hc : Separated (D := D) (B := C))
    (hcard : B.card ≤ C.card) (hne : C ≠ B) : Separated (D := K) (B := C) :=
  separated_next sem hB S hc (fun h => hne (Finset.eq_of_subset_of_card_le h hcard))

/-- Relocation transports the *universal* mute receipt, not merely the bottom
label of the selected display. Higher ambient owners are not bounded here. -/
theorem completed_highest_inactive (hk : 0 < k) (hcard : B.card = k + 1)
    {p : Cell (carrier sem hB (S.finish hk hcard)) → ExtOrd}
    (hp : RespectsSemantics (rows sem hB (S.finish hk hcard) hsep) p)
    (d : Cell (carrier sem hB (S.finish hk hcard)))
    (hdB : (carrier sem hB (S.finish hk hcard)).scope d ⊆ B)
    (hd : (carrier sem hB (S.finish hk hcard)).grade d = k + 1) : p d = ⊥ := by
  obtain ⟨c, rfl⟩ := local_exhaustive sem hB (S.finish hk hcard) d hdB
  have hg : (S.finish hk hcard).carrier.grade c = k + 1 := by
    simpa only [CellScheme.grade, local_index] using hd
  exact S.finish_highest_inactive hk hcard
    ((localFace sem hB (S.finish hk hcard) hsep).restrict hp) c hg

end

section InitialBoundary
variable {ι : Type*} [DecidableEq ι] {A L R B : Finset ι}
variable {P : Finset (Finset ι)} {m nL nR : ℕ}

/-- On the actual ordered input boundary, being mixed supplies precisely the
separation used by relocation, even when a private owner has a higher grade. -/
theorem boundary_separated (I : WholeDonorBoundary.Input A L R P m nL nR)
    (hL : ¬ B ⊆ L) (hR : ¬ B ⊆ R) : Separated (D := I.boundary) (B := B) := by
  intro d hd
  rcases (I.occupied_iff (I.boundary.cell_mem d)).mp ⟨d, rfl⟩ with hl | hr
  · exact hL (hd.trans hl)
  · exact hR (hd.trans hr)

end InitialBoundary
end VaughtConjecture.Knight.OrderedScopeRelocation
