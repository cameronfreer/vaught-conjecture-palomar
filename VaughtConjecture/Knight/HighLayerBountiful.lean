/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SeparatedSourceLayerCarrier
public import VaughtConjecture.Knight.EffectiveGradeLifting

/-! # Bountifulness survives a strictly higher full-scope layer

Only literal old rows and old bountifulness are required. A proper prescription
has no new-grade occurrences: lift below the old grade ceiling, then paste the
new upper tail at the original permitted cap. This does not cover prescribed
proper owners of the new grade, nor force positive upper continuation.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.HighLayerBountiful
open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan SourceLayerCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q : Type*) [Fintype Q] (l : ℕ) (hl : 0 < l) (hlA : l ≤ A.card)

abbrev old (d : Cell D) := toCell D Q l hl hlA (.inl d)

/-- Exact domains whenever the new index is absent: proper scopes and low
full-scope cuts are handled by the same equivalence. -/
def equiv (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, l) J) :
    D.below J ≃ (scheme D Q l hl hlA).below J :=
  Equiv.ofBijective (fun d => ⟨old D Q l hl hlA d.1, by
    simpa only [old, cell_toCell, index] using d.2⟩) ⟨by
      intro d e h
      exact Subtype.ext ((old_order D Q l hl hlA).injective (congrArg Subtype.val h)), by
      intro d
      cases he : toOcc D Q l hl hlA d.1 with
      | inl c =>
        have hc : GradedLe (D.cell c) J := by
          simpa only [cell_eq, he, index] using d.2
        refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
        change toCell D Q l hl hlA (.inl c) = d.1
        rw [← he, toCell_toOcc]
      | inr q => exact False.elim (hJ (by
          simpa only [cell_eq, he, index] using d.2))⟩

theorem equiv_cell (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, l) J) (d : D.below J) :
    (scheme D Q l hl hlA).cell (equiv D Q l hl hlA J hJ d).1 = D.cell d.1 :=
  cell_toCell _ _ _ _ _ (.inl d.1)

variable (K : ℕ) (hK : ∀ d : Cell D, D.grade d ≤ K) (hKl : K < l)

include hK hKl in
theorem separated (d : Cell D) : ¬ GradedLe (A, l) (D.cell d) :=
  fun h => (not_le_of_gt hKl) (h.2.trans (hK d))

variable (sem : Semantics D) (out : Semantics (scheme D Q l hl hlA))
variable (hrow : ∀ (c : Cell D) (d : D.below (D.cell c)),
  out.E (old D Q l hl hlA c)
    (SeparatedSourceLayerCarrier.ownerEquiv D Q l hl hlA (separated D l K hK hKl) c d) =
    sem.E c d)

include hrow in
theorem respects_iff (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, l) J)
    (p : D.below J → ExtOrd) :
    RespectsSemanticsBelow sem J p ↔
      RespectsSemanticsBelow out J (p ∘ (equiv D Q l hl hlA J hJ).symm) := by
  apply respects_iff_of_equiv (equiv D Q l hl hlA J hJ)
    (fun d => (congrArg Prod.snd (equiv_cell D Q l hl hlA J hJ d)).symm)
    (fun d e => ?_) (fun b d _ => ?_) p
  · simp only [CellScheme.scope, equiv_cell]
  · exact (hrow b.1 d).symm

include hrow in
theorem pullback_respects {J : Finset ι × ℕ} (hJ : ¬ GradedLe (A, l) J)
    {q : (scheme D Q l hl hlA).below J → ExtOrd}
    (hq : RespectsSemanticsBelow out J q) :
    RespectsSemanticsBelow sem J (q ∘ equiv D Q l hl hlA J hJ) := by
  apply (respects_iff D Q l hl hlA K hK hKl sem out hrow J hJ _).mpr
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hq

include hrow in
theorem transport_lift {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hJ : ¬ GradedLe (A, l) J) (hb : CappedLift sem h) : CappedLift out h := by
  intro p q γ hp hq hγ hag
  have hI : ¬ GradedLe (A, l) I := fun hI => hJ (hI.trans h)
  let eI := equiv D Q l hl hlA I hI
  let eJ := equiv D Q l hl hlA J hJ
  have hm (d : D.below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  obtain ⟨r, hr, hcap, hread⟩ := hb (p ∘ eI) (q ∘ eJ) γ
    (pullback_respects D Q l hl hlA K hK hKl sem out hrow hI hp)
    (pullback_respects D Q l hl hlA K hK hKl sem out hrow hJ hq) hγ
    (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm,
    (respects_iff D Q l hl hlA K hK hKl sem out hrow J hJ r).mp hr, fun d => ?_, fun d => ?_⟩
  · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (eJ.symm d)
  · have hd : eJ.symm (CellScheme.below.mono h d) =
        CellScheme.below.mono h (eI.symm d) := by
      apply eJ.injective
      rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply]
    rw [Function.comp_apply, hd, hread]
    exact congrArg p (eI.apply_symm_apply d)

end
end VaughtConjecture.Knight.HighLayerBountiful

namespace VaughtConjecture.Knight
open Transform Value ExtOrd CoatomBoundaryExtension

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- Proper-to-full lifting above an effective prescribed grade ceiling.
The lower lift is an actual already-proved clause, not a new-output completion
assumption. Every old prescribed value, including top, remains literal. -/
theorem cappedLift_of_prescribed_grade_bound {C B : Finset ι} {i n : ℕ}
    (hCB : C ⊆ B) (hin : i ≤ n)
    (hbound : ∀ d : D.below (C, n), D.grade d.1 ≤ i)
    (hlower : CappedLift sem (show GradedLe (C, i) (B, i) from ⟨hCB, le_rfl⟩)) :
    CappedLift sem (show GradedLe (C, n) (B, n) from ⟨hCB, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  let hCi : GradedLe (C, i) (C, n) := ⟨Finset.Subset.refl _, hin⟩
  let hBi : GradedLe (B, i) (B, n) := ⟨Finset.Subset.refl _, hin⟩
  let hlow : GradedLe (C, i) (B, i) := ⟨hCB, le_rfl⟩
  obtain ⟨u, hu, hucap, huread⟩ := hlower
    (p ∘ CellScheme.below.mono hCi) (q ∘ CellScheme.below.mono hBi) γ
    (hp.mono hCi) (hq.mono hBi) (hγ.mono hin) (fun d => hag (CellScheme.below.mono hCi d))
  obtain ⟨r, hr, hcap, hread⟩ := bountiful_same_scope sem hBi u q γ hu hq hγ
    (fun d => (hucap d).symm)
  refine ⟨r, hr, hcap, fun d => ?_⟩
  let e : D.below (C, i) := ⟨d.1, d.2.1, hbound d⟩
  exact (hread (CellScheme.below.mono hlow e)).trans (huread e)

end VaughtConjecture.Knight

namespace VaughtConjecture.Knight.HighLayerBountiful
open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan SourceLayerCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q : Type*) [Fintype Q] (l : ℕ) (hl : 0 < l) (hlA : l ≤ A.card)
variable (K : ℕ) (hK : ∀ d : Cell D, D.grade d ≤ K) (hKl : K < l)
variable (sem : Semantics D) (out : Semantics (scheme D Q l hl hlA))
variable (hrow : ∀ (c : Cell D) (d : D.below (D.cell c)),
  out.E (old D Q l hl hlA c)
    (SeparatedSourceLayerCarrier.ownerEquiv D Q l hl hlA (separated D l K hK hKl) c d) =
    sem.E c d)

include hrow in
/-- No condition on the new source profiles is needed for this lifting
reduction: their consistency is a separate construction theorem. -/
theorem bountiful (hpos : 0 < K) (hb : sem.IsBountiful) : out.IsBountiful := by
  have hmax (d : Cell (scheme D Q l hl hlA)) : (scheme D Q l hl hlA).grade d ≤ l := by
    rw [CellScheme.grade, cell_eq]
    cases toOcc D Q l hl hlA d with
    | inl x => exact (hK x).trans hKl.le
    | inr q => exact le_rfl
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade hmax hl
  intro C B n hC hB hn hCB
  change (C, n) ∈ Plan.gradedPlan D.plan at hC
  change (B, n) ∈ Plan.gradedPlan D.plan at hB
  by_cases hnew : GradedLe (A, l) (B, n)
  · have hBA : B = A := Finset.Subset.antisymm
      (D.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hB).1) hnew.1
    have hnl : n = l := le_antisymm hn hnew.2
    subst B; subst n
    by_cases hCA : C = A
    · subst C; exact lift_refl
    have hproper : ¬ A ⊆ C := fun hAC => hCA (Finset.Subset.antisymm hCB hAC)
    apply cappedLift_of_prescribed_grade_bound hCB hKl.le
    · intro d
      obtain ⟨c, hc⟩ := (equiv D Q l hl hlA (C, l) (fun h => hproper h.1)).surjective d
      rw [← hc]
      change ((scheme D Q l hl hlA).cell _).2 ≤ K
      rw [equiv_cell]
      exact hK c.1
    · apply transport_lift D Q l hl hlA K hK hKl sem out hrow
        (I := (C, K)) (J := (A, K)) ⟨hCB, le_rfl⟩
        (fun h => (not_le_of_gt hKl) h.2)
      apply lift_of_bountiful hb
      · exact Plan.mem_gradedPlan.mpr
          ⟨(Plan.mem_gradedPlan.mp hC).1, hpos, hKl.le.trans (Plan.mem_gradedPlan.mp hC).2.2⟩
      · exact Plan.mem_gradedPlan.mpr
          ⟨(Plan.mem_gradedPlan.mp hB).1, hpos, hKl.le.trans hlA⟩
  · exact transport_lift D Q l hl hlA K hK hKl sem out hrow
      (I := (C, n)) (J := (B, n)) ⟨hCB, le_rfl⟩ hnew
      (lift_of_bountiful hb hC hB ⟨hCB, le_rfl⟩)

end
end VaughtConjecture.Knight.HighLayerBountiful
