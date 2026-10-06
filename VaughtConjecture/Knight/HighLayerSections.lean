/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HighLayerBountiful
public import VaughtConjecture.Knight.GradeTailRestoration

/-! # Literal section supply with a zero high tail

This construction accepts arbitrary lawful old values, including literal top.
It requires neither positive continuation nor a supported canonical encoding.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.HighLayerBountiful
open Transform Value ExtOrd CoatomBoundaryExtension SourceLayerCarrier GradeTailRestoration
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
theorem exists_zero_tail {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    ∃ r : Cell (scheme D Q l hl hlA) → ExtOrd,
      RespectsSemantics out r ∧
      (∀ d, r (old D Q l hl hlA d) = p d) ∧
      ∀ q : Q, r (SourceLayerCarrier.controller D Q l hl hlA q).1 = ⊥ := by
  let e := equiv D Q l hl hlA (A, K) (fun h => (not_le_of_gt hKl) h.2)
  let v : (scheme D Q l hl hlA).below (A, K) → ExtOrd := fun d => p (e.symm d).1
  have hv : RespectsSemanticsBelow out (A, K) v :=
    (respects_iff D Q l hl hlA K hK hKl sem out hrow (A, K)
      (fun h => (not_le_of_gt hKl) h.2) _).mp (hp.toBelow _)
  let u : (scheme D Q l hl hlA).below (A, l) → ExtOrd := fun _ => ⊥
  have hu : RespectsSemanticsBelow out (A, l) u :=
    (bottomSection out (A, l) (A, l)).left_lawful
  have hs : RespectsSemanticsBelow out (A, l) (splice u v) :=
    splice_respects hKl.le hu hv (M := ⊥) (fun _ _ => le_rfl)
      (fun _ => by simp only [u, min_bot_right])
  have hall (d : Cell (scheme D Q l hl hlA)) :
      GradedLe ((scheme D Q l hl hlA).cell d) (A, l) := by
    refine ⟨(scheme D Q l hl hlA).isPlan.subset_of_mem
      ((scheme D Q l hl hlA).scope_mem_plan d), ?_⟩
    rw [cell_eq]
    cases toOcc D Q l hl hlA d with
    | inl x => exact (hK x).trans hKl.le
    | inr q => exact le_rfl
  refine ⟨fun d => splice u v ⟨d, hall d⟩, hs.toRespects hall, ?_, ?_⟩
  · intro d
    have hd : (scheme D Q l hl hlA).grade (old D Q l hl hlA d) ≤ K := by
      simpa only [CellScheme.grade, old, cell_toCell, index] using hK d
    apply (splice_low u v ⟨old D Q l hl hlA d, hall _⟩ hd).trans
    let d₀ : D.below (A, K) := ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hK d⟩
    change p (e.symm (e d₀)).1 = p d
    rw [Equiv.symm_apply_apply]
  · intro q
    apply splice_high u v _
    change ¬ ((scheme D Q l hl hlA).cell
      (SourceLayerCarrier.controller D Q l hl hlA q).1).2 ≤ K
    rw [(SourceLayerCarrier.controller D Q l hl hlA q).2]
    exact not_le_of_gt hKl

end
end VaughtConjecture.Knight.HighLayerBountiful
