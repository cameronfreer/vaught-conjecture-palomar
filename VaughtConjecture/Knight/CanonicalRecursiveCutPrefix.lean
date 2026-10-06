/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursivePrefix
public import VaughtConjecture.Knight.CanonicalRecursiveAmbient

/-! # Current-boundary repair with the complete persistent field inventory

Only the actual grade cut participates in old-face completion. Every other
original field is retained before normalization, so controller caps continue
to refer to the same full inventory.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveCutPrefix
open Transform Value ExtOrd CanonicalRecursiveSuccessorRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))

abbrev cut := GradeCutBoundary.scheme D (n + 4)
abbrev cutRows := GradeCutBoundary.rows D (n + 4) sem
abbrev occurrence := GradeCutBoundary.toCell D (n + 4)

def oldTarget (d : Cell (cut (D := D) n)) : CanonicalRecursiveAmbient.target sem n hA :=
  ⟨boundary sem n hA (occurrence (D := D) n d), by
    have he : (carrier sem n hA).cell (boundary sem n hA (occurrence (D := D) n d)) =
        D.cell (occurrence (D := D) n d) :=
      CanonicalRecursiveInventory.boundary_cell sem (n + 4) hA _
    rw [he]
    exact ⟨D.isPlan.subset_of_mem (D.scope_mem_plan _), GradeCutBoundary.grade_bound D _ d⟩⟩

theorem oldTarget_cell (d : Cell (cut (D := D) n)) :
    (carrier sem n hA).cell (oldTarget sem n hA d).1 = (cut (D := D) n).cell d :=
  CanonicalRecursiveInventory.boundary_cell sem (n + 4) hA _

theorem exists_section (a : Profile sem n)
    {p : Cell (cut (D := D) n) → ExtOrd} (hpr : RespectsSemantics (cutRows sem n) p)
    (ht : ∀ d, p d ≠ ⊤) {B : ℕ} (hB : B ≤ 2 * Fintype.card (Cell D) + 1)
    (hag : ∀ d, min (a.val (occurrence (D := D) n d)) (CanonicalPairedInverse.grid (n + 4) B) =
      min (p d) (CanonicalPairedInverse.grid (n + 4) B)) :
    ∃ r : Cell (carrier sem n hA) → ExtOrd,
      RespectsSemanticsBelow (rows sem n hA hp P) (A, n + 4) (fun d => r d.1) ∧
      (∀ d, r (oldTarget sem n hA d).1 = p d) ∧
      ∀ d, min (r d) (CanonicalPairedInverse.grid (n + 4) B) =
        min (source sem n hA hp P a d) (CanonicalPairedInverse.grid (n + 4) B) := by
  classical
  let occ := occurrence (D := D) n
  let v := Function.extend occ p a.val
  have hv (d) : v (occ d) = p d := occ.injective.extend_apply p a.val d
  have hvp : RespectsSemantics (cutRows sem n) (v ∘ occ) := by
    simpa only [Function.comp_def, hv] using hpr
  have hl := (GradeCutBoundary.respects_iff D (n + 4) sem (A, n + 4) le_rfl _).mp
    (hvp.toBelow (A, n + 4))
  have hvl : RespectsSemanticsBelow sem (A, n + 4) (fun d => v d.1) := by
    convert hl using 1
    funext d
    exact (congrArg v (congrArg Subtype.val
      ((GradeCutBoundary.belowEquiv D (n + 4) (A, n + 4) le_rfl).apply_symm_apply d))).symm
  have hvt : ∀ x, v x ≠ ⊤ := by
    intro x
    by_cases hx : ∃ d, occ d = x
    · obtain ⟨d, rfl⟩ := hx
      rw [hv]; exact ht d
    · rw [show v x = a.val x from Function.extend_apply' p a.val x hx]
      exact a.property.2.2 x
  have hva : ∀ x, min (a.val x) (CanonicalPairedInverse.grid (n + 4) B) =
      min (v x) (CanonicalPairedInverse.grid (n + 4) B) := by
    intro x
    by_cases hx : ∃ d, occ d = x
    · obtain ⟨d, rfl⟩ := hx
      rw [hv]; exact hag d
    · rw [show v x = a.val x from Function.extend_apply' p a.val x hx]
  obtain ⟨r, hr, hread, hcap⟩ :=
    CanonicalRecursivePrefix.exists_section sem n hA hp P a hvl hvt hB hva
  exact ⟨r, hr, fun d => (hread (occ d)).trans (hv d), hcap⟩

end
end VaughtConjecture.Knight.CanonicalRecursiveCutPrefix
