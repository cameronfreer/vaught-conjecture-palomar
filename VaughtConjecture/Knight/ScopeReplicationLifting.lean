/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ScopeReplicationSemantics
public import VaughtConjecture.Knight.CoatomBoundaryExtension

/-! # Whole-target section equivalence and all-coordinate lift transport

On a full-scope graded domain, lawful replicated sections are exactly the
duplicates of lawful single-copy sections. This is derived from actual copy
equality. Consequently an original-face lift transfers with every occurrence's
cap retained. No mixed-prescription extension, source admission, or missing
original-face lift is assumed proved by this module.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ScopeReplicationLifting
open AmalgamationPlan Transform Value ExtOrd ScopeReplicationCarrier
open ScopeReplicationSemantics CoatomBoundaryExtension
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (B C : Finset ι)
  (hcover : ∀ c : Cell D, D.scope c ≠ A → D.scope c ⊆ B ∨ D.scope c ⊆ C)
  (sem : Semantics D)

def fullErase (j : ℕ) (d : (scheme D B C).below (A, j)) : D.below (A, j) :=
  ⟨erase D B C d.1, D.isPlan.subset_of_mem (D.scope_mem_plan _),
    (erase_grade D B C d.1).le.trans d.2.2⟩

def duplicate {j : ℕ} (p : D.below (A, j) → ExtOrd) : (scheme D B C).below (A, j) → ExtOrd :=
  p ∘ fullErase D B C j

theorem duplicate_lawful {j : ℕ} {p : D.below (A, j) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (A, j) p) :
    RespectsSemanticsBelow (rows D B C hcover sem) (A, j) (duplicate D B C p) :=
  duplicateBelow_respects D B C hcover sem (fun d => (fullErase D B C j d).2) hp

theorem restrict_duplicate {j : ℕ} (p : D.below (A, j) → ExtOrd) :
    duplicate D B C p ∘ oldBelow D B C (A, j) = p := by
  funext d
  exact congrArg p (Subtype.ext (erase_old D B C d.1))

/-- Every auxiliary copy is retained individually, not reconstructed from
field readouts or a selected profile. -/
theorem duplicate_restrict {j : ℕ} {p : (scheme D B C).below (A, j) → ExtOrd}
    (hp : RespectsSemanticsBelow (rows D B C hcover sem) (A, j) p) :
    duplicate D B C (p ∘ oldBelow D B C (A, j)) = p := by
  funext d
  apply (copy_eq D B C hcover sem hp d (oldBelow D B C (A, j) (fullErase D B C j d))
    ?_ ?_).symm
  · change (scheme D B C).scope d.1 ⊆ (scheme D B C).scope (old D B C (erase D B C d.1))
    simpa only [CellScheme.scope, old_index] using scope_le_erase D B C d.1
  · exact (erase_old D B C (erase D B C d.1)).symm

/-- A single-copy original-face lift gives a replicated full-target lift at
the same external cap, bottom and top included. -/
theorem lift_to_full {I : Finset ι × ℕ} {j : ℕ} (h : GradedLe I (A, j))
    (hside : I.1 ⊆ B ∨ I.1 ⊆ C) (hl : CappedLift sem h) :
    CappedLift (rows D B C hcover sem) h := by
  intro p q γ hp hq hγ hag
  let p' := p ∘ oldBelow D B C I
  let q' := q ∘ oldBelow D B C (A, j)
  have hp' : RespectsSemanticsBelow sem I p' := restrict_respects D B C hcover sem hp
  have hq' : RespectsSemanticsBelow sem (A, j) q' := restrict_respects D B C hcover sem hq
  obtain ⟨r, hr, hcap, hread⟩ := hl p' q' γ hp' hq' hγ (fun d => hag (oldBelow D B C I d))
  refine ⟨duplicate D B C r, duplicate_lawful D B C hcover sem hr, ?_, ?_⟩
  · intro d
    have hc := hcap (fullErase D B C j d)
    have he := congrFun (duplicate_restrict D B C hcover sem hq) d
    exact hc.trans (congrArg (fun x => min x γ) he)
  · intro d
    rcases cases D B C d.1 with ⟨c, hc⟩ | ⟨a, ha⟩
    · have hcI : GradedLe (D.cell c) I := by rw [← old_index D B C c, ← hc]; exact d.2
      have he : oldBelow D B C I ⟨c, hcI⟩ = d := Subtype.ext hc.symm
      rw [← he]
      change r (fullErase D B C j (CellScheme.below.mono h
        (oldBelow D B C I ⟨c, hcI⟩))) = p' ⟨c, hcI⟩
      have hf : fullErase D B C j (CellScheme.below.mono h
          (oldBelow D B C I ⟨c, hcI⟩)) = CellScheme.below.mono h ⟨c, hcI⟩ :=
        Subtype.ext (erase_old D B C c)
      exact (congrArg r hf).trans (hread ⟨c, hcI⟩)
    · have hs : a.1.1.1 ⊆ I.1 := by
        simpa only [ha, added_index] using d.2.1
      exact (hside.elim (fun hb => a.2.2.1.1 (hs.trans hb))
        (fun hc => a.2.2.1.2 (hs.trans hc))).elim

end
end VaughtConjecture.Knight.ScopeReplicationLifting
