/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceLayerCarrier

/-! # Replicating full-scope auxiliary occurrences at mixed scopes

Keep the entire original enumeration and append one scope-tagged copy of each
full-scope cell at every proper mixed plan scope permitting its grade. Erasing
a scope tag preserves the grade, but need not preserve the scope. Original
proper owners retain their domains; auxiliary owners acquire new arguments.
No semantic or lifting hypothesis enters this finite carrier construction.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ScopeReplicationCarrier
open AmalgamationPlan
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (B C : Finset ι)

def Mixed (U : Finset ι) : Prop := ¬ U ⊆ B ∧ ¬ U ⊆ C

abbrev Copy := {p : (↑D.plan) × Cell D //
  p.1.1 ≠ A ∧ Mixed B C p.1.1 ∧ D.scope p.2 = A ∧ D.grade p.2 ≤ p.1.1.card}

instance : Fintype (Copy D B C) := Fintype.ofFinite _

def scheme : CellScheme A where
  plan := D.plan
  isPlan := D.isPlan
  card := D.card + Fintype.card (Copy D B C)
  cell := Fin.addCases D.cell (fun i =>
    let p := (Fintype.equivFin (Copy D B C)).symm i
    (p.1.1.1, D.grade p.1.2))
  cell_mem c := by
    refine Fin.addCases ?_ ?_ c
    · intro d; simpa only [Fin.addCases_left] using D.cell_mem d
    · intro i
      simp only [Fin.addCases_right]
      let p := (Fintype.equivFin (Copy D B C)).symm i
      exact Plan.mem_gradedPlan.mpr ⟨p.1.1.2, D.grade_pos _, p.2.2.2.2⟩

def enumeration : (Cell D ⊕ Copy D B C) ≃ Cell (scheme D B C) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin (Copy D B C))).trans finSumFinEquiv

abbrev old (d : Cell D) : Cell (scheme D B C) := enumeration D B C (.inl d)
abbrev added (p : Copy D B C) : Cell (scheme D B C) := enumeration D B C (.inr p)

theorem old_index (d : Cell D) : (scheme D B C).cell (old D B C d) = D.cell d := by
  change (scheme D B C).cell (Fin.castAdd (Fintype.card (Copy D B C)) d) = D.cell d
  unfold scheme
  simp only [Fin.addCases_left]

theorem added_index (p : Copy D B C) :
    (scheme D B C).cell (added D B C p) = (p.1.1.1, D.grade p.1.2) := by
  change (scheme D B C).cell (Fin.natAdd D.card (Fintype.equivFin (Copy D B C) p)) = _
  unfold scheme
  simp only [Fin.addCases_right, Equiv.symm_apply_apply]

theorem old_order : StrictMono (old D B C) := Fin.strictMono_castAdd _

theorem cases (d : Cell (scheme D B C)) :
    (∃ c, d = old D B C c) ∨ ∃ p, d = added D B C p := by
  obtain ⟨x, rfl⟩ := (enumeration D B C).surjective d
  cases x with
  | inl c => exact Or.inl ⟨c, rfl⟩
  | inr p => exact Or.inr ⟨p, rfl⟩

def erase (d : Cell (scheme D B C)) : Cell D :=
  match (enumeration D B C).symm d with
  | .inl c => c
  | .inr p => p.1.2

@[simp] theorem erase_old (d : Cell D) : erase D B C (old D B C d) = d := by
  simp only [erase, old, Equiv.symm_apply_apply]

@[simp] theorem erase_added (p : Copy D B C) : erase D B C (added D B C p) = p.1.2 := by
  simp only [erase, added, Equiv.symm_apply_apply]

theorem erase_grade (d : Cell (scheme D B C)) :
    D.grade (erase D B C d) = (scheme D B C).grade d := by
  rcases cases D B C d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · rw [erase_old]; exact (congrArg Prod.snd (old_index D B C c)).symm
  · rw [erase_added]; exact (congrArg Prod.snd (added_index D B C p)).symm

theorem erase_scope_of_ne (d : Cell (scheme D B C)) (h : D.scope (erase D B C d) ≠ A) :
    D.scope (erase D B C d) = (scheme D B C).scope d := by
  rcases cases D B C d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · rw [erase_old]; exact (congrArg Prod.fst (old_index D B C c)).symm
  · exact (h (by rw [erase_added]; exact p.2.2.2.1)).elim

theorem scope_le_erase (d : Cell (scheme D B C)) :
    (scheme D B C).scope d ⊆ D.scope (erase D B C d) := by
  rcases cases D B C d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · rw [erase_old]
    exact (congrArg Prod.fst (old_index D B C c)).le
  · rw [erase_added, p.2.2.2.1]
    exact (scheme D B C).isPlan.subset_of_mem ((scheme D B C).scope_mem_plan _)

theorem full_or_mixed (d : Cell (scheme D B C))
    (h : D.scope (erase D B C d) = A) :
    (scheme D B C).scope d = A ∨ Mixed B C ((scheme D B C).scope d) := by
  rcases cases D B C d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · exact Or.inl ((congrArg Prod.fst (old_index D B C c)).trans
      (by simpa only [erase_old, CellScheme.scope] using h))
  · exact Or.inr (by simpa only [CellScheme.scope, added_index] using p.2.2.1)

variable (hcover : ∀ c : Cell D, D.scope c ≠ A → D.scope c ⊆ B ∨ D.scope c ⊆ C)

include hcover in
theorem erase_le {d c : Cell (scheme D B C)}
    (h : GradedLe ((scheme D B C).cell d) ((scheme D B C).cell c)) :
    GradedLe (D.cell (erase D B C d)) (D.cell (erase D B C c)) := by
  refine ⟨?_, ?_⟩
  swap
  · change D.grade (erase D B C d) ≤ D.grade (erase D B C c)
    rw [erase_grade, erase_grade]
    exact h.2
  change D.scope (erase D B C d) ⊆ D.scope (erase D B C c)
  by_cases hc : D.scope (erase D B C c) = A
  · rw [hc]; exact D.isPlan.subset_of_mem (D.scope_mem_plan _)
  · rw [erase_scope_of_ne D B C c hc]
    rcases cases D B C d with ⟨e, rfl⟩ | ⟨p, rfl⟩
    · simpa only [erase_old, CellScheme.scope, old_index] using h.1
    · have hs : p.1.1.1 ⊆ D.scope (erase D B C c) := by
        rw [erase_scope_of_ne D B C c hc]
        simpa only [CellScheme.scope, added_index] using h.1
      rcases hcover _ hc with hb | hc'
      · exact (p.2.2.1.1 (hs.trans hb)).elim
      · exact (p.2.2.1.2 (hs.trans hc')).elim

def belowErase (c : Cell (scheme D B C)) :
    (scheme D B C).below ((scheme D B C).cell c) → D.below (D.cell (erase D B C c)) :=
  fun d => ⟨erase D B C d.1, erase_le D B C hcover d.2⟩

include hcover in
/-- New occurrences occupy formerly empty proper mixed indices. -/
theorem old_index_exhaustive (c : Cell D) (z : Cell (scheme D B C))
    (hz : (scheme D B C).cell z = D.cell c) : ∃ d, old D B C d = z := by
  rcases cases D B C z with ⟨d, rfl⟩ | ⟨p, rfl⟩
  · exact ⟨d, rfl⟩
  · have hs : p.1.1.1 = D.scope c := (congrArg Prod.fst (added_index D B C p)).symm.trans
      (congrArg Prod.fst hz)
    by_cases hc : D.scope c = A
    · exact (p.2.1 (hs.trans hc)).elim
    · rcases hcover c hc with hb | hc'
      · exact (p.2.2.1.1 (hs ▸ hb)).elim
      · exact (p.2.2.1.2 (hs ▸ hc')).elim

def oldBelow (J : Finset ι × ℕ) (d : D.below J) : (scheme D B C).below J :=
  ⟨old D B C d.1, by rw [old_index]; exact d.2⟩

/-- Relocate a full-scope prototype to an actual mixed scope, retaining its
identity. At the full scope use its existing occurrence. -/
def atScope (U : Finset ι) (hU : U ∈ D.plan) (hm : U = A ∨ Mixed B C U)
    (c : Cell D) (hc : D.scope c = A) (hg : D.grade c ≤ U.card) :
    Cell (scheme D B C) := by
  classical
  exact if h : U = A then old D B C c else
    added D B C ⟨(⟨U, hU⟩, c), h, hm.resolve_left h, hc, hg⟩

theorem atScope_index (U : Finset ι) (hU : U ∈ D.plan) (hm : U = A ∨ Mixed B C U)
    (c : Cell D) (hc : D.scope c = A) (hg : D.grade c ≤ U.card) :
    (scheme D B C).cell (atScope D B C U hU hm c hc hg) = (U, D.grade c) := by
  classical
  unfold atScope
  split_ifs with h
  · exact (old_index D B C c).trans (Prod.ext (hc.trans h.symm) rfl)
  · exact added_index D B C _

theorem erase_atScope (U : Finset ι) (hU : U ∈ D.plan) (hm : U = A ∨ Mixed B C U)
    (c : Cell D) (hc : D.scope c = A) (hg : D.grade c ≤ U.card) :
    erase D B C (atScope D B C U hU hm c hc hg) = c := by
  classical
  unfold atScope
  split_ifs <;> simp only [erase_old, erase_added]

/-- Any original availability witness at the erased target has an actual
occurrence at that target's scope, with exactly the same prototype. -/
theorem exists_at_index (t : Cell (scheme D B C)) (w : Cell D)
    (hw : D.cell w = D.cell (erase D B C t)) :
    ∃ z : Cell (scheme D B C),
      (scheme D B C).cell z = (scheme D B C).cell t ∧ erase D B C z = w := by
  by_cases ht : D.scope (erase D B C t) = A
  · have hws : D.scope w = A := (congrArg Prod.fst hw).trans ht
    have hwg : D.grade w = (scheme D B C).grade t :=
      (congrArg Prod.snd hw).trans (erase_grade D B C t)
    let z := atScope D B C ((scheme D B C).scope t) ((scheme D B C).scope_mem_plan t)
      (full_or_mixed D B C t ht) w hws (hwg ▸ (scheme D B C).grade_le_card_scope t)
    refine ⟨z, ?_, erase_atScope D B C _ _ _ _ _ _⟩
    exact (atScope_index D B C _ _ _ _ _ _).trans (by rw [hwg]; rfl)
  · refine ⟨old D B C w, (old_index D B C w).trans (hw.trans ?_), erase_old D B C w⟩
    exact Prod.ext (erase_scope_of_ne D B C t ht) (erase_grade D B C t)

end
end VaughtConjecture.Knight.ScopeReplicationCarrier
