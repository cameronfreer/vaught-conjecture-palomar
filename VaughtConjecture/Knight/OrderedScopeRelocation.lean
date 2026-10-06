/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryScopeOperator
public import VaughtConjecture.Knight.ScopeBoundary

/-! # Ordered relocation of a completed scope into its ambient inventory

The overlap is the actual restriction of the ambient inventory. The ordered
union identifies precisely those occurrences, not cells with equal indices.
Scope separation proves that no new cell enters any earlier owner's lower
domain. This operation does not impose a grade bound on the ambient scheme.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrderedScopeRelocation
open AmalgamationPlan Transform Value ExtOrd
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}
variable {D : CellScheme A} (sem : Semantics D) (hB : B ∈ D.plan) {k : ℕ}
variable (S : OrdinaryScopeOperator.Core (ScopeBoundary.rows D B hB sem) k)

abbrev shared := ScopeBoundary.scheme D B hB
abbrev leftMap := (ScopeBoundary.toCell D B hB).toEmbedding
abbrev rightMap := S.original.toEmbedding
abbrev Occ := ProfileFaceUnion.Carrier (X := Cell D) (rightMap sem hB S)

def enumeration : Occ sem hB S ≃ Fin (Fintype.card (Occ sem hB S)) :=
  ProfileBoundaryOrder.enumeration (leftMap hB) (rightMap sem hB S)
    (ScopeBoundary.toCell D B hB).strictMono S.original.strictMono

def index : Occ sem hB S → Finset ι × ℕ :=
  ProfileFaceUnion.paste (rightMap sem hB S) D.cell S.carrier.cell

theorem index_left (d : Cell D) :
    index sem hB S (ProfileFaceUnion.left (rightMap sem hB S) d) = D.cell d := rfl

theorem index_right (d : Cell S.carrier) :
    index sem hB S (ProfileFaceUnion.right (leftMap hB) (rightMap sem hB S) d) =
      S.carrier.cell d :=
  ProfileFaceUnion.paste_right _ _ (fun c => (S.index c).symm) d

theorem index_mem (z : Occ sem hB S) : index sem hB S z ∈ Plan.gradedPlan D.plan := by
  rcases ProfileFaceUnion.covered (leftMap hB) (rightMap sem hB S) z with
    ⟨d, rfl⟩ | ⟨d, rfl⟩
  · exact D.cell_mem d
  · rw [index_right]
    obtain ⟨hp, hg, hc⟩ := Plan.mem_gradedPlan.mp (S.carrier.cell_mem d)
    rw [S.plan] at hp
    exact Plan.mem_gradedPlan.mpr ⟨(Finset.mem_inter.mp hp).1, hg, hc⟩

def carrier : CellScheme A where
  plan := D.plan
  isPlan := D.isPlan
  card := Fintype.card (Occ sem hB S)
  cell c := index sem hB S ((enumeration sem hB S).symm c)
  cell_mem _ := index_mem sem hB S _

def old (d : Cell D) : Cell (carrier sem hB S) :=
  enumeration sem hB S (ProfileFaceUnion.left (rightMap sem hB S) d)

def localCell (d : Cell S.carrier) : Cell (carrier sem hB S) :=
  enumeration sem hB S (ProfileFaceUnion.right (leftMap hB) (rightMap sem hB S) d)

theorem old_index (d : Cell D) : (carrier sem hB S).cell (old sem hB S d) = D.cell d := by
  change index sem hB S ((enumeration sem hB S).symm (enumeration sem hB S _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem local_index (d : Cell S.carrier) :
    (carrier sem hB S).cell (localCell sem hB S d) = S.carrier.cell d := by
  change index sem hB S ((enumeration sem hB S).symm (enumeration sem hB S _)) = _
  rw [Equiv.symm_apply_apply, index_right]

theorem old_order : StrictMono (old sem hB S) :=
  ProfileBoundaryOrder.enumeration_left _ _ _ _

theorem local_order : StrictMono (localCell sem hB S) :=
  ProfileBoundaryOrder.enumeration_right _ _ _ _

theorem shared_cell (c : Cell (shared hB)) :
    localCell sem hB S (S.original c) = old sem hB S (ScopeBoundary.toCell D B hB c) :=
  congrArg (enumeration sem hB S) (ProfileFaceUnion.right_shared _ _ c)

theorem covered (z : Cell (carrier sem hB S)) :
    (∃ d, old sem hB S d = z) ∨ ∃ e, localCell sem hB S e = z := by
  rcases ProfileFaceUnion.covered (leftMap hB) (rightMap sem hB S)
    ((enumeration sem hB S).symm z) with ⟨d, hd⟩ | ⟨e, he⟩
  · exact Or.inl ⟨d, (congrArg (enumeration sem hB S) hd).trans
      ((enumeration sem hB S).apply_symm_apply z)⟩
  · exact Or.inr ⟨e, (congrArg (enumeration sem hB S) he).trans
      ((enumeration sem hB S).apply_symm_apply z)⟩

theorem classify (z : Cell (carrier sem hB S)) :
    (∃ d, old sem hB S d = z) ∨ (carrier sem hB S).scope z = B := by
  rcases covered sem hB S z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · exact Or.inl ⟨d, rfl⟩
  · rcases S.coverage e with ⟨c, rfl⟩ | hc
    · exact Or.inl ⟨ScopeBoundary.toCell D B hB c, (shared_cell sem hB S c).symm⟩
    · exact Or.inr ((congrArg Prod.fst (local_index sem hB S e)).trans hc)

theorem local_exhaustive (z : Cell (carrier sem hB S))
    (hz : (carrier sem hB S).scope z ⊆ B) : ∃ e, localCell sem hB S e = z := by
  rcases covered sem hB S z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · change ((carrier sem hB S).cell (old sem hB S d)).1 ⊆ B at hz
    rw [old_index] at hz
    obtain ⟨c, rfl⟩ := ScopeBoundary.exhaustive D B hB hz
    exact ⟨S.original c, shared_cell sem hB S c⟩
  · exact ⟨e, rfl⟩

/-- Separation concerns scope containment, not a global bound on old grades. -/
def Separated : Prop := ∀ d : Cell D, ¬ B ⊆ D.scope d

variable (hsep : Separated (D := D) (B := B))

include hsep in
theorem old_exhaustive (c : Cell D) (z : Cell (carrier sem hB S))
    (hz : (carrier sem hB S).scope z ⊆ D.scope c) : ∃ d, old sem hB S d = z := by
  rcases classify sem hB S z with h | h
  · exact h
  · exact False.elim (hsep c (h ▸ hz))

def oldBelow (c : Cell D) :
    D.below (D.cell c) ≃ (carrier sem hB S).below ((carrier sem hB S).cell (old sem hB S c)) :=
  Equiv.ofBijective (fun d => ⟨old sem hB S d.1, by
    rw [old_index, old_index]; exact d.2⟩) ⟨by
      intro d e h
      exact Subtype.ext ((old_order sem hB S).injective (congrArg Subtype.val h)), by
      intro z
      have hz := z.2.1
      simp only [old_index] at hz
      obtain ⟨d, hd⟩ := old_exhaustive sem hB S hsep c z.1 hz
      refine ⟨⟨d, ?_⟩, Subtype.ext hd⟩
      have h := z.2
      simpa only [← hd, old_index] using h⟩

def localBelow (c : Cell S.carrier) :
    S.carrier.below (S.carrier.cell c) ≃
      (carrier sem hB S).below ((carrier sem hB S).cell (localCell sem hB S c)) :=
  Equiv.ofBijective (fun d => ⟨localCell sem hB S d.1, by
    rw [local_index, local_index]; exact d.2⟩) ⟨by
      intro d e h
      exact Subtype.ext ((local_order sem hB S).injective (congrArg Subtype.val h)), by
      intro z
      have hz := z.2.1
      simp only [local_index] at hz
      obtain ⟨d, hd⟩ := local_exhaustive sem hB S z.1
        (hz.trans (S.carrier.isPlan.subset_of_mem (S.carrier.scope_mem_plan c)))
      refine ⟨⟨d, ?_⟩, Subtype.ext hd⟩
      have h := z.2
      simpa only [← hd, local_index] using h⟩

open AmalgamatedBoundaryRows (total total_below pushRow pushRow_at pushRow_outside)

local notation "K" => carrier sem hB S
local notation "l" => old sem hB S
local notation "r" => localCell sem hB S

theorem total_shared (c d : Cell (shared hB)) :
    total sem (ScopeBoundary.toCell D B hB c) (ScopeBoundary.toCell D B hB d) =
      total S.rows (S.original c) (S.original d) := by
  classical
  by_cases hd : GradedLe ((shared hB).cell d) ((shared hB).cell c)
  · exact (total_below sem (ScopeBoundary.toCell D B hB c)
      ⟨ScopeBoundary.toCell D B hB d, hd⟩).trans
      ((S.row c ⟨d, hd⟩).symm.trans (total_below S.rows (S.original c)
        ⟨S.original d, by rw [S.index, S.index]; exact hd⟩).symm)
  · exact (AmalgamatedBoundaryRows.total_outside sem
      (ScopeBoundary.toCell D B hB c) (ScopeBoundary.toCell D B hB d) hd).trans
      (AmalgamatedBoundaryRows.total_outside S.rows (S.original c) (S.original d)
        (by simpa only [S.index] using hd)).symm

include hsep in
theorem pushRow_shared (c : Cell (shared hB)) :
    pushRow l sem (ScopeBoundary.toCell D B hB c) = pushRow r S.rows (S.original c) := by
  funext z
  by_cases hz : GradedLe ((K).cell z) (D.cell (ScopeBoundary.toCell D B hB c))
  · have hzl : GradedLe ((K).cell z) ((K).cell (l (ScopeBoundary.toCell D B hB c))) := by
      rw [old_index]; exact hz
    obtain ⟨d, hd⟩ := (oldBelow sem hB S hsep (ScopeBoundary.toCell D B hB c)).surjective
      ⟨z, hzl⟩
    have he : l d.1 = z := congrArg Subtype.val hd
    obtain ⟨e, he'⟩ := ScopeBoundary.exhaustive D B hB
      (d.2.1.trans (ScopeBoundary.scope_bound D B hB c))
    rw [← he, ← he', pushRow_at l (old_order sem hB S).injective,
      ← shared_cell, pushRow_at r (local_order sem hB S).injective]
    exact total_shared sem hB S c e
  · rw [pushRow_outside l (old_order sem hB S).injective (old_index sem hB S) sem _ _ hz,
      pushRow_outside r (local_order sem hB S).injective (local_index sem hB S) S.rows]
    simpa only [S.index, ScopeBoundary.cell_eq] using hz

def table (c : Cell K) : Cell K → ExtOrd :=
  ProfileFaceUnion.paste (rightMap sem hB S) (pushRow l sem) (pushRow r S.rows)
    ((enumeration sem hB S).symm c)

theorem table_old (c d : Cell D) : table sem hB S (l c) (l d) = total sem c d := by
  change ProfileFaceUnion.paste _ (pushRow l sem) (pushRow r S.rows) ((enumeration sem hB S).symm
    (enumeration sem hB S (ProfileFaceUnion.left _ c))) (l d) = _
  rw [Equiv.symm_apply_apply]
  exact pushRow_at l (old_order sem hB S).injective sem c d

include hsep in
theorem table_local (c d : Cell S.carrier) :
    table sem hB S (r c) (r d) = total S.rows c d := by
  change ProfileFaceUnion.paste _ (pushRow l sem) (pushRow r S.rows) ((enumeration sem hB S).symm
    (enumeration sem hB S (ProfileFaceUnion.right (leftMap hB) _ c))) (r d) = _
  rw [Equiv.symm_apply_apply, ProfileFaceUnion.paste_right _ _
    (pushRow_shared sem hB S hsep)]
  exact pushRow_at r (local_order sem hB S).injective S.rows c d

include hsep in
theorem table_orderly (c : Cell K) (d : (K).below ((K).cell c)) :
    table sem hB S c d.1 = extVisibilityReplace (table sem hB S c d.1)
      ((K).grade d.1) ((K).grade d.1) := by
  rcases covered sem hB S c with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
    change table sem hB S (l c) (l e.1) =
      extVisibilityReplace (table sem hB S (l c) (l e.1)) ((K).cell (l e.1)).2 ((K).cell (l e.1)).2
    rw [table_old, total_below, old_index]
    exact sem.orderly c e
  · obtain ⟨e, rfl⟩ := (localBelow sem hB S c).surjective d
    change table sem hB S (r c) (r e.1) =
      extVisibilityReplace (table sem hB S (r c) (r e.1)) ((K).cell (r e.1)).2 ((K).cell (r e.1)).2
    rw [table_local sem hB S hsep, total_below, local_index]
    exact S.rows.orderly c e

def rows : Semantics K where
  E c d := table sem hB S c d.1
  orderly := table_orderly sem hB S hsep

theorem row_old (c : Cell D) (d : D.below (D.cell c)) :
    (rows sem hB S hsep).E (l c) (oldBelow sem hB S hsep c d) = sem.E c d :=
  (table_old sem hB S c d.1).trans (total_below sem c d)

theorem row_local (c : Cell S.carrier) (d : S.carrier.below (S.carrier.cell c)) :
    (rows sem hB S hsep).E (r c) (localBelow sem hB S c d) = S.rows.E c d :=
  (table_local sem hB S hsep c d.1).trans (total_below S.rows c d)

/-- The completed scope is an exact semantic face of the installed carrier. -/
def localFace : ExactSemanticFace S.rows (rows sem hB S hsep) where
  map := ⟨r, (local_order sem hB S).injective⟩
  index := local_index sem hB S
  exhaustive := local_exhaustive sem hB S
  row := row_local sem hB S hsep

theorem consistent (hc : sem.IsConsistent) : (rows sem hB S hsep).IsConsistent := by
  intro z
  rcases covered sem hB S z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have h := respects_iff_of_equiv (sem' := sem) (sem := rows sem hB S hsep)
      (oldBelow sem hB S hsep c) (fun d => (congrArg Prod.snd (old_index sem hB S d.1)).symm)
      (fun d e => ?_) (fun c d hd => ?_) (sem.E c)
    · have he : sem.E c ∘ (oldBelow sem hB S hsep c).symm =
          (rows sem hB S hsep).E (l c) := by
        funext d
        obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
        simp only [Function.comp_apply, Equiv.symm_apply_apply]
        exact (row_old sem hB S hsep c e).symm
      rw [he] at h
      exact h.mp (hc c)
    · change D.scope d.1 ⊆ D.scope e.1 ↔ ((K).cell (l d.1)).1 ⊆ ((K).cell (l e.1)).1
      rw [old_index, old_index]; rfl
    · exact (row_old sem hB S hsep c.1 d).symm
  · exact (localFace sem hB S hsep).consistent_at S.consistent c

theorem coded (hc : sem.IsCoded) : (rows sem hB S hsep).IsCoded := by
  intro z d
  rcases covered sem hB S z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
    change IsCodedLabel ((K).cell (l c)).2 ((rows sem hB S hsep).E (l c) _)
    rw [row_old, old_index]
    exact hc c e
  · exact (localFace sem hB S hsep).coded_at S.coded c d

end
end VaughtConjecture.Knight.OrderedScopeRelocation
