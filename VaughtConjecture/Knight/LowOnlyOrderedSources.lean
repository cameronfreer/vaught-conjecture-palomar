/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyOrderedLadder
public import VaughtConjecture.Knight.LowOnlyRecursiveCoverage

/-! # LOW source lawfulness on the ordered boundary at every cutoff

The literal two-face paste is lawful on the currently present lower set.
Zero padding is only an auxiliary proof of this fact; future source fields
are unchanged. In particular this does not promote a lower admitted state
to a higher cutoff.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyOrderedSources
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)

include hroot in
theorem boundary_lawful_at (j : ℕ) (S : State I.left I.right) (hs : F.Admissible j S) :
    RespectsSemanticsBelow I.rows (A, j) (fun d => S.profile (field I d.1)) := by
  let u := CellScheme.zeroAbove (S.lowerP j)
  let v := CellScheme.zeroAbove (S.lowerC j)
  have hshared (i : Cell I.common.scheme) : u (I.shared.f i) = v (I.shared.g i) := by
    have hg : I.left.scheme.grade (I.shared.f i) = I.right.scheme.grade (I.shared.g i) :=
      congrArg (fun x : Finset ι × ℕ => x.2) (I.shared.shared i)
    by_cases hd : I.left.scheme.grade (I.shared.f i) ≤ min j n
    · have he : I.right.scheme.grade (I.shared.g i) ≤ min j n := hg ▸ hd
      rw [show u (I.shared.f i) = S.u (I.shared.f i) from
        CellScheme.zeroAbove_low (S.lowerP j) ⟨_, Finset.subset_univ _, hd⟩,
        show v (I.shared.g i) = S.v (I.shared.g i) from
        CellScheme.zeroAbove_low (S.lowerC j) ⟨_, Finset.subset_univ _, he⟩]
      exact shared I F hroot hs.shared i
    · have he : ¬ I.right.scheme.grade (I.shared.g i) ≤ min j n := hg ▸ hd
      exact (CellScheme.zeroAbove_high (S.lowerP j) hd).trans
        (CellScheme.zeroAbove_high (S.lowerC j) he).symm
  have hl := (I.paste_respects hs.lawfulP.zeroAbove hs.lawfulC.zeroAbove hshared).toBelow (A, j)
  have he : (fun d : I.boundary.below (A, j) => S.profile (field I d.1)) =
      (fun d => I.paste u v d.1) := by
    funext d
    rw [field_read]
    rcases OrderedFaceBoundaryRows.covered I.leftScheme I.rightScheme I.shared R I.isPlan
        I.leftPlan_le I.rightPlan_le d.1 with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hi := d.2.2
      change I.boundary.grade d.1 ≤ j at hi
      rw [← hc] at hi
      have hgrade := congrArg Prod.snd (I.leftFace.index c)
      change I.boundary.grade (I.leftFace.map c) = I.left.scheme.grade c at hgrade
      have hg : I.left.scheme.grade c ≤ min j n :=
        le_min (hgrade.symm ▸ hi) (gradeC_le c)
      rw [← hc]
      change I.paste S.u S.v (I.leftFace.map c) = I.paste u v (I.leftFace.map c)
      exact (I.paste_left S.u S.v c).trans
        ((CellScheme.zeroAbove_low (S.lowerP j) ⟨c, Finset.subset_univ _, hg⟩).symm.trans
          (I.paste_left u v c).symm)
    · have hi := d.2.2
      change I.boundary.grade d.1 ≤ j at hi
      rw [← hc] at hi
      have hgrade := congrArg Prod.snd (I.rightFace.index c)
      change I.boundary.grade (I.rightFace.map c) = I.right.scheme.grade c at hgrade
      have hg : I.right.scheme.grade c ≤ min j n :=
        le_min (hgrade.symm ▸ hi) (gradeC_le c)
      rw [← hc]
      change I.paste S.u S.v (I.rightFace.map c) = I.paste u v (I.rightFace.map c)
      exact (I.paste_right S.u S.v (shared I F hroot hs.shared) c).trans
        ((CellScheme.zeroAbove_low (S.lowerC j) ⟨c, Finset.subset_univ _, hg⟩).symm.trans
          (I.paste_right u v hshared c).symm)
  exact he ▸ hl

include hroot in
theorem anchor_lawful (j : ℕ) (a : F.Anchor j) :
    RespectsSemanticsBelow I.rows (A, j) (fun d => F.fields j a (field I d.1)) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  have hv : (fun d : I.boundary.below (A, j) => F.fields j a (field I d.1)) =
      (fun d => S.profile (field I d.1)) := funext (fun d => (congrFun he _).symm)
  exact hv ▸ boundary_lawful_at I F hroot j S hS

end
end VaughtConjecture.Knight.LowOnlyOrderedSources
