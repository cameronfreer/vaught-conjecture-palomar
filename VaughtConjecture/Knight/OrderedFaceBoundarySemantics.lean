/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrderedFaceBoundaryRows
public import VaughtConjecture.Knight.ExactSemanticFace

/-! # Lawful pasting on two arbitrary exact ordered faces

Generalizes `AmalgamatedBoundarySemantics` beyond coatom geometry.
The constructed inherited boundary is coded and consistent when both inputs are.
A boundary labelling is lawful exactly when both literal face restrictions are.
Compatible lawful inputs therefore have a unique lawful boundary paste.

No completeness or lifting at new mixed indices is asserted. The boundary has no
new owners; it is not packaged as a legal receiving scheme.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.OrderedFaceBoundarySemantics

open AmalgamationPlan OrderedFaceBoundary OrderedFaceBoundaryRows
open AmalgamatedBoundary (Overlap)
open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
variable (D : CellScheme B) (E : CellScheme C)
variable {k : ℕ} (w : Overlap D E k)
variable (R : Finset (Finset ι)) (hR : Plan.IsPlan A R)
variable (hD : D.plan ⊆ R) (hE : E.plan ⊆ R)
variable (semD : Semantics D) (semE : Semantics E)
variable (hc : Compatible D E w semD semE)

local notation "K" => scheme D E w R hR hD hE
local notation "l" => leftCell D E w R hR hD hE
local notation "r" => rightCell D E w R hR hD hE
local notation "sem" => rows D E w R hR hD hE semD semE hc

noncomputable def leftFace : ExactSemanticFace semD sem where
  map := ⟨l, (left_order D E w R hR hD hE).injective⟩
  index := left_index D E w R hR hD hE
  exhaustive := left_exhaustive D E w R hR hD hE
  row := rows_left D E w R hR hD hE semD semE hc

noncomputable def rightFace : ExactSemanticFace semE sem where
  map := ⟨r, (right_order D E w R hR hD hE).injective⟩
  index := right_index D E w R hR hD hE
  exhaustive := right_exhaustive D E w R hR hD hE
  row := rows_right D E w R hR hD hE semD semE hc

theorem consistent (hd : semD.IsConsistent) (he : semE.IsConsistent) : (sem).IsConsistent := by
  intro c
  rcases covered D E w R hR hD hE c with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (leftFace D E w R hR hD hE semD semE hc).consistent_at hd c
  · exact (rightFace D E w R hR hD hE semD semE hc).consistent_at he c

theorem coded (hd : semD.IsCoded) (he : semE.IsCoded) : (sem).IsCoded := by
  intro c d
  rcases covered D E w R hR hD hE c with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (leftFace D E w R hR hD hE semD semE hc).coded_at hd c d
  · exact (rightFace D E w R hR hD hE semD semE hc).coded_at he c d

/-- There are no additional cross-face lawfulness conditions on the proper
boundary: every locality and availability target is inherited. -/
theorem respects_iff (p : Cell K → ExtOrd) : RespectsSemantics sem p ↔
    RespectsSemantics semD (p ∘ l) ∧ RespectsSemantics semE (p ∘ r) := by
  constructor
  · intro hp
    exact ⟨(leftFace D E w R hR hD hE semD semE hc).restrict hp,
      (rightFace D E w R hR hD hE semD semE hc).restrict hp⟩
  · rintro ⟨hpD, hpE⟩
    constructor
    · intro c
      rcases covered D E w R hR hD hE c with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change p (l c) = extVisibilityReplace (p (l c))
          ((K).cell (l c)).2 ((K).cell (l c)).2
        rw [left_index]
        exact hpD.orderly c
      · change p (r c) = extVisibilityReplace (p (r c))
          ((K).cell (r c)).2 ((K).cell (r c)).2
        rw [right_index]
        exact hpE.orderly c
    · intro c
      rcases covered D E w R hR hD hE c with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact (leftFace D E w R hR hD hE semD semE hc).locality_of_restrict hpD c
      · exact (rightFace D E w R hR hD hE semD semE hc).locality_of_restrict hpE c
    · intro c e hs hg
      rcases covered D E w R hR hD hE e with ⟨e, rfl⟩ | ⟨e, rfl⟩
      · exact (leftFace D E w R hR hD hE semD semE hc).availability_at hpD c e hs hg
      · exact (rightFace D E w R hR hD hE semD semE hc).availability_at hpE c e hs hg

noncomputable def paste (p : Cell D → ExtOrd) (q : Cell E → ExtOrd) : Cell K → ExtOrd :=
  ProfileFaceUnion.paste w.g p q ∘ (enumeration D E w).symm

theorem paste_left (p : Cell D → ExtOrd) (q : Cell E → ExtOrd) (d : Cell D) :
    paste D E w R hR hD hE p q (l d) = p d := by
  change ProfileFaceUnion.paste w.g p q ((enumeration D E w).symm
    (enumeration D E w (ProfileFaceUnion.left w.g d))) = p d
  rw [Equiv.symm_apply_apply]
  rfl

theorem paste_right (p : Cell D → ExtOrd) (q : Cell E → ExtOrd)
    (h : ∀ i, p (w.f i) = q (w.g i)) (e : Cell E) :
    paste D E w R hR hD hE p q (r e) = q e := by
  change ProfileFaceUnion.paste w.g p q ((enumeration D E w).symm
    (enumeration D E w (ProfileFaceUnion.right w.f w.g e))) = q e
  rw [Equiv.symm_apply_apply]
  exact ProfileFaceUnion.paste_right w.f w.g h e

theorem paste_respects {p : Cell D → ExtOrd} {q : Cell E → ExtOrd}
    (hp : RespectsSemantics semD p) (hq : RespectsSemantics semE q)
    (h : ∀ i, p (w.f i) = q (w.g i)) :
    RespectsSemantics sem (paste D E w R hR hD hE p q) := by
  apply (respects_iff D E w R hR hD hE semD semE hc _).mpr
  constructor
  · simpa only [Function.comp_def, paste_left] using hp
  · simpa only [Function.comp_def, paste_right D E w R hR hD hE p q h] using hq

/-- Two whole faces have a lawful simultaneous boundary section exactly
when every shared label agrees. No common whole completion is assumed. -/
theorem section_iff {p : Cell D → ExtOrd} {q : Cell E → ExtOrd}
    (hp : RespectsSemantics semD p) (hq : RespectsSemantics semE q) :
    (∃ t, RespectsSemantics sem t ∧ (∀ d, t (l d) = p d) ∧ ∀ e, t (r e) = q e) ↔
      ∀ i, p (w.f i) = q (w.g i) := by
  constructor
  · rintro ⟨t, _, hl, hr⟩ i
    exact (hl _).symm.trans ((congrArg t (shared_cell D E w R hR hD hE i)).trans (hr _))
  · intro h
    exact ⟨paste D E w R hR hD hE p q,
      paste_respects D E w R hR hD hE semD semE hc hp hq h,
      paste_left D E w R hR hD hE p q, paste_right D E w R hR hD hE p q h⟩

theorem section_unique {p q : Cell K → ExtOrd}
    (hl : ∀ d, p (l d) = q (l d)) (hr : ∀ e, p (r e) = q (r e)) : p = q := by
  funext c
  rcases covered D E w R hR hD hE c with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · exact hl d
  · exact hr e

end VaughtConjecture.Knight.OrderedFaceBoundarySemantics
