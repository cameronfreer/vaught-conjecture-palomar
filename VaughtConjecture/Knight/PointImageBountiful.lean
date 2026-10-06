/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PointImageSemantics
public import VaughtConjecture.Knight.PartialSections

/-! # Bountifulness under an injective change of point domain

Both lower domains retain the same occurrences and source values. The
original cap and arbitrary target-local ambient transport literally.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.PointImageSemantics

open AmalgamationPlan Transform Value ExtOrd AmalgamatedBoundary

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {B : Finset ι} {C : Finset κ} (D : CellScheme B) (e : ι ↪ κ)
variable (he : B.image e = C) (sem : Semantics D)

local notation "K" => pointImage D e he

theorem respects_owner_iff (c : Cell D) (q : (K).below ((K).cell c) → ExtOrd) :
    RespectsSemanticsBelow (rows D e he sem) ((K).cell c) q ↔
      RespectsSemanticsBelow sem (D.cell c) (q ∘ belowEquiv D e he c) :=
  respects_iff_of_equiv (belowEquiv D e he c).symm (fun _ => rfl)
    (fun _ _ => Finset.image_subset_image_iff e.injective) (fun _ _ _ => rfl) q

theorem bountiful (hD : D.IsComplete) (hb : sem.IsBountiful) :
    (rows D e he sem).IsBountiful := by
  intro CI BJ hCI hBJ h hne p a γ hp ha hγ hag
  obtain ⟨c, hc⟩ := pointImage_complete D e he hD CI hCI
  obtain ⟨d, hd⟩ := pointImage_complete D e he hD BJ hBJ
  cases hc
  cases hd
  have h' := (below_iff D e he c d).mp h
  have hne' : D.cell c ≠ D.cell d := by
    intro heq
    exact hne (congrArg (fun z : Finset ι × ℕ => (z.1.image e, z.2)) heq)
  exact bountiful_of_equiv (sem' := rows D e he sem) (sem := sem) h h'
    (belowEquiv D e he d).symm (belowEquiv D e he c).symm (fun _ => rfl)
    (respects_owner_iff D e he sem d) (respects_owner_iff D e he sem c)
    (hb (D.cell c) (D.cell d) (D.cell_mem c) (D.cell_mem d) h' hne') rfl
    p a γ hp ha hγ hag

end VaughtConjecture.Knight.PointImageSemantics
