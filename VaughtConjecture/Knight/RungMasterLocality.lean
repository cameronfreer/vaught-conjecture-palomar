/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RecursiveRungRendering

/-! # Long-rung charts including every original field

The fixed master row includes the complete field vector as well as every base
rung. Its locality is constructed from the rank table, without shortness of
the long diagonal or a catalogue anchor for the rendered profile. Actual field
grades and scope restrictions can subsequently restrict these exact readings.
This does not install a cell scheme or prove original-owner lawfulness.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.RungMasterLocality
open Transform Value ExtOrd LadderScalarRendering
open RecursiveRungRendering
noncomputable section
variable {X B : Type*} [Fintype X]

abbrev Master (X B : Type*) [Fintype X] := X ⊕ Base X B

def index (ranks : B → X → ℕ) (r : X → ℕ) : Master X B → ℕ
  | .inl d => r d
  | .inr v => min (FiniteProfileControllers.cut (height X) r (ranks v.1)) (v.2.val + 1)

def row (ranks : B → X → ℕ) (c : Base X B) (d : Master X B) : ExtOrd :=
  SupportLadderRows.source (c.2.val + 1) (index ranks (ranks c.1) d)

def table (ranks : B → X → ℕ) (p : X → ExtOrd) (C : ExtOrd) : Master X B → ExtOrd :=
  Sum.elim p (RungTableRendering.render ranks p C)

theorem index_agreement (ranks : B → X → ℕ) (r s : X → ℕ) (d : Master X B) :
    min (index ranks r d) (FiniteProfileControllers.cut (height X) r s) =
      min (index ranks s d) (FiniteProfileControllers.cut (height X) r s) := by
  cases d with
  | inl d => exact FiniteProfileControllers.agree_cut _ _ _ d
  | inr v =>
    have h := FiniteProfileControllers.cross_agreement (height X) r s (ranks v.1)
    dsimp only [index]
    omega

theorem table_eq_level (ranks : B → X → ℕ) (p : X → ExtOrd) (C : ExtOrd)
    (d : Master X B) :
    table ranks p C d = LadderScalarRendering.level (values p) C (index ranks (fieldRank p) d) := by
  cases d with
  | inl d => exact (field_readback p C d).symm
  | inr v => rfl

/-- The interpolation includes the old field columns, not just rung columns. -/
theorem locality [Finite B] (ranks : B → X → ℕ) (c : Base X B)
    {p : X → ExtOrd} {C : ExtOrd} (hp : ∀ d, SelfVis 1 (p d))
    (hC : SelfVis 1 C) (hb : ∀ d, p d ≤ C) :
    TransformsTo (fun _ : Master X B => 1) (row ranks c)
      (fun d => min (table ranks p C d) (table ranks p C (.inr c))) := by
  let f := LadderScalarRendering.level (values p) C
  have hf : Monotone f := level_mono (values_bound hb)
  let e := index ranks (fieldRank p) (.inr c)
  have he : e ≤ c.2.val + 1 := min_le_right _ _
  have ht (d : Master X B) :
      min (table ranks p C d) (table ranks p C (.inr c)) =
        f (min (index ranks (ranks c.1) d) e) := by
    rw [table_eq_level, table_eq_level, ← hf.map_min]
    apply congrArg f
    have ha := index_agreement ranks (fieldRank p) (ranks c.1) d
    change min (index ranks (fieldRank p) d)
      (min (FiniteProfileControllers.cut (height X) (fieldRank p) (ranks c.1))
        (c.2.val + 1)) = _
    change min (index ranks (fieldRank p) d)
      (min (FiniteProfileControllers.cut (height X) (fieldRank p) (ranks c.1))
        (c.2.val + 1)) =
      min (index ranks (ranks c.1) d)
        (min (FiniteProfileControllers.cut (height X) (fieldRank p) (ranks c.1))
          (c.2.val + 1))
    omega
  rw [funext ht]
  by_cases hzero : C = ⊥
  · have hz : ∀ i, f i = ⊥ := fun i => le_bot_iff.mp ((level_le (values_bound hb) i).trans_eq hzero)
    simp only [hz]
    exact TransformsTo.to_bot _
  by_cases hezero : e = 0
  · simp only [hezero, Nat.min_zero, show f 0 = ⊥ from level_zero _ _]
    exact TransformsTo.to_bot _
  have hlocal := SupportLadderRows.transforms_positive
    (index ranks (ranks c.1)) (c.2.val + 1) (fun i => f (min i e))
    (fun _ _ h => hf (min_le_min_right _ h))
    (by simpa only [Nat.zero_min] using level_zero (values p) C)
    (fun i => level_visible hp hC _)
    (fun i hi _ => level_pos (bot_not_values p) (values_bound hb) hzero (by omega))
  unfold row
  convert hlocal using 1
  funext d
  rw [min_assoc, min_eq_right he]

/-- A faithful normalized chart is available at the actual capped rung value. -/
theorem exists_chart [Finite B] (ranks : B → X → ℕ) (c : Base X B)
    {p : X → ExtOrd} {C : ExtOrd} (hp : ∀ d, SelfVis 1 (p d))
    (hC : SelfVis 1 C) (hb : ∀ d, p d ≤ C) :
    ∃ σ : ExtOrd → ExtOrd, Witness (gTop 1) σ ∧
      (∀ x, σ x ≤ table ranks p C (.inr c)) ∧
      ∀ d, σ (row ranks c d) = min (table ranks p C d) (table ranks p C (.inr c)) := by
  apply exists_bounded_exact_capped_witness (grade := fun _ : Master X B => 1)
    (c := .inr c) (fun _ => le_rfl) _ (locality ranks c hp hC hb)
  rw [table_eq_level]
  exact level_visible hp hC _

end
end VaughtConjecture.Knight.RungMasterLocality
