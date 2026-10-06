/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RecursiveRungLocality
public import VaughtConjecture.Knight.LowOnlyLadderRepair

/-! # Recursive auxiliary charts for the actual LOW catalogues

Every source grade uses its own finite admitted catalogue. Canonical membership
supplies properness, bounds and native shortness; present-cell lawfulness and
future visibility supply grade-one visibility on the complete field vector.
Thus the recursive charts specialize without an abstract source-row contract.

This is numerical auxiliary locality, not original-owner lawfulness or an
installed scope geometry. It neither promotes admission to a higher cutoff nor
asserts equality of renderings made at different construction grades.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyRecursiveCharts
open Transform Value ExtOrd CappedDonor LowOnly
open PairedSlotEncoding RecursiveRungRendering RecursiveRungLocality
open SharpWitnessComposition
noncomputable section
variable {m K : ℕ} {P C : SemScheme m} (F : LowOnly.Family P C K)

private theorem lower_visible_one {D : SemScheme m} {j : ℕ}
    {v : Cell D.scheme → ExtOrd}
    (hv : RespectsSemanticsBelow D.rows (effC m j) (fun d => v d.1))
    (hf : ∀ d, j < D.scheme.grade d → SelfVis 1 (v d)) (d : Cell D.scheme) :
    SelfVis 1 (v d) := by
  by_cases hd : D.scheme.grade d ≤ j
  · let d' : D.scheme.below (effC m j) :=
      ⟨d, Finset.subset_univ _, le_min hd (gradeC_le d)⟩
    exact selfVis_mono (hv.orderly d').symm (D.scheme.grade_pos d)
  · exact hf d (Nat.lt_of_not_ge hd)

/-- Future fields and the free cutoff are covered too. -/
theorem profile_visible_one {j : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) (d : Field P C) : SelfVis 1 (S.profile d) := by
  rcases d with d | d | d
  · exact lower_visible_one hS.lawfulP hS.futureP d
  · exact lower_visible_one hS.lawfulC hS.futureC d
  · exact selfVis_mono hS.cutoff (le_min hj F.gap.K_pos)

def ranks (a : F.Anchor 1) : Field P C → ℕ :=
  LadderScalarRendering.fieldRank (F.fields 1 a)

theorem anchor_proper {j : ℕ} (a : F.Anchor j) (d : Field P C) :
    F.fields j a d ≠ ⊤ := a.property.1.2 d

theorem anchor_bound {j : ℕ} (a : F.Anchor j) (d : Field P C) :
    F.fields j a d ≤ ceiling (Field P C) j := by
  apply (CanonicalPairedProfiles.inventory_bound _ _ a.property.1 d).trans
  exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr; omega) le_rfl)

theorem anchor_short {j : ℕ} (a : F.Anchor j) (d : Field P C) :
    Short j (F.fields j a d) :=
  CanonicalPairedProfiles.inventory_short _ _ a.property.1 d

theorem anchor_visible_one {j : ℕ} (hj : 1 ≤ j) (a : F.Anchor j) (d : Field P C) :
    SelfVis 1 (F.fields j a d) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  change SelfVis 1 (a.val d)
  rw [← he]
  exact profile_visible_one F hj hS d

/-- All higher catalogue leaves, at every later rendering stage. The source
assumptions in the generic chart theorem are discharged by actual membership. -/
theorem leaf_chart (n t : ℕ) (a : F.Anchor (n + 2))
    (p : F.Anchor (n + t + 2)) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop (n + 2)) τ ∧
      ∀ d : Point (Field P C) (F.Anchor 1) F.Anchor (n + 1),
        τ (raw (ranks F) F.fields n (F.fields (n + 2) a) d) =
          min (render (ranks F) F.fields (n + 1 + t) (F.fields (n + t + 2) p)
            (grid (Field P C) (n + t + 2)) (ceiling (Field P C) (n + t + 2)) (raise t d))
            (render (ranks F) F.fields (n + 1 + t) (F.fields (n + t + 2) p)
              (grid (Field P C) (n + t + 2)) (ceiling (Field P C) (n + t + 2))
                (raise t (.inr (.inr a)))) :=
  inherited_leaf_chart (ranks F) F.fields n t a
    (anchor_proper F a) (anchor_bound F a) (anchor_short F a)
    (anchor_proper F p) (fun _ hz => PairedSlotComparison.sourceGrid_visible hz)
    (PairedSlotComparison.sourceGrid_visible (PairedSlotComparison.sourceGrid_endpoint le_rfl))

/-- Native long-rung rows read every admitted source at every later grade. -/
theorem rung_chart (n : ℕ) (c : Base (Field P C) (F.Anchor 1)) (p : F.Anchor (n + 1)) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop 1) τ ∧
      ∀ d : RungMasterLocality.Master (Field P C) (F.Anchor 1),
        τ (RungMasterLocality.row (ranks F) c d) =
          min (render (ranks F) F.fields n (F.fields (n + 1) p)
            (grid (Field P C) (n + 1)) (ceiling (Field P C) (n + 1)) (basePoint n d))
            (render (ranks F) F.fields n (F.fields (n + 1) p)
              (grid (Field P C) (n + 1)) (ceiling (Field P C) (n + 1))
                (basePoint n (.inr c))) :=
  inherited_rung_chart (ranks F) F.fields n c
    (anchor_proper F p) (anchor_visible_one F (by omega) p)
    (fun _ hz => PairedSlotComparison.sourceGrid_visible hz)
    (PairedSlotComparison.sourceGrid_visible (PairedSlotComparison.sourceGrid_endpoint le_rfl))
    (anchor_bound F p)

end
end VaughtConjecture.Knight.LowOnlyRecursiveCharts
