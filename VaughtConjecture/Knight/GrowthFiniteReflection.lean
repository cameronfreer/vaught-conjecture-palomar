/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthNormalization
public import VaughtConjecture.Knight.SupportLadderBottomReflection

/-! # Growth admission under finite complete-profile reflection

Adapted from the oracle's growth2 candidate (gr2, section 3.3).
A local chart need only reflect bottom on the complete source vector.
No reflection outside its represented values is assumed. This supplies
admission transport once a physical chart has established those receipts;
it does not construct that chart or prove mixed-scope lawfulness.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.Growth
open Transform Value ExtOrd AmalgamationPlan CappedDonor.Ref SharpWitnessComposition
noncomputable section
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

/-- Finite reflection on the complete source vector suffices. No global
bottom-reflection property is asserted of the actual local chart. -/
theorem Admitted.map_on_profile {j : ℕ} {S : State DA DQ} (hS : Admitted X j S)
    {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop j) σ) (hj : 1 ≤ j)
    (hbot : ∀ f : Field DA DQ, σ (S.profile f) = ⊥ → S.profile f = ⊥) : Admitted X j (S.map σ) where
  private_lawful := map_respects_of_bottom_reflection hS.private_lawful
    (fun d => d.2.2) (boundedMap_of_witness hσ) (fun d => by
      constructor
      · exact hbot (.inl d.1)
      · intro hz; rw [hz, hσ.bot])
  donor_lawful := map_respects_of_bottom_reflection hS.donor_lawful
    (fun d => d.2.2) (boundedMap_of_witness hσ) (fun d => by
      constructor
      · exact hbot (.inr d.1)
      · intro hz; rw [hz, hσ.bot])
  visible f := by
    rw [State.profile_map]
    exact selfVis_map hσ hj (hS.visible f)
  shared d := congrArg σ (hS.shared d)
  correct hN hc := by
    have hc' : InClass X.ZA S.privateValues := by
      intro d
      constructor
      · intro hd
        apply (hc d).mp
        change σ (S.privateValues d.1) = ⊥
        rw [hd, hσ.bot]
      · intro hd
        exact hbot (.inl d.1) ((hc d).mpr hd)
    obtain ⟨hz, hf, ht⟩ := hS.correct hN hc'
    refine ⟨?_, ?_, ?_⟩
    · intro z hZ
      change min (σ (S.donorValues z)) (σ (S.privateValues X.req.C)) = ⊥
      rw [← hσ.mono.map_min]
      exact (congrArg σ (hz z hZ)).trans hσ.bot
    · intro f hF
      change min (σ (S.donorValues f)) (σ (S.privateValues X.req.C)) =
        min (extVisibilityReplace (σ (S.privateValues (X.req.ρ f).1)) X.req.N
          (X.req.off f)) (σ (S.privateValues X.req.C))
      rw [← map_comm hσ hN _ (X.off_lt f hF), ← hσ.mono.map_min,
        ← hσ.mono.map_min]
      exact congrArg σ (hf f hF)
    · intro y hT
      change min (extVisibilityReplace (σ (S.privateValues X.req.a.1)) X.req.N X.req.R)
        (σ (S.privateValues X.req.C)) ≤
        min (σ (S.donorValues y)) (σ (S.privateValues X.req.C))
      rw [← map_comm hσ hN _ X.req.R_lt_N.le, ← hσ.mono.map_min,
        ← hσ.mono.map_min]
      exact hσ.mono (ht y hT)

end
end VaughtConjecture.Knight.Growth
