/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthCompleteFields
public import VaughtConjecture.Knight.CappedDonorNormalization
public import VaughtConjecture.Knight.CanonicalPairedProfiles

/-! # Current-grade normalization of complete growth fields

This uses the growth request relation, not LOW or its private surgery. Future
fields are normalized together with present fields. Admission goes downward;
there is no assertion that an earlier source survives later activation.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.Growth
open Transform Value ExtOrd AmalgamationPlan CappedDonor.Ref SharpWitnessComposition
noncomputable section
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}

namespace State
def encoder (j : ℕ) (S : State DA DQ) : ExtOrd → ExtOrd :=
  PairedSlotIncoming.encoder j (PairedSlotEncoding.values S.profile)

def normalize (j : ℕ) (S : State DA DQ) : State DA DQ := S.map (S.encoder j)

theorem profile_normalize (j : ℕ) (S : State DA DQ) (f : Field DA DQ) :
    (S.normalize j).profile f = PairedSlotEncoding.normalize j S.profile f := by
  rw [normalize, profile_map]
  exact PairedSlotIncoming.encoder_profile j S.profile f
end State

variable (X : RelativeData DA semA DQ semQ)

theorem Admitted.map {j : ℕ} {S : State DA DQ} (hS : Admitted X j S)
    {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop j) σ) (hj : 1 ≤ j)
    (hbot : ∀ x, σ x = ⊥ → x = ⊥) : Admitted X j (S.map σ) where
  private_lawful := map_respects_of_bottom_reflecting hS.private_lawful
    (fun d => d.2.2) (boundedMap_of_witness hσ) hbot
  donor_lawful := map_respects_of_bottom_reflecting hS.donor_lawful
    (fun d => d.2.2) (boundedMap_of_witness hσ) hbot
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
        exact hbot _ ((hc d).mpr hd)
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

theorem normalize_admitted {j : ℕ} (hj : 1 ≤ j) {S : State DA DQ}
    (hS : Admitted X j S) : Admitted X j (S.normalize j) :=
  hS.map X (PairedSlotIncoming.encoder_witness j _) hj
    (PairedSlotIncoming.encoder_reflects_bottom j _)

theorem normalize_inventory (j : ℕ) {S : State DA DQ} (hp : ∀ f, S.profile f ≠ ⊤) :
    (S.normalize j).profile ∈ CanonicalPairedProfiles.inventory (Field DA DQ) j := by
  rw [show (S.normalize j).profile = PairedSlotEncoding.normalize j S.profile from
    funext (State.profile_normalize j S)]
  exact CanonicalPairedProfiles.normalize_mem_inventory _ _ hp

theorem normalize_caps {j B : ℕ} {S T : State DA DQ}
    (hS : S.profile ∈ CanonicalPairedProfiles.inventory (Field DA DQ) j)
    (hcap : S.CapEq (ofOrd (Ordinal.omega0 * B + j)) T) :
    S.CapEq (ofOrd (Ordinal.omega0 * B + j)) (T.normalize j) := by
  intro f
  rw [State.profile_normalize]
  exact CanonicalPairedProfiles.normalize_cap _ _ hS (fun f => (hcap f).symm) f

/-- The fixed catalogue is the whole canonical admitted family, before any
lifting request. It does not depend on a proposed replacement. -/
def Catalogue (j : ℕ) :=
  {a : Field DA DQ → ExtOrd //
    a ∈ CanonicalPairedProfiles.inventory (Field DA DQ) j ∧
    ∃ S : State DA DQ, Admitted X j S ∧ S.profile = a}

instance catalogueFinite (j : ℕ) : Finite (Catalogue X j) := by
  classical
  let := (CanonicalPairedProfiles.inventory_finite (Field DA DQ) j).fintype
  apply Finite.of_injective (fun a : Catalogue X j => (⟨a.1, a.2.1⟩ :
    ↥(CanonicalPairedProfiles.inventory (Field DA DQ) j)))
  intro a b h
  apply Subtype.ext
  exact congrArg (fun z : ↥(CanonicalPairedProfiles.inventory (Field DA DQ) j) => z.1) h

def normalizedMember {j : ℕ} (hj : 1 ≤ j) {S : State DA DQ}
    (hS : Admitted X j S) (hp : ∀ f, S.profile f ≠ ⊤) : Catalogue X j :=
  ⟨(S.normalize j).profile, normalize_inventory j hp,
    S.normalize j, normalize_admitted X hj hS, rfl⟩

/-- A catalogue seed obtained directly from the admitted zero state. -/
def zeroMember (j : ℕ) (hj : 1 ≤ j) : Catalogue X j :=
  normalizedMember X hj (zero_admitted X j) (fun f => by cases f <;> exact bot_ne_top)

end
end VaughtConjecture.Knight.Growth
