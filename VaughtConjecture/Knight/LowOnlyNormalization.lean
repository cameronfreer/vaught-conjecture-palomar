/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyFibres
public import VaughtConjecture.Knight.CappedDonorNormalization
public import VaughtConjecture.Knight.CanonicalPairedProfiles

/-! # Current-grade normalization of the complete gate-free LOW inventory

The inventory contains both complete original vectors and the cutoff, including
future occurrences. Common-root copies are equal but need not be quotiented.
Closure uses bottom-reflecting transport on long original rows. This is not
upward admission, and no physical auxiliary receipts are asserted here.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref
open SharpWitnessComposition

noncomputable section

variable {n K : ℕ} {P C : SemScheme n}

abbrev Field (P C : SemScheme n) := Cell P.scheme ⊕ (Cell C.scheme ⊕ Unit)

namespace State

def profile (S : State P C) : Field P C → ExtOrd
  | .inl d => S.u d
  | .inr (.inl d) => S.v d
  | .inr (.inr _) => S.b

/-- Recover both complete vectors and the stored cutoff from their coordinates. -/
def ofProfile (a : Field P C → ExtOrd) : State P C :=
  ⟨fun d => a (.inl d), fun d => a (.inr (.inl d)), a (.inr (.inr ()))⟩

@[simp] theorem ofProfile_profile (S : State P C) : ofProfile S.profile = S := rfl

@[simp] theorem profile_ofProfile (a : Field P C → ExtOrd) :
    (ofProfile a).profile = a := by
  funext f
  rcases f with d | d | ⟨⟩ <;> rfl

theorem profile_injective : Function.Injective (profile (P := P) (C := C)) := by
  intro S T h
  simpa only [ofProfile_profile] using congrArg ofProfile h

def map (σ : ExtOrd → ExtOrd) (S : State P C) : State P C :=
  ⟨fun d => σ (S.u d), fun d => σ (S.v d), σ S.b⟩

theorem profile_map (σ : ExtOrd → ExtOrd) (S : State P C) (d : Field P C) :
    (S.map σ).profile d = σ (S.profile d) := by
  rcases d with d | d | d <;> rfl

theorem capEq_iff_profile {S S' : State P C} {γ : ExtOrd} :
    S.CapEq γ S' ↔ ∀ d, min (S'.profile d) γ = min (S.profile d) γ := by
  constructor
  · rintro ⟨hu, hv, hb⟩ (d | d | d)
    · exact hu d
    · exact hv d
    · exact hb
  · intro h
    exact ⟨fun d => h (.inl d), fun d => h (.inr (.inl d)), h (.inr (.inr ()))⟩

def encoder (j : ℕ) (S : State P C) : ExtOrd → ExtOrd :=
  PairedSlotIncoming.encoder j (PairedSlotEncoding.values S.profile)

def normalize (j : ℕ) (S : State P C) : State P C := S.map (S.encoder j)

theorem profile_normalize (j : ℕ) (S : State P C) (d : Field P C) :
    (S.normalize j).profile d = PairedSlotEncoding.normalize j S.profile d := by
  rw [normalize, profile_map]
  exact PairedSlotIncoming.encoder_profile j S.profile d

theorem profile_count : Fintype.card (Field P C) =
    Fintype.card (Cell P.scheme) + Fintype.card (Cell C.scheme) + 1 := by
  simp only [Field, Fintype.card_sum, Fintype.card_unit, Nat.add_assoc]

end State

namespace Family

variable (F : Family P C K)

theorem maximum_map {j : ℕ} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop j) σ)
    (S : State P C) : F.maximum (S.map σ) = σ (F.maximum S) := by
  classical
  unfold maximum nonTopMax
  rw [Finset.apply_sup_eq_sup_comp σ (fun _ _ => hσ.mono.map_max) hσ.bot]
  rfl

/-- Current-grade, bottom-reflecting maps preserve the gate-free relation. -/
theorem Admissible.map {j : ℕ} {S : State P C} (hS : F.Admissible j S)
    {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop j) σ) (hj : 1 ≤ j)
    (hbot : ∀ x, σ x = ⊥ → x = ⊥) : F.Admissible j (S.map σ) where
  lawfulP := map_respects_of_bottom_reflecting hS.lawfulP
    (fun d => d.2.2.trans (min_le_left _ _)) (boundedMap_of_witness hσ) hbot
  lawfulC := map_respects_of_bottom_reflecting hS.lawfulC
    (fun d => d.2.2.trans (min_le_left _ _)) (boundedMap_of_witness hσ) hbot
  shared a := congrArg σ (hS.shared a)
  futureP d hd := selfVis_map hσ hj (hS.futureP d hd)
  futureC d hd := selfVis_map hσ hj (hS.futureC d hd)
  cutoff := selfVis_map hσ (min_le_left _ _) hS.cutoff
  low hK hm d hd := by
    rw [F.maximum_map hσ] at hm
    have hm' : F.maximum S < S.b := lt_of_not_ge (fun h => not_le.mpr hm (hσ.mono h))
    change max (σ S.b)
      (min (σ (S.v F.gap.c)) (extVisibilityReplace (σ (S.v F.gap.r.1)) K K)) ≤ σ (S.u d)
    rw [← map_comm hσ hK _ le_rfl, ← hσ.mono.map_min, ← hσ.mono.map_max]
    exact hσ.mono (hS.low hK hm' d hd)

theorem normalize_admissible {j : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) : F.Admissible j (S.normalize j) :=
  hS.map F (PairedSlotIncoming.encoder_witness j _) hj
    (PairedSlotIncoming.encoder_reflects_bottom j _)

/-- Proper normalized sources belong to the unchanged canonical complete-field inventory. -/
theorem normalize_inventory (j : ℕ) {S : State P C} (hp : ∀ d, S.profile d ≠ ⊤) :
    (S.normalize j).profile ∈ CanonicalPairedProfiles.inventory (Field P C) j := by
  have he : (S.normalize j).profile = PairedSlotEncoding.normalize j S.profile :=
    funext (State.profile_normalize j S)
  rw [he]
  exact CanonicalPairedProfiles.normalize_mem_inventory _ _ hp

theorem normalize_short (j : ℕ) (S : State P C) (d : Field P C) :
    Short j ((S.normalize j).profile d) := by
  rw [State.profile_normalize]
  exact PairedSlotProfiles.normalize_short j S.profile d

theorem normalize_bottom (j : ℕ) (S : State P C) (d : Field P C) :
    (S.normalize j).profile d = ⊥ ↔ S.profile d = ⊥ := by
  rw [State.profile_normalize]
  exact PairedSlotEncoding.normalize_bot_iff j S.profile d

/-- Relative normalization fixes the complete prefix against a canonical input. -/
theorem normalize_caps {j B : ℕ} {S S' : State P C}
    (hS : S.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j)
    (hcap : S.CapEq (ofOrd (Ordinal.omega0 * B + j)) S') :
    S.CapEq (ofOrd (Ordinal.omega0 * B + j)) (S'.normalize j) := by
  apply State.capEq_iff_profile.mpr
  intro d
  rw [State.profile_normalize]
  exact CanonicalPairedProfiles.normalize_cap _ _ hS
    (fun d => (State.capEq_iff_profile.mp hcap d).symm) d

/-- Normalizing a constructed private repair preserves admission; literal readback
and complete caps refer to the raw repair, before normalization. -/
theorem private_lift_normalized {j : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (v d) γ = min (S.lowerC j d) γ) :
    ∃ S', F.Admissible j S' ∧ S'.lowerC j = v ∧ S.CapEq γ S' ∧ S.FutureEq j S' ∧
      F.Admissible j (S'.normalize j) := by
  obtain ⟨S', hS', hv', hcap, hfuture⟩ := F.private_lift hS hv hγ hag
  exact ⟨S', hS', hv', hcap, hfuture, F.normalize_admissible hj hS'⟩

theorem donor_lift_normalized {j : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (u d) γ = min (S.lowerP j d) γ) :
    ∃ S', F.Admissible j S' ∧ S'.lowerP j = u ∧ S.CapEq γ S' ∧ S.FutureEq j S' ∧
      F.Admissible j (S'.normalize j) := by
  obtain ⟨S', hS', hu', hcap, hfuture⟩ := F.donor_lift hS hu hγ hag
  exact ⟨S', hS', hu', hcap, hfuture, F.normalize_admissible hj hS'⟩

end Family
end
end VaughtConjecture.Knight.LowOnly
