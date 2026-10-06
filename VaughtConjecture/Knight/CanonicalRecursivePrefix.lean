/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics
public import VaughtConjecture.Knight.CanonicalPairedInverse

/-! # Supported source-prefix completion on the recursive successor

The proper old-boundary repair is normalized and decoded by a constructed
supported inverse. Every recursive controller and every retained old occurrence
keeps its source-grid cap. Lawfulness concerns the actual current lower domain;
retained proper owners above it are not incorrectly assumed to have low grade.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursivePrefix
open Transform Value ExtOrd SourcePrefixRows CanonicalRecursiveSuccessorRows
open CanonicalPairedInverse PairedSlotEncoding
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))

/-- The repair is an old-boundary input; its whole recursive extension,
supported inverse and all auxiliary source-cap equations are constructed. -/
theorem exists_section
    (a : Profile sem n)
    {p : Cell D → ExtOrd}
    (hpr : RespectsSemanticsBelow sem (A, (n + 4)) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤)
    {B : ℕ} (hB : B ≤ 2 * Fintype.card (Cell D) + 1)
    (hag : ∀ d, min (a.val d) (CanonicalPairedInverse.grid (n + 4) B) =
      min (p d) (CanonicalPairedInverse.grid (n + 4) B)) :
    ∃ r : Cell (carrier sem n hA) → ExtOrd,
      RespectsSemanticsBelow (rows sem n hA hp P) (A, (n + 4)) (fun d => r d.1) ∧
      (∀ d, r (boundary sem n hA d) = p d) ∧
      (∀ d, min (r d) (CanonicalPairedInverse.grid (n + 4) B) =
        min (source sem n hA hp P a d) (CanonicalPairedInverse.grid (n + 4) B)) := by
  let F := data sem n hA hp P
  let b := CanonicalRecursiveInventory.encode sem (n + 1) hpr ht
  have hb : ∀ d, min (b.val d) (CanonicalPairedInverse.grid (n + 4) B) =
      min (a.val d) (CanonicalPairedInverse.grid (n + 4) B) :=
    CanonicalPairedProfiles.normalize_cap (Cell D) (n + 4) a.property.2 hag
  have hgrid : CanonicalPairedInverse.grid (n + 4) B ∈
      CanonicalRecursiveSuccessorRows.grid (D := D) n :=
    PairedSlotComparison.sourceGrid_endpoint hB
  have hsource := source_agreement_all sem n hA hp P
    b a hgrid hb
  obtain ⟨κ, hw, hread, hfix, hreach, _⟩ :=
    CanonicalPairedInverse.exists_supported_inverse a.property.2 ht hag
  have hfixGrid : ∀ z ∈ CanonicalRecursiveSuccessorRows.grid (D := D) n,
      z < CanonicalPairedInverse.grid (n + 4) B → κ z = z := by
    classical
    intro z hz hzB
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hw.bot
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hz
      apply hfix b
      by_contra hn
      have hBn : B ≤ b := Nat.le_of_not_gt hn
      have he : CanonicalPairedInverse.grid (n + 4) B ≤
          CanonicalPairedInverse.grid (n + 4) b :=
        ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl)
      exact (not_le_of_gt hzB) he
  have hfixBoundary : ∀ d, a.val d < CanonicalPairedInverse.grid (n + 4) B →
      κ (a.val d) = a.val d := by
    intro d hd
    have hba : a.val d = b.val d := eq_of_cap_eq_lt (hb d).symm hd
    have hpa : a.val d = p d := eq_of_cap_eq_lt (hag d) hd
    calc
      κ (a.val d) = κ (b.val d) := congrArg κ hba
      _ = p d := hread d
      _ = a.val d := hpa.symm
  have hguard : CanonicalPairedInverse.grid (n + 4) B ≤ gTop (n + 4) (n + 4) := by
    rw [gTop_of_le le_rfl]
    exact le_top
  have hcaps := OrbitPrefixSupport.decode_agree hw (grid_visible (n + 4) B) hguard hreach
    hfixGrid hfixBoundary (source_supported sem n hA hp P a)
    hsource
  have hpos : CanonicalPairedInverse.grid (n + 4) B ≠ ⊥ := ofOrd_ne_bot _
  have hwhole := SharpWitnessComposition.map_respects_of_positive_cap_agreement
    (F.profile_respects (controller sem n hA b))
    (F.profile_respects (controller sem n hA a))
    (fun d => d.2.2) (SharpWitnessComposition.boundedMap_of_witness hw)
    hpos (fun d => hcaps d.1)
  refine ⟨fun d => κ (source sem n hA hp P b d),
    hwhole, ?_, hcaps⟩
  intro d
  dsimp only
  rw [source_boundary]
  exact hread d

end
end VaughtConjecture.Knight.CanonicalRecursivePrefix
