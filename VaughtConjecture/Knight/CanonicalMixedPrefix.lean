/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedGradeLayers
public import VaughtConjecture.Knight.CanonicalPairedInverse

/-! # Constructed source-prefix sections on the canonical two-grade carrier

A lawful proper old-boundary repair agreeing with a canonical source at a
positive source-grid cut extends over both controller layers. Normalization,
the supported inverse, output lawfulness and every auxiliary source cap are
constructed here. This is source-prefix completion, not yet decoding against
an arbitrary ambient at an unrelated external cap.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalMixedPrefix
open Transform Value ExtOrd SourcePrefixRows CanonicalMixedGradeLayers
open CanonicalPairedInverse PairedSlotEncoding
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)
variable (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
variable (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

/-- No supported inverse, coded completion, or output lawfulness is assumed.
The proper repaired old boundary is the input produced by ordinary old-face
amalgamation. Every actual controller coordinate retains its source cap. -/
theorem exists_section
    (a : CanonicalFieldLayer.Profile sem k (Cell D) id)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {B : ℕ} (hB : B ≤ 2 * Fintype.card (Cell D) + 1)
    (hag : ∀ d, min (a.val d) (grid k B) = min (p d) (grid k B)) :
    ∃ r : Cell (scheme sem j hj hjA k hk hkA) → ExtOrd,
      RespectsSemantics (rows sem j hj hjA hproper k hg hk hkA hjk) r ∧
      (∀ d, r (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA d)) = p d) ∧
      (∀ d, min (r d) (grid k B) =
        min (source sem j hj hjA hproper k hg hk hkA hjk a d) (grid k B)) := by
  let F := data sem j hj hjA hproper k hg hk hkA hjk
  let b := normalized sem k hg hp ht
  have hb : ∀ d, min (b.val d) (grid k B) = min (a.val d) (grid k B) :=
    CanonicalPairedProfiles.normalize_cap (Cell D) k a.property.2 hag
  have hgrid : grid k B ∈ upperGrid (D := D) k :=
    PairedSlotComparison.sourceGrid_endpoint hB
  have hsource := source_agreement sem j hj hjA hproper k hg hk hkA hjk
    b a hgrid hb
  obtain ⟨κ, hw, hread, hfix, hreach, _⟩ :=
    CanonicalPairedInverse.exists_supported_inverse a.property.2 ht hag
  have hfixGrid : ∀ z ∈ upperGrid (D := D) k, z < grid k B → κ z = z := by
    classical
    intro z hz hzB
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hw.bot
    · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hz
      apply hfix n
      by_contra hn
      have hBn : B ≤ n := Nat.le_of_not_gt hn
      have he : grid k B ≤ grid k n := ofOrd_le_ofOrd.mpr
        (add_le_add (by gcongr) le_rfl)
      exact (not_le_of_gt hzB) he
  have hfixBoundary : ∀ d, a.val d < grid k B → κ (a.val d) = a.val d := by
    intro d hd
    have hba : a.val d = b.val d := eq_of_cap_eq_lt (hb d).symm hd
    have hpa : a.val d = p d := eq_of_cap_eq_lt (hag d) hd
    calc
      κ (a.val d) = κ (b.val d) := congrArg κ hba
      _ = p d := hread d
      _ = a.val d := hpa.symm
  have hguard : grid k B ≤ gTop k k := by rw [gTop_of_le le_rfl]; exact le_top
  have hcaps := OrbitPrefixSupport.decode_agree hw (grid_visible k B) hguard hreach
    hfixGrid hfixBoundary (source_supported sem j hj hjA hproper k hg hk hkA hjk a)
    hsource
  have hpos : grid k B ≠ ⊥ := ofOrd_ne_bot _
  have hwhole := SharpWitnessComposition.map_respects_of_positive_cap_agreement
    ((F.profile_respects (controller sem j hj hjA k hk hkA b)).toBelow (A, k))
    ((F.profile_respects (controller sem j hj hjA k hk hkA a)).toBelow (A, k))
    (fun d => F.max_grade d.1) (SharpWitnessComposition.boundedMap_of_witness hw)
    hpos (fun d => hcaps d.1)
  refine ⟨fun d => κ (source sem j hj hjA hproper k hg hk hkA hjk b d),
    hwhole.toRespects (fun d => ⟨(scheme sem j hj hjA k hk hkA).isPlan.subset_of_mem
      ((scheme sem j hj hjA k hk hkA).scope_mem_plan d), F.max_grade d⟩), ?_, hcaps⟩
  intro d
  dsimp only
  rw [source_boundary]
  exact hread d

end
end VaughtConjecture.Knight.CanonicalMixedPrefix
