/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalFieldLayer
public import VaughtConjecture.Knight.CanonicalPairedInverse

/-! # Prefix completion on the actual canonical lower layer

Unrepresented fields remain part of the normalization inventory and of every
controller agreement cut. A repaired physical boundary is extended to those
fields by retaining their old source values, not by dropping them.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalFieldPrefix
open Transform Value ExtOrd SourcePrefixRows CanonicalFieldLayer
open CanonicalPairedInverse PairedSlotEncoding
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (X : Type*) [Fintype X] (occ : Cell D → X)
variable (hj : 0 < j) (hA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ j)

theorem exists_section (a : Profile sem j X occ)
    {p : X → ExtOrd} (hp : RespectsSemantics sem (p ∘ occ)) (ht : ∀ x, p x ≠ ⊤)
    {B : ℕ} (hB : B ≤ 2 * Fintype.card X + 1)
    (hag : ∀ x, min (a.val x) (grid j B) = min (p x) (grid j B)) :
    ∃ r : Cell (scheme sem j X occ hj hA) → ExtOrd,
      RespectsSemantics (rows sem j X occ hj hA hproper hg) r ∧
      (∀ d, r (old sem j X occ hj hA d) = p (occ d)) ∧
      ∀ d, min (r d) (grid j B) =
        min (source sem j X occ hj hA hproper hg a d) (grid j B) := by
  let F := data sem j X occ hj hA hproper hg
  let b := encode sem j X occ hg hp ht
  have hb : ∀ x, min (b.val x) (grid j B) = min (a.val x) (grid j B) :=
    CanonicalPairedProfiles.normalize_cap X j a.property.2 hag
  have hgrid : grid j B ∈ PairedSlotComparison.sourceGrid j (Fintype.card X) :=
    PairedSlotComparison.sourceGrid_endpoint hB
  have hs := source_prefix sem j X occ hj hA hproper hg b a hgrid hb
  obtain ⟨κ, hw, hread, hfix, hreach, _⟩ :=
    exists_supported_inverse a.property.2 ht hag
  have hfixGrid : ∀ z ∈ PairedSlotComparison.sourceGrid j (Fintype.card X),
      z < grid j B → κ z = z := by
    classical
    intro z hz hzB
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hw.bot
    · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hz
      apply hfix n
      by_contra hn
      have hBn : B ≤ n := Nat.le_of_not_gt hn
      exact (not_le_of_gt hzB) (ofOrd_le_ofOrd.mpr
        (add_le_add (by gcongr) le_rfl))
  have hfixBoundary (x : X) (hx : a.val x < grid j B) : κ (a.val x) = a.val x := by
    have hba := eq_of_cap_eq_lt (hb x).symm hx
    have hpa := eq_of_cap_eq_lt (hag x) hx
    exact (congrArg κ hba).trans ((hread x).trans hpa.symm)
  have hfixSource (d : Cell (scheme sem j X occ hj hA))
      (hd : source sem j X occ hj hA hproper hg a d < grid j B) :
      κ (source sem j X occ hj hA hproper hg a d) =
        source sem j X occ hj hA hproper hg a d := by
    by_cases he : (scheme sem j X occ hj hA).cell d = (A, j)
    · have hh : source sem j X occ hj hA hproper hg a d ∈ F.grid := by
        change F.profile (controller sem j X occ hj hA a) d ∈ F.grid
        rw [show d = (⟨d, he⟩ : SourcePrefixLayer.Controller _ j).1 from rfl,
          F.profile_new]
        exact cut_mem F.bot_mem _ _
      exact hfixGrid _ hh hd
    · obtain ⟨e, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j X occ)
        j hj hA d he
      rw [source_old] at hd ⊢
      exact hfixBoundary (occ e) hd
  have hcaps : ∀ d, min (κ (source sem j X occ hj hA hproper hg b d)) (grid j B) =
      min (source sem j X occ hj hA hproper hg a d) (grid j B) := by
    apply hs.decode hw.mono monotone_id hreach le_rfl
    intro d hd
    have he := eq_of_cap_eq_lt (hs d) hd
    rw [he, hfixSource d (he ▸ hd)]
    rfl
  have hr := SharpWitnessComposition.map_respects_of_positive_cap_agreement
    ((F.profile_respects (controller sem j X occ hj hA b)).toBelow (A, j))
    ((F.profile_respects (controller sem j X occ hj hA a)).toBelow (A, j))
    (fun d => F.max_grade d.1) (SharpWitnessComposition.boundedMap_of_witness hw)
    (ofOrd_ne_bot _) (fun d => hcaps d.1)
  refine ⟨fun d => κ (source sem j X occ hj hA hproper hg b d),
    hr.toRespects (fun d => ⟨(scheme sem j X occ hj hA).isPlan.subset_of_mem
      ((scheme sem j X occ hj hA).scope_mem_plan d), F.max_grade d⟩), ?_, hcaps⟩
  intro d
  dsimp only
  rw [source_old]
  exact hread (occ d)

/-- Completion of physical occurrences, with all other fields retained before
normalization. Injectivity is occurrence injectivity, not label injectivity. -/
theorem exists_boundary_section (hinj : Function.Injective occ) (a : Profile sem j X occ)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {B : ℕ} (hB : B ≤ 2 * Fintype.card X + 1)
    (hag : ∀ d, min (a.val (occ d)) (grid j B) = min (p d) (grid j B)) :
    ∃ r : Cell (scheme sem j X occ hj hA) → ExtOrd,
      RespectsSemantics (rows sem j X occ hj hA hproper hg) r ∧
      (∀ d, r (old sem j X occ hj hA d) = p d) ∧
      ∀ d, min (r d) (grid j B) =
        min (source sem j X occ hj hA hproper hg a d) (grid j B) := by
  classical
  let v := Function.extend occ p a.val
  have hv (d : Cell D) : v (occ d) = p d := hinj.extend_apply p a.val d
  have hvp : RespectsSemantics sem (v ∘ occ) := by
    simpa only [Function.comp_def, hv] using hp
  have hvt : ∀ x, v x ≠ ⊤ := by
    intro x
    by_cases hx : ∃ d, occ d = x
    · obtain ⟨d, rfl⟩ := hx
      rw [hv]; exact ht d
    · rw [show v x = a.val x from Function.extend_apply' p a.val x hx]
      exact a.property.2.2 x
  have hva : ∀ x, min (a.val x) (grid j B) = min (v x) (grid j B) := by
    intro x
    by_cases hx : ∃ d, occ d = x
    · obtain ⟨d, rfl⟩ := hx
      rw [hv]; exact hag d
    · rw [show v x = a.val x from Function.extend_apply' p a.val x hx]
  obtain ⟨r, hr, hread, hcap⟩ := exists_section sem j X occ hj hA hproper hg
    a hvp hvt hB hva
  exact ⟨r, hr, fun d => (hread d).trans (hv d), hcap⟩

end
end VaughtConjecture.Knight.CanonicalFieldPrefix
