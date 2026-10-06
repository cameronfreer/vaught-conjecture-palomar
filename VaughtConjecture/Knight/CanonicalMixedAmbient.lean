/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedGradeLayers
public import VaughtConjecture.Knight.SourcePrefixAmbient

/-! # Arbitrary ambients on the constructed two-grade carrier

Availability on the new canonical rows chooses an actual canonical upper source
profile. Its clipped locality
witness reads the complete ambient cap vector, including both controller
layers. No hypothesis identifies the ambient with a constructed section.
The first reaching grid cut is produced, but prescribed-owner retuning at
that cut is not asserted here.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.CanonicalMixedAmbient

open Transform Value ExtOrd SourcePrefixRows CanonicalMixedGradeLayers
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)
variable (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
variable (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

private def seed : CanonicalFieldLayer.Profile sem k (Cell D) id :=
  CanonicalFieldLayer.encode sem k (Cell D) id hg (p := fun _ => ⊥)
    (RespectsSemantics.bot sem) (fun _ => bot_ne_top)

abbrev target := (scheme sem j hj hjA k hk hkA).below (A, k)

/-- An arbitrary active ambient has a genuine source-family representation
at the original cap, with a constructed first reaching grid cut. -/
theorem exists_capped_source {q : target sem j hj hjA k hk hkA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k) q)
    (d : target sem j hj hjA k hk hkA)
    (hd : (scheme sem j hj hjA k hk hkA).grade d.1 = k)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hb : γ ≠ ⊥) (hactive : γ ≤ q d) :
    ∃ (a : CanonicalFieldLayer.Profile sem k (Cell D) id) (τ : ExtOrd → ExtOrd) (h : ExtOrd),
      Witness (gTop k) τ ∧ (∀ x, τ x ≤ γ) ∧
      τ (upperCeiling (D := D) k) = γ ∧
      h ∈ upperGrid (D := D) k ∧ SelfVis k h ∧ ⊥ < h ∧
      h ≤ upperCeiling (D := D) k ∧ τ h = γ ∧
      (∀ z ∈ upperGrid (D := D) k, z < h → τ z < γ) ∧
      (∀ x : target sem j hj hjA k hk hkA,
        τ (source sem j hj hjA hproper k hg hk hkA hjk a x.1) = min (q x) γ) ∧
      RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k)
        (fun x => τ (source sem j hj hjA hproper k hg hk hkA hjk a x.1)) := by
  let F := data sem j hj hjA hproper k hg hk hkA hjk
  obtain ⟨c, τ, _, hτ, hbound, hC, hread⟩ := SourcePrefixAmbient.exists_active_source F
    (controller sem j hj hjA k hk hkA (seed sem k hg)) hq d hd hγ hactive
  let a := member sem j hj hjA hproper k hk hkA hjk c
  have ha : controller sem j hj hjA k hk hkA a = c :=
    (SeparatedSourceLayerCarrier.controllerEquiv (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA
      (lower_separated sem j hj hjA hproper k hjk)).apply_symm_apply c
  have hr (x : target sem j hj hjA k hk hkA) :
      τ (source sem j hj hjA hproper k hg hk hkA hjk a x.1) = min (q x) γ := by
    change τ (F.profile (controller sem j hj hjA k hk hkA a) x.1) = _
    rw [ha]
    exact hread x
  obtain ⟨h, hh, hv, hp, hc, he, hm⟩ :=
    SourcePrefixAmbient.exists_first_cut F hτ hb hbound hC
  refine ⟨a, τ, h, hτ, hbound, hC, hh, hv, hp, hc, he, hm, hr, ?_⟩
  have hf : (fun x : target sem j hj hjA k hk hkA =>
      τ (source sem j hj hjA hproper k hg hk hkA hjk a x.1)) =
      (fun x => min (q x) γ) := funext hr
  rw [hf]
  exact hq.cap hγ

/-- Cap agreement with a prescribed owner above the cap supplies activation.
This uses the actual inclusion of the prescribed lower domain. -/
theorem prescribed_owner_active {CI : Finset ι × ℕ} (hCI : GradedLe CI (A, k))
    {p : (scheme sem j hj hjA k hk hkA).below CI → ExtOrd}
    {q : target sem j hj hjA k hk hkA → ExtOrd} {γ : ExtOrd}
    (hag : ∀ x : (scheme sem j hj hjA k hk hkA).below CI,
      min (p x) γ = min (q ⟨x.1, x.2.trans hCI⟩) γ)
    (d : (scheme sem j hj hjA k hk hkA).below CI) (hp : γ < p d) :
    γ ≤ q ⟨d.1, d.2.trans hCI⟩ :=
  (AmbientGradeCharts.cap_reaches_iff (hag d)).mp hp.le

/-- The active prescribed-high branch of Plan 29 supplies its capped ambient
normal form without a chosen controller, chosen witness, or ambient completion.
Only the CAPPED prescription is recovered; literal restoration above the cap
is the separate alignment problem. -/
theorem exists_source_of_prescribed_owner {CI : Finset ι × ℕ}
    (hCI : GradedLe CI (A, k))
    {p : (scheme sem j hj hjA k hk hkA).below CI → ExtOrd}
    {q : target sem j hj hjA k hk hkA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k) q)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hb : γ ≠ ⊥)
    (hag : ∀ x : (scheme sem j hj hjA k hk hkA).below CI,
      min (p x) γ = min (q ⟨x.1, x.2.trans hCI⟩) γ)
    (d : (scheme sem j hj hjA k hk hkA).below CI)
    (hd : (scheme sem j hj hjA k hk hkA).grade d.1 = k) (hp : γ < p d) :
    ∃ (a : CanonicalFieldLayer.Profile sem k (Cell D) id) (τ : ExtOrd → ExtOrd),
      Witness (gTop k) τ ∧ (∀ x, τ x ≤ γ) ∧
      (∀ x : target sem j hj hjA k hk hkA,
        τ (source sem j hj hjA hproper k hg hk hkA hjk a x.1) = min (q x) γ) ∧
      (∀ x : (scheme sem j hj hjA k hk hkA).below CI,
        τ (source sem j hj hjA hproper k hg hk hkA hjk a x.1) = min (p x) γ) ∧
      RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k)
        (fun x => τ (source sem j hj hjA hproper k hg hk hkA hjk a x.1)) := by
  have hactive := prescribed_owner_active sem j hj hjA k hk hkA hCI hag d hp
  obtain ⟨a, τ, _, hτ, hbound, _, _, _, _, _, _, _, hr, hl⟩ :=
    exists_capped_source sem j hj hjA hproper k hg hk hkA hjk hq
      ⟨d.1, d.2.trans hCI⟩ hd hγ hb hactive
  refine ⟨a, τ, hτ, hbound, hr, ?_, hl⟩
  intro x
  exact (hr ⟨x.1, x.2.trans hCI⟩).trans (hag x).symm

end
end VaughtConjecture.Knight.CanonicalMixedAmbient
