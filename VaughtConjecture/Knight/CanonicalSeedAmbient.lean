/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics
public import VaughtConjecture.Knight.ScopedSourcePrefixAmbient

/-! # Arbitrary ambient extraction on the recursive seed

Actual availability chooses a source row; its clipped locality witness reads
the entire target-local cap vector. No canonical-ambient hypothesis or supplied
serving controller is used. Higher proper owners outside the target stay in
the carrier without entering this domain.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.CanonicalSeedAmbient

open Transform Value ExtOrd SourcePrefixRows CanonicalRecursiveSeedRows
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)

private def seed : Profile sem :=
  CanonicalRecursiveInventory.encode sem 0 (p := fun _ => ⊥)
    ((RespectsSemantics.bot sem).toBelow (A, 3)) (fun _ => bot_ne_top)

abbrev target := (carrier sem hA).below (A, 3)

/-- An arbitrary active ambient has a genuine source-family representation
at the original cap, with a constructed first reaching grid cut. -/
theorem exists_capped_source {q : target sem hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem hA hp) (A, 3) q)
    (d : target sem hA)
    (hd : (carrier sem hA).grade d.1 = 3)
    {γ : ExtOrd} (hγ : SelfVis 3 γ) (hb : γ ≠ ⊥) (hactive : γ ≤ q d) :
    ∃ (a : Profile sem) (τ : ExtOrd → ExtOrd) (h : ExtOrd),
      Witness (gTop 3) τ ∧ (∀ x, τ x ≤ γ) ∧
      τ (ceiling (D := D)) = γ ∧
      h ∈ grid (D := D) ∧ SelfVis 3 h ∧ ⊥ < h ∧
      h ≤ ceiling (D := D) ∧ τ h = γ ∧
      (∀ z ∈ grid (D := D), z < h → τ z < γ) ∧
      (∀ x : target sem hA,
        τ (source sem hA hp a x.1) = min (q x) γ) ∧
      RespectsSemanticsBelow (rows sem hA hp) (A, 3)
        (fun x => τ (source sem hA hp a x.1)) := by
  let F := data sem hA hp
  obtain ⟨c, τ, _, hτ, hbound, hC, hread⟩ := ScopedSourcePrefixAmbient.exists_active_source F
    (controller sem hA (seed sem)) hq d hd hγ hactive
  let a := member sem hA hp c
  have ha : controller sem hA a = c :=
    (controllerEquiv sem hA hp).apply_symm_apply c
  have hr (x : target sem hA) :
      τ (source sem hA hp a x.1) = min (q x) γ := by
    change τ (F.profile (controller sem hA a) x.1) = _
    rw [ha]
    exact hread x
  obtain ⟨h, hh, hv, hpos, hc, he, hm⟩ :=
    ScopedSourcePrefixAmbient.exists_first_cut F hτ hb hbound hC
  refine ⟨a, τ, h, hτ, hbound, hC, hh, hv, hpos, hc, he, hm, hr, ?_⟩
  have hf : (fun x : target sem hA =>
      τ (source sem hA hp a x.1)) =
      (fun x => min (q x) γ) := funext hr
  rw [hf]
  exact hq.cap hγ

/-- Cap agreement with a prescribed owner above the cap supplies activation.
This uses the actual inclusion of the prescribed lower domain. -/
theorem prescribed_owner_active {CI : Finset ι × ℕ} (hCI : GradedLe CI (A, 3))
    {p : (carrier sem hA).below CI → ExtOrd}
    {q : target sem hA → ExtOrd} {γ : ExtOrd}
    (hag : ∀ x : (carrier sem hA).below CI,
      min (p x) γ = min (q ⟨x.1, x.2.trans hCI⟩) γ)
    (d : (carrier sem hA).below CI) (hpd : γ < p d) :
    γ ≤ q ⟨d.1, d.2.trans hCI⟩ :=
  (AmbientGradeCharts.cap_reaches_iff (hag d)).mp hpd.le

/-- Source extraction for an active prescribed owner, at the original cap.
Literal restoration above that cap is not asserted here. -/
theorem exists_source_of_prescribed_owner {CI : Finset ι × ℕ}
    (hCI : GradedLe CI (A, 3))
    {p : (carrier sem hA).below CI → ExtOrd}
    {q : target sem hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem hA hp) (A, 3) q)
    {γ : ExtOrd} (hγ : SelfVis 3 γ) (hb : γ ≠ ⊥)
    (hag : ∀ x : (carrier sem hA).below CI,
      min (p x) γ = min (q ⟨x.1, x.2.trans hCI⟩) γ)
    (d : (carrier sem hA).below CI)
    (hd : (carrier sem hA).grade d.1 = 3) (hpd : γ < p d) :
    ∃ (a : Profile sem) (τ : ExtOrd → ExtOrd),
      Witness (gTop 3) τ ∧ (∀ x, τ x ≤ γ) ∧
      (∀ x : target sem hA,
        τ (source sem hA hp a x.1) = min (q x) γ) ∧
      (∀ x : (carrier sem hA).below CI,
        τ (source sem hA hp a x.1) = min (p x) γ) ∧
      RespectsSemanticsBelow (rows sem hA hp) (A, 3)
        (fun x => τ (source sem hA hp a x.1)) := by
  have hactive := prescribed_owner_active sem hA hCI hag d hpd
  obtain ⟨a, τ, _, hτ, hbound, _, _, _, _, _, _, _, hr, hl⟩ :=
    exists_capped_source sem hA hp hq
      ⟨d.1, d.2.trans hCI⟩ hd hγ hb hactive
  refine ⟨a, τ, hτ, hbound, hr, ?_, hl⟩
  intro x
  exact (hr ⟨x.1, x.2.trans hCI⟩).trans (hag x).symm

end
end VaughtConjecture.Knight.CanonicalSeedAmbient
