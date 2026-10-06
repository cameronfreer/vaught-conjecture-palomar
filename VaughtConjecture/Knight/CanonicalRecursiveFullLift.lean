/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveActiveLift
public import VaughtConjecture.Knight.CanonicalRecursiveTopSections

/-! # All-cap proper-face lifting at the recursive successor grade

Bottom-cap supply first completes the actual old boundary using its two
lifting clauses, then extends through the recursive layers with exact top
decoding. Positive caps split into active and inactive prescribed owners.
No future completion or output bountifulness is assumed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveFullLift
open Transform Value ExtOrd CoatomBoundaryExtension
open CanonicalRecursiveSuccessorRows CanonicalRecursiveCutPrefix CanonicalRecursiveActiveLift
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)
variable {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A)
variable {U V O : Finset ι × ℕ}
variable (hcover : ∀ d : Cell (cut (D := D) n),
  GradedLe ((cut (D := D) n).cell d) U ∨ GradedLe ((cut (D := D) n).cell d) V)
variable (hCU : GradedLe (C, n + 4) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
variable (hinter : ∀ d : Cell (cut (D := D) n), GradedLe ((cut (D := D) n).cell d) U →
  GradedLe ((cut (D := D) n).cell d) V → GradedLe ((cut (D := D) n).cell d) O)
variable (hleft : CappedLift (cutRows sem n) hCU) (hright : CappedLift (cutRows sem n) hOV)

include hC hCA hcover hOU hinter hleft hright in
/-- Local bottom-cap supply, not just extension of an already whole boundary.
The prescription may contain literal top. No ambient is needed. -/
theorem exists_section
    {p : (carrier sem n hA).below (C, n + 4) → ExtOrd}
    (hpr : RespectsSemanticsBelow (outputRows sem n hA hp) (C, n + 4) p) :
    ∃ r : CanonicalRecursiveAmbient.target sem n hA → ExtOrd,
      RespectsSemanticsBelow (outputRows sem n hA hp) (A, n + 4) r ∧
      ∀ e, r (CellScheme.below.mono
        (show GradedLe (C, n + 4) (A, n + 4) from
          ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) = p e := by
  have hCnot : ¬ A ⊆ C := fun h =>
    hCA (Finset.Subset.antisymm (D.isPlan.subset_of_mem hC) h)
  let E := faceEquiv sem n hA (C, n + 4) hCnot le_rfl
  have hp₀ := pullback_respects sem n hA hp (C, n + 4) hCnot le_rfl hpr
  obtain ⟨b, hbread⟩ := CoatomBoundaryExtension.section_left
    hCU hOU hOV hinter hleft hright (p ∘ E) hp₀
  let F := GradeCutBoundary.belowEquiv D (n + 4) (A, n + 4) le_rfl
  have hu := (GradeCutBoundary.respects_iff D (n + 4) sem (A, n + 4) le_rfl _).mp
    ((b.whole_respects hcover).toBelow (A, n + 4))
  obtain ⟨r, hr, hread⟩ := CanonicalRecursiveTopSections.exists_section sem hp (n + 1) hA hu
  refine ⟨r, hr, ?_⟩
  intro e
  obtain ⟨d, rfl⟩ := E.surjective e
  let dA : (cut (D := D) n).below (A, n + 4) :=
    ⟨d.1, d.2.1.trans (D.isPlan.subset_of_mem hC), d.2.2⟩
  have hd : CellScheme.below.mono
      (show GradedLe (C, n + 4) (A, n + 4) from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) (E d) =
      CanonicalRecursiveTopSections.boundaryTarget sem (n + 1) hA (F dA) :=
    Subtype.ext (faceEquiv_val sem n hA _ hCnot le_rfl d)
  rw [hd, hread]
  change b.whole hcover (F.symm (F dA)).1 = p (E d)
  rw [Equiv.symm_apply_apply]
  exact (b.whole_left hcover (CellScheme.below.mono hCU d)).trans
    ((b.value_left _).symm.trans (hbread d))

include hC hCA hcover hOU hinter hleft hright in
/-- All original permitted caps at the new same-grade proper-to-full pair.
The predecessor supplies only lower restoration. Old-face clauses supply
only boundary completion. Every actual successor auxiliary cap survives. -/
theorem full_lift
    (hb : CanonicalRecursiveRestoration.LowerBountiful sem n hA (predecessorState sem n hA hp))
    (hCc : n + 4 ≤ C.card)
    (hfull : ∃ c : (cut (D := D) n).below (C, n + 4),
      (cut (D := D) n).cell c.1 = (C, n + 4))
    (hU : U.2 ≤ n + 4) (hV : V.2 ≤ n + 4) :
    CappedLift (outputRows sem n hA hp)
      (show GradedLe (C, n + 4) (A, n + 4) from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  intro p q γ hpr hqr hγ hag
  by_cases hγb : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := exists_section sem n hA hp hC hCA
      hcover hCU hOU hOV hinter hleft hright hpr
    exact ⟨r, hr, fun _ => by simp only [hγb, min_bot_right], hread⟩
  by_cases hactive : ∃ d : (carrier sem n hA).below (C, n + 4),
      (carrier sem n hA).grade d.1 = n + 4 ∧ γ < p d
  · obtain ⟨r, hr, hread, hcap⟩ := CanonicalRecursiveActiveLift.exists_lift
      sem n hA hp hb hC hCA hCc hfull hpr hqr hγ hγb (fun d => (hag d).symm)
      hactive hcover hCU hOU hOV hinter hleft hright hU hV
    exact ⟨r, hr, hcap, hread⟩
  · exact CanonicalRecursiveRestoration.inactive sem n hA hp
      (predecessorState sem n hA hp) hb hC (Nat.le_of_succ_le hCc) hpr hqr hγ hag
      (fun d hd => not_lt.mp (fun h => hactive ⟨d, hd, h⟩))

end
end VaughtConjecture.Knight.CanonicalRecursiveFullLift
