/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSections
public import VaughtConjecture.Knight.CanonicalInactiveLift

/-! # All-cap lifting of original faces into the canonical two-grade target

Bottom cap uses independent section supply. At a positive cap, inactive upper
data use lower lifting and a bounded tail; active upper data use the maximal
prescribed owner and literal lower restoration. Empty scopes and grade zero
require no owner. Every target controller cap is retained.

This is the original-face ledger, not the full-scope grade-one to grade-two
pair whose prescription includes the newly added lower controllers.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalOriginalLift
open Transform Value ExtOrd CanonicalMixedGradeLayers CanonicalMixedOwnerLift
open CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 2 ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ 2)

/-- Unrestricted original-face lifting at every permitted cap. The owner
incidences are ordinary OLD completeness data, only at possible grades. All
section and lifting premises concern the two old faces, never the output.
No properness, owner domination, or active-owner assumption on labels remains. -/
theorem exists_lift {C : Finset ι} {n : ℕ} (hn : n ≤ 2)
    (hfull₁ : C.Nonempty → ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    (hfull₂ : 2 ≤ C.card → ∃ c : D.below (C, 2), D.cell c.1 = (C, 2))
    {p : D.below (C, n) → ExtOrd} (hp : RespectsSemanticsBelow sem (C, n) p)
    {q : CanonicalMixedAmbient.target sem 1 (by decide) (by omega) 2 (by decide) hA → ExtOrd}
    (hq : RespectsSemanticsBelow
      (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ)
    (hag : ∀ e : D.below (C, n), min (p e) γ =
      min (q (oldTarget sem 1 (by decide) (by omega) hproper 2 hg
        (by decide) hA (by decide) e.1)) γ)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hCU : GradedLe (C, n) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hCU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ 2) (hV : V.2 ≤ 2)
    {U₁ V₁ O₁ : Finset ι × ℕ}
    (hcover₁ : ∀ d : Cell D, D.grade d ≤ 1 →
      GradedLe (D.cell d) U₁ ∨ GradedLe (D.cell d) V₁)
    (hCU₁ : GradedLe (C, 1) U₁) (hOU₁ : GradedLe O₁ U₁) (hOV₁ : GradedLe O₁ V₁)
    (hinter₁ : ∀ d : Cell D, GradedLe (D.cell d) U₁ → GradedLe (D.cell d) V₁ →
      GradedLe (D.cell d) O₁)
    (hleft₁ : CappedLift sem hCU₁) (hright₁ : CappedLift sem hOV₁)
    (hU₁ : U₁.2 ≤ 1) (hV₁ : V₁.2 ≤ 1) :
    ∃ r : CanonicalMixedAmbient.target sem 1 (by decide) (by omega) 2 (by decide) hA → ExtOrd,
      RespectsSemanticsBelow
        (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)) (A, 2) r ∧
      (∀ e : D.below (C, n), r (oldTarget sem 1 (by decide) (by omega) hproper 2 hg
        (by decide) hA (by decide) e.1) = p e) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  by_cases hne : C.Nonempty
  swap
  · refine ⟨q, hq, ?_, fun _ => rfl⟩
    intro e
    have hcard : 0 < C.card := (D.grade_pos e.1).trans_le
      ((D.grade_le_card_scope e.1).trans (Finset.card_le_card e.2.1))
    exact (hne (Finset.card_pos.mp hcard)).elim
  by_cases hn0 : n = 0
  · refine ⟨q, hq, ?_, fun _ => rfl⟩
    intro e
    have he : D.grade e.1 ≤ 0 := e.2.2.trans hn0.le
    exact (not_le_of_gt (D.grade_pos e.1) he).elim
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  by_cases hγb : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := CanonicalSections.exists_section sem 1 (by decide) (by omega)
      hproper 2 hg (by decide) hA (by decide) hcover hCU hOU hOV hinter hleft hright hp
    exact ⟨r, hr, hread, fun _ => by simp only [hγb, min_bot_right]⟩
  by_cases hactive : ∃ d : D.below (C, n), D.grade d.1 = 2 ∧ γ < p d
  · have hn2 : n = 2 := by
      obtain ⟨d, hd, _⟩ := hactive
      have he := d.2.2
      change D.grade d.1 ≤ n at he
      omega
    subst n
    have hcard : 2 ≤ C.card := by
      obtain ⟨d, hd, _⟩ := hactive
      exact hd ▸ (D.grade_le_card_scope d.1).trans (Finset.card_le_card d.2.1)
    exact CanonicalTwoGradeLift.exists_lift sem hA hproper hg (hfull₂ hcard) (hfull₁ hne)
      hp hq hγ hγb hag hactive hcover hCU hOU hOV hinter hleft hright hU hV
      hcover₁ hCU₁ hOU₁ hOV₁ hinter₁ hleft₁ hright₁ hU₁ hV₁
  · exact CanonicalInactiveLift.exists_lift sem hA hproper hg hn1 (Or.inr (hfull₁ hne))
      hp hq hγ hγb hag (fun d hd => not_lt.mp (fun h => hactive ⟨d, hd, h⟩))
      hcover₁ hCU₁ hOU₁ hOV₁ hinter₁ hleft₁ hright₁ hU₁ hV₁

end
end VaughtConjecture.Knight.CanonicalOriginalLift
