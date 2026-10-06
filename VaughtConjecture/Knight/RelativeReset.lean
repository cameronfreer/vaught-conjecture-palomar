/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLift
public import VaughtConjecture.Knight.GradeEnvelope

/-! # The reset direction: prescribe the candidate, release the old high tail

The reviewer's notes7 (`mixed_proper_top_charts.md` §4.2, 2026-09-19), on the general-cap
relative data.  The private context is identified with the candidate's root along `φ`, is
bountiful, and its cells may have grades above the cap's grade `N`.

**`lift_reset`.**  Given an allowed pair `(u, v)` and any lawful candidate prescription `v'`
agreeing with `v` below `γ`, first install the prescribed root into `u` by the private
context's bountifulness (retaining every private `γ`-reading), then cap every private cell
of grade at least `N` at `γ` (`high_tail_release`).  The result `u'` is lawful, has the
literal root `v'|_B` (root cells have grade below `N`), agrees with `u` below `γ`, and reads
`u'(C) ≤ γ`; so in the class every correctness relation is evaluated below `γ`, where the
retained readings decide it (`correct_of_cap_le`).  At `γ = ⊥` the cap becomes bottom and
the class is inactive.

**Cap visibility at the target grade.**  The comparison cap `γ` must be visible at the
private top grade `topA.2`, which may exceed `N`: the tail clipping installs `γ` at every
grade from `N` up to `topA.2`, and orderliness there needs exactly that.  The grade gap
`q < N` (root cells below `N`) is a separate requirement.  Neither is implied by
`SelfVis N γ`.

Both lifts retain the selector's cap (`selector_cap_agree`), restated here as
`lift_reset_selector` and `relative_lift_selector`.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ] {A : Finset ιA} {Q : Finset ιQ}
  {DA : CellScheme A} {semA : Semantics DA} {DQ : CellScheme Q} {semQ : Semantics DQ}

/-- **The reset data**: the private context's root and top indices, the identification of
the candidate's root with the private root (compatible with `κ`), lawfulness transport of
candidate labellings to private root sections, and the private context's bountifulness.
Root cells have grade below `N`; the private top grade may exceed `N`. -/
structure ResetData (X : RelativeData DA semA DQ semQ) where
  rootA : Finset ιA × ℕ
  topA : Finset ιA × ℕ
  rootA_mem : rootA ∈ Plan.gradedPlan DA.plan
  topA_mem : topA ∈ Plan.gradedPlan DA.plan
  rootA_le : GradedLe rootA topA
  rootA_ne : rootA ≠ topA
  below_topA : ∀ d, GradedLe (DA.cell d) topA
  /-- The grade gap: root cells lie strictly below the cap's grade. -/
  rootA_lt_N : rootA.2 < X.req.N
  /-- The identification of the two roots. -/
  φ : DQ.below X.root ≃ DA.below rootA
  φ_κ : ∀ r, (φ r).1 = (X.κ r).1
  /-- Lawful candidate labellings restrict to lawful private root sections. -/
  respects_φ' : ∀ v : Cell DQ → ExtOrd, RespectsSemantics semQ v →
    RespectsSemanticsBelow semA rootA (fun d => v (φ.symm d).1)
  /-- The private context is bountiful. -/
  bountifulA : semA.IsBountiful

namespace ResetData

variable {X : RelativeData DA semA DQ semQ} (Y : ResetData X)

theorem N_le_topA : X.req.N ≤ Y.topA.2 := by
  have h : DA.grade X.req.C ≤ Y.topA.2 := (Y.below_topA X.req.C).2
  rwa [X.grade_C] at h

/-- **The reset lift**: every lawful candidate prescription agreeing with `v` below a cap
visible at the private top grade lifts to a lawful private labelling with the literal
prescribed root, agreeing with `u` below the cap, allowed against the prescription, and
reading the cap at most `γ`. -/
theorem lift_reset {u : Cell DA → ExtOrd} {v v' : Cell DQ → ExtOrd} (hall : X.Allowed u v)
    (hv' : RespectsSemantics semQ v') {γ : ExtOrd} (hγ : SelfVis Y.topA.2 γ)
    (hag : ∀ d, min (v' d) γ = min (v d) γ) :
    ∃ u' : Cell DA → ExtOrd, X.Allowed u' v' ∧ (∀ d, min (u' d) γ = min (u d) γ) ∧
      u' X.req.C ≤ γ := by
  obtain ⟨hu, hv, hroot, hrc⟩ := hall
  have hp : RespectsSemanticsBelow semA Y.rootA (fun d => v' (Y.φ.symm d).1) :=
    Y.respects_φ' v' hv'
  obtain ⟨t, ht, hcapt, hfacet⟩ := Y.bountifulA Y.rootA Y.topA Y.rootA_mem Y.topA_mem
    Y.rootA_le Y.rootA_ne (fun d => v' (Y.φ.symm d).1) (fun d => u d.1) γ hp (hu.toBelow _) hγ
    (fun d => by
      change min (u d.1) γ = min (v' (Y.φ.symm d).1) γ
      rw [hag, hroot, ← Y.φ_κ, Equiv.apply_symm_apply])
  obtain ⟨hrel, -, -, hrelcap⟩ := high_tail_release ht hγ X.req.N
  set u' : Cell DA → ExtOrd :=
    fun d => min (t ⟨d, Y.below_topA d⟩) (tailCaps X.req.N γ (DA.grade d)) with hu'def
  have hu' : RespectsSemantics semA u' := RespectsSemantics.of_below_top Y.below_topA hrel
  have hagu : ∀ d, min (u' d) γ = min (u d) γ := fun d =>
    (hrelcap ⟨d, Y.below_topA d⟩).trans (hcapt ⟨d, Y.below_topA d⟩)
  have hroot' : ∀ r : DQ.below X.root, v' r.1 = u' (X.κ r).1 := by
    intro r
    have hg : DA.grade (X.κ r).1 < X.req.N := by
      rw [← Y.φ_κ r]
      exact (Y.φ r).2.2.trans_lt Y.rootA_lt_N
    have hmono : (⟨(X.κ r).1, Y.below_topA _⟩ : DA.below Y.topA) =
        CellScheme.below.mono Y.rootA_le (Y.φ r) := Subtype.ext (Y.φ_κ r).symm
    change v' r.1 = min (t ⟨(X.κ r).1, Y.below_topA _⟩) (tailCaps X.req.N γ (DA.grade (X.κ r).1))
    rw [tailCaps_of_lt γ hg, min_eq_left le_top, hmono, hfacet (Y.φ r), Equiv.symm_apply_apply]
  have hc' : u' X.req.C ≤ γ := by
    change min (t ⟨X.req.C, Y.below_topA _⟩) (tailCaps X.req.N γ (DA.grade X.req.C)) ≤ γ
    rw [X.grade_C, tailCaps_of_le γ le_rfl]
    exact min_le_right _ _
  refine ⟨u', ⟨hu', hv', hroot', fun hcls => ?_⟩, hagu, hc'⟩
  have hγne : γ ≠ ⊥ := fun h => X.cap_ne_bot hcls (le_bot_iff.mp (h ▸ hc'))
  have hclsu : InClass X.ZA u := fun d => by
    rw [← bottom_pattern_of_cap_agreement hγne hagu d.1]
    exact hcls d
  exact X.correct_of_cap_le hu' (hrc hclsu) hagu hc' hag

/-- The reset lift retains the selector's cap. -/
theorem lift_reset_selector {u : Cell DA → ExtOrd} {v v' : Cell DQ → ExtOrd}
    (hall : X.Allowed u v) (hv' : RespectsSemantics semQ v') {γ : ExtOrd}
    (hγ : SelfVis Y.topA.2 γ) (hag : ∀ d, min (v' d) γ = min (v d) γ) :
    ∃ u' : Cell DA → ExtOrd, X.Allowed u' v' ∧ (∀ d, min (u' d) γ = min (u d) γ) ∧
      min (X.selector u') γ = min (X.selector u) γ := by
  obtain ⟨u', hall', hagu, -⟩ := Y.lift_reset hall hv' hγ hag
  exact ⟨u', hall', hagu, X.selector_cap_agree hagu⟩

end ResetData

namespace RelativeData

variable (X : RelativeData DA semA DQ semQ)

/-- The relative lift retains the selector's cap: the prescribed old face agrees with the old
one below `γ`, hence so do the selectors. -/
theorem relative_lift_selector {u v u' : _} (hall : X.Allowed u v)
    (hu' : RespectsSemantics semA u') {γ : ExtOrd} (hγ : SelfVis X.req.N γ)
    (hag : ∀ d, min (u' d) γ = min (u d) γ) :
    (∃ v' : Cell DQ → ExtOrd, X.Allowed u' v' ∧ ∀ d, min (v' d) γ = min (v d) γ) ∧
      min (X.selector u') γ = min (X.selector u) γ :=
  ⟨X.relative_lift hall hu' hγ hag, X.selector_cap_agree hag⟩

end RelativeData

end VaughtConjecture.Knight
