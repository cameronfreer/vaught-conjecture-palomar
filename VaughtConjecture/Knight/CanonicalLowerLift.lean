/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalGradeOneLift
public import VaughtConjecture.Knight.CanonicalLowerDomain

/-! # Grade-one lifting inside the actual canonical two-grade output -/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalLowerLift
open Transform Value ExtOrd CanonicalMixedGradeLayers CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- The old graded-pair clause transports exactly to the grade cut, retaining
every old occurrence and its original cap. -/
theorem cut_lift {sem : Semantics D} {I U : Finset ι × ℕ} {j : ℕ}
    (h : GradedLe I U) (hU : U.2 ≤ j) (hlift : CappedLift sem h) :
    CappedLift (GradeCutBoundary.rows D j sem) h := by
  intro p q γ hp hq hγ hag
  let eI := GradeCutBoundary.belowEquiv D j I (h.2.trans hU)
  let eU := GradeCutBoundary.belowEquiv D j U hU
  have hp' := (GradeCutBoundary.respects_iff D j sem I (h.2.trans hU) p).mp hp
  have hq' := (GradeCutBoundary.respects_iff D j sem U hU q).mp hq
  have hm (d : (GradeCutBoundary.scheme D j).below I) :
      eU (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  have hms (d : D.below I) :
      eU.symm (CellScheme.below.mono h d) = CellScheme.below.mono h (eI.symm d) := by
    apply eU.injective
    rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply]
  obtain ⟨r, hr, hcap, hread⟩ := hlift (p ∘ eI.symm) (q ∘ eU.symm) γ hp' hq' hγ
    (fun d => by simpa only [Function.comp_apply, hms] using hag (eI.symm d))
  refine ⟨r ∘ eU, GradeCutBoundary.pullback_respects D j sem hU hr, ?_, ?_⟩
  · intro d
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hcap (eU d)
  · intro d
    simpa only [Function.comp_apply, hm, Equiv.symm_apply_apply] using hread (eI d)

variable (sem : Semantics D) (hA : 1 ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)
variable (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
variable (hk : 0 < k) (hkA : k ≤ A.card) (h1k : 1 < k)

def oldLow (d : Cell D) (hd : D.grade d ≤ 1) :
    (scheme sem 1 (by decide) hA k hk hkA).below (A, 1) :=
  ⟨oldCell sem 1 (by decide) hA k hk hkA (lowerOld sem 1 (by decide) hA d), by
    simpa only [oldCell, lowerOld, CanonicalGradeCutSections.old,
      SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using
      (show GradedLe (D.cell d) (A, 1) from
        ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩)⟩

theorem equiv_old (d : Cell (GradeCutBoundary.scheme D 1)) :
    CanonicalLowerDomain.equiv sem 1 (by decide) hA k hk hkA h1k (A, 1) le_rfl
      (CanonicalFieldOwnerLift.oldTarget (GradeCutBoundary.rows D 1 sem) 1 (Cell D)
        (GradeCutBoundary.toCell D 1) (by decide) hA (GradeCutBoundary.proper D 1 hproper)
        (GradeCutBoundary.grade_bound D 1) d) =
      oldLow sem hA k hk hkA (GradeCutBoundary.toCell D 1 d)
        (GradeCutBoundary.grade_bound D 1 d) := by
  apply Subtype.ext
  change oldCell sem 1 (by decide) hA k hk hkA
    (GradeCutLayerCarrier.embed D (CanonicalGradeCutSections.Profiles sem 1) 1 (by decide) hA
      (SourceLayerCarrier.toCell (GradeCutBoundary.scheme D 1)
        (CanonicalGradeCutSections.Profiles sem 1) 1 (by decide) hA (.inl d))) = _
  rw [GradeCutLayerCarrier.embed_toCell]
  rfl

/-- The actual lower-layer lift, from arbitrary lawful local inputs. It
restores distinct values and top, with no bound by an upper-grade owner.
The only section-supply inputs are the two OLD face lifting clauses. -/
theorem exists_positive_lift {C : Finset ι}
    (hfull : ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    {p : D.below (C, 1) → ExtOrd} (hp : RespectsSemanticsBelow sem (C, 1) p)
    {q : (scheme sem 1 (by decide) hA k hk hkA).below (A, 1) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem 1 (by decide) hA hproper k hg hk hkA h1k) (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e : D.below (C, 1),
      min (p e) γ = min (q (oldLow sem hA k hk hkA e.1 e.2.2)) γ)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, D.grade d ≤ 1 →
      GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hCU : GradedLe (C, 1) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hCU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ 1) (hV : V.2 ≤ 1) :
    ∃ r : (scheme sem 1 (by decide) hA k hk hkA).below (A, 1) → ExtOrd,
      RespectsSemanticsBelow (rows sem 1 (by decide) hA hproper k hg hk hkA h1k) (A, 1) r ∧
      (∀ e : D.below (C, 1), r (oldLow sem hA k hk hkA e.1 e.2.2) = p e) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  let eC := GradeCutBoundary.belowEquiv D 1 (C, 1) le_rfl
  let eA := CanonicalLowerDomain.equiv sem 1 (by decide) hA k hk hkA h1k (A, 1) le_rfl
  have hp' := GradeCutBoundary.pullback_respects D 1 sem le_rfl hp
  have hq' := CanonicalLowerDomain.pullback_respects sem 1 (by decide) hA hproper k hg hk hkA
    h1k le_rfl hq
  have hf : ∃ c : (GradeCutBoundary.scheme D 1).below (C, 1),
      (GradeCutBoundary.scheme D 1).cell c.1 = (C, 1) := by
    obtain ⟨c, hc⟩ := hfull
    refine ⟨eC.symm c, ?_⟩
    have he := congrArg (fun z : D.below (C, 1) => D.cell z.1) (eC.apply_symm_apply c)
    exact he.trans hc
  have hmap (e : (GradeCutBoundary.scheme D 1).below (C, 1)) :
      eA (CanonicalFieldOwnerLift.oldTarget (GradeCutBoundary.rows D 1 sem) 1 (Cell D)
        (GradeCutBoundary.toCell D 1) (by decide) hA (GradeCutBoundary.proper D 1 hproper)
        (GradeCutBoundary.grade_bound D 1) e.1) =
      oldLow sem hA k hk hkA (eC e).1 (eC e).2.2 :=
    equiv_old sem hA hproper k hk hkA h1k e.1
  obtain ⟨r, hr, hread, hcap⟩ := CanonicalGradeOneLift.exists_positive_lift
    (GradeCutBoundary.rows D 1 sem) (Cell D) (GradeCutBoundary.toCell D 1) hA
    (GradeCutBoundary.proper D 1 hproper) (GradeCutBoundary.grade_bound D 1)
    (GradeCutBoundary.toCell D 1).injective hf hp' hq' hγ hγb
    (fun e => by
      change min (p (eC e)) γ = min (q (eA _)) γ
      rw [hmap]
      exact hag (eC e))
    (fun d => hcover (GradeCutBoundary.toCell D 1 d) (GradeCutBoundary.grade_bound D 1 d))
    hCU hOU hOV (fun d => hinter (GradeCutBoundary.toCell D 1 d))
    (cut_lift hCU hU hleft) (cut_lift hOV hV hright) hU hV
  refine ⟨r ∘ eA.symm,
    (CanonicalLowerDomain.respects_iff sem 1 (by decide) hA hproper k hg hk hkA h1k
      (A, 1) le_rfl r).mp hr, ?_, ?_⟩
  · intro e
    have he := hread (eC.symm e)
    have hm := hmap (eC.symm e)
    rw [eC.apply_symm_apply] at hm
    rw [← hm, Function.comp_apply, eA.symm_apply_apply, he]
    exact congrArg p (eC.apply_symm_apply e)
  · intro d
    have he := hcap (eA.symm d)
    change min (r (eA.symm d)) γ = min (q (eA (eA.symm d))) γ at he
    simpa only [Function.comp_apply, eA.apply_symm_apply] using he

end
end VaughtConjecture.Knight.CanonicalLowerLift
