/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PartialSections
public import VaughtConjecture.Knight.FiniteOffset

/-! # Transport along an occurrence-exact semantic face

An exact face copies graded indices and source rows, and exhausts all cells
inside its point scope. Arbitrary lawful local labellings and original-cap
lifts transport along its actual lower-domain equivalences.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {B A : Finset ι}
variable {D : CellScheme B} {K : CellScheme A}
variable (semD : Semantics D) (semK : Semantics K)

/-- Literal inherited semantics with no foreign cells inside the face. -/
structure ExactSemanticFace where
  map : Cell D ↪ Cell K
  index : ∀ d, K.cell (map d) = D.cell d
  exhaustive : ∀ z, K.scope z ⊆ B → ∃ d, map d = z
  row : ∀ (c : Cell D) (d : D.below (D.cell c)),
    semK.E (map c) ⟨map d.1, by rw [index, index]; exact d.2⟩ = semD.E c d

namespace ExactSemanticFace

variable {semD semK} (F : ExactSemanticFace semD semK)

def belowMap (c : Cell D) (d : D.below (D.cell c)) : K.below (K.cell (F.map c)) :=
  ⟨F.map d.1, by rw [F.index, F.index]; exact d.2⟩

noncomputable def belowEquiv (BJ : Finset ι × ℕ) (hB : BJ.1 ⊆ B) :
    D.below BJ ≃ K.below BJ :=
  Equiv.ofBijective (fun d => ⟨F.map d.1, by rw [F.index]; exact d.2⟩) ⟨by
    intro d e h
    exact Subtype.ext (F.map.injective (congrArg Subtype.val h)), by
    intro z
    obtain ⟨d, hd⟩ := F.exhaustive z.1 (z.2.1.trans hB)
    have hh : GradedLe (D.cell d) BJ := by rw [← F.index, hd]; exact z.2
    exact ⟨⟨d, hh⟩, Subtype.ext hd⟩⟩

theorem respects_below_iff (BJ : Finset ι × ℕ) (hB : BJ.1 ⊆ B)
    (q : K.below BJ → ExtOrd) :
    RespectsSemanticsBelow semK BJ q ↔
      RespectsSemanticsBelow semD BJ (q ∘ F.belowEquiv BJ hB) := by
  have h := respects_iff_of_equiv (sem' := semD) (sem := semK)
    (F.belowEquiv BJ hB) (fun d => (congrArg Prod.snd (F.index d.1)).symm)
    (fun d e => ?_) (fun c d hd => ?_) (q ∘ F.belowEquiv BJ hB)
  · have he : (q ∘ F.belowEquiv BJ hB) ∘ (F.belowEquiv BJ hB).symm = q := by
      funext d
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rw [he] at h
    exact h.symm
  · change D.scope d.1 ⊆ D.scope e.1 ↔ (K.cell (F.map d.1)).1 ⊆ (K.cell (F.map e.1)).1
    rw [F.index, F.index]
    rfl
  · exact (F.row c.1 d).symm

/-- Restriction includes arbitrary whole ambient labellings. -/
theorem restrict {q : Cell K → ExtOrd} (hq : RespectsSemantics semK q) :
    RespectsSemantics semD (q ∘ F.map) where
  orderly d := by
    change q (F.map d) = extVisibilityReplace (q (F.map d)) (D.cell d).2 (D.cell d).2
    have h := hq.orderly (F.map d)
    change q (F.map d) = extVisibilityReplace (q (F.map d))
      (K.cell (F.map d)).2 (K.cell (F.map d)).2 at h
    simpa only [F.index] using h
  locality c := by
    have h := (hq.locality (F.map c)).reindex (F.belowMap c)
    refine transformsTo_congr ?_ ?_ rfl h
    · funext d
      exact congrArg Prod.snd (F.index d.1)
    · funext d
      exact F.row c d
  availability c e hs hg := by
    obtain ⟨z, hz, hle⟩ := hq.availability (F.map c) (F.map e)
      (by change (K.cell _).1 ⊆ (K.cell _).1; rwa [F.index, F.index])
      (by change (K.cell _).2 = (K.cell _).2; rwa [F.index, F.index])
    have hzb : K.scope z ⊆ B := by
      change (K.cell z).1 ⊆ B
      rw [hz, F.index]
      exact D.isPlan.subset_of_mem (D.scope_mem_plan e)
    obtain ⟨d, rfl⟩ := F.exhaustive z hzb
    refine ⟨d, ?_, hle⟩
    simpa only [F.index] using hz

noncomputable def ownerEquiv (c : Cell D) :
    D.below (D.cell c) ≃ K.below (K.cell (F.map c)) :=
    Equiv.ofBijective (F.belowMap c) ⟨by
      intro d e h
      exact Subtype.ext (F.map.injective (congrArg Subtype.val h)), by
      intro z
      have hzb : K.scope z.1 ⊆ B := z.2.1.trans (by
        rw [F.index]
        exact D.isPlan.subset_of_mem (D.scope_mem_plan c))
      obtain ⟨d, hd⟩ := F.exhaustive z.1 hzb
      have hh : GradedLe (D.cell d) (D.cell c) := by
        have hh := z.2
        rw [← hd, F.index, F.index] at hh
        exact hh
      exact ⟨⟨d, hh⟩, Subtype.ext hd⟩⟩

/-- Old locality is also sufficient at the copied owner, on its whole
actual lower domain rather than only on named occurrences. -/
theorem locality_of_restrict {q : Cell K → ExtOrd}
    (hq : RespectsSemantics semD (q ∘ F.map)) (c : Cell D) :
    TransformsTo (fun d : K.below (K.cell (F.map c)) => K.grade d.1)
      (semK.E (F.map c)) (fun d => min (q d.1) (q (F.map c))) := by
  exact TransformsTo.of_equiv (F.ownerEquiv c)
    (fun d => congrArg Prod.snd (F.index d.1))
    (fun d => F.row c d) (fun _ => rfl) (hq.locality c)

/-- Consistency at an inherited owner is exactly old consistency transported
through the occurrence equivalence. -/
theorem consistent_at (hc : semD.IsConsistent) (c : Cell D) :
    RespectsSemanticsBelow semK (K.cell (F.map c)) (semK.E (F.map c)) := by
  have h := respects_iff_of_equiv (sem' := semD) (sem := semK)
    (F.ownerEquiv c) (fun d => (congrArg Prod.snd (F.index d.1)).symm)
    (fun d e => ?_) (fun c d hd => ?_) (semD.E c)
  · have he : semD.E c ∘ (F.ownerEquiv c).symm = semK.E (F.map c) := by
      funext d
      obtain ⟨e, rfl⟩ := (F.ownerEquiv c).surjective d
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      exact (F.row c e).symm
    rw [he] at h
    exact h.mp (hc c)
  · change D.scope d.1 ⊆ D.scope e.1 ↔ (K.cell (F.map d.1)).1 ⊆ (K.cell (F.map e.1)).1
    rw [F.index, F.index]
    rfl
  · exact (F.row c.1 d).symm

theorem coded_at (hc : semD.IsCoded) (c : Cell D)
    (d : K.below (K.cell (F.map c))) :
    IsCodedLabel (K.grade (F.map c)) (semK.E (F.map c) d) := by
  obtain ⟨e, rfl⟩ := (F.ownerEquiv c).surjective d
  change IsCodedLabel (K.cell (F.map c)).2
    (semK.E (F.map c) (F.belowMap c e))
  have hr : semK.E (F.map c) (F.belowMap c e) = semD.E c e := F.row c e
  rw [F.index, hr]
  exact hc c e

/-- Availability toward an inherited index is supplied inside that same
face; no witness from outside the target face is used. -/
theorem availability_at {q : Cell K → ExtOrd}
    (hq : RespectsSemantics semD (q ∘ F.map)) (z : Cell K) (c : Cell D)
    (hs : K.scope z ⊆ K.scope (F.map c)) (hg : K.grade z = K.grade (F.map c)) :
    ∃ d, K.cell d = K.cell (F.map c) ∧ q z ≤ q d := by
  have hzb : K.scope z ⊆ B := hs.trans (by
    change (K.cell (F.map c)).1 ⊆ B
    rw [F.index]
    exact D.isPlan.subset_of_mem (D.scope_mem_plan c))
  obtain ⟨e, rfl⟩ := F.exhaustive z hzb
  have hes : D.scope e ⊆ D.scope c := by
    change (D.cell e).1 ⊆ (D.cell c).1
    change (K.cell (F.map e)).1 ⊆ (K.cell (F.map c)).1 at hs
    simpa only [F.index] using hs
  have heg : D.grade e = D.grade c := by
    change (D.cell e).2 = (D.cell c).2
    change (K.cell (F.map e)).2 = (K.cell (F.map c)).2 at hg
    simpa only [F.index] using hg
  obtain ⟨d, hd, hle⟩ := hq.availability e c hes heg
  exact ⟨F.map d, (F.index d).trans (hd.trans (F.index c).symm), hle⟩

include F in
/-- Every proper-target lifting clause transfers at the original cap. -/
theorem lift {CI BJ : Finset ι × ℕ} (hB : BJ.1 ⊆ B)
    (hCI : CI ∈ Plan.gradedPlan D.plan) (hBJ : BJ ∈ Plan.gradedPlan D.plan)
    (h : GradedLe CI BJ) (hne : CI ≠ BJ) (hb : semD.IsBountiful)
    (p : K.below CI → ExtOrd) (q : K.below BJ → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow semK CI p) (hq : RespectsSemanticsBelow semK BJ q)
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ)
    (hc : ∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q', RespectsSemanticsBelow semK BJ q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      ∀ d, q' (CellScheme.below.mono h d) = p d := by
  let eB := F.belowEquiv BJ hB
  let eC := F.belowEquiv CI (h.1.trans hB)
  apply bountiful_of_equiv (sem' := semK) (sem := semD) h h eB.symm eC.symm
    ?_ ?_ ?_ (hb CI BJ hCI hBJ h hne) rfl p q γ hp hq hγ hc
  · intro d
    apply eB.injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact (congrArg Subtype.val (eC.apply_symm_apply d)).symm
  · intro q
    exact F.respects_below_iff BJ hB q
  · intro p
    exact F.respects_below_iff CI (h.1.trans hB) p

end ExactSemanticFace

end VaughtConjecture.Knight
