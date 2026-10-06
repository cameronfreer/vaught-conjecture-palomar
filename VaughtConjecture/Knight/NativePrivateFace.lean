/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PointImageSemantics
public import VaughtConjecture.Knight.ExactSemanticFace
public import VaughtConjecture.Knight.CappedDonorSource

/-! # The full native private domain as an actual placed semantic face

An occurrence-exact semantic face under an injective point placement supplies
the full private lower-domain equivalence and lawfulness transport. No
selected-section or ambient-extension hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.NativePrivateFace
open Transform Value ExtOrd CappedDonor
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A S : Finset ι} {D : CellScheme A}
variable {N : ℕ} (C : SemScheme N) (place : Fin N ↪ ι) (hS : Finset.univ.image place = S)
variable {sem : Semantics D}
variable (E : ExactSemanticFace (PointImageSemantics.rows C.scheme place hS C.rows) sem)

theorem index (d : Cell C.scheme) :
    D.cell (E.map d) = ((C.scheme.scope d).image place, C.scheme.grade d) := E.index d

def fullEquiv : C.scheme.below (effC N N) ≃ D.below (S, N) :=
  Equiv.ofBijective (fun d => ⟨E.map d.1, by
    rw [index C place hS E]
    exact ⟨hS ▸ Finset.image_subset_image (Finset.subset_univ _), gradeC_le d.1⟩⟩) ⟨by
    intro d e he
    exact Subtype.ext (E.map.injective (congrArg Subtype.val he)), by
    intro d
    obtain ⟨c, hc⟩ := E.exhaustive d.1 d.2.1
    exact ⟨⟨c, Finset.subset_univ _, le_min (gradeC_le c) (gradeC_le c)⟩,
      Subtype.ext hc⟩⟩

theorem fullEquiv_grade (d : C.scheme.below (effC N N)) :
    D.grade (fullEquiv C place hS E d).1 = C.scheme.grade d.1 :=
  congrArg Prod.snd (index C place hS E d.1)

theorem respects_iff (p : D.below (S, N) → ExtOrd) :
    RespectsSemanticsBelow sem (S, N) p ↔
      RespectsSemanticsBelow C.rows (effC N N) (p ∘ fullEquiv C place hS E) := by
  have h := respects_iff_of_equiv (sem' := C.rows) (sem := sem)
    (fullEquiv C place hS E) (fun d => (fullEquiv_grade C place hS E d).symm)
    (fun d e => ?_) (fun c d hd => ?_) (p ∘ fullEquiv C place hS E)
  · have he : (p ∘ fullEquiv C place hS E) ∘ (fullEquiv C place hS E).symm = p := by
      funext d
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rw [he] at h
    exact h.symm
  · change C.scheme.scope d.1 ⊆ C.scheme.scope e.1 ↔
      (D.cell (E.map d.1)).1 ⊆ (D.cell (E.map e.1)).1
    rw [index C place hS E, index C place hS E, Finset.image_subset_image_iff place.injective]
  · exact ((E.row c.1 (PointImageSemantics.belowEquiv C.scheme place hS c.1 d)).trans
      (PointImageSemantics.row C.scheme place hS C.rows c.1 d)).symm

end
end VaughtConjecture.Knight.NativePrivateFace
