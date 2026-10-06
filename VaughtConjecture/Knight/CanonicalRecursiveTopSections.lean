/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics

/-! # Literal-top boundary sections on the constructed recursive carrier

Finite outer coding gives a proper source profile; decoding recovers every
current old-boundary coordinate literally. No lower lifting or output
bountifulness is assumed. Future old fields outside the target are not part
of this prescription.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveTopSections
open Transform Value ExtOrd CanonicalRecursiveContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : ∀ d : Cell D, D.scope d ≠ A)
variable (n : ℕ) (hA : n + 3 ≤ A.card)

def boundaryTarget (d : D.below (A, n + 3)) : (carrier sem n hA).below (A, n + 3) :=
  ⟨boundary sem n hA d.1, by
    rw [CanonicalRecursiveInventory.boundary_cell]
    exact d.2⟩

/-- Arbitrary lawful current boundary values, including literal top, extend
through every recursive controller. This is section supply, not cap lifting. -/
theorem exists_section {p : D.below (A, n + 3) → ExtOrd}
    (hpr : RespectsSemanticsBelow sem (A, n + 3) p) :
    ∃ r : (carrier sem n hA).below (A, n + 3) → ExtOrd,
      RespectsSemanticsBelow (CanonicalRecursiveSemantics.rows sem hp n hA) (A, n + 3) r ∧
      ∀ d, r (boundaryTarget sem n hA d) = p d := by
  classical
  obtain ⟨S, u, hu, _, hcode, hdecode⟩ := hpr.exists_coded_representative
    (fun d => d.2.2) (le_refl (Nat.card (D.below (A, n + 3))))
  let v : Cell D → ExtOrd := fun d => if hd : D.grade d ≤ n + 3 then
    u ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩ else ⊥
  have hv (d : D.below (A, n + 3)) : v d.1 = u d := dite_eq_left d.2.2
  have hvr : RespectsSemanticsBelow sem (A, n + 3) (fun d => v d.1) := by
    simpa only [hv] using hu
  have hvt (d : Cell D) : v d ≠ ⊤ := by
    dsimp only [v]
    split_ifs with hd
    · rcases mem_codedAlphabet_iff.mp
        (hcode ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩) with
        hb | ⟨b, i, _, _, he⟩
      · exact hb.trans_ne bot_ne_top
      · exact he.trans_ne (ofOrd_ne_top _)
    · exact bot_ne_top
  let T := CanonicalRecursiveSemantics.state sem hp n hA
  let w := T.sectionOf le_rfl hvr hvt ∅ ⊤
  have hw : RespectsSemanticsBelow T.rows (A, n + 3) (fun d => w d.1) :=
    T.section_lawful le_rfl hvr hvt (by simp) (extVisibilityReplace_top _ _)
  refine ⟨fun d => canonicalDecoder S (n + 3) (w d.1),
    hw.decoded S (fun d => d.2.2), ?_⟩
  intro d
  have hr := T.section_boundary le_rfl hvr hvt (G := ∅) (by simp)
    (extVisibilityReplace_top (n + 3) (n + 3)) d.1
  change canonicalDecoder S (n + 3) (w (boundary sem n hA d.1)) = p d
  exact (congrArg (canonicalDecoder S (n + 3)) (hr.trans (hv d))).trans (hdecode d)

end
end VaughtConjecture.Knight.CanonicalRecursiveTopSections
