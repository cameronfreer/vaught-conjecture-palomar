/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyFaceRestoration
public import VaughtConjecture.Knight.CappedDonorRelease

/-! # Private source gaps independently of receiving reference records

This is precisely the original-row data needed for LOW-only frontier release. There is
no upper threshold, reference-block inventory, or inequality between the two facet arities.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd SharpWitnessComposition AmalgamationPlan CappedDonor

/-- A private owner and a strictly lower rounded source on its actual row. -/
structure SourceGap {n : ℕ} (C : SemScheme n) (K : ℕ) where
  c : Cell C.scheme
  c_grade : C.scheme.grade c = K
  r : C.scheme.below (C.scheme.cell c)
  gap_c : extVisibilityReplace (C.rows.E c r) K K <
    C.rows.E c ⟨c, GradedLe.refl _⟩

namespace SourceGap

variable {n K : ℕ} {C : SemScheme n} (L : SourceGap C K)

abbrev Dom := C.scheme.below (C.scheme.cell L.c)

def cL : L.Dom := ⟨L.c, GradedLe.refl _⟩

include L in
theorem K_pos : 0 < K := (C.scheme.grade_pos L.c).trans_eq L.c_grade

include L in
theorem K_le : K ≤ n := L.c_grade.symm.trans_le (gradeC_le L.c)

theorem grade_dom (d : L.Dom) : C.scheme.grade d.1 ≤ K := d.2.2.trans_eq L.c_grade

noncomputable def h : ExtOrd := extVisibilityReplace (C.rows.E L.c L.r) K K

theorem h_selfVis : SelfVis K L.h := TopSupport.selfVis_evr_self K _

theorem h_lt_c : L.h < C.rows.E L.c L.cL := L.gap_c

theorem srcE_r_le_h : C.rows.E L.c L.r ≤ L.h := TopSupport.le_evr_self _ K

noncomputable def e (v : L.Dom → ExtOrd) : ExtOrd :=
  min (v L.cL) (extVisibilityReplace (v L.r) K K)

theorem e_le_c (v : L.Dom → ExtOrd) : L.e v ≤ v L.cL := min_le_left _ _

theorem e_min {γ : ExtOrd} (hγ : SelfVis K γ) (v : L.Dom → ExtOrd) :
    L.e (fun d => min (v d) γ) = min (L.e v) γ := by
  unfold e
  rw [evr_min_of_selfVis hγ le_rfl le_rfl, min_min_min_comm, min_self]

theorem c_selfVis {v : L.Dom → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) v) :
    SelfVis K (v L.cL) := by
  have h := (hv.orderly L.cL).symm
  change SelfVis (C.scheme.grade L.c) (v L.cL) at h
  rwa [L.c_grade] at h

theorem e_selfVis {v : L.Dom → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) v) : SelfVis K (L.e v) :=
  selfVis_min (L.c_selfVis hv) (TopSupport.selfVis_evr_self K _)

theorem exists_witness {v : L.Dom → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) v) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop K) τ ∧ (∀ x, τ x ≤ v L.cL) ∧
      ∀ d : L.Dom, τ (C.rows.E L.c d) = min (v d) (v L.cL) := by
  have h := exists_bounded_exact_capped_witness (grade := fun d : L.Dom => C.scheme.grade d.1)
    (c := L.cL) (p := v) (fun d => d.2.2) (hv.orderly L.cL).symm (hv.locality L.cL)
  have hg : C.scheme.grade L.cL.1 = K := L.c_grade
  rwa [hg] at h

theorem e_eq_read {v : L.Dom → ExtOrd} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop K) τ)
    (hread : ∀ d : L.Dom, τ (C.rows.E L.c d) = min (v d) (v L.cL))
    (hvis : SelfVis K (v L.cL)) : L.e v = τ L.h := by
  unfold e h
  rw [hτ.comm_gTop _ le_rfl, hread, evr_min_of_selfVis hvis le_rfl le_rfl, min_comm]

/-- The original strict gap, not the numerical top flag, supplies this bound. -/
theorem e_le_of_gap {v : L.Dom → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) v)
    (d : L.Dom) (hd : L.h < C.rows.E L.c d) : L.e v ≤ v d := by
  obtain ⟨τ, hτ, -, hread⟩ := L.exists_witness hv
  rw [L.e_eq_read hτ hread (L.c_selfVis hv)]
  exact (hτ.mono hd.le).trans ((hread d).le.trans (min_le_left _ _))

theorem domLe {j : ℕ} (hj : K ≤ j) : GradedLe (C.scheme.cell L.c) (effC n j) :=
  ⟨Finset.subset_univ _, L.c_grade.trans_le (le_min hj L.K_le)⟩

def lowD {j : ℕ} (hj : K ≤ j) (v : C.scheme.below (effC n j) → ExtOrd)
    (d : L.Dom) : ExtOrd := v (CellScheme.below.mono (L.domLe hj) d)

theorem lowD_respects {j : ℕ} (hj : K ≤ j) {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) :
    RespectsSemanticsBelow C.rows (C.scheme.cell L.c) (L.lowD hj v) := hv.mono (L.domLe hj)

def cC {j : ℕ} (hj : K ≤ j) : C.scheme.below (effC n j) :=
  CellScheme.below.mono (L.domLe hj) L.cL

def rC {j : ℕ} (hj : K ≤ j) : C.scheme.below (effC n j) :=
  CellScheme.below.mono (L.domLe hj) L.r

noncomputable def eC {j : ℕ} (hj : K ≤ j) (v : C.scheme.below (effC n j) → ExtOrd) : ExtOrd :=
  L.e (L.lowD hj v)

theorem le_r_of_lt_e {v : L.Dom → ExtOrd} {γ : ExtOrd} (hγ : SelfVis K γ)
    (he : γ < L.e v) : γ ≤ v L.r := by
  by_contra hlt
  have h1 : extVisibilityReplace (v L.r) K K ≤ γ :=
    evr_le_of_le_selfVis hγ le_rfl le_rfl (not_le.mp hlt).le
  exact absurd ((he.trans_le (min_le_right _ _)).trans_le h1) (lt_irrefl _)

end SourceGap

end VaughtConjecture.Knight.LowOnly
