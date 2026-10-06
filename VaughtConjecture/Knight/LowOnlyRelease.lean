/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyFrontier

/-! # Exact LOW-only frontier release with literal whole-root retention

The actual private source gap and the designated root-top predicate suffice. The proof
reuses the scalar release witness from `CappedDonorRelease`, but constructs the section
and both original-scheme bountifulness calls without a `Ref` or `LowRef`.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly.SourceGap

open Transform Value ExtOrd SharpWitnessComposition AmalgamationPlan CappedDonor
open CappedDonor.Ref.LowRef

variable {n K : ℕ} {C : SemScheme n} (L : SourceGap C K)

/-- A positive-cap frontier release on the unchanged private scheme. The root may have
arbitrarily high grades; only its low part passes through the owner's cap. -/
theorem exists_release {j : ℕ} (hj : K ≤ j)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ) (hγpos : γ ≠ ⊥) (he : γ < L.eC hj v)
    {A : Finset (Fin n)} (hA : A ∈ C.scheme.plan) (hAc : A ⊆ C.scheme.scope L.c)
    (T : Cell C.scheme → Prop)
    (htop : ∀ a : C.scheme.below (faceIndex A j), T a.1 → C.scheme.grade a.1 ≤ K)
    (hgap : ∀ (a : C.scheme.below (faceIndex A K))
      (ha : GradedLe (C.scheme.cell a.1) (C.scheme.cell L.c)),
      T a.1 → L.h < C.rows.E L.c ⟨a.1, ha⟩)
    (hshield : ∀ a : C.scheme.below (faceIndex A j), ¬ T a.1 →
      v (CellScheme.below.mono (faceIndex_le A j) a) < γ) :
    ∃ v' : C.scheme.below (effC n j) → ExtOrd,
      RespectsSemanticsBelow C.rows (effC n j) v' ∧
      (∀ a : C.scheme.below (faceIndex A j),
        v' (CellScheme.below.mono (faceIndex_le A j) a) =
          v (CellScheme.below.mono (faceIndex_le A j) a)) ∧
      (∀ d, min (v' d) γ = min (v d) γ) ∧
      v' (L.rC hj) = γ ∧ v (L.cC hj) ≤ v' (L.cC hj) ∧ L.eC hj v' = γ := by
  have hγK : SelfVis K γ := hγ.mono (le_min hj L.K_le)
  set w₀ := L.lowD hj v
  have hw₀ := L.lowD_respects hj hv
  have hLvis := L.c_selfVis hw₀
  have hγL : γ < w₀ L.cL := he.trans_le (L.e_le_c _)
  have hγr : γ ≤ w₀ L.r := L.le_r_of_lt_e hγK he
  obtain ⟨τ, hτ, -, hread⟩ := L.exists_witness hw₀
  have hν : Witness (gTop K) (releaseShifter τ L.h γ) :=
    releaseShifter_witness hτ L.h_selfVis hγK hγpos
  set w : L.Dom → ExtOrd := fun d => releaseShifter τ L.h γ (C.rows.E L.c d)
  have hE := C.consistent L.c
  have hcapL : SelfVis (C.scheme.cell L.c).2 (w₀ L.cL) := by
    change SelfVis (C.scheme.grade L.c) (w₀ L.cL)
    rw [L.c_grade]; exact hLvis
  have ht : RespectsSemanticsBelow C.rows (C.scheme.cell L.c)
      (fun d => τ (C.rows.E L.c d)) := by
    have heq : (fun d : L.Dom => τ (C.rows.E L.c d)) =
        fun d => min (w₀ d) (w₀ L.cL) := funext hread
    rw [heq]; exact hw₀.cap hcapL
  have hw : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) w := by
    refine (map_respects_iff_rowBlockBottom hE L.grade_dom (boundedMap_of_witness hν)).mpr ?_
    refine rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects ht) fun d => ?_
    exact releaseShifter_eq_bot_iff hγpos _
  have hwc : w L.cL = w₀ L.cL := by
    change releaseShifter τ L.h γ (C.rows.E L.c L.cL) = _
    rw [releaseShifter_of_lt L.h_lt_c, hread, min_self]
  have hwr : w L.r = γ := by
    change releaseShifter τ L.h γ (C.rows.E L.c L.r) = _
    rw [releaseShifter_of_le L.srcE_r_le_h, hread]
    exact min_eq_right (le_min hγr hγL.le)
  have hwcap : ∀ d, min (w d) γ = min (w₀ d) γ := by
    intro d
    change min (releaseShifter τ L.h γ (C.rows.E L.c d)) γ = _
    unfold releaseShifter
    split_ifs
    · rw [hread, min_assoc, min_self, min_assoc, min_eq_right hγL.le]
    · rw [hread, min_assoc, min_eq_right hγL.le]
  have hfaceLe : GradedLe (faceIndex A K) (C.scheme.cell L.c) :=
    ⟨hAc, (min_le_right _ _).trans_eq L.c_grade.symm⟩
  have hwface : ∀ a : C.scheme.below (faceIndex A K),
      w (CellScheme.below.mono hfaceLe a) =
        min (w₀ (CellScheme.below.mono hfaceLe a)) (w₀ L.cL) := by
    intro a
    change releaseShifter τ L.h γ (C.rows.E L.c (CellScheme.below.mono hfaceLe a)) = _
    by_cases hat : T a.1
    · have hlt : L.h < C.rows.E L.c (CellScheme.below.mono hfaceLe a) :=
        hgap a (a.2.trans hfaceLe) hat
      rw [releaseShifter_of_lt hlt, hread]
    · have hlt : w₀ (CellScheme.below.mono hfaceLe a) < γ :=
        hshield (CellScheme.below.mono (faceIndex_mono A hj) a) hat
      unfold releaseShifter
      split_ifs
      · rw [hread, min_eq_left ((min_le_left _ _).trans hlt.le)]
      · rw [hread]
  have hrest : ∃ w' : L.Dom → ExtOrd,
      RespectsSemanticsBelow C.rows (C.scheme.cell L.c) w' ∧
      (∀ d, min (w' d) (w₀ L.cL) = min (w d) (w₀ L.cL)) ∧
      ∀ a : C.scheme.below (faceIndex A K),
        w' (CellScheme.below.mono hfaceLe a) = w₀ (CellScheme.below.mono hfaceLe a) := by
    by_cases hk : 0 < min A.card K
    · apply C.bountiful.extend (faceIndex_mem hA hk) (C.scheme.cell_mem L.c)
        hfaceLe (hw₀.mono hfaceLe) hw hcapL
      intro a
      rw [hwface, min_assoc, min_self]
    · exact ⟨w, hw, fun _ => rfl, fun a => (faceIndex_absent hk a).elim⟩
  obtain ⟨w', hw', hcap', hface'⟩ := hrest
  have hw'r : w' L.r = γ := by
    have h := hcap' L.r
    rw [hwr, min_eq_left hγL.le] at h
    exact eq_of_capAgree_of_lt (x := γ) (by rw [min_eq_left hγL.le]; exact h.symm) hγL
  have hw'c : w₀ L.cL ≤ w' L.cL := by
    have h := hcap' L.cL
    rw [hwc, min_self] at h
    exact h.symm ▸ min_le_left _ _
  have hw'cap : ∀ d, min (w' d) γ = min (w₀ d) γ := by
    intro d
    calc min (w' d) γ = min (min (w' d) (w₀ L.cL)) γ := by
            rw [min_assoc, min_eq_right hγL.le]
      _ = min (min (w d) (w₀ L.cL)) γ := by rw [hcap' d]
      _ = min (w d) γ := by rw [min_assoc, min_eq_right hγL.le]
      _ = min (w₀ d) γ := hwcap d
  obtain ⟨v', hv', hcap, hlow⟩ := C.bountiful.extend (C.scheme.cell_mem L.c)
    (effC_mem (L.K_pos.trans_le hj) (L.K_pos.trans_le L.K_le))
    (L.domLe hj) hw' hv hγ (fun d => (hw'cap d).symm)
  have hlowD : L.lowD hj v' = w' := funext hlow
  refine ⟨v', hv', ?_, hcap, ?_, ?_, ?_⟩
  · intro a
    by_cases hK : C.scheme.grade a.1 ≤ K
    · let aK : C.scheme.below (faceIndex A K) :=
        ⟨a.1, a.2.1, le_min (a.2.2.trans (min_le_left _ _)) hK⟩
      change L.lowD hj v' (CellScheme.below.mono hfaceLe aK) =
        L.lowD hj v (CellScheme.below.mono hfaceLe aK)
      rw [hlowD]
      exact hface' aK
    · exact eq_of_capAgree_of_lt (hcap _).symm (hshield a fun ht => hK (htop a ht))
  · change L.lowD hj v' L.r = γ
    rw [hlowD, hw'r]
  · change L.lowD hj v L.cL ≤ L.lowD hj v' L.cL
    rw [hlowD]; exact hw'c
  · unfold eC
    rw [hlowD]
    unfold e
    rw [hw'r, evr_eq_self_of_selfVis hγK, min_eq_right (hγL.le.trans hw'c)]

end VaughtConjecture.Knight.LowOnly.SourceGap
