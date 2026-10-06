/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyRetarget

/-! # Whole-root restoration after LOW-only donor retargeting

The face is an actual face of the original donor, not a reference-context surrogate.
Only its grade-at-most-`K` portion is restored at the retargeting cap; higher original
rows are retained using their unchanged capped targets. Empty faces need no lift.
The proof factors `CappedDonor.Ref.exists_retarget_restore` without its `Ref` geometry.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd AmalgamationPlan CappedDonor

variable {n : ℕ} {P : SemScheme n}

/-- The present part of an actual root scope. -/
def faceIndex (A : Finset (Fin n)) (j : ℕ) : Finset (Fin n) × ℕ :=
  (A, min A.card j)

theorem faceIndex_le (A : Finset (Fin n)) (j : ℕ) :
    GradedLe (faceIndex A j) (effC n j) :=
  ⟨Finset.subset_univ _, le_min (min_le_right _ _)
    ((min_le_left _ _).trans (by simpa using Finset.card_le_univ A))⟩

theorem faceIndex_mono (A : Finset (Fin n)) {i j : ℕ} (h : i ≤ j) :
    GradedLe (faceIndex A i) (faceIndex A j) := ⟨le_rfl, min_le_min_left _ h⟩

theorem faceIndex_mem {A : Finset (Fin n)} (hA : A ∈ P.scheme.plan) {j : ℕ}
    (hj : 0 < min A.card j) : faceIndex A j ∈ Plan.gradedPlan P.scheme.plan :=
  Plan.mem_gradedPlan.mpr ⟨hA, hj, min_le_left _ _⟩

theorem faceIndex_absent {A : Finset (Fin n)} {j : ℕ} (h : ¬ 0 < min A.card j)
    (d : P.scheme.below (faceIndex A j)) : False :=
  h ((P.scheme.grade_pos d.1).trans_le d.2.2)

/-- Restore an arbitrary lawful whole-root prescription after retargeting designated tops.
No second scheme, receiving reference, or output bountifulness is an input. -/
theorem RetargetData.exists_retarget_restore
    {p : Cell P.scheme → ExtOrd} (hp : RespectsSemantics P.rows p)
    {K j : ℕ} (hK : 0 < K) (hn : 0 < n) (hj : K ≤ j)
    (ht : ∀ d, p d = ⊤ → P.scheme.grade d ≤ K)
    {u : P.scheme.below (effC n j) → ExtOrd} {b η : ExtOrd}
    (hu : RetargetData (p := p) (K := K) u b η)
    {A : Finset (Fin n)} (hA : A ∈ P.scheme.plan)
    {v : P.scheme.below (faceIndex A j) → ExtOrd}
    (hv : RespectsSemanticsBelow P.rows (faceIndex A j) v)
    (hnon : ∀ a, p a.1 ≠ ⊤ → v a = u (CellScheme.below.mono (faceIndex_le A j) a))
    (htop : ∀ a, p a.1 = ⊤ → η ≤ v a) :
    ∃ u' : P.scheme.below (effC n j) → ExtOrd,
      RespectsSemanticsBelow P.rows (effC n j) u' ∧
      (∀ d, p d.1 ≠ ⊤ → u' d = u d) ∧ (∀ d, p d.1 = ⊤ → η ≤ u' d) ∧
      ∀ a, u' (CellScheme.below.mono (faceIndex_le A j) a) = v a := by
  have hw := hu.retargetTops_respects hp ht
  have hKj : GradedLe (effC n K) (effC n j) := ⟨le_rfl, min_le_min_right _ hj⟩
  have hwK := hw.mono hKj
  have hηK : SelfVis (effC n K).2 η := hu.η_vis.mono (min_le_left _ _)
  have hrest : ∃ w : P.scheme.below (effC n K) → ExtOrd,
      RespectsSemanticsBelow P.rows (effC n K) w ∧
      (∀ d, min (w d) η = min (retargetTops (p := p) η u
        (CellScheme.below.mono hKj d)) η) ∧
      ∀ a : P.scheme.below (faceIndex A K),
        w (CellScheme.below.mono (faceIndex_le A K) a) =
          v (CellScheme.below.mono (faceIndex_mono A hj) a) := by
    by_cases hk : 0 < min A.card K
    · apply P.bountiful.extend (faceIndex_mem hA hk) (effC_mem hK hn) (faceIndex_le A K)
        (hv.mono (faceIndex_mono A hj)) hwK hηK
      intro a
      by_cases hat : p a.1 = ⊤
      · rw [retargetTops_of_top η u hat, min_self]
        exact (min_eq_right (htop _ hat)).symm
      · rw [retargetTops_of_nonTop η u hat]
        exact congrArg (fun x => min x η)
          (hnon (CellScheme.below.mono (faceIndex_mono A hj) a) hat).symm
    · exact ⟨_, hwK, fun _ => rfl, fun a => (faceIndex_absent hk a).elim⟩
  obtain ⟨w, hw, hcap, hface⟩ := hrest
  have hlowNon : ∀ d : P.scheme.below (effC n K), p d.1 ≠ ⊤ →
      w d = u (CellScheme.below.mono hKj d) := by
    intro d hd
    have h := hcap d
    rw [retargetTops_of_nonTop η u hd] at h
    exact eq_of_capAgree_of_lt h.symm ((hu.nonTop_lt _ hd).trans_le hu.b_le_η)
  have hlowTop : ∀ d : P.scheme.below (effC n K), p d.1 = ⊤ → η ≤ w d := by
    intro d hd
    have h := hcap d
    rw [retargetTops_of_top η u hd, min_self] at h
    exact h.symm ▸ min_le_left _ _
  have hhighNon : ∀ d : P.scheme.below (effC n j),
      ¬ GradedLe (P.scheme.cell d.1) (effC n K) → p d.1 ≠ ⊤ := by
    intro d hd htop
    exact hd ⟨Finset.subset_univ _, le_min (ht d.1 htop) (gradeC_le d.1)⟩
  refine ⟨glueSection w u, hu.respects.glue hKj rfl hw ?_, ?_, ?_, ?_⟩
  · intro Sig hS d hd
    have hSn := hhighNon Sig hS
    by_cases hdt : p d.1 = ⊤
    · rw [min_eq_right ((hu.nonTop_lt Sig hSn).le.trans (hu.b_le_η.trans
        (hlowTop ⟨d.1, hd⟩ hdt))),
        min_eq_right ((hu.nonTop_lt Sig hSn).le.trans (hu.top_ge _ hdt))]
    · rw [hlowNon ⟨d.1, hd⟩ hdt]; rfl
  · intro d hd
    by_cases h : GradedLe (P.scheme.cell d.1) (effC n K)
    · rw [glueSection_of_le w u h, hlowNon ⟨d.1, h⟩ hd]; rfl
    · rw [glueSection_of_not_le w u h]
  · intro d hd
    have h : GradedLe (P.scheme.cell d.1) (effC n K) :=
      ⟨Finset.subset_univ _, le_min (ht d.1 hd) (gradeC_le d.1)⟩
    rw [glueSection_of_le w u h]
    exact hlowTop ⟨d.1, h⟩ hd
  · intro a
    by_cases hK : P.scheme.grade a.1 ≤ K
    · have hg : GradedLe (P.scheme.cell a.1) (effC n K) :=
        ⟨Finset.subset_univ _, le_min hK (gradeC_le a.1)⟩
      rw [glueSection_of_le w u hg]
      exact hface ⟨a.1, a.2.1, le_min (a.2.2.trans (min_le_left _ _)) hK⟩
    · have hg : ¬ GradedLe (P.scheme.cell a.1) (effC n K) := fun hg =>
        hK (hg.2.trans (min_le_left _ _))
      rw [glueSection_of_not_le w u hg]
      exact (hnon a fun ht' => hK (ht a.1 ht')).symm

/-- The retarget-and-restore operation preserves every external cap once both the
old and repaired top values lie above it. In particular the retargeting floor may
be strictly above this external cap. -/
theorem RetargetData.exists_retarget_restore_caps
    {p : Cell P.scheme → ExtOrd} (hp : RespectsSemantics P.rows p)
    {K j : ℕ} (hK : 0 < K) (hn : 0 < n) (hj : K ≤ j)
    (ht : ∀ d, p d = ⊤ → P.scheme.grade d ≤ K)
    {u : P.scheme.below (effC n j) → ExtOrd} {b η γ : ExtOrd}
    (hu : RetargetData (p := p) (K := K) u b η) (hγη : γ ≤ η)
    (hold : ∀ d, p d.1 = ⊤ → γ ≤ u d)
    {A : Finset (Fin n)} (hA : A ∈ P.scheme.plan)
    {v : P.scheme.below (faceIndex A j) → ExtOrd}
    (hv : RespectsSemanticsBelow P.rows (faceIndex A j) v)
    (hnon : ∀ a, p a.1 ≠ ⊤ → v a = u (CellScheme.below.mono (faceIndex_le A j) a))
    (htop : ∀ a, p a.1 = ⊤ → η ≤ v a) :
    ∃ u' : P.scheme.below (effC n j) → ExtOrd,
      RespectsSemanticsBelow P.rows (effC n j) u' ∧
      (∀ d, min (u' d) γ = min (u d) γ) ∧
      (∀ d, p d.1 ≠ ⊤ → u' d = u d) ∧ (∀ d, p d.1 = ⊤ → η ≤ u' d) ∧
      ∀ a, u' (CellScheme.below.mono (faceIndex_le A j) a) = v a := by
  obtain ⟨u', hu', hnon', htop', hface⟩ :=
    hu.exists_retarget_restore hp hK hn hj ht hA hv hnon htop
  refine ⟨u', hu', ?_, hnon', htop', hface⟩
  intro d
  by_cases hd : p d.1 = ⊤
  · rw [min_eq_right (hγη.trans (htop' d hd)), min_eq_right (hold d hd)]
  · rw [hnon' d hd]

end VaughtConjecture.Knight.LowOnly
