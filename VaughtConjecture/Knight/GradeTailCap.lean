/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FullScopeBountiful

/-! # Explicit grade-tail capping

This exposes the unchanged-prefix special case of the construction in
`bountiful_full_scope`. Grades at most `i` stay literal; only larger grades
are capped. In particular the cap need not fix the lower-grade values.
No source row is changed and no extension-existence hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {BJ : Finset ι × ℕ}

/-- Keep the lower-grade prefix, capping only the grade tail. -/
noncomputable def gradeTailCap (i : ℕ) (η : ExtOrd)
    (q : D.below BJ → ExtOrd) (d : D.below BJ) : ExtOrd :=
  if D.grade d.1 ≤ i then q d else min (q d) η

/-- Explicit respect preservation, including the original availability witnesses. -/
theorem RespectsSemanticsBelow.gradeTailCap {sem : Semantics D}
    {q : D.below BJ → ExtOrd} (hq : RespectsSemanticsBelow sem BJ q)
    (i : ℕ) {η : ExtOrd} (hη : SelfVis BJ.2 η) :
    RespectsSemanticsBelow sem BJ (gradeTailCap i η q) := by
  classical
  by_cases hi : i ≤ BJ.2
  · let u : D.below BJ → ExtOrd := fun d => min (q d) η
    let v : D.below (BJ.1, i) → ExtOrd :=
      fun d => q (GradeTailRestoration.lowerIncl hi d)
    have hv : RespectsSemanticsBelow sem (BJ.1, i) v :=
      hq.mono (show GradedLe (BJ.1, i) BJ from ⟨Finset.Subset.refl _, hi⟩)
    have hcap : ∀ d, min (v d) η = min (u (GradeTailRestoration.lowerIncl hi d)) η := by
      intro d
      dsimp only [v, u]
      rw [min_assoc, min_self]
    have he : Knight.gradeTailCap i η q = GradeTailRestoration.splice u v := by
      funext d
      dsimp only [Knight.gradeTailCap, GradeTailRestoration.splice]
      split_ifs <;> rfl
    rw [he]
    exact GradeTailRestoration.splice_respects hi (hq.cap hη) hv
      (fun _ _ => min_le_right _ _) hcap
  · have he : Knight.gradeTailCap i η q = q := by
      funext d
      exact ite_eq_left (d.2.2.trans (not_le.mp hi).le)
    rw [he]
    exact hq

theorem gradeTailCap_eq {q : D.below BJ → ExtOrd} {i : ℕ} {η : ExtOrd}
    {d : D.below BJ} (hd : D.grade d.1 ≤ i) : gradeTailCap i η q d = q d :=
  ite_eq_left hd

theorem gradeTailCap_capped (q : D.below BJ → ExtOrd) (i : ℕ) (η : ExtOrd)
    (d : D.below BJ) : min (gradeTailCap i η q d) η = min (q d) η := by
  unfold gradeTailCap
  split_ifs <;> simp only [min_assoc, min_self]

end VaughtConjecture.Knight
