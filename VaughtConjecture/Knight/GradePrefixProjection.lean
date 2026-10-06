/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoherentGradeCaps

/-! # Lawful projection from lawful grade-capped prefixes

The raw vector need not be lawful or belong to a single admitted catalogue.
It suffices that its cap at each grade is lawful through that grade, with
antitone heights. The projected vector uses the height at each cell's own
grade. This is the finite semantic observation of new72 §5.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GradePrefixProjection
open Transform Value ExtOrd AmalgamationPlan
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ} {ρ : Cell D → ExtOrd} {H : ℕ → ExtOrd}

/-- At an owner the projected locality target is exactly the target of its
lawful grade prefix; availability also stays within that single grade. -/
theorem respectsBelow (ha : Antitone H)
    (hp : ∀ j ≤ BJ.2, RespectsSemanticsBelow sem (BJ.1, j)
      (fun d => min (ρ d.1) (H j))) :
    RespectsSemanticsBelow sem BJ (fun d => min (ρ d.1) (H (D.grade d.1))) where
  orderly d := (hp (D.grade d.1) d.2.2).orderly ⟨d.1, d.2.1, le_rfl⟩
  locality c := by
    have ht := (hp (D.grade c.1) c.2.2).locality ⟨c.1, c.2.1, le_rfl⟩
    refine transformsTo_congr rfl rfl ?_ ht
    funext d
    change min (min (ρ d.1) (H (D.grade c.1))) (min (ρ c.1) (H (D.grade c.1))) =
      min (min (ρ d.1) (H (D.grade d.1))) (min (ρ c.1) (H (D.grade c.1)))
    have hdc : H (D.grade c.1) ≤ H (D.grade d.1) := ha d.2.2
    rw [min_min_min_comm, min_self, min_min_min_comm, min_eq_right hdc]
  availability c e hs hg := by
    obtain ⟨w, hw, hle⟩ := (hp (D.grade c.1) c.2.2).availability
      ⟨c.1, c.2.1, le_rfl⟩ ⟨e.1, e.2.1, hg.symm.le⟩ hs hg
    refine ⟨⟨w.1, w.2.1, w.2.2.trans c.2.2⟩, hw, ?_⟩
    have hgrade : D.grade w.1 = D.grade c.1 := (congrArg Prod.snd hw).trans hg.symm
    change min (ρ c.1) (H (D.grade c.1)) ≤ min (ρ w.1) (H (D.grade w.1))
    rw [hgrade]
    exact hle

/-- The whole-scheme form needs only its finite height bound. It assumes no
visibility of the raw heights beyond what the lawful prefixes already supply. -/
theorem respects {K : ℕ} (hK : ∀ d : Cell D, D.grade d ≤ K) (ha : Antitone H)
    (hp : ∀ j ≤ K, RespectsSemanticsBelow sem (A, j) (fun d => min (ρ d.1) (H j))) :
    RespectsSemantics sem (fun d => min (ρ d) (H (D.grade d))) :=
  (respectsBelow (BJ := (A, K)) ha hp).toRespects fun d =>
    ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), hK d⟩

/-- The complete original-coordinate cap is retained precisely when its
reading lies below the coordinate's projected height. -/
theorem cap_receipts_iff (γ : ExtOrd) :
    (∀ d : D.below BJ, min (min (ρ d.1) (H (D.grade d.1))) γ = min (ρ d.1) γ) ↔
      ∀ d : D.below BJ, min (ρ d.1) γ ≤ H (D.grade d.1) := by
  simp only [min_right_comm (ρ _), min_eq_left_iff]

end VaughtConjecture.Knight.GradePrefixProjection
