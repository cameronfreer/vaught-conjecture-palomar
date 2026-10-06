/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TopGradeStableCore

/-! # High common covers

Directedness and top-grade growth supply a common cover with a full-scope top
above any finite grade floor. This geometric construction computes no stable
value or source offset and requires only consistency and covering.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.KnightRealization
open StageType
universe w
variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-- Absorb a tuple and then grow past a prescribed grade floor. -/
theorem exists_high_common_cover (hc : R.IsExactParentConsistent)
    (hv : R.IsInitialSegmentCovering) (hg : R.HasTopGradeGrowth)
    (x : R.LabelledExt) {k : ℕ} (s : Fin k ↪ M) (B : ℕ) :
    ∃ z : R.LabelledExt, x ≤ z ∧
      (∃ g : Fin k ↪ Fin z.arity, g.trans z.tuple = s) ∧ B < z.type.topGrade ∧
      ∃ c : Cell z.type.scheme.scheme, z.type.scheme.scheme.scope c = Finset.univ ∧
        z.type.scheme.scheme.grade c = z.type.topGrade ∧ z.type.label c = ⊤ := by
  obtain ⟨y, hxy, g, hgu⟩ := exists_labelledExt_le hc hv x s
  obtain ⟨z, hhigh, hyz⟩ := hg B y
  change B < z.type.topGrade at hhigh
  have hxz := hxy.trans hyz
  obtain ⟨e, heu, _⟩ := hyz
  obtain ⟨c, hsc, hgr, htop⟩ := exists_topCell_of_topGrade_pos z.type (by omega)
  refine ⟨z, hxz, ⟨g.trans e, ?_⟩, hhigh, c, hsc, hgr, htop⟩
  rw [Function.Embedding.trans_assoc, heu, hgu]

end VaughtConjecture.Knight.KnightRealization
