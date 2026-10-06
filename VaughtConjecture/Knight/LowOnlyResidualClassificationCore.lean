/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyResidualCoverCore
public import VaughtConjecture.Knight.CharacteristicGradeBounds
public import VaughtConjecture.Knight.ModelEmpty
public import VaughtConjecture.Knight.RootedKarp
public import VaughtConjecture.Knight.FiniteHull

/-! # Cap-native rooted classification of the residual

A directional step needs source consistency, covering and a top-grade bound. The target
supplies consistency, finite-cut receiving, an eventual constant top-grade tail, and
flexibility. Two-sided comparison uses these data on each side and preserves the supplied
common root coordinatewise. No old-model reconstruction is used.

A constant tail here is `KnightRealization.IsCoinitial`: above every context is a context
whose every extension has the stated grade. The zero-grade converse is not part of this API.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyResidualClassification
open TypeTower StageType KnightRealization Value ExtOrd
noncomputable section
universe w
variable {α : LimitStage} {M₁ M₂ : Type w}
  {W₁ : KnightRealization α M₁} {W₂ : KnightRealization α M₂}

/-- Extend an exact common chart to cover a scheduled point on the first side.
Only the receiving side needs to be in the residual branch. -/
theorem exists_step_left_of_receiving
    (hcons₁ : W₁.IsExactParentConsistent) (hcov₁ : W₁.IsInitialSegmentCovering)
    (hcons₂ : W₂.IsExactParentConsistent) (hFC₂ : FiniteCutReceiving W₂) {K : ℕ}
    (hbound₁ : ∀ x : W₁.LabelledExt, x.type.topGrade ≤ K)
    (hcoin₂ : KnightRealization.IsCoinitial {x : W₂.LabelledExt | x.type.topGrade = K})
    (hKpos : 0 < K)
    (hres₂ : ∀ {k : ℕ} (B : Fin k ↪ M₂), ¬ TopSupportRigidCore.RigidCore W₂ B)
    (nd : CommonChartNode (A₁ := W₁) (A₂ := W₂)) (x : M₁) :
    ∃ (next : CommonChartNode (A₁ := W₁) (A₂ := W₂)) (emb : Fin nd.arity ↪ Fin next.arity),
      emb.trans next.tuple₁ = nd.tuple₁ ∧ emb.trans next.tuple₂ = nd.tuple₂ ∧
      ∃ i, next.tuple₁ i = x := by
  classical
  by_cases hx : x ∈ Set.range nd.tuple₁
  · obtain ⟨i, hi⟩ := hx
    exact ⟨nd, Function.Embedding.refl _, Function.Embedding.refl_trans _,
      Function.Embedding.refl_trans _, i, hi⟩
  -- Use the least actual support of the old chart and the requested point.
  obtain ⟨c, g, hg, _hull⟩ := FiniteHull.exists_hull_chart
    hcons₁ hcov₁ (snoc nd.tuple₁ x hx)
  let f : Fin nd.arity ↪ Fin c.arity := Fin.castSuccEmb.trans g
  have hfs : f.trans c.tuple = nd.tuple₁ := by
    change (Fin.castSuccEmb.trans g).trans c.tuple = _
    rw [Function.Embedding.trans_assoc, hg, castSuccEmb_trans_snoc]
  have hfp : typeMap f c.type = some nd.type := by
    have h := hcons₁ c.tuple c.type f c.eval_eq
    rw [hfs, nd.eval₁] at h
    exact h.symm
  have hPK : ∀ d, c.type.label d = ⊤ → c.type.scheme.scheme.grade d ≤ K := fun _ hd =>
    (le_csSup c.type.topGrades_bddAbove (grade_mem_topGrades hd)).trans (hbound₁ c)
  obtain ⟨u, hfu, hu⟩ := LowOnlyResidualReceiving.receive_cover_of_tail hcons₂ hFC₂ hcoin₂ hKpos
    hres₂ c.type hPK f
    nd.tuple₂ nd.type hfp nd.eval₂
  refine ⟨⟨c.arity, c.tuple, u, c.type, c.eval_eq, hu⟩, f, hfs, hfu,
    g (Fin.last nd.arity), ?_⟩
  have hlast := congrArg (fun t : Fin (nd.arity + 1) ↪ M₁ => t (Fin.last nd.arity)) hg
  simpa only [Function.Embedding.trans_apply, snoc_apply_last] using hlast

/-- Exact chart density follows from the constructed receiver on both sides. -/
theorem stepSupply_of_receiving (hcons₁ : W₁.IsExactParentConsistent)
    (hcov₁ : W₁.IsInitialSegmentCovering)
    (hFC₁ : FiniteCutReceiving W₁) (hcons₂ : W₂.IsExactParentConsistent)
    (hcov₂ : W₂.IsInitialSegmentCovering) (hFC₂ : FiniteCutReceiving W₂) {K : ℕ}
    (hcoin₁ : KnightRealization.IsCoinitial {x : W₁.LabelledExt | x.type.topGrade = K})
    (hcoin₂ : KnightRealization.IsCoinitial {x : W₂.LabelledExt | x.type.topGrade = K})
    (hKpos : 0 < K)
    (hres₁ : ∀ {k : ℕ} (B : Fin k ↪ M₁), ¬ TopSupportRigidCore.RigidCore W₁ B)
    (hres₂ : ∀ {k : ℕ} (B : Fin k ↪ M₂), ¬ TopSupportRigidCore.RigidCore W₂ B) :
    CommonChartStepSupply (A₁ := W₁) (A₂ := W₂) := by
  intro nd z
  rcases z with x | y
  · obtain ⟨next, emb, h₁, h₂, hx⟩ := exists_step_left_of_receiving hcons₁ hcov₁ hcons₂ hFC₂
      (topGrade_le_of_isCoinitial hcoin₁) hcoin₂ hKpos hres₂ nd x
    exact ⟨⟨next, emb, h₁, h₂, fun _ hx' => (Sum.inl.inj hx') ▸ hx,
      fun _ hy => absurd hy Sum.inl_ne_inr⟩⟩
  · obtain ⟨next, emb, h₂, h₁, hy⟩ := exists_step_left_of_receiving hcons₂ hcov₂ hcons₁ hFC₁
      (topGrade_le_of_isCoinitial hcoin₂) hcoin₁ hKpos hres₁
      (TopSupportRigidCore.swapNode nd) y
    exact ⟨⟨TopSupportRigidCore.swapNode next, emb, h₁, h₂,
      fun _ hx => absurd hx Sum.inr_ne_inl, fun _ hy' => (Sum.inr.inj hy') ▸ hy⟩⟩

/-- **Root-preserving residual classification**: in the positive finite-characteristic
residual, every common chart of two countable models extends to an isomorphism carrying the
one tuple onto the other coordinatewise. -/
theorem exists_iso_of_commonChart_of_receiving [Countable M₁] [Countable M₂]
    [Nonempty M₁] [Nonempty M₂]
    (hcons₁ : W₁.IsExactParentConsistent) (hcov₁ : W₁.IsInitialSegmentCovering)
    (hFC₁ : FiniteCutReceiving W₁) (hcons₂ : W₂.IsExactParentConsistent)
    (hcov₂ : W₂.IsInitialSegmentCovering) (hFC₂ : FiniteCutReceiving W₂) {K : ℕ}
    (hcoin₁ : KnightRealization.IsCoinitial {x : W₁.LabelledExt | x.type.topGrade = K})
    (hcoin₂ : KnightRealization.IsCoinitial {x : W₂.LabelledExt | x.type.topGrade = K})
    (hKpos : 0 < K)
    (hres₁ : ∀ {k : ℕ} (B : Fin k ↪ M₁), ¬ TopSupportRigidCore.RigidCore W₁ B)
    (hres₂ : ∀ {k : ℕ} (B : Fin k ↪ M₂), ¬ TopSupportRigidCore.RigidCore W₂ B)
    {k : ℕ} (t₁ : Fin k ↪ M₁) (t₂ : Fin k ↪ M₂) {p : S α.1 k}
    (h₁ : W₁.eval t₁ = some p) (h₂ : W₂.eval t₂ = some p) :
    ∃ e : W₁.Iso W₂, ∀ i, e.1 (t₁ i) = t₂ i :=
  exists_iso_of_commonChartStepSupply hcons₁ hcons₂ ⟨k, t₁, t₂, p, h₁, h₂⟩
    (stepSupply_of_receiving hcons₁ hcov₁ hFC₁ hcons₂ hcov₂ hFC₂ hcoin₁ hcoin₂ hKpos hres₁ hres₂)

/-- At any limit stage, at most one countable residual class has each positive
finite characteristic. -/
theorem nonempty_iso_of_receiving [Countable M₁] [Countable M₂]
    [Nonempty M₁] [Nonempty M₂]
    (hcons₁ : W₁.IsExactParentConsistent) (hcov₁ : W₁.IsInitialSegmentCovering)
    (hFC₁ : FiniteCutReceiving W₁) (hcons₂ : W₂.IsExactParentConsistent)
    (hcov₂ : W₂.IsInitialSegmentCovering) (hFC₂ : FiniteCutReceiving W₂) {K : ℕ}
    (hcoin₁ : KnightRealization.IsCoinitial {x : W₁.LabelledExt | x.type.topGrade = K})
    (hcoin₂ : KnightRealization.IsCoinitial {x : W₂.LabelledExt | x.type.topGrade = K})
    (hKpos : 0 < K)
    (hres₁ : ∀ {k : ℕ} (B : Fin k ↪ M₁), ¬ TopSupportRigidCore.RigidCore W₁ B)
    (hres₂ : ∀ {k : ℕ} (B : Fin k ↪ M₂), ¬ TopSupportRigidCore.RigidCore W₂ B) :
    Nonempty (W₁.Iso W₂) := by
  obtain ⟨p₁, hp₁⟩ := exists_eval_empty_of_structural hcons₁ hcov₁
  obtain ⟨p₂, hp₂⟩ := exists_eval_empty_of_structural hcons₂ hcov₂
  obtain rfl : p₁ = p₂ := Subsingleton.elim _ _
  obtain ⟨e, -⟩ := exists_iso_of_commonChart_of_receiving hcons₁ hcov₁ hFC₁
    hcons₂ hcov₂ hFC₂ hcoin₁ hcoin₂ hKpos hres₁ hres₂
    Function.Embedding.ofIsEmpty Function.Embedding.ofIsEmpty hp₁ hp₂
  exact ⟨e⟩

end
end VaughtConjecture.Knight.LowOnlyResidualClassification
