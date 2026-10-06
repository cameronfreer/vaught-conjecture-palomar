/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HollowGrowthExactReceiving
public import VaughtConjecture.Knight.OnePointRootedExtension
public import VaughtConjecture.Knight.SelectedCommonCharts
public import VaughtConjecture.Knight.ModelBookkeeping

/-! # Exact rooted extension and comparison for hollow growth

The constructed exact receiver supplies finite rooted extension and hence
isomorphism of countable hollow growth models at the same stage. This producer
does not depend on seed counting or on a non-hollow prolongation theorem.
The seed-counting applications remain in `HollowGrowthCountability`.

The receiver works over every actual root and imposes no admissibility
restriction, so comparison selects all common actual charts: a requested point
is covered on its side and the finite donor is received exactly over the other
side's chart (`commonChartStepSupply`), and the direct selected-chart consumer
keeps the initial chart as its seed. No core invariant is carried.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.HollowGrowth
open TypeTower KnightRealization Cardinal
noncomputable section
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}

/-- Arbitrary cores, without any restriction on the candidate top pattern. -/
theorem onePointRootedExtension (hM : W.IsModel) (hg : W.HasTopGradeGrowth)
    (hh : W.IsHollow) {c : ℕ} (core : Fin c ↪ M) :
    OnePointRootedExtensionOver W core (AdmTop α) := by
  intro n t p _ hp q hq _
  obtain ⟨y, hy, he⟩ := HollowGrowthTemplate.receives_exactly hM hg hh t p hp q hq
  exact ⟨snoc t y hy, castSuccEmb_trans_snoc t y hy, he⟩

theorem rootedExtension (hM : W.IsModel) (hg : W.HasTopGradeGrowth)
    (hh : W.IsHollow) {c : ℕ} (core : Fin c ↪ M) :
    RootedExtensionOver W core (AdmTop α) :=
  rootedExtensionOver_of_onePoint hM.consistent (onePointRootedExtension hM hg hh core)

/-- **Finite exact receiving over an actual root.** Every rooted extension of the label of an
actual tuple is realized over that tuple. This is the one-point receiver iterated along visible
one-point enlargements (`rootedExtensionOver_of_onePoint`), with the tuple itself as the root and
the trivial admissibility; no core is carried. -/
theorem receives_finite_exactly (hM : W.IsModel) (hg : W.HasTopGradeGrowth) (hh : W.IsHollow)
    {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (hp : W.eval t = some p)
    {N : ℕ} (f : Fin n ↪ Fin N) (P : S α.1 N) (hP : typeMap f P = some p) :
    ∃ u : Fin N ↪ M, f.trans u = t ∧ W.eval u = some P :=
  rootedExtension hM hg hh t t p ⟨Function.Embedding.refl _, Function.Embedding.refl_trans _⟩
    hp f P hP trivial

/-- One side of the hollow chart step: cover a common chart's first tuple together with a
requested point by an actual chart of `V`, then receive that finite donor exactly over the
second tuple in `W`. -/
theorem exists_common_cover {M₁ M₂ : Type w}
    {V : KnightRealization α M₁} {W : KnightRealization α M₂}
    (hcV : V.IsExactParentConsistent) (hvV : V.IsInitialSegmentCovering) (hW : W.IsModel)
    (hgW : W.HasTopGradeGrowth) (hhW : W.IsHollow) {n : ℕ} {t₁ : Fin n ↪ M₁}
    {t₂ : Fin n ↪ M₂} {p : S α.1 n} (h₁ : V.eval t₁ = some p) (h₂ : W.eval t₂ = some p)
    (x : M₁) :
    ∃ (N : ℕ) (f : Fin n ↪ Fin N) (s : Fin N ↪ M₁) (u : Fin N ↪ M₂) (P : S α.1 N),
      f.trans s = t₁ ∧ f.trans u = t₂ ∧ V.eval s = some P ∧ W.eval u = some P ∧
        ∃ i, s i = x := by
  classical
  by_cases hx : x ∈ Set.range t₁
  · obtain ⟨i, hi⟩ := hx
    exact ⟨n, Function.Embedding.refl _, t₁, t₂, p, Function.Embedding.refl_trans _,
      Function.Embedding.refl_trans _, h₁, h₂, i, hi⟩
  · obtain ⟨k, s, hst, hsome⟩ := hvV (snoc t₁ x hx)
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hsome
    have hft : (Fin.castSuccEmb.trans (Fin.castAddEmb k)).trans s = t₁ := trans_snoc_cover hst
    have htm : typeMap (Fin.castSuccEmb.trans (Fin.castAddEmb k)) P = some p := by
      rw [← exactParent_typeMap hcV s P _ hP, hft]
      exact h₁
    obtain ⟨u, hut, huP⟩ := receives_finite_exactly hW hgW hhW t₂ p h₂ _ P htm
    exact ⟨_, _, s, u, P, hft, hut, hP, huP, cover_mem_range hst⟩

/-- **Every common actual chart absorbs every requested point.** Cover the chart together with
the point on the source side, then receive that finite donor exactly on the other side over the
chart's actual root. -/
theorem commonChartStepSupply {M₁ M₂ : Type w}
    {V : KnightRealization α M₁} {W : KnightRealization α M₂}
    (hV : V.IsModel) (hW : W.IsModel)
    (hgV : V.HasTopGradeGrowth) (hgW : W.HasTopGradeGrowth)
    (hhV : V.IsHollow) (hhW : W.IsHollow) :
    CommonChartStepSupply (A₁ := V) (A₂ := W) := by
  rintro nd (x | y)
  · obtain ⟨N, f, s, u, P, hs, hu, hsP, huP, i, hi⟩ :=
      exists_common_cover hV.consistent hV.covering hW hgW hhW nd.eval₁ nd.eval₂ x
    exact ⟨⟨⟨N, s, u, P, hsP, huP⟩, f, hs, hu, fun x' hx' => ⟨i, hi.trans (Sum.inl.inj hx')⟩,
      fun _ hy => absurd hy Sum.inl_ne_inr⟩⟩
  · obtain ⟨N, f, s, u, P, hs, hu, hsP, huP, i, hi⟩ :=
      exists_common_cover hW.consistent hW.covering hV hgV hhV nd.eval₂ nd.eval₁ y
    exact ⟨⟨⟨N, u, s, P, huP, hsP⟩, f, hu, hs, fun _ hx => absurd hx.symm Sum.inl_ne_inr,
      fun y' hy' => ⟨i, hi.trans (Sum.inr.inj hy')⟩⟩⟩

/-- Every common chart of two countable hollow growth models at the same stage extends to
an isomorphism carrying the one tuple onto the other coordinatewise.

All common actual charts are selected (`commonChartStepSupply`); the direct consumer keeps the
initial chart as its seed, so no core invariant is carried. -/
theorem exists_iso_of_commonChart {M₁ M₂ : Type w} [Countable M₁] [Countable M₂]
    {V : KnightRealization α M₁} {W : KnightRealization α M₂}
    (hV : V.IsModel) (hW : W.IsModel)
    (hgV : V.HasTopGradeGrowth) (hgW : W.HasTopGradeGrowth)
    (hhV : V.IsHollow) (hhW : W.IsHollow) {c : ℕ} (core₁ : Fin c ↪ M₁) (core₂ : Fin c ↪ M₂)
    {s : S α.1 c} (hs₁ : V.eval core₁ = some s) (hs₂ : W.eval core₂ = some s) :
    ∃ e : V.Iso W, ∀ i, e.1 (core₁ i) = core₂ i :=
  exists_iso_of_selectedCommonCharts hV.consistent hW.consistent (fun _ => True)
    ⟨c, core₁, core₂, s, hs₁, hs₂⟩ trivial
    (restrictedCommonChartStepSupply_true (commonChartStepSupply hV hW hgV hgW hhV hhW))

/-- Hollow growth models at the same stage are isomorphic when countable. -/
theorem nonempty_iso {M₁ M₂ : Type w} [Countable M₁] [Countable M₂]
    {V : KnightRealization α M₁} {W : KnightRealization α M₂}
    (hV : V.IsModel) (hW : W.IsModel)
    (hgV : V.HasTopGradeGrowth) (hgW : W.HasTopGradeGrowth)
    (hhV : V.IsHollow) (hhW : W.IsHollow) : Nonempty (V.Iso W) := by
  obtain ⟨sV, hsV⟩ := exists_eval_empty_at hV
  obtain ⟨sW, hsW⟩ := exists_eval_empty_at hW
  have hs : sW = sV := Subsingleton.elim _ _
  subst sW
  obtain ⟨e, -⟩ := exists_iso_of_commonChart hV hW hgV hgW hhV hhW
    Function.Embedding.ofIsEmpty Function.Embedding.ofIsEmpty hsV hsW
  exact ⟨e⟩

end
end VaughtConjecture.Knight.HollowGrowth
