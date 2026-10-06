/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyResidualClassificationCore
public import VaughtConjecture.Knight.TopSupportRigidCore
public import VaughtConjecture.Knight.TopGradeDichotomy
public import VaughtConjecture.Knight.CountableTerminalFibres
public import VaughtConjecture.CountableCover

/-! # Counting terminal classes directly from top-grade behaviour

At a countable stage the models are covered by countably many conditions, each met by
at most one isomorphism class:

* an actual globally rigid core of a given finite type (rigid-core comparison);
* no globally rigid core, and top grade eventually a given `K` (cap-native residual
  comparison, which consumes the coinitial top-grade tail itself);
* hollow top-grade growth (hollow-growth comparison).

The top-grade dichotomy places every model without a core in the second or third
condition. Eventual top grade zero leaves no actual top cell, so the empty tuple is then a
globally rigid core; the second condition therefore only occurs with `K > 0`.

No characteristic arity, stable spectrum, or characteristic-based growth predicate on
terminal classes is used. Growth prolongation and hollow-growth comparison are consumed
as hypotheses here and supplied in `ConstructedTerminalCountability`.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.TopGradeTerminalCounting
open TypeTower StageType KnightRealization Value ExtOrd TopSupport Cardinal
noncomputable section
universe w
variable {α : LimitStage} {M : Type w} {W : KnightRealization α M}

/-- Countably many conditions, each met by at most one member of a family and jointly
covering it, make the family countable. -/
theorem countable_of_cover {ι κ : Type*} [Countable κ] (P : κ → ι → Prop)
    (hsub : ∀ c i j, P c i → P c j → i = j) (hcover : ∀ i, ∃ c, P c i) : Countable ι :=
  CountableCover.countable_of_cover P hsub hcover

/-- **Eventual top grade zero gives a rigid core**: every actual top grade is then zero,
so no actual cover has a top cell, and every tuple (in particular the empty one) is a
globally rigid core. -/
theorem rigidCore_of_isCoinitial_zero
    (hcoin : KnightRealization.IsCoinitial {x : W.LabelledExt | x.type.topGrade = 0})
    {k : ℕ} (B : Fin k ↪ M) : TopSupportRigidCore.RigidCore W B := by
  intro m C c hc e he H hH ht
  apply Set.Subset.antisymm hH.subset
  intro d hd
  have hg : c.scheme.scheme.grade d ≤ 0 :=
    (le_csSup c.topGrades_bddAbove (grade_mem_topGrades (mem_topSet.mp hd))).trans
      (topGrade_le_of_isCoinitial hcoin ⟨m, C, c, hc⟩)
  exact ((c.scheme.scheme.grade_pos d).ne' (Nat.le_zero.mp hg)).elim

/-- Without a globally rigid core, an eventual top grade is positive. -/
theorem pos_of_isCoinitial {K : ℕ}
    (hcoin : KnightRealization.IsCoinitial {x : W.LabelledExt | x.type.topGrade = K})
    (hres : ∀ {k : ℕ} (B : Fin k ↪ M), ¬ TopSupportRigidCore.RigidCore W B) : 0 < K := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact (hres (Function.Embedding.ofIsEmpty : Fin 0 ↪ M)
      (rigidCore_of_isCoinitial_zero hcoin _)).elim
  · exact hK

/-- **At most one coreless class per eventual top grade**: two countable models at the
same stage without globally rigid cores, whose top grades are eventually the same `K`,
are isomorphic. Positivity of `K` is derived, not assumed. -/
theorem nonempty_iso_of_isCoinitial {M₁ M₂ : Type w} [Countable M₁] [Countable M₂]
    {W₁ : KnightRealization α M₁} {W₂ : KnightRealization α M₂}
    (hM₁ : W₁.IsModel) (hM₂ : W₂.IsModel) {K : ℕ}
    (hcoin₁ : KnightRealization.IsCoinitial {x : W₁.LabelledExt | x.type.topGrade = K})
    (hcoin₂ : KnightRealization.IsCoinitial {x : W₂.LabelledExt | x.type.topGrade = K})
    (hres₁ : ∀ {k : ℕ} (B : Fin k ↪ M₁), ¬ TopSupportRigidCore.RigidCore W₁ B)
    (hres₂ : ∀ {k : ℕ} (B : Fin k ↪ M₂), ¬ TopSupportRigidCore.RigidCore W₂ B) :
    Nonempty (W₁.Iso W₂) := by
  have := hM₁.nonempty
  have := hM₂.nonempty
  exact LowOnlyResidualClassification.nonempty_iso_of_receiving hM₁.consistent hM₁.covering
    (OrdinaryModelReceiving.finiteCutReceiving hM₁) hM₂.consistent hM₂.covering
    (OrdinaryModelReceiving.finiteCutReceiving hM₂) hcoin₁ hcoin₂
    (pos_of_isCoinitial hcoin₁ hres₁) hres₁ hres₂

/-- **Counting by top-grade conditions.** At a countable stage, a pairwise non-isomorphic
family of countable models is countable when its growth members are hollow and hollow
growth members compare. The cover: an actual rigid core of a given finite type; no rigid
core and eventual top grade a given `K`; hollow growth. -/
theorem countable {ι : Type*} (hα : α.1.card ≤ Cardinal.aleph0)
    {N : ι → Type w} [∀ i, Countable (N i)]
    (W : ∀ i, KnightRealization α (N i)) (hW : ∀ i, (W i).IsModel)
    (hhollow : ∀ i, (W i).HasTopGradeGrowth → (W i).IsHollow)
    (hcompare : ∀ i j, (W i).HasTopGradeGrowth → (W j).HasTopGradeGrowth →
      (W i).IsHollow → (W j).IsHollow → Nonempty ((W i).Iso (W j)))
    (hanti : ∀ i j, i ≠ j → IsEmpty ((W i).Iso (W j))) : Countable ι := by
  have : ∀ n, Countable (S α.1 n) := fun n => StageType.countable_S hα n
  have heq : ∀ i j, Nonempty ((W i).Iso (W j)) → i = j := by
    intro i j h
    by_contra hne
    exact (hanti i j hne).false h.some
  refine countable_of_cover (κ := (Σ n : ℕ, S α.1 n) ⊕ ℕ ⊕ Unit)
    (Sum.elim
      (fun p i => ∃ B : Fin p.1 ↪ N i,
        (W i).eval B = some p.2 ∧ TopSupportRigidCore.RigidCore (W i) B)
      (Sum.elim
        (fun K i => (∀ {k : ℕ} (B : Fin k ↪ N i), ¬ TopSupportRigidCore.RigidCore (W i) B) ∧
          KnightRealization.IsCoinitial {x : (W i).LabelledExt | x.type.topGrade = K})
        (fun _ i => (W i).HasTopGradeGrowth ∧ (W i).IsHollow))) ?_ ?_
  · rintro (⟨k, p⟩ | K | ⟨⟩) i j hi hj
    · obtain ⟨B₁, h₁, r₁⟩ := hi
      obtain ⟨B₂, h₂, r₂⟩ := hj
      exact heq i j (TopSupportRigidCore.nonempty_iso_of_rigidCores (hW i) (hW j) h₁ h₂ r₁ r₂)
    · exact heq i j (nonempty_iso_of_isCoinitial (hW i) (hW j) hi.2 hj.2 hi.1 hj.1)
    · exact heq i j (hcompare i j hi.1 hj.1 hi.2 hj.2)
  · intro i
    by_cases hcore : ∃ (k : ℕ) (B : Fin k ↪ N i), TopSupportRigidCore.RigidCore (W i) B
    · obtain ⟨k, B, b, hb, hr⟩ := TopSupportRigidCore.exists_labelled_core (hW i) hcore
      exact ⟨.inl ⟨k, b⟩, B, hb, hr⟩
    · rcases (hW i).hasTopGradeGrowth_or_coinitial_constant with hg | ⟨K, hK⟩
      · exact ⟨.inr (.inr ()), hg, hhollow i hg⟩
      · exact ⟨.inr (.inl K), fun B hB => hcore ⟨_, B, hB⟩, hK⟩

/-- **Terminal countability from top-grade behaviour.** At a countable block, the terminal
classes are countable once non-hollow growth prolongs and hollow growth models compare.
Terminality turns the prolongation into hollowness of every growth representative. -/
theorem countable_terminalClass {ρ : Ordinal.{0}} (hρ : ρ < (aleph 1).ord)
    (hprolong : ∀ W : TerminalModel ρ, ¬ W.1.IsHollow → W.1.HasTopGradeGrowth →
      W.1.ProlongsToIn IsModelClass (blockStage_le_succ ρ))
    (hcompare : ∀ W V : TerminalModel ρ,
      W.1.HasTopGradeGrowth → V.1.HasTopGradeGrowth → W.1.IsHollow → V.1.IsHollow →
        Nonempty (W.1.Iso V.1)) : Countable (TerminalClass ρ) := by
  apply countable
    (Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_ord.mp (blockLevel_lt_ord_aleph_one hρ)))
    (fun q : TerminalClass ρ => q.out.1) (fun q => q.out.2.1)
  · intro q hg
    by_contra hn
    exact q.out.2.2 (hprolong q.out hn hg)
  · intro q r
    exact hcompare q.out r.out
  · intro q r hne
    exact ⟨fun e => hne (Quotient.out_equiv_out.mp ⟨e⟩)⟩

/-- The same count in the neutral per-rank fibre contract. -/
theorem countableTerminalFibres_of_growth_results
    (hprolong : ∀ (ρ : Ordinal.{0}), ρ < (aleph 1).ord → ∀ W : TerminalModel ρ,
      ¬ W.1.IsHollow → W.1.HasTopGradeGrowth →
        W.1.ProlongsToIn IsModelClass (blockStage_le_succ ρ))
    (hcompare : ∀ (ρ : Ordinal.{0}), ρ < (aleph 1).ord →
      ∀ W V : TerminalModel ρ,
        W.1.HasTopGradeGrowth → V.1.HasTopGradeGrowth → W.1.IsHollow → V.1.IsHollow →
          Nonempty (W.1.Iso V.1)) : CountableTerminalFibres := by
  intro ρ hρ
  exact Cardinal.mk_le_aleph0_iff.mpr
    (countable_terminalClass hρ (hprolong ρ hρ) (hcompare ρ hρ))

end
end VaughtConjecture.Knight.TopGradeTerminalCounting
