/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionDomain
public import VaughtConjecture.Knight.ProjectedChartComparison
public import VaughtConjecture.Knight.ClassPresentation
public import InfinitaryLogic.ModelTheory.MorleyCounting

/-! # Back-and-forth equivalence on an expansion domain, and countable `≡_η` quotients

The projected receipt comparison `bfEquiv_of_commonChart_projected` proves back-and-forth
equivalence through `η` from a common chart at `blockStage η`, before sentence agreement.
Every model labels the empty tuple, and there is only one such label, so any two models at one
block have a common chart of the empty tuple (`hasCommonChart_elim0`).  Hence:

* `bfEquiv_of_mem_domain`: two counted models whose classes lie in `domain η` are
  back-and-forth equivalent at level `η` on the empty tuple;
* `bfEquivSetoid_r_of_mem_domain`: the same for coded `ℕ`-models of `knightSentence`, in the
  form of the library relation `bfEquivSetoid knightSentence η`.

**Countable `≡_η` quotients** (`mk_bfEquivSetoid_quotient_le_aleph0`).  Put `E = (domain η)ᶜ`,
and let `π` send a class to its `≡_η`-class (isomorphism refines `≡_η`, so `π` is defined on
`Classes`).  Every `≡_η`-class lies in `π[E] ∪ π[domain η]`; the first set is countable because
`E` is (`compl_countable`), and the second has at most one element by the comparison above.
No representative of `domain η` is chosen, so an empty domain needs no separate case.

Terminal countability is an explicit hypothesis.  Nothing here uses stopping ranks, the
Morley or Silver dichotomy, or thinness.  The converse (that `≡_η`-equivalent models lie in
the same domain) is not claimed. -/

@[expose] public section

namespace VaughtConjecture.Knight.ExpansionDomain

open TypeTower FirstOrder Language KnightRealization Cardinal StoppingRankFiltration

universe w

private theorem bfEquiv_reduct_stage_eq {δ ε ζ : LimitStage}
    (h : δ = ε) (hδ : δ ≤ ζ) (hε : ε ≤ ζ)
    {M N : Type*} (W : KnightRealization ζ M) (V : KnightRealization ζ N)
    {η : Ordinal.{0}} {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    (@BFEquiv (stageLang δ) M (stageStructureOf (W.reduct hδ))
      N (stageStructureOf (V.reduct hδ)) η n a b) ↔
    (@BFEquiv (stageLang ε) M (stageStructureOf (W.reduct hε))
      N (stageStructureOf (V.reduct hε)) η n a b) := by
  cases h
  rfl

/-- Transport the projected comparison from block zero to the sentence's `ω` language.
The stage equality is eliminated explicitly; no additional comparison or rank loss occurs. -/
theorem bfEquiv_of_commonChart_projected_omega {η : Ordinal.{0}} {M N : Type w}
    (W : KnightRealization (blockStage η) M) (V : KnightRealization (blockStage η) N)
    (hW : W.IsModel) (hV : V.IsModel) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hc : HasCommonChart W V a b) :
    @BFEquiv knightLang M (structureOf (W.reduct (omegaStage_le _)))
      N (structureOf (V.reduct (omegaStage_le _))) η n a b :=
  (bfEquiv_reduct_stage_eq blockStage_zero (blockStage_zero_le η) (omegaStage_le _) W V a b).mp
    (bfEquiv_of_commonChart_projected η W V hW hV hc)

/-- Any two models at one stage have a common chart of the empty tuple: both label it, and
there is only one label of the empty tuple. -/
theorem hasCommonChart_elim0 {α : LimitStage} {M N : Type}
    {W : KnightRealization α M} {V : KnightRealization α N} (hW : W.IsModel)
    (hV : V.IsModel) :
    HasCommonChart W V (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  obtain ⟨p, hp⟩ := exists_eval_empty_at hW
  obtain ⟨p', hp'⟩ := exists_eval_empty_at hV
  refine ⟨0, Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, Fin.elim0, p, hp, ?_,
    funext fun i => i.elim0, funext fun i => i.elim0⟩
  rw [hp', Subsingleton.elim p' p]

/-- **Back-and-forth equivalence on an expansion domain.**  Two counted models whose classes
lie in `domain η` are back-and-forth equivalent at level `η` on the empty tuple, directly from
the projected receipt comparison, transported to the sentence's language. -/
theorem bfEquiv_of_mem_domain {η : Ordinal.{0}} {R S : KnightNatModel}
    (hR : Quotient.mk knightModelSetoid R ∈ domain η)
    (hS : Quotient.mk knightModelSetoid S ∈ domain η) :
    @BFEquiv knightLang ℕ (structureOf R.1) ℕ (structureOf S.1) η 0 Fin.elim0 Fin.elim0 := by
  obtain ⟨W, hWm, hWr⟩ := exists_model_of_mem_domain hR
  obtain ⟨V, hVm, hVr⟩ := exists_model_of_mem_domain hS
  have h := bfEquiv_of_commonChart_projected_omega W V hWm hVm
    (hasCommonChart_elim0 hWm hVm)
  rwa [reduct_omegaStage_eq hWr, reduct_omegaStage_eq hVr] at h

/-- **The library relation on a domain**: coded `ℕ`-models of `knightSentence` whose classes
lie in `domain η` are related by `bfEquivSetoid knightSentence η`. -/
theorem bfEquivSetoid_r_of_mem_domain {η : Ordinal.{0}} {c d : ModelsOf knightSentence}
    (hc : modelClass c ∈ domain η) (hd : modelClass d ∈ domain η) :
    (bfEquivSetoid knightSentence η).r c d := by
  have h := bfEquiv_of_mem_domain (R := realizationOfCode c) (S := realizationOfCode d) hc hd
  have hc' := @equiv_implies_BFEquiv knightLang ℕ ℕ c.1.toStructure
    (structureOf (realizationOfCode c).1)
    (@Language.Equiv.symm knightLang ℕ ℕ (structureOf (realizationOfCode c).1)
      c.1.toStructure (isKnightModel_of_mem c).structureOfToRealizationEquiv) η 0 Fin.elim0
  have hd' := @equiv_implies_BFEquiv knightLang ℕ ℕ (structureOf (realizationOfCode d).1)
    d.1.toStructure (isKnightModel_of_mem d).structureOfToRealizationEquiv η 0 Fin.elim0
  rw [comp_fin_elim0] at hc' hd'
  have hcd := @BFEquiv.trans knightLang ℕ c.1.toStructure ℕ
    (structureOf (realizationOfCode c).1) ℕ (structureOf (realizationOfCode d).1)
    (n := 0) (α := η) (a := Fin.elim0) (b := Fin.elim0) (c := Fin.elim0) hc' h
  exact @BFEquiv.trans knightLang ℕ c.1.toStructure ℕ (structureOf (realizationOfCode d).1)
    ℕ d.1.toStructure (n := 0) (α := η) (a := Fin.elim0) (b := Fin.elim0) (c := Fin.elim0)
    hcd hd'

/-- **Countably many `≡_η`-classes**: for every countable `η`, the library's quotient of the
coded `ℕ`-models of `knightSentence` by back-and-forth equivalence at level `η` is countable.
The classes outside `domain η` are countable, and the classes inside it project to at most one
`≡_η`-class. -/
theorem mk_bfEquivSetoid_quotient_le_aleph0 (hct : CountableTerminalFibres)
    {η : Ordinal.{0}} (hη : η < (aleph 1).ord) :
    #(Quotient (bfEquivSetoid knightSentence η)) ≤ ℵ₀ := by
  let π : Classes → Quotient (bfEquivSetoid knightSentence η) :=
    fun q => bfProj knightSentence η (isoClassEquiv.symm q)
  have hπ (c : ModelsOf knightSentence) : π (modelClass c) = Quotient.mk _ c := by
    change bfProj knightSentence η (isoClassEquiv.symm (isoClassEquiv _)) = _
    rw [Equiv.symm_apply_apply, bfProj_mk]
  have hcover : (Set.univ : Set (Quotient (bfEquivSetoid knightSentence η))) ⊆
      π '' (domain η)ᶜ ∪ π '' domain η := by
    rintro x -
    induction x using Quotient.inductionOn with
    | h c =>
      by_cases hc : modelClass c ∈ domain η
      · exact Or.inr ⟨_, hc, hπ c⟩
      · exact Or.inl ⟨_, hc, hπ c⟩
  have hsub : (π '' domain η).Subsingleton := by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨s, hs, rfl⟩
    obtain ⟨c, rfl⟩ := modelClass_surjective q
    obtain ⟨d, rfl⟩ := modelClass_surjective s
    rw [hπ, hπ]
    exact Quotient.sound (bfEquivSetoid_r_of_mem_domain hq hs)
  have hcount := (((compl_countable hct hη).image π).union hsub.countable).mono hcover
  exact mk_le_aleph0_iff.mpr (Set.countable_univ_iff.mp hcount)

end VaughtConjecture.Knight.ExpansionDomain
