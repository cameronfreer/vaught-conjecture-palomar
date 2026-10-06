/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.CountableLoss
public import VaughtConjecture.Knight.LimitExpansion
public import VaughtConjecture.Knight.ProlongationNormalization
public import VaughtConjecture.Knight.CountableTerminalFibres
public import VaughtConjecture.Knight.ClassTruth
public import VaughtConjecture.Knight.OneBlockComparison

/-! # Expansion domains: countable fixed-stage exceptions without stopping ranks

`domain ξ` is the set of counted isomorphism classes admitting a model expansion to block
`ξ`.  It is defined by expansion **existence**, not by the stopping rank, and the three facts
below use no stopping rank, no termination theorem, and no canonical stopping expansion:

* **Successor losses are countable** (`loss_countable`): any expansion witnessing membership
  in `domain ξ` of a class outside `domain (ξ + 1)` is terminal, so the loss lies in the image
  of the terminal classes at block `ξ` (`loss_subset_range`), countable by the supplied
  terminal-fibre countability.  No canonical or unique expansion is chosen.
* **No loss at a countable limit** (`iInter_subset_domain`): the countable-limit expansion
  theorem `exists_model_at_limit_of_forall_lt`.
* **Fixed-stage complements are countable** (`compl_countable`): the generic
  `CountableLoss.compl_countable_of_loss`.

With the one-block readback hypothesis, classes in `domain (ω · η)` agree on every sentence of
quantifier rank at most `η` (`realizes_iff_of_mem_domain`), so every sentence has a countable
truth side (`sentence_split_countable`).  Terminal countability and receiving are explicit
hypotheses here; `ExpansionDomainThinness` discharges them.  The existing rank filtration is
untouched: under termination, `domain ξ = {q | ξ ≤ knightNatStopRank q}`, but that
identification is not used. -/

@[expose] public section

namespace VaughtConjecture.Knight.ExpansionDomain

open TypeTower FirstOrder Language KnightRealization Cardinal StoppingRankFiltration

/-- **The expansion domain at block `ξ`**: the counted classes admitting a model expansion
to `blockStage ξ` (up to isomorphism; on the counted carrier by normalization). -/
def domain (ξ : Ordinal.{0}) : Set Classes :=
  {q | Quotient.lift
    (fun R : KnightNatModel => R.atBlockZero.ProlongsToIn IsModelClass (blockStage_zero_le ξ))
    (fun _ _ h => propext (Realization.prolongsToIn_iff_of_iso
      (KnightNatModel.iso_atBlockZero (knightModelSetoid_r_iff.mp h)) _)) q}

theorem mem_domain_mk {ξ : Ordinal.{0}} (R : KnightNatModel) :
    Quotient.mk knightModelSetoid R ∈ domain ξ ↔
      R.atBlockZero.ProlongsToIn IsModelClass (blockStage_zero_le ξ) :=
  Iff.rfl

/-- Membership normalizes to an actual model on the counted carrier. -/
theorem exists_model_of_mem_domain {ξ : Ordinal.{0}} {R : KnightNatModel}
    (h : Quotient.mk knightModelSetoid R ∈ domain ξ) :
    ∃ W : KnightRealization (blockStage ξ) ℕ,
      W.IsModel ∧ W.reduct (blockStage_zero_le ξ) = R.atBlockZero :=
  (prolongsToIn_isModelClass_iff_on _ _).mp h

theorem mem_domain_of_model {ξ : Ordinal.{0}} {R : KnightNatModel}
    {W : KnightRealization (blockStage ξ) ℕ} (hW : W.IsModel)
    (hWr : W.reduct (blockStage_zero_le ξ) = R.atBlockZero) :
    Quotient.mk knightModelSetoid R ∈ domain ξ :=
  Realization.ProlongsToOnIn.prolongsToIn ⟨W, hW, hWr⟩

/-- Every class expands to block `0`. -/
theorem domain_zero : domain 0 = Set.univ := by
  ext q
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  induction q using Quotient.inductionOn with
  | h R =>
    exact mem_domain_of_model (R := R) (R.2.reduct blockStage_zero_le_omegaStage)
      (Realization.reduct_refl _)

/-- **Expansion domains decrease**: an expansion to a higher block reduces to a lower one. -/
theorem domain_antitone : Antitone domain := by
  intro ξ η hξη q hq
  induction q using Quotient.inductionOn with
  | h R =>
    exact Realization.ProlongsToIn.mono isModelClass_reduct (blockStage_mono hξη) hq

/-! ## Successor losses -/

/-- A class lost at the next block is the class of a terminal model at this block. -/
theorem loss_subset_range (ξ : Ordinal.{0}) :
    domain ξ \ domain (ξ + 1) ⊆ Set.range (terminalToClass ξ) := by
  rintro q ⟨hq, hq'⟩
  induction q using Quotient.inductionOn with
  | h R =>
    obtain ⟨W, hWm, hWr⟩ := exists_model_of_mem_domain hq
    have hterm : W.NoProlongationToIn IsModelClass (blockStage_le_succ ξ) := by
      intro hprol
      obtain ⟨V, hVm, hVr⟩ :=
        (prolongsToIn_isModelClass_iff_on W (blockStage_le_succ ξ)).mp hprol
      refine hq' (mem_domain_of_model hVm ?_)
      rw [← Realization.reduct_reduct (blockStage_zero_le ξ) (blockStage_le_succ ξ) V, hVr,
        hWr]
    refine ⟨Quotient.mk _ ⟨W, hWm, hterm⟩, ?_⟩
    change Quotient.mk knightModelSetoid (TerminalModel.toNatModel ⟨W, hWm, hterm⟩) =
      Quotient.mk knightModelSetoid R
    congr 1
    apply Subtype.ext
    change liftBlockZero (W.reduct (blockStage_zero_le ξ)) = R.1
    rw [hWr]
    exact liftBlockZero_reduct R.1

/-- **Successor losses are countable**, given countable terminal fibres. -/
theorem loss_countable (hct : CountableTerminalFibres) {ξ : Ordinal.{0}}
    (hξ : ξ < (aleph 1).ord) : (domain ξ \ domain (ξ + 1)).Countable :=
  have : Countable (TerminalClass ξ) := Cardinal.mk_le_aleph0_iff.mp (hct ξ hξ)
  (Set.countable_range _).mono (loss_subset_range ξ)

/-! ## Limits -/

/-- **No loss at a countable limit**: the countable-limit expansion theorem. -/
theorem iInter_subset_domain {l : Ordinal.{0}} (hl : Order.IsSuccLimit l)
    (hlω : l < (aleph 1).ord) : (⋂ ξ < l, domain ξ) ⊆ domain l := by
  intro q hq
  induction q using Quotient.inductionOn with
  | h R =>
    obtain ⟨W, hWm, hWr⟩ := exists_model_at_limit_of_forall_lt hl hlω (R := R.atBlockZero)
      fun ξ hξ => exists_model_of_mem_domain (Set.mem_iInter₂.mp hq ξ hξ)
    exact mem_domain_of_model hWm hWr

/-- **Full limit continuity**: at a countable limit the domain is the intersection of the
earlier domains (decreasingness gives one inclusion, limit expansion the other). -/
theorem domain_limit_eq {l : Ordinal.{0}} (hl : Order.IsSuccLimit l)
    (hlω : l < (aleph 1).ord) : domain l = ⋂ ξ < l, domain ξ :=
  Set.Subset.antisymm (Set.subset_iInter₂ fun _ hξ => domain_antitone hξ.le)
    (iInter_subset_domain hl hlω)

/-- **Fixed-stage complements are countable.** -/
theorem compl_countable (hct : CountableTerminalFibres) {β : Ordinal.{0}}
    (hβ : β < (aleph 1).ord) : (domain β)ᶜ.Countable :=
  CountableLoss.compl_countable_of_loss domain domain_zero
    (fun _ hξ => loss_countable hct hξ) (fun _ hl hlω => iInter_subset_domain hl hlω) β hβ

/-! ## Fixed-stage comparison on a domain -/

theorem reduct_omegaStage_eq {ξ : Ordinal.{0}} {R : KnightNatModel}
    {W : KnightRealization (blockStage ξ) ℕ}
    (hWr : W.reduct (blockStage_zero_le ξ) = R.atBlockZero) :
    W.reduct (omegaStage_le _) = R.1 := by
  rw [← Realization.reduct_reduct omegaStage_le_blockStage_zero (blockStage_zero_le ξ) W, hWr]
  exact liftBlockZero_reduct R.1

/-- Classes in the domain at the comparison block agree on sentences of bounded rank. -/
theorem realizes_iff_of_mem_domain (hobr : OneBlockReadback.{0}) (φ : knightLang.Sentenceω)
    {η : Ordinal.{0}} (hφ : φ.qrank ≤ η) {q s : Classes}
    (hq : q ∈ domain (Ordinal.omega0 * η)) (hs : s ∈ domain (Ordinal.omega0 * η)) :
    realizes φ q ↔ realizes φ s := by
  revert hq hs
  refine Quotient.inductionOn₂ q s fun R S hq hs => ?_
  obtain ⟨W, hWm, hWr⟩ := exists_model_of_mem_domain hq
  obtain ⟨V, hVm, hVr⟩ := exists_model_of_mem_domain hs
  have h := agree_sentence_of_obr hobr W V hWm hVm φ hφ
  rw [reduct_omegaStage_eq hWr, reduct_omegaStage_eq hVr] at h
  exact h

/-- The comparison block of a sentence is countable (as in `SentenceMinimality.threshold_lt`). -/
theorem threshold_lt (φ : knightLang.Sentenceω) :
    Ordinal.omega0 * φ.qrank < (aleph 1).ord := by
  rw [Cardinal.lt_ord, Ordinal.card_mul, Ordinal.card_omega0]
  exact (mul_le_mul' le_rfl
    (Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_ord.mp (qrank_lt_ord_aleph_one φ)))).trans_lt
    (by simpa only [aleph0_mul_aleph0] using aleph0_lt_aleph_one)

/-- **Rank-free sentence splits**: one truth side of every sentence is countable, from
countable terminal fibres and one-block readback alone. -/
theorem sentence_split_countable (hct : CountableTerminalFibres) (hobr : OneBlockReadback.{0})
    (φ : knightLang.Sentenceω) :
    ({q : Classes | realizes φ q} : Set Classes).Countable ∨
      ({q : Classes | ¬ realizes φ q} : Set Classes).Countable := by
  have hc := compl_countable hct (threshold_lt φ)
  by_cases h : ∃ q ∈ domain (Ordinal.omega0 * φ.qrank), realizes φ q
  · obtain ⟨q₀, hq₀, hr⟩ := h
    exact Or.inr (Set.Countable.mono (fun s hs hsd =>
      hs ((realizes_iff_of_mem_domain hobr φ le_rfl hsd hq₀).mpr hr)) hc)
  · exact Or.inl (Set.Countable.mono (fun q hq hqd => h ⟨q, hqd, hq⟩) hc)

end VaughtConjecture.Knight.ExpansionDomain
