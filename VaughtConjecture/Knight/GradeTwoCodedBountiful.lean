/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoReadOneStable
public import VaughtConjecture.Knight.PositiveNormalization

/-! # The coded base obligation from ordinary base bountifulness

`CodedBountiful sem₀ I` (`Knight/GradeTwoAgreeingMember.lean`) asked the base for an
alphabet-valued lift under `max γ δ`.  This module derives it from **ordinary** bountifulness
of the base (`codedBountiful_of_isBountiful`), so that the coded member-extension argument rests
on `sem₀.IsBountiful` alone, with the tower's existing size hypotheses.

* **The alphabet retraction** `alphRetract I`: the identity on `alph 2 I`, sending every other
  label into the alphabet — a value in a block below `I` keeps its block and has its finite part
  cut at `3`; a value at or beyond block `I`, and `⊤`, go to the alphabet's top.  It is a
  bottom-reflecting `2`-step shifter (`isStepShifter_alphRetract`), so it preserves respect
  with the semantic rows unchanged (`RespectsSemanticsBelow.map_bottom_reflecting`), fixes the
  boundary (`alphRetract_eq_self_of_mem_alph`), and commutes with capping (monotone).  Index
  check: for positive `I`, `alph 2 I` is the coded alphabet at block bound `I - 1` and grade `2`.
* **Grade-sensitive capping** (`RespectsSemanticsBelow.gradeCap`): capping a respecting
  labelling at a grade-dependent, antitone family of caps self-visible at their grades preserves
  respect — at each controller the row is capped by the controller's own cap (the Cap Lemma
  `TransformsTo.cap`), the cells below carrying larger caps.  The caps used are the largest
  alphabet values self-visible at each grade below `max γ δ` (`roundDownVis`): a grade-one
  value invisible at grade two survives under the grade-one cap, so no visibility of `δ` is
  needed and the bound `F' ≤ max γ δ` holds as stated.
* **The base bridge** (`baseEquiv`, `RespectsBase.toBelow`, `RespectsBase.ofBelow`): respect of
  the base semantics on the base cells of grade `≤ 2` is respect of `E⟨A,2⟩`.
* **The derivation** (`codedBountiful_of_isBountiful`): the ordinary lift, retracted into the
  alphabet, then capped grade-sensitively.  Literal labels and cap agreement survive both steps
  because the prescribed labels, the ambient labels and the cap are alphabet values below the
  caps.
* **Specialization to the cutoff-correct family** (`cutoffCorrect_congr_of_scope`,
  `lift_of_coded_input_cutoff`): when the prescribed scope contains the three reference cells,
  the family predicate depends only on the cells under it, so the lift by controller change for
  coded inputs holds over any bountiful base — ordinary base bountifulness is the substantive
  inductive hypothesis.  Faces missing a reference cell and arbitrary ambient labellings are not
  addressed, and tower bountifulness is not claimed.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd

/-! ## The alphabet retraction -/

section Retract

variable (I : ℕ)

/-- The top of the alphabet `alph 2 I`: `ω·(I-1) + 3`. -/
noncomputable def alphTop : ExtOrd :=
  ofOrd (Ordinal.omega0 * ((I - 1 : ℕ) : Ordinal) + ((3 : ℕ) : Ordinal))

/-- **The alphabet retraction**: the identity on `alph 2 I`; a value in a block below `I` keeps
its block with finite part cut at `3`; every other value goes to the top of the alphabet. -/
noncomputable def alphRetract : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => alphTop I
  | some (some v) =>
      if blockIdx v < (I : Ordinal) then
        ofOrd (limitPart v + ((min (finitePart v) 3 : ℕ) : Ordinal))
      else alphTop I

theorem alphRetract_bot : alphRetract I ⊥ = ⊥ := rfl
theorem alphRetract_top : alphRetract I ⊤ = alphTop I := rfl
theorem alphRetract_ofOrd (v : Ordinal.{0}) :
    alphRetract I (ofOrd v) =
      if blockIdx v < (I : Ordinal) then
        ofOrd (limitPart v + ((min (finitePart v) 3 : ℕ) : Ordinal))
      else alphTop I := rfl

variable {I}

theorem alphTop_mem_alph (hI : 0 < I) : alphTop I ∈ alph 2 I :=
  mem_alph_iff.mpr (Or.inr ⟨I - 1, 3, by omega, by omega, rfl⟩)

theorem alphTop_selfVis (k : ℕ) (hk : k ≤ 3) : SelfVis k (alphTop I) := by
  unfold alphTop
  rw [selfVis_ofOrd_iff, finitePart_mul_add]
  exact hk

theorem le_alphTop_of_mem_alph (hI : 0 < I) {x : ExtOrd} (hx : x ∈ alph 2 I) : x ≤ alphTop I := by
  rcases mem_alph_iff.mp hx with rfl | ⟨i, j, hi, hj, rfl⟩
  · exact bot_le
  · unfold alphTop
    rw [ofOrd_le_ofOrd]
    have h1 : (i : Ordinal) ≤ ((I - 1 : ℕ) : Ordinal) := by exact_mod_cast (by omega : i ≤ I - 1)
    have h2 : (j : Ordinal) ≤ ((3 : ℕ) : Ordinal) := by exact_mod_cast hj
    gcongr

/-- The block index of a block-start-plus-natural is the block index. -/
theorem blockIdx_limitPart_add_nat (ξ : Ordinal.{0}) (i : ℕ) :
    blockIdx (limitPart ξ + i) = blockIdx ξ := by
  rw [limitPart_eq_mul_blockIdx]
  unfold blockIdx
  rw [Ordinal.mul_add_div _ Ordinal.omega0_ne_zero,
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 i), add_zero]

theorem alphRetract_mem_alph (hI : 0 < I) (x : ExtOrd) : alphRetract I x ∈ alph 2 I := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · rw [alphRetract_bot]; exact bot_mem_alph _ _
  · rw [alphRetract_top]; exact alphTop_mem_alph hI
  · rw [alphRetract_ofOrd]
    split_ifs with h
    · obtain ⟨t, ht⟩ : ∃ t : ℕ, blockIdx v = t :=
        Ordinal.lt_omega0.mp (h.trans (Ordinal.natCast_lt_omega0 I))
      have htI : t < I := by rw [ht] at h; exact_mod_cast h
      have hl : limitPart v = Ordinal.omega0 * (t : Ordinal) := by
        rw [limitPart_eq_mul_blockIdx, ht]
      rw [hl]
      exact mem_alph_iff.mpr (Or.inr ⟨t, min (finitePart v) 3, htI, by omega, rfl⟩)
    · exact alphTop_mem_alph hI

theorem alphRetract_eq_self_of_mem_alph {x : ExtOrd} (hx : x ∈ alph 2 I) : alphRetract I x = x := by
  rcases mem_alph_iff.mp hx with rfl | ⟨i, j, hi, hj, rfl⟩
  · rfl
  · rw [alphRetract_ofOrd, blockIdx_mul_add, limitPart_mul_add, finitePart_mul_add,
      min_eq_left hj, ite_eq_left_of_eq_true _ _ (eq_true (by exact_mod_cast hi))]

theorem alphRetract_ne_bot_of_ne_bot {x : ExtOrd} (hx : x ≠ ⊥) : alphRetract I x ≠ ⊥ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact absurd rfl hx
  · rw [alphRetract_top]; exact ofOrd_ne_bot _
  · rw [alphRetract_ofOrd]
    split_ifs
    · exact ofOrd_ne_bot _
    · exact ofOrd_ne_bot _

theorem alphRetract_bot_reflecting (x : ExtOrd) (h : alphRetract I x = ⊥) : x = ⊥ := by
  by_contra hx
  exact alphRetract_ne_bot_of_ne_bot hx h

/-- The retraction is monotone. -/
theorem alphRetract_mono (hI : 0 < I) : Monotone (alphRetract I) := by
  intro x y hxy
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · rw [alphRetract_bot]; exact bot_le
  · rw [top_le_iff.mp hxy]
  · rcases ExtOrd.cases y with rfl | rfl | ⟨w, rfl⟩
    · exact absurd hxy (not_ofOrd_le_bot v)
    · rw [alphRetract_top]; exact le_alphTop_of_mem_alph hI (alphRetract_mem_alph hI _)
    · have hvw : v ≤ w := ofOrd_le_ofOrd.mp hxy
      rw [alphRetract_ofOrd, alphRetract_ofOrd]
      split_ifs with hv hw hw
      · rw [ofOrd_le_ofOrd]
        rcases lt_or_eq_of_le (limitPart_mono hvw) with hlt | heq
        · have h3 : limitPart v + ((min (finitePart v) 3 : ℕ) : Ordinal) ≤
              limitPart v + ((3 : ℕ) : Ordinal) :=
            add_le_add_right (by exact_mod_cast min_le_right _ _) _
          exact h3.trans ((limitPart_add_nat_le_of_lt hlt 3).trans le_self_add)
        · rw [heq]
          exact add_le_add_right (by
            exact_mod_cast min_le_min_right 3
              (finitePart_le_of_le_of_limitPart_eq hvw heq)) _
      · have hmem := alphRetract_mem_alph hI (ofOrd v)
        rw [alphRetract_ofOrd, ite_eq_left_of_eq_true _ _ (eq_true hv)] at hmem
        exact le_alphTop_of_mem_alph hI hmem
      · exact absurd ((blockIdx_mono hvw).trans_lt hw) hv
      · exact le_rfl

theorem alphRetract_selfVis {x : ExtOrd} {k : ℕ} (hk : k ≤ 2) (hx : SelfVis k x) :
    SelfVis k (alphRetract I x) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · rw [alphRetract_bot]; exact selfVis_bot k
  · rw [alphRetract_top]; exact alphTop_selfVis k (by omega)
  · rw [selfVis_ofOrd_iff] at hx
    rw [alphRetract_ofOrd]
    split_ifs
    · rw [selfVis_ofOrd_iff, finitePart_limitPart_add_nat]
      omega
    · exact alphTop_selfVis k (by omega)

/-- **The retraction is a bottom-reflecting `2`-step shifter.** -/
theorem isStepShifter_alphRetract (hI : 0 < I) : IsStepShifter 2 (alphRetract I) where
  map_bot := rfl
  mono := alphRetract_mono hI
  selfVis x k hk hx := alphRetract_selfVis hk hx
  blockwise ξ := by
    by_cases h : blockIdx ξ < (I : Ordinal)
    · refine Or.inl ⟨limitPart ξ, finitePart_limitPart ξ, fun i hi => ?_⟩
      rw [alphRetract_ofOrd, blockIdx_limitPart_add_nat, limitPart_limitPart_add_nat,
        finitePart_limitPart_add_nat, min_eq_left (by omega : i ≤ 3),
        ite_eq_left_of_eq_true _ _ (eq_true h)]
    · refine Or.inr ⟨alphTop I, alphTop_selfVis 2 (by omega), fun i _ => ?_⟩
      rw [alphRetract_ofOrd, blockIdx_limitPart_add_nat, ite_eq_right_of_eq_false _ _ (eq_false h)]
  bot_blocks ξ ζ _ h := absurd h (alphRetract_ne_bot_of_ne_bot (ofOrd_ne_bot ξ))

end Retract

/-! ## Grade-sensitive rounding and capping -/

section GradeCap

/-- The largest alphabet value self-visible at grade `k` below `x` (`⊥` at worst): rounding in
`alph 2 I`, with the visibility threshold `k` decoupled from the alphabet grade. -/
noncomputable def roundDownVis (k I : ℕ) (x : ExtOrd) : ExtOrd :=
  ((alph 2 I).filter fun a => SelfVis k a ∧ a ≤ x).max'
    ⟨⊥, Finset.mem_filter.mpr ⟨bot_mem_alph 2 I, selfVis_bot k, bot_le⟩⟩

theorem roundDownVis_spec (k I : ℕ) (x : ExtOrd) :
    roundDownVis k I x ∈ alph 2 I ∧ SelfVis k (roundDownVis k I x) ∧ roundDownVis k I x ≤ x := by
  have h := Finset.max'_mem ((alph 2 I).filter fun a => SelfVis k a ∧ a ≤ x)
    ⟨⊥, Finset.mem_filter.mpr ⟨bot_mem_alph 2 I, selfVis_bot k, bot_le⟩⟩
  rw [Finset.mem_filter] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem roundDownVis_mem (k I : ℕ) (x : ExtOrd) : roundDownVis k I x ∈ alph 2 I :=
  (roundDownVis_spec k I x).1

theorem roundDownVis_selfVis (k I : ℕ) (x : ExtOrd) : SelfVis k (roundDownVis k I x) :=
  (roundDownVis_spec k I x).2.1

theorem roundDownVis_le (k I : ℕ) (x : ExtOrd) : roundDownVis k I x ≤ x :=
  (roundDownVis_spec k I x).2.2

theorem le_roundDownVis {k I : ℕ} {a x : ExtOrd} (ha : a ∈ alph 2 I) (hs : SelfVis k a)
    (hax : a ≤ x) : a ≤ roundDownVis k I x :=
  Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨ha, hs, hax⟩)

/-- Rounding is antitone in the visibility threshold. -/
theorem roundDownVis_anti {k k' I : ℕ} (hkk' : k ≤ k') (x : ExtOrd) :
    roundDownVis k' I x ≤ roundDownVis k I x :=
  le_roundDownVis (roundDownVis_mem k' I x) (SelfVis.mono (roundDownVis_selfVis k' I x) hkk')
    (roundDownVis_le k' I x)

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- **Grade-sensitive capping preserves respect**: capping a respecting labelling at an
antitone family of caps self-visible at their grades respects again — at each controller the row
is capped by the controller's own cap (the Cap Lemma), the cells below carrying larger caps. -/
theorem RespectsSemanticsBelow.gradeCap {sem : Semantics D} {BJ : Finset ι × ℕ}
    {r : D.below BJ → ExtOrd} (h : RespectsSemanticsBelow sem BJ r) (g : ℕ → ExtOrd)
    (hanti : ∀ k k', k ≤ k' → g k' ≤ g k) (hvis : ∀ k, k ≤ BJ.2 → SelfVis k (g k)) :
    RespectsSemanticsBelow sem BJ (fun d => min (r d) (g (D.grade d.1))) where
  orderly d := (selfVis_min (h.orderly d).symm (hvis _ d.2.2)).symm
  locality Sig := by
    have key : TransformsTo (fun d : D.below (D.cell Sig.1) => D.grade d.1) (sem.E Sig.1)
        (fun d => min (min (r (CellScheme.below.incl Sig d)) (r Sig)) (g (D.grade Sig.1))) :=
      (h.locality Sig).cap (fun d => d.2.2) (hvis _ Sig.2.2)
    have heq : (fun d : D.below (D.cell Sig.1) =>
        min (min (r (CellScheme.below.incl Sig d)) (g (D.grade (CellScheme.below.incl Sig d).1)))
          (min (r Sig) (g (D.grade Sig.1)))) =
        fun d => min (min (r (CellScheme.below.incl Sig d)) (r Sig)) (g (D.grade Sig.1)) := by
      funext d
      have hgd : g (D.grade Sig.1) ≤ g (D.grade (CellScheme.below.incl Sig d).1) :=
        hanti _ _ d.2.2
      rw [min_min_min_comm, min_eq_right hgd]
    rw [heq]
    exact key
  availability Sig Xi₀ hscope hgrade := by
    obtain ⟨Xi, hcell, hle⟩ := h.availability Sig Xi₀ hscope hgrade
    refine ⟨Xi, hcell, ?_⟩
    have hg : D.grade Xi.1 = D.grade Sig.1 := by
      change (D.cell Xi.1).2 = (D.cell Sig.1).2
      rw [hcell]
      exact hgrade.symm
    rw [hg]
    exact min_le_min hle le_rfl

end GradeCap

/-! ## The base bridge -/

section Bridge

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A} {sem₀ : Semantics D₀}

/-- The base cells of grade `≤ 2` are the lower set of the full index at grade two. -/
def baseEquiv : BaseCells D₀ 2 ≃ D₀.below (A, 2) where
  toFun d := ⟨d.1, ⟨D₀.isPlan.subset_of_mem (D₀.scope_mem_plan d.1), d.2⟩⟩
  invFun d := ⟨d.1, d.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem baseEquiv_val (d : BaseCells D₀ 2) : (baseEquiv (D₀ := D₀) d).1 = d.1 := rfl

/-- Respect of the base semantics on the base cells is respect of `E⟨A,2⟩`. -/
theorem RespectsBase.toBelow {F : BaseCells D₀ 2 → ExtOrd} (h : RespectsBase sem₀ 2 F) :
    RespectsSemanticsBelow sem₀ (A, 2) (fun d => F ⟨d.1, d.2.2⟩) where
  orderly d := (h.orderly ⟨d.1, d.2.2⟩).symm
  locality Sig := h.locality ⟨Sig.1, Sig.2.2⟩
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hXi, hle⟩ := h.availability ⟨Sig.1, Sig.2.2⟩ ⟨Xi₀.1, Xi₀.2.2⟩ hs hg
    exact ⟨⟨Xi.1, ⟨D₀.isPlan.subset_of_mem (D₀.scope_mem_plan Xi.1), Xi.2⟩⟩, hXi, hle⟩

/-- Respect of `E⟨A,2⟩` is respect of the base semantics on the base cells. -/
theorem RespectsBase.ofBelow {r : D₀.below (A, 2) → ExtOrd}
    (h : RespectsSemanticsBelow sem₀ (A, 2) r) :
    RespectsBase sem₀ 2 (fun d => r (baseEquiv d)) where
  orderly d := (h.orderly (baseEquiv d)).symm
  locality y := h.locality (baseEquiv y)
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hXi, hle⟩ := h.availability (baseEquiv Sig) (baseEquiv Xi₀) hs hg
    exact ⟨⟨Xi.1, Xi.2.2⟩, hXi, hle⟩

end Bridge

/-! ## The derivation -/

section Derivation

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A} {sem₀ : Semantics D₀}
  {I : ℕ}

theorem min_mem_alph {l : ℕ} {a b : ExtOrd} (ha : a ∈ alph l I) (hb : b ∈ alph l I) :
    min a b ∈ alph l I := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]; exact ha
  · rw [min_eq_right h]; exact hb

/-- **The coded base obligation follows from ordinary base bountifulness**: the ordinary lift,
retracted into the alphabet and capped grade-sensitively below `max γ δ`. -/
theorem codedBountiful_of_isBountiful (hB : sem₀.IsBountiful)
    (hA2 : (A, 2) ∈ Plan.gradedPlan D₀.plan) (hI : 0 < I) : CodedBountiful sem₀ I := by
  intro C hC hCA F G γ δ hF hFr hFγ hG hGr hGδ hγm hγv hag
  have h := gradedLe_full_two (D₀ := D₀) hC
  obtain ⟨q', hq', hcap, hres⟩ := hB (C, 2) (A, 2) hC hA2 h (fun e => hCA (congrArg Prod.fst e))
    (fun d => G ⟨d.1, d.2.2⟩) (fun d => F ⟨d.1, d.2.2⟩) γ (hGr.toBelow.mono h) hFr.toBelow hγv
    (fun d => (hag ⟨d.1, d.2.2⟩ d.2.1).symm)
  have hr₁ : RespectsSemanticsBelow sem₀ (A, 2) (fun d => alphRetract I (q' d)) :=
    hq'.map_bottom_reflecting (fun d => d.2.2) (isStepShifter_alphRetract hI)
      (alphRetract_bot_reflecting (I := I))
  have hr₂ := hr₁.gradeCap (fun k => roundDownVis k I (max γ δ))
    (fun k k' hkk' => roundDownVis_anti hkk' _) (fun k _ => roundDownVis_selfVis k I _)
  refine ⟨fun d => min (alphRetract I (q' (baseEquiv d)))
    (roundDownVis (D₀.grade (baseEquiv d).1) I (max γ δ)), ?_, RespectsBase.ofBelow hr₂, ?_, ?_,
    ?_⟩
  · exact fun d => min_mem_alph (alphRetract_mem_alph hI _) (roundDownVis_mem _ _ _)
  · exact fun d => (min_le_right _ _).trans (roundDownVis_le _ _ _)
  · intro d
    have hγg : γ ≤ roundDownVis (D₀.grade (baseEquiv d).1) I (max γ δ) :=
      le_roundDownVis hγm (SelfVis.mono hγv d.2) (le_max_left _ _)
    calc min (min (alphRetract I (q' (baseEquiv d)))
          (roundDownVis (D₀.grade (baseEquiv d).1) I (max γ δ))) γ
        = min (alphRetract I (q' (baseEquiv d))) γ := by rw [min_assoc, min_eq_right hγg]
      _ = alphRetract I (min (q' (baseEquiv d)) γ) := by
          rw [(alphRetract_mono hI).map_min, alphRetract_eq_self_of_mem_alph hγm]
      _ = alphRetract I (min (F d) γ) := by
          rw [hcap (baseEquiv d)]
          rfl
      _ = min (F d) γ := by
          rw [(alphRetract_mono hI).map_min, alphRetract_eq_self_of_mem_alph (hF d),
            alphRetract_eq_self_of_mem_alph hγm]
  · intro d hd
    have hq : q' (baseEquiv d) = G d := hres ⟨d.1, ⟨hd, d.2⟩⟩
    change min (alphRetract I (q' (baseEquiv d)))
      (roundDownVis (D₀.grade (baseEquiv d).1) I (max γ δ)) = G d
    rw [hq, alphRetract_eq_self_of_mem_alph (hG d)]
    exact min_eq_left (le_roundDownVis (hG d) (hGr.orderly d) ((hGδ d).trans (le_max_right _ _)))

end Derivation

/-! ## Specialization to the cutoff-correct family -/

section Cutoff

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}

/-- When the prescribed scope contains the three reference cells, cutoff-correctness depends only
on the labels under it. -/
theorem cutoffCorrect_congr_of_scope (c ρ q : Cell D₀) (hc : D₀.grade c ≤ 2)
    (hρ : D₀.grade ρ ≤ 2) (hq : D₀.grade q ≤ 2) {C : Finset ι} (hcC : D₀.scope c ⊆ C)
    (hρC : D₀.scope ρ ⊆ C) (hqC : D₀.scope q ⊆ C) (F F' : BaseCells D₀ 2 → ExtOrd)
    (h : ∀ d : BaseCells D₀ 2, D₀.scope d.1 ⊆ C → F d = F' d)
    (hF : CutoffCorrect c ρ q hc hρ hq F) : CutoffCorrect c ρ q hc hρ hq F' := by
  unfold CutoffCorrect at hF ⊢
  rw [← h ⟨ρ, hρ⟩ hρC, ← h ⟨c, hc⟩ hcC, ← h ⟨q, hq⟩ hqC]
  exact hF

variable (sem₀ : Semantics D₀) (I M : ℕ) (c ρ q : Cell D₀) (hc : D₀.grade c = 2)
  (hρ : D₀.grade ρ ≤ 2) (hq : D₀.grade q ≤ 2)
  (hAk : ∀ k, 1 ≤ k → k ≤ M + 2 → (A, k) ∈ Plan.gradedPlan D₀.plan)
  (hI : Fintype.card (Cell D₀) + 2 ≤ I) (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A)

include sem₀ I M c ρ q hc hρ hq hAk hI hproper

/-- The tower's lower sets, over the cutoff-correct family. -/
local notation "Tbelow" =>
  CellScheme.below (tower sem₀ I M (CutoffCorrect c ρ q hc.le hρ hq) hAk)
/-- The member row of a cutoff-correct member. -/
local notation "MROW" =>
  memberRow sem₀ I M (CutoffCorrect c ρ q hc.le hρ hq) hAk hI hproper

/-- **The lift for coded inputs over a bountiful base, on the cutoff-correct family.**  With the
prescribed scope containing the three reference cells, ordinary bountifulness of the base gives,
for an ambient the row of a correct member `m` at its cap and a prescribed input the row of a
correct member `mp` restricted to `D⟨C,2⟩` agreeing under `m.γ`, a lift by controller change
agreeing with the ambient on the full decoded vector under its cap. -/
theorem lift_of_coded_input_cutoff (hB : sem₀.IsBountiful) (C : Finset ι)
    (hC : (C, 2) ∈ Plan.gradedPlan D₀.plan) (hCA : C ≠ A) (hcC : D₀.scope c ⊆ C)
    (hρC : D₀.scope ρ ⊆ C) (hqC : D₀.scope q ⊆ C)
    (m mp : Member sem₀ I 2 (CutoffCorrect c ρ q hc.le hρ hq))
    (hagree : ∀ d : BaseCells D₀ 2, D₀.scope d.1 ⊆ C → min (mp.F d) m.γ = min (m.F d) m.γ) :
    ∃ q' : Tbelow (A, 2) → ExtOrd,
      RespectsSemanticsBelow
        (towerSem sem₀ I M (CutoffCorrect c ρ q hc.le hρ hq) hAk hI hproper) (A, 2) q' ∧
      (∀ d, min (q' d) m.γ = min (MROW m d) m.γ) ∧
      ∀ d : Tbelow (C, 2), q' (CellScheme.below.mono (gradedLe_full_two hC) d) =
        MROW mp (CellScheme.below.mono (gradedLe_full_two hC) d) :=
  lift_of_coded_input' sem₀ I M (CutoffCorrect c ρ q hc.le hρ hq) hAk hI hproper
    (codedBountiful_of_isBountiful hB (hAk 2 (by omega) (by omega)) (by omega)) C hC hCA m mp
    hagree (cutoffCorrect_congr_of_scope c ρ q hc.le hρ hq hcC hρC hqC)

end Cutoff

end VaughtConjecture.Knight
