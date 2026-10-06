/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Domain
public import VaughtConjecture.Knight.NormalForm

/-! # The one-point type with a prescribed successor label (Lemma 4.2.2, second clause)

Knight's Lemma 4.2.2 asserts, besides `S^α_1 ≠ ∅` and the mute domain, that for any non-zero
non-limit `γ < α` there is a one-point type with a cell labelled `γ`.  V-C had compiled only
the mute clause (`SemScheme.mute`, `StageType.mute`, `Knight/Domain.lean`).  This module builds
the successor-labelled one-point type faithfully, for every `γ` with `γ + 1 < α`:

* the domain `successorOneSemScheme`: the complete arity-one cell scheme of the mute chain,
  with every row the constant `1` (`successorOneSemantics`).  The rows are coded
  (`1 = ω·0 + 1`, `1 ≤ grade + 1`), orderly (`1` is self-visible at grade `1`), consistent
  (locality by the reflexive transform, availability at the cell itself), and bountiful
  vacuously — an arity-one plan has the single graded pair `(univ, 1)`, so no strict pair
  `⟨C,i⟩ ≺ ⟨B,j⟩` exists (`gradedPair_unique_fin_one`);
* the labelling: the constant `γ + 1`, self-visible at grade `1` for every `γ`
  (`successor_selfVisible`: its finite part is `finitePart γ + 1 ≥ 1`), strictly bounded at
  `α`, and respecting the semantics: locality is the transform `1 ↦ γ + 1` through the
  step shifter `constNonbot (γ + 1)` (`⊥ ↦ ⊥`, everything else to `γ + 1`), whose Def. 2.3.9
  legality — clause 5 included — is the compiled `IsStepShifter.transformsTo` of
  `Knight/NormalForm.lean`; availability is at the cell itself.

`exists_successorOneType_of_lt` is the clause as consumed by the coatom-amalgamation
candidates (`Knight/CoatomAmalgamation.lean`): at a limit stage, for every `γ < α`, a one-point
type with a cell labelled `γ + 1`.  Construction-private, not root-exported. -/

@[expose] public section

namespace VaughtConjecture.Knight

open VaughtConjecture.AmalgamationPlan
open Transform Value ExtOrd

/-! ### The constant-off-bottom shifter -/

/-- The shifter sending `⊥` to `⊥` and every other label to the constant `c`. -/
noncomputable def constNonbot (c : ExtOrd) (x : ExtOrd) : ExtOrd :=
  if x = ⊥ then ⊥ else c

@[simp] theorem constNonbot_bot (c : ExtOrd) : constNonbot c ⊥ = ⊥ := by
  simp [constNonbot]

@[simp] theorem constNonbot_ofOrd (c : ExtOrd) (x : Ordinal) :
    constNonbot c (ofOrd x) = c := by
  simp [constNonbot]

theorem monotone_constNonbot (c : ExtOrd) : Monotone (constNonbot c) := by
  intro x y hxy
  by_cases hx : x = ⊥
  · rw [hx, constNonbot_bot]
    exact bot_le
  have hy : y ≠ ⊥ := by
    intro hy
    apply hx
    exact le_bot_iff.mp (hy ▸ hxy)
  simp [constNonbot, hx, hy]

/-- `constNonbot c` is a `K`-step shifter whenever `c ≠ ⊥` is self-visible at `K`: it is
constant on every block, and its `⊥`-fiber is `{⊥}`. -/
theorem isStepShifter_constNonbot {K : ℕ} {c : ExtOrd}
    (hc0 : c ≠ ⊥) (hc : extVisibilityReplace c K K = c) :
    IsStepShifter K (constNonbot c) where
  map_bot := constNonbot_bot c
  mono := monotone_constNonbot c
  selfVis x k hk _ := by
    by_cases hx : x = ⊥
    · simp [hx]
    rw [show constNonbot c x = c by simp [constNonbot, hx]]
    exact extVisReplace_self_of_le hc hk
  blockwise _ := Or.inr ⟨c, hc, fun i _ => by simp⟩
  bot_blocks _ _ _ hbot := by
    rw [constNonbot_ofOrd] at hbot
    exact absurd hbot hc0

/-! ### Arity one: every cell has grade `1`, and there is one graded pair -/

/-- On a scheme over `Fin 1` every cell has grade `1`. -/
theorem grade_eq_one_of_fin_one (D : CellScheme (ι := Fin 1) Finset.univ) (d : Cell D) :
    D.grade d = 1 := by
  have hpos := D.grade_pos d
  have hscope := D.grade_le_card_scope d
  have hcard : (D.scope d).card ≤ 1 := (Finset.card_le_univ _).trans (by simp)
  omega

/-- The graded plan of a plan on `Fin 1` has a single member, `(univ, 1)`. -/
theorem gradedPair_unique_fin_one
    (D : CellScheme (ι := Fin 1) Finset.univ)
    {X Y : Finset (Fin 1) × ℕ}
    (hX : X ∈ Plan.gradedPlan D.plan) (hY : Y ∈ Plan.gradedPlan D.plan) : X = Y := by
  rcases X with ⟨BX, jX⟩
  rcases Y with ⟨BY, jY⟩
  obtain ⟨_, hjX0, hjXB⟩ := Plan.mem_gradedPlan.mp hX
  obtain ⟨_, hjY0, hjYB⟩ := Plan.mem_gradedPlan.mp hY
  change 0 < jX at hjX0
  change jX ≤ BX.card at hjXB
  change 0 < jY at hjY0
  change jY ≤ BY.card at hjYB
  have hcX : BX.card ≤ 1 := Finset.card_le_univ BX
  have hcY : BY.card ≤ 1 := Finset.card_le_univ BY
  have hjX : jX = 1 := by omega
  have hjY : jY = 1 := by omega
  have hBXcard : BX.card = 1 := by omega
  have hBYcard : BY.card = 1 := by omega
  have hBXeq : BX = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hBXcard])
  have hBYeq : BY = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hBYcard])
  rw [hBXeq, hBYeq, hjX, hjY]

/-! ### The domain: constant row `1` on the arity-one mute scheme -/

/-- The label `1` is self-visible at grade `1`. -/
theorem one_selfVisible :
    extVisibilityReplace (ofOrd (1 : ℕ)) 1 1 = ofOrd (1 : ℕ) := by
  rw [extVisibilityReplace_self_iff]
  refine Or.inr (Or.inr ⟨((1 : ℕ) : Ordinal), rfl, ?_⟩)
  have h := finitePart_limitPart_add_nat (0 : Ordinal) 1
  have hzero : limitPart (0 : Ordinal) = 0 := by simp [limitPart]
  rw [hzero, zero_add] at h
  exact h.symm.le

/-- The semantics on the arity-one mute scheme whose every row is the constant `1`. -/
noncomputable def successorOneSemantics :
    Semantics (SemScheme.muteChain 1).scheme where
  E := fun _ _ => ofOrd (1 : ℕ)
  orderly _ d := by
    change ofOrd (1 : ℕ) = extVisibilityReplace (ofOrd (1 : ℕ))
      ((SemScheme.muteChain 1).scheme.grade d.1)
      ((SemScheme.muteChain 1).scheme.grade d.1)
    rw [grade_eq_one_of_fin_one (D := (SemScheme.muteChain 1).scheme) d.1]
    exact one_selfVisible.symm

/-- The constant-`1` rows are consistent: each row respects the restricted semantics by the
reflexive transform, with availability at the cell itself. -/
theorem successorOneSemantics_consistent : successorOneSemantics.IsConsistent := by
  intro Sig
  refine
    { orderly := successorOneSemantics.orderly Sig
      locality := fun d => by
        change TransformsTo _ (fun _ => ofOrd (1 : ℕ))
          (fun _ => min (ofOrd (1 : ℕ)) (ofOrd (1 : ℕ)))
        simpa using
          (TransformsTo.refl (grade := fun x : (SemScheme.muteChain 1).scheme.below
            ((SemScheme.muteChain 1).scheme.cell d.1) =>
              (SemScheme.muteChain 1).scheme.grade x.1) (fun _ => ofOrd (1 : ℕ)))
      availability := fun _ e _ _ => ⟨e, rfl, le_rfl⟩ }

/-- The arity-one domain with constant row `1`: coded, consistent, bountiful (vacuously —
there is no strict pair of graded indices), complete. -/
noncomputable def successorOneSemScheme : SemScheme 1 where
  scheme := (SemScheme.muteChain 1).scheme
  rows := successorOneSemantics
  rows_coded _ _ := by
    change ExtOrd.IsCodedLabel _ (ofOrd (1 : ℕ))
    exact Or.inr ⟨0, 1, by omega, by simp⟩
  consistent := successorOneSemantics_consistent
  bountiful _ _ hCI hBJ _ hne _ _ _ _ _ _ _ :=
    absurd (gradedPair_unique_fin_one _ hCI hBJ) hne
  complete := (SemScheme.muteChain 1).complete

/-! ### The labelling `γ + 1` -/

/-- Every successor label is self-visible at grade `1`: its finite part is at least `1`. -/
theorem successor_selfVisible (γ : Ordinal) :
    extVisibilityReplace (ofOrd (γ + 1)) 1 1 = ofOrd (γ + 1) := by
  rw [extVisibilityReplace_self_iff]
  refine Or.inr (Or.inr ⟨γ + 1, rfl, ?_⟩)
  have hfp : finitePart (γ + 1) = finitePart γ + 1 := by
    have hdecomp : γ + 1 = (limitPart γ + (finitePart γ : Ordinal)) + 1 :=
      congrArg (fun x : Ordinal => x + 1) (decomposition γ).symm
    have hcast : (finitePart γ : Ordinal) + 1 = ((finitePart γ + 1 : ℕ) : Ordinal) := by simp
    have hnormal : γ + 1 = limitPart γ + ((finitePart γ + 1 : ℕ) : Ordinal) := by
      rw [hdecomp, add_assoc, hcast]
    rw [hnormal, finitePart_limitPart_add_nat]
  rw [hfp]
  exact Nat.le_add_left 1 _

/-- The constant labelling `γ + 1` respects the constant-`1` semantics: orderliness by
self-visibility, locality by the step shifter `constNonbot (γ + 1)` at threshold `1`,
availability at the cell itself. -/
theorem successorOneLabel_respects (γ : Ordinal) :
    RespectsSemantics successorOneSemantics (fun _ => ofOrd (γ + 1)) where
  orderly _ := by
    rw [grade_eq_one_of_fin_one]
    exact (successor_selfVisible γ).symm
  locality Sig := by
    have hgrade : ∀ d : (SemScheme.muteChain 1).scheme.below
        ((SemScheme.muteChain 1).scheme.cell Sig),
        (SemScheme.muteChain 1).scheme.grade d.1 ≤ 1 := fun _ => by
      rw [grade_eq_one_of_fin_one]
    simpa [successorOneSemantics] using
      (isStepShifter_constNonbot (K := 1)
        (c := ofOrd (γ + 1)) (ofOrd_ne_bot _) (successor_selfVisible γ)).transformsTo
          hgrade (fun _ => ofOrd (1 : ℕ))
  availability _ Xi _ _ := ⟨Xi, rfl, le_rfl⟩

/-- **The successor-labelled one-point type** (Lemma 4.2.2, second clause): for `γ + 1 < α`,
the stage type on `successorOneSemScheme` with every cell labelled `γ + 1`. -/
noncomputable def successorOneType (α γ : Ordinal) (hγ : γ + 1 < α) : S α 1 where
  scheme := successorOneSemScheme
  label := fun _ => ofOrd (γ + 1)
  label_bound _ := Or.inl (ofOrd_lt_ofOrd.mpr hγ)
  respects := successorOneLabel_respects γ

/-- For `γ + 1 < α` there is a one-point type with a cell labelled `γ + 1` (the cell exists by
completeness at the graded pair `(univ, 1)`). -/
theorem exists_successorOneType {α γ : Ordinal} (hγ : γ + 1 < α) :
    ∃ (r : S α 1) (Sig : Cell r.scheme.scheme), r.label Sig = ofOrd (γ + 1) := by
  let r := successorOneType α γ hγ
  have hcomplete := r.scheme.complete (Finset.univ, 1)
    (Plan.mem_gradedPlan.mpr ⟨r.scheme.scheme.isPlan.domain_mem, by omega, by simp⟩)
  obtain ⟨Sig, -⟩ := hcomplete
  exact ⟨r, Sig, rfl⟩

/-- At a limit stage, every `γ < α` has a one-point type with a cell labelled `γ + 1`. -/
theorem exists_successorOneType_of_lt {α γ : Ordinal} (hα : Order.IsSuccLimit α)
    (hγ : γ < α) :
    ∃ (r : S α 1) (Sig : Cell r.scheme.scheme), r.label Sig = ofOrd (γ + 1) :=
  exists_successorOneType (hα.add_one_lt hγ)

end VaughtConjecture.Knight
