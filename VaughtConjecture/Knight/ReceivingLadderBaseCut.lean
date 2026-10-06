/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingLadderExtraction
public import VaughtConjecture.Knight.SharpWitnessComposition

/-! # The active grade-one cut on the installed long ladder

An arbitrary lawful lower ambient supplies a faithful whole-coordinate chart.
An active original coordinate puts the first reaching rank strictly below the
spare tip. Thus every reading below the cut is short, although the complete
leaf row is not. No canonical-ambient or selected-display hypothesis is used.

This is the low/high receipt part of the grade-one base, not its replacement
anchor construction or a scope-raising lifting theorem.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingLadderBaseCut
open Transform Value ExtOrd ReceivingLadderCarrier SharpWitnessComposition
noncomputable section

variable {L : ℕ} {X Q U : Type*} [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)
  (field : Cell C → X) (request : X) (profile : Q → X → ℕ)

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC
local notation "idx" => lowerIndex (L := L) (U := U) C hC field request profile
local notation "src" => fun a d => SupportLadderRows.source L (idx a d)

theorem index_bound (hbound : ∀ a x, profile a x ≤ L) (a : Q) (d : Cell D) :
    idx a d ≤ L := by
  cases hv : view C hC d with
  | inl c => simpa only [lowerIndex, hv] using hbound a (field c)
  | inr z =>
    cases z with
    | request => simpa only [lowerIndex, hv] using hbound a request
    | ladder b v =>
      simpa only [lowerIndex, hv] using SupportLadderRows.index_le (profile := profile) a v
    | upper b a node => simp only [lowerIndex, hv, Nat.zero_le]
    | apex => simp only [lowerIndex, hv, Nat.zero_le]

/-- Availability and actual leaf locality give an exact, bounded faithful
chart on the whole lower domain, including unused rungs and both copies. -/
theorem exists_chart [Nonempty Q] (hL : 0 < L) (hbound : ∀ a x, profile a x ≤ L)
    (b : Bool) (sem : Semantics D)
    (hrows : HasLadderRows C hC field request profile sem)
    {q : (D).below (scope b, 1) → ExtOrd}
    (hq : RespectsSemanticsBelow sem (scope b, 1) q) :
    ∃ a σ, Witness (gTop 1) σ ∧
      (∀ x, σ x ≤ q (tableAt C hC b (GradedLe.refl _) (SupportLadderRows.leaf hL a))) ∧
      ∀ d, σ (src a d.1) = q d := by
  obtain ⟨a, f, hf, _, _, hread⟩ := exists_lowerShapeBelow C hC field request profile
    hL hbound b (GradedLe.refl _) sem hrows q hq
  let c := tableAt (X := X) (U := U) C hC b (GradedLe.refl _) (SupportLadderRows.leaf hL a)
  have hleaf : q c = f L := by
    have hh := hread c
    simpa only [c, tableAt, lowerImage, lowerIndex, view_added,
      SupportLadderRows.index_leaf, FiniteProfileControllers.cut_refl] using hh
  have hdom (d : (D).below (scope b, 1)) : q d ≤ q c := by
    exact (hread d).trans_le
      ((hf (index_bound C hC field request profile hbound a d.1)).trans_eq hleaf.symm)
  let self : (D).below ((D).cell c.1) := ⟨c.1, GradedLe.refl _⟩
  let qloc : (D).below ((D).cell c.1) → ExtOrd := fun d => q (CellScheme.below.incl c d)
  have hm : ∀ d : (D).below ((D).cell c.1), (D).grade d.1 ≤ (D).grade self.1 := fun d => d.2.2
  have hv : SelfVis ((D).grade self.1) (qloc self) := (hq.orderly c).symm
  obtain ⟨σ, hσ, hboundσ, hr⟩ := exists_bounded_exact_capped_witness hm hv (hq.locality c)
  have hcgrade : (D).grade c.1 = 1 := ladder_grade C hC b _
  refine ⟨a, σ, hcgrade ▸ hσ, hboundσ, ?_⟩
  intro d
  let e : (D).below ((D).cell c.1) :=
    ⟨d.1, by change GradedLe ((D).cell d.1) ((D).cell (added C hC _))
             rw [added_index]; exact d.2⟩
  have he := hr e
  have hrow : sem.E c.1 e = src a d.1 := by
    calc
      sem.E c.1 e = ladderRow C hC field request profile (SupportLadderRows.leaf hL a) e.1 :=
        hrows b (SupportLadderRows.leaf hL a) e
      _ = src a d.1 := by rw [ladderRow, SupportLadderRows.ceiling_leaf]; rfl
  rw [hrow] at he
  exact he.trans (min_eq_left (hdom d))

theorem source_short_of_rank_lt {i : ℕ} (hi : i < L) :
    Short 1 (SupportLadderRows.source L i) := by
  rw [SupportLadderRows.source_short hi.le (Or.inl hi)]
  unfold SlotControllerFamily.value
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)

/-- The first reaching rank is constructed, not supplied. Its strict bound
comes from an active original field, not from shortness of the long leaf. -/
theorem exists_first_cut {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop 1) σ)
    {γ : ExtOrd} (hpos : ⊥ < γ) {t : ℕ} (ht : t < L)
    (hactive : γ ≤ σ (SupportLadderRows.source L t)) :
    ∃ k, 0 < k ∧ k ≤ t ∧
      γ ≤ σ (SupportLadderRows.source L k) ∧
      (∀ i, i < k → σ (SupportLadderRows.source L i) < γ) ∧
      (∀ i, SupportLadderRows.source L i < SupportLadderRows.source L k →
        Short 1 (SupportLadderRows.source L i)) ∧
      ∀ i, σ (SupportLadderRows.source L i) < γ →
        SupportLadderRows.source L i < SupportLadderRows.source L k := by
  classical
  have hex : ∃ k, γ ≤ σ (SupportLadderRows.source L k) := ⟨t, hactive⟩
  let k := Nat.find hex
  have hk : γ ≤ σ (SupportLadderRows.source L k) := Nat.find_spec hex
  have hkt : k ≤ t := Nat.find_min' hex hactive
  have hkpos : 0 < k := by
    by_contra hn
    have he : k = 0 := by omega
    rw [he, SupportLadderRows.source_zero, hσ.bot] at hk
    exact (not_le_of_gt hpos) hk
  refine ⟨k, hkpos, hkt, hk, fun i hi => not_le.mp (Nat.find_min hex hi), ?_, ?_⟩
  · intro i hi
    have hik : i < k := by
      by_contra hn
      exact (not_le_of_gt hi) (SupportLadderRows.source_mono L (not_lt.mp hn))
    exact source_short_of_rank_lt ((hik.trans_le hkt).trans ht)
  · intro i hi
    by_contra hn
    exact (not_le_of_gt hi) (hk.trans (hσ.mono (not_lt.mp hn)))

/-- The cap calculation only needs receipts on short readings below the
active cut. Long tips and every spare coordinate use cut reach instead. -/
theorem caps_of_short_prefix {Y : Type*} {u v : Y → ExtOrd} {δ γ : ExtOrd}
    {σ μ : ExtOrd → ExtOrd} (hσ : Monotone σ) (hμ : Monotone μ)
    (hσδ : γ ≤ σ δ) (hμδ : γ ≤ μ δ)
    (hprefix : ∀ d, min (v d) δ = min (u d) δ)
    (hlow : ∀ d, u d < δ → Short 1 (u d))
    (hread : ∀ x, Short 1 x → x < δ → min (μ x) γ = min (σ x) γ) :
    ∀ d, min (μ (v d)) γ = min (σ (u d)) γ := by
  intro d
  by_cases hd : u d < δ
  · have he : v d = u d := by
      have hh := hprefix d
      rw [min_eq_left hd.le] at hh
      exact (min_eq_iff.mp hh).elim (fun h => h.1) (fun h => False.elim (ne_of_lt hd h.1.symm))
    rw [he]
    exact hread _ (hlow d hd) hd
  · have hu : δ ≤ u d := not_lt.mp hd
    have hv : δ ≤ v d := by
      apply min_eq_right_iff.mp
      exact (hprefix d).trans (min_eq_right hu)
    rw [min_eq_right (hμδ.trans (hμ hv)), min_eq_right (hσδ.trans (hσ hu))]

end
end VaughtConjecture.Knight.ReceivingLadderBaseCut
