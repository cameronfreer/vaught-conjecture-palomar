/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingCutDecoder

/-! # Literal lower readback by a cap-preserving rank table

The low rank segment retains the actual ambient chart. The high segment is
the finite maximum of the prescribed values already encountered. Distinct
prescriptions and literal top are retained without synchronizing physical
sections with raw receiving fields.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingRankLift
open Transform Value ExtOrd SharpWitnessComposition FullRowLifting
open LadderScalarRendering
noncomputable section

/-- Every occupied rank has an actual field representative. -/
theorem exists_field_rank {X : Type*} [Fintype X] (a : X → ExtOrd) {i : ℕ}
    (hi : 0 < i) (hic : i ≤ (values a).card) : ∃ f, fieldRank a f = i := by
  classical
  let S := values a
  have he : S.image (rank S) = Finset.Icc 1 S.card := by
    apply Finset.eq_of_subset_of_card_le
    · intro n hn
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_Icc.mpr ⟨rank_pos hx, rank_le_card _ _⟩
    · have hinj : Set.InjOn (rank S) S := by
        intro x hx y hy hxy
        rcases lt_trichotomy x y with h | h | h
        · exact ((rank_strict hy h).ne hxy).elim
        · exact h
        · exact ((rank_strict hx h).ne hxy.symm).elim
      rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]
      omega
  have hm : i ∈ S.image (rank S) := by rw [he]; exact Finset.mem_Icc.mpr ⟨hi, hic⟩
  obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hm
  obtain ⟨_, f, hf⟩ := mem_values.mp hx
  exact ⟨f, by change rank S (a f) = i; rw [hf]; exact hxi⟩

open Classical in
def table {X : Type*} [Fintype X] (r : X → ℕ) (p : X → ExtOrd)
    (f : ℕ → ExtOrd) (k : ℕ) (γ : ExtOrd) (i : ℕ) : ExtOrd :=
  if i < k then f i else max γ ((Finset.univ.filter (fun d => r d ≤ i)).sup p)

/-- Ordered private requirements have a literal extension of the frozen rank
prefix. Every high rank stays above the original cap. -/
theorem exists_table {X : Type*} [Finite X] (a b : X → ℕ) (p : X → ExtOrd)
    (f : ℕ → ExtOrd) {k : ℕ} {γ : ExtOrd}
    (hk : 0 < k) (hf : Monotone f) (h0 : f 0 = ⊥)
    (hfv : ∀ i, SelfVis 1 (f i)) (hpv : ∀ d, SelfVis 1 (p d)) (hγ : SelfVis 1 γ)
    (hlow : ∀ i, i < k → f i < γ) (hreach : γ ≤ f k)
    (hprefix : ∀ d, min (a d) k = min (b d) k)
    (hag : ∀ d, min (f (a d)) γ = min (p d) γ)
    (horder : ∀ d e, b d ≤ b e → p d ≤ p e) :
    ∃ g, Monotone g ∧ g 0 = ⊥ ∧ (∀ i, SelfVis 1 (g i)) ∧
      (∀ i, i < k → g i = f i) ∧ γ ≤ g k ∧ ∀ d, g (b d) = p d := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let g := table b p f k γ
  have glow (i) (hi : i < k) : g i = f i := ite_eq_left hi
  have ghigh (i) (hi : k ≤ i) :
      g i = max γ ((Finset.univ.filter (fun d => b d ≤ i)).sup p) := ite_eq_right (not_lt.mpr hi)
  have gh (i) (hi : k ≤ i) : γ ≤ g i := by rw [ghigh i hi]; exact le_max_left _ _
  refine ⟨g, ?_, (glow 0 hk).trans h0, ?_, glow, gh k le_rfl, ?_⟩
  · intro i j hij
    by_cases hj : j < k
    · rw [glow i (hij.trans_lt hj), glow j hj]; exact hf hij
    · by_cases hi : i < k
      · rw [glow i hi]; exact (hlow i hi).le.trans (gh j (not_lt.mp hj))
      · rw [ghigh i (not_lt.mp hi), ghigh j (not_lt.mp hj)]
        apply max_le_max_left
        apply Finset.sup_le
        intro d hd
        exact Finset.le_sup (f := p) (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hd).2.trans hij⟩)
  · intro i
    by_cases hi : i < k
    · rw [glow i hi]; exact hfv i
    · rw [ghigh i (not_lt.mp hi)]
      apply selfVis_max hγ
      exact Finset.sup_induction (selfVis_bot 1) (fun _ ha _ hb => selfVis_max ha hb)
        (fun d _ => hpv d)
  · intro d
    by_cases hd : b d < k
    · have he : a d = b d := by have := hprefix d; omega
      rw [glow _ hd]
      exact PairedSlotEncoding.eq_of_cap_eq_lt (he ▸ hag d) (hlow _ hd)
    · have ha : k ≤ a d := by have := hprefix d; omega
      have hpd : γ ≤ p d := by
        apply min_eq_right_iff.mp
        exact (hag d).symm.trans (min_eq_right (hreach.trans (hf ha)))
      rw [ghigh _ (not_lt.mp hd)]
      apply le_antisymm
      · exact max_le hpd (Finset.sup_le (fun e he => horder e d (Finset.mem_filter.mp he).2))
      · exact (Finset.le_sup (s := Finset.univ.filter (fun e => b e ≤ b d)) (f := p)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ d, le_rfl⟩)).trans
          (le_max_right _ _)

/-- A bounded grade-one map reads every actual rung, including the long tip.
Lawfulness of its physical image is subsequently obtained by positive-cap
transport, not by claiming arbitrary faithful composition. -/
theorem exists_rank_decoder (H : ℕ) (g : ℕ → ExtOrd) (hg : Monotone g)
    (h0 : g 0 = ⊥) (hv : ∀ i, SelfVis 1 (g i)) :
    ∃ τ, BoundedMap 1 τ ∧ ∀ i, i ≤ H → τ (SupportLadderRows.source H i) = g i := by
  let s : Fin (H + 1) → ExtOrd := fun i => SupportLadderRows.source H i
  let v : Fin (H + 1) → ExtOrd := fun i => g i
  have ho : ∀ i j, s i ≤ s j → v i ≤ v j := by
    intro i j h
    have hh := (SupportLadderRows.source_le_iff H i j).mp h
    rw [min_eq_left (by omega : i.val ≤ H), min_eq_left (by omega : j.val ≤ H)] at hh
    exact hg hh
  have hz : ∀ i, s i = ⊥ → v i = ⊥ := by
    intro i h
    have hh := (SupportLadderRows.source_bot_iff H i).mp h
    rw [min_eq_left (by omega : i.val ≤ H)] at hh
    exact (congrArg g hh).trans h0
  refine ⟨orderInterpolate s v,
    orderInterpolate_bounded (fun i => SupportLadderRows.source_visible _ _) (fun i => hv i), ?_⟩
  intro i hi
  exact orderInterpolate_read ho hz ⟨i, by omega⟩

end
end VaughtConjecture.Knight.ReceivingRankLift
