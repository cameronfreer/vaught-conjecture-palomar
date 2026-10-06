/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PositiveNormalization
public import VaughtConjecture.Knight.MixedGradeInterpolation

/-! # Bottom-reflecting interpolation on finitely many ordinal blocks

The map is built from affine block rays and a nonbottom baseline. Its purpose is
incoming-face transport: a lawful requested labelling remains lawful when mapped
to source columns. This is not an inverse-transformation principle.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

namespace FiniteOrbitEmbedding

open Classical in
/-- An affine block, followed by its visible endpoint and preceded by bottom. -/
noncomputable def ray (K : ℕ) (μ ν : Ordinal.{0}) : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ofOrd (ν + K)
  | some (some ξ) =>
      if limitPart ξ < μ then ⊥
      else if limitPart ξ = μ then ofOrd (ν + (min (finitePart ξ) K : ℕ))
      else ofOrd (ν + K)

@[simp] theorem ray_bot (K : ℕ) (μ ν : Ordinal.{0}) : ray K μ ν ⊥ = ⊥ := rfl

open Classical in
theorem ray_ofOrd (K : ℕ) (μ ν ξ : Ordinal.{0}) :
    ray K μ ν (ofOrd ξ) =
      if limitPart ξ < μ then ⊥
      else if limitPart ξ = μ then ofOrd (ν + (min (finitePart ξ) K : ℕ))
      else ofOrd (ν + K) := rfl

theorem ray_le (K : ℕ) (μ ν : Ordinal.{0}) (x : ExtOrd) :
    ray K μ ν x ≤ ofOrd (ν + K) := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨ξ, rfl⟩
  · exact bot_le
  · exact le_rfl
  · change (if limitPart ξ < μ then ⊥ else if limitPart ξ = μ then _ else _) ≤ _
    split_ifs
    · exact bot_le
    · exact ofOrd_le_ofOrd.mpr (add_le_add_right (Nat.cast_le.mpr (min_le_right _ _)) _)
    · exact le_rfl

theorem ray_mono (K : ℕ) (μ ν : Ordinal.{0}) : Monotone (ray K μ ν) := by
  classical
  intro x y hxy
  rcases ExtOrd.cases x with rfl | rfl | ⟨ξ, rfl⟩
  · exact bot_le
  · have hy : y = ⊤ := top_le_iff.mp hxy
    rw [hy]
  · rcases ExtOrd.cases y with rfl | rfl | ⟨ζ, rfl⟩
    · exact False.elim (not_ofOrd_le_bot _ hxy)
    · exact ray_le K μ ν _
    · have hl := limitPart_mono (ofOrd_le_ofOrd.mp hxy)
      change (if limitPart ξ < μ then ⊥ else if limitPart ξ = μ then _ else _) ≤
        (if limitPart ζ < μ then ⊥ else if limitPart ζ = μ then _ else _)
      by_cases hx : limitPart ξ < μ
      · rw [ite_eq_left hx]; exact bot_le
      have hy : ¬ limitPart ζ < μ := fun h => hx (hl.trans_lt h)
      rw [ite_eq_right hx, ite_eq_right hy]
      by_cases he : limitPart ξ = μ
      · rw [ite_eq_left he]
        by_cases hf : limitPart ζ = μ
        · rw [ite_eq_left hf]
          apply ofOrd_le_ofOrd.mpr
          exact add_le_add_right (Nat.cast_le.mpr (min_le_min_right K
            (finitePart_le_of_le (he.trans hf.symm) (ofOrd_le_ofOrd.mp hxy)))) _
        · rw [ite_eq_right hf]
          exact ofOrd_le_ofOrd.mpr
            (add_le_add_right (Nat.cast_le.mpr (min_le_right _ _)) _)
      · have hf : ¬ limitPart ζ = μ := fun h =>
          he (le_antisymm (h ▸ hl) (not_lt.mp hx))
        rw [ite_eq_right he, ite_eq_right hf]

theorem ray_step (K : ℕ) {μ ν : Ordinal.{0}} (hν : limitPart ν = ν) :
    IsStepShifter K (ray K μ ν) where
  map_bot := rfl
  mono := ray_mono K μ ν
  selfVis := by
    classical
    intro x k hk hx
    have hfp (j : ℕ) : finitePart (ν + j) = j := by
      simpa only [hν] using finitePart_limitPart_add_nat ν j
    have hv (j : ℕ) (hj : k ≤ j) : extVisibilityReplace (ofOrd (ν + j)) k k =
        ofOrd (ν + j) := by
      apply selfVis_ofOrd_iff.mpr
      rwa [hfp j]
    rcases ExtOrd.cases x with rfl | rfl | ⟨ξ, rfl⟩
    · rfl
    · exact hv K hk
    · rw [ray_ofOrd]
      split_ifs
      · rfl
      · exact hv _ (le_min (selfVis_ofOrd_iff.mp hx) hk)
      · exact hv K hk
  blockwise := by
    classical
    intro ξ
    by_cases hl : limitPart ξ < μ
    · exact Or.inr ⟨⊥, rfl, fun i _ => by
        simp only [ray_ofOrd, limitPart_limitPart_add_nat, ite_eq_left hl]⟩
    by_cases he : limitPart ξ = μ
    · refine Or.inl ⟨ν, ?_, ?_⟩
      · have h := finitePart_limitPart ν
        rwa [hν] at h
      · intro i hi
        simp only [ray_ofOrd, limitPart_limitPart_add_nat, finitePart_limitPart_add_nat,
          ite_eq_right hl, ite_eq_left he, min_eq_left hi]
    · refine Or.inr ⟨ofOrd (ν + K), ?_, ?_⟩
      · apply selfVis_ofOrd_iff.mpr
        simpa only [hν] using (finitePart_limitPart_add_nat ν K).ge
      · intro i hi
        simp only [ray_ofOrd, limitPart_limitPart_add_nat, ite_eq_right hl, ite_eq_right he]
  bot_blocks := by
    classical
    intro ξ ζ he hx
    change (if limitPart ξ < μ then ⊥ else if limitPart ξ = μ then _ else _) = ⊥ at hx
    change (if limitPart ζ < μ then ⊥ else if limitPart ζ = μ then _ else _) = ⊥
    by_cases hl : limitPart ξ < μ
    · rw [← he, ite_eq_left hl]
    · split_ifs at hx <;> simp_all only [ofOrd_ne_bot]

/-- Exact readback on every finite offset up to the grade bound. -/
theorem ray_at (K : ℕ) {μ ν : Ordinal.{0}} (hμ : limitPart μ = μ)
    {i : ℕ} (hi : i ≤ K) : ray K μ ν (ofOrd (μ + i)) = ofOrd (ν + i) := by
  classical
  have hl : limitPart (μ + i) = μ := by
    simpa only [hμ] using limitPart_limitPart_add_nat μ i
  have hf : finitePart (μ + i) = i := by
    simpa only [hμ] using finitePart_limitPart_add_nat μ i
  rw [ray_ofOrd, hl, hf, ite_eq_right (lt_irrefl μ), ite_eq_left rfl, min_eq_left hi]

/-- The initial ray reflects bottom while retaining the finite offsets in block zero. -/
theorem baseline_reflects_bottom (K : ℕ) (x : ExtOrd)
    (hx : ray K 0 0 x = ⊥) : x = ⊥ := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨ξ, rfl⟩
  · rfl
  · exact False.elim (ofOrd_ne_bot _ hx)
  · rw [ray_ofOrd, ite_eq_right (not_lt.mpr (zero_le (a := limitPart ξ)))] at hx
    split_ifs at hx <;> exact False.elim (ofOrd_ne_bot _ hx)

section Finite

variable {I : Type*} [Fintype I] (K : ℕ) (μ ν : I → Ordinal.{0})

/-- The nonbottom baseline and one ray per prescribed block. Repeated input blocks
are allowed; the agreement hypothesis of `interpolate_at` keeps their images equal. -/
noncomputable def interpolate (x : ExtOrd) : ExtOrd :=
  max (ray K 0 0 x) (Finset.univ.sup (fun i => ray K (μ i) (ν i) x))

theorem interpolate_witness (hν : ∀ i, limitPart (ν i) = ν i) :
    Witness (gTop K) (interpolate K μ ν) := by
  have h0 : limitPart (0 : Ordinal.{0}) = 0 := by
    simpa only [Nat.cast_zero] using limitPart_natCast 0
  exact (ray_step K h0).normalizedWitness.max
    (Witness.finset_sup (MixedGradeInterpolation.zero_witness K) Finset.univ
      (fun i _ => (ray_step K (hν i)).normalizedWitness))

theorem interpolate_reflects_bottom (x : ExtOrd)
    (hx : interpolate K μ ν x = ⊥) : x = ⊥ :=
  baseline_reflects_bottom K x (le_bot_iff.mp ((le_max_left _ _).trans_eq hx))

/-- Interpolation is exact on the entire prescribed low orbit, not just its sample.
Positive input blocks need room below their source block for the nonbottom baseline. -/
theorem interpolate_at
    (hμ : ∀ i, limitPart (μ i) = μ i) (hν : ∀ i, limitPart (ν i) = ν i)
    (horder : ∀ i j, μ i < μ j → ν i < ν j)
    (heq : ∀ i j, μ i = μ j → ν i = ν j)
    (hroom : ∀ i, μ i ≠ 0 → Ordinal.omega0 ≤ ν i)
    (j : I) {k : ℕ} (hk : k ≤ K) :
    interpolate K μ ν (ofOrd (μ j + k)) = ofOrd (ν j + k) := by
  classical
  apply le_antisymm
  · apply max_le
    · by_cases hzero : μ j = 0
      · rw [hzero, ray_at K (by simpa only [Nat.cast_zero] using limitPart_natCast 0) hk,
          zero_add]
        exact ofOrd_le_ofOrd.mpr le_add_self
      · calc ray K 0 0 (ofOrd (μ j + k)) ≤ ofOrd (0 + K) := ray_le _ _ _ _
             _ ≤ ofOrd (ν j + k) := ofOrd_le_ofOrd.mpr (by
               rw [zero_add]
               exact (Ordinal.natCast_lt_omega0 K).le.trans ((hroom j hzero).trans le_self_add))
    · apply Finset.sup_le
      intro i _
      have hl : limitPart (μ j + k) = μ j := by
        simpa only [hμ j] using limitPart_limitPart_add_nat (μ j) k
      rcases lt_trichotomy (μ j) (μ i) with hlt | he | hgt
      · rw [ray_ofOrd, hl, ite_eq_left hlt]; exact bot_le
      · rw [← he, ← heq j i he, ray_at K (hμ j) hk]
      · calc ray K (μ i) (ν i) (ofOrd (μ j + k)) ≤ ofOrd (ν i + K) := ray_le _ _ _ _
             _ ≤ ofOrd (ν j + k) := ofOrd_le_ofOrd.mpr (by
               have hh : limitPart (ν i) < limitPart (ν j) := by
                 rw [hν i, hν j]
                 exact horder i j hgt
               have hgap := limitPart_add_omega0_le hh
               rw [hν i, hν j] at hgap
               exact ((add_lt_add_right (Ordinal.natCast_lt_omega0 K) _).le.trans hgap).trans
                 le_self_add)
  · calc ofOrd (ν j + k) = ray K (μ j) (ν j) (ofOrd (μ j + k)) := (ray_at K (hμ j) hk).symm
         _ ≤ Finset.univ.sup (fun i => ray K (μ i) (ν i) (ofOrd (μ j + k))) :=
           Finset.le_sup (f := fun i => ray K (μ i) (ν i) (ofOrd (μ j + k)))
             (Finset.mem_univ j)
         _ ≤ interpolate K μ ν (ofOrd (μ j + k)) := le_max_right _ _

end Finite

/-- Witness form of bottom-reflecting respect transport, useful for finite maxima.
The semantic rows and availability incidences are unchanged. -/
theorem map_respects
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    {K : ℕ} {σ : ExtOrd → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hσ : Witness (gTop K) σ) (hbot : ∀ x, σ x = ⊥ → x = ⊥) :
    RespectsSemanticsBelow sem BJ (fun d => σ (r d)) where
  orderly d := by
    have h := hσ.clause5 (r d) (D.grade d.1)
      (by rw [gTop_of_le (hK d)]; exact le_top) (D.grade d.1) le_rfl
    rwa [← hr.orderly d] at h
  locality c := by
    let owner : D.below (D.cell c.1) := ⟨c.1, GradedLe.refl _⟩
    let p : D.below (D.cell c.1) → ExtOrd := fun d => r (CellScheme.below.incl c d)
    exact map_capped_locality_of_bottom_reflecting
      (c := owner) (p := p) (fun d => d.2.2) (hK c) (hr.orderly c).symm
      (hr.locality c) hσ hbot
  availability c d hs hg := by
    obtain ⟨e, he, hle⟩ := hr.availability c d hs hg
    exact ⟨e, he, hσ.mono hle⟩

/-- All incoming localities and availability follow together from the constructed map. -/
theorem incoming_respects
    {ι I : Type*} [DecidableEq ι] [Fintype I]
    {A : Finset ι} {D : CellScheme A} {sem : Semantics D} {BJ : Finset ι × ℕ}
    {r : D.below BJ → ExtOrd} {K : ℕ} (μ ν : I → Ordinal.{0})
    (hν : ∀ i, limitPart (ν i) = ν i)
    (hr : RespectsSemanticsBelow sem BJ r) (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) :
    RespectsSemanticsBelow sem BJ (fun d => interpolate K μ ν (r d)) :=
  map_respects hr hK (interpolate_witness K μ ν hν) (interpolate_reflects_bottom K μ ν)

end FiniteOrbitEmbedding

end VaughtConjecture.Knight
