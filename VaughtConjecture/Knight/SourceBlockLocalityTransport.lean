/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PrefixFaithfulInterpolation

/-! # Positive-cap agreement repairs locality composition

For a bounded-commuting scalar image of a respecting labelling, the only remaining
locality condition is the capped bottom pattern on each actual source block.
This is necessary and sufficient, independent of off-row witness choices.
Agreement below any nonbottom cap with a respecting ambient supplies that pattern.
No global faithful outer shifter, bottom reflection, or extra visibility grade is
needed. This does not construct the scalar map or the replacement base labelling.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SharpWitnessComposition

open Transform Value ExtOrd

/-- A normalized witness supplies bounded commutation at its own grade. -/
theorem boundedMap_of_witness {m : ℕ} {τ : ExtOrd → ExtOrd}
    (hτ : Witness (gTop m) τ) : BoundedMap m τ where
  bot := hτ.bot
  mono := hτ.mono
  comm x k i hk hi := hτ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi

/-- The outer scalar map needs bounded commutation, not a global faithful witness. -/
theorem BoundedMap.comp_witness {m K : ℕ} {σ ν : ExtOrd → ExtOrd}
    (hν : BoundedMap K ν) (hσ : Witness (gTop m) σ) (hmK : m ≤ K) :
    BoundedMap m (ν ∘ σ) where
  bot := by simp only [Function.comp_apply, hσ.bot, hν.bot]
  mono := hν.mono.comp hσ.mono
  comm x k i hk hi := by
    simp only [Function.comp_apply]
    rw [(boundedMap_of_witness hσ).comm x k i hk hi, hν.comm _ k i (hk.trans hmK) hi]

section Scheme

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

/-- One implication per actual pair of source occurrences. No auxiliary floor values occur. -/
def RowBlockBottom (sem : Semantics D) (BJ : Finset ι × ℕ)
    (r : D.below BJ → ExtOrd) : Prop :=
  ∀ (c : D.below BJ) (d e : D.below (D.cell c.1)),
    blockFloor (sem.E c.1 d) = blockFloor (sem.E c.1 e) →
    min (r (CellScheme.below.incl c d)) (r c) = ⊥ →
    min (r (CellScheme.below.incl c e)) (r c) = ⊥

/-- Actual respect forces the source-block bottom law, using normalized local witnesses. -/
theorem rowBlockBottom_of_respects {q : D.below BJ → ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) : RowBlockBottom sem BJ q := by
  obtain ⟨C⟩ := exists_localCharts hq
  intro c d e hb hz
  rw [← C.read c d] at hz
  rw [← C.read c e]
  exact witness_bot_of_same_block (C.witness c) hb hz

/-- For a scalar image of a respecting labelling, the source-block bottom law is exact.
The test is stated entirely in terms of semantic sources and actual capped target labels. -/
theorem map_respects_iff_rowBlockBottom {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) {K : ℕ} {ν : ExtOrd → ExtOrd}
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) (hν : BoundedMap K ν) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) ↔
      RowBlockBottom sem BJ (fun d => ν (r d)) := by
  constructor
  · exact rowBlockBottom_of_respects
  · intro hb
    obtain ⟨C⟩ := exists_localCharts hr
    refine ⟨?_, ?_, ?_⟩
    · intro d
      have h := hν.comm (r d) (D.grade d.1) (D.grade d.1) (hK d) le_rfl
      rwa [← hr.orderly d] at h
    · intro c
      classical
      let _ := Fintype.ofFinite (D.below (D.cell c.1))
      let s := Finset.univ.image (sem.E c.1)
      let hf := hν.comp_witness (C.witness c) (hK c)
      have hbs : BlockBottom s (ν ∘ C.shift c) := by
        intro x hx y hy hxy hz
        obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hy
        change ν (C.shift c (sem.E c.1 e)) = ⊥
        change ν (C.shift c (sem.E c.1 d)) = ⊥ at hz
        rw [C.read c d, hν.mono.map_min] at hz
        rw [C.read c e, hν.mono.map_min]
        exact hb c d e hxy hz
      obtain ⟨τ, hτ, hread⟩ := (hf.interpolate_iff_source_blocks s).mpr hbs
      apply hτ.transformsTo
      intro d
      have hd : D.grade d.1 ≤ D.grade c.1 := d.2.2
      rw [gTop_of_le hd, min_top_right,
        hread _ (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩)]
      change min (ν (r (CellScheme.below.incl c d))) (ν (r c)) =
        ν (C.shift c (sem.E c.1 d))
      rw [C.read c d, hν.mono.map_min]
    · intro d c hs hg
      obtain ⟨e, he, hde⟩ := hr.availability d c hs hg
      exact ⟨e, he, hν.mono hde⟩

/-- Equal cellwise bottom flags give equal capped bottom flags at every controller. -/
theorem rowBlockBottom_of_same_pattern {q r : D.below BJ → ExtOrd}
    (hq : RowBlockBottom sem BJ q) (hpattern : ∀ d, r d = ⊥ ↔ q d = ⊥) :
    RowBlockBottom sem BJ r := by
  have he (c : D.below BJ) (d : D.below (D.cell c.1)) :
      min (r (CellScheme.below.incl c d)) (r c) = ⊥ ↔
        min (q (CellScheme.below.incl c d)) (q c) = ⊥ := by
    simp only [min_eq_bot, hpattern]
  intro c d e hb hz
  exact (he c e).mpr (hq c d e hb ((he c d).mp hz))

/-- Capped agreement at a nonbottom cap preserves the cellwise bottom flag. -/
theorem bottom_pattern_of_cap_agreement {X : Type*} {q r : X → ExtOrd} {γ : ExtOrd}
    (hγ : γ ≠ ⊥) (hag : ∀ d, min (r d) γ = min (q d) γ) :
    ∀ d, r d = ⊥ ↔ q d = ⊥ := by
  intro d
  have h := hag d
  have hr : min (r d) γ = ⊥ ↔ r d = ⊥ := by simp only [min_eq_bot, hγ, or_false]
  have hq : min (q d) γ = ⊥ ↔ q d = ⊥ := by simp only [min_eq_bot, hγ, or_false]
  rw [← hr, ← hq, h]

/-- Positive-cap agreement supplies all the source-block checks. The transformed labelling's
respect is a conclusion, not an assumption. The cap need not satisfy a visibility hypothesis. -/
theorem map_respects_of_positive_cap_agreement {q r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) (hq : RespectsSemanticsBelow sem BJ q)
    {K : ℕ} {ν : ExtOrd → ExtOrd} (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hν : BoundedMap K ν) {γ : ExtOrd} (hγ : γ ≠ ⊥)
    (hag : ∀ d, min (ν (r d)) γ = min (q d) γ) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) := by
  apply (map_respects_iff_rowBlockBottom hr hK hν).mpr
  exact rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects hq)
    (bottom_pattern_of_cap_agreement hγ hag)

end Scheme

end VaughtConjecture.Knight.SharpWitnessComposition
