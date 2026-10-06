/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PositiveNormalization

/-! # Faithful composition on grade-short source rows

A monotone, bottom-preserving map commuting with replacements through grade `m`
can fail the bottom guard at higher grades. Flattening each source block after
offset `m` repairs that guard. It leaves every source of finite part at most `m`
literal. Consequently normalized witnesses compose on such source rows without
bottom reflection, although their literal function composite need not be faithful.

The source condition is stronger than `IsCodedLabel m`, which permits offset
`m + 1`. No unrestricted transitivity or closure for arbitrary coded rows is
asserted. Bottom and top are fixed by the source flattening.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SharpWitnessComposition

open Transform Value ExtOrd

/-- Flatten the unused finite tail, without moving a source to another block. -/
noncomputable def trim (m : ℕ) : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some a) => ofOrd (limitPart a + (min (finitePart a) m : ℕ))

@[simp] theorem trim_bot (m : ℕ) : trim m ⊥ = ⊥ := rfl
@[simp] theorem trim_top (m : ℕ) : trim m ⊤ = ⊤ := rfl
@[simp] theorem trim_ofOrd (m : ℕ) (a : Ordinal.{0}) :
    trim m (ofOrd a) = ofOrd (limitPart a + (min (finitePart a) m : ℕ)) := rfl

theorem trim_eq {m : ℕ} {a : Ordinal.{0}} (ha : finitePart a ≤ m) :
    trim m (ofOrd a) = ofOrd a := by
  rw [trim_ofOrd, min_eq_left ha, decomposition]

theorem trim_mono (m : ℕ) : Monotone (trim m) := by
  intro x y hxy
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact bot_le
  · rw [top_le_iff.mp hxy]
  · rcases ExtOrd.cases y with rfl | rfl | ⟨b, rfl⟩
    · exact False.elim (not_ofOrd_le_bot _ hxy)
    · exact le_top
    · rw [trim_ofOrd, trim_ofOrd, ofOrd_le_ofOrd]
      have hab := ofOrd_le_ofOrd.mp hxy
      rcases (limitPart_mono hab).eq_or_lt with he | hl
      · rw [he]
        exact add_le_add_right (Nat.cast_le.mpr
          (min_le_min_right m (finitePart_le_of_le he hab))) _
      · exact ((add_lt_add_right (Ordinal.natCast_lt_omega0 _) _).le.trans
          (limitPart_add_omega0_le hl)).trans le_self_add

/-- Bounded replacements commute with source flattening. -/
theorem trim_evr (m : ℕ) (x : ExtOrd) {k i : ℕ} (hk : k ≤ m) (hi : i ≤ k) :
    trim m (extVisibilityReplace x k i) = extVisibilityReplace (trim m x) k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rfl
  · rfl
  · by_cases ha : finitePart a < k
    · rw [extVisibilityReplace_of_finitePart_lt ha, trim_ofOrd,
        finitePart_limitPart_add_nat, limitPart_limitPart_add_nat,
        min_eq_left (hi.trans hk), trim_ofOrd,
        extVisibilityReplace_of_finitePart_lt (by
          rw [finitePart_limitPart_add_nat]; exact (min_le_left _ _).trans_lt ha),
        limitPart_limitPart_add_nat]
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp ha), trim_ofOrd,
        extVisibilityReplace_of_le_finitePart (by
          rw [finitePart_limitPart_add_nat]; exact le_min (not_lt.mp ha) hk)]

/-- The weak data needed before repairing the higher-grade bottom guard. -/
structure BoundedMap (m : ℕ) (f : ExtOrd → ExtOrd) : Prop where
  bot : f ⊥ = ⊥
  mono : Monotone f
  comm : ∀ x k i, k ≤ m → i ≤ k →
    f (extVisibilityReplace x k i) = extVisibilityReplace (f x) k i

namespace BoundedMap

variable {m : ℕ} {f : ExtOrd → ExtOrd} (hf : BoundedMap m f)

include hf

/-- If the repaired map kills one point of a block, it kills the entire block. -/
theorem trim_bot_block {a b : Ordinal.{0}} (hab : limitPart a = limitPart b)
    (ha : f (trim m (ofOrd a)) = ⊥) : f (trim m (ofOrd b)) = ⊥ := by
  have hfloor : f (ofOrd (limitPart a)) = ⊥ := by
    apply le_bot_iff.mp
    exact (hf.mono (ofOrd_le_ofOrd.mpr le_self_add)).trans_eq ha
  by_cases hm : m = 0
  · simpa [trim_ofOrd, hm, ← hab] using hfloor
  have he : extVisibilityReplace (ofOrd (limitPart a)) m (min (finitePart b) m) =
      trim m (ofOrd b) := by
    rw [extVisibilityReplace_of_finitePart_lt (by
      rw [finitePart_limitPart]; exact Nat.pos_of_ne_zero hm), limitPart_idem,
      trim_ofOrd, hab]
  rw [← he, hf.comm _ _ _ le_rfl (min_le_right _ _), hfloor,
    extVisibilityReplace_bot]

/-- The repaired function is a full faithful witness at every threshold. -/
theorem witness : Witness (gTop m) (f ∘ trim m) where
  anti := (witness_id m).anti
  vis := (witness_id m).vis
  bot := hf.bot
  mono := hf.mono.comp (trim_mono m)
  clause5 := by
    intro x k hact i hi
    change f (trim m (extVisibilityReplace x k i)) =
      extVisibilityReplace (f (trim m x)) k i
    by_cases hk : k ≤ m
    · rw [trim_evr m x hk hi, hf.comm _ _ _ hk hi]
    · have hz : f (trim m x) = ⊥ := by
        simpa only [Function.comp_apply, gTop_of_gt (not_le.mp hk), le_bot_iff] using hact
      rw [hz, extVisibilityReplace_bot]
      rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
      · exact hf.bot
      · exact hz
      · rw [extVisibilityReplace_ofOrd]
        apply hf.trim_bot_block _ hz
        unfold visibilityReplace
        split_ifs
        · exact (limitPart_limitPart_add_nat _ _).symm
        · rfl

end BoundedMap

/-- Only the low source offsets are used; literal top is also harmless. -/
def Short (m : ℕ) (x : ExtOrd) : Prop :=
  x = ⊥ ∨ x = ⊤ ∨ ∃ a : Ordinal.{0}, x = ofOrd a ∧ finitePart a ≤ m

theorem trim_of_short {m : ℕ} {x : ExtOrd} (hx : Short m x) : trim m x = x := by
  rcases hx with rfl | rfl | ⟨a, rfl, ha⟩
  · rfl
  · rfl
  · exact trim_eq ha

/-- The function composite has bounded commutation, even without bottom reflection. -/
theorem bounded_comp {m K : ℕ} {σ ν : ExtOrd → ExtOrd}
    (hσ : Witness (gTop m) σ) (hν : Witness (gTop K) ν) (hmK : m ≤ K) :
    BoundedMap m (ν ∘ σ) where
  bot := by simp only [Function.comp_apply, hσ.bot, hν.bot]
  mono := hν.mono.comp hσ.mono
  comm := by
    intro x k i hk hi
    simp only [Function.comp_apply]
    rw [hσ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi,
      hν.clause5 (σ x) k (by rw [gTop_of_le (hk.trans hmK)]; exact le_top) i hi]

/-- Repair the composite off the row. Every grade-short source is unchanged. -/
theorem comp_read {m K : ℕ} {σ ν : ExtOrd → ExtOrd}
    (hσ : Witness (gTop m) σ) (hν : Witness (gTop K) ν) (hmK : m ≤ K) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop m) τ ∧
      ∀ x, Short m x → τ x = ν (σ x) := by
  refine ⟨(ν ∘ σ) ∘ trim m, (bounded_comp hσ hν hmK).witness, ?_⟩
  intro x hx
  simp only [Function.comp_apply, trim_of_short hx]

/-- A source-short controller locality survives any normalized outer shifter of
at least its grade. The witness is repaired, not the semantic source row. -/
theorem map_capped_locality
    {X : Type*} {grade : X → ℕ} {E p : X → ExtOrd} {c : X}
    {K : ℕ} {ν : ExtOrd → ExtOrd}
    (hmax : ∀ d, grade d ≤ grade c) (hcK : grade c ≤ K)
    (hshort : ∀ d, Short (grade c) (E d))
    (hvis : SelfVis (grade c) (p c))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c)))
    (hν : Witness (gTop K) ν) :
    TransformsTo grade E (fun d => min (ν (p d)) (ν (p c))) := by
  obtain ⟨σ, hσ, _, hread⟩ := exists_bounded_exact_capped_witness hmax hvis hloc
  obtain ⟨τ, hτ, hτread⟩ := comp_read hσ hν hcK
  apply hτ.transformsTo
  intro d
  rw [gTop_of_le (hmax d), min_top_right, hτread _ (hshort d), hread,
    hν.mono.map_min]

/-- On a source-short scheme, bottom reflection is unnecessary for transport of
respect. This is a structural source hypothesis, not ordinary codedness. -/
theorem map_respects_of_short
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    {K : ℕ} {ν : ExtOrd → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hshort : ∀ c : D.below BJ, ∀ d : D.below (D.cell c.1),
      Short (D.grade c.1) (sem.E c.1 d))
    (hν : Witness (gTop K) ν) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) where
  orderly d := by
    have h := hν.clause5 (r d) (D.grade d.1)
      (by rw [gTop_of_le (hK d)]; exact le_top) (D.grade d.1) le_rfl
    rwa [← hr.orderly d] at h
  locality c := map_capped_locality
    (c := (⟨c.1, GradedLe.refl _⟩ : D.below (D.cell c.1)))
    (p := fun d => r (CellScheme.below.incl c d))
    (fun d => d.2.2) (hK c) (hshort c)
    (hr.orderly c).symm (hr.locality c) hν
  availability d c hs hg := by
    obtain ⟨e, he, hde⟩ := hr.availability d c hs hg
    exact ⟨e, he, hν.mono hde⟩

end VaughtConjecture.Knight.SharpWitnessComposition
