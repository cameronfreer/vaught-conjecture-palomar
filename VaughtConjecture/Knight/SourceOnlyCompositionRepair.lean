/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteCompositionRepair

/-! # Source-only tests for faithful interpolation

For a bounded-commuting monotone map, a faithful interpolant on a finite source
inventory exists exactly when the forced bounded replacement table has a constant
bottom flag on each source block. Unforced floor readings are not constraints.
This is a normalized-witness interpolation theorem, not unrestricted transitivity.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SharpWitnessComposition

open Transform Value ExtOrd

open Classical in
/-- Original sources and their replacements at the maximal bounded threshold. -/
noncomputable def forcedSources (m : ℕ) (s : Finset ExtOrd) : Finset ExtOrd :=
  s ∪ (Finset.range (m + 1)).biUnion (fun i => s.image (fun x => extVisibilityReplace x m i))

theorem subset_forcedSources (m : ℕ) (s : Finset ExtOrd) : s ⊆ forcedSources m s :=
  Finset.subset_union_left

theorem replace_mem_forcedSources {m : ℕ} {s : Finset ExtOrd} {x : ExtOrd}
    (hx : x ∈ s) {i : ℕ} (hi : i ≤ m) :
    extVisibilityReplace x m i ∈ forcedSources m s := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_range.mpr (by omega), Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩)

/-- A lower-threshold replacement of an original source is already in the table. -/
theorem bounded_replace_mem {m : ℕ} {s : Finset ExtOrd} {x : ExtOrd}
    (hx : x ∈ s) {k i : ℕ} (hk : k ≤ m) (hi : i ≤ k) :
    extVisibilityReplace x k i ∈ forcedSources m s := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact subset_forcedSources m s hx
  · exact subset_forcedSources m s hx
  · by_cases ha : finitePart a < k
    · rw [extVisibilityReplace_of_finitePart_lt ha]
      have h := replace_mem_forcedSources hx (hi.trans hk)
      rwa [extVisibilityReplace_of_finitePart_lt (ha.trans_le hk)] at h
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp ha)]
      exact subset_forcedSources m s hx

/-- No further iterations of replacement add points. -/
theorem forcedSources_closed (m : ℕ) (s : Finset ExtOrd) :
    ∀ x ∈ forcedSources m s, ∀ k i : ℕ, k ≤ m → i ≤ k →
      extVisibilityReplace x k i ∈ forcedSources m s := by
  classical
  intro x hx k i hk hi
  rcases Finset.mem_union.mp hx with hx | hx
  · exact bounded_replace_mem hx hk hi
  · obtain ⟨j, hj, hjx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hjx
    rcases ExtOrd.cases y with rfl | rfl | ⟨a, rfl⟩
    · exact subset_forcedSources m s hy
    · exact subset_forcedSources m s hy
    · by_cases ha : finitePart a < m
      · rw [extVisibilityReplace_of_finitePart_lt ha]
        by_cases hjk : j < k
        · rw [extVisibilityReplace_of_finitePart_lt (by
            rw [finitePart_limitPart_add_nat]; exact hjk), limitPart_limitPart_add_nat]
          have h := replace_mem_forcedSources hy (hi.trans hk)
          rwa [extVisibilityReplace_of_finitePart_lt ha] at h
        · rw [extVisibilityReplace_of_le_finitePart (by
            rw [finitePart_limitPart_add_nat]; exact not_lt.mp hjk)]
          have h := replace_mem_forcedSources (m := m) (i := j) hy
            (by have := Finset.mem_range.mp hj; omega)
          rwa [extVisibilityReplace_of_finitePart_lt ha] at h
      · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp ha)]
        exact bounded_replace_mem hy hk hi

/-- A bottom reading and a positive reading may not share a represented source block. -/
def BlockBottom (s : Finset ExtOrd) (f : ExtOrd → ExtOrd) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, blockFloor x = blockFloor y → f x = ⊥ → f y = ⊥

/-- A normalized witness has a globally block-constant bottom flag. -/
theorem witness_blockBottom {m : ℕ} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop m) τ)
    (s : Finset ExtOrd) : BlockBottom s τ := by
  intro x _ y _ hb hx
  apply bot_of_same_block (f := τ) _ hb hx
  intro z hz k i hi
  have h := hτ.clause5 z k (by rw [hz]; exact bot_le) i hi
  rwa [hz, extVisibilityReplace_bot] at h

/-- The finite source reads force all the bounded replacement reads. -/
theorem forcedSources_read {m : ℕ} {s : Finset ExtOrd} {f τ : ExtOrd → ExtOrd}
    (hf : BoundedMap m f) (hτ : Witness (gTop m) τ)
    (hr : ∀ x ∈ s, τ x = f x) : ∀ x ∈ forcedSources m s, τ x = f x := by
  classical
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact hr x hx
  · obtain ⟨i, hi, hix⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hix
    have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
    rw [hf.comm y m i le_rfl hi', hτ.clause5 y m
      (by rw [gTop_of_le le_rfl]; exact le_top) i hi', hr y hy]

namespace BoundedMap

variable {m : ℕ} {f : ExtOrd → ExtOrd} (hf : BoundedMap m f)

include hf

/-- Raise only unrepresented low source inputs; all represented reads stay fixed. -/
theorem roundUp_bounded (s : Finset ExtOrd)
    (hclosed : ∀ x ∈ s, ∀ k i : ℕ, k ≤ m → i ≤ k → extVisibilityReplace x k i ∈ s) :
    BoundedMap m (f ∘ roundUp s) where
  bot := by simp only [Function.comp_apply, roundUp_bot, hf.bot]
  mono := hf.mono.comp (roundUp_mono s)
  comm x k i hk hi := by
    simp only [Function.comp_apply]
    rw [roundUp_commutes s m hclosed x k i hk hi, hf.comm _ k i hk hi]

/-- On a closed source inventory, blockwise bottom agreement repairs the unused floors. -/
theorem interpolate_closed (s : Finset ExtOrd)
    (hclosed : ∀ x ∈ s, ∀ k i : ℕ, k ≤ m → i ≤ k → extVisibilityReplace x k i ∈ s)
    (hb : BlockBottom s f) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop m) τ ∧ ∀ x ∈ s, τ x = f x := by
  let hg := hf.roundUp_bounded s hclosed
  have hfloor : ∀ x ∈ s,
      (f ∘ roundUp s) (blockFloor x) = ⊥ → (f ∘ roundUp s) x = ⊥ := by
    intro x hx h
    change f (roundUp s x) = ⊥
    rw [roundUp_of_mem hx]
    exact hb _ (roundUp_floor_mem hx) x hx
      (by rw [blockFloor_roundUp, blockFloor_idem]) h
  refine ⟨finiteLowerEnvelope (stripDomain m s) (f ∘ roundUp s),
    hg.finite_witness s (hg.floor_check_on_strip s hfloor), ?_⟩
  intro x hx
  rw [hg.finite_read s hx]
  simp only [Function.comp_apply, roundUp_of_mem hx]

/-- Exact criterion: only original sources and the replacements they force are tested. -/
theorem interpolate_iff (s : Finset ExtOrd) :
    (∃ τ : ExtOrd → ExtOrd, Witness (gTop m) τ ∧ ∀ x ∈ s, τ x = f x) ↔
      BlockBottom (forcedSources m s) f := by
  constructor
  · rintro ⟨τ, hτ, hr⟩
    have he := forcedSources_read hf hτ hr
    intro x hx y hy hb hbot
    rw [← he y hy]
    exact witness_blockBottom hτ _ x hx y hy hb (by rw [he x hx]; exact hbot)
  · intro hb
    obtain ⟨τ, hτ, hr⟩ := hf.interpolate_closed (forcedSources m s)
      (forcedSources_closed m s) hb
    exact ⟨τ, hτ, fun x hx => hr x (subset_forcedSources m s hx)⟩

end BoundedMap

/-- Visibility replacement does not change a bottom flag. -/
theorem replace_eq_bot_iff (x : ExtOrd) (k i : ℕ) :
    extVisibilityReplace x k i = ⊥ ↔ x = ⊥ := by
  constructor
  · intro h
    by_contra hx
    exact extVisibilityReplace_ne_bot hx k i h
  · intro h
    rw [h, extVisibilityReplace_bot]

namespace BoundedMap

variable {m : ℕ} {f : ExtOrd → ExtOrd} (hf : BoundedMap m f)

include hf

/-- Every forced reading has the source block and bottom flag of an original reading. -/
theorem forcedSources_origin {s : Finset ExtOrd} {z : ExtOrd} (hz : z ∈ forcedSources m s) :
    ∃ x ∈ s, blockFloor z = blockFloor x ∧ (f z = ⊥ ↔ f x = ⊥) := by
  classical
  rcases Finset.mem_union.mp hz with hz | hz
  · exact ⟨z, hz, rfl, Iff.rfl⟩
  · obtain ⟨i, hi, hiz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hiz
    have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
    refine ⟨x, hx, blockFloor_evr x m i, ?_⟩
    rw [hf.comm x m i le_rfl hi']
    exact replace_eq_bot_iff (f x) m i

/-- The forced table adds no new bottom-pattern tests. -/
theorem forcedSources_blockBottom_iff (s : Finset ExtOrd) :
    BlockBottom (forcedSources m s) f ↔ BlockBottom s f := by
  constructor
  · intro h x hx y hy hb hz
    exact h x (subset_forcedSources m s hx) y (subset_forcedSources m s hy) hb hz
  · intro h x hx y hy hb hz
    obtain ⟨u, hu, hux, huf⟩ := hf.forcedSources_origin hx
    obtain ⟨v, hv, hvy, hvf⟩ := hf.forcedSources_origin hy
    exact hvf.mpr (h u hu v hv (hux.symm.trans (hb.trans hvy)) (huf.mp hz))

/-- The exact test uses only the original source reads, not even their forced replacements. -/
theorem interpolate_iff_source_blocks (s : Finset ExtOrd) :
    (∃ τ : ExtOrd → ExtOrd, Witness (gTop m) τ ∧ ∀ x ∈ s, τ x = f x) ↔
      BlockBottom s f :=
  (hf.interpolate_iff s).trans (hf.forcedSources_blockBottom_iff s)

end BoundedMap

/-- The exact interpolation criterion also applies to a composite of normalized witnesses. -/
theorem comp_read_iff {m K : ℕ} {σ ν : ExtOrd → ExtOrd}
    (hσ : Witness (gTop m) σ) (hν : Witness (gTop K) ν) (hmK : m ≤ K)
    (s : Finset ExtOrd) :
    (∃ τ : ExtOrd → ExtOrd, Witness (gTop m) τ ∧ ∀ x ∈ s, τ x = ν (σ x)) ↔
      BlockBottom (forcedSources m s) (ν ∘ σ) :=
  (bounded_comp hσ hν hmK).interpolate_iff s

/-- Faithful composition on a finite source row is equivalent to a source-block bottom test. -/
theorem comp_read_iff_source_blocks {m K : ℕ} {σ ν : ExtOrd → ExtOrd}
    (hσ : Witness (gTop m) σ) (hν : Witness (gTop K) ν) (hmK : m ≤ K)
    (s : Finset ExtOrd) :
    (∃ τ : ExtOrd → ExtOrd, Witness (gTop m) τ ∧ ∀ x ∈ s, τ x = ν (σ x)) ↔
      BlockBottom s (ν ∘ σ) :=
  (bounded_comp hσ hν hmK).interpolate_iff_source_blocks s

end VaughtConjecture.Knight.SharpWitnessComposition
