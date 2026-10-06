/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceOnlyCompositionRepair

/-! # Finite interpolation preserving an entire faithful prefix

Two normalized witnesses agreeing at a grade-visible source cut can be joined,
keeping the first witness on the entire closed prefix. No extra visibility grade
is required: the cut itself belongs to the retained side. Combining this with
source-only interpolation gives an exact finite test for retaining an old prefix
while satisfying new literal source reads. It constructs witnesses, not rows.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SharpWitnessComposition

open Transform Value ExtOrd

/-- The bottom fibre of any faithful witness is constant on source blocks. -/
theorem witness_bot_of_same_block {g : ℕ → ExtOrd} {τ : ExtOrd → ExtOrd}
    (hτ : Witness g τ) {x y : ExtOrd} (hb : blockFloor x = blockFloor y)
    (hx : τ x = ⊥) : τ y = ⊥ := by
  apply bot_of_same_block (f := τ) _ hb hx
  intro z hz k i hi
  have h := hτ.clause5 z k (by rw [hz]; exact bot_le) i hi
  rwa [hz, extVisibilityReplace_bot] at h

/-- Bounded replacements do not bring an input above a visible cut back to the prefix. -/
theorem replace_gt_visible_cut {m k i : ℕ} {a x : ExtOrd}
    (ha : SelfVis m a) (hk : k ≤ m) (hx : a < x) :
    a < extVisibilityReplace x k i := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨b, rfl⟩
  · exact bot_lt_iff_ne_bot.mpr (extVisibilityReplace_ne_bot (ne_of_gt hx) k i)
  · exact False.elim (not_lt_of_ge le_top hx)
  · rcases ExtOrd.cases x with rfl | rfl | ⟨c, rfl⟩
    · exact False.elim (not_lt_of_ge bot_le hx)
    · exact hx
    · rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
      exact visReplace_gt_of_gt (hk.trans (selfVis_ofOrd_iff.mp ha)) (ofOrd_lt_ofOrd.mp hx)

/-- The entire closed prefix is invariant under bounded replacements. -/
theorem replace_le_visible_cut_iff {m k i : ℕ} {a x : ExtOrd}
    (ha : SelfVis m a) (hk : k ≤ m) (hi : i ≤ k) :
    extVisibilityReplace x k i ≤ a ↔ x ≤ a := by
  constructor
  · intro h
    by_contra hx
    exact not_lt_of_ge h (replace_gt_visible_cut ha hk (not_le.mp hx))
  · intro h
    exact (extVisibilityReplace_mono k i hi h).trans_eq
      (evr_eq_self_of_selfVis (selfVis_mono ha hk) i)

open Classical in
/-- Keep the old shifter through the cut, and the new one strictly above it. -/
noncomputable def prefixSplice (a : ExtOrd) (σ τ : ExtOrd → ExtOrd) (x : ExtOrd) : ExtOrd :=
  if x ≤ a then σ x else τ x

theorem prefixSplice_of_le {a x : ExtOrd} {σ τ : ExtOrd → ExtOrd} (hx : x ≤ a) :
    prefixSplice a σ τ x = σ x := ite_eq_left hx

theorem prefixSplice_of_gt {a x : ExtOrd} {σ τ : ExtOrd → ExtOrd} (hx : a < x) :
    prefixSplice a σ τ x = τ x := ite_eq_right (not_le.mpr hx)

theorem prefixSplice_mono {a : ExtOrd} {σ τ : ExtOrd → ExtOrd}
    (hσ : Monotone σ) (hτ : Monotone τ) (he : σ a = τ a) :
    Monotone (prefixSplice a σ τ) := by
  intro x y hxy
  by_cases hx : x ≤ a <;> by_cases hy : y ≤ a
  · rw [prefixSplice_of_le hx, prefixSplice_of_le hy]
    exact hσ hxy
  · rw [prefixSplice_of_le hx, prefixSplice_of_gt (not_le.mp hy)]
    exact (hσ hx).trans (he ▸ hτ (not_le.mp hy).le)
  · exact False.elim (hx (hxy.trans hy))
  · rw [prefixSplice_of_gt (not_le.mp hx), prefixSplice_of_gt (not_le.mp hy)]
    exact hτ hxy

/-- Agreement at the cut also controls a bottom fibre crossing that cut. -/
theorem prefixSplice_bot_block {m : ℕ} {a : ExtOrd} {σ τ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop m) σ) (hτ : Witness (gTop m) τ) (he : σ a = τ a)
    {x y : ExtOrd} (hb : blockFloor x = blockFloor y)
    (hz : prefixSplice a σ τ x = ⊥) : prefixSplice a σ τ y = ⊥ := by
  by_cases hx : x ≤ a <;> by_cases hy : y ≤ a
  · rw [prefixSplice_of_le hx] at hz
    rw [prefixSplice_of_le hy]
    exact witness_bot_of_same_block hσ hb hz
  · rw [prefixSplice_of_le hx] at hz
    rw [prefixSplice_of_gt (not_le.mp hy)]
    have hba : blockFloor a = blockFloor x :=
      blockFloor_eq_of_between hx (not_le.mp hy).le hb
    have hza : σ a = ⊥ := witness_bot_of_same_block hσ hba.symm hz
    exact witness_bot_of_same_block hτ (hba.trans hb) (he ▸ hza)
  · rw [prefixSplice_of_gt (not_le.mp hx)] at hz
    rw [prefixSplice_of_le hy]
    exact le_bot_iff.mp ((hσ.mono hy).trans ((he.symm ▸ hτ.mono (not_le.mp hx).le).trans_eq hz))
  · rw [prefixSplice_of_gt (not_le.mp hx)] at hz
    rw [prefixSplice_of_gt (not_le.mp hy)]
    exact witness_bot_of_same_block hτ hb hz

/-- Witnesses splice at their own-grade-visible source cut; the whole old prefix stays literal. -/
theorem prefixSplice_witness {m : ℕ} {a : ExtOrd} {σ τ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop m) σ) (hτ : Witness (gTop m) τ)
    (ha : SelfVis m a) (he : σ a = τ a) : Witness (gTop m) (prefixSplice a σ τ) where
  anti := hσ.anti
  vis := hσ.vis
  bot := by rw [prefixSplice_of_le bot_le]; exact hσ.bot
  mono := prefixSplice_mono hσ.mono hτ.mono he
  clause5 := by
    intro x k hact i hi
    by_cases hk : k ≤ m
    · by_cases hx : x ≤ a
      · rw [prefixSplice_of_le hx,
          prefixSplice_of_le ((replace_le_visible_cut_iff ha hk hi).mpr hx)]
        exact hσ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi
      · rw [prefixSplice_of_gt (not_le.mp hx),
          prefixSplice_of_gt (replace_gt_visible_cut ha hk (not_le.mp hx))]
        exact hτ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi
    · have hz : prefixSplice a σ τ x = ⊥ := by
        rwa [gTop_of_gt (not_le.mp hk), le_bot_iff] at hact
      rw [hz, extVisibilityReplace_bot]
      exact prefixSplice_bot_block hσ hτ he (blockFloor_evr x k i).symm hz

namespace BoundedMap

variable {m : ℕ} {f σ : ExtOrd → ExtOrd} (hf : BoundedMap m f)

include hf

/-- Exact finite interpolation with an infinite prescribed prefix. The only new source
anchor is the cut; no samples of the rest of the old prefix are needed. -/
theorem interpolate_prefix_iff (hσ : Witness (gTop m) σ) (s : Finset ExtOrd)
    {a : ExtOrd} (ha : SelfVis m a) (hae : f a = σ a)
    (hleft : ∀ x ∈ s, x ≤ a → f x = σ x) :
    (∃ τ : ExtOrd → ExtOrd, Witness (gTop m) τ ∧
      (∀ x, x ≤ a → τ x = σ x) ∧ (∀ x ∈ s, τ x = f x)) ↔
      BlockBottom (forcedSources m (insert a s)) f := by
  classical
  constructor
  · rintro ⟨τ, hτ, hpre, hr⟩
    apply (hf.interpolate_iff (insert a s)).mp
    refine ⟨τ, hτ, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with hxa | hx
    · rw [hxa]
      exact (hpre a le_rfl).trans hae.symm
    · exact hr x hx
  · intro hb
    obtain ⟨τ, hτ, hr⟩ := (hf.interpolate_iff (insert a s)).mpr hb
    have he : σ a = τ a := hae.symm.trans (hr a (Finset.mem_insert_self _ _)).symm
    refine ⟨prefixSplice a σ τ, prefixSplice_witness hσ hτ ha he,
      fun x hx => prefixSplice_of_le hx, ?_⟩
    intro x hx
    by_cases hxa : x ≤ a
    · rw [prefixSplice_of_le hxa]
      exact (hleft x hx hxa).symm
    · rw [prefixSplice_of_gt (not_le.mp hxa)]
      exact hr x (Finset.mem_insert_of_mem hx)

/-- Only the original sources and the cut anchor are tested, while every old prefix value
is preserved. The off-row floors and the bounded replacement slots need no separate checks. -/
theorem interpolate_prefix_iff_source_blocks (hσ : Witness (gTop m) σ) (s : Finset ExtOrd)
    {a : ExtOrd} (ha : SelfVis m a) (hae : f a = σ a)
    (hleft : ∀ x ∈ s, x ≤ a → f x = σ x) :
    (∃ τ : ExtOrd → ExtOrd, Witness (gTop m) τ ∧
      (∀ x, x ≤ a → τ x = σ x) ∧ (∀ x ∈ s, τ x = f x)) ↔
      BlockBottom (insert a s) f :=
  (hf.interpolate_prefix_iff hσ s ha hae hleft).trans
    (hf.forcedSources_blockBottom_iff (insert a s))

end BoundedMap

end VaughtConjecture.Knight.SharpWitnessComposition
