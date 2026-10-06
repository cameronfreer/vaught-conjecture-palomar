/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PositiveFloor

/-! # The relative tail floor: keep the proper prefix, floor only the tail

The reviewer's notes6 (`simplification_and_completion.md` §5, 2026-09-19).
`tailFloor δ w x = x` if `x ≤ δ`, `max x w` otherwise.  The positive floor of
`Knight/PositiveFloor.lean` is the case `δ = ⊥`.  The note's side condition `δ ≤ w` is never
needed: the floor is monotone, bottom-reflecting and commutes with replacement without it.

* **Replacement cannot cross a visible cutoff** (`le_iff_evr_le`): for `δ` `k`-visible and
  `i ≤ k`, `x ≤ δ ↔ R_{k,i} x ≤ δ`.  Hence the floor commutes with replacement through the
  visibility grade of `δ` and `w` (`tailFloor_evr`) and is a bottom-reflecting normalized
  grade-`K` witness (`witness_tailFloor`); it transports lawfulness on unchanged long rows
  (`tailFloor_respects`).
* **The exact cap identity** (`tailFloor_min`): `min (F_{δ,w} x) γ = F_{δ∧γ, w∧γ} (min x γ)`,
  a lattice identity valid for every cap `γ`; in particular every comparison cap `γ ≤ δ` is
  untouched (`tailFloor_min_of_le`).  That the capped parameters `δ ∧ γ`, `w ∧ γ` themselves
  give a grade-`K` witness is a separate claim needing their own visibility
  (`witness_tailFloor_min`); the identity does not supply it.
* **The localized-height version** (`tailFloor_respects_whole`): on an arbitrary scheme whose
  rows above `K` need not be mute, if the *selected* section reads every owner of grade above
  `K` at most `δ`, then the floored section is lawful on the whole unchanged scheme: owners of
  grade at most `K` use the witness, higher owners see a literally unchanged capped locality
  target.  This is a condition on the section, not on the scheme's rows, and no mute-diagonal
  assumption replaces it.  The note asks for `δ` visible through the target height; formally
  `K`-visibility of both `δ` and `w` suffices, because a higher owner `o` with `p o ≤ δ` reads
  `min (F x) (p o) = min x (p o)` for every `x` by `tailFloor_min_of_le`, with no replacement
  involved.

What it does not do: restore reference equations, activate a guard, or produce a
reference-frame theorem — those are the remaining construction obligations.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-! ## Replacement cannot cross a visible cutoff -/

/-- For `δ` `k`-visible, a value and its replacement at grade `k` lie on the same side of `δ`. -/
theorem le_iff_evr_le {δ x : ExtOrd} {k i : ℕ} (hδ : SelfVis k δ) (hi : i ≤ k) :
    x ≤ δ ↔ extVisibilityReplace x k i ≤ δ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top]
  · by_cases hfp : k ≤ finitePart a
    · rw [extVisibilityReplace_of_le_finitePart hfp]
    · have hfp' := not_le.mp hfp
      rw [extVisibilityReplace_of_finitePart_lt hfp']
      rcases ExtOrd.cases δ with rfl | rfl | ⟨g, rfl⟩
      · simp only [le_bot_iff]
        exact ⟨fun h => absurd h (ofOrd_ne_bot _), fun h => absurd h (ofOrd_ne_bot _)⟩
      · simp only [le_top]
      · rw [selfVis_ofOrd_iff] at hδ
        rw [ofOrd_le_ofOrd, ofOrd_le_ofOrd]
        constructor
        · intro h
          have hl : limitPart a ≤ limitPart g := limitPart_mono h
          rcases hl.lt_or_eq with hlt | heq
          · exact (limitPart_add_nat_le_of_lt hlt i).trans (limitPart_le g)
          · rw [heq]
            calc limitPart g + (i : Ordinal.{0}) ≤ limitPart g + (finitePart g : Ordinal.{0}) :=
                  add_le_add_right (Nat.cast_le.mpr (hi.trans hδ)) _
              _ = g := limitPart_add_finitePart g
        · intro h
          have hl : limitPart a ≤ limitPart g := by
            have := limitPart_mono h
            rwa [limitPart_limitPart_add_nat] at this
          rcases hl.lt_or_eq with hlt | heq
          · have h1 := limitPart_add_nat_le_of_lt hlt (finitePart a)
            rw [limitPart_add_finitePart] at h1
            exact h1.trans (limitPart_le g)
          · calc a = limitPart a + (finitePart a : Ordinal.{0}) := (limitPart_add_finitePart a).symm
              _ ≤ limitPart g + (finitePart g : Ordinal.{0}) := by
                  rw [heq]; exact add_le_add_right (Nat.cast_le.mpr (hfp'.le.trans hδ)) _
              _ = g := limitPart_add_finitePart g

/-! ## The floor -/

/-- The relative tail floor: the identity up to `δ`, `max · w` above it. -/
noncomputable def tailFloor (δ w x : ExtOrd) : ExtOrd := if x ≤ δ then x else max x w

theorem tailFloor_of_le {δ w x : ExtOrd} (h : x ≤ δ) : tailFloor δ w x = x := ite_eq_left h

theorem tailFloor_of_gt {δ w x : ExtOrd} (h : δ < x) : tailFloor δ w x = max x w :=
  ite_eq_right (not_le.mpr h)

theorem tailFloor_bot (δ w : ExtOrd) : tailFloor δ w ⊥ = ⊥ := tailFloor_of_le bot_le

theorem positiveFloor_eq_tailFloor (w x : ExtOrd) : positiveFloor w x = tailFloor ⊥ w x := by
  by_cases hx : x = ⊥
  · rw [hx, positiveFloor_bot, tailFloor_bot]
  · rw [positiveFloor_of_ne hx, tailFloor_of_gt (bot_lt_iff_ne_bot.mpr hx)]

theorem self_le_tailFloor (δ w x : ExtOrd) : x ≤ tailFloor δ w x := by
  by_cases h : x ≤ δ
  · rw [tailFloor_of_le h]
  · rw [tailFloor_of_gt (not_le.mp h)]; exact le_max_left _ _

theorem tailFloor_eq_bot_iff {δ w x : ExtOrd} : tailFloor δ w x = ⊥ ↔ x = ⊥ :=
  ⟨fun h => le_bot_iff.mp ((self_le_tailFloor δ w x).trans h.le),
    fun h => by rw [h, tailFloor_bot]⟩

theorem tailFloor_mono (δ w : ExtOrd) : Monotone (tailFloor δ w) := by
  intro x y hxy
  by_cases hx : x ≤ δ
  · rw [tailFloor_of_le hx]
    exact hxy.trans (self_le_tailFloor δ w y)
  · have hy : ¬ y ≤ δ := fun h => hx (hxy.trans h)
    rw [tailFloor_of_gt (not_le.mp hx), tailFloor_of_gt (not_le.mp hy)]
    exact max_le_max hxy le_rfl

/-- **Replacement commutes with the floor** through the visibility grade of `δ` and `w`. -/
theorem tailFloor_evr {δ w : ExtOrd} {K : ℕ} (hδ : SelfVis K δ) (hw : SelfVis K w) {k i : ℕ}
    (hk : k ≤ K) (hi : i ≤ k) (x : ExtOrd) :
    tailFloor δ w (extVisibilityReplace x k i) = extVisibilityReplace (tailFloor δ w x) k i := by
  by_cases hx : x ≤ δ
  · rw [tailFloor_of_le hx, tailFloor_of_le ((le_iff_evr_le (hδ.mono hk) hi).mp hx)]
  · have hx' := not_le.mp hx
    have hx'' : ¬ extVisibilityReplace x k i ≤ δ := fun h =>
      hx ((le_iff_evr_le (hδ.mono hk) hi).mpr h)
    rw [tailFloor_of_gt hx', tailFloor_of_gt (not_le.mp hx''), (evr_monotone k i hi).map_max,
      evr_eq_self_of_selfVis (hw.mono hk) i]

/-- **The floor is a normalized grade-`K` witness.** -/
theorem witness_tailFloor {δ w : ExtOrd} {K : ℕ} (hδ : SelfVis K δ) (hw : SelfVis K w) :
    Witness (gTop K) (tailFloor δ w) where
  anti := (witness_id K).anti
  vis := (witness_id K).vis
  bot := tailFloor_bot δ w
  mono := tailFloor_mono δ w
  clause5 α k hle i hi := by
    by_cases hk : k ≤ K
    · exact tailFloor_evr hδ hw hk hi α
    · have h0 : tailFloor δ w α = ⊥ := by
        rw [gTop, ite_eq_right hk] at hle
        exact le_bot_iff.mp hle
      have hα : α = ⊥ := tailFloor_eq_bot_iff.mp h0
      rw [hα, extVisibilityReplace_bot, tailFloor_bot, extVisibilityReplace_bot]

theorem boundedMap_tailFloor {δ w : ExtOrd} {K : ℕ} (hδ : SelfVis K δ) (hw : SelfVis K w) :
    BoundedMap K (tailFloor δ w) :=
  boundedMap_of_witness (witness_tailFloor hδ hw)

/-! ## The exact cap identity -/

/-- `min (F_{δ,w} x) γ = F_{δ ∧ γ, w ∧ γ} (min x γ)`. -/
theorem tailFloor_min (δ w x γ : ExtOrd) :
    min (tailFloor δ w x) γ = tailFloor (min δ γ) (min w γ) (min x γ) := by
  by_cases hx : x ≤ δ
  · rw [tailFloor_of_le hx, tailFloor_of_le (min_le_min_right γ hx)]
  · have hx' := not_le.mp hx
    rw [tailFloor_of_gt hx']
    by_cases hγ : γ ≤ δ
    · have h1 : min x γ = γ := min_eq_right (hγ.trans hx'.le)
      have h2 : min δ γ = γ := min_eq_right hγ
      rw [h1, h2, tailFloor_of_le le_rfl]
      exact min_eq_right (hγ.trans (hx'.le.trans (le_max_left _ _)))
    · have hγ' := not_le.mp hγ
      have h2 : min δ γ = δ := min_eq_left hγ'.le
      have hlt : δ < min x γ := lt_min hx' hγ'
      rw [h2, tailFloor_of_gt hlt]
      have hm : Monotone fun y : ExtOrd => min y γ := fun _ _ h => min_le_min_right γ h
      exact hm.map_max

/-- A comparison cap at most `δ` is untouched by the floor. -/
theorem tailFloor_min_of_le {δ w x γ : ExtOrd} (h : γ ≤ δ) :
    min (tailFloor δ w x) γ = min x γ := by
  rw [tailFloor_min, min_eq_right h]
  exact tailFloor_of_le (min_le_right x γ)

/-- The capped floor is itself a grade-`K` witness **when the capped parameters are visible**;
this is the separate visibility requirement, not a consequence of `tailFloor_min`. -/
theorem witness_tailFloor_min {δ w γ : ExtOrd} {K : ℕ} (hδ : SelfVis K (min δ γ))
    (hw : SelfVis K (min w γ)) : Witness (gTop K) (tailFloor (min δ γ) (min w γ)) :=
  witness_tailFloor hδ hw

/-! ## Transport on unchanged rows -/

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- The floor transports lawfulness through grade `K` on unchanged rows (long rows included). -/
theorem tailFloor_respects {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) {K : ℕ} (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    {δ w : ExtOrd} (hδ : SelfVis K δ) (hw : SelfVis K w) :
    RespectsSemanticsBelow sem BJ (fun d => tailFloor δ w (r d)) :=
  map_respects_of_bottom_reflecting hr hK (boundedMap_tailFloor hδ hw)
    (fun _ h => tailFloor_eq_bot_iff.mp h)

/-- **The localized-height version**: on a scheme whose rows above `K` need not be mute, a
lawful section reading every owner of grade above `K` at most `δ` stays lawful after the
floor; the higher owners see a literally unchanged locality target. -/
theorem tailFloor_respects_whole {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) {K : ℕ}
    {δ w : ExtOrd} (hδ : SelfVis K δ) (hw : SelfVis K w)
    (hhigh : ∀ o, K < D.grade o → p o ≤ δ) :
    RespectsSemantics sem (fun d => tailFloor δ w (p d)) where
  orderly d := by
    change tailFloor δ w (p d) =
      extVisibilityReplace (tailFloor δ w (p d)) (D.grade d) (D.grade d)
    by_cases hg : D.grade d ≤ K
    · rw [← tailFloor_evr hδ hw hg le_rfl, ← hp.orderly d]
    · rw [tailFloor_of_le (hhigh d (not_le.mp hg))]
      exact hp.orderly d
  locality o := by
    by_cases hg : D.grade o ≤ K
    · exact (tailFloor_respects (hp.toBelow (D.cell o)) (fun d => d.2.2.trans hg) hδ hw).locality
        ⟨o, GradedLe.refl _⟩
    · have hpo : p o ≤ δ := hhigh o (not_le.mp hg)
      have e : (fun d : D.below (D.cell o) => min (tailFloor δ w (p d.1)) (tailFloor δ w (p o))) =
          fun d => min (p d.1) (p o) := by
        funext d
        rw [tailFloor_of_le hpo]
        exact tailFloor_min_of_le hpo
      rw [e]
      exact hp.locality o
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hc, hle⟩ := hp.availability Sig Xi₀ hs hg
    exact ⟨Xi, hc, tailFloor_mono δ w hle⟩

end VaughtConjecture.Knight
