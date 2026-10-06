/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativePrefixEncoding

/-! # A lawful two-input paste at aligned cuts

Keep the old source labelling below a source cut, and attach a coded tail only
where the prescribed output exceeds a separate output cap. Raised outputs must
come from old sources at or above the source cut. Under this explicit alignment,
the paste respects the unchanged semantics. Locality is proved by bounded
commutation and repair on the actual source blocks; availability may use either
input's witnesses. No general closure under pointwise maximum is asserted.
-/

@[expose] public section

namespace VaughtConjecture.Knight.AlignedCutJoin

open Transform Value ExtOrd SharpWitnessComposition

/-- Bounded commutation is closed under pointwise maximum. The above-grade
bottom clause of a faithful witness is deliberately not asserted here. -/
theorem bounded_max {K : ℕ} {f g : ExtOrd → ExtOrd}
    (hf : BoundedMap K f) (hg : BoundedMap K g) :
    BoundedMap K (fun x => max (f x) (g x)) where
  bot := by rw [hf.bot, hg.bot, max_self]
  mono := fun _ _ h => max_le_max (hf.mono h) (hg.mono h)
  comm x k i hk hi := by
    have hm : Monotone (fun y => extVisibilityReplace y k i) := fun _ _ h => evr_mono h hi
    rw [hf.comm x k i hk hi, hg.comm x k i hk hi, hm.map_max]

/-- A scalar tail gated at a visible output cap. It need not be faithful above
the grade bound, so its consumer repairs actual source blocks instead. -/
noncomputable def above (γ : ExtOrd) (f : ExtOrd → ExtOrd) (y : ExtOrd) : ExtOrd :=
  if y ≤ γ then ⊥ else f y

theorem above_of_le {γ y : ExtOrd} {f : ExtOrd → ExtOrd} (hy : y ≤ γ) :
    above γ f y = ⊥ := ite_eq_left hy

theorem above_of_gt {γ y : ExtOrd} {f : ExtOrd → ExtOrd} (hy : γ < y) :
    above γ f y = f y := ite_eq_right (not_le.mpr hy)

theorem above_bounded {K : ℕ} {γ : ExtOrd} {f : ExtOrd → ExtOrd}
    (hf : BoundedMap K f) (hγ : SelfVis K γ) : BoundedMap K (above γ f) where
  bot := above_of_le bot_le
  mono := by
    intro x y hxy
    by_cases hx : x ≤ γ
    · rw [above_of_le hx]; exact bot_le
    · have hy : γ < y := (not_le.mp hx).trans_le hxy
      rw [above_of_gt (not_le.mp hx), above_of_gt hy]
      exact hf.mono hxy
  comm x k i hk hi := by
    by_cases hx : x ≤ γ
    · rw [above_of_le hx, above_of_le ((replace_le_visible_cut_iff hγ hk hi).mpr hx),
        extVisibilityReplace_bot]
    · rw [above_of_gt (not_le.mp hx),
        above_of_gt (replace_gt_visible_cut hγ hk (not_le.mp hx))]
      exact hf.comm x k i hk hi

/-- The old source prefix and the new output tail are separate inputs. -/
noncomputable def paste {X : Type*} (s p : X → ExtOrd) (a : ExtOrd)
    (v : ExtOrd → ExtOrd) (d : X) : ExtOrd := max (min (s d) a) (v (p d))

section Scalar

variable {X : Type*} {s p : X → ExtOrd} {a γ : ExtOrd} {v : ExtOrd → ExtOrd}
  (hlow : ∀ d, p d ≤ γ → v (p d) = ⊥)
  (hhigh : ∀ d, γ < p d → a < v (p d))
  (halign : ∀ d, γ < p d → a ≤ s d)

include hlow in
theorem paste_of_le (d : X) (hd : p d ≤ γ) : paste s p a v d = min (s d) a := by
  rw [paste, hlow d hd, max_bot_right]

include hhigh in
theorem paste_of_gt (d : X) (hd : γ < p d) : paste s p a v d = v (p d) := by
  exact max_eq_right ((min_le_right _ _).trans (hhigh d hd).le)

include hlow hhigh halign in
/-- Every old source cut is preserved, even when the old output witness
identifies distinct source values. -/
theorem paste_cap (d : X) : min (paste s p a v d) a = min (s d) a := by
  by_cases hd : p d ≤ γ
  · rw [paste_of_le hlow d hd, min_assoc, min_self]
  · have hgt := not_le.mp hd
    rw [paste_of_gt hhigh d hgt, min_eq_right (hhigh d hgt).le,
      min_eq_right (halign d hgt)]

include hlow hhigh halign in
/-- This lattice identity is where the alignment hypothesis is used. It
identifies the actual capped target at every controller, not just global caps. -/
theorem paste_read (hv : Monotone v) (d c : X) :
    max (min (min (s d) (s c)) a) (v (min (p d) (p c))) =
      min (paste s p a v d) (paste s p a v c) := by
  rw [hv.map_min]
  by_cases hd : p d ≤ γ <;> by_cases hc : p c ≤ γ
  · rw [hlow d hd, hlow c hc, min_self, max_bot_right,
      paste_of_le hlow d hd, paste_of_le hlow c hc]
    simpa only [min_self] using (min_min_min_comm (s d) a (s c) a).symm
  · have hc' := not_le.mp hc
    rw [hlow d hd, min_bot_left, max_bot_right,
      paste_of_le hlow d hd, paste_of_gt hhigh c hc',
      min_eq_left ((min_le_right _ _).trans (hhigh c hc').le),
      min_assoc, min_eq_right (halign c hc')]
  · have hd' := not_le.mp hd
    rw [hlow c hc, min_bot_right, max_bot_right,
      paste_of_gt hhigh d hd', paste_of_le hlow c hc,
      min_eq_right ((min_le_right _ _).trans (hhigh d hd').le)]
    rw [min_comm (s d) (s c), min_assoc, min_eq_right (halign d hd')]
  · have hd' := not_le.mp hd
    have hc' := not_le.mp hc
    rw [paste_of_gt hhigh d hd', paste_of_gt hhigh c hc']
    exact max_eq_right ((min_le_right _ _).trans
      (le_min (hhigh d hd').le (hhigh c hc').le))

end Scalar

section Scheme

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

/-- Convert bounded read equations into an actual faithful locality using
only the block-bottom condition at the controller's actual source occurrences. -/
theorem locality_of_bounded_read {q : D.below BJ → ExtOrd}
    (hb : RowBlockBottom sem BJ q) (c : D.below BJ) {f : ExtOrd → ExtOrd}
    (hf : BoundedMap (D.grade c.1) f)
    (hread : ∀ d, f (sem.E c.1 d) = min (q (CellScheme.below.incl c d)) (q c)) :
    TransformsTo (fun d : D.below (D.cell c.1) => D.grade d.1) (sem.E c.1)
      (fun d => min (q (CellScheme.below.incl c d)) (q c)) := by
  classical
  let _ := Fintype.ofFinite (D.below (D.cell c.1))
  let sources := Finset.univ.image (sem.E c.1)
  have hbs : BlockBottom sources f := by
    intro x hx y hy hxy hz
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hy
    rw [hread d] at hz
    rw [hread e]
    exact hb c d e hxy hz
  obtain ⟨τ, hτ, hr⟩ := (hf.interpolate_iff_source_blocks sources).mpr hbs
  apply hτ.transformsTo
  intro d
  have hd : D.grade d.1 ≤ D.grade c.1 := d.2.2
  rw [gTop_of_le hd, min_top_right,
    hr _ (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩), hread d]

/-- The pasted labelling is lawful on the original scheme. No shared
availability selector, injective decoder, or pre-existing completion is assumed. -/
theorem paste_respects {s p : D.below BJ → ExtOrd} {K : ℕ} {a γ : ExtOrd}
    {v : ExtOrd → ExtOrd}
    (hs : RespectsSemanticsBelow sem BJ s) (hp : RespectsSemanticsBelow sem BJ p)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (ha : SelfVis K a) (hab : a ≠ ⊥) (hv : BoundedMap K v)
    (hlow : ∀ d, p d ≤ γ → v (p d) = ⊥)
    (hhigh : ∀ d, γ < p d → a < v (p d))
    (halign : ∀ d, γ < p d → a ≤ s d) :
    RespectsSemanticsBelow sem BJ (paste s p a v) := by
  have hbottom : RowBlockBottom sem BJ (paste s p a v) :=
    rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects hs)
      (bottom_pattern_of_cap_agreement hab (paste_cap hlow hhigh halign))
  obtain ⟨Cs⟩ := exists_localCharts hs
  obtain ⟨Cp⟩ := exists_localCharts hp
  refine ⟨?_, ?_, ?_⟩
  · intro d
    have hpv : SelfVis (D.grade d.1) (v (p d)) := by
      have h := hv.comm (p d) (D.grade d.1) (D.grade d.1) (hK d) le_rfl
      rw [← hp.orderly d] at h
      exact h.symm
    exact (selfVis_max (selfVis_min (hs.orderly d).symm (ha.mono (hK d))) hpv).symm
  · intro c
    apply locality_of_bounded_read hbottom c
      (bounded_max (boundedMap_of_witness
        (FreeDiagonal.clip_witness (Cs.witness c) (ha.mono (hK c))))
        (hv.comp_witness (Cp.witness c) (hK c)))
    intro d
    change max (min (Cs.shift c (sem.E c.1 d)) a) (v (Cp.shift c (sem.E c.1 d))) = _
    rw [Cs.read c d, Cp.read c d]
    exact paste_read hlow hhigh halign hv.mono _ _
  · intro d c hscope hgrade
    by_cases h : v (p d) ≤ min (s d) a
    · obtain ⟨e, he, hde⟩ := hs.availability d c hscope hgrade
      refine ⟨e, he, ?_⟩
      change max (min (s d) a) (v (p d)) ≤ max (min (s e) a) (v (p e))
      rw [max_eq_left h]
      exact (min_le_min hde le_rfl).trans (le_max_left _ _)
    · obtain ⟨e, he, hde⟩ := hp.availability d c hscope hgrade
      refine ⟨e, he, ?_⟩
      change max (min (s d) a) (v (p d)) ≤ max (min (s e) a) (v (p e))
      rw [max_eq_right (not_le.mp h).le]
      exact (hv.mono hde).trans (le_max_right _ _)

end Scheme

end VaughtConjecture.Knight.AlignedCutJoin
