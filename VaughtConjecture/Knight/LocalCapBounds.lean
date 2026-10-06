/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoherentGradeCaps

/-! # Local target bounds instead of globally decreasing caps

Antitonicity of the grade caps is sufficient but unnecessary. To reuse each
old controller's capped witness, the exact condition is that every old capped
target below that controller fit under the occurrence's own grade cap.
Availability uses the same old witnesses because the cap is constant on a
grade. No transformation is composed and no new-controller witness is assumed.

The condition is necessary and sufficient for equality of these capped
targets, not for semantic locality by some other witness. This module does
not choose caps, build fresh rows, or prove arbitrary-face completion.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.CoherentGradeCaps

open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {F : Finset ι} {D : CellScheme F}
  {BJ : Finset ι × ℕ}

private theorem capped_target_iff (x y u v : ExtOrd) :
    min (min x u) (min y v) = min x (min y v) ↔ min x (min y v) ≤ u := by
  have he : min (min x u) (min y v) = min (min x (min y v)) u := by ac_rfl
  rw [he, min_eq_left_iff]

/-- These are inequalities on the actual old occurrences, at the actual
clipped controller value, rather than comparisons of the caps alone. -/
def LocalBounds (p : D.below BJ → ExtOrd) (g : ℕ → ExtOrd) : Prop :=
  ∀ (c : D.below BJ) (d : D.below (D.cell c.1)),
    min (p (CellScheme.below.incl c d)) (min (p c) (g (D.grade c.1))) ≤ g (D.grade d.1)

theorem localBounds_iff (p : D.below BJ → ExtOrd) (g : ℕ → ExtOrd) :
    LocalBounds p g ↔ ∀ (c : D.below BJ) (d : D.below (D.cell c.1)),
      min (clipped g p (CellScheme.below.incl c d)) (clipped g p c) =
        min (min (p (CellScheme.below.incl c d)) (p c)) (g (D.grade c.1)) := by
  constructor
  · intro h c d
    exact ((capped_target_iff _ _ _ _).mpr (h c d)).trans (min_assoc _ _ _).symm
  · intro h c d
    exact (capped_target_iff _ _ _ _).mp ((h c d).trans (min_assoc _ _ _))

/-- The usual global antitonicity is one sufficient way to obtain the bounds. -/
theorem localBounds_of_antitone (p : D.below BJ → ExtOrd) {g : ℕ → ExtOrd}
    (ha : Antitone g) : LocalBounds p g := by
  intro c d
  exact (min_le_right _ _).trans ((min_le_right _ _).trans (ha d.2.2))

/-- In particular, a fully protected old labelling need not satisfy a global
order between donor labels at different grades. -/
theorem localBounds_of_labels_le (p : D.below BJ → ExtOrd) (g : ℕ → ExtOrd)
    (h : ∀ d, p d ≤ g (D.grade d.1)) : LocalBounds p g := by
  intro c d
  exact (min_le_left _ _).trans (h (CellScheme.below.incl c d))

/-- Construct respect directly from the exact target bounds. The cap lemma
is used once at each old controller; availability retains its actual witness. -/
theorem respects_of_localBounds {sem : Semantics D} {p : D.below BJ → ExtOrd}
    (hp : RespectsSemanticsBelow sem BJ p) (g : ℕ → ExtOrd)
    (hv : ∀ k ≤ BJ.2, SelfVis k (g k)) (hb : LocalBounds p g) :
    RespectsSemanticsBelow sem BJ (clipped g p) where
  orderly d := (selfVis_min (hp.orderly d).symm (hv _ d.2.2)).symm
  locality c := by
    have ht := TransformsTo.capped (fun d : D.below (D.cell c.1) => d.2.2)
      (hv _ c.2.2) (hp.locality c)
    refine transformsTo_congr rfl rfl ?_ ht
    exact funext fun d => ((localBounds_iff p g).mp hb c d).symm
  availability c e hs hg := by
    obtain ⟨w, hw, hle⟩ := hp.availability c e hs hg
    refine ⟨w, hw, ?_⟩
    have hgrade : D.grade w.1 = D.grade c.1 := (congrArg Prod.snd hw).trans hg.symm
    change min (p c) (g (D.grade c.1)) ≤ min (p w) (g (D.grade w.1))
    rw [hgrade]
    exact min_le_min_right _ hle

/-- At a donor whose new cap is below its old label, the local bounds keep
its entire old target literal under that new cap, even for increasing caps. -/
theorem at_controller_cap (p : D.below BJ → ExtOrd) (g : ℕ → ExtOrd)
    (hb : LocalBounds p g) (c : D.below BJ)
    (hcut : g (D.grade c.1) ≤ p c) (d : D.below (D.cell c.1)) :
    min (clipped g p (CellScheme.below.incl c d)) (g (D.grade c.1)) =
      min (p (CellScheme.below.incl c d)) (g (D.grade c.1)) := by
  have he := (localBounds_iff p g).mp hb c d
  change min (clipped g p (CellScheme.below.incl c d)) (min (p c) (g (D.grade c.1))) = _
    at he
  rw [min_eq_right hcut, min_assoc, min_eq_right hcut] at he
  exact he

/-- The same relaxation also serves an actual donor's fresh orbit columns.
It reuses one old witness, not a composite transformation or a new search.
The carrier here is old occurrences plus requests, not a complete new scheme. -/
theorem donor_orbit_of_localBounds {sem : Semantics D} {p : D.below BJ → ExtOrd}
    (hp : RespectsSemanticsBelow sem BJ p) (g : ℕ → ExtOrd)
    (hb : LocalBounds p g) (c : D.below BJ)
    (hv : SelfVis (D.grade c.1) (g (D.grade c.1)))
    {I : Type*} (newGrade : I → ℕ) (ref : I → D.below (D.cell c.1)) (offset : I → ℕ)
    (hnew : ∀ i, newGrade i ≤ D.grade c.1) (hoff : ∀ i, offset i ≤ D.grade c.1)
    (y : I → ExtOrd) (hcut : g (D.grade c.1) ≤ p c)
    (he : ∀ i, min (y i) (g (D.grade c.1)) =
      min (extVisibilityReplace (p (CellScheme.below.incl c (ref i)))
        (D.grade c.1) (offset i)) (g (D.grade c.1))) :
    TransformsTo (Sum.elim (fun d : D.below (D.cell c.1) => D.grade d.1) newGrade)
      (OrbitCap.row (sem.E c.1) ref offset (D.grade c.1))
      (fun d => min (OrbitCap.labels
        (fun e => clipped g p (CellScheme.below.incl c e)) y d) (g (D.grade c.1))) := by
  let p₀ := fun d : D.below (D.cell c.1) => p (CellScheme.below.incl c d)
  have hcut₀ : g (D.grade c.1) ≤ p₀ ⟨c.1, GradedLe.refl _⟩ :=
    hcut.trans_eq (congrArg p (Subtype.ext rfl))
  have ht := (OrbitCap.synchronizedCap_actual_donor c.1 (hp.mono c.2)
    newGrade ref offset hnew hoff y hv hcut₀ he).2.1
  refine transformsTo_congr rfl rfl ?_ ht
  funext d
  cases d with
  | inl d =>
    exact (OrbitCap.synchronizedCap_capped p₀ (g (D.grade c.1)) d).trans
      (at_controller_cap p g hb c hcut d).symm
  | inr i => rfl

end VaughtConjecture.Knight.CoherentGradeCaps
