/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.DonorSections

/-! # Prescribed fresh faces: the exact simultaneous-section criterion at one incidence

The reviewer's task (2026-09-15): prove the exact simultaneous-section criterion at the single
incidence — prescribed old-face labels **and a fixed fresh label** — first at bottom cap, then
against an arbitrary lawful ambient at the original cap; derive the required fresh readback
equation at the actual donor cap; construct the constrained old completion when possible;
distinguish necessary from sufficient compatibility; keep the rows frozen.  The qualification
driving it: when the prescribed face already contains the fresh cell, its value may not be
repaired, and agreement below the ambient cap alone does not suffice.

**The criterion** (`simultaneous_iff`).  For a lawful labelling `p` of the donor's lower domain
and a fixed fresh label `φ`, the mixed row transforms to `(p, φ)` capped at `p`'s donor value
**iff** `min φ (p owner) = sectionFresh p`: the fresh label, capped at the donor, must equal the
forced reading.  Necessity is `capped_fresh`; sufficiency is `section_transformsTo`.  So the
literal fresh label is admitted exactly when it is the forced reading, or exceeds the donor
value while the forced reading equals it.

**At the actual donor cap** (`sectionFresh_label`, `readback_at_donor_cap`,
`prescribed_eq_value_of_lt`): with the receiver's labels the forced reading is the requested
value, so the equation is `min φ (label donor) = value`; when the requested value is strictly
below the donor's label, the only admissible fresh label is the requested value itself.

**Agreement is not enough** (`agreement_insufficient`).  A fresh label whose capped value is
not the requested value agrees with the selected display under every cap at most both, yet
admits no simultaneous section with the actual labels.  Repairing it is what `DonorSections`
did; with the fresh cell prescribed, that repair is unavailable.

**Bottom cap on a proper old sub-index** (`bottomCap_prescribed_iff`): a lawful section of a
proper old sub-index together with a fixed fresh label extends to the incidence iff some
lawful old completion satisfies the criterion — necessary and sufficient, but not checkable on
the prescribed data alone, because the donor value and the representative's value are
completed, not prescribed.

**The constrained old completion** (`constrained_completion`, sufficient).  If a lawful old
ambient `q` on the donor's lower domain satisfies the criterion with `φ`, and the prescribed
sub-index face agrees with `q` under a cap `γ`, self-visible at the donor's grade and
**strictly above `q`'s donor value**, then the receiver's own positive-cap bountifulness
supplies a lawful completion agreeing with `q` under `γ`; the strict inequality pins the donor
value and the capped representative value, so the criterion transfers.  This uses the frozen
old rows only.

**Against an arbitrary lawful ambient at the original cap** (`positiveCap_prescribed_iff`,
`positiveCap_constrained_completion`).  For an ambient `(qo, F)` of the carrier that is a
faithful capped target, a cap `γ`, and prescribed data agreeing with it under `γ`, a lawful
completion agreeing with the ambient under `γ` and carrying the literal `φ` exists iff some
lawful old completion agreeing with `qo` under `γ` satisfies the criterion (necessary and
sufficient); and it exists whenever `γ` is strictly above the ambient's donor value
(sufficient).  When the cap is at most the ambient's donor value, agreement leaves the donor
value free above the cap, and the criterion is a genuine additional condition — this is where
agreement below the cap does not suffice.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

namespace ReferenceContext

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} {C : ReferenceContext R t reqs} {i : Fin reqs.length}

namespace MixedDonor

variable (D : C.MixedDonor i)

/-- **A simultaneous section**: prescribed old-face labels `p` and a fixed fresh label `φ`, as a
faithful capped target of the mixed row at fresh grade `g₀`. -/
def SimultaneousSection (p : D.Old → ExtOrd) (φ : ExtOrd) (g₀ : ℕ) : Prop :=
  TransformsTo (Sum.elim (fun d : D.Old => C.p₀.scheme.scheme.grade d.1) (fun _ => g₀))
    D.mixedSource (fun x => min (Sum.elim p (fun _ => φ) x) (p D.owner))

/-- **The exact criterion**: a lawful old face and a fixed fresh label form a simultaneous
section iff the fresh label capped at the donor is the forced reading. -/
theorem simultaneous_iff (p : D.Old → ExtOrd)
    (hp : RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p)
    (φ : ExtOrd) (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell) :
    D.SimultaneousSection p φ g₀ ↔ min φ (p D.owner) = D.sectionFresh p := by
  constructor
  · intro h
    exact D.capped_fresh g₀ hg₀ (Sum.elim p (fun _ => φ)) (hp.orderly D.owner).symm h
  · intro h
    have hs := D.section_transformsTo p hp g₀ hg₀
    unfold SimultaneousSection
    convert hs using 1
    funext x
    rcases x with d | u
    · rfl
    · change min φ (p D.owner) = min (D.sectionFresh p) (p D.owner)
      rw [h, min_eq_left (D.sectionFresh_le p (hp.orderly D.owner).symm)]

/-! ## At the actual donor cap -/

include D in
/-- Under the receiver's labels the forced reading is the requested value. -/
theorem sectionFresh_label (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block) :
    D.sectionFresh (fun d => C.p₀.label d.1) = ofOrd reqs[i.val].value := by
  have hr := List.getElem_mem i.isLt
  unfold sectionFresh
  change extVisibilityReplace (min (C.p₀.label (C.repBase reqs[i.val].block)) (C.p₀.label D.cell))
    (C.p₀.scheme.scheme.grade D.cell) reqs[i.val].offset = _
  rw [min_eq_left D.rep_le_label, C.rep_label _ hr]
  exact extVisibilityReplace_rep (hblocks _ hr) D.rep_off_lt

/-- **The required fresh readback equation at the actual donor cap**: with the receiver's
labels, a fixed fresh label forms a simultaneous section iff its value capped at the donor's
label is the requested value. -/
theorem readback_at_donor_cap (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block) (φ : ExtOrd)
    (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell) :
    D.SimultaneousSection (fun d => C.p₀.label d.1) φ g₀ ↔
      min φ (C.p₀.label D.cell) = ofOrd reqs[i.val].value := by
  rw [D.simultaneous_iff _ (C.p₀.respects.toBelow _) φ g₀ hg₀, D.sectionFresh_label hblocks]
  exact Iff.rfl

/-- When the requested value is strictly below the donor's label, the requested value is the
only admissible fixed fresh label. -/
theorem prescribed_eq_value_of_lt (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block)
    (hlt : ofOrd reqs[i.val].value < C.p₀.label D.cell) (φ : ExtOrd)
    (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell) :
    D.SimultaneousSection (fun d => C.p₀.label d.1) φ g₀ ↔ φ = ofOrd reqs[i.val].value := by
  rw [D.readback_at_donor_cap hblocks φ g₀ hg₀]
  constructor
  · intro h
    rcases le_or_gt φ (C.p₀.label D.cell) with hle | hgt
    · rwa [min_eq_left hle] at h
    · rw [min_eq_right hgt.le] at h
      exact absurd hlt (not_lt.mpr h.le)
  · intro h
    rw [h, min_eq_left hlt.le]

/-- **Agreement below a cap does not suffice**: a fixed fresh label whose capped value is not
the requested value agrees with the selected display under every cap at most both, yet admits
no simultaneous section with the actual labels. -/
theorem agreement_insufficient (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block) (φ : ExtOrd)
    (hφ : min φ (C.p₀.label D.cell) ≠ ofOrd reqs[i.val].value)
    (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell) :
    ¬ D.SimultaneousSection (fun d => C.p₀.label d.1) φ g₀ ∧
      ∀ γ : ExtOrd, γ ≤ φ → γ ≤ ofOrd reqs[i.val].value →
        min φ γ = min (ofOrd reqs[i.val].value) γ := by
  refine ⟨fun h => hφ ((D.readback_at_donor_cap hblocks φ g₀ hg₀).mp h), ?_⟩
  intro γ h1 h2
  rw [min_eq_right h1, min_eq_right h2]

/-! ## Bottom cap on a proper old sub-index -/

/-- **The bottom-cap criterion for prescribed data on a proper old sub-index**: a lawful
section `p` of a proper old sub-index and a fixed fresh label extend to a simultaneous section
iff some lawful old completion of `p` satisfies the criterion. -/
theorem bottomCap_prescribed_iff (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell)
    {CI : Finset (Fin C.m) × ℕ} (hle : GradedLe CI (C.p₀.scheme.scheme.cell D.cell))
    (p : C.p₀.scheme.scheme.below CI → ExtOrd) (φ : ExtOrd) :
    (∃ p' : D.Old → ExtOrd,
      RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p' ∧
      (∀ d : C.p₀.scheme.scheme.below CI, p' (CellScheme.below.mono hle d) = p d) ∧
      D.SimultaneousSection p' φ g₀) ↔
    ∃ p' : D.Old → ExtOrd,
      RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p' ∧
      (∀ d : C.p₀.scheme.scheme.below CI, p' (CellScheme.below.mono hle d) = p d) ∧
      min φ (p' D.owner) = D.sectionFresh p' := by
  constructor
  · rintro ⟨p', hp', hres, hs⟩
    exact ⟨p', hp', hres, (D.simultaneous_iff p' hp' φ g₀ hg₀).mp hs⟩
  · rintro ⟨p', hp', hres, hs⟩
    exact ⟨p', hp', hres, (D.simultaneous_iff p' hp' φ g₀ hg₀).mpr hs⟩

/-! ## The constrained old completion -/

/-- Under a cap strictly above `q`'s donor value, agreement with `q` under the cap pins the
donor value and the capped representative value, hence the forced reading. -/
theorem sectionFresh_eq_of_agree {p q : D.Old → ExtOrd} {γ : ExtOrd}
    (hlt : q D.owner < γ) (hagree : ∀ d, min (p d) γ = min (q d) γ) :
    p D.owner = q D.owner ∧ D.sectionFresh p = D.sectionFresh q := by
  have ho : p D.owner = q D.owner := by
    have h := hagree D.owner
    rw [min_eq_left hlt.le] at h
    rcases le_or_gt (p D.owner) γ with hp | hp
    · rw [min_eq_left hp] at h; exact h
    · rw [min_eq_right hp.le] at h
      exact absurd hlt (not_lt.mpr h.le)
  refine ⟨ho, ?_⟩
  have hoγ : p D.owner ≤ γ := ho ▸ hlt.le
  unfold sectionFresh
  congr 1
  calc min (p D.rep) (p D.owner) = min (min (p D.rep) γ) (p D.owner) := by
        rw [min_assoc, min_eq_right hoγ]
    _ = min (min (q D.rep) γ) (p D.owner) := by rw [hagree D.rep]
    _ = min (q D.rep) (p D.owner) := by rw [min_assoc, min_eq_right hoγ]
    _ = min (q D.rep) (q D.owner) := by rw [ho]

/-- **The constrained old completion (sufficient)**: if a lawful old ambient `q` satisfies the
criterion with the fixed fresh label, and a lawful section of a proper old sub-index agrees
with `q` under a cap self-visible at the donor's grade and strictly above `q`'s donor value,
then the receiver's own positive-cap bountifulness completes it, agreeing with `q` under the
cap, and the completion carries the literal fresh label.  The rows are frozen. -/
theorem constrained_completion (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell)
    {CI : Finset (Fin C.m) × ℕ} (hCI : CI ∈ Plan.gradedPlan C.p₀.scheme.scheme.plan)
    (hle : GradedLe CI (C.p₀.scheme.scheme.cell D.cell)) (hne : CI ≠ C.p₀.scheme.scheme.cell D.cell)
    (p : C.p₀.scheme.scheme.below CI → ExtOrd)
    (hp : RespectsSemanticsBelow C.p₀.scheme.rows CI p)
    (q : D.Old → ExtOrd)
    (hq : RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) q)
    (φ : ExtOrd) (hqφ : min φ (q D.owner) = D.sectionFresh q)
    {γ : ExtOrd} (hγ : SelfVis (C.p₀.scheme.scheme.grade D.cell) γ) (hlt : q D.owner < γ)
    (hagree : ∀ d : C.p₀.scheme.scheme.below CI,
      min (q (CellScheme.below.mono hle d)) γ = min (p d) γ) :
    ∃ p' : D.Old → ExtOrd,
      RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p' ∧
      (∀ d : D.Old, min (p' d) γ = min (q d) γ) ∧
      (∀ d : C.p₀.scheme.scheme.below CI, p' (CellScheme.below.mono hle d) = p d) ∧
      D.SimultaneousSection p' φ g₀ := by
  obtain ⟨p', hp', hagree', hres⟩ := C.p₀.scheme.bountiful CI _ hCI
    (C.p₀.scheme.scheme.cell_mem D.cell) hle hne p q γ hp hq hγ hagree
  obtain ⟨ho, hsf⟩ := D.sectionFresh_eq_of_agree hlt hagree'
  refine ⟨p', hp', hagree', hres, (D.simultaneous_iff p' hp' φ g₀ hg₀).mpr ?_⟩
  rw [ho, hsf]
  exact hqφ

/-! ## Against an arbitrary lawful ambient at the original cap -/

/-- **The positive-cap criterion for prescribed data**: given an ambient `(qo, F)` of the
carrier, a cap `γ`, and prescribed data on a proper old sub-index with a fixed fresh label
agreeing with the ambient under `γ`, a lawful completion agreeing with the ambient under `γ`
and carrying the literal fresh label exists iff some lawful old completion agreeing with `qo`
under `γ` satisfies the criterion. -/
theorem positiveCap_prescribed_iff (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell)
    {CI : Finset (Fin C.m) × ℕ} (hle : GradedLe CI (C.p₀.scheme.scheme.cell D.cell))
    (p : C.p₀.scheme.scheme.below CI → ExtOrd) (φ : ExtOrd) (qo : D.Old → ExtOrd)
    (γ : ExtOrd) :
    (∃ p' : D.Old → ExtOrd,
      RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p' ∧
      (∀ d : D.Old, min (p' d) γ = min (qo d) γ) ∧
      (∀ d : C.p₀.scheme.scheme.below CI, p' (CellScheme.below.mono hle d) = p d) ∧
      D.SimultaneousSection p' φ g₀) ↔
    ∃ p' : D.Old → ExtOrd,
      RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p' ∧
      (∀ d : D.Old, min (p' d) γ = min (qo d) γ) ∧
      (∀ d : C.p₀.scheme.scheme.below CI, p' (CellScheme.below.mono hle d) = p d) ∧
      min φ (p' D.owner) = D.sectionFresh p' := by
  constructor
  · rintro ⟨p', hp', ha, hres, hs⟩
    exact ⟨p', hp', ha, hres, (D.simultaneous_iff p' hp' φ g₀ hg₀).mp hs⟩
  · rintro ⟨p', hp', ha, hres, hs⟩
    exact ⟨p', hp', ha, hres, (D.simultaneous_iff p' hp' φ g₀ hg₀).mpr hs⟩

/-- **Positive-cap completion with a literal fresh label (sufficient)**: for an ambient
`(qo, F)` that is a faithful capped target with lawful old part, a cap self-visible at the
donor's grade and strictly above the ambient's donor value, and prescribed data agreeing with
the ambient under the cap on the old sub-index and at the fresh cell, a lawful completion
agreeing with the ambient under the cap and carrying the literal fresh label exists. -/
theorem positiveCap_constrained_completion (g₀ : ℕ)
    (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell)
    {CI : Finset (Fin C.m) × ℕ} (hCI : CI ∈ Plan.gradedPlan C.p₀.scheme.scheme.plan)
    (hle : GradedLe CI (C.p₀.scheme.scheme.cell D.cell)) (hne : CI ≠ C.p₀.scheme.scheme.cell D.cell)
    (p : C.p₀.scheme.scheme.below CI → ExtOrd)
    (hp : RespectsSemanticsBelow C.p₀.scheme.rows CI p)
    (qo : D.Old → ExtOrd)
    (hqo : RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) qo)
    (F : ExtOrd) (hamb : D.SimultaneousSection qo F g₀)
    {γ : ExtOrd} (hγ : SelfVis (C.p₀.scheme.scheme.grade D.cell) γ) (hlt : qo D.owner < γ)
    (hagree : ∀ d : C.p₀.scheme.scheme.below CI,
      min (qo (CellScheme.below.mono hle d)) γ = min (p d) γ)
    (φ : ExtOrd) (hφ : min F γ = min φ γ) :
    ∃ p' : D.Old → ExtOrd,
      RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p' ∧
      (∀ d : D.Old, min (p' d) γ = min (qo d) γ) ∧
      (∀ d : C.p₀.scheme.scheme.below CI, p' (CellScheme.below.mono hle d) = p d) ∧
      D.SimultaneousSection p' φ g₀ := by
  have hF := (D.simultaneous_iff qo hqo F g₀ hg₀).mp hamb
  have hqφ : min φ (qo D.owner) = D.sectionFresh qo := by
    rw [← hF]
    calc min φ (qo D.owner) = min (min φ γ) (qo D.owner) := by
          rw [min_assoc, min_eq_right hlt.le]
      _ = min (min F γ) (qo D.owner) := by rw [hφ]
      _ = min F (qo D.owner) := by rw [min_assoc, min_eq_right hlt.le]
  exact D.constrained_completion g₀ hg₀ hCI hle hne p hp qo hqo φ hqφ hγ hlt hagree

end MixedDonor

end ReferenceContext

end VaughtConjecture.Knight
