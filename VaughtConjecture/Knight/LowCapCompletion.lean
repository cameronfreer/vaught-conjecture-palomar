/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PrescribedFreshFace

/-! # The low-cap case: completing under a cap at most the ambient's donor value

The reviewer's task (2026-09-15): in the unresolved low-cap case, construct an old completion
satisfying the exact equation
`min (fresh label) (completed donor value) = sectionFresh (completed old labels)` while
retaining the prescribed fresh label and the ambient caps — or exhibit lawful inputs for which
none exists.  A failure concerns this donor construction, not every possible extension.

**Below the cap: resolved positively** (`lowCap_completion_of_lt`).  If the prescribed fresh
label is strictly below the cap, then *every* completion supplied by the receiver's own
positive-cap bountifulness satisfies the equation.  Agreement with the ambient under the cap
pins the fresh label to the ambient's, which is the ambient's forced reading, and the forced
reading of the completion agrees with the ambient's under the cap; since both sit strictly
below the cap they are equal, and the completion's donor value is at least the cap.  The rows
are frozen and no whole-ambient completion is assumed.

**Above the cap: an ambient-independent obstruction** (`owner_ge_of_unique`,
`lowCap_obstruction`).  With the donor unique at its index and the representative inside the
prescribed sub-index, every lawful completion reads the donor at least as high as every
prescribed same-grade cell (availability).  If some prescribed same-grade cell is read
strictly above both the prescribed representative value and its replacement at the requested
offset, and the prescribed fresh label is at least that cell, then **no lawful completion
satisfies the equation**, whatever the ambient and cap: the capped representative value is
the prescribed one, so the forced reading is its replacement, while the fresh label capped at
the completed donor value is at least the dominating cell.  These inputs are lawful whenever
such a section of the sub-index exists; cap-agreement with any ambient is untouched by the
three inequalities, since they concern values above any cap at most the representative's
replacement.  Whether a given receiver carries such a section is not decided here.

So under a low cap the exact equation is decidable on the prescribed data only through the
completed donor value, which agreement with the ambient does not control; the fresh label
below the cap is the case it does control.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

private theorem min_min_right_distrib' (a b γ : ExtOrd) :
    min (min a b) γ = min (min a γ) (min b γ) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (min_le_min_right γ h)]
  · rw [min_eq_right h, min_eq_right (min_le_min_right γ h)]

namespace ReferenceContext

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} {C : ReferenceContext R t reqs} {i : Fin reqs.length}

namespace MixedDonor

variable (D : C.MixedDonor i)

/-- **Below the cap, every bountiful completion satisfies the equation**: for an ambient
`(qo, F)` that is a faithful capped target with lawful old part, a cap self-visible at the
donor's grade and at most the ambient's donor value, prescribed data on a proper old sub-index
agreeing with the ambient under the cap, and a prescribed fresh label strictly below the cap,
the receiver's own positive-cap bountifulness yields a lawful completion agreeing with the
ambient under the cap and carrying the literal fresh label. -/
theorem lowCap_completion_of_lt (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell)
    {CI : Finset (Fin C.m) × ℕ} (hCI : CI ∈ Plan.gradedPlan C.p₀.scheme.scheme.plan)
    (hle : GradedLe CI (C.p₀.scheme.scheme.cell D.cell)) (hne : CI ≠ C.p₀.scheme.scheme.cell D.cell)
    (p : C.p₀.scheme.scheme.below CI → ExtOrd)
    (hp : RespectsSemanticsBelow C.p₀.scheme.rows CI p)
    (qo : D.Old → ExtOrd)
    (hqo : RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) qo)
    (F : ExtOrd) (hamb : D.SimultaneousSection qo F g₀)
    {γ : ExtOrd} (hγ : SelfVis (C.p₀.scheme.scheme.grade D.cell) γ) (hlow : γ ≤ qo D.owner)
    (hagree : ∀ d : C.p₀.scheme.scheme.below CI,
      min (qo (CellScheme.below.mono hle d)) γ = min (p d) γ)
    (φ : ExtOrd) (hφ : min F γ = min φ γ) (hφlt : φ < γ) :
    ∃ p' : D.Old → ExtOrd,
      RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p' ∧
      (∀ d : D.Old, min (p' d) γ = min (qo d) γ) ∧
      (∀ d : C.p₀.scheme.scheme.below CI, p' (CellScheme.below.mono hle d) = p d) ∧
      D.SimultaneousSection p' φ g₀ := by
  obtain ⟨p', hp', hagree', hres⟩ := C.p₀.scheme.bountiful CI _ hCI
    (C.p₀.scheme.scheme.cell_mem D.cell) hle hne p qo γ hp hqo hγ hagree
  refine ⟨p', hp', hagree', hres, (D.simultaneous_iff p' hp' φ g₀ hg₀).mpr ?_⟩
  -- the ambient's fresh reading is the prescribed label
  have hF : F = φ := by
    rw [min_eq_left hφlt.le] at hφ
    rcases le_or_gt F γ with h | h
    · rwa [min_eq_left h] at hφ
    · rw [min_eq_right h.le] at hφ
      exact absurd hφlt (not_lt.mpr hφ.le)
  -- hence the ambient's forced reading is the prescribed label
  have hsq : D.sectionFresh qo = φ := by
    have h := (D.simultaneous_iff qo hqo F g₀ hg₀).mp hamb
    rw [hF, min_eq_left (hφlt.le.trans hlow)] at h
    exact h.symm
  -- the completion's forced reading agrees with the ambient's under the cap
  have hy : min (min (p' D.rep) (p' D.owner)) γ =
      min (min (qo D.rep) (qo D.owner)) γ := by
    rw [min_min_right_distrib', hagree' D.rep, hagree' D.owner, ← min_min_right_distrib']
  have hR : min (D.sectionFresh p') γ = min (D.sectionFresh qo) γ :=
    min_extVisibilityReplace_eq hγ hy
  rw [hsq, min_eq_left hφlt.le] at hR
  have hsp : D.sectionFresh p' = φ := by
    rcases le_or_gt (D.sectionFresh p') γ with h | h
    · rwa [min_eq_left h] at hR
    · rw [min_eq_right h.le] at hR
      exact absurd hφlt (not_lt.mpr hR.le)
  -- the completion's donor value is at least the cap
  have ho : γ ≤ p' D.owner := by
    have h := hagree' D.owner
    rw [min_eq_right hlow] at h
    exact min_eq_right_iff.mp h
  rw [hsp, min_eq_left (hφlt.le.trans ho)]

/-- **A unique donor is read at least as high as every same-grade cell of a prescribed
sub-index** by every lawful completion (availability). -/
theorem owner_ge_of_unique {CI : Finset (Fin C.m) × ℕ}
    (hle : GradedLe CI (C.p₀.scheme.scheme.cell D.cell))
    (huniq : ∀ w : D.Old, C.p₀.scheme.scheme.cell w.1 = C.p₀.scheme.scheme.cell D.cell →
      w.1 = D.cell)
    (d : C.p₀.scheme.scheme.below CI)
    (hd : C.p₀.scheme.scheme.grade d.1 = C.p₀.scheme.scheme.grade D.cell)
    (p' : D.Old → ExtOrd)
    (hp' : RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p') :
    p' (CellScheme.below.mono hle d) ≤ p' D.owner := by
  obtain ⟨Xi, hXi, hle'⟩ := hp'.availability (CellScheme.below.mono hle d) D.owner
    (d.2.trans hle).1 hd
  have hXi' : Xi = D.owner := Subtype.ext (huniq Xi hXi)
  rwa [hXi'] at hle'

/-- **Above the cap: inputs for which no completion exists.**  With the donor unique at its
index and the representative inside the prescribed sub-index, if a prescribed same-grade cell
is read strictly above both the prescribed representative value and its replacement at the
requested offset, and the prescribed fresh label is at least that cell, then no lawful
completion of the prescribed face forms a simultaneous section with that fresh label —
whatever the ambient and the cap. -/
theorem lowCap_obstruction (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell)
    {CI : Finset (Fin C.m) × ℕ} (hle : GradedLe CI (C.p₀.scheme.scheme.cell D.cell))
    (huniq : ∀ w : D.Old, C.p₀.scheme.scheme.cell w.1 = C.p₀.scheme.scheme.cell D.cell →
      w.1 = D.cell)
    (hrep : GradedLe (C.p₀.scheme.scheme.cell (C.repBase reqs[i.val].block)) CI)
    (d : C.p₀.scheme.scheme.below CI)
    (hd : C.p₀.scheme.scheme.grade d.1 = C.p₀.scheme.scheme.grade D.cell)
    (p : C.p₀.scheme.scheme.below CI → ExtOrd) (φ : ExtOrd)
    (h1 : p ⟨C.repBase reqs[i.val].block, hrep⟩ < p d)
    (h2 : extVisibilityReplace (p ⟨C.repBase reqs[i.val].block, hrep⟩)
      (C.p₀.scheme.scheme.grade D.cell) reqs[i.val].offset < p d)
    (h3 : p d ≤ φ) :
    ¬ ∃ p' : D.Old → ExtOrd,
      RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p' ∧
      (∀ e : C.p₀.scheme.scheme.below CI, p' (CellScheme.below.mono hle e) = p e) ∧
      D.SimultaneousSection p' φ g₀ := by
  rintro ⟨p', hp', hres, hs⟩
  have hcrit := (D.simultaneous_iff p' hp' φ g₀ hg₀).mp hs
  -- the completed representative value is the prescribed one
  have hrep' : p' D.rep = p ⟨C.repBase reqs[i.val].block, hrep⟩ := by
    have h := hres ⟨C.repBase reqs[i.val].block, hrep⟩
    rwa [show CellScheme.below.mono hle ⟨C.repBase reqs[i.val].block, hrep⟩ = D.rep from
      Subtype.ext rfl] at h
  -- the completed donor value dominates the prescribed cell
  have hod : p d ≤ p' D.owner := by
    have h := D.owner_ge_of_unique hle huniq d hd p' hp'
    rwa [hres d] at h
  have hlt : p' D.rep < p' D.owner := by rw [hrep']; exact h1.trans_le hod
  unfold sectionFresh at hcrit
  rw [min_eq_left hlt.le, hrep'] at hcrit
  have hge : p d ≤ min φ (p' D.owner) := le_min h3 hod
  rw [hcrit] at hge
  exact absurd h2 (not_lt.mpr hge)

end MixedDonor

end ReferenceContext

end VaughtConjecture.Knight
