/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoCodedBountiful
public import VaughtConjecture.Knight.CoupledGradeOne
public import VaughtConjecture.Knight.SemScheme

/-! # The grade envelope: bounded-output lifting and high-tail release

Two corollaries of the grade-cap clipping `RespectsSemanticsBelow.gradeCap` (a lawful section
capped by an antitone, gradewise-visible family of caps is lawful), from the reviewer's
notes5 (`plan11.md` §2, `plan16.md` §2, 2026-09-18).

**Bounded-output lifting** (`bounded_lift`, `bounded_lift_of_bountiful`).  Given a lift `t` of
a prescription `p` against an ambient `q` at cap `γ`, and a bound `B ≥ γ` above every
prescribed value, clipping `t` at the **grade envelope**
`G i = max γ (max {p d : grade d ≥ i})` gives a lift with the same prescription and the same
`γ`-reading whose output is at most `B`.  `G` is antitone and `G i` is `i`-visible (every
contributing value is visible at a grade at least `i`), so the clipping is lawful; a
prescribed grade-`i` value contributes to `G i` and is retained; every `G i ≥ γ` keeps the
cap reading.  `B` need not be visible at the target grade — that is why the envelope is
gradewise rather than a uniform clip.

**High-tail release** (`high_tail_release`).  Clipping a lawful section at `⊤` below grade
`H` and at `γ` from grade `H` on is lawful, keeps every reading below `H` literal, and turns
every reading of grade at least `H` into its `γ`-reading.  **What it does and does not do**
(the reviewer's correction): it retains a prescribed face literally exactly when that face's
coordinates of grade at least `H` are already bottom (`high_tail_release_face`); it does *not*
address a prescribed high above the cap on an active face — that obstruction is untouched.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- Lower sets are finite; a local `Fintype` instance for finite maxima. -/
noncomputable abbrev fintypeBelow (BJ : Finset ι × ℕ) : Fintype (D.below BJ) :=
  Fintype.ofFinite _

attribute [local instance] fintypeBelow

/-! ## The grade envelope -/

/-- The grade envelope of a prescription: the maximum of the cap and of every prescribed value
of grade at least `i`. -/
noncomputable def gradeEnvelope {CI : Finset ι × ℕ} (p : D.below CI → ExtOrd) (γ : ExtOrd)
    (i : ℕ) : ExtOrd :=
  max γ ((Finset.univ.filter fun d : D.below CI => i ≤ D.grade d.1).sup p)

theorem le_gradeEnvelope {CI : Finset ι × ℕ} (p : D.below CI → ExtOrd) (γ : ExtOrd) (i : ℕ) :
    γ ≤ gradeEnvelope p γ i := le_max_left _ _

theorem le_gradeEnvelope_of_grade {CI : Finset ι × ℕ} (p : D.below CI → ExtOrd) (γ : ExtOrd)
    {i : ℕ} {d : D.below CI} (hd : i ≤ D.grade d.1) : p d ≤ gradeEnvelope p γ i :=
  le_max_of_le_right (Finset.le_sup (f := p) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩))

theorem gradeEnvelope_le {CI : Finset ι × ℕ} {p : D.below CI → ExtOrd} {γ B : ExtOrd}
    (hγB : γ ≤ B) (hpB : ∀ d, p d ≤ B) (i : ℕ) : gradeEnvelope p γ i ≤ B :=
  max_le hγB (Finset.sup_le fun d _ => hpB d)

theorem gradeEnvelope_anti {CI : Finset ι × ℕ} (p : D.below CI → ExtOrd) (γ : ExtOrd) :
    ∀ k k', k ≤ k' → gradeEnvelope p γ k' ≤ gradeEnvelope p γ k := by
  intro k k' hk
  refine max_le_max le_rfl (Finset.sup_mono ?_)
  intro d hd
  rw [Finset.mem_filter] at hd ⊢
  exact ⟨hd.1, hk.trans hd.2⟩

/-- The envelope at grade `i` is `i`-visible: the cap is, and every contributing prescribed
value is visible at a grade at least `i`. -/
theorem gradeEnvelope_selfVis {CI : Finset ι × ℕ} {p : D.below CI → ExtOrd}
    (hp : RespectsSemanticsBelow sem CI p) {K : ℕ} {γ : ExtOrd} (hγ : SelfVis K γ) {i : ℕ}
    (hi : i ≤ K) : SelfVis i (gradeEnvelope p γ i) := by
  refine selfVis_max (hγ.mono hi) ?_
  refine Finset.sup_induction (selfVis_bot i) (fun a ha b hb => selfVis_max ha hb) ?_
  intro d hd
  have hv : SelfVis (D.grade d.1) (p d) := (hp.orderly d).symm
  exact hv.mono (Finset.mem_filter.mp hd).2

/-! ## Bounded-output lifting -/

/-- **Bounded-output lifting**: a lift of `p` against `q` at `γ`, clipped at the grade
envelope, is a lift with the same prescription and `γ`-reading and output at most `B`. -/
theorem bounded_lift {CI BJ : Finset ι × ℕ} (h : GradedLe CI BJ) {p : D.below CI → ExtOrd}
    {q t : D.below BJ → ExtOrd} (hp : RespectsSemanticsBelow sem CI p)
    (ht : RespectsSemanticsBelow sem BJ t) (hface : ∀ d, t (CellScheme.below.mono h d) = p d)
    {γ : ExtOrd} (hcap : ∀ d, min (t d) γ = min (q d) γ) (hγ : SelfVis BJ.2 γ) {B : ExtOrd}
    (hγB : γ ≤ B) (hpB : ∀ d, p d ≤ B) :
    ∃ r : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ r ∧
      (∀ d, r (CellScheme.below.mono h d) = p d) ∧ (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ d, r d ≤ B := by
  refine ⟨fun d => min (t d) (gradeEnvelope p γ (D.grade d.1)),
    ht.gradeCap (gradeEnvelope p γ) (gradeEnvelope_anti p γ)
      (fun k hk => gradeEnvelope_selfVis hp hγ hk), ?_, ?_, ?_⟩
  · intro d
    change min (t (CellScheme.below.mono h d)) (gradeEnvelope p γ (D.grade d.1)) = p d
    rw [hface d]
    exact min_eq_left (le_gradeEnvelope_of_grade p γ le_rfl)
  · intro d
    change min (min (t d) (gradeEnvelope p γ (D.grade d.1))) γ = min (q d) γ
    rw [min_assoc, min_eq_right (le_gradeEnvelope p γ _), hcap d]
  · intro d
    exact (min_le_right _ _).trans (gradeEnvelope_le hγB hpB _)

/-- **Bounded-output bountiful lifting**: bountifulness at a graded pair, with a bound above
the cap and the prescription, gives a lift with bounded output. -/
theorem bounded_lift_of_bountiful (hb : sem.IsBountiful) {CI BJ : Finset ι × ℕ}
    (hCI : CI ∈ Plan.gradedPlan D.plan) (hBJ : BJ ∈ Plan.gradedPlan D.plan) (h : GradedLe CI BJ)
    (hne : CI ≠ BJ) {p : D.below CI → ExtOrd} {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hp : RespectsSemanticsBelow sem CI p) (hq : RespectsSemanticsBelow sem BJ q)
    (hγ : SelfVis BJ.2 γ) (hag : ∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ)
    {B : ExtOrd} (hγB : γ ≤ B) (hpB : ∀ d, p d ≤ B) :
    ∃ r : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ r ∧
      (∀ d, r (CellScheme.below.mono h d) = p d) ∧ (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ d, r d ≤ B := by
  obtain ⟨t, ht, hcap, hface⟩ := hb CI BJ hCI hBJ h hne p q γ hp hq hγ hag
  exact bounded_lift h hp ht hface hcap hγ hγB hpB

/-! ## High-tail release -/

/-- The tail caps: `⊤` below grade `H`, `γ` from `H` on. -/
noncomputable def tailCaps (H : ℕ) (γ : ExtOrd) (i : ℕ) : ExtOrd := if i < H then ⊤ else γ

theorem tailCaps_of_lt {H : ℕ} (γ : ExtOrd) {i : ℕ} (h : i < H) : tailCaps H γ i = ⊤ :=
  ite_eq_left h

theorem tailCaps_of_le {H : ℕ} (γ : ExtOrd) {i : ℕ} (h : H ≤ i) : tailCaps H γ i = γ :=
  ite_eq_right (not_lt.mpr h)

theorem tailCaps_anti (H : ℕ) (γ : ExtOrd) :
    ∀ k k', k ≤ k' → tailCaps H γ k' ≤ tailCaps H γ k := by
  intro k k' hk
  by_cases h' : k' < H
  · rw [tailCaps_of_lt γ h', tailCaps_of_lt γ (hk.trans_lt h')]
  · rw [tailCaps_of_le γ (not_lt.mp h')]
    by_cases h : k < H
    · rw [tailCaps_of_lt γ h]; exact le_top
    · rw [tailCaps_of_le γ (not_lt.mp h)]

theorem tailCaps_selfVis {H K : ℕ} {γ : ExtOrd} (hγ : SelfVis K γ) {k : ℕ} (hk : k ≤ K) :
    SelfVis k (tailCaps H γ k) := by
  unfold tailCaps
  split_ifs
  · exact extVisibilityReplace_top _ _
  · exact hγ.mono hk

/-- **High-tail release**: clipping at `⊤` below `H` and at `γ` from `H` on is lawful, keeps
readings below `H` literal, and reads every cell of grade at least `H` at its `γ`-reading. -/
theorem high_tail_release {BJ : Finset ι × ℕ} {t : D.below BJ → ExtOrd}
    (ht : RespectsSemanticsBelow sem BJ t) {γ : ExtOrd} (hγ : SelfVis BJ.2 γ) (H : ℕ) :
    RespectsSemanticsBelow sem BJ (fun d => min (t d) (tailCaps H γ (D.grade d.1))) ∧
      (∀ d, D.grade d.1 < H → min (t d) (tailCaps H γ (D.grade d.1)) = t d) ∧
      (∀ d, H ≤ D.grade d.1 → min (t d) (tailCaps H γ (D.grade d.1)) = min (t d) γ) ∧
      ∀ d, min (min (t d) (tailCaps H γ (D.grade d.1))) γ = min (t d) γ := by
  refine ⟨ht.gradeCap (tailCaps H γ) (tailCaps_anti H γ)
    (fun k hk => tailCaps_selfVis hγ hk), ?_, ?_, ?_⟩
  · intro d hd
    rw [tailCaps_of_lt γ hd]
    exact min_eq_left le_top
  · intro d hd
    rw [tailCaps_of_le γ hd]
  · intro d
    rw [min_assoc]
    congr 1
    by_cases hd : D.grade d.1 < H
    · rw [tailCaps_of_lt γ hd]; exact min_eq_right le_top
    · rw [tailCaps_of_le γ (not_lt.mp hd)]; exact min_self γ

/-- **The released lift keeps a prescribed face literal exactly when that face's coordinates of
grade at least `H` are bottom.**  This is the only sense in which release preserves a
prescription; a prescribed high above the cap on an active face is not addressed. -/
theorem high_tail_release_face {CI BJ : Finset ι × ℕ} (h : GradedLe CI BJ)
    {p : D.below CI → ExtOrd} {t : D.below BJ → ExtOrd}
    (hface : ∀ d, t (CellScheme.below.mono h d) = p d) {γ : ExtOrd} (H : ℕ)
    (hbot : ∀ d : D.below CI, H ≤ D.grade d.1 → p d = ⊥) (d : D.below CI) :
    min (t (CellScheme.below.mono h d)) (tailCaps H γ (D.grade (CellScheme.below.mono h d).1)) =
      p d := by
  change min (t (CellScheme.below.mono h d)) (tailCaps H γ (D.grade d.1)) = p d
  rw [hface d]
  by_cases hd : D.grade d.1 < H
  · rw [tailCaps_of_lt γ hd]; exact min_eq_left le_top
  · rw [hbot d (not_lt.mp hd)]; exact min_eq_left bot_le

end VaughtConjecture.Knight
