/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SeparatedGradeOne

/-! # Whole bountifulness of separated grade-one rows with mute higher rows

Mute labels are derived from locality, not imposed on the input. Restriction
to grade one and extension by bottom preserve respect in both directions.
Thus the constructed family is bountiful at every literal graded pair when
the carrier is complete and index-injective. The cap is never raised.

No higher-grade nonbottom request is served by this construction.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SeparatedGradeOne.Profile

open AmalgamationPlan Transform Value ExtOrd FullRowLifting

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (F : Profile D) {BJ : Finset ι × ℕ}

private theorem below_eta (d : D.below BJ) (h : GradedLe (D.cell d.1) BJ) :
    (⟨d.1, h⟩ : D.below BJ) = d := Subtype.ext rfl

/-- A mute owner's label is bottom in every lawful local input. -/
theorem mute_label {p : D.below BJ → ExtOrd} (hp : RespectsSemanticsBelow F.rows BJ p)
    (c : D.below BJ) (hc : D.grade c.1 ≠ 1) : p c = ⊥ := by
  rcases c with ⟨c, hcBJ⟩
  obtain ⟨g, σ, _, _, hbot, _, _, he⟩ := hp.locality ⟨c, hcBJ⟩
  have hh := he ⟨c, GradedLe.refl _⟩
  change min (p ⟨c, hcBJ⟩) (p ⟨c, hcBJ⟩) =
    min (σ (if D.grade c = 1 then F.source c else ⊥)) (g (D.grade c)) at hh
  simpa only [hc, ↓reduceIte, hbot, min_bot_left, min_self] using hh

/-- Extend a grade-one labelling by bottom at every higher-grade occurrence. -/
def extend (r : D.below (BJ.1, 1) → ExtOrd) (d : D.below BJ) : ExtOrd :=
  if hd : D.grade d.1 = 1 then r ⟨d.1, d.2.1, hd.le⟩ else ⊥

theorem extend_respects {r : D.below (BJ.1, 1) → ExtOrd}
    (hr : RespectsSemanticsBelow F.rows (BJ.1, 1) r) :
    RespectsSemanticsBelow F.rows BJ (extend r) where
  orderly d := by
    by_cases hd : D.grade d.1 = 1
    · simpa only [extend, hd, ↓reduceDIte] using hr.orderly ⟨d.1, d.2.1, hd.le⟩
    · simp only [extend, hd, ↓reduceDIte, extVisibilityReplace_bot]
  locality c := by
    by_cases hc : D.grade c.1 = 1
    · have ht := hr.locality ⟨c.1, c.2.1, hc.le⟩
      convert ht using 1
      funext d
      have hd : D.grade d.1 = 1 := le_antisymm (hc ▸ d.2.2) (D.grade_pos d.1)
      simp only [extend, CellScheme.below.incl, hd, hc, ↓reduceDIte]
    · have ht := (TransformsTo.refl
        (grade := fun d : D.below (D.cell c.1) => D.grade d.1) (F.rows.E c.1)).cap
        (fun d => d.2.2) (selfVis_bot (D.grade c.1))
      simpa only [extend, hc, ↓reduceDIte, min_bot_right] using ht
  availability d e hs hg := by
    by_cases hd : D.grade d.1 = 1
    · have he : D.grade e.1 = 1 := hg.symm.trans hd
      obtain ⟨⟨f, hf₀⟩, hf, hle⟩ :=
        hr.availability ⟨d.1, d.2.1, hd.le⟩ ⟨e.1, e.2.1, he.le⟩ hs hg
      have hfgrade : D.grade f = 1 := (congrArg Prod.snd hf).trans he
      have hfbelow : GradedLe (D.cell f) BJ := by rw [hf]; exact e.2
      refine ⟨⟨f, hfbelow⟩, hf, ?_⟩
      simpa only [extend, hd, hfgrade, ↓reduceDIte] using hle
    · exact ⟨e, rfl, by simp only [extend, hd, ↓reduceDIte, bot_le]⟩

/-- Every lawful input is recovered from its grade-one restriction; no
ambient extension is needed for this normal form. -/
theorem extend_restrict {p : D.below BJ → ExtOrd} (hJ : 1 ≤ BJ.2)
    (hp : RespectsSemanticsBelow F.rows BJ p) :
    extend (fun d => p (CellScheme.below.mono (show GradedLe (BJ.1, 1) BJ from
      ⟨Finset.Subset.refl _, hJ⟩) d)) = p := by
  funext d
  by_cases hd : D.grade d.1 = 1
  · simp only [extend, hd, ↓reduceDIte, CellScheme.below.mono, below_eta]
  · simp only [extend, hd, ↓reduceDIte, F.mute_label hp d hd]

/-- Grade one belongs to the plan at every scope appearing in a graded index. -/
theorem one_mem {J : Finset ι × ℕ} (hJ : J ∈ Plan.gradedPlan D.plan) :
    (J.1, 1) ∈ Plan.gradedPlan D.plan := by
  obtain ⟨hs, hg, hcard⟩ := Plan.mem_gradedPlan.mp hJ
  exact Plan.mem_gradedPlan.mpr ⟨hs, Nat.zero_lt_one, (Nat.succ_le_of_lt hg).trans hcard⟩

/-- Whole-scheme unrestricted bountifulness for the constructed rows.
Completeness and index injectivity are geometric, not extension hypotheses. -/
theorem bountiful (hinj : Function.Injective D.cell) (hcomplete : D.IsComplete) :
    F.rows.IsBountiful := by
  intro CI BJ hCI hBJ h _ p q γ hp hq hγ hag
  have hI : 1 ≤ CI.2 := (Plan.mem_gradedPlan.mp hCI).2.1
  have hJ : 1 ≤ BJ.2 := (Plan.mem_gradedPlan.mp hBJ).2.1
  let i : GradedLe (CI.1, 1) CI := ⟨Finset.Subset.refl _, hI⟩
  let j : GradedLe (BJ.1, 1) BJ := ⟨Finset.Subset.refl _, hJ⟩
  let ij : GradedLe (CI.1, 1) (BJ.1, 1) := ⟨h.1, le_rfl⟩
  obtain ⟨b, hb⟩ := hcomplete _ (one_mem hCI)
  obtain ⟨c, hc⟩ := hcomplete _ (one_mem hBJ)
  have hp1 := hp.mono i
  have hq1 := hq.mono j
  have hγJ : SelfVis BJ.2 γ := hγ
  have hγ1 : SelfVis 1 γ := hγJ.mono hJ
  obtain ⟨r, hr, hcap, hpres⟩ := F.liftsAt hinj ij rfl rfl ⟨b, hb⟩ ⟨c, hc⟩
    _ _ γ hp1 hq1 hγ1 (fun d => hag (CellScheme.below.mono i d))
  refine ⟨extend r, F.extend_respects hr, ?_, ?_⟩
  · intro d
    by_cases hd : D.grade d.1 = 1
    · have hh := hcap ⟨d.1, d.2.1, hd.le⟩
      simpa only [extend, hd, ↓reduceDIte, CellScheme.below.mono, below_eta] using hh
    · simp only [extend, hd, ↓reduceDIte, F.mute_label hq d hd]
  · intro d
    by_cases hd : D.grade d.1 = 1
    · have hh := hpres ⟨d.1, d.2.1, hd.le⟩
      simpa only [extend, CellScheme.below.mono, hd, ↓reduceDIte, below_eta] using hh
    · simp only [extend, CellScheme.below.mono, hd, ↓reduceDIte, F.mute_label hp d hd]

end VaughtConjecture.Knight.SeparatedGradeOne.Profile
