/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HighGradeExtension

/-! # Unrestricted lifting across a fresh higher grade

Lift the retained part by its bountifulness. At the new controller keep
the prescribed value if present, and otherwise cap its actual ambient
value at the original cap. Its locality follows by the Cap Lemma. No
separated-source, uniqueness, selected-label, or whole-ambient hypothesis
is imposed on the lower-grade semantics.
-/

@[expose] public section

namespace VaughtConjecture.Knight.HighGradeExtension.Data

open AmalgamationPlan Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}
  (F : Data D k) {BJ CI : Finset ι × ℕ}

def cut (BJ : Finset ι × ℕ) (k : ℕ) : Finset ι × ℕ := (BJ.1, min BJ.2 k)

omit [DecidableEq ι] in
theorem cut_le : GradedLe (cut BJ k) BJ := ⟨Finset.Subset.refl _, min_le_left _ _⟩

omit [DecidableEq ι] in
theorem cut_mono (h : GradedLe CI BJ) : GradedLe (cut CI k) (cut BJ k) :=
  ⟨h.1, min_le_min h.2 le_rfl⟩

theorem cut_mem (hk : 1 ≤ k) (h : BJ ∈ Plan.gradedPlan D.plan) :
    cut BJ k ∈ Plan.gradedPlan D.plan := by
  obtain ⟨hB, hJ, hcard⟩ := Plan.mem_gradedPlan.mp h
  exact Plan.mem_gradedPlan.mpr ⟨hB, lt_min hJ (Nat.lt_of_lt_of_le (by decide) hk),
    (min_le_left _ _).trans hcard⟩

theorem respects_of {r : D.below (cut BJ k) → ExtOrd} {q : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow F.base (cut BJ k) r)
    (hread : ∀ d : D.below BJ, ∀ hd : D.grade d.1 ≤ k,
      q d = r ⟨d.1, d.2.1, le_min d.2.2 hd⟩)
    (hvis : ∀ d, SelfVis (D.grade d.1) (q d))
    (hmute : ∀ d, ¬D.grade d.1 ≤ k → d.1 ≠ F.high → q d = ⊥)
    (hhigh : ∀ c : D.below BJ, c.1 = F.high →
      TransformsTo (fun d : D.below (D.cell c.1) => D.grade d.1) (F.rows.E c.1)
        (fun d => min (q (CellScheme.below.incl c d)) (q c))) :
    RespectsSemanticsBelow F.rows BJ q where
  orderly d := (hvis d).symm
  locality c := by
    by_cases hc : D.grade c.1 ≤ k
    · rw [F.row_old hc]
      have ht := hr.locality ⟨c.1, c.2.1, le_min c.2.2 hc⟩
      convert ht using 1
      funext d
      rw [hread c hc, hread (CellScheme.below.incl c d) (d.2.2.trans hc)]
      rfl
    · by_cases he : c.1 = F.high
      · exact hhigh c he
      · simpa only [hmute c hc he, min_bot_right] using
          (TransformsTo.to_bot (grade := fun d : D.below (D.cell c.1) => D.grade d.1)
            (F.rows.E c.1))
  availability d e hs hg := by
    by_cases hd : D.grade d.1 ≤ k
    · have he : D.grade e.1 ≤ k := hg ▸ hd
      obtain ⟨f, hf, hv⟩ := hr.availability
        ⟨d.1, d.2.1, le_min d.2.2 hd⟩ ⟨e.1, e.2.1, le_min e.2.2 he⟩ hs hg
      have hfb : GradedLe (D.cell f.1) BJ := f.2.trans cut_le
      have hfk : D.grade f.1 ≤ k := f.2.2.trans (min_le_right _ _)
      refine ⟨⟨f.1, hfb⟩, hf, ?_⟩
      rw [hread d hd, hread ⟨f.1, hfb⟩ hfk]
      exact hv
    · by_cases he : d.1 = F.high
      · refine ⟨d, ?_, le_rfl⟩
        rw [he]
        exact F.high_index (by simpa only [he] using hs) (by simpa only [he] using hg)
      · exact ⟨e, rfl, by rw [hmute d hd he]; exact bot_le⟩

def fill (r : D.below (cut BJ k) → ExtOrd) (η : ExtOrd) (d : D.below BJ) : ExtOrd :=
  if hd : D.grade d.1 ≤ k then r ⟨d.1, d.2.1, le_min d.2.2 hd⟩ else
    if d.1 = F.high then η else ⊥

theorem fill_old {r : D.below (cut BJ k) → ExtOrd} {η : ExtOrd}
    (d : D.below BJ) (hd : D.grade d.1 ≤ k) :
    F.fill r η d = r ⟨d.1, d.2.1, le_min d.2.2 hd⟩ := by
  simp only [fill, hd, ↓reduceDIte]

theorem fill_high {r : D.below (cut BJ k) → ExtOrd} {η : ExtOrd}
    (hc : GradedLe (D.cell F.high) BJ) : F.fill r η ⟨F.high, hc⟩ = η := by
  simp only [fill, not_le_of_gt F.above, ↓reduceDIte, ↓reduceIte]

theorem fill_mute {r : D.below (cut BJ k) → ExtOrd} {η : ExtOrd}
    (d : D.below BJ) (hd : ¬D.grade d.1 ≤ k) (he : d.1 ≠ F.high) :
    F.fill r η d = ⊥ := by simp only [fill, hd, he, ↓reduceDIte, ↓reduceIte]

private theorem base_lift (hb : F.base.IsBountiful)
    (hCI : CI ∈ Plan.gradedPlan D.plan) (hBJ : BJ ∈ Plan.gradedPlan D.plan)
    (h : GradedLe CI BJ) (p : D.below CI → ExtOrd) (q : D.below BJ → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow F.base CI p) (hq : RespectsSemanticsBelow F.base BJ q)
    (hγ : SelfVis BJ.2 γ)
    (hag : ∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ out, RespectsSemanticsBelow F.base BJ out ∧
      (∀ d, min (out d) γ = min (q d) γ) ∧
      ∀ d, out (CellScheme.below.mono h d) = p d := by
  by_cases he : CI = BJ
  · subst BJ
    exact ⟨p, hp, fun d => (hag d).symm, fun _ => rfl⟩
  · exact hb CI BJ hCI hBJ h he p q γ hp hq hγ hag

private theorem below_eta (d : D.below BJ) (hd : GradedLe (D.cell d.1) BJ) :
    (⟨d.1, hd⟩ : D.below BJ) = d := Subtype.ext rfl

/-- Whole-scheme bountifulness follows from the old bountifulness. The
new grade is above the retained bound, while its scope is the whole carrier. -/
theorem bountiful (hk : 1 ≤ k) (hb : F.base.IsBountiful) : F.rows.IsBountiful := by
  classical
  intro CI BJ hCI hBJ hle _ p q γ hp hq hγ hag
  let i : GradedLe (cut CI k) CI := cut_le
  let j : GradedLe (cut BJ k) BJ := cut_le
  let ij : GradedLe (cut CI k) (cut BJ k) := cut_mono hle
  have hp1 := (F.old_respects_iff (min_le_right _ _)).mp (hp.mono i)
  have hq1 := (F.old_respects_iff (min_le_right _ _)).mp (hq.mono j)
  have hγJ : SelfVis BJ.2 γ := hγ
  obtain ⟨r, hr, hcap, hpres⟩ := F.base_lift hb (cut_mem hk hCI) (cut_mem hk hBJ) ij
    _ _ γ hp1 hq1 (hγJ.mono (min_le_left _ _))
      (fun d => hag (CellScheme.below.mono i d))
  let η : ExtOrd := if hi : GradedLe (D.cell F.high) CI then p ⟨F.high, hi⟩
    else if hj : GradedLe (D.cell F.high) BJ then min (q ⟨F.high, hj⟩) γ else ⊥
  let out := F.fill r η
  have ηvis : SelfVis (D.grade F.high) η := by
    dsimp only [η]
    split_ifs with hi hj
    · exact (hp.orderly ⟨F.high, hi⟩).symm
    · exact selfVis_min (hq.orderly ⟨F.high, hj⟩).symm (hγJ.mono hj.2)
    · exact selfVis_bot _
  have outcap (d : D.below BJ) : min (out d) γ = min (q d) γ := by
    by_cases hd : D.grade d.1 ≤ k
    · have ht := hcap ⟨d.1, d.2.1, le_min d.2.2 hd⟩
      simpa only [out, fill, hd, ↓reduceDIte, CellScheme.below.mono, below_eta] using ht
    · by_cases he : d.1 = F.high
      · rcases d with ⟨d, hdBJ⟩
        dsimp only at he
        subst d
        rw [show out ⟨F.high, hdBJ⟩ = η from F.fill_high hdBJ]
        dsimp only [η]
        by_cases hi : GradedLe (D.cell F.high) CI
        · rw [dite_eq_left hi]
          simpa only [CellScheme.below.mono, below_eta] using (hag ⟨F.high, hi⟩).symm
        · rw [dite_eq_right hi, dite_eq_left hdBJ]
          simp only [min_assoc, min_self]
      · simp only [out, F.fill_mute d hd he, F.mute_label hq d hd he]
  have outpres (d : D.below CI) : out (CellScheme.below.mono hle d) = p d := by
    by_cases hd : D.grade d.1 ≤ k
    · have ht := hpres ⟨d.1, d.2.1, le_min d.2.2 hd⟩
      simpa only [out, fill, hd, ↓reduceDIte, CellScheme.below.mono, below_eta] using ht
    · by_cases he : d.1 = F.high
      · rcases d with ⟨d, hdCI⟩
        dsimp only at he
        subst d
        change F.fill r η ⟨F.high, hdCI.trans hle⟩ = _
        rw [F.fill_high]
        exact dite_eq_left hdCI
      · simp only [out, fill, CellScheme.below.mono, hd, he, ↓reduceDIte, ↓reduceIte,
          F.mute_label hp d hd he]
  refine ⟨out, ?_, outcap, outpres⟩
  apply F.respects_of hr (fun d hd => F.fill_old d hd)
  · intro d
    by_cases hd : D.grade d.1 ≤ k
    · simpa only [fill, hd, ↓reduceDIte] using
        (hr.orderly ⟨d.1, d.2.1, le_min d.2.2 hd⟩).symm
    · by_cases he : d.1 = F.high
      · rcases d with ⟨d, hdBJ⟩
        dsimp only at he
        subst d
        simpa only [fill, not_le_of_gt F.above, ↓reduceDIte, ↓reduceIte] using ηvis
      · simpa only [fill, hd, he, ↓reduceDIte, ↓reduceIte] using selfVis_bot (D.grade d.1)
  · exact fun d hd he => F.fill_mute d hd he
  · rintro ⟨c, hcBJ⟩ he
    dsimp only at he
    subst c
    by_cases hi : GradedLe (D.cell F.high) CI
    · have read (e : D.below (D.cell F.high)) :
          out ⟨e.1, e.2.trans hcBJ⟩ = p ⟨e.1, e.2.trans hi⟩ := outpres ⟨e.1, e.2.trans hi⟩
      have readc : out ⟨F.high, hcBJ⟩ = p ⟨F.high, hi⟩ := outpres ⟨F.high, hi⟩
      convert hp.locality ⟨F.high, hi⟩ using 1
      funext e
      change min (out ⟨e.1, e.2.trans hcBJ⟩) (out ⟨F.high, hcBJ⟩) = _
      rw [read e, readc]
      rfl
    · have readc : out ⟨F.high, hcBJ⟩ = min (q ⟨F.high, hcBJ⟩) γ := by
        rw [show out ⟨F.high, hcBJ⟩ = η from F.fill_high hcBJ]
        simp only [η, dite_eq_right hi, dite_eq_left hcBJ]
      have ht := (hq.locality ⟨F.high, hcBJ⟩).cap (fun e => e.2.2) (hγJ.mono hcBJ.2)
      convert ht using 1
      funext e
      change min (out ⟨e.1, e.2.trans hcBJ⟩) (out ⟨F.high, hcBJ⟩) = _
      rw [readc]
      calc
        _ = min (min (out ⟨e.1, e.2.trans hcBJ⟩) γ) (q ⟨F.high, hcBJ⟩) := by ac_rfl
        _ = min (min (q ⟨e.1, e.2.trans hcBJ⟩) γ) (q ⟨F.high, hcBJ⟩) :=
          congrArg (fun x => min x (q ⟨F.high, hcBJ⟩)) (outcap ⟨e.1, e.2.trans hcBJ⟩)
        _ = _ := by dsimp only [CellScheme.below.incl]; ac_rfl

end VaughtConjecture.Knight.HighGradeExtension.Data
