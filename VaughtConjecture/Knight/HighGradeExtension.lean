/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceCode
public import VaughtConjecture.Knight.Domain

/-! # A full-scope row above an arbitrary retained grade bound

Rows through grade `k` are retained literally. One full-scope cell of a
strictly higher grade receives a lawful source profile on the retained
part and a visible diagonal; every other higher row is mute. The retained
semantics may already contain non-mute higher-grade controllers.

The construction changes rows on an existing carrier. It neither adds a
point nor supplies the missing proper mixed scopes of a point extension.
-/

@[expose] public section

namespace VaughtConjecture.Knight.HighGradeExtension

open AmalgamationPlan Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}

structure Data (D : CellScheme A) (k : ℕ) where
  base : Semantics D
  high : Cell D
  above : k < D.grade high
  full : D.scope high = A
  profile : D.below (A, k) → ExtOrd
  lawful : RespectsSemanticsBelow base (A, k) profile
  diagonal : ExtOrd
  visible : SelfVis (D.grade high) diagonal

namespace Data

variable (F : Data D k) {BJ : Finset ι × ℕ}

def oldCell (d : Cell D) (hd : D.grade d ≤ k) : D.below (A, k) :=
  ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩

def display (d : Cell D) : ExtOrd :=
  if hd : D.grade d ≤ k then F.profile (oldCell d hd) else
    if d = F.high then F.diagonal else ⊥

theorem display_old (d : Cell D) (hd : D.grade d ≤ k) :
    F.display d = F.profile (oldCell d hd) := by simp only [display, hd, ↓reduceDIte]

theorem display_high : F.display F.high = F.diagonal := by
  simp only [display, not_le_of_gt F.above, ↓reduceDIte, ↓reduceIte]

theorem display_other (d : Cell D) (hd : ¬D.grade d ≤ k) (hne : d ≠ F.high) :
    F.display d = ⊥ := by simp only [display, hd, hne, ↓reduceDIte, ↓reduceIte]

theorem display_visible (d : Cell D) : SelfVis (D.grade d) (F.display d) := by
  by_cases hd : D.grade d ≤ k
  · rw [F.display_old d hd]
    exact (F.lawful.orderly _).symm
  · by_cases he : d = F.high
    · subst d
      rw [F.display_high]
      exact F.visible
    · rw [F.display_other d hd he]
      exact selfVis_bot _

def rows : Semantics D where
  E c d := if D.grade c ≤ k then F.base.E c d else
    if c = F.high then F.display d.1 else ⊥
  orderly c d := by
    split_ifs with hc he
    · exact F.base.orderly c d
    · exact (F.display_visible d.1).symm
    · exact (selfVis_bot _).symm

theorem row_old {c : Cell D} (hc : D.grade c ≤ k) : F.rows.E c = F.base.E c := by
  funext d
  simp only [rows, hc, ↓reduceIte]

theorem row_high (d : D.below (D.cell F.high)) : F.rows.E F.high d = F.display d.1 := by
  simp only [rows, not_le_of_gt F.above, ↓reduceIte]

theorem rows_high : F.rows.E F.high = fun d => F.display d.1 := funext F.row_high

theorem row_mute {c : Cell D} (hc : ¬D.grade c ≤ k) (he : c ≠ F.high)
    (d : D.below (D.cell c)) : F.rows.E c d = ⊥ := by
  simp only [rows, hc, he, ↓reduceIte]

theorem old_respects_iff (hJ : BJ.2 ≤ k) {p : D.below BJ → ExtOrd} :
    RespectsSemanticsBelow F.rows BJ p ↔ RespectsSemanticsBelow F.base BJ p := by
  constructor <;> intro hp <;> refine ⟨hp.orderly, ?_, hp.availability⟩
  · intro c
    simpa only [F.row_old (c.2.2.trans hJ)] using hp.locality c
  · intro c
    rw [F.row_old (c.2.2.trans hJ)]
    exact hp.locality c

theorem high_index {e : Cell D} (hs : D.scope F.high ⊆ D.scope e)
    (hg : D.grade F.high = D.grade e) : D.cell F.high = D.cell e := by
  apply Prod.ext
  · apply Finset.Subset.antisymm hs
    rw [F.full]
    exact D.isPlan.subset_of_mem (D.scope_mem_plan e)
  · exact hg

/-- Every locality and availability of the constructed rows follows from
old consistency and the lawful old profile, including its higher grades. -/
theorem consistent (hb : F.base.IsConsistent) : F.rows.IsConsistent := by
  intro c
  by_cases hc : D.grade c ≤ k
  · apply (F.old_respects_iff hc).mpr
    simpa only [F.row_old hc] using hb c
  refine ⟨F.rows.orderly c, ?_, ?_⟩
  · intro d
    by_cases he : c = F.high
    · subst c
      by_cases hd : D.grade d.1 ≤ k
      · have ht := F.lawful.locality (oldCell d.1 hd)
        have hlow (e : D.below (D.cell d.1)) : D.grade e.1 ≤ k := e.2.2.trans hd
        simpa only [F.row_old hd, F.rows_high, F.display_old d.1 hd,
          F.display_old _ (hlow _),
          CellScheme.below.incl, oldCell] using ht
      · by_cases hdhi : d.1 = F.high
        · rcases d with ⟨d, hdle⟩
          dsimp only at hdhi
          subst d
          have ht := (TransformsTo.refl
            (grade := fun e : D.below (D.cell F.high) => D.grade e.1)
            (F.rows.E F.high)).cap (fun e => e.2.2) F.visible
          simpa only [F.rows_high, F.display_high, CellScheme.below.incl] using ht
        · simpa only [F.rows_high, F.display_other d.1 hd hdhi, min_bot_right] using
            (TransformsTo.to_bot (grade := fun e : D.below (D.cell d.1) => D.grade e.1)
              (F.rows.E d.1))
    · simpa only [rows, hc, he, ↓reduceIte, min_bot_right] using
        (TransformsTo.to_bot (grade := fun e : D.below (D.cell d.1) => D.grade e.1)
          (F.rows.E d.1))
  · intro d e hs hg
    by_cases he : c = F.high
    · subst c
      by_cases hd : D.grade d.1 ≤ k
      · have he : D.grade e.1 ≤ k := hg ▸ hd
        obtain ⟨f, hf, hv⟩ := F.lawful.availability
          (oldCell d.1 hd) (oldCell e.1 he) hs hg
        have hfb : GradedLe (D.cell f.1) (D.cell F.high) := by rw [hf]; exact e.2
        refine ⟨⟨f.1, hfb⟩, hf, ?_⟩
        simpa only [F.rows_high, F.display_old d.1 hd, F.display_old f.1 f.2.2,
          show oldCell f.1 f.2.2 = f from Subtype.ext rfl] using hv
      · by_cases hdhi : d.1 = F.high
        · refine ⟨d, ?_, le_rfl⟩
          rw [hdhi]
          exact F.high_index (by simpa only [hdhi] using hs) (by simpa only [hdhi] using hg)
        · refine ⟨e, rfl, ?_⟩
          rw [F.row_high, F.display_other d.1 hd hdhi]
          exact bot_le
    · exact ⟨e, rfl, by simp only [F.row_mute hc he, le_refl]⟩

theorem mute_label {p : D.below BJ → ExtOrd}
    (hp : RespectsSemanticsBelow F.rows BJ p) (c : D.below BJ)
    (hc : ¬D.grade c.1 ≤ k) (hne : c.1 ≠ F.high) : p c = ⊥ := by
  rcases c with ⟨c, hcBJ⟩
  obtain ⟨g, σ, _, _, hbot, _, _, he⟩ := hp.locality ⟨c, hcBJ⟩
  have hh := he ⟨c, GradedLe.refl _⟩
  change min (p ⟨c, hcBJ⟩) (p ⟨c, hcBJ⟩) =
    min (σ (F.rows.E c ⟨c, GradedLe.refl _⟩)) (g (D.grade c)) at hh
  simpa only [rows, hc, hne, ↓reduceIte, hbot, min_bot_left, min_self] using hh

end Data

end VaughtConjecture.Knight.HighGradeExtension
