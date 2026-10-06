/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SeparatedGradeOneMute
public import VaughtConjecture.Knight.SourceCode

/-! # Producing separated source profiles by one common codebook

Grade-one coding of visible labels has exactly offset one at every nonbottom
value. Thus equality of block floors is equality of codes. This supplies the
separation hypothesis of the actual bountiful row construction, including
inputs with literal top. The selected uncoded labels themselves respect the
new rows by direct outgoing witnesses, not by faithful composition.

This is not a replacement for arbitrary inherited rows. The source profile
is shared by all grade-one rows, and every higher-grade row remains mute.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SeparatedGradeOne

open AmalgamationPlan Transform Value ExtOrd FullRowLifting

/-- The fixed offset-one source form. -/
noncomputable def band (n : ℕ) : ExtOrd := ofOrd (Ordinal.omega0 * n + (1 : ℕ))

theorem band_visible (n : ℕ) : SelfVis 1 (band n) := by
  rw [band, selfVis_ofOrd_iff]
  exact (finitePart_mul_add n 1).ge

theorem band_coded (n k : ℕ) : IsCodedLabel k (band n) :=
  Or.inr ⟨n, 1, by omega, rfl⟩

theorem band_mono {m n : ℕ} (h : m ≤ n) : band m ≤ band n := by
  apply ofOrd_le_ofOrd.mpr
  gcongr

theorem band_floor (n : ℕ) : blockFloor (band n) = ofOrd (Ordinal.omega0 * n) := by
  rw [band, blockFloor_ofOrd, limitPart_mul_add n 1]

theorem band_separated {m n : ℕ} (h : blockFloor (band m) = blockFloor (band n)) :
    band m = band n := by
  rw [band_floor, band_floor] at h
  have he : Ordinal.omega0 * m = Ordinal.omega0 * n := ofOrd_inj.mp h
  exact congrArg (fun a => ofOrd (a + (1 : ℕ))) he

/-- Shared grade-one coding puts every nonbottom source at offset exactly one. -/
theorem encode_shape (S : Finset Ordinal.{0}) {x : ExtOrd} (hx : SelfVis 1 x) :
    SourceCode.encode 1 S x = ⊥ ∨ ∃ n, SourceCode.encode 1 S x = band n := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨(keys 1 S).card + 1, rfl⟩
  · refine Or.inr ⟨blockOf 1 S v, ?_⟩
    change ofOrd (Ordinal.omega0 * blockOf 1 S v + (min (finitePart v) 1 : ℕ)) = _
    rw [min_eq_right (selfVis_ofOrd_iff.mp hx)]
    rfl

theorem encode_separated (S : Finset Ordinal.{0}) {x y : ExtOrd}
    (hx : SelfVis 1 x) (hy : SelfVis 1 y)
    (h : blockFloor (SourceCode.encode 1 S x) = blockFloor (SourceCode.encode 1 S y)) :
    SourceCode.encode 1 S x = SourceCode.encode 1 S y := by
  rcases encode_shape S hx with hx | ⟨m, hx⟩
  · rcases encode_shape S hy with hy | ⟨n, hy⟩
    · exact hx.trans hy.symm
    · rw [hx, hy, blockFloor_bot, band_floor] at h
      exact False.elim ((ofOrd_ne_bot _) h.symm)
  · rcases encode_shape S hy with hy | ⟨n, hy⟩
    · rw [hx, hy, band_floor, blockFloor_bot] at h
      exact False.elim ((ofOrd_ne_bot _) h)
    · rw [hx, hy] at h ⊢
      exact band_separated h

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- A numerical rank monotone along the grade-one scope inclusions produces
actual separated source data, independently of output labels. -/
noncomputable def ofRanks (rank : Cell D → ℕ)
    (hm : ∀ d e, D.scope d ⊆ D.scope e → D.grade d = 1 → D.grade e = 1 → rank d ≤ rank e) :
    Profile D where
  source d := band (rank d)
  visible _ := band_visible _
  separated _ _ h := band_separated h
  available d e hs hd he := band_mono (hm d e hs hd he)

/-- A common finite codebook constructs a profile from scope-monotone labels.
Supported values may include bottom and literal top. -/
noncomputable def ofLabels (S : Finset Ordinal.{0}) (p : Cell D → ExtOrd)
    (hv : ∀ d, SelfVis 1 (p d)) (hS : ∀ d, SourceCode.Supported S (p d))
    (hm : ∀ d e, D.scope d ⊆ D.scope e → D.grade d = 1 → D.grade e = 1 → p d ≤ p e) :
    Profile D where
  source d := SourceCode.encode 1 S (p d)
  visible d := SourceCode.encode_selfVis 1 S le_rfl (hv d)
  separated d e := encode_separated S (hv d) (hv e)
  available d e hs hd he := SourceCode.encode_le 1 S (hS d) (hS e) (hm d e hs hd he)

theorem ofLabels_coded (S : Finset Ordinal.{0}) (p : Cell D → ExtOrd)
    (hv : ∀ d, SelfVis 1 (p d)) (hS : ∀ d, SourceCode.Supported S (p d))
    (hm : ∀ d e, D.scope d ⊆ D.scope e → D.grade d = 1 → D.grade e = 1 → p d ≤ p e) :
    (ofLabels S p hv hS hm).rows.IsCoded := by
  intro c d
  by_cases hc : D.grade c = 1
  · rw [Profile.row_one _ hc, hc]
    exact SourceCode.encode_coded 1 S _
  · exact Or.inl (Profile.row_mute _ hc d)

/-- The original selected labels respect the newly constructed rows. The
outgoing witness is direct at each actual owner cap; top is recovered literally. -/
theorem ofLabels_respects (S : Finset Ordinal.{0}) (p : Cell D → ExtOrd)
    (hv : ∀ d, SelfVis 1 (p d)) (hS : ∀ d, SourceCode.Supported S (p d))
    (hm : ∀ d e, D.scope d ⊆ D.scope e → D.grade d = 1 → D.grade e = 1 → p d ≤ p e)
    (hMute : ∀ d, D.grade d ≠ 1 → p d = ⊥) :
    RespectsSemantics (ofLabels S p hv hS hm).rows p where
  orderly d := by
    by_cases hd : D.grade d = 1
    · simpa only [hd] using (hv d).symm
    · simp only [hMute d hd, extVisibilityReplace_bot]
  locality c := by
    by_cases hc : D.grade c = 1
    · have ht := SourceCode.outgoing (fun d : D.below (D.cell c) => D.grade d.1)
        (fun d => p d.1) 1 S (fun d => d.2.2.trans hc.le) (fun d => hS d.1) (hv c)
      simpa only [Profile.rows, hc, ↓reduceIte, ofLabels] using ht
    · simpa only [hMute c hc, min_bot_right] using
        (TransformsTo.to_bot (grade := fun d : D.below (D.cell c) => D.grade d.1)
          ((ofLabels S p hv hS hm).rows.E c))
  availability d e hs hg := by
    refine ⟨e, rfl, ?_⟩
    by_cases hd : D.grade d = 1
    · exact hm d e hs hd (hg.symm.trans hd)
    · rw [hMute d hd]
      exact bot_le

/-- The structural construction supplies a genuine legal domain when the
given carrier is complete and index-injective. -/
noncomputable def domain {n : ℕ} {D : CellScheme (ι := Fin n) Finset.univ}
    (hinj : Function.Injective D.cell) (hcomplete : D.IsComplete)
    (p : Cell D → ExtOrd) (hv : ∀ d, SelfVis 1 (p d))
    (hm : ∀ d e, D.scope d ⊆ D.scope e → D.grade d = 1 → D.grade e = 1 → p d ≤ p e) :
    SemScheme n where
  scheme := D
  rows := (ofLabels (primRange p) p hv (SourceCode.supported_primRange p) hm).rows
  rows_coded := ofLabels_coded _ _ _ _ _
  consistent := Profile.consistent _
  bountiful := Profile.bountiful _ hinj hcomplete
  complete := hcomplete

end VaughtConjecture.Knight.SeparatedGradeOne
