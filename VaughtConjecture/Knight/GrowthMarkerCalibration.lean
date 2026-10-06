/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthContextSynchronization

/-! # A least top source supplies the hollow-growth marker inequality

At a full-scope maximal-grade top owner, choose a top argument with least
source value. Any top argument whose provisional value is at least `α + L`
lies above the marker's replacement at offset `L`. This is a weak source
inequality, not strict separation. The proof handles provisionally capped
and band-valued arguments separately on their actual rows.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthMarkerCalibration
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan
noncomputable section

private theorem evr_offset_mono (x : ExtOrd) (N : ℕ) {i j : ℕ} (h : i ≤ j) :
    extVisibilityReplace x N i ≤ extVisibilityReplace x N j := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · simp
  · simp
  · by_cases ha : finitePart a < N
    · rw [extVisibilityReplace_of_finitePart_lt ha,
        extVisibilityReplace_of_finitePart_lt ha, ofOrd_le_ofOrd]
      exact add_le_add_right (Nat.cast_le.mpr h) _
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp ha),
        extVisibilityReplace_of_le_finitePart (not_lt.mp ha)]

variable {α : Ordinal.{0}} {n : ℕ} {p : S α n} {c : Cell p.scheme.scheme}

/-- The row inequality needed for a marker, from a least top source and a
provisional lower bound. No physical receiver is used. -/
theorem marker_le_of_provisional (hsc : p.scheme.scheme.scope c = Finset.univ)
    (hgr : p.scheme.scheme.grade c = p.topGrade) (hc : p.label c = ⊤)
    (r : p.scheme.scheme.below (p.scheme.scheme.cell c))
    (hmin : ∀ d : p.scheme.scheme.below (p.scheme.scheme.cell c), p.label d.1 = ⊤ →
      p.scheme.rows.E c r ≤ p.scheme.rows.E c d)
    (d : p.scheme.scheme.below (p.scheme.scheme.cell c)) (hd : p.label d.1 = ⊤)
    {L : ℕ} (hL : L ≤ p.topGrade) (hv : ofOrd (α + L) ≤ p.someProvisionalValue d.1) :
    extVisibilityReplace (p.scheme.rows.E c r) p.topGrade L ≤ p.scheme.rows.E c d := by
  by_cases hcap : p.ProvisionalCap d.1
  · obtain ⟨s, hs, hsd⟩ := hcap.transport d.2 hsc hgr hc
    exact ((evr_mono (hmin s hs) hL).trans
      (evr_offset_mono (p.scheme.rows.E c s) p.topGrade hL)).trans hsd
  · have hnotself : extVisibilityReplace (p.scheme.rows.E c d) p.topGrade p.topGrade ≠
        p.scheme.rows.E c d := fun h =>
      hcap ⟨c, d.2, d, hsc, hgr, hc, hd, h.le⟩
    obtain ⟨a, ha, hfp⟩ : ∃ a : Ordinal.{0}, p.scheme.rows.E c d = ofOrd a ∧
        finitePart a < p.topGrade := by
      rcases ExtOrd.cases (p.scheme.rows.E c d) with hb | ht | ⟨a, ha⟩
      · simp [hb] at hnotself
      · simp [ht] at hnotself
      · refine ⟨a, ha, ?_⟩
        by_contra hn
        exact hnotself (by rw [ha, extVisibilityReplace_of_le_finitePart (not_lt.mp hn)])
    have hband : p.ProvisionalBand d.1 (finitePart a) := by
      refine ⟨c, d.2, hsc, hgr, hc, ?_⟩
      change p.scheme.rows.E c d =
        extVisibilityReplace (p.scheme.rows.E c d) p.topGrade (finitePart a)
      rw [ha, extVisibilityReplace_of_finitePart_lt hfp, limitPart_add_finitePart]
    have hval : p.someProvisionalValue d.1 = ofOrd (α + finitePart a) :=
      (isProvisionalValue_iff.mp (Or.inr (Or.inr ⟨hd, hcap, finitePart a, hband, rfl⟩))).symm
    have hLf : L ≤ finitePart a := by
      rw [hval, ofOrd_le_ofOrd] at hv
      exact Nat.cast_le.mp (le_of_add_le_add_left hv)
    apply (evr_mono (hmin d hd) hL).trans
    rw [ha, extVisibilityReplace_of_finitePart_lt hfp, ofOrd_le_ofOrd]
    exact (add_le_add_right (Nat.cast_le.mpr hLf) _).trans_eq (limitPart_add_finitePart a)

/-- The marker is an actual top occurrence, chosen from a finite nonempty
set of arguments of the maximal top owner. -/
theorem exists_marker (hsc : p.scheme.scheme.scope c = Finset.univ)
    (hgr : p.scheme.scheme.grade c = p.topGrade) (hc : p.label c = ⊤) :
    ∃ r : p.scheme.scheme.below (p.scheme.scheme.cell c), p.label r.1 = ⊤ ∧
      ∀ (L : ℕ), L ≤ p.topGrade →
        ∀ d : p.scheme.scheme.below (p.scheme.scheme.cell c), p.label d.1 = ⊤ →
          ofOrd (α + L) ≤ p.someProvisionalValue d.1 →
            extVisibilityReplace (p.scheme.rows.E c r) p.topGrade L ≤ p.scheme.rows.E c d := by
  classical
  let : Fintype (p.scheme.scheme.below (p.scheme.scheme.cell c)) := Fintype.ofFinite _
  let T := Finset.univ.filter fun d : p.scheme.scheme.below (p.scheme.scheme.cell c) =>
    p.label d.1 = ⊤
  have hT : T.Nonempty := ⟨⟨c, GradedLe.refl _⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩
  obtain ⟨r, hr, hmin⟩ := T.exists_min_image (p.scheme.rows.E c) hT
  refine ⟨r, (Finset.mem_filter.mp hr).2, fun L hL d hd hv => ?_⟩
  exact marker_le_of_provisional hsc hgr hc r
    (fun s hs => hmin s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)) d hd hL hv

/-- An actual hollow-growth context with its marker and root source inequalities.
The top grade exceeds both requested floors. This constructs calibration data,
not the physical receiving scheme which would consume it. -/
theorem exists_hollow_marker_context {M : Type*} {α : LimitStage}
    {W : KnightRealization α M} (hM : W.IsModel) (hg : W.HasTopGradeGrowth)
    (hh : W.IsHollow) {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n)
    (hp : W.eval t = some p) (K L : ℕ) :
    ∃ (y : W.LabelledExt) (f : Fin n ↪ Fin y.arity) (_hf : f.trans y.tuple = t)
      (hpy : typeMap f y.type = some p) (c : Cell y.type.scheme.scheme)
      (r : y.type.scheme.scheme.below (y.type.scheme.scheme.cell c)),
      max K L < y.type.topGrade ∧ y.type.scheme.scheme.scope c = Finset.univ ∧
      y.type.scheme.scheme.grade c = y.type.topGrade ∧ y.type.label c = ⊤ ∧
      y.type.label r.1 = ⊤ ∧
      (∀ d, p.label d ≠ ⊤ → y.type.someProvisionalValue (mapCell hpy d) = p.label d) ∧
      (∀ d, p.label d = ⊤ →
        ∃ hd : GradedLe (y.type.scheme.scheme.cell (mapCell hpy d))
            (y.type.scheme.scheme.cell c),
          extVisibilityReplace (y.type.scheme.rows.E c r) y.type.topGrade L ≤
            y.type.scheme.rows.E c ⟨mapCell hpy d, hd⟩) := by
  obtain ⟨y, f, hf, hpy, c, hN, hsc, hgr, hc, hproper, htop⟩ :=
    GrowthContextSynchronization.exists_hollow_context hM hg hh t p hp (max K L) L
  obtain ⟨r, hr, hm⟩ := exists_marker hsc hgr hc
  refine ⟨y, f, hf, hpy, c, r, hN, hsc, hgr, hc, hr, hproper, fun d hd => ?_⟩
  have hdtop : y.type.label (mapCell hpy d) = ⊤ := by rw [label_mapCell hpy, hd]
  have hbelow : GradedLe (y.type.scheme.scheme.cell (mapCell hpy d))
      (y.type.scheme.scheme.cell c) := by
    constructor
    · change y.type.scheme.scheme.scope (mapCell hpy d) ⊆ y.type.scheme.scheme.scope c
      rw [hsc]
      exact Finset.subset_univ _
    · change y.type.scheme.scheme.grade (mapCell hpy d) ≤ y.type.scheme.scheme.grade c
      rw [hgr]
      exact le_csSup y.type.topGrades_bddAbove (grade_mem_topGrades hdtop)
  exact ⟨hbelow, hm L ((le_max_right K L).trans hN.le)
    ⟨mapCell hpy d, hbelow⟩ hdtop (htop d hd).le⟩

end
end VaughtConjecture.Knight.GrowthMarkerCalibration
