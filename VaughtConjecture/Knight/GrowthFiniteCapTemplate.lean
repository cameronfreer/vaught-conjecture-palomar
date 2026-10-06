/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFiniteCapEncoding

/-! # A constructed donor template below a finite marker reading

The native source and chart come from the actual private row. The shorter
encoding, its root alignment, lawful encoded donor and literal restoration
are constructed here. The donor's own bountifulness is the only lifting
input. In particular, the encoding grade is not the marker offset.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthFiniteCapTemplate
open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition
noncomputable section
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}

/-- Construct a lawful donor template from the finite-cap chart and its
actual block-reference readings. Neither an encoding nor root source
alignment nor a replacement donor is an input. -/
theorem exists_template (req : Requests DA DQ)
    (e : DA.below (DA.cell req.C) → ExtOrd)
    (he : RespectsSemanticsBelow semA (DA.cell req.C) e)
    (heproper : ∀ d, e d ≠ ⊤)
    (w : Cell DA → ExtOrd) (hebot : ∀ d, e d = ⊥ ↔ w d.1 = ⊥)
    {τ : ExtOrd → ExtOrd} (hτ : BoundedMap req.N τ)
    (hchart : ∀ d, τ (e d) = min (w d.1) (w req.C))
    {α : Ordinal.{0}} (hα : limitPart α = α) {i : ℕ} (hi : i < req.N)
    (ha : w req.a.1 = ofOrd (α + i))
    (hai : ofOrd (α + i) < w req.C)
    (hcut : ofOrd (α + req.R) < w req.C)
    (S : Finset Ordinal.{0}) (hS : ∀ μ ∈ S, limitPart μ = μ)
    (hle : ∀ μ ∈ S, μ ≤ α)
    (ref : Ordinal.{0} → DA.below (DA.cell req.C))
    (off : Ordinal.{0} → ℕ) (hoff : ∀ μ ∈ S, off μ < req.N)
    (href : ∀ μ ∈ S, τ (e (ref μ)) = ofOrd (μ + off μ))
    {P : Cell DQ → ExtOrd} (hP : RespectsSemantics semQ P)
    (hblocks : ∀ d p, P d = ofOrd p → limitPart p ∈ S ∧ finitePart p < req.R)
    (hproper : ∀ d, P d ≠ ⊤ → P d < ofOrd (α + req.R))
    {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_lt_R : top.2 < req.R)
    (κ : DQ.below root → DA.below (DA.cell req.C))
    (hroot : ∀ s : DA.below (DA.cell req.C) → ExtOrd,
      RespectsSemanticsBelow semA (DA.cell req.C) s →
        RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful) (hlit : ∀ d, P d.1 = w (κ d).1)
    (hZ : ∀ z ∈ req.Z, P z = ⊥) (hT : ∀ y ∈ req.T, P y = ⊤)
    (hF : ∀ f ∈ req.F, ∃ p, P f = ofOrd p ∧ req.ρ f = ref (limitPart p) ∧
      req.off f = finitePart p) :
    ∃ V : Cell DQ → ExtOrd, RespectsSemantics semQ V ∧ (∀ d, V d.1 = e (κ d)) ∧
      req.Correct e V ∧ (req.T.Nonempty → ∀ f ∈ req.F, req.tOf e f ≤ req.dOf e) ∧
      (∀ f ∈ req.F, V f = extVisibilityReplace (e (req.ρ f)) req.N (req.off f)) ∧
      (∀ y ∈ req.T, extVisibilityReplace (e req.a) req.N req.R ≤ V y) ∧
      ∀ z ∈ req.Z, V z = ⊥ := by
  classical
  have hma : τ (e req.a) = ofOrd (α + i) := by
    rw [hchart, ha, min_eq_left hai.le]
  have hanb : e req.a ≠ ⊥ := by
    intro hb
    rw [hb, hτ.bot] at hma
    exact ofOrd_ne_bot _ hma.symm
  let sa := ordOf (e req.a)
  have hsa : e req.a = ofOrd sa := (ofOrd_ordOf hanb (heproper _)).symm
  have hmar : τ (ofOrd sa) = ofOrd (α + i) := hsa ▸ hma
  let src := fun μ => ordOf (e (ref μ))
  have hsrc (μ) (hμ : μ ∈ S) : e (ref μ) = ofOrd (src μ) := by
    apply (ofOrd_ordOf ?_ (heproper _)).symm
    intro hb
    have hr := href μ hμ
    rw [hb, hτ.bot] at hr
    exact ofOrd_ne_bot _ hr.symm
  have hread (μ) (hμ : μ ∈ S) : τ (ofOrd (src μ)) = ofOrd (μ + off μ) := by
    rw [← hsrc μ hμ, href μ hμ]
  let B := GrowthFiniteCapEncoding.code hτ hα hmar hi top_lt_R S hS hle src off hoff hread
  let height := ofOrd (limitPart sa + req.R)
  have hBtop : B.code ⊤ = height := rfl
  have hcode {p : Ordinal.{0}} (hp : limitPart p ∈ S) (hfp : finitePart p ≤ req.R) :
      B.code (ofOrd p) = ofOrd (limitPart (src (limitPart p)) + finitePart p) :=
    GrowthFiniteCapEncoding.code_listed hτ hα hmar hi top_lt_R S hS hle src off hoff hread hp hfp
  have hfs : finitePart sa < req.N := (read_finitePart hτ hmar (by
    rw [finitePart_add_nat_of_limit hα]; exact hi)).1
  have hheight : extVisibilityReplace (e req.a) req.N req.R = height := by
    rw [hsa, extVisibilityReplace_of_finitePart_lt hfs]
  have hheight_read : τ height = ofOrd (α + req.R) :=
    GrowthFiniteCapEncoding.marker_read hτ hα hmar hi req.R_lt_N
  have hbotP (d) : B.code (P d) = ⊥ → P d = ⊥ := by
    intro hb
    rcases ExtOrd.cases (P d) with hb' | ht | ⟨p, hp⟩
    · exact hb'
    · rw [ht, hBtop] at hb; exact (ofOrd_ne_bot _ hb).elim
    · obtain ⟨hs, ho⟩ := hblocks d p hp
      rw [hp, hcode hs ho.le] at hb
      exact (ofOrd_ne_bot _ hb).elim
  have hrootcap (d : DQ.below root) : min (B.code (P d.1)) height = min (e (κ d)) height := by
    rcases ExtOrd.cases (P d.1) with hb | ht | ⟨p, hp⟩
    · rw [hb, B.code_bot, (hebot _).mpr ((hlit d).symm.trans hb)]
    · rw [ht, hBtop, min_self]
      have hr := hchart (κ d)
      rw [← hlit, ht, min_top_left] at hr
      have hh : height ≤ e (κ d) := by
        by_contra hn
        have hm := hτ.mono (not_le.mp hn).le
        rw [hr, hheight_read] at hm
        exact (not_le_of_gt hcut) hm
      exact (min_eq_right hh).symm
    · obtain ⟨hs, ho⟩ := hblocks d.1 p hp
      have hb : e (κ d) ≠ ⊥ := by
        intro hz
        exact ofOrd_ne_bot p ((hp.symm.trans (hlit d)).trans ((hebot _).mp hz))
      have heq : e (κ d) = ofOrd (ordOf (e (κ d))) := (ofOrd_ordOf hb (heproper _)).symm
      have hr : τ (ofOrd (ordOf (e (κ d)))) = ofOrd p := by
        rw [← heq, hchart, ← hlit,
          min_eq_left ((hproper d.1 (hp ▸ ofOrd_ne_top p)).trans hcut).le, hp]
      have hal := GrowthFiniteCapEncoding.code_of_read hτ hα hmar hi req.R_lt_N
        top_lt_R S hS hle src off hoff hread hs ho hr
      rw [hp, hal, ← heq]
  have hFenc (d) (hd : d ∈ req.F) :
      B.code (P d) = extVisibilityReplace (e (req.ρ d)) req.N (req.off d) := by
    obtain ⟨p, hp, hρ, ho⟩ := hF d hd
    obtain ⟨hs, hfp⟩ := hblocks d p hp
    have hfr := (read_finitePart hτ (hread _ hs) (by
      rw [finitePart_limitPart_add_nat]; exact hoff _ hs)).1
    rw [hp, hcode hs hfp.le, hρ, ho, hsrc _ hs, extVisibilityReplace_of_finitePart_lt hfr]
  have hFlt (d) (hd : d ∈ req.F) :
      extVisibilityReplace (e (req.ρ d)) req.N (req.off d) < height := by
    obtain ⟨p, hp, _, _⟩ := hF d hd
    obtain ⟨hs, hfp⟩ := hblocks d p hp
    rw [← hFenc d hd, hp, hcode hs hfp.le]
    exact ofOrd_lt_ofOrd.mpr ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hfp) |>.trans_le
      (add_le_add_left (GrowthFiniteCapEncoding.strip_le hτ hα hmar hi S hS hle src off
        hoff hread _ hs) _))
  have hvis : SelfVis top.2 (extVisibilityReplace (e req.a) req.N req.R) := by
    rw [hheight]
    exact extVisibilityReplace_of_le_finitePart
      (by rw [finitePart_limitPart_add_nat]; exact top_lt_R.le) _
  exact template_of_encoding_at_grade req e he hanb hP root_mem top_mem root_le root_ne
    below_top κ hroot bountiful B.boundedMap_code hbotP hvis
    (by simpa only [hheight] using hrootcap) hZ hFenc
    (by simpa only [hheight] using hFlt)
    (fun y hy => (congrArg B.code (hT y hy)).trans (hBtop.trans hheight.symm))

end
end VaughtConjecture.Knight.GrowthFiniteCapTemplate
