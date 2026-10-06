/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorRetarget

/-! # LOW-only donor retargeting without reference-context geometry

This factors the donor surgery of `CappedDonorRetarget` through a lawful donor display,
on an arbitrary actual lower domain. No reference context or arity inequality is required.
The existing scalar shifter is reused; locality and availability are constructed on the
unchanged donor rows. Attribution: the corresponding proofs in `CappedDonorRetarget`.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref

variable {n : ℕ} {P : SemScheme n} {BJ : Finset (Fin n) × ℕ}
  {p : Cell P.scheme → ExtOrd} (hp : RespectsSemantics P.rows p)

include hp in
/-- Rounded non-top sources lie below top sources in the original lawful donor. -/
theorem srcP_nonTop_lt_top (o : P.scheme.below (BJ)) (ho : p o.1 = ⊤)
    (d t : P.scheme.below (P.scheme.cell o.1)) (hd : p d.1 ≠ ⊤) (ht : p t.1 = ⊤) :
    extVisibilityReplace (P.rows.E o.1 d) (P.scheme.grade o.1) (P.scheme.grade o.1) <
      P.rows.E o.1 t := by
  have hp := hp.toBelow (BJ)
  obtain ⟨τ, hτ, -, hread⟩ := exists_bounded_exact_capped_witness
    (grade := fun d : P.scheme.below (P.scheme.cell o.1) => P.scheme.grade d.1)
    (c := ⟨o.1, GradedLe.refl _⟩) (p := fun d => p d.1) (fun d => d.2.2)
    (hp.orderly o).symm (hp.locality o)
  have hd' : τ (P.rows.E o.1 d) = p d.1 := by
    rw [hread]
    change min (p d.1) (p o.1) = _
    rw [ho, min_top_right]
  have ht' : τ (P.rows.E o.1 t) = ⊤ := by
    rw [hread]
    change min (p t.1) (p o.1) = _
    rw [ho, ht, min_top_right]
  by_contra hle
  have h := hτ.mono (not_lt.mp hle)
  rw [ht', hτ.comm_gTop _ le_rfl, hd', top_le_iff] at h
  exact TopSupport.evr_ne_top hd _ _ h

/-! ## Uniform retargeting -/

open Classical in
/-- Replace every designated donor-top value by `η`, retain every other value. -/
noncomputable def retargetTops (η : ExtOrd) (u : P.scheme.below (BJ) → ExtOrd)
    (d : P.scheme.below (BJ)) : ExtOrd :=
  if p d.1 = ⊤ then η else u d

theorem retargetTops_of_top (η : ExtOrd) (u : P.scheme.below (BJ) → ExtOrd)
    {d : P.scheme.below (BJ)} (h : p d.1 = ⊤) : retargetTops (p := p) η u d = η := by
  unfold retargetTops; rw [ite_eq_left h]

theorem retargetTops_of_nonTop (η : ExtOrd) (u : P.scheme.below (BJ) → ExtOrd)
    {d : P.scheme.below (BJ)} (h : p d.1 ≠ ⊤) : retargetTops (p := p) η u d = u d := by
  unfold retargetTops; rw [ite_eq_right h]

section Retarget

variable {K : ℕ} {u : P.scheme.below (BJ) → ExtOrd}
  {b η : ExtOrd}

/-- The hypotheses of the retargeting lemma: a lawful section whose donor non-top values lie
strictly below a positive `K`-visible `b` and whose donor-top values are at least `b`, and a
`K`-visible target `η ≥ b`. -/
structure RetargetData (u : P.scheme.below (BJ) → ExtOrd) (b η : ExtOrd) : Prop where
  respects : RespectsSemanticsBelow P.rows (BJ) u
  b_vis : SelfVis K b
  b_pos : ⊥ < b
  nonTop_lt : ∀ d, p d.1 ≠ ⊤ → u d < b
  top_ge : ∀ d, p d.1 = ⊤ → b ≤ u d
  η_vis : SelfVis K η
  b_le_η : b ≤ η

variable (hu : RetargetData (p := p) (K := K) u b η)

include hu

theorem RetargetData.retargetTops_le (d : P.scheme.below (BJ)) :
    retargetTops (p := p) η u d ≤ η := by
  by_cases h : p d.1 = ⊤
  · rw [retargetTops_of_top η u h]
  · rw [retargetTops_of_nonTop η u h]; exact ((hu.nonTop_lt d h).le.trans hu.b_le_η)

theorem RetargetData.top_pos {d : P.scheme.below (BJ)} (h : p d.1 = ⊤) : ⊥ < u d :=
  hu.b_pos.trans_le (hu.top_ge d h)

/-- The rounded non-top sources below an owner. -/
noncomputable def RetargetData.srcMax (o : P.scheme.below (BJ)) : ExtOrd :=
  letI := Fintype.ofFinite (P.scheme.below (P.scheme.cell o.1))
  (Finset.univ.filter fun d : P.scheme.below (P.scheme.cell o.1) => p d.1 ≠ ⊤).sup
    fun d => extVisibilityReplace (P.rows.E o.1 d) (P.scheme.grade o.1) (P.scheme.grade o.1)

omit hu in
theorem RetargetData.srcMax_selfVis (o : P.scheme.below (BJ)) :
    SelfVis (P.scheme.grade o.1) (RetargetData.srcMax (p := p) o) :=
  TopSupport.selfVis_sup_evr _ _ _

omit hu in
theorem RetargetData.le_srcMax (o : P.scheme.below (BJ))
    {d : P.scheme.below (P.scheme.cell o.1)} (hd : p d.1 ≠ ⊤) :
    P.rows.E o.1 d ≤ RetargetData.srcMax (p := p) o := by
  let _ := Fintype.ofFinite (P.scheme.below (P.scheme.cell o.1))
  exact (TopSupport.le_evr_self _ _).trans (Finset.le_sup (f := fun d =>
    extVisibilityReplace (P.rows.E o.1 d) (P.scheme.grade o.1) (P.scheme.grade o.1))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩))

omit hu in
include hp in
/-- Every donor-top source below a donor-top owner exceeds the rounded non-top sources. -/
theorem RetargetData.srcMax_lt_top (o : P.scheme.below (BJ)) (ho : p o.1 = ⊤)
    {t : P.scheme.below (P.scheme.cell o.1)} (ht : p t.1 = ⊤) :
    RetargetData.srcMax (p := p) o < P.rows.E o.1 t := by
  let _ := Fintype.ofFinite (P.scheme.below (P.scheme.cell o.1))
  have hpos : ⊥ < P.rows.E o.1 t := by
    have hp := hp.toBelow (BJ)
    obtain ⟨τ, hτ, -, hread⟩ := exists_bounded_exact_capped_witness
      (grade := fun d : P.scheme.below (P.scheme.cell o.1) => P.scheme.grade d.1)
      (c := ⟨o.1, GradedLe.refl _⟩) (p := fun d => p d.1) (fun d => d.2.2)
      (hp.orderly o).symm (hp.locality o)
    have h := hread t
    change τ (P.rows.E o.1 t) = min (p t.1) (p o.1) at h
    rw [ht, ho, min_top_right] at h
    apply bot_lt_iff_ne_bot.mpr
    intro hbot
    rw [hbot, hτ.bot] at h
    exact bot_ne_top h
  unfold RetargetData.srcMax
  rw [Finset.sup_lt_iff hpos]
  intro d hd
  exact srcP_nonTop_lt_top hp o ho d t (Finset.mem_filter.mp hd).2 ht


include hp in
/-- **Uniform top retargeting is lawful** (audit16 §2, note §3.1). -/
theorem RetargetData.retargetTops_respects
    (htop : ∀ d, p d = ⊤ → P.scheme.grade d ≤ K) :
    RespectsSemanticsBelow P.rows (BJ) (retargetTops (p := p) η u) where
  orderly d := by
    by_cases h : p d.1 = ⊤
    · rw [retargetTops_of_top η u h]
      exact (hu.η_vis.mono ((htop d.1 h).trans_eq' rfl)).symm
    · rw [retargetTops_of_nonTop η u h]; exact hu.respects.orderly d
  locality o := by
    by_cases ho : p o.1 = ⊤
    · -- a donor-top owner: per-owner surgery on the exact witness
      obtain ⟨τ, hτ, -, hread⟩ := exists_bounded_exact_capped_witness
        (grade := fun d : P.scheme.below (P.scheme.cell o.1) => P.scheme.grade d.1)
        (c := ⟨o.1, GradedLe.refl _⟩) (p := fun d => u (CellScheme.below.incl o d))
        (fun d => d.2.2) (hu.respects.orderly o).symm (hu.respects.locality o)
      have hko : P.scheme.grade o.1 ≤ K := htop o.1 ho
      have hτa : τ (RetargetData.srcMax (p := p) o) ≤ b := by
        let _ := Fintype.ofFinite (P.scheme.below (P.scheme.cell o.1))
        unfold RetargetData.srcMax
        rw [Finset.apply_sup_eq_sup_comp τ (fun _ _ => hτ.mono.map_max) hτ.bot]
        refine Finset.sup_le fun d hd => ?_
        simp only [Function.comp_apply]
        rw [hτ.comm_gTop _ le_rfl, hread]
        change extVisibilityReplace (min (u (CellScheme.below.incl o d)) (u o)) _ _ ≤ b
        exact evr_le_of_le_selfVis hu.b_vis hko le_rfl ((min_le_left _ _).trans
          (hu.nonTop_lt _ (Finset.mem_filter.mp hd).2).le)
      have hw := retargetShifter_witness hτ (RetargetData.srcMax_selfVis (p := p) o) hτa
        hu.b_le_η (hu.η_vis.mono hko) (hu.b_pos.trans_le hu.b_le_η)
      refine hw.transformsTo fun d => ?_
      have hg : gTop (P.scheme.grade (⟨o.1, GradedLe.refl _⟩ :
          P.scheme.below (P.scheme.cell o.1)).1) (P.scheme.grade d.1) = ⊤ :=
        gTop_of_le d.2.2
      rw [hg, min_top_right, retargetTops_of_top η u ho]
      by_cases hd : p d.1 = ⊤
      · rw [retargetTops_of_top η u (d := CellScheme.below.incl o d) hd, min_self]
        have hne : τ (P.rows.E o.1 d) ≠ ⊥ := by
          rw [hread]
          change min (u (CellScheme.below.incl o d)) (u o) ≠ ⊥
          exact ne_bot_of_gt (lt_min (hu.top_pos hd) (hu.top_pos ho))
        rw [retargetShifter_of_lt hne (RetargetData.srcMax_lt_top (p := p) hp o ho hd)]
      · rw [retargetTops_of_nonTop η u (d := CellScheme.below.incl o d) hd,
          retargetShifter_of_le (RetargetData.le_srcMax (p := p) o hd), hread]
        change min (u (CellScheme.below.incl o d)) η = min (u (CellScheme.below.incl o d)) (u o)
        rw [min_eq_left ((hu.nonTop_lt _ hd).le.trans hu.b_le_η),
          min_eq_left ((hu.nonTop_lt _ hd).le.trans (hu.top_ge o ho))]
    · -- a donor non-top owner: the capped target is unchanged
      have key := hu.respects.locality o
      have heq : (fun d : P.scheme.below (P.scheme.cell o.1) =>
          min (retargetTops (p := p) η u (CellScheme.below.incl o d))
            (retargetTops (p := p) η u o)) =
          fun d => min (u (CellScheme.below.incl o d)) (u o) := by
        funext d
        rw [retargetTops_of_nonTop η u ho]
        by_cases hd : p d.1 = ⊤
        · rw [retargetTops_of_top η u (d := CellScheme.below.incl o d) hd,
            min_eq_right ((hu.nonTop_lt o ho).le.trans hu.b_le_η),
            min_eq_right ((hu.nonTop_lt o ho).le.trans (hu.top_ge _ hd))]
        · rw [retargetTops_of_nonTop η u (d := CellScheme.below.incl o d) hd]
      rw [heq]; exact key
  availability Sig Xi₀ hs hg := by
    by_cases hS : p Sig.1 = ⊤
    · obtain ⟨Xi, hcell, hle⟩ := (hp.toBelow (BJ)).availability Sig Xi₀ hs hg
      have hX : p Xi.1 = ⊤ := top_le_iff.mp (hS ▸ hle)
      refine ⟨Xi, hcell, ?_⟩
      rw [retargetTops_of_top η u hS, retargetTops_of_top η u hX]
    · obtain ⟨Xi, hcell, hle⟩ := hu.respects.availability Sig Xi₀ hs hg
      refine ⟨Xi, hcell, ?_⟩
      rw [retargetTops_of_nonTop η u hS]
      by_cases hX : p Xi.1 = ⊤
      · rw [retargetTops_of_top η u hX]
        exact (hu.nonTop_lt Sig hS).le.trans hu.b_le_η
      · rw [retargetTops_of_nonTop η u hX]; exact hle


end Retarget

end VaughtConjecture.Knight.LowOnly
