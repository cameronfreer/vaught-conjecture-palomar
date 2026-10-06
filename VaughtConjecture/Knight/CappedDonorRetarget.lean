/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowRef

/-! # Uniform top retargeting and exact old-face restoration (audit16 §2, note §3.1)

The first of the two original-row operations of the two-threshold family: on the **unchanged
request scheme `P`**, using only its original rows and the original donor.

**Vertical gluing** (`RespectsSemanticsBelow.glue`): a lawful section on a lower grade set and a
lawful section on the full set with the same scope glue to a lawful section when, at every owner
above the lower grade, the lower section reads like the full one below the owner's own value.

**Uniform retargeting** (`retargetTops`, `retargetTops_respects`): let `u` be lawful at a cutoff
`j ≥ K`,
let `b` be positive and `K`-visible with every donor non-top value strictly below `b` and every
donor-top value at least `b`, and let `η ≥ b` be `K`-visible.  Replacing every designated
donor-top value by `η` and retaining every other value is lawful.  At a donor non-top owner the
capped target is unchanged.  At a donor-top owner `o` (grade `k ≤ K`) the original donor gives
`R_k(E_o d) < E_o t` between donor non-top and donor-top sources (`srcP_nonTop_lt_top`, from
the donor's exact witness at `o`); with `a_o` the maximum of the rounded non-top sources, the
new shifter is the exact normalized witness of `u` at `o` below `a_o`, constantly `η` above, and
bottom wherever the old witness is bottom — monotone, replacement-compatible through `k`, and
bottom-closed above `k` (`retargetShifter_witness`).  Availability uses the donor's witnesses at
designated tops and `u`'s witnesses elsewhere.  This is per-owner surgery, not one scalar
function of the values.

**Exact old-face restoration, arbitrary root** (`exists_retarget_restore`; newapproach2 §4):
given further a lawful private section whose present face values agree with `u` at every donor
non-top face cell and are at least `η` at every donor-top face cell, there is a lawful section
at the cutoff with the whole present face literally that section's, every donor non-top value
literally `u`'s, and every donor-top value at least `η`: restore only the **grade-`≤ K` part of
the face** inside the retargeted section through the effective grade `min K (arity P)` by old
`P`-bountifulness at cap `η`, then attach the unchanged higher-grade values by gluing — every
higher owner is donor non-top and lies below `b ≤ η`, so its whole locality target is unchanged.
The higher-grade face cells are donor non-top, so their prescribed values are `u`'s and the
gluing restores them too.  No bound `KA ≤ K` on the root arity is needed; an empty low part
needs no extension call.  The cap `η` is used as a bountifulness cap only through `K`, never at
a higher grade. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

/-! ## Vertical gluing -/

section Glue

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

open Classical in
/-- The glued section: the lower section on the lower set, the full section above. -/
noncomputable def glueSection {CI BJ : Finset ι × ℕ} (w : D.below CI → ExtOrd)
    (q : D.below BJ → ExtOrd) (d : D.below BJ) : ExtOrd :=
  if hd : GradedLe (D.cell d.1) CI then w ⟨d.1, hd⟩ else q d

theorem glueSection_of_le {CI BJ : Finset ι × ℕ} (w : D.below CI → ExtOrd)
    (q : D.below BJ → ExtOrd) {d : D.below BJ} (hd : GradedLe (D.cell d.1) CI) :
    glueSection w q d = w ⟨d.1, hd⟩ := by
  unfold glueSection; rw [dite_eq_left hd]

theorem glueSection_of_not_le {CI BJ : Finset ι × ℕ} (w : D.below CI → ExtOrd)
    (q : D.below BJ → ExtOrd) {d : D.below BJ} (hd : ¬ GradedLe (D.cell d.1) CI) :
    glueSection w q d = q d := by
  unfold glueSection; rw [dite_eq_right hd]

/-- **Vertical gluing**: with `CI` of the same scope as `BJ` and lower grade, a lawful section
`w` on `CI` and a lawful section `q` on `BJ` glue to a lawful section on `BJ` provided that, at
every owner `Sig` of `BJ` above `CI`, `w` reads like `q` below `Sig` capped at `q Sig`. -/
theorem RespectsSemanticsBelow.glue {CI BJ : Finset ι × ℕ} (h : GradedLe CI BJ)
    (hscope : CI.1 = BJ.1) {q : D.below BJ → ExtOrd} (hq : RespectsSemanticsBelow sem BJ q)
    {w : D.below CI → ExtOrd} (hw : RespectsSemanticsBelow sem CI w)
    (hcompat : ∀ Sig : D.below BJ, ¬ GradedLe (D.cell Sig.1) CI →
      ∀ (d : D.below (D.cell Sig.1)) (hd : GradedLe (D.cell d.1) CI),
        min (w ⟨d.1, hd⟩) (q Sig) = min (q (CellScheme.below.incl Sig d)) (q Sig)) :
    RespectsSemanticsBelow sem BJ (glueSection w q) where
  orderly d := by
    by_cases hd : GradedLe (D.cell d.1) CI
    · rw [glueSection_of_le w q hd]; exact hw.orderly ⟨d.1, hd⟩
    · rw [glueSection_of_not_le w q hd]; exact hq.orderly d
  locality Sig := by
    by_cases hS : GradedLe (D.cell Sig.1) CI
    · have key := hw.locality ⟨Sig.1, hS⟩
      have heq : (fun d : D.below (D.cell Sig.1) =>
          min (glueSection w q (CellScheme.below.incl Sig d)) (glueSection w q Sig)) =
          fun d => min (w (CellScheme.below.incl ⟨Sig.1, hS⟩ d)) (w ⟨Sig.1, hS⟩) := by
        funext d
        rw [glueSection_of_le w q hS, glueSection_of_le w q (d.2.trans hS)]
        rfl
      rw [heq]; exact key
    · have key := hq.locality Sig
      have heq : (fun d : D.below (D.cell Sig.1) =>
          min (glueSection w q (CellScheme.below.incl Sig d)) (glueSection w q Sig)) =
          fun d => min (q (CellScheme.below.incl Sig d)) (q Sig) := by
        funext d
        rw [glueSection_of_not_le w q hS]
        by_cases hd : GradedLe (D.cell d.1) CI
        · rw [glueSection_of_le w q (d := CellScheme.below.incl Sig d) hd]
          exact hcompat Sig hS d hd
        · rw [glueSection_of_not_le w q (d := CellScheme.below.incl Sig d) hd]
      rw [heq]; exact key
  availability Sig Xi₀ hs hg := by
    by_cases hS : GradedLe (D.cell Sig.1) CI
    · have hX : GradedLe (D.cell Xi₀.1) CI :=
        ⟨by rw [hscope]; exact Xi₀.2.1, by
          change D.grade Xi₀.1 ≤ CI.2
          rw [← hg]; exact hS.2⟩
      obtain ⟨Xi, hcell, hle⟩ := hw.availability ⟨Sig.1, hS⟩ ⟨Xi₀.1, hX⟩ hs hg
      refine ⟨⟨Xi.1, Xi.2.trans h⟩, hcell, ?_⟩
      rw [glueSection_of_le w q hS, glueSection_of_le w q (d := ⟨Xi.1, Xi.2.trans h⟩) Xi.2]
      exact hle
    · obtain ⟨Xi, hcell, hle⟩ := hq.availability Sig Xi₀ hs hg
      have hX : ¬ GradedLe (D.cell Xi.1) CI := by
        intro hX
        apply hS
        refine ⟨by rw [hscope]; exact Sig.2.1, ?_⟩
        have h1 : D.grade Xi.1 = D.grade Xi₀.1 := congrArg Prod.snd hcell
        change D.grade Sig.1 ≤ CI.2
        rw [hg, ← h1]; exact hX.2
      refine ⟨Xi, hcell, ?_⟩
      rw [glueSection_of_not_le w q hS, glueSection_of_not_le w q hX]
      exact hle

end Glue

namespace CappedDonor

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-! ## The donor's source separation at a donor-top owner -/

/-- At a donor-top owner, the original donor separates the sources: every donor non-top source
rounded at the owner's grade lies strictly below every donor-top source. -/
theorem srcP_nonTop_lt_top {j : ℕ} (o : P.scheme.below (effP nP j)) (ho : R.p o.1 = ⊤)
    (d t : P.scheme.below (P.scheme.cell o.1)) (hd : R.p d.1 ≠ ⊤) (ht : R.p t.1 = ⊤) :
    extVisibilityReplace (P.rows.E o.1 d) (P.scheme.grade o.1) (P.scheme.grade o.1) <
      P.rows.E o.1 t := by
  have hp := R.p_respects.toBelow (effP nP j)
  obtain ⟨τ, hτ, -, hread⟩ := exists_bounded_exact_capped_witness
    (grade := fun d : P.scheme.below (P.scheme.cell o.1) => P.scheme.grade d.1)
    (c := ⟨o.1, GradedLe.refl _⟩) (p := fun d => R.p d.1) (fun d => d.2.2)
    (hp.orderly o).symm (hp.locality o)
  have hd' : τ (P.rows.E o.1 d) = R.p d.1 := by
    rw [hread]
    change min (R.p d.1) (R.p o.1) = _
    rw [ho, min_top_right]
  have ht' : τ (P.rows.E o.1 t) = ⊤ := by
    rw [hread]
    change min (R.p t.1) (R.p o.1) = _
    rw [ho, ht, min_top_right]
  by_contra hle
  have h := hτ.mono (not_lt.mp hle)
  rw [ht', hτ.comm_gTop _ le_rfl, hd', top_le_iff] at h
  exact TopSupport.evr_ne_top hd _ _ h

/-! ## Uniform retargeting -/

open Classical in
/-- Replace every designated donor-top value by `η`, retain every other value. -/
noncomputable def retargetTops {j : ℕ} (η : ExtOrd) (u : P.scheme.below (effP nP j) → ExtOrd)
    (d : P.scheme.below (effP nP j)) : ExtOrd :=
  if R.p d.1 = ⊤ then η else u d

theorem retargetTops_of_top {j : ℕ} (η : ExtOrd) (u : P.scheme.below (effP nP j) → ExtOrd)
    {d : P.scheme.below (effP nP j)} (h : R.p d.1 = ⊤) : retargetTops (R := R) η u d = η := by
  unfold retargetTops; rw [ite_eq_left h]

theorem retargetTops_of_nonTop {j : ℕ} (η : ExtOrd) (u : P.scheme.below (effP nP j) → ExtOrd)
    {d : P.scheme.below (effP nP j)} (h : R.p d.1 ≠ ⊤) : retargetTops (R := R) η u d = u d := by
  unfold retargetTops; rw [ite_eq_right h]

section Retarget

variable {K : ℕ} (L : R.LowRef K) {j : ℕ} {u : P.scheme.below (effP nP j) → ExtOrd}
  {b η : ExtOrd}

/-- The hypotheses of the retargeting lemma: a lawful section whose donor non-top values lie
strictly below a positive `K`-visible `b` and whose donor-top values are at least `b`, and a
`K`-visible target `η ≥ b`. -/
structure RetargetData (u : P.scheme.below (effP nP j) → ExtOrd) (b η : ExtOrd) : Prop where
  respects : RespectsSemanticsBelow P.rows (effP nP j) u
  b_vis : SelfVis K b
  b_pos : ⊥ < b
  nonTop_lt : ∀ d, R.p d.1 ≠ ⊤ → u d < b
  top_ge : ∀ d, R.p d.1 = ⊤ → b ≤ u d
  η_vis : SelfVis K η
  b_le_η : b ≤ η

variable (hj : K ≤ j) (hu : RetargetData (R := R) (K := K) u b η)

include L hj hu

omit L hj in
theorem RetargetData.retargetTops_le (d : P.scheme.below (effP nP j)) :
    retargetTops (R := R) η u d ≤ η := by
  by_cases h : R.p d.1 = ⊤
  · rw [retargetTops_of_top η u h]
  · rw [retargetTops_of_nonTop η u h]; exact ((hu.nonTop_lt d h).le.trans hu.b_le_η)

omit L hj in
theorem RetargetData.top_pos {d : P.scheme.below (effP nP j)} (h : R.p d.1 = ⊤) : ⊥ < u d :=
  hu.b_pos.trans_le (hu.top_ge d h)

omit hj in
/-- The rounded non-top sources below an owner. -/
noncomputable def RetargetData.srcMax (o : P.scheme.below (effP nP j)) : ExtOrd :=
  letI := Fintype.ofFinite (P.scheme.below (P.scheme.cell o.1))
  (Finset.univ.filter fun d : P.scheme.below (P.scheme.cell o.1) => R.p d.1 ≠ ⊤).sup
    fun d => extVisibilityReplace (P.rows.E o.1 d) (P.scheme.grade o.1) (P.scheme.grade o.1)

omit L hj hu in
theorem RetargetData.srcMax_selfVis (o : P.scheme.below (effP nP j)) :
    SelfVis (P.scheme.grade o.1) (RetargetData.srcMax (R := R) o) :=
  TopSupport.selfVis_sup_evr _ _ _

omit L hj hu in
theorem RetargetData.le_srcMax (o : P.scheme.below (effP nP j))
    {d : P.scheme.below (P.scheme.cell o.1)} (hd : R.p d.1 ≠ ⊤) :
    P.rows.E o.1 d ≤ RetargetData.srcMax (R := R) o := by
  let _ := Fintype.ofFinite (P.scheme.below (P.scheme.cell o.1))
  exact (TopSupport.le_evr_self _ _).trans (Finset.le_sup (f := fun d =>
    extVisibilityReplace (P.rows.E o.1 d) (P.scheme.grade o.1) (P.scheme.grade o.1))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩))

omit L hj hu in
/-- Every donor-top source below a donor-top owner exceeds the rounded non-top sources. -/
theorem RetargetData.srcMax_lt_top (o : P.scheme.below (effP nP j)) (ho : R.p o.1 = ⊤)
    {t : P.scheme.below (P.scheme.cell o.1)} (ht : R.p t.1 = ⊤) :
    RetargetData.srcMax (R := R) o < P.rows.E o.1 t := by
  let _ := Fintype.ofFinite (P.scheme.below (P.scheme.cell o.1))
  have hpos : ⊥ < P.rows.E o.1 t := by
    have hp := R.p_respects.toBelow (effP nP j)
    obtain ⟨τ, hτ, -, hread⟩ := exists_bounded_exact_capped_witness
      (grade := fun d : P.scheme.below (P.scheme.cell o.1) => P.scheme.grade d.1)
      (c := ⟨o.1, GradedLe.refl _⟩) (p := fun d => R.p d.1) (fun d => d.2.2)
      (hp.orderly o).symm (hp.locality o)
    have h := hread t
    change τ (P.rows.E o.1 t) = min (R.p t.1) (R.p o.1) at h
    rw [ht, ho, min_top_right] at h
    apply bot_lt_iff_ne_bot.mpr
    intro hbot
    rw [hbot, hτ.bot] at h
    exact bot_ne_top h
  unfold RetargetData.srcMax
  rw [Finset.sup_lt_iff hpos]
  intro d hd
  exact R.srcP_nonTop_lt_top o ho d t (Finset.mem_filter.mp hd).2 ht

/-- The shifter at a donor-top owner: the old witness where it is bottom or below the rounded
non-top sources, constantly `η` above. -/
noncomputable def retargetShifter (τ : ExtOrd → ExtOrd) (a η : ExtOrd) (x : ExtOrd) : ExtOrd :=
  if τ x = ⊥ then ⊥ else if x ≤ a then τ x else η

omit L hj hu in
theorem retargetShifter_of_bot {τ : ExtOrd → ExtOrd} {a η x : ExtOrd} (h : τ x = ⊥) :
    retargetShifter τ a η x = ⊥ := by
  unfold retargetShifter; rw [ite_eq_left h]

omit L hj hu in
theorem retargetShifter_of_le {τ : ExtOrd → ExtOrd} {a η x : ExtOrd} (hx : x ≤ a) :
    retargetShifter τ a η x = τ x := by
  unfold retargetShifter
  by_cases h : τ x = ⊥
  · rw [ite_eq_left h, h]
  · rw [ite_eq_right h, ite_eq_left hx]

omit L hj hu in
theorem retargetShifter_of_lt {τ : ExtOrd → ExtOrd} {a η x : ExtOrd} (h : τ x ≠ ⊥) (hx : a < x) :
    retargetShifter τ a η x = η := by
  unfold retargetShifter; rw [ite_eq_right h, ite_eq_right (not_le.mpr hx)]

omit L hj hu in
/-- The retargeting shifter is a normalized witness through `k` whenever the old witness is, the
split point is `k`-visible with the old witness at most `b ≤ η` there, and `η` is `k`-visible and
positive. -/
theorem retargetShifter_witness {k : ℕ} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop k) τ)
    {a b η : ExtOrd} (ha : SelfVis k a) (hτa : τ a ≤ b) (hbη : b ≤ η) (hη : SelfVis k η)
    (hηpos : ⊥ < η) : Witness (gTop k) (retargetShifter τ a η) where
  anti := hτ.anti
  vis := hτ.vis
  bot := retargetShifter_of_bot hτ.bot
  mono := by
    intro x y hxy
    by_cases hx : τ x = ⊥
    · rw [retargetShifter_of_bot hx]; exact bot_le
    have hy : τ y ≠ ⊥ := fun hy => hx (le_bot_iff.mp (hy ▸ hτ.mono hxy))
    by_cases hya : y ≤ a
    · rw [retargetShifter_of_le (hxy.trans hya), retargetShifter_of_le hya]
      exact hτ.mono hxy
    · rw [retargetShifter_of_lt hy (not_le.mp hya)]
      by_cases hxa : x ≤ a
      · rw [retargetShifter_of_le hxa]
        exact (hτ.mono hxa).trans (hτa.trans hbη)
      · rw [retargetShifter_of_lt hx (not_le.mp hxa)]
  clause5 := by
    intro x kk hle i hi
    by_cases hkk : kk ≤ k
    · by_cases hx : τ x = ⊥
      · have h1 : τ (extVisibilityReplace x kk i) = ⊥ := by
          rw [hτ.clause5 x kk (by rw [gTop_of_le hkk]; exact le_top) i hi, hx,
            extVisibilityReplace_bot]
        rw [retargetShifter_of_bot hx, retargetShifter_of_bot h1, extVisibilityReplace_bot]
      · have h1 : τ (extVisibilityReplace x kk i) = extVisibilityReplace (τ x) kk i :=
          hτ.clause5 x kk (by rw [gTop_of_le hkk]; exact le_top) i hi
        by_cases hxa : x ≤ a
        · have h2 : extVisibilityReplace x kk i ≤ a := evr_le_of_le_selfVis ha hkk hi hxa
          rw [retargetShifter_of_le hxa, retargetShifter_of_le h2, h1]
        · have h2 : a < extVisibilityReplace x kk i :=
            lt_evr_of_selfVis_lt (ha.mono hkk) (not_le.mp hxa)
          have h3 : τ (extVisibilityReplace x kk i) ≠ ⊥ := by
            rw [h1]; exact extVisibilityReplace_ne_bot hx _ _
          rw [retargetShifter_of_lt hx (not_le.mp hxa), retargetShifter_of_lt h3 h2,
            evr_eq_self_of_selfVis (hη.mono hkk) i]
    · -- above `k` the suppressor is bottom: bottom is closed under replacement
      rw [gTop_of_gt (not_le.mp hkk), le_bot_iff] at hle
      have hx : τ x = ⊥ := by
        by_contra hx
        unfold retargetShifter at hle
        rw [ite_eq_right hx] at hle
        split_ifs at hle with hxa
        · exact hx hle
        · exact absurd hle (ne_bot_of_gt hηpos)
      have h1 : τ (extVisibilityReplace x kk i) = ⊥ := by
        rw [hτ.clause5 x kk (by rw [gTop_of_gt (not_le.mp hkk), hx]) i hi, hx,
          extVisibilityReplace_bot]
      rw [hle, retargetShifter_of_bot h1, extVisibilityReplace_bot]

omit hj in
/-- **Uniform top retargeting is lawful** (audit16 §2, note §3.1). -/
theorem RetargetData.retargetTops_respects :
    RespectsSemanticsBelow P.rows (effP nP j) (retargetTops (R := R) η u) where
  orderly d := by
    by_cases h : R.p d.1 = ⊤
    · rw [retargetTops_of_top η u h]
      exact (hu.η_vis.mono ((L.top_grade d.1 h).trans_eq' rfl)).symm
    · rw [retargetTops_of_nonTop η u h]; exact hu.respects.orderly d
  locality o := by
    by_cases ho : R.p o.1 = ⊤
    · -- a donor-top owner: per-owner surgery on the exact witness
      obtain ⟨τ, hτ, -, hread⟩ := exists_bounded_exact_capped_witness
        (grade := fun d : P.scheme.below (P.scheme.cell o.1) => P.scheme.grade d.1)
        (c := ⟨o.1, GradedLe.refl _⟩) (p := fun d => u (CellScheme.below.incl o d))
        (fun d => d.2.2) (hu.respects.orderly o).symm (hu.respects.locality o)
      have hko : P.scheme.grade o.1 ≤ K := L.top_grade o.1 ho
      have hτa : τ (RetargetData.srcMax (R := R) o) ≤ b := by
        let _ := Fintype.ofFinite (P.scheme.below (P.scheme.cell o.1))
        unfold RetargetData.srcMax
        rw [Finset.apply_sup_eq_sup_comp τ (fun _ _ => hτ.mono.map_max) hτ.bot]
        refine Finset.sup_le fun d hd => ?_
        simp only [Function.comp_apply]
        rw [hτ.comm_gTop _ le_rfl, hread]
        change extVisibilityReplace (min (u (CellScheme.below.incl o d)) (u o)) _ _ ≤ b
        exact evr_le_of_le_selfVis hu.b_vis hko le_rfl ((min_le_left _ _).trans
          (hu.nonTop_lt _ (Finset.mem_filter.mp hd).2).le)
      have hw := retargetShifter_witness hτ (RetargetData.srcMax_selfVis (R := R) o) hτa
        hu.b_le_η (hu.η_vis.mono hko) (hu.b_pos.trans_le hu.b_le_η)
      refine hw.transformsTo fun d => ?_
      have hg : gTop (P.scheme.grade (⟨o.1, GradedLe.refl _⟩ :
          P.scheme.below (P.scheme.cell o.1)).1) (P.scheme.grade d.1) = ⊤ :=
        gTop_of_le d.2.2
      rw [hg, min_top_right, retargetTops_of_top η u ho]
      by_cases hd : R.p d.1 = ⊤
      · rw [retargetTops_of_top η u (d := CellScheme.below.incl o d) hd, min_self]
        have hne : τ (P.rows.E o.1 d) ≠ ⊥ := by
          rw [hread]
          change min (u (CellScheme.below.incl o d)) (u o) ≠ ⊥
          exact ne_bot_of_gt (lt_min (hu.top_pos hd) (hu.top_pos ho))
        rw [retargetShifter_of_lt hne (RetargetData.srcMax_lt_top (R := R) o ho hd)]
      · rw [retargetTops_of_nonTop η u (d := CellScheme.below.incl o d) hd,
          retargetShifter_of_le (RetargetData.le_srcMax (R := R) o hd), hread]
        change min (u (CellScheme.below.incl o d)) η = min (u (CellScheme.below.incl o d)) (u o)
        rw [min_eq_left ((hu.nonTop_lt _ hd).le.trans hu.b_le_η),
          min_eq_left ((hu.nonTop_lt _ hd).le.trans (hu.top_ge o ho))]
    · -- a donor non-top owner: the capped target is unchanged
      have key := hu.respects.locality o
      have heq : (fun d : P.scheme.below (P.scheme.cell o.1) =>
          min (retargetTops (R := R) η u (CellScheme.below.incl o d))
            (retargetTops (R := R) η u o)) =
          fun d => min (u (CellScheme.below.incl o d)) (u o) := by
        funext d
        rw [retargetTops_of_nonTop η u ho]
        by_cases hd : R.p d.1 = ⊤
        · rw [retargetTops_of_top η u (d := CellScheme.below.incl o d) hd,
            min_eq_right ((hu.nonTop_lt o ho).le.trans hu.b_le_η),
            min_eq_right ((hu.nonTop_lt o ho).le.trans (hu.top_ge _ hd))]
        · rw [retargetTops_of_nonTop η u (d := CellScheme.below.incl o d) hd]
      rw [heq]; exact key
  availability Sig Xi₀ hs hg := by
    by_cases hS : R.p Sig.1 = ⊤
    · obtain ⟨Xi, hcell, hle⟩ := (R.p_respects.toBelow (effP nP j)).availability Sig Xi₀ hs hg
      have hX : R.p Xi.1 = ⊤ := top_le_iff.mp (hS ▸ hle)
      refine ⟨Xi, hcell, ?_⟩
      rw [retargetTops_of_top η u hS, retargetTops_of_top η u hX]
    · obtain ⟨Xi, hcell, hle⟩ := hu.respects.availability Sig Xi₀ hs hg
      refine ⟨Xi, hcell, ?_⟩
      rw [retargetTops_of_nonTop η u hS]
      by_cases hX : R.p Xi.1 = ⊤
      · rw [retargetTops_of_top η u hX]
        exact (hu.nonTop_lt Sig hS).le.trans hu.b_le_η
      · rw [retargetTops_of_nonTop η u hX]; exact hle

/-! ## Exact old-face restoration -/

/-- **Exact old-face restoration, arbitrary root** (audit16 §2, note §3.1; newapproach2 §4): a
lawful private section whose present face values agree with `u` at the donor non-top face cells
and are at least `η` at the donor-top face cells is matched, on the whole present face, by a
lawful section at the cutoff that retains every donor non-top value literally and puts every
donor-top value at least `η`.  Only the grade-`≤ K` part of the face goes through bountifulness;
the higher-grade face values are attached by vertical gluing. -/
theorem exists_retarget_restore {v₁ : C.scheme.below (effC J j) → ExtOrd}
    (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁)
    (hnon : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j), R.p a.1 ≠ ⊤ →
      v₁ (R.privFace a h) = u (R.reqFace a h))
    (htop : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j), R.p a.1 = ⊤ →
      η ≤ v₁ (R.privFace a h)) :
    ∃ u' : P.scheme.below (effP nP j) → ExtOrd, RespectsSemanticsBelow P.rows (effP nP j) u' ∧
      (∀ d, R.p d.1 ≠ ⊤ → u' d = u d) ∧ (∀ d, R.p d.1 = ⊤ → η ≤ u' d) ∧
      ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
        u' (R.reqFace a h) = v₁ (R.privFace a h) := by
  have hw := hu.retargetTops_respects L
  -- the lower set through the effective grade `min K (arity P)`
  have hKj : GradedLe (effP nP K) (effP nP j) := effP_mono hj
  have hwK : RespectsSemanticsBelow P.rows (effP nP K)
      (fun d => retargetTops (R := R) η u (CellScheme.below.mono hKj d)) := hw.mono hKj
  have hηK : extVisibilityReplace η (effP nP K).2 (effP nP K).2 = η :=
    hu.η_vis.mono (min_le_left _ _)
  -- restore the grade-`≤ K` part of the face inside the effective grade-`K` lower set
  have hrest : ∃ u'' : P.scheme.below (effP nP K) → ExtOrd,
      RespectsSemanticsBelow P.rows (effP nP K) u'' ∧
      (∀ d, min (u'' d) η = min (retargetTops (R := R) η u (CellScheme.below.mono hKj d)) η) ∧
      ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ K),
        u'' (R.reqFace a h) = v₁ (R.privFace a (h.trans hj)) := by
    by_cases hk : 0 < min R.KA K
    · have hv₁K : RespectsSemanticsBelow C.rows (effC J K)
          (fun d => v₁ (CellScheme.below.mono (effC_mono hj) d)) := hv₁.mono (effC_mono hj)
      obtain ⟨u'', hu'', hcap, hface⟩ := P.bountiful.extend (R.face_mem hk (min_le_left _ _))
        (effP_mem L.K_pos) R.face_le_effP (R.faceSec_respects hv₁K) hwK hηK (by
          intro a
          have ha : P.scheme.grade a.1 ≤ K := a.2.2.trans (min_le_right _ _)
          by_cases hat : R.p a.1 = ⊤
          · rw [retargetTops_of_top η u (d := CellScheme.below.mono hKj
              (CellScheme.below.mono R.face_le_effP a)) hat, min_self]
            exact (min_eq_right (htop (R.faceLift (min_le_left _ _) a) (ha.trans hj) hat)).symm
          · rw [retargetTops_of_nonTop η u (d := CellScheme.below.mono hKj
              (CellScheme.below.mono R.face_le_effP a)) hat]
            exact congrArg (fun x => min x η)
              (hnon (R.faceLift (min_le_left _ _) a) (ha.trans hj) hat).symm)
      exact ⟨u'', hu'', hcap, fun a h => hface ⟨a.1, ⟨a.2.1, le_min a.2.2 h⟩⟩⟩
    · exact ⟨fun d => retargetTops (R := R) η u (CellScheme.below.mono hKj d), hwK, fun _ => rfl,
        fun a h => (R.face_absent hk a h).elim⟩
  obtain ⟨u'', hu'', hcap, hface⟩ := hrest
  -- the values of the restored lower section
  have hlowNon : ∀ d : P.scheme.below (effP nP K), R.p d.1 ≠ ⊤ →
      u'' d = u (CellScheme.below.mono hKj d) := by
    intro d hd
    have h := hcap d
    rw [retargetTops_of_nonTop η u (d := CellScheme.below.mono hKj d) hd] at h
    exact eq_of_capAgree_of_lt h.symm ((hu.nonTop_lt _ hd).trans_le hu.b_le_η)
  have hlowTop : ∀ d : P.scheme.below (effP nP K), R.p d.1 = ⊤ → η ≤ u'' d := by
    intro d hd
    have h := hcap d
    rw [retargetTops_of_top η u (d := CellScheme.below.mono hKj d) hd, min_self] at h
    exact le_of_capAgree_of_le (x := η) (by rw [min_self]; exact h.symm) le_rfl
  have hhighNon : ∀ d : P.scheme.below (effP nP j), ¬ GradedLe (P.scheme.cell d.1) (effP nP K) →
      R.p d.1 ≠ ⊤ := by
    intro d hd ht
    exact hd ⟨Finset.subset_univ _, le_min (L.top_grade d.1 ht) (gradeP_le d.1)⟩
  refine ⟨glueSection u'' u, hu.respects.glue hKj rfl hu'' ?_, ?_, ?_, ?_⟩
  · intro Sig hS d hd
    have hSn := hhighNon Sig hS
    by_cases hdt : R.p d.1 = ⊤
    · rw [min_eq_right ((hu.nonTop_lt Sig hSn).le.trans (hu.b_le_η.trans
        (hlowTop ⟨d.1, hd⟩ hdt))),
        min_eq_right ((hu.nonTop_lt Sig hSn).le.trans (hu.top_ge _ hdt))]
    · rw [hlowNon ⟨d.1, hd⟩ hdt]; rfl
  · intro d hd
    by_cases h : GradedLe (P.scheme.cell d.1) (effP nP K)
    · rw [glueSection_of_le u'' u h, hlowNon ⟨d.1, h⟩ hd]; rfl
    · rw [glueSection_of_not_le u'' u h]
  · intro d hd
    have h : GradedLe (P.scheme.cell d.1) (effP nP K) :=
      ⟨Finset.subset_univ _, le_min (L.top_grade d.1 hd) (gradeP_le d.1)⟩
    rw [glueSection_of_le u'' u h]
    exact hlowTop ⟨d.1, h⟩ hd
  · intro a h
    by_cases hK : P.scheme.grade a.1 ≤ K
    · have hg : GradedLe (P.scheme.cell a.1) (effP nP K) :=
        ⟨Finset.subset_univ _, le_min hK (gradeP_le a.1)⟩
      rw [glueSection_of_le u'' u (d := R.reqFace a h) hg]
      exact hface a hK
    · have hg : ¬ GradedLe (P.scheme.cell a.1) (effP nP K) := fun hg =>
        hK (hg.2.trans (min_le_left _ _))
      rw [glueSection_of_not_le u'' u (d := R.reqFace a h) hg]
      exact (hnon a h fun ht => hK (L.top_grade a.1 ht)).symm

end Retarget

end Ref

end CappedDonor

end VaughtConjecture.Knight
