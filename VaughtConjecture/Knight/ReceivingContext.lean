/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingTemplate

/-! # The receiving template from an actual receiving context

The reviewer's notes7 (`mixed_proper_top_charts.md` §6, 2026-09-19), at the level of the
finite schemes: from the actual private labelling `u₀` reading a full-scope grade-`N` cap
`C` at `⊤`, the cap's row, one old reference per block of the candidate's proper values
(labelled in that block with offset below `N`), a top marker `a`, and a lawful candidate `P`
extending the root literally, the theorem `exists_relativeData_of_context` **produces** the
relative data: the cleaned donor, the source strips, the block code, the encoded candidate,
and the literal root restoration.  The remaining model-side input is one clause:

* **the one-row criterion** (`htoproot`): a top-labelled root cell's source dominates the
  marker's offset-`R` replacement.  `ProvisionalCap.transport` supplies the intermediate
  inequality `R_{N,N}(E_C Σ) ≤ E_C d` for a provisionally capped `d` and some top source `Σ`;
  it does not construct the joint context in which the marker is a *least* top source and
  every top root cell is provisionally capped.  A least-top-source marker is a sufficient
  route, not necessarily the weakest requirement.  Stable-top fixedness or effective-anchor
  data do not discharge `htoproot` until that context-selection theorem is proved.

**Proper-root alignment is derived, not assumed.**  Every proper candidate label has offset
below `N` (`hblocks`), so a proper root cell's source sits on an *affine* strip of the reading
witness, and two distinct strips cannot both map affinely onto one block
(`strip_unique_of_read`): the root cell's source is its block's reference strip at its own
offset.  The earlier hypothesis `halign` is now a lemma inside the proof.  The grade-one
merging regression (`TemplateRegression.no_scalar_root`) has a value whose offset equals the
grade, outside this offset bound; it shows the bound is necessary, not that alignment fails
under it.

The reading witness `τ` of the cap's row (`exists_exact_capped_shifter`) yields the source
facts used: a source read to a proper value with offset below `N` has the same offset
(`read_finitePart`), readings in different blocks come from different strips, in order
(`strip_lt_of_read`), readings in the same block come from the same strip
(`strip_unique_of_read`), and every such strip plus `N` lies below the offset-`R` replacement
of a source read to `⊤` (`strip_add_le_of_read_top`).

Not here: obtaining the context itself (references by uniformity, provisional bounds for the
root's top cells and one private stably-top occurrence, `N = topGrade`) from the model
clauses; that is the model-side supply, stated in `docs/STATUS.md`.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-! ## The ordinal under a proper value -/

theorem ofOrd_ordOf {x : ExtOrd} (hb : x ≠ ⊥) (ht : x ≠ ⊤) : ofOrd (ordOf x) = x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact absurd rfl hb
  · exact absurd rfl ht
  · rw [ordOf_ofOrd]

/-! ## Reading-witness facts -/

section Reading

variable {N : ℕ} {τ : ExtOrd → ExtOrd} (hτ : BoundedMap N τ)

include hτ in
/-- A source read to a proper value with offset below `N` has offset below `N`, the same. -/
theorem read_finitePart {s t : Ordinal.{0}} (h : τ (ofOrd s) = ofOrd t)
    (ht : finitePart t < N) : finitePart s < N ∧ finitePart s = finitePart t := by
  have key : ∀ i ≤ N, τ (extVisibilityReplace (ofOrd s) N i) = ofOrd (limitPart t + i) := by
    intro i hi
    rw [hτ.comm _ N i le_rfl hi, h, extVisibilityReplace_of_finitePart_lt ht]
  have hlt : finitePart s < N := by
    by_contra hge
    have hge' := not_lt.mp hge
    have h1 := key (finitePart t) ht.le
    have h2 := key (finitePart t + 1) ht
    rw [extVisibilityReplace_of_le_finitePart hge'] at h1 h2
    rw [h1, ofOrd_inj] at h2
    have h3 := add_left_cancel h2
    exact absurd (Nat.cast_injective h3) (Nat.succ_ne_self _).symm
  refine ⟨hlt, ?_⟩
  have h1 := key (finitePart s) hlt.le
  rw [extVisibilityReplace_of_finitePart_lt hlt, limitPart_add_finitePart, h, ofOrd_inj] at h1
  have := congrArg finitePart h1
  rw [finitePart_limitPart_add_nat] at this
  exact this.symm

include hτ in
/-- Two proper readings with offsets below `N` in different blocks come from different
strips, in the same order. -/
theorem strip_lt_of_read {s s' t t' : Ordinal.{0}} (h : τ (ofOrd s) = ofOrd t)
    (h' : τ (ofOrd s') = ofOrd t') (ht : finitePart t < N) (ht' : finitePart t' < N)
    (hlt : limitPart t < limitPart t') : limitPart s < limitPart s' := by
  have hss' : s < s' := by
    by_contra hle
    have := hτ.mono (ofOrd_le_ofOrd.mpr (not_lt.mp hle))
    rw [h, h', ofOrd_le_ofOrd] at this
    exact absurd (limitPart_mono this) (not_le.mpr hlt)
  have hlp : limitPart s ≤ limitPart s' := limitPart_mono hss'.le
  rcases hlp.lt_or_eq with hlt' | heq
  · exact hlt'
  exfalso
  have hfs := (read_finitePart hτ h ht).1
  have hfs' := (read_finitePart hτ h' ht').1
  have k1 := hτ.comm (ofOrd s) N 0 le_rfl (Nat.zero_le _)
  have k2 := hτ.comm (ofOrd s') N 0 le_rfl (Nat.zero_le _)
  rw [extVisibilityReplace_of_finitePart_lt hfs, h, extVisibilityReplace_of_finitePart_lt ht,
    Nat.cast_zero, add_zero, add_zero] at k1
  rw [extVisibilityReplace_of_finitePart_lt hfs', h', extVisibilityReplace_of_finitePart_lt ht',
    Nat.cast_zero, add_zero, add_zero] at k2
  rw [heq] at k1
  rw [k1, ofOrd_inj] at k2
  exact hlt.ne k2

include hτ in
/-- **Strip uniqueness**: two proper readings with offsets below `N` in the *same* block come
from the same strip.  Both sources sit on affine strips through offset `N`; if the strips
differed, the lower strip's `N`-endpoint would map at or below the upper strip's floor. -/
theorem strip_unique_of_read {s s' t t' : Ordinal.{0}} (h : τ (ofOrd s) = ofOrd t)
    (h' : τ (ofOrd s') = ofOrd t') (ht : finitePart t < N) (ht' : finitePart t' < N)
    (heq : limitPart t = limitPart t') : limitPart s = limitPart s' := by
  have key : ∀ (s t : Ordinal.{0}), τ (ofOrd s) = ofOrd t → finitePart t < N →
      ∀ i ≤ N, τ (ofOrd (limitPart s + i)) = ofOrd (limitPart t + i) := by
    intro s t h ht i hi
    have hfs := (read_finitePart hτ h ht).1
    have k := hτ.comm (ofOrd s) N i le_rfl hi
    rwa [extVisibilityReplace_of_finitePart_lt hfs, h,
      extVisibilityReplace_of_finitePart_lt ht] at k
  have hNpos : (0 : ℕ) < N := lt_of_le_of_lt (Nat.zero_le _) ht
  -- one direction: a strictly lower strip is impossible
  have one : ∀ (s s' t t' : Ordinal.{0}), τ (ofOrd s) = ofOrd t → τ (ofOrd s') = ofOrd t' →
      finitePart t < N → finitePart t' < N → limitPart t = limitPart t' →
      ¬ limitPart s < limitPart s' := by
    intro s s' t t' h h' ht ht' heq hlt
    have h1 := key s t h ht N le_rfl
    have h2 := key s' t' h' ht' 0 (Nat.zero_le _)
    rw [Nat.cast_zero, add_zero, add_zero] at h2
    have hle : limitPart s + (N : Ordinal.{0}) < limitPart s' :=
      add_nat_lt_of_lt_limit (limitPart_idem s) (limitPart_idem s') hlt N
    have hm := hτ.mono (ofOrd_le_ofOrd.mpr hle.le)
    rw [h1, h2, ofOrd_le_ofOrd, ← heq] at hm
    have : (N : Ordinal.{0}) ≤ 0 := le_of_add_le_add_left (by rwa [add_zero])
    exact absurd (Nat.cast_le.mp this) (not_le.mpr hNpos)
  rcases lt_trichotomy (limitPart s) (limitPart s') with hlt | heq' | hgt
  · exact absurd hlt (one s s' t t' h h' ht ht' heq)
  · exact heq'
  · exact absurd hgt (one s' s t' t h' h ht' ht heq.symm)

include hτ in
/-- Below a source read to `⊤`: its offset-`R` replacement is a proper `R`-visible value, and
every strip of a proper reading with offset below `N`, plus `N`, lies at most there. -/
theorem strip_add_le_of_read_top {sa : Ordinal.{0}} (ha : τ (ofOrd sa) = ⊤) (R : ℕ)
    (hR : R < N) :
    ∃ h : Ordinal.{0}, extVisibilityReplace (ofOrd sa) N R = ofOrd h ∧ R ≤ finitePart h ∧
      ∀ s t : Ordinal.{0}, τ (ofOrd s) = ofOrd t → finitePart t < N →
        limitPart s + N ≤ h := by
  by_cases hfa : finitePart sa < N
  · refine ⟨limitPart sa + R, extVisibilityReplace_of_finitePart_lt hfa R, ?_, ?_⟩
    · rw [finitePart_limitPart_add_nat]
    · intro s t h ht
      have hfs := (read_finitePart hτ h ht).1
      have hss : s < sa := by
        by_contra hle
        have := hτ.mono (ofOrd_le_ofOrd.mpr (not_lt.mp hle))
        rw [h, ha] at this
        exact absurd this (not_top_le_ofOrd t)
      have hlp : limitPart s ≤ limitPart sa := limitPart_mono hss.le
      rcases hlp.lt_or_eq with hlt | heq
      · exact (limitPart_add_nat_le_of_lt hlt N).trans le_self_add
      · exfalso
        have k1 := hτ.comm (ofOrd s) N 0 le_rfl (Nat.zero_le _)
        have k2 := hτ.comm (ofOrd sa) N 0 le_rfl (Nat.zero_le _)
        rw [extVisibilityReplace_of_finitePart_lt hfs, h,
          extVisibilityReplace_of_finitePart_lt ht] at k1
        rw [extVisibilityReplace_of_finitePart_lt hfa, ha, extVisibilityReplace_top] at k2
        rw [heq] at k1
        rw [k1] at k2
        exact ofOrd_ne_top _ k2
  · have hfa' := not_lt.mp hfa
    refine ⟨sa, extVisibilityReplace_of_le_finitePart hfa' R, hR.le.trans hfa', ?_⟩
    intro s t h ht
    have hss : s < sa := by
      by_contra hle
      have := hτ.mono (ofOrd_le_ofOrd.mpr (not_lt.mp hle))
      rw [h, ha] at this
      exact absurd this (not_top_le_ofOrd t)
    calc limitPart s + (N : Ordinal.{0}) ≤ limitPart sa + (N : Ordinal.{0}) :=
          add_le_add_left (limitPart_mono hss.le) _
      _ ≤ limitPart sa + (finitePart sa : Ordinal.{0}) :=
          add_le_add_right (Nat.cast_le.mpr hfa') _
      _ = sa := limitPart_add_finitePart sa

end Reading

/-! ## The template from an actual receiving context -/

section Context

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ] {A : Finset ιA} {Q : Finset ιQ}
  {DA : CellScheme A} {semA : Semantics DA} {DQ : CellScheme Q} {semQ : Semantics DQ}

/-- The actual construction retains the input occurrence geometry and the
whole actual private bottom-pattern class. -/
theorem exists_relativeData_of_context_with_root (req : Requests DA DQ)
    (grade_C : DA.grade req.C = req.N)
    (hrow : RespectsSemanticsBelow semA (DA.cell req.C) (semA.E req.C))
    {u₀ : Cell DA → ExtOrd} (hu₀ : RespectsSemantics semA u₀) (hC : u₀ req.C = ⊤)
    (ha_top : u₀ req.a.1 = ⊤) (ha_ne_top : semA.E req.C req.a ≠ ⊤)
    (S : Finset Ordinal.{0}) (hS : ∀ μ ∈ S, limitPart μ = μ)
    (ref : Ordinal.{0} → DA.below (DA.cell req.C))
    (href : ∀ μ ∈ S, ∃ j < req.N, u₀ (ref μ).1 = ofOrd (μ + j))
    {P : Cell DQ → ExtOrd} (hP : RespectsSemantics semQ P) {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_le_R : top.2 ≤ req.R)
    (κ : DQ.below root → DA.below (DA.cell req.C))
    (hroot : ∀ s : DA.below (DA.cell req.C) → ExtOrd,
      RespectsSemanticsBelow semA (DA.cell req.C) s →
        RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    (cover : ∀ d, d ∈ req.Z ∨ d ∈ req.F ∨ d ∈ req.T ∨ ∃ r : DQ.below root, r.1 = d)
    (hlit : ∀ r : DQ.below root, P r.1 = u₀ (κ r).1)
    (hblocks : ∀ d p, P d = ofOrd p → limitPart p ∈ S ∧ finitePart p < req.N)
    (hZ : ∀ z ∈ req.Z, P z = ⊥) (hT : ∀ y ∈ req.T, P y = ⊤)
    (hF : ∀ f ∈ req.F, ∃ p, P f = ofOrd p ∧ req.ρ f = ref (limitPart p) ∧
      req.off f = finitePart p)
    (htoproot : ∀ r : DQ.below root, u₀ (κ r).1 = ⊤ →
      extVisibilityReplace (semA.E req.C req.a) req.N req.R ≤ semA.E req.C (κ r)) :
    ∃ X : RelativeData DA semA DQ semQ, X.req = req ∧ X.root = root ∧ X.top = top ∧
      HEq X.κ κ ∧ HEq X.ZA {d : DA.below (DA.cell req.C) | u₀ d.1 = ⊥} ∧
      (∀ d, X.e d = if u₀ d.1 = ⊥ then ⊥ else semA.E X.req.C d) ∧
      (∀ f ∈ X.req.F,
        X.V f = extVisibilityReplace (semA.E X.req.C (X.req.ρ f)) X.req.N (X.req.off f)) ∧
      (∀ y ∈ X.req.T, extVisibilityReplace (semA.E X.req.C X.req.a) X.req.N X.req.R ≤ X.V y) ∧
      ∀ z ∈ X.req.Z, X.V z = ⊥ := by
  classical
  -- the reading witness of the cap's row
  have hvis : SelfVis (DA.grade req.C) (u₀ req.C) := (hu₀.orderly req.C).symm
  obtain ⟨τ, hbot, hmono, hread, hcomm, -⟩ := exists_exact_capped_shifter
    (D := DA.below (DA.cell req.C)) (grade := fun d => DA.grade d.1) (p := fun d => u₀ d.1)
    (c := req.capCell) (fun d => d.2.2) hvis (hu₀.locality req.C)
  have hτ : BoundedMap req.N τ :=
    ⟨hbot, hmono, fun x k i hk hi =>
      hcomm x k i (by change k ≤ DA.grade req.C; rw [grade_C]; exact hk) hi⟩
  have hread' : ∀ d : DA.below (DA.cell req.C), τ (semA.E req.C d) = u₀ d.1 := by
    intro d
    rw [hread d]
    change min (u₀ d.1) (u₀ req.C) = u₀ d.1
    rw [hC, min_top_right]
  have hτtop : τ ⊤ = ⊤ := by
    have h1 := hread' req.capCell
    change τ (semA.E req.C req.capCell) = u₀ req.C at h1
    rw [hC] at h1
    have h2 : τ (semA.E req.C req.capCell) ≤ τ ⊤ := hmono le_top
    rw [h1] at h2
    exact top_le_iff.mp h2
  -- the donor
  set e : DA.below (DA.cell req.C) → ExtOrd :=
    fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d with hedef
  have he : RespectsSemanticsBelow semA (DA.cell req.C) e :=
    cleaned_respects_of_bottom_agreement hrow (hu₀.toBelow _)
      (fun d => d.2.2.trans_eq grade_C) hτ (fun d => by rw [hread' d])
  have he_eq : ∀ d, u₀ d.1 ≠ ⊥ → e d = semA.E req.C d := fun d h => by
    change (if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) = _
    rw [ite_eq_right h]
  -- the marker's source
  have ha_ne_bot : semA.E req.C req.a ≠ ⊥ := fun h0 => by
    have := hread' req.a
    rw [h0, hbot, ha_top] at this
    exact bot_ne_top this
  obtain ⟨sa, hsa⟩ : ∃ sa, semA.E req.C req.a = ofOrd sa := by
    rcases ExtOrd.cases (semA.E req.C req.a) with h | h | ⟨sa, h⟩
    · exact absurd h ha_ne_bot
    · exact absurd h ha_ne_top
    · exact ⟨sa, h⟩
  have hτa : τ (ofOrd sa) = ⊤ := by rw [← hsa, hread', ha_top]
  obtain ⟨h, hh, hRh, hstrip⟩ := strip_add_le_of_read_top hτ hτa req.R req.R_lt_N
  -- the references' sources
  have hsrc : ∀ μ ∈ S, ∃ s, semA.E req.C (ref μ) = ofOrd s ∧
      τ (ofOrd s) = u₀ (ref μ).1 := by
    intro μ hμ
    obtain ⟨j, -, hj⟩ := href μ hμ
    rcases ExtOrd.cases (semA.E req.C (ref μ)) with h0 | h0 | ⟨s, h0⟩
    · exfalso
      have := hread' (ref μ)
      rw [h0, hbot, hj] at this
      exact ofOrd_ne_bot _ this.symm
    · exfalso
      have := hread' (ref μ)
      rw [h0, hτtop, hj] at this
      exact ofOrd_ne_top _ this.symm
    · exact ⟨s, h0, by rw [← h0]; exact hread' _⟩
  set strip : Ordinal.{0} → Ordinal.{0} := fun μ => limitPart (ordOf (semA.E req.C (ref μ)))
    with hstripdef
  have hsrc' : ∀ μ ∈ S, ∃ j < req.N, τ (ofOrd (ordOf (semA.E req.C (ref μ)))) = ofOrd (μ + j) ∧
      strip μ = limitPart (ordOf (semA.E req.C (ref μ))) := by
    intro μ hμ
    obtain ⟨s, hs, hτs⟩ := hsrc μ hμ
    obtain ⟨j, hjN, hj⟩ := href μ hμ
    refine ⟨j, hjN, ?_, rfl⟩
    rw [hs, ordOf_ofOrd, hτs, hj]
  have hfpμ : ∀ μ ∈ S, ∀ j : ℕ, finitePart (μ + (j : Ordinal.{0})) = j := fun μ hμ j =>
    finitePart_add_nat_of_limit (hS μ hμ) j
  have hlpμ : ∀ μ ∈ S, ∀ j : ℕ, limitPart (μ + (j : Ordinal.{0})) = μ := fun μ hμ j =>
    limitPart_add_nat_of_limit (hS μ hμ) j
  -- the block code
  have hlim : ∀ μ ∈ S, limitPart (strip μ) = strip μ := fun μ _ => limitPart_idem _
  have hle : ∀ μ ∈ S, strip μ + req.N ≤ h := by
    intro μ hμ
    obtain ⟨j, hjN, hτs, -⟩ := hsrc' μ hμ
    exact hstrip _ _ hτs (by rw [hfpμ μ hμ]; exact hjN)
  have hstrict : ∀ μ ∈ S, ∀ μ' ∈ S, μ < μ' → strip μ < strip μ' := by
    intro μ hμ μ' hμ' hlt
    obtain ⟨j, hjN, hτs, -⟩ := hsrc' μ hμ
    obtain ⟨j', hjN', hτs', -⟩ := hsrc' μ' hμ'
    exact strip_lt_of_read hτ hτs hτs' (by rw [hfpμ μ hμ]; exact hjN)
      (by rw [hfpμ μ' hμ']; exact hjN') (by rw [hlpμ μ hμ, hlpμ μ' hμ']; exact hlt)
  set B : BlockCode := BlockCode.ofFinset req.N req.R req.R_lt_N S strip h hlim hle hstrict hRh
    with hBdef
  have hB_N : B.N = req.N := rfl
  have hB_R : B.R = req.R := rfl
  have hBtop : B.code ⊤ = ofOrd h := rfl
  have hBlisted : ∀ μ ∈ S, B.Λ μ = some (strip μ) := fun μ hμ =>
    BlockCode.ofFinset_Λ_listed req.N req.R req.R_lt_N S strip h hlim hle hstrict hRh hμ
  have hcode : ∀ p, limitPart p ∈ S → finitePart p ≤ req.N →
      B.code (ofOrd p) = ofOrd (strip (limitPart p) + finitePart p) := fun p hp hfp =>
    B.code_listed hp (hBlisted _ hp) hfp
  -- the source facts of a listed block
  have hsrcfp : ∀ μ ∈ S, finitePart (ordOf (semA.E req.C (ref μ))) < req.N := by
    intro μ hμ
    obtain ⟨j, hjN, hτs, -⟩ := hsrc' μ hμ
    exact (read_finitePart hτ hτs (by rw [hfpμ μ hμ]; exact hjN)).1
  have hevr : ∀ μ ∈ S, ∀ i, extVisibilityReplace (semA.E req.C (ref μ)) req.N i =
      ofOrd (strip μ + i) := by
    intro μ hμ i
    obtain ⟨s, hs, -⟩ := hsrc μ hμ
    have hfs : finitePart s < req.N := by
      have := hsrcfp μ hμ
      rwa [hs, ordOf_ofOrd] at this
    rw [hs, extVisibilityReplace_of_finitePart_lt hfs]
    change ofOrd (limitPart s + i) = ofOrd (limitPart (ordOf (semA.E req.C (ref μ))) + i)
    rw [hs, ordOf_ofOrd]
  -- the encoding hypotheses
  have hh' : extVisibilityReplace (e req.a) req.N req.R = ofOrd h := by
    rw [he_eq _ (by rw [ha_top]; exact top_ne_bot), hsa]; exact hh
  have hvish : SelfVis req.R (extVisibilityReplace (e req.a) req.N req.R) := by
    rw [hh']; exact extVisibilityReplace_of_le_finitePart hRh _
  have hbotP : ∀ d, B.code (P d) = ⊥ → P d = ⊥ := by
    intro d hd
    rcases ExtOrd.cases (P d) with h0 | h0 | ⟨p, h0⟩
    · exact h0
    · rw [h0, hBtop] at hd; exact absurd hd (ofOrd_ne_bot _)
    · obtain ⟨hp, hfp⟩ := hblocks d p h0
      rw [h0, hcode p hp hfp.le] at hd
      exact absurd hd (ofOrd_ne_bot _)
  -- proper-root alignment, derived from strip uniqueness
  have halign : ∀ (r : DQ.below root) p, P r.1 = ofOrd p →
      semA.E req.C (κ r) = ofOrd (strip (limitPart p) + finitePart p) := by
    intro r p hP0
    obtain ⟨hp, hfp⟩ := hblocks _ p hP0
    have hu : u₀ (κ r).1 = ofOrd p := by rw [← hlit r]; exact hP0
    obtain ⟨s, hs⟩ : ∃ s, semA.E req.C (κ r) = ofOrd s := by
      rcases ExtOrd.cases (semA.E req.C (κ r)) with h0 | h0 | ⟨s, h0⟩
      · exfalso
        have := hread' (κ r)
        rw [h0, hbot, hu] at this
        exact ofOrd_ne_bot _ this.symm
      · exfalso
        have := hread' (κ r)
        rw [h0, hτtop, hu] at this
        exact ofOrd_ne_top _ this.symm
      · exact ⟨s, h0⟩
    have hτs : τ (ofOrd s) = ofOrd p := by rw [← hs, hread', hu]
    obtain ⟨j, hjN, hτref, hstripμ⟩ := hsrc' _ hp
    have hlp : limitPart s = strip (limitPart p) := by
      rw [hstripμ]
      exact strip_unique_of_read hτ hτs hτref hfp (by rw [hfpμ _ hp]; exact hjN)
        (by rw [hlpμ _ hp])
    have hfp' : finitePart s = finitePart p := (read_finitePart hτ hτs hfp).2
    rw [hs, ← hlp, ← hfp', limitPart_add_finitePart]
  have hroot_cap : ∀ r : DQ.below root,
      min (B.code (P r.1)) (ofOrd h) = min (e (κ r)) (ofOrd h) := by
    intro r
    rcases ExtOrd.cases (u₀ (κ r).1) with h0 | h0 | ⟨p, h0⟩
    · rw [hlit r, h0, B.code_bot]
      change min ⊥ (ofOrd h) = min (if u₀ (κ r).1 = ⊥ then ⊥ else semA.E req.C (κ r)) (ofOrd h)
      rw [ite_eq_left h0]
    · rw [hlit r, h0, hBtop, min_self, he_eq _ (by rw [h0]; exact top_ne_bot)]
      have := htoproot r h0
      rw [hsa, hh] at this
      exact (min_eq_right this).symm
    · have hP0 : P r.1 = ofOrd p := by rw [hlit r, h0]
      obtain ⟨hp, hfp⟩ := hblocks _ p hP0
      rw [hP0, hcode p hp hfp.le, he_eq _ (by rw [h0]; exact ofOrd_ne_bot _), halign r p hP0]
  have hF' : ∀ f ∈ req.F, B.code (P f) =
      extVisibilityReplace (e (req.ρ f)) req.N (req.off f) := by
    intro f hf
    obtain ⟨p, hPf, hρ, hoff⟩ := hF f hf
    obtain ⟨hp, hfp⟩ := hblocks f p hPf
    obtain ⟨j, -, hj⟩ := href _ hp
    rw [hPf, hcode p hp hfp.le, hρ, hoff, he_eq _ (by rw [hj]; exact ofOrd_ne_bot _), hevr _ hp]
  have hFlt : ∀ f ∈ req.F, extVisibilityReplace (e (req.ρ f)) req.N (req.off f) <
      extVisibilityReplace (e req.a) req.N req.R := by
    intro f hf
    obtain ⟨p, hPf, hρ, hoff⟩ := hF f hf
    obtain ⟨hp, hfp⟩ := hblocks f p hPf
    obtain ⟨j, -, hj⟩ := href _ hp
    rw [hρ, hoff, he_eq _ (by rw [hj]; exact ofOrd_ne_bot _), hevr _ hp, hh', ofOrd_lt_ofOrd]
    calc strip (limitPart p) + (finitePart p : Ordinal.{0})
        < strip (limitPart p) + (req.N : Ordinal.{0}) :=
          (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hfp)
      _ ≤ h := hle _ hp
  have hT' : ∀ y ∈ req.T, B.code (P y) = extVisibilityReplace (e req.a) req.N req.R := by
    intro y hy
    rw [hT y hy, hBtop, hh']
  have ha_ne : e req.a ≠ ⊥ := by
    rw [he_eq _ (by rw [ha_top]; exact top_ne_bot), hsa]; exact ofOrd_ne_bot _
  -- the template
  obtain ⟨V, hVr, hVroot, hVcorr, hframe, hVF, hVT, hVZ⟩ := template_of_encoding_capped req e he
    ha_ne hP root_mem top_mem root_le root_ne below_top top_le_R κ hroot bountiful
    (B.boundedMap_code) hbotP hvish (by rw [hh']; exact hroot_cap) hZ hF' hFlt hT'
  have ha_ne' : u₀ req.a.1 ≠ ⊥ := by rw [ha_top]; exact top_ne_bot
  have hρ_ne : ∀ f ∈ req.F, u₀ (req.ρ f).1 ≠ ⊥ := by
    intro f hf
    obtain ⟨p, hPf, hρ, -⟩ := hF f hf
    obtain ⟨hp, -⟩ := hblocks f p hPf
    obtain ⟨j, -, hj⟩ := href _ hp
    rw [hρ, hj]; exact ofOrd_ne_bot _
  have hoff_lt : ∀ f ∈ req.F, req.off f ≤ req.N := by
    intro f hf
    obtain ⟨p, hPf, -, hoff⟩ := hF f hf
    rw [hoff]; exact (hblocks f p hPf).2.le
  refine ⟨mkRelativeData req grade_C hrow hu₀ hC ha_ne' hρ_ne hoff_lt root_mem top_mem root_le
    root_ne below_top (top_le_R.trans req.R_lt_N.le) κ hroot bountiful cover V hVr hVroot hVcorr
    hframe, rfl, rfl, rfl, HEq.rfl, HEq.rfl, fun _ => rfl, ?_, ?_, hVZ⟩
  · intro f hf
    have h1 := hVF f hf
    obtain ⟨p, hPf, hρ, -⟩ := hF f hf
    obtain ⟨hp, -⟩ := hblocks f p hPf
    obtain ⟨j, -, hj⟩ := href _ hp
    rw [he_eq _ (by rw [hρ, hj]; exact ofOrd_ne_bot _)] at h1
    exact h1
  · intro y hy
    have h1 := hVT y hy
    rw [he_eq _ ha_ne'] at h1
    exact h1

/-- **The relative data from an actual receiving context.**  Inputs: the requests with a
full-scope grade-`N` cap `C` read at `⊤` by the actual lawful labelling `u₀`, the cap's
lawful row, a top marker `a` with proper source, a finite set `S` of blocks with one old
reference per block labelled in that block below offset `N`, and a lawful candidate `P`
extending the root literally whose proper values all lie in listed blocks with offsets below
`N`, with requested bottoms, tops, and exact requests referring to their block's reference.
The one model-side clause is the one-row criterion `htoproot`; proper-root alignment is
derived (`strip_unique_of_read`).  Output: relative data with the cleaned donor, whose template
reads every exact
request at its reference strip, every high request at least at the marker's replacement,
and every requested bottom at bottom. -/
theorem exists_relativeData_of_context (req : Requests DA DQ)
    (grade_C : DA.grade req.C = req.N)
    (hrow : RespectsSemanticsBelow semA (DA.cell req.C) (semA.E req.C))
    {u₀ : Cell DA → ExtOrd} (hu₀ : RespectsSemantics semA u₀) (hC : u₀ req.C = ⊤)
    (ha_top : u₀ req.a.1 = ⊤) (ha_ne_top : semA.E req.C req.a ≠ ⊤)
    (S : Finset Ordinal.{0}) (hS : ∀ μ ∈ S, limitPart μ = μ)
    (ref : Ordinal.{0} → DA.below (DA.cell req.C))
    (href : ∀ μ ∈ S, ∃ j < req.N, u₀ (ref μ).1 = ofOrd (μ + j))
    {P : Cell DQ → ExtOrd} (hP : RespectsSemantics semQ P) {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_le_R : top.2 ≤ req.R)
    (κ : DQ.below root → DA.below (DA.cell req.C))
    (hroot : ∀ s : DA.below (DA.cell req.C) → ExtOrd,
      RespectsSemanticsBelow semA (DA.cell req.C) s →
        RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    (cover : ∀ d, d ∈ req.Z ∨ d ∈ req.F ∨ d ∈ req.T ∨ ∃ r : DQ.below root, r.1 = d)
    (hlit : ∀ r : DQ.below root, P r.1 = u₀ (κ r).1)
    (hblocks : ∀ d p, P d = ofOrd p → limitPart p ∈ S ∧ finitePart p < req.N)
    (hZ : ∀ z ∈ req.Z, P z = ⊥) (hT : ∀ y ∈ req.T, P y = ⊤)
    (hF : ∀ f ∈ req.F, ∃ p, P f = ofOrd p ∧ req.ρ f = ref (limitPart p) ∧
      req.off f = finitePart p)
    (htoproot : ∀ r : DQ.below root, u₀ (κ r).1 = ⊤ →
      extVisibilityReplace (semA.E req.C req.a) req.N req.R ≤ semA.E req.C (κ r)) :
    ∃ X : RelativeData DA semA DQ semQ, X.req = req ∧
      (∀ d, X.e d = if u₀ d.1 = ⊥ then ⊥ else semA.E X.req.C d) ∧
      (∀ f ∈ X.req.F,
        X.V f = extVisibilityReplace (semA.E X.req.C (X.req.ρ f)) X.req.N (X.req.off f)) ∧
      (∀ y ∈ X.req.T, extVisibilityReplace (semA.E X.req.C X.req.a) X.req.N X.req.R ≤ X.V y) ∧
      ∀ z ∈ X.req.Z, X.V z = ⊥ := by
  obtain ⟨X, hreq, _, _, _, _, he, hF', hT', hZ'⟩ :=
    exists_relativeData_of_context_with_root req grade_C hrow hu₀ hC ha_top ha_ne_top S hS
      ref href hP root_mem top_mem root_le root_ne below_top top_le_R κ hroot bountiful cover
      hlit hblocks hZ hT hF htoproot
  exact ⟨X, hreq, he, hF', hT', hZ'⟩


end Context

end VaughtConjecture.Knight
