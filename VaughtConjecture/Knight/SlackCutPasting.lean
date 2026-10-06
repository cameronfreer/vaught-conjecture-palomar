/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledRepairPaste

/-! # Pasting with one grade of slack

A monotone operation fixing a cut commutes with capped pasting without input agreement
if it preserves the strict lower half of the cut. Visibility replacement has this property
when the cut is self-visible one grade higher than the thresholds in use.

This is a locality tool, not a general bountifulness theorem: sections must still be
constructed, and availability involves a choice of dominating controller. Separate
existential domination is not, by itself, preserved by coordinatewise pasting.

For actual respecting inputs, `paste_iff_high_controller_overlap` isolates the exact
availability condition. Unique graded indices suffice, but are not imposed on the
existing constructions, which genuinely have multiple cells at some indices. The
fixed repaired three-level scheme also pastes at slack cuts by its exact classification.

The extra visibility is essential for unrestricted operation commutation. It cannot
be substituted for the externally supplied cap in unrestricted bountifulness, nor
confused with the limit stage used for reduction.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-- Strict preservation below a fixed cut replaces the agreement hypothesis of
`map_paste_of_agree`. The two inputs here are arbitrary. -/
theorem map_paste_of_strict_cut {α : Type*} [LinearOrder α] {g q s : α}
    (f : α → α) (hf : Monotone f) (hg : f g = g)
    (hstrict : ∀ x, x < g → f x < g) :
    f (paste g q s) = paste g (f q) (f s) := by
  by_cases hq : q < g
  · rw [paste_of_lt hq, paste_of_lt (hstrict q hq)]
  · have hqg : g ≤ q := le_of_not_gt hq
    have hfg : g ≤ f q := hg ▸ hf hqg
    rw [paste_of_ge hqg, paste_of_ge hfg, hf.map_max, hg]

/-- Above the cut in both inputs, domination by a pasted controller is exactly an
overlap condition: its first value reaches the cut and its second dominates the source. -/
theorem paste_le_iff_high_overlap {α : Type*} [LinearOrder α] {g q s q' s' : α}
    (hq : g ≤ q) (hs : g < s) :
    paste g q s ≤ paste g q' s' ↔ g ≤ q' ∧ s ≤ s' := by
  rw [paste_of_ge hq, max_eq_right hs.le]
  unfold paste
  split_ifs <;> grind

/-- Replacement below a strictly higher visibility threshold cannot land on the cut. -/
theorem evr_lt_of_slack_cut {g x : ExtOrd} {K k i : ℕ}
    (hg : SelfVis (K + 1) g) (hk : k ≤ K) (hi : i ≤ k) (hx : x < g) :
    extVisibilityReplace x k i < g := by
  have hle : extVisibilityReplace x k i ≤ g :=
    extVisibilityReplace_le_of_le_selfVis hi (hg.mono (by omega)) hx.le
  refine lt_of_le_of_ne hle ?_
  intro heq
  by_cases hsame : extVisibilityReplace x k i = x
  · exact hx.ne (hsame.symm.trans heq)
  obtain ⟨a, rfl, ha⟩ := exists_of_extVisibilityReplace_ne hsame
  rw [extVisibilityReplace_of_finitePart_lt ha] at heq
  have hfp := (selfVis_ofOrd_iff.mp (heq.symm ▸ hg))
  rw [finitePart_limitPart_add_nat] at hfp
  omega

/-- One grade of slack makes every bounded replacement commute with the paste, with
no agreement of its two inputs. Bottom and top cuts are included. -/
theorem evr_paste_of_slack {g q s : ExtOrd} {K k i : ℕ}
    (hg : SelfVis (K + 1) g) (hk : k ≤ K) (hi : i ≤ k) :
    extVisibilityReplace (paste g q s) k i =
      paste g (extVisibilityReplace q k i) (extVisibilityReplace s k i) := by
  apply map_paste_of_strict_cut _ (fun _ _ h => evr_mono h hi)
  · exact evr_eq_self_of_selfVis (hg.mono (by omega)) i
  · intro x hx
    exact evr_lt_of_slack_cut hg hk hi hx

/-- The useful part of controller capping, with the bottom-controller case included:
an exact shifter with bounded-threshold commutation and all-threshold bottom propagation. -/
theorem exists_exact_capped_shifter {D : Type*} {grade : D → ℕ} {E p : D → ExtOrd} {c : D}
    (hmax : ∀ d, grade d ≤ grade c) (hvis : SelfVis (grade c) (p c))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c))) :
    ∃ τ : ExtOrd → ExtOrd, τ ⊥ = ⊥ ∧ Monotone τ ∧
      (∀ d, τ (E d) = min (p d) (p c)) ∧
      (∀ x k i, k ≤ grade c → i ≤ k →
        τ (extVisibilityReplace x k i) = extVisibilityReplace (τ x) k i) ∧
      (∀ x, τ x = ⊥ → ∀ k i, i ≤ k → τ (extVisibilityReplace x k i) = ⊥) := by
  by_cases hb : p c = ⊥
  · refine ⟨fun _ => ⊥, rfl, monotone_const, ?_, ?_, ?_⟩
    · intro d
      simp only [hb, min_bot_right]
    · intro x k i _ _
      exact (extVisibilityReplace_bot k i).symm
    · intros
      rfl
  · obtain ⟨_, τ, _, _, hbot, hmono, _, _, _, hsrc, hcomm, hprop⟩ :=
      exists_cappedWitness grade E p c hmax hvis hb hloc
    exact ⟨τ, hbot, hmono, hsrc, hcomm, hprop⟩

/-- Two actual controller localities paste to a full faithful locality at a slack cut.
This includes clause 5 at every threshold, not just a bounded check or a row equation.
No agreement between the two labellings is assumed. -/
theorem TransformsTo.paste_capped_of_slack {D : Type*} {grade : D → ℕ}
    {E q s : D → ExtOrd} {c : D} {g : ExtOrd}
    (hmax : ∀ d, grade d ≤ grade c)
    (hqvis : SelfVis (grade c) (q c)) (hsvis : SelfVis (grade c) (s c))
    (hg : SelfVis (grade c + 1) g)
    (hq : TransformsTo grade E (fun d => min (q d) (q c)))
    (hs : TransformsTo grade E (fun d => min (s d) (s c))) :
    TransformsTo grade E (fun d => min (paste g (q d) (s d)) (paste g (q c) (s c))) := by
  obtain ⟨τq, hqb, hqm, hqs, hqc, hqp⟩ := exists_exact_capped_shifter hmax hqvis hq
  obtain ⟨τs, hsb, hsm, hss, hsc, hsp⟩ := exists_exact_capped_shifter hmax hsvis hs
  refine ⟨stepSuppressor (grade c), fun x => paste g (τq x) (τs x),
    stepSuppressor_antitone _, stepSuppressor_selfVis _, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [hqb, hsb, paste_bot]
  · exact fun _ _ h => paste_mono (hqm h) (hsm h)
  · intro x k hact i hi
    dsimp only at hact ⊢
    by_cases hk : k ≤ grade c
    · rw [hqc x k i hk hi, hsc x k i hk hi, evr_paste_of_slack hg hk hi]
    · rw [stepSuppressor_of_gt (not_le.mp hk)] at hact
      have hb := le_bot_iff.mp hact
      rw [hb, extVisibilityReplace_bot]
      exact paste_coupling (fun h => hqp x h k i hi) (fun h => hsp x h k i hi) hb
  · intro d
    dsimp only
    rw [stepSuppressor_of_le (hmax d), min_top_right, hqs, hss, paste_min]

section Locality

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} {q s : D.below BJ → ExtOrd}

/-- On an arbitrary scheme, all localities of two respecting labellings paste at a
slack cut. Availability of the pasted labelling is deliberately not asserted here. -/
theorem RespectsSemanticsBelow.locality_paste_of_slack
    (hq : RespectsSemanticsBelow sem BJ q) (hs : RespectsSemanticsBelow sem BJ s)
    {g : ExtOrd} (hg : SelfVis (BJ.2 + 1) g) (c : D.below BJ) :
    TransformsTo (fun d : D.below (D.cell c.1) => D.grade d.1) (sem.E c.1)
      (fun d => min (paste g (q (CellScheme.below.incl c d)) (s (CellScheme.below.incl c d)))
        (paste g (q c) (s c))) := by
  let c₀ : D.below (D.cell c.1) := ⟨c.1, GradedLe.refl _⟩
  have hqvis : SelfVis (D.grade c.1) (q (CellScheme.below.incl c c₀)) :=
    (hq.orderly c).symm
  have hsvis : SelfVis (D.grade c.1) (s (CellScheme.below.incl c c₀)) :=
    (hs.orderly c).symm
  exact TransformsTo.paste_capped_of_slack (c := c₀) (fun d => d.2.2) hqvis hsvis
    (hg.mono (Nat.add_le_add_right c.2.2 1)) (hq.locality c) (hs.locality c)

/-- At a slack cut, the precise remaining law is overlap of high-controller sets.
The first labelling's availability handles sources below the cut and sources whose
second value is at most the cut. Only the high/high case needs a joint witness.
This is an equivalence on actual respecting inputs, not a scalar sufficiency assumption. -/
theorem RespectsSemanticsBelow.paste_iff_high_controller_overlap
    (hq : RespectsSemanticsBelow sem BJ q) (hs : RespectsSemanticsBelow sem BJ s)
    {g : ExtOrd} (hg : SelfVis (BJ.2 + 1) g) :
    RespectsSemanticsBelow sem BJ (fun d => paste g (q d) (s d)) ↔
      ∀ a b : D.below BJ, D.scope a.1 ⊆ D.scope b.1 → D.grade a.1 = D.grade b.1 →
        g ≤ q a → g < s a →
        ∃ c : D.below BJ, D.cell c.1 = D.cell b.1 ∧ g ≤ q c ∧ s a ≤ s c := by
  constructor
  · intro hp a b hab hgrade hqa hsa
    obtain ⟨c, hc, hle⟩ := hp.availability a b hab hgrade
    exact ⟨c, hc, (paste_le_iff_high_overlap hqa hsa).mp hle⟩
  · intro hoverlap
    refine ⟨?_, fun c => hq.locality_paste_of_slack hs hg c, ?_⟩
    · intro d
      exact (paste_visible (hg.mono (d.2.2.trans (Nat.le_succ _)))
        (hq.orderly d).symm (hs.orderly d).symm).symm
    · intro a b hab hgrade
      obtain ⟨c, hc, hqle⟩ := hq.availability a b hab hgrade
      by_cases hqa : q a < g
      · refine ⟨c, hc, ?_⟩
        calc
          paste g (q a) (s a) = paste g (q a) ⊥ := by rw [paste_of_lt hqa, paste_of_lt hqa]
          _ ≤ paste g (q c) (s c) := paste_mono hqle bot_le
      · have hga : g ≤ q a := le_of_not_gt hqa
        by_cases hsa : s a ≤ g
        · refine ⟨c, hc, ?_⟩
          rw [paste_of_ge hga, max_eq_left hsa, paste_of_ge (hga.trans hqle)]
          exact le_max_left _ _
        · obtain ⟨d, hd, hqd, hsd⟩ := hoverlap a b hab hgrade hga (lt_of_not_ge hsa)
          exact ⟨d, hd, (paste_le_iff_high_overlap hga (lt_of_not_ge hsa)).mpr ⟨hqd, hsd⟩⟩

/-- A common dominating controller for the two inputs supplies the remaining availability
law. This is an explicit sufficient condition, not inferred from separate availability. -/
theorem RespectsSemanticsBelow.paste_of_joint_domination
    (hq : RespectsSemanticsBelow sem BJ q) (hs : RespectsSemanticsBelow sem BJ s)
    {g : ExtOrd} (hg : SelfVis (BJ.2 + 1) g)
    (hjoint : ∀ a b : D.below BJ, D.scope a.1 ⊆ D.scope b.1 → D.grade a.1 = D.grade b.1 →
      ∃ c : D.below BJ, D.cell c.1 = D.cell b.1 ∧ q a ≤ q c ∧ s a ≤ s c) :
    RespectsSemanticsBelow sem BJ (fun d => paste g (q d) (s d)) := by
  apply (hq.paste_iff_high_controller_overlap hs hg).mpr
  intro a b hab hgrade hqa _
  obtain ⟨c, hc, hqle, hsle⟩ := hjoint a b hab hgrade
  exact ⟨c, hc, hqa.trans hqle, hsle⟩

/-- If a graded index has at most one cell in the lower set, the two availability
witnesses must be the same cell. No uniqueness assumption is made elsewhere. -/
theorem RespectsSemanticsBelow.paste_of_index_injective
    (hq : RespectsSemanticsBelow sem BJ q) (hs : RespectsSemanticsBelow sem BJ s)
    {g : ExtOrd} (hg : SelfVis (BJ.2 + 1) g)
    (hinj : Function.Injective (fun d : D.below BJ => D.cell d.1)) :
    RespectsSemanticsBelow sem BJ (fun d => paste g (q d) (s d)) := by
  apply hq.paste_of_joint_domination hs hg
  intro a b hab hgrade
  obtain ⟨c, hc, hqle⟩ := hq.availability a b hab hgrade
  obtain ⟨d, hd, hsle⟩ := hs.availability a b hab hgrade
  have hcd : c = d := hinj (hc.trans hd.symm)
  exact ⟨c, hc, hqle, hcd ▸ hsle⟩

end Locality

/-- On the fixed repaired three-level semantics, all seven-parameter legality laws
survive arbitrary pasting at a grade-four-visible cap. At a merely grade-three-visible
cap, use the shared-proper-probe theorem instead. -/
theorem legal_paste_of_slack {g v x₀ x₁ H z₁ z₂ w v' x₀' x₁' H' z₁' z₂' w' : ExtOrd}
    (L : Legal₃ v x₀ x₁ H z₁ z₂ w) (S : Legal₃ v' x₀' x₁' H' z₁' z₂' w')
    (hg : SelfVis 4 g) :
    Legal₃ (paste g v v') (paste g x₀ x₀') (paste g x₁ x₁') (paste g H H') (paste g z₁ z₁')
      (paste g z₂ z₂') (paste g w w') := by
  have hg1 : SelfVis 1 g := hg.mono (by decide)
  have hg2 : SelfVis 2 g := hg.mono (by decide)
  have hg3 : SelfVis 3 g := hg.mono (by decide)
  have htwo : Legal₂ (paste g v v') (paste g x₀ x₀') (paste g x₁ x₁') (paste g H H') := by
    refine ⟨paste_visible hg1 L.two.visP S.two.visP,
      paste_mono L.two.vle S.two.vle, paste_mono L.two.le01 S.two.le01,
      paste_coupling L.two.coup S.two.coup,
      paste_visible hg1 L.two.vis0 S.two.vis0, paste_visible hg1 L.two.vis1 S.two.vis1,
      paste_visible hg2 L.two.visH S.two.visH, paste_mono L.two.Hle S.two.Hle, ?_⟩
    rw [← paste_min]
    exact paste_visible hg2 L.two.vismin S.two.vismin
  refine ⟨htwo, paste_mono L.z12 S.z12, paste_mono L.z2x S.z2x,
    paste_mono L.z2w S.z2w, paste_mono L.wH S.wH,
    paste_visible hg3 L.vis1 S.vis1, paste_visible hg3 L.vis2 S.vis2,
    paste_visible hg3 L.visw S.visw, ?_, ?_, ?_,
    paste_coupling L.coup₃ S.coup₃, ?_⟩
  · rw [← paste_min]
    exact paste_visible hg3 L.vismin S.vismin
  · rw [L.orbit, S.orbit, ← evr_paste_of_slack hg (by decide) le_rfl, paste_min]
  · rw [← paste_min, evr_paste_of_slack hg (by decide) (by decide), L.fix, S.fix]
  · rw [← paste_min]
    exact paste_coupling L.coup₄ S.coup₄

/-- The fixed repaired scheme needs no shared-probe hypothesis at a slack cut;
its existing necessity and sufficiency theorems discharge availability as well. -/
theorem respectsR_paste_of_slack {q s : D₂.below (Finset.univ, 3) → ExtOrd}
    (hq : RespectsSemanticsBelow rowsR (Finset.univ, 3) q)
    (hs : RespectsSemanticsBelow rowsR (Finset.univ, 3) s)
    (sc : D₂.below (Finset.univ, 3)) (hsc : IsProper sc.1) (hgrade : D₂.grade sc.1 = 1)
    (s1 : D₂.below (Finset.univ, 3)) (hs1 : IsProper s1.1) (hs1c : D₂.cell s1.1 = ({1}, 1))
    {g : ExtOrd} (hg : SelfVis 4 g) :
    RespectsSemanticsBelow rowsR (Finset.univ, 3) (fun d => paste g (q d) (s d)) := by
  obtain ⟨Q, LQ⟩ := shape_legal_of_respectsR hq sc hsc hgrade s1 hs1 hs1c
  obtain ⟨S, LS⟩ := shape_legal_of_respectsR hs sc hsc hgrade s1 hs1 hs1c
  exact respects_of_shape₃ (legal_paste_of_slack LQ LS hg) (shape_paste Q S g)

/-- The slack assumption cannot be dropped from the operation-commutation theorem.
Here the cut is grade-three visible, but replacement reaches it from strictly below. -/
theorem evr_paste_boundary_counterexample :
    SelfVis 3 (ofOrd 3) ∧
      extVisibilityReplace (paste (ofOrd 3) (ofOrd 1) ⊤) 3 3 ≠
        paste (ofOrd 3) (extVisibilityReplace (ofOrd 1) 3 3) (extVisibilityReplace ⊤ 3 3) := by
  have h13 : ofOrd 1 < ofOrd 3 := by norm_num
  have hfp : finitePart (1 : Ordinal.{0}) < 3 := by
    simpa using (show finitePart ((1 : ℕ) : Ordinal.{0}) < 3 by
      rw [Value.finitePart_natCast]
      decide)
  have hr : extVisibilityReplace (ofOrd 1) 3 3 = ofOrd 3 := by
    have hl : limitPart (1 : Ordinal.{0}) = 0 := by simpa using Value.limitPart_natCast 1
    rw [extVisibilityReplace_of_finitePart_lt hfp]
    simp only [hl, zero_add, Nat.cast_ofNat]
  refine ⟨selfVis_ofOrd_iff.mpr ?_, ?_⟩
  · have hf3 : finitePart (3 : Ordinal.{0}) = 3 := by simpa using Value.finitePart_natCast 3
    exact hf3.ge
  · rw [paste_of_lt h13, hr, extVisibilityReplace_top, paste_of_ge le_rfl, max_eq_right le_top]
    exact ofOrd_ne_top 3

/-- Separate witnesses for existential domination need not survive a paste. This is
an order-theoretic regression, not a claim that these tuples respect some semantics. -/
theorem separate_domination_does_not_paste :
    let q : Fin 3 → ℕ := ![5, 5, 0]
    let s : Fin 3 → ℕ := ![6, 0, 6]
    (q 0 ≤ q 1 ∨ q 0 ≤ q 2) ∧ (s 0 ≤ s 1 ∨ s 0 ≤ s 2) ∧
      ¬ (paste 4 (q 0) (s 0) ≤ paste 4 (q 1) (s 1) ∨
        paste 4 (q 0) (s 0) ≤ paste 4 (q 2) (s 2)) := by
  decide

end VaughtConjecture.Knight
