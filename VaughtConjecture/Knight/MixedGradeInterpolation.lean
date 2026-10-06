/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ControllerPrefixFamily

/-! # Mixed-grade interpolation: orbit blocks, not just source order

A grade-two witness can interpolate one grade-one-visible value followed by an arbitrary
finite monotone list of grade-two-visible values. The source template is fixed in advance:
`ω + 1` for the low probe and `ω * (i + 2) + 2` for the high probes. The witness is one orbit
strip and a finite maximum of limit steps. Bottom, top, and repeated high values are allowed.

This does not assemble a controller family or establish bountifulness. In particular, separate
source blocks cannot be used indiscriminately: equal capped targets that are not visible at
the controller grade must come from the same source block. The latter is a necessary law for
every actual maximal-grade controller locality, not just the interpolation template.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-- A monotone map commuting with self-replacement can identify two separated source blocks
only at a self-visible output. -/
theorem selfVis_of_equal_images_separated_blocks {τ : ExtOrd → ExtOrd} {K : ℕ}
    (hm : Monotone τ)
    (hc : ∀ x, τ (extVisibilityReplace x K K) = extVisibilityReplace (τ x) K K)
    {a b : Ordinal.{0}} (hab : limitPart a < limitPart b)
    (he : τ (ofOrd a) = τ (ofOrd b)) : SelfVis K (τ (ofOrd a)) := by
  have hsrc : extVisibilityReplace (ofOrd a) K K ≤ ofOrd b := by
    by_cases ha : finitePart a < K
    · rw [extVisibilityReplace_of_finitePart_lt ha, ofOrd_le_ofOrd]
      exact (limitPart_add_nat_le_of_lt hab K).trans (limitPart_le b)
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp ha), ofOrd_le_ofOrd,
        ← decomposition a]
      exact (limitPart_add_nat_le_of_lt hab (finitePart a)).trans (limitPart_le b)
  exact le_antisymm (by simpa only [hc, ← he] using hm hsrc)
    (le_extVisibilityReplace_self _ _)

/-- Equal non-visible capped probes must share a source block. Changing finite offsets alone
cannot rescue a source template that has put them in distinct blocks. -/
theorem TransformsTo.source_blocks_eq_of_equal_nonvisible {D : Type*} {grade : D → ℕ}
    {E p : D → ExtOrd} {c d e : D} (hmax : ∀ x, grade x ≤ grade c)
    (hvis : SelfVis (grade c) (p c))
    (h : TransformsTo grade E (fun x => min (p x) (p c)))
    {a b : Ordinal.{0}} (hd : E d = ofOrd a) (he : E e = ofOrd b)
    (heq : min (p d) (p c) = min (p e) (p c))
    (hnv : ¬ SelfVis (grade c) (min (p d) (p c))) : limitPart a = limitPart b := by
  obtain ⟨τ, _, hm, hs, hc, _⟩ := exists_exact_capped_shifter hmax hvis h
  have htd : τ (ofOrd a) = min (p d) (p c) := hd ▸ hs d
  have hte : τ (ofOrd b) = min (p e) (p c) := he ▸ hs e
  have ht : τ (ofOrd a) = τ (ofOrd b) := htd.trans (heq.trans hte.symm)
  rcases lt_trichotomy (limitPart a) (limitPart b) with hab | hab | hab
  · exact False.elim (hnv (htd ▸ selfVis_of_equal_images_separated_blocks hm
      (fun x => hc x _ _ le_rfl le_rfl) hab ht))
  · exact hab
  · exact False.elim (hnv ((hte.trans heq.symm) ▸ selfVis_of_equal_images_separated_blocks hm
      (fun x => hc x _ _ le_rfl le_rfl) hab ht.symm))

/-- At a non-visible ordinal output, bounded replacement commutation determines the source's
finite part exactly, not just an upper bound on it. -/
theorem finitePart_eq_of_nonvisible_image {τ : ExtOrd → ExtOrd} {K : ℕ}
    (hc : ∀ x i, i ≤ K →
      τ (extVisibilityReplace x K i) = extVisibilityReplace (τ x) K i)
    {a t : Ordinal.{0}} (ht : τ (ofOrd a) = ofOrd t) (hft : finitePart t < K) :
    finitePart a = finitePart t := by
  have hfa : finitePart a < K := by
    by_contra hfa
    have hh := hc (ofOrd a) K le_rfl
    rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hfa), ht] at hh
    exact (not_le_of_gt hft) (selfVis_ofOrd_iff.mp hh.symm)
  have hh := hc (ofOrd a) (finitePart a) hfa.le
  rw [extVisibilityReplace_of_finitePart_lt hfa, decomposition a, ht,
    extVisibilityReplace_of_finitePart_lt hft, ofOrd_inj] at hh
  have hf := congrArg finitePart hh
  rw [finitePart_limitPart_add_nat] at hf
  exact hf.symm

/-- A non-visible capped output has a singleton source fibre. Thus a permutation family that
keeps distinct probes in distinct source positions cannot handle all mixed-grade ties. -/
theorem TransformsTo.source_eq_of_equal_nonvisible {D : Type*} {grade : D → ℕ}
    {E p : D → ExtOrd} {c d e : D} (hmax : ∀ x, grade x ≤ grade c)
    (hvis : SelfVis (grade c) (p c))
    (h : TransformsTo grade E (fun x => min (p x) (p c)))
    {a b t : Ordinal.{0}} (hd : E d = ofOrd a) (he : E e = ofOrd b)
    (hdt : min (p d) (p c) = ofOrd t) (het : min (p e) (p c) = ofOrd t)
    (hnt : finitePart t < grade c) : E d = E e := by
  have hnv : ¬ SelfVis (grade c) (min (p d) (p c)) := by
    rw [hdt, selfVis_ofOrd_iff]
    exact not_le_of_gt hnt
  have hblock := TransformsTo.source_blocks_eq_of_equal_nonvisible hmax hvis h hd he
    (hdt.trans het.symm) hnv
  obtain ⟨τ, _, _, hs, hc, _⟩ := exists_exact_capped_shifter hmax hvis h
  have hta : τ (ofOrd a) = ofOrd t := (hd ▸ hs d).trans hdt
  have htb : τ (ofOrd b) = ofOrd t := (he ▸ hs e).trans het
  have hfa := finitePart_eq_of_nonvisible_image (fun x i hi => hc x _ i le_rfl hi) hta hnt
  have hfb := finitePart_eq_of_nonvisible_image (fun x i hi => hc x _ i le_rfl hi) htb hnt
  rw [hd, he, ofOrd_inj, ← decomposition a, ← decomposition b, hblock, hfa, hfb]

/-- Finite pointwise suprema preserve witnesses with a common suppressor, provided the empty
supremum has a witness too. This is a construction tool, not composition of transformations. -/
theorem Witness.finset_sup {ι : Type*} {g : ℕ → ExtOrd} {f : ι → ExtOrd → ExtOrd}
    (hbot : Witness g (fun _ => ⊥)) (s : Finset ι) (hf : ∀ i ∈ s, Witness g (f i)) :
    Witness g (fun a => s.sup (fun i => f i a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty] using hbot
  | @insert i s hi ih =>
    simpa only [Finset.sup_insert] using
      (hf i (Finset.mem_insert_self _ _)).max
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

namespace MixedGradeInterpolation

/-- The constant-bottom shifter is a witness at every grade. -/
theorem zero_witness (K : ℕ) : Witness (gTop K) (fun _ => ⊥) where
  anti := (witness_id K).anti
  vis := (witness_id K).vis
  bot := rfl
  mono := monotone_const
  clause5 := by intros; exact (extVisibilityReplace_bot _ _).symm

/-- The grade-two sources have distinct blocks and finite part two. -/
noncomputable def highSource (i : ℕ) : ExtOrd :=
  ofOrd (Ordinal.omega0 * ((i + 2 : ℕ) : Ordinal) + 2)

theorem highSource_visible (i : ℕ) : SelfVis 2 (highSource i) := by
  rw [highSource, selfVis_ofOrd_iff]
  simpa using (finitePart_mul_add (i + 2) 2).ge

theorem highSource_coded (i : ℕ) : IsCodedLabel 2 (highSource i) :=
  Or.inr ⟨i + 2, 2, by decide, rfl⟩

private theorem source_lt_cut {i n k : ℕ} (h : i < n) :
    ofOrd (Ordinal.omega0 * (i : Ordinal) + k) <
      ofOrd (Ordinal.omega0 * (n : Ordinal)) :=
  ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr h) k)

private theorem cut_le_source {i n k : ℕ} (h : n ≤ i) :
    ofOrd (Ordinal.omega0 * (n : Ordinal)) ≤
      ofOrd (Ordinal.omega0 * (i : Ordinal) + k) :=
  ofOrd_le_ofOrd.mpr ((mul_le_mul_right (Nat.cast_le.mpr h) _).trans le_self_add)

/-- One orbit strip plus an arbitrary finite number of visible plateaux. -/
noncomputable def shifter {n : ℕ} (m : ExtOrd) (v : Fin (n + 1) → ExtOrd) (a : ExtOrd) :
    ExtOrd := max (stripShifter m (v 0) a)
      (Finset.univ.sup (fun i : Fin (n + 1) => stepShifter (i.val + 2) ⊥ (v i) a))

theorem shifter_witness {n : ℕ} {m : ExtOrd} {v : Fin (n + 1) → ExtOrd}
    (hm : SelfVis 1 m) (hv : ∀ i, SelfVis 2 (v i)) (hmv : m ≤ v 0) :
    Witness (gTop 2) (shifter m v) :=
  (Witness.strip hm (hv 0) hmv).max
    (Witness.finset_sup (zero_witness 2) Finset.univ
      (fun i _ => Witness.stepLimit 2 (i.val + 2) bot_le (extVisibilityReplace_bot _ _) (hv i)))

theorem shifter_low {n : ℕ} {m : ExtOrd} {v : Fin (n + 1) → ExtOrd}
    (hm : SelfVis 1 m) : shifter m v (BranchAvailability.source 1) = m := by
  have hs : stripShifter m (v 0) (BranchAvailability.source 1) = m := by
    simpa [v₀, BranchAvailability.source] using (strip_v₀ (c := v 0) hm)
  have hsteps : Finset.univ.sup (fun i : Fin (n + 1) =>
      stepShifter (i.val + 2) ⊥ (v i) (BranchAvailability.source 1)) = ⊥ := by
    apply le_bot_iff.mp
    apply Finset.sup_le
    intro i _
    have hc : BranchAvailability.source 1 <
        ofOrd (Ordinal.omega0 * ((i.val + 2 : ℕ) : Ordinal)) := by
      simpa [BranchAvailability.source] using
        source_lt_cut (k := 1) (by omega : 1 < i.val + 2)
    have hz : stepShifter (i.val + 2) ⊥ (v i) (BranchAvailability.source 1) = ⊥ :=
      stepShifter_of_lt (show BranchAvailability.source 1 ≠ ⊥ from ofOrd_ne_bot _) hc
    exact hz.le
  rw [shifter, hs, hsteps, max_eq_left bot_le]

theorem shifter_high {n : ℕ} {m : ExtOrd} {v : Fin (n + 1) → ExtOrd}
    (hv : Monotone v) (j : Fin (n + 1)) : shifter m v (highSource j.val) = v j := by
  have hs : stripShifter m (v 0) (highSource j.val) = v 0 :=
    strip_of_ge (cut_le_source (by omega : 2 ≤ j.val + 2))
  have hself : stepShifter (j.val + 2) ⊥ (v j) (highSource j.val) = v j :=
    stepShifter_of_ge (cut_le_source le_rfl)
  rw [shifter, hs]
  apply le_antisymm
  · apply max_le (hv (Fin.zero_le j))
    apply Finset.sup_le
    intro i _
    by_cases hij : i ≤ j
    · have hc : ofOrd (Ordinal.omega0 * ((i.val + 2 : ℕ) : Ordinal)) ≤ highSource j.val := by
        simpa [highSource] using
          cut_le_source (k := 2) (by omega : i.val + 2 ≤ j.val + 2)
      rw [stepShifter_of_ge hc]
      exact hv hij
    · have hc : highSource j.val < ofOrd (Ordinal.omega0 * ((i.val + 2 : ℕ) : Ordinal)) := by
        simpa [highSource] using
          source_lt_cut (k := 2) (by omega : j.val + 2 < i.val + 2)
      have hz : stepShifter (i.val + 2) ⊥ (v i) (highSource j.val) = ⊥ :=
        stepShifter_of_lt (show highSource j.val ≠ ⊥ from ofOrd_ne_bot _) hc
      rw [hz]
      exact bot_le
  · calc v j = stepShifter (j.val + 2) ⊥ (v j) (highSource j.val) := hself.symm
         _ ≤ Finset.univ.sup (fun i : Fin (n + 1) =>
             stepShifter (i.val + 2) ⊥ (v i) (highSource j.val)) :=
           Finset.le_sup (f := fun i : Fin (n + 1) =>
             stepShifter (i.val + 2) ⊥ (v i) (highSource j.val)) (Finset.mem_univ j)
         _ ≤ _ := le_max_right _ _

/-- A fixed mixed-grade row, independent of the output values. -/
noncomputable def sourceRow {n : ℕ} : Option (Fin (n + 1)) → ExtOrd
  | none => BranchAvailability.source 1
  | some i => highSource i.val

/-- The low probe has grade one and every remaining probe has grade two. -/
def grade {n : ℕ} : Option (Fin (n + 1)) → ℕ
  | none => 1
  | some _ => 2

/-- The same source row is sharply coded at owner grade two at every length. -/
theorem sourceRow_coded {n : ℕ} (d : Option (Fin (n + 1))) :
    IsCodedLabel 2 (sourceRow d) := by
  cases d with
  | none => exact BranchAvailability.source_coded 1 2
  | some i => exact highSource_coded i.val

/-- Its source labels are orderly at their individual probe grades. -/
theorem sourceRow_orderly {n : ℕ} (d : Option (Fin (n + 1))) :
    SelfVis (grade d) (sourceRow d) := by
  cases d with
  | none => exact BranchAvailability.source_visible 1
  | some i => exact highSource_visible i.val

/-- Uniform interpolation of arbitrarily many ordered high classes, including ties and
bottom/top. This proves one faithful row transformation, not joint controller consistency. -/
theorem transforms_chain {n : ℕ} {m : ExtOrd} {v : Fin (n + 1) → ExtOrd}
    (hm : SelfVis 1 m) (hv : ∀ i, SelfVis 2 (v i)) (hord : Monotone v) (hmv : m ≤ v 0) :
    TransformsTo grade sourceRow (fun d => d.elim m v) := by
  apply (shifter_witness hm hv hmv).transformsTo
  intro d
  cases d with
  | none => simp [sourceRow, grade, shifter_low hm, gTop]
  | some i => simp [sourceRow, grade, shifter_high hord, gTop]

/-- The interpolable chains are closed under cap pasting already at visibility two. No slack
grade or source-level compatibility condition is needed for this particular target class. -/
theorem transforms_pasted_chain {n : ℕ} {γ m m' : ExtOrd}
    {v v' : Fin (n + 1) → ExtOrd} (hγ : SelfVis 2 γ)
    (hm : SelfVis 1 m) (hm' : SelfVis 1 m')
    (hv : ∀ i, SelfVis 2 (v i)) (hv' : ∀ i, SelfVis 2 (v' i))
    (hord : Monotone v) (hord' : Monotone v') (hmv : m ≤ v 0) (hmv' : m' ≤ v' 0) :
    TransformsTo grade sourceRow
      (fun d => paste γ (d.elim m v) (d.elim m' v')) := by
  have h := transforms_chain (paste_visible (hγ.mono (by decide)) hm hm')
    (fun i => paste_visible hγ (hv i) (hv' i))
    (fun _ _ hij => paste_mono (hord hij) (hord' hij)) (paste_mono hmv hmv')
  convert h using 1
  funext d
  cases d <;> rfl

/-! ## A non-vacuous mixed-grade tie regression -/

/-- Two low probes and a grade-two controller. This is a row carrier, not a support plan. -/
def tieGrade (d : Fin 3) : ℕ := if d = 2 then 2 else 1

/-- The positive repair shares the low source, while the high source stays in a new block. -/
noncomputable def tiedSource (d : Fin 3) : ExtOrd :=
  if d = 2 then highSource 0 else BranchAvailability.source 1

noncomputable def tiedTarget (m c : ExtOrd) (d : Fin 3) : ExtOrd := if d = 2 then c else m

/-- Every visible low/high pair is realized by the merged-source row, including a low value
that is not grade-two-visible. -/
theorem tied_locality {m c : ExtOrd} (hm : SelfVis 1 m) (hc : SelfVis 2 c) (hmc : m ≤ c) :
    TransformsTo tieGrade tiedSource (tiedTarget m c) := by
  apply (Witness.strip hm hc hmc).transformsTo
  intro d
  by_cases hd : d = 2
  · subst d
    have hs : stripShifter m c (highSource 0) = c :=
      strip_of_ge (cut_le_source (by decide : 2 ≤ 0 + 2))
    simp [tieGrade, tiedSource, tiedTarget, hs, gTop]
  · have hs : stripShifter m c (BranchAvailability.source 1) = m := by
      simpa [v₀, BranchAvailability.source] using (strip_v₀ (c := c) hm)
    simp [tieGrade, tiedSource, tiedTarget, hd, hs, gTop]

/-- Keeping two low sources in distinct blocks cannot realize an equal non-visible pair,
however the controller source is chosen. This is an actual faithful-locality no-go. -/
theorem no_separated_tie {E : Fin 3 → ExtOrd} {a b t : Ordinal.{0}} {c : ExtOrd}
    (h0 : E 0 = ofOrd a) (h1 : E 1 = ofOrd b) (hab : limitPart a ≠ limitPart b)
    (ht : finitePart t < 2) (hc : SelfVis 2 c) (htc : ofOrd t ≤ c) :
    ¬ TransformsTo tieGrade E (tiedTarget (ofOrd t) c) := by
  intro h
  have hcap : (fun d => min (tiedTarget (ofOrd t) c d) (tiedTarget (ofOrd t) c 2)) =
      tiedTarget (ofOrd t) c := by
    funext d
    by_cases hd : d = 2 <;> simp [tiedTarget, hd, min_eq_left htc]
  have ht' : ¬ SelfVis (tieGrade 2) (min (tiedTarget (ofOrd t) c 0)
      (tiedTarget (ofOrd t) c 2)) := by
    simpa [tieGrade, tiedTarget, min_eq_left htc, selfVis_ofOrd_iff] using not_le_of_gt ht
  apply hab
  apply TransformsTo.source_blocks_eq_of_equal_nonvisible
    (c := 2) (d := 0) (e := 1) (p := tiedTarget (ofOrd t) c)
    (by intro x; by_cases hx : x = 2 <;> simp [tieGrade, hx])
    (by simpa [tieGrade, tiedTarget] using hc) (hcap ▸ h) h0 h1
  · simp [tiedTarget]
  · exact ht'

end MixedGradeInterpolation
end VaughtConjecture.Knight
