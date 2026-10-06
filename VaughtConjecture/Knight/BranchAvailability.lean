/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SlackCutPasting

/-! # Branching availability and face-aware retuning

A complete, coded, consistent and bountiful binary scheme with two controllers at the
same graded index separates locality from availability. Its controller labels `a,b`
jointly dominate a proper label `max a b`.

Two actual respecting labellings have a non-respecting cellwise paste, even at a cut
with an extra grade of visibility and agreement on both proper cells. More strongly,
no output can preserve every accidentally agreeing coordinate and retain global capped
agreement. The protected collection in that no-go is not a face.

Face-aware retuning succeeds: change the unprotected controller choices along with the
proper value. `paste_retunes_attained_cover` is the index-independent order lemma; the
binary instance gives unrestricted bountifulness of this regression domain. It does not
assert semantic sufficiency for arbitrary controller families or solve mixed-row sections.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd VaughtConjecture.AmalgamationPlan

/-- Retune an attained upper bound across any family of branches. No branch is chosen:
all are retuned, and any old maximizing branch attains the prescribed new value.
This is order algebra, not a semantic extension theorem for arbitrary row families. -/
theorem paste_retunes_attained_cover {I α : Type*} [LinearOrder α]
    {a : I → α} {g v v' : α} (hbound : ∀ i, a i ≤ v) (hattain : ∃ i, a i = v)
    (hagree : min v g = min v' g) :
    (∀ i, paste g (a i) v' ≤ v') ∧ (∃ i, paste g (a i) v' = v') ∧
      (∀ i, min (paste g (a i) v') g = min (a i) g) := by
  have hv : paste g v v' = v' := paste_eq_of_agree hagree
  refine ⟨fun i => ?_, ?_, fun i => paste_cap _ _ _⟩
  · exact (paste_mono (hbound i) le_rfl).trans_eq hv
  · obtain ⟨i, hi⟩ := hattain
    exact ⟨i, by rw [hi, hv]⟩

namespace BranchAvailability

def indices (d : Fin 5) : Finset (Fin 2) × ℕ :=
  match d.val with
  | 0 => ({0}, 1)
  | 1 => ({1}, 1)
  | 4 => (Finset.univ, 2)
  | _ => (Finset.univ, 1)

theorem binary_plan : Plan.IsPlan (Finset.univ : Finset (Fin 2))
    {∅, {0}, {1}, Finset.univ} := by
  apply Plan.IsPlan.step (a := 0) (b := 1)
    (Q := {∅, {1}}) (R := {∅, {0}}) (by decide) (by decide) (by decide)
  · convert Plan.IsPlan.singleton (1 : Fin 2) using 1
    decide
  · convert Plan.IsPlan.singleton (0 : Fin 2) using 1
    decide
  all_goals decide

/-- Two proper singletons, two competing full grade-one controllers, and a mute top. -/
abbrev scheme : CellScheme (ι := Fin 2) Finset.univ where
  plan := {∅, {0}, {1}, Finset.univ}
  isPlan := binary_plan
  card := 5
  cell := indices
  cell_mem := by decide

theorem complete : scheme.IsComplete := by
  intro BJ h
  have hlist : ∀ BJ ∈ Plan.gradedPlan scheme.plan, ∃ d : Fin 5, indices d = BJ := by decide
  exact hlist BJ h

/-- A positive source in block `n`, visible at grade one. -/
noncomputable def source (n : ℕ) : ExtOrd := ofOrd (Ordinal.omega0 * n + 1)

theorem source_visible (n : ℕ) : SelfVis 1 (source n) := by
  unfold source
  rw [selfVis_ofOrd_iff]
  simpa using (finitePart_mul_add n 1).ge

theorem source_coded (n k : ℕ) : IsCodedLabel k (source n) :=
  Or.inr ⟨n, 1, by omega, by simp [source]⟩

noncomputable def row (c d : Fin 5) : ExtOrd :=
  match c.val with
  | 0 | 1 => source 1
  | 2 => if d.val = 3 then source 1 else source 2
  | 3 => if d.val = 2 then source 1 else source 2
  | _ => ⊥

private theorem row_cases (c d : Fin 5) :
    row c d = ⊥ ∨ row c d = source 1 ∨ row c d = source 2 := by
  fin_cases c <;> fin_cases d <;> simp [row]

private theorem lower_grade_one {c d : Fin 5} (hc : c ≠ 4)
    (hd : GradedLe (scheme.cell d) (scheme.cell c)) : scheme.grade d = 1 := by
  have h : ∀ c d : Fin 5, c ≠ 4 → GradedLe (scheme.cell d) (scheme.cell c) →
      scheme.grade d = 1 := by unfold GradedLe; decide
  exact h c d hc hd

/-- The two controller rows interchange their low source at the other controller. -/
noncomputable def rows : Semantics scheme where
  E c d := row c d.1
  orderly := by
    intro c ⟨d, hd⟩
    by_cases hc : c = 4
    · subst c
      exact (extVisibilityReplace_bot _ _).symm
    change row c d = extVisibilityReplace (row c d) (scheme.grade d) (scheme.grade d)
    rw [lower_grade_one hc hd]
    rcases row_cases c d with h | h | h
    · rw [h, extVisibilityReplace_bot]
    · rw [h]; exact (source_visible 1).symm
    · rw [h]; exact (source_visible 2).symm

theorem coded : rows.IsCoded := by
  intro c d
  change IsCodedLabel _ (row c d.1)
  rcases row_cases c d.1 with h | h | h
  · exact Or.inl h
  · rw [h]; exact source_coded _ _
  · rw [h]; exact source_coded _ _

/-- Two controller values and their common proper maximum; the top cell stays mute. -/
noncomputable def label (a b : ExtOrd) (d : Fin 5) : ExtOrd :=
  match d.val with
  | 0 | 1 => max a b
  | 2 => a
  | 3 => b
  | _ => ⊥

private theorem step_source_low {a b : ExtOrd} : stepShifter 2 a b (source 1) = a := by
  apply stepShifter_of_lt (ofOrd_ne_bot _)
  rw [ofOrd_lt_ofOrd]
  simp [Ordinal.mul_two]

private theorem step_source_high {a b : ExtOrd} : stepShifter 2 a b (source 2) = b := by
  apply stepShifter_of_ge
  exact ofOrd_le_ofOrd.mpr (le_self_add)

attribute [-simp] CellScheme.cell_eq in
/-- Every pair of visible controller labels gives an actual respecting labelling. -/
theorem label_respects {a b : ExtOrd} (ha : SelfVis 1 a) (hb : SelfVis 1 b) :
    RespectsSemantics rows (label a b) := by
  have hm : SelfVis 1 (max a b) := by
    rcases le_total a b with h | h
    · simpa only [max_eq_right h] using hb
    · simpa only [max_eq_left h] using ha
  refine { orderly := ?_, locality := ?_, availability := ?_ }
  · intro d
    fin_cases d <;> simp_all [label, indices, CellScheme.grade, SelfVis]
  · intro c
    fin_cases c
    · apply (Witness.stepLimit 1 2 (le_refl (max a b)) hm hm).transformsTo
      intro ⟨d, hd⟩
      have heq : d = 0 := by
        have h : ∀ d : Fin 5, GradedLe (scheme.cell d) (scheme.cell 0) → d = 0 := by
          unfold GradedLe; decide
        exact h d hd
      subst d
      simp [rows, row, label, CellScheme.grade, indices, gTop, step_source_low]
    · apply (Witness.stepLimit 1 2 (le_refl (max a b)) hm hm).transformsTo
      intro ⟨d, hd⟩
      have heq : d = 1 := by
        have h : ∀ d : Fin 5, GradedLe (scheme.cell d) (scheme.cell 1) → d = 1 := by
          unfold GradedLe; decide
        exact h d hd
      subst d
      simp [rows, row, label, CellScheme.grade, indices, gTop, step_source_low]
    · apply (Witness.stepLimit 1 2 (min_le_left a b) (selfVis_min' ha hb) ha).transformsTo
      intro ⟨d, hd⟩
      fin_cases d <;> simp_all [rows, row, label, scheme, indices, GradedLe,
        CellScheme.grade, gTop, step_source_low, step_source_high, min_comm]
    · apply (Witness.stepLimit 1 2 (min_le_right a b) (selfVis_min' ha hb) hb).transformsTo
      intro ⟨d, hd⟩
      fin_cases d <;> simp_all [rows, row, label, scheme, indices, GradedLe,
        CellScheme.grade, gTop, step_source_low, step_source_high]
    · simpa [label] using (TransformsTo.to_bot
        (grade := fun d : scheme.below (scheme.cell 4) => scheme.grade d.1) (rows.E 4))
  · intro c d hs hg
    have hbound : ∀ c : Fin 5, label a b c ≤ max a b := by
      intro c; fin_cases c <;> simp [label]
    have hfull : ∃ e : Fin 5, scheme.cell e = (Finset.univ, 1) ∧
        label a b c ≤ label a b e := by
      rcases le_total a b with h | h
      · refine ⟨3, rfl, ?_⟩
        change label a b c ≤ b
        simpa only [max_eq_right h] using hbound c
      · refine ⟨2, rfl, ?_⟩
        change label a b c ≤ a
        simpa only [max_eq_left h] using hbound c
    fin_cases d
    · refine ⟨0, rfl, ?_⟩
      fin_cases c <;> simp_all [indices, CellScheme.scope, CellScheme.grade, label]
    · refine ⟨1, rfl, ?_⟩
      fin_cases c <;> simp_all [indices, CellScheme.scope, CellScheme.grade, label]
    · exact hfull
    · exact hfull
    · refine ⟨4, rfl, ?_⟩
      fin_cases c <;> simp_all [indices, CellScheme.scope, CellScheme.grade, label]

private theorem consistent_of_label (c : Fin 5) {a b : ExtOrd}
    (ha : SelfVis 1 a) (hb : SelfVis 1 b)
    (heq : ∀ d : scheme.below (scheme.cell c), row c d.1 = label a b d.1) :
    RespectsSemanticsBelow rows (scheme.cell c) (rows.E c) := by
  have hfun : rows.E c = fun d => label a b d.1 := funext heq
  rw [hfun]
  exact (label_respects ha hb).toBelow _

attribute [-simp] CellScheme.cell_eq in
/-- The branching rows are consistent, not merely orderly source tables. -/
theorem consistent : rows.IsConsistent := by
  have h12 : source 1 ≤ source 2 := by
    apply ofOrd_le_ofOrd.mpr
    gcongr
    norm_num
  intro c
  fin_cases c
  · apply consistent_of_label 0 (source_visible 1) (source_visible 1)
    intro ⟨d, hd⟩
    have h : ∀ d : Fin 5, GradedLe (scheme.cell d) (scheme.cell 0) → d = 0 := by
      unfold GradedLe; decide
    have hd0 := h d hd
    subst d
    simp [row, label]
  · apply consistent_of_label 1 (source_visible 1) (source_visible 1)
    intro ⟨d, hd⟩
    have h : ∀ d : Fin 5, GradedLe (scheme.cell d) (scheme.cell 1) → d = 1 := by
      unfold GradedLe; decide
    have hd1 := h d hd
    subst d
    simp [row, label]
  · apply consistent_of_label 2 (source_visible 2) (source_visible 1)
    intro ⟨d, hd⟩
    have hg := lower_grade_one (c := 2) (by decide) hd
    fin_cases d <;> simp_all [row, label, indices, CellScheme.grade]
  · apply consistent_of_label 3 (source_visible 1) (source_visible 2)
    intro ⟨d, hd⟩
    have hg := lower_grade_one (c := 3) (by decide) hd
    fin_cases d <;> simp_all [row, label, indices, CellScheme.grade]
  · apply consistent_of_label 4 (a := ⊥) (b := ⊥) (extVisibilityReplace_bot _ _)
      (extVisibilityReplace_bot _ _)
    intro ⟨d, hd⟩
    fin_cases d <;> simp [row, label]

/-- Every respecting labelling must choose one of the two grade-one controllers. -/
theorem proper_le_some {p : Fin 5 → ExtOrd} (hp : RespectsSemantics rows p) :
    p 0 ≤ p 2 ∨ p 0 ≤ p 3 := by
  obtain ⟨e, he, hp⟩ := hp.availability 0 2 (Finset.subset_univ _) rfl
  have h : ∀ e : Fin 5, scheme.cell e = scheme.cell 2 → e = 2 ∨ e = 3 := by decide
  rcases h e he with rfl | rfl
  · exact Or.inl hp
  · exact Or.inr hp

private theorem nat_visible {k n : ℕ} (h : k ≤ n) : SelfVis k (ofOrd (n : Ordinal)) := by
  rw [selfVis_ofOrd_iff, finitePart_natCast]
  exact h

noncomputable def num (n : ℕ) : ExtOrd := ofOrd (n : Ordinal)

@[local simp] private theorem num_le (m n : ℕ) : num m ≤ num n ↔ m ≤ n := by
  simp only [num, ofOrd_le_ofOrd, Nat.cast_le]

@[local simp] private theorem num_lt (m n : ℕ) : num m < num n ↔ m < n := by
  simp only [num, ofOrd_lt_ofOrd, Nat.cast_lt]

/-- Two actual respecting labellings with different availability witnesses. -/
noncomputable def first : Fin 5 → ExtOrd := label (num 5) (num 1)

noncomputable def second : Fin 5 → ExtOrd := label (num 6) (num 7)

theorem first_respects : RespectsSemantics rows first :=
  label_respects (nat_visible (by norm_num)) (nat_visible (by norm_num))

theorem second_respects : RespectsSemantics rows second :=
  label_respects (nat_visible (by norm_num)) (nat_visible (by norm_num))

/-- The pasting cut is strictly more visible than either active controller needs. -/
theorem cut_visible : SelfVis 3 (num 4) := nat_visible (by norm_num)

/-- All localities of the failing paste still hold: availability is the only obstruction. -/
theorem pasted_locality (c : Fin 5) :
    TransformsTo (fun d : scheme.below (scheme.cell c) => scheme.grade d.1)
      (rows.E c) (fun d => min (paste (num 4) (first d.1) (second d.1))
        (paste (num 4) (first c) (second c))) := by
  have hall : ∀ d : Fin 5, GradedLe (scheme.cell d) (Finset.univ, 2) := by
    unfold GradedLe; decide
  exact (first_respects.toBelow (Finset.univ, 2)).locality_paste_of_slack
    (second_respects.toBelow (Finset.univ, 2)) cut_visible ⟨c, hall c⟩

/-- Actual respecting inputs can lose availability under a slack-cut paste. -/
theorem not_respects_paste :
    ¬ RespectsSemantics rows (fun d => paste (num 4) (first d) (second d)) := by
  intro h
  have hh := proper_le_some h
  norm_num [first, second, label, paste, min_def, max_def] at hh

/-- No alternative output can preserve *all* accidentally agreeing coordinates. This
set of protected coordinates is not a face, so this is not a bountifulness no-go. -/
theorem no_universal_agreement_preservation :
    ¬ ∃ r : Fin 5 → ExtOrd, RespectsSemantics rows r ∧
      (∀ d, min (r d) (num 4) = min (first d) (num 4)) ∧
      (∀ d, min (first d) (num 4) = min (second d) (num 4) → r d = second d) := by
  rintro ⟨r, hr, hcap, hlit⟩
  have h0 : r 0 = num 7 := by
    have := hlit 0 (by norm_num [first, second, label, min_def, max_def])
    simpa [second, label, max_def] using this
  have h2 : r 2 = num 6 := hlit 2 (by norm_num [first, second, label, min_def, max_def])
  have h3 : r 3 = num 1 := by
    have h := hcap 3
    have h14 : num 1 < num 4 := by simp
    have hmin : min (r 3) (num 4) = num 1 := by simpa [first, label, min_def] using h
    have hlow : r 3 < num 4 := by grind
    simpa only [min_eq_left hlow.le] using hmin
  have h := proper_le_some hr
  rw [h0, h2, h3] at h
  norm_num at h

/-- A maximum of branches can be retuned uniformly without preserving the unprotected
section's branch choices. Valid for an arbitrary linear order, including endpoint cuts. -/
theorem max_retune {α : Type*} [LinearOrder α] {g a b v : α}
    (h : min (max a b) g = min v g) :
    max (paste g a v) (paste g b v) = v := by
  have hm : max (paste g a v) (paste g b v) = paste g (max a b) v := by
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab, max_eq_right (paste_mono hab le_rfl)]
    · rw [max_eq_left hba, max_eq_left (paste_mono hba le_rfl)]
  rw [hm, paste_eq_of_agree h]

/-- A proper value agreeing below the cut has a respecting extension. Only the face is
prescribed; the free controllers are chosen jointly to retain their maximum. -/
theorem face_retune {g a b v : ExtOrd} (hg : SelfVis 1 g)
    (ha : SelfVis 1 a) (hb : SelfVis 1 b) (hv : SelfVis 1 v)
    (h : min (max a b) g = min v g) :
    ∃ r : Fin 5 → ExtOrd, RespectsSemantics rows r ∧ r 0 = v ∧ r 1 = v ∧
      ∀ d, min (r d) g = min (label a b d) g := by
  refine ⟨label (paste g a v) (paste g b v),
    label_respects (paste_visible hg ha hv) (paste_visible hg hb hv), ?_, ?_, ?_⟩
  · exact max_retune h
  · exact max_retune h
  · intro d
    fin_cases d <;> simp [label, max_retune h, h, paste_cap]

def low (j : ℕ) (hj : 1 ≤ j) (d : Fin 4) : scheme.below (Finset.univ, j) :=
  ⟨d.castSucc, Finset.subset_univ _, by
    have h : ∀ d : Fin 4, scheme.grade d.castSucc = 1 := by decide
    exact (h d).le.trans hj⟩

/-- On every full lower set containing grade one, these are all respecting labellings. -/
theorem shape {j : ℕ} (hj : 1 ≤ j) {q : scheme.below (Finset.univ, j) → ExtOrd}
    (hq : RespectsSemanticsBelow rows (Finset.univ, j) q) :
    ∀ d, q d = label (q (low j hj 2)) (q (low j hj 3)) d.1 := by
  have hproper : ∀ i : Fin 2,
      q (low j hj (Fin.castAdd 2 i)) = max (q (low j hj 2)) (q (low j hj 3)) := by
    intro i
    have h2 : q (low j hj 2) ≤ q (low j hj (Fin.castAdd 2 i)) := by
      exact hq.ge_of_row_eq_diag (low j hj 2)
        ⟨Fin.castAdd 3 i, ⟨Finset.subset_univ _, by fin_cases i <;> exact le_rfl⟩⟩
        (by fin_cases i <;> rfl) (by fin_cases i <;> exact le_rfl)
    have h3 : q (low j hj 3) ≤ q (low j hj (Fin.castAdd 2 i)) := by
      exact hq.ge_of_row_eq_diag (low j hj 3)
        ⟨Fin.castAdd 3 i, ⟨Finset.subset_univ _, by fin_cases i <;> exact le_rfl⟩⟩
        (by fin_cases i <;> rfl) (by fin_cases i <;> exact le_rfl)
    apply le_antisymm _ (max_le h2 h3)
    obtain ⟨e, he, hv⟩ := hq.availability (low j hj (Fin.castAdd 2 i)) (low j hj 2)
      (Finset.subset_univ _) (by fin_cases i <;> rfl)
    have h : ∀ e : Fin 5, scheme.cell e = scheme.cell 2 → e = 2 ∨ e = 3 := by decide
    rcases h e.1 he with h | h
    · have heq : e = low j hj 2 := Subtype.ext h
      exact heq ▸ hv.trans (le_max_left _ _)
    · have heq : e = low j hj 3 := Subtype.ext h
      exact heq ▸ hv.trans (le_max_right _ _)
  intro ⟨d, hd⟩
  fin_cases d
  · exact hproper 0
  · exact hproper 1
  · rfl
  · rfl
  · obtain ⟨g, σ, _, _, hb, _, _, he⟩ := hq.locality ⟨4, hd⟩
    have hh := he ⟨4, GradedLe.refl _⟩
    change min (q ⟨4, hd⟩) (q ⟨4, hd⟩) = min (σ ⊥) (g 2) at hh
    change q ⟨4, hd⟩ = ⊥
    simpa only [min_self, hb, min_bot_left] using hh

/-- The exact whole-domain classification used by the discovery script. -/
theorem respects_iff (p : Fin 5 → ExtOrd) :
    RespectsSemantics rows p ↔ SelfVis 1 (p 2) ∧ SelfVis 1 (p 3) ∧
      p = label (p 2) (p 3) := by
  constructor
  · intro hp
    refine ⟨(hp.orderly 2).symm, (hp.orderly 3).symm, ?_⟩
    funext d
    have hd : GradedLe (scheme.cell d) (Finset.univ, 2) := by
      have h : ∀ d : Fin 5, GradedLe (scheme.cell d) (Finset.univ, 2) := by
        unfold GradedLe; decide
      exact h d
    exact shape (by decide) (hp.toBelow (Finset.univ, 2)) ⟨d, hd⟩
  · rintro ⟨ha, hb, he⟩
    rw [he]
    exact label_respects ha hb

private theorem singleton_lift (i : Fin 2) {j : ℕ} (hj : 1 ≤ j)
    (h : GradedLe (scheme.cell (Fin.castAdd 3 i)) (Finset.univ, j))
    (p : scheme.below (scheme.cell (Fin.castAdd 3 i)) → ExtOrd)
    (q : scheme.below (Finset.univ, j) → ExtOrd) (g : ExtOrd)
    (hp : RespectsSemanticsBelow rows (scheme.cell (Fin.castAdd 3 i)) p)
    (hq : RespectsSemanticsBelow rows (Finset.univ, j) q) (hg : SelfVis j g)
    (hagree : ∀ d, min (q (CellScheme.below.mono h d)) g = min (p d) g) :
    ∃ q', RespectsSemanticsBelow rows (Finset.univ, j) q' ∧
      (∀ d, min (q' d) g = min (q d) g) ∧
      (∀ d, q' (CellScheme.below.mono h d) = p d) := by
  let d0 : scheme.below (scheme.cell (Fin.castAdd 3 i)) := ⟨Fin.castAdd 3 i, GradedLe.refl _⟩
  have hv : SelfVis 1 (p d0) := by
    have hh := (hp.orderly d0).symm
    fin_cases i <;> exact hh
  have ha : SelfVis 1 (q (low j hj 2)) := (hq.orderly _).symm
  have hb : SelfVis 1 (q (low j hj 3)) := (hq.orderly _).symm
  have hcap : min (max (q (low j hj 2)) (q (low j hj 3))) g = min (p d0) g := by
    have hh := hagree d0
    rw [shape hj hq] at hh
    fin_cases i <;> exact hh
  obtain ⟨r, hr, h0, h1, hcapr⟩ := face_retune (hg.mono hj) ha hb hv hcap
  refine ⟨fun d => r d.1, hr.toBelow _, ?_, ?_⟩
  · intro d
    rw [shape hj hq d]
    exact hcapr d.1
  · intro ⟨d, hd⟩
    have heq : d = Fin.castAdd 3 i := by
      have ht : ∀ i : Fin 2, ∀ d : Fin 5,
          GradedLe (scheme.cell d) (scheme.cell (Fin.castAdd 3 i)) → d = Fin.castAdd 3 i := by
        unfold GradedLe; decide
      exact ht i d hd
    subst d
    fin_cases i
    · exact h0
    · exact h1

/-- The regression scheme is bountiful. The availability failure of the universal paste
does not prevent a face-sensitive extension, even at bottom or top caps. -/
theorem bountiful : rows.IsBountiful := by
  intro CI BJ hCI hBJ h hne p q g hp hq hg hagree
  have hc : ∀ CI ∈ Plan.gradedPlan scheme.plan, ∀ BJ ∈ Plan.gradedPlan scheme.plan,
      GradedLe CI BJ → CI ≠ BJ →
      (CI = scheme.cell 0 ∧ (BJ = scheme.cell 2 ∨ BJ = scheme.cell 4)) ∨
      (CI = scheme.cell 1 ∧ (BJ = scheme.cell 2 ∨ BJ = scheme.cell 4)) ∨
      (CI = scheme.cell 2 ∧ BJ = scheme.cell 4) := by
    unfold GradedLe
    decide
  rcases hc CI hCI BJ hBJ h hne with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
  · exact singleton_lift 0 (by decide) h p q g hp hq hg hagree
  · exact singleton_lift 0 (by decide) h p q g hp hq hg hagree
  · exact singleton_lift 1 (by decide) h p q g hp hq hg hagree
  · exact singleton_lift 1 (by decide) h p q g hp hq hg hagree
  · exact bountiful_full_scope rows h p q g hp hq hg hagree

/-- A complete, sharply coded, consistent and bountiful domain with branching availability. -/
noncomputable def domain : SemScheme 2 :=
  ⟨scheme, rows, coded, consistent, bountiful, complete⟩

end BranchAvailability

end VaughtConjecture.Knight
