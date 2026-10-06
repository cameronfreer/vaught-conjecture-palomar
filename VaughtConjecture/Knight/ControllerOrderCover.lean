/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.BranchAvailability

/-! # Opposite source orders in a jointly lawful controller family

A fixed controller cannot expose opposite orders of one pair of sources in two
labellings. A bottom/nonbottom split also requires different source blocks. These
are necessary conditions, not a sufficiency test for arbitrary rows.

The binary example has two fixed controllers with opposite source orders. Every
pair of grade-one-visible proper values extends, with locality at BOTH controllers.
The controller seeing the larger value has the larger cap; the other controller
sees the capped, constant target. The rows do not depend on the input labelling.
The example does not construct mixed rows over arbitrary input semantics.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd VaughtConjecture.AmalgamationPlan

/-- At a maximal-grade controller, strict capped targets require strict source order,
even if the two observed cells have different grades. -/
theorem TransformsTo.source_lt_of_capped_lt {D : Type*} {grade : D → ℕ}
    {E p : D → ExtOrd} {c d e : D} (hmax : ∀ x, grade x ≤ grade c)
    (hvis : SelfVis (grade c) (p c))
    (h : TransformsTo grade E (fun x => min (p x) (p c)))
    (hlt : min (p d) (p c) < min (p e) (p c)) : E d < E e := by
  obtain ⟨τ, _, hm, hs, _, _⟩ := exists_exact_capped_shifter hmax hvis h
  apply lt_of_not_ge
  intro he
  have hh := hm he
  rw [hs, hs] at hh
  exact (not_le_of_gt hlt) hh

/-- No one fixed row can expose a strict pair in opposite orders in two faithful
controller localities. The caps and witnesses may differ. -/
theorem TransformsTo.no_capped_order_reversal {D : Type*} {grade : D → ℕ}
    {E p q : D → ExtOrd} {c d e : D} (hmax : ∀ x, grade x ≤ grade c)
    (hpvis : SelfVis (grade c) (p c)) (hqvis : SelfVis (grade c) (q c))
    (hp : TransformsTo grade E (fun x => min (p x) (p c)))
    (hq : TransformsTo grade E (fun x => min (q x) (q c)))
    (hpord : min (p d) (p c) < min (p e) (p c)) :
    ¬ min (q e) (q c) < min (q d) (q c) := by
  intro hqord
  exact (asymm (TransformsTo.source_lt_of_capped_lt hmax hpvis hp hpord))
    (TransformsTo.source_lt_of_capped_lt hmax hqvis hq hqord)

/-- Splitting a source equality only inside its old block cannot expose a
bottom/nonbottom distinction. This uses clause 5 at every threshold. -/
theorem TransformsTo.source_blocks_ne_of_capped_bot {D : Type*} {grade : D → ℕ}
    {E p : D → ExtOrd} {c d e : D} (hmax : ∀ x, grade x ≤ grade c)
    (hvis : SelfVis (grade c) (p c))
    (h : TransformsTo grade E (fun x => min (p x) (p c)))
    (hd : min (p d) (p c) = ⊥) (he : min (p e) (p c) ≠ ⊥) :
    blockFloor (E d) ≠ blockFloor (E e) := by
  obtain ⟨τ, _, _, hs, _, hb⟩ := exists_exact_capped_shifter hmax hvis h
  intro hblock
  have hh := bot_of_same_block hb hblock ((hs d).trans hd)
  exact he ((hs e).symm.trans hh)

namespace ControllerOrderCover

def indices (d : Fin 5) : Finset (Fin 2) × ℕ :=
  match d.val with
  | 0 => ({0}, 1)
  | 1 => ({1}, 1)
  | 4 => (Finset.univ, 2)
  | _ => (Finset.univ, 1)

/-- The same binary support plan as the branching-availability regression. -/
abbrev scheme : CellScheme (ι := Fin 2) Finset.univ where
  plan := BranchAvailability.scheme.plan
  isPlan := BranchAvailability.scheme.isPlan
  card := 5
  cell := indices
  cell_mem := by decide

theorem complete : scheme.IsComplete := by
  intro BJ h
  have hc : ∀ BJ ∈ Plan.gradedPlan scheme.plan, ∃ d : Fin 5, indices d = BJ := by decide
  exact hc BJ h

open BranchAvailability (source source_visible source_coded)

/-- Ascending at controller 2, descending at controller 3. The other controller is
always read at the lower source, so both row equations can hold simultaneously. -/
noncomputable def row (c d : Fin 5) : ExtOrd :=
  match c.val with
  | 0 | 1 => source 1
  | 2 => if d.val = 0 ∨ d.val = 3 then source 1 else source 2
  | 3 => if d.val = 1 ∨ d.val = 2 then source 1 else source 2
  | _ => ⊥

private theorem lower_grade_one {c d : Fin 5} (hc : c ≠ 4)
    (hd : GradedLe (scheme.cell d) (scheme.cell c)) : scheme.grade d = 1 := by
  have h : ∀ c d : Fin 5, c ≠ 4 → GradedLe (scheme.cell d) (scheme.cell c) →
      scheme.grade d = 1 := by unfold GradedLe; decide
  exact h c d hc hd

private theorem row_cases (c d : Fin 5) :
    row c d = ⊥ ∨ row c d = source 1 ∨ row c d = source 2 := by
  fin_cases c <;> fin_cases d <;> simp [row]

/-- The source rows are fixed before either proper value is supplied. -/
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

/-- Both proper labels are free; each is copied at the oppositely named controller. -/
noncomputable def label (a b : ExtOrd) (d : Fin 5) : ExtOrd :=
  match d.val with
  | 0 | 3 => a
  | 1 | 2 => b
  | _ => ⊥

private theorem step_low {a b : ExtOrd} : stepShifter 2 a b (source 1) = a := by
  apply stepShifter_of_lt (ofOrd_ne_bot _)
  rw [ofOrd_lt_ofOrd]
  simp [Ordinal.mul_two]

private theorem step_high {a b : ExtOrd} : stepShifter 2 a b (source 2) = b := by
  apply stepShifter_of_ge
  exact ofOrd_le_ofOrd.mpr (le_self_add)

attribute [-simp] CellScheme.cell_eq in
/-- Every visible pair has a section with all faithful localities and availability.
Bottom and literal top are allowed independently in either coordinate. -/
theorem label_respects {a b : ExtOrd} (ha : SelfVis 1 a) (hb : SelfVis 1 b) :
    RespectsSemantics rows (label a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    fin_cases d <;> simp_all [label, indices, CellScheme.grade, SelfVis]
  · intro c
    fin_cases c
    · apply (Witness.stepLimit 1 2 (le_refl a) ha ha).transformsTo
      intro ⟨d, hd⟩
      have hc : ∀ d : Fin 5, GradedLe (scheme.cell d) (scheme.cell 0) → d = 0 := by
        unfold GradedLe; decide
      have he := hc d hd
      subst d
      simp [rows, row, label, CellScheme.grade, indices, gTop, step_low]
    · apply (Witness.stepLimit 1 2 (le_refl b) hb hb).transformsTo
      intro ⟨d, hd⟩
      have hc : ∀ d : Fin 5, GradedLe (scheme.cell d) (scheme.cell 1) → d = 1 := by
        unfold GradedLe; decide
      have he := hc d hd
      subst d
      simp [rows, row, label, CellScheme.grade, indices, gTop, step_low]
    · apply (Witness.stepLimit 1 2 (min_le_right a b) (selfVis_min' ha hb) hb).transformsTo
      intro ⟨d, hd⟩
      fin_cases d <;> simp_all [rows, row, label, indices, GradedLe,
        CellScheme.grade, gTop, step_low, step_high]
    · apply (Witness.stepLimit 1 2 (min_le_left a b) (selfVis_min' ha hb) ha).transformsTo
      intro ⟨d, hd⟩
      fin_cases d <;> simp_all [rows, row, label, indices, GradedLe,
        CellScheme.grade, gTop, step_low, step_high, min_comm]
    · simpa [label] using (TransformsTo.to_bot
        (grade := fun d : scheme.below (scheme.cell 4) => scheme.grade d.1) (rows.E 4))
  · intro c d hs hg
    let pick : Fin 5 → Fin 5 := fun c =>
      match c.val with
      | 0 => 3
      | 1 => 2
      | _ => c
    have geom : ∀ c d : Fin 5, scheme.scope c ⊆ scheme.scope d →
        scheme.grade c = scheme.grade d → c = d ∨ scheme.cell (pick c) = scheme.cell d := by
      decide
    rcases geom c d hs hg with rfl | he
    · exact ⟨c, rfl, le_rfl⟩
    · refine ⟨pick c, he, ?_⟩
      have hl : label a b (pick c) = label a b c := by fin_cases c <;> rfl
      rw [hl]

private theorem consistent_of_label (c : Fin 5) {a b : ExtOrd}
    (ha : SelfVis 1 a) (hb : SelfVis 1 b)
    (heq : ∀ d : scheme.below (scheme.cell c), row c d.1 = label a b d.1) :
    RespectsSemanticsBelow rows (scheme.cell c) (rows.E c) := by
  have hfun : rows.E c = fun d => label a b d.1 := funext heq
  rw [hfun]
  exact (label_respects ha hb).toBelow _

attribute [-simp] CellScheme.cell_eq in
/-- Both opposite-order controllers are consistent against each other. -/
theorem consistent : rows.IsConsistent := by
  intro c
  fin_cases c
  · apply consistent_of_label 0 (source_visible 1) (source_visible 1)
    intro ⟨d, hd⟩
    have h : ∀ d : Fin 5, GradedLe (scheme.cell d) (scheme.cell 0) → d = 0 := by
      unfold GradedLe; decide
    have he := h d hd
    subst d
    rfl
  · apply consistent_of_label 1 (source_visible 1) (source_visible 1)
    intro ⟨d, hd⟩
    have h : ∀ d : Fin 5, GradedLe (scheme.cell d) (scheme.cell 1) → d = 1 := by
      unfold GradedLe; decide
    have he := h d hd
    subst d
    rfl
  · apply consistent_of_label 2 (source_visible 1) (source_visible 2)
    intro ⟨d, hd⟩
    have hg := lower_grade_one (c := 2) (by decide) hd
    fin_cases d <;> simp_all [row, label, indices, CellScheme.grade]
  · apply consistent_of_label 3 (source_visible 2) (source_visible 1)
    intro ⟨d, hd⟩
    have hg := lower_grade_one (c := 3) (by decide) hd
    fin_cases d <;> simp_all [row, label, indices, CellScheme.grade]
  · apply consistent_of_label 4 (a := ⊥) (b := ⊥) (extVisibilityReplace_bot _ _)
      (extVisibilityReplace_bot _ _)
    intro ⟨d, hd⟩
    fin_cases d <;> rfl

/-- The two prescribed proper labels are realized literally in one fixed semantics. -/
theorem prescribed_pair_section {a b : ExtOrd} (ha : SelfVis 1 a) (hb : SelfVis 1 b) :
    ∃ p : Fin 5 → ExtOrd, RespectsSemantics rows p ∧ p 0 = a ∧ p 1 = b :=
  ⟨label a b, label_respects ha hb, rfl, rfl⟩

/-- The ascending controller dominates both probes exactly in the ascending case. -/
theorem ascending_dominates_iff (a b : ExtOrd) : max a b ≤ label a b 2 ↔ a ≤ b := by
  change max a b ≤ b ↔ a ≤ b
  simp only [max_le_iff, le_refl, and_true]

/-- The descending controller dominates both probes exactly in the descending case. -/
theorem descending_dominates_iff (a b : ExtOrd) : max a b ≤ label a b 3 ↔ b ≤ a := by
  change max a b ≤ a ↔ b ≤ a
  simp only [max_le_iff, le_refl, true_and]

/-- Requiring both opposite controllers to dominate both probes would lose the
independent-pair property. In the actual section the smaller controller is capped low. -/
theorem both_dominate_iff (a b : ExtOrd) :
    (max a b ≤ label a b 2 ∧ max a b ≤ label a b 3) ↔ a = b := by
  rw [ascending_dominates_iff, descending_dominates_iff]
  exact le_antisymm_iff.symm

/-- The two capped probe equations and availability force coordinate copies.
No ordinal arithmetic or visibility assumption is needed for this order calculation. -/
theorem cap_pair_shape {α : Type*} [LinearOrder α] {a b u v : α}
    (hub : u ≤ b) (hva : v ≤ a)
    (h0 : min a u = min v u) (h1 : min b v = min u v)
    (ha : a ≤ max u v) (hb : b ≤ max u v) : u = b ∧ v = a := by
  grind

def low (j : ℕ) (hj : 1 ≤ j) (d : Fin 4) : scheme.below (Finset.univ, j) :=
  ⟨d.castSucc, Finset.subset_univ _, by
    have h : ∀ d : Fin 4, scheme.grade d.castSucc = 1 := by decide
    exact (h d).le.trans hj⟩

/-- Every respecting full labelling has precisely the two free proper coordinates.
The copies are forced by locality AND availability, not by graded-index equality. -/
theorem shape {j : ℕ} (hj : 1 ≤ j) {q : scheme.below (Finset.univ, j) → ExtOrd}
    (hq : RespectsSemanticsBelow rows (Finset.univ, j) q) :
    ∀ d, q d = label (q (low j hj 0)) (q (low j hj 1)) d.1 := by
  have h2 : q (low j hj 2) ≤ q (low j hj 1) :=
    hq.ge_of_row_eq_diag (low j hj 2)
      ⟨1, by change GradedLe (scheme.cell 1) (scheme.cell 2); unfold GradedLe; decide⟩ rfl le_rfl
  have h3 : q (low j hj 3) ≤ q (low j hj 0) :=
    hq.ge_of_row_eq_diag (low j hj 3)
      ⟨0, by change GradedLe (scheme.cell 0) (scheme.cell 3); unfold GradedLe; decide⟩ rfl le_rfl
  have h0 : min (q (low j hj 0)) (q (low j hj 2)) =
      min (q (low j hj 3)) (q (low j hj 2)) :=
    hq.probe_eq_of_row_eq (low j hj 2)
      ⟨0, by change GradedLe (scheme.cell 0) (scheme.cell 2); unfold GradedLe; decide⟩
      ⟨3, GradedLe.refl _⟩ rfl rfl
  have h1 : min (q (low j hj 1)) (q (low j hj 3)) =
      min (q (low j hj 2)) (q (low j hj 3)) :=
    hq.probe_eq_of_row_eq (low j hj 3)
      ⟨1, by change GradedLe (scheme.cell 1) (scheme.cell 3); unfold GradedLe; decide⟩
      ⟨2, GradedLe.refl _⟩ rfl rfl
  have hav : ∀ i : Fin 2, q (low j hj (Fin.castAdd 2 i)) ≤
      max (q (low j hj 2)) (q (low j hj 3)) := by
    intro i
    obtain ⟨e, he, hv⟩ := hq.availability (low j hj (Fin.castAdd 2 i)) (low j hj 2)
      (Finset.subset_univ _) (by fin_cases i <;> rfl)
    have h : ∀ e : Fin 5, scheme.cell e = scheme.cell 2 → e = 2 ∨ e = 3 := by decide
    rcases h e.1 he with h | h
    · have heq : e = low j hj 2 := Subtype.ext h
      exact heq ▸ hv.trans (le_max_left _ _)
    · have heq : e = low j hj 3 := Subtype.ext h
      exact heq ▸ hv.trans (le_max_right _ _)
  obtain ⟨hu, hv⟩ := cap_pair_shape h2 h3 h0 h1 (hav 0) (hav 1)
  intro ⟨d, hd⟩
  fin_cases d
  · rfl
  · rfl
  · exact hu
  · exact hv
  · obtain ⟨g, σ, _, _, hb, _, _, he⟩ := hq.locality ⟨4, hd⟩
    have hh := he ⟨4, GradedLe.refl _⟩
    change min (q ⟨4, hd⟩) (q ⟨4, hd⟩) = min (σ ⊥) (g 2) at hh
    change q ⟨4, hd⟩ = ⊥
    simpa only [min_self, hb, min_bot_left] using hh

/-- An exact unrestricted-ordinal characterization, including independent bottom/top values. -/
theorem respects_iff (p : Fin 5 → ExtOrd) :
    RespectsSemantics rows p ↔ SelfVis 1 (p 0) ∧ SelfVis 1 (p 1) ∧
      p = label (p 0) (p 1) := by
  constructor
  · intro hp
    refine ⟨(hp.orderly 0).symm, (hp.orderly 1).symm, ?_⟩
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
    (hq : RespectsSemanticsBelow rows (Finset.univ, j) q)
    (hagree : ∀ d, min (q (CellScheme.below.mono h d)) g = min (p d) g) :
    ∃ q', RespectsSemanticsBelow rows (Finset.univ, j) q' ∧
      (∀ d, min (q' d) g = min (q d) g) ∧
      (∀ d, q' (CellScheme.below.mono h d) = p d) := by
  let d0 : scheme.below (scheme.cell (Fin.castAdd 3 i)) :=
    ⟨Fin.castAdd 3 i, GradedLe.refl _⟩
  have hv : SelfVis 1 (p d0) := by
    have hh := (hp.orderly d0).symm
    fin_cases i <;> exact hh
  have hsingle : ∀ d : scheme.below (scheme.cell (Fin.castAdd 3 i)), d.1 = Fin.castAdd 3 i := by
    intro d
    have ht : ∀ i : Fin 2, ∀ d : Fin 5,
        GradedLe (scheme.cell d) (scheme.cell (Fin.castAdd 3 i)) → d = Fin.castAdd 3 i := by
      unfold GradedLe; decide
    exact ht i d.1 d.2
  have ha : SelfVis 1 (q (low j hj 0)) := (hq.orderly _).symm
  have hb : SelfVis 1 (q (low j hj 1)) := (hq.orderly _).symm
  have hc := hagree d0
  fin_cases i
  · refine ⟨fun d => label (p d0) (q (low j hj 1)) d.1,
      (label_respects hv hb).toBelow _, ?_, ?_⟩
    · intro ⟨d, hd⟩
      rw [shape hj hq ⟨d, hd⟩]
      fin_cases d <;> first | exact hc.symm | rfl
    · intro d
      have he : d = d0 := Subtype.ext (hsingle d)
      subst d
      rfl
  · refine ⟨fun d => label (q (low j hj 0)) (p d0) d.1,
      (label_respects ha hv).toBelow _, ?_, ?_⟩
    · intro ⟨d, hd⟩
      rw [shape hj hq ⟨d, hd⟩]
      fin_cases d <;> first | exact hc.symm | rfl
    · intro d
      have he : d = d0 := Subtype.ext (hsingle d)
      subst d
      rfl

/-- Arbitrary singleton-face retuning is coordinatewise; full-scope grade extension is
the generic theorem. In particular the example is genuinely bountiful. -/
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
  · exact singleton_lift 0 (by decide) h p q g hp hq hagree
  · exact singleton_lift 0 (by decide) h p q g hp hq hagree
  · exact singleton_lift 1 (by decide) h p q g hp hq hagree
  · exact singleton_lift 1 (by decide) h p q g hp hq hagree
  · exact bountiful_full_scope rows h p q g hp hq hg hagree

/-- One fixed legal domain realizes either proper ordering, not a row chosen per input. -/
noncomputable def domain : SemScheme 2 :=
  ⟨scheme, rows, coded, consistent, bountiful, complete⟩

end ControllerOrderCover

end VaughtConjecture.Knight
