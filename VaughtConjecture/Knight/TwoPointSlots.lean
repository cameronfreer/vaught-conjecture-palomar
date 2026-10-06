/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SlotCappedLifting
public import VaughtConjecture.Knight.BranchAvailability

/-! # Installing the slot family on the complete two-point plan

The singleton rows admit independent visible labels. Both slot controllers
are installed at the full grade-one index, with their directed cross-readings
unchanged; the required grade-two cell is mute. All occurrences remain distinct.
This is a first geometric installation, not an iteration or a higher-grade
request construction.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.TwoPointSlots

open AmalgamationPlan Transform Value ExtOrd DonorSlotAssembly

abbrev scheme := BranchAvailability.scheme
abbrev Inventory := Occ Unit

noncomputable def source : Unit → ExtOrd := fun _ => SeparatedGradeOne.band 1

def embed : Inventory → Cell scheme
  | .inl none => 1
  | .inl (some _) => 0
  | .inr j => ⟨j.val + 2, by have h : j.val < 2 := j.isLt; change j.val + 2 < 5; omega⟩

def project (d : Cell scheme) : Inventory :=
  if d = 0 then old () else if d = 1 then fresh else
    controller (if d = 2 then 0 else 1)

theorem project_embed (d : Inventory) : project (embed d) = d := by
  rcases d with (_ | u) | j
  · rfl
  · cases u; rfl
  · fin_cases j <;> rfl

theorem embed_project (d : Cell scheme) (hd : d ≠ 4) : embed (project d) = d := by
  fin_cases d <;> simp_all [embed, project, old, fresh, controller]

theorem embed_ne_four (d : Inventory) : embed d ≠ 4 := by
  rcases d with (_ | u) | j
  · decide
  · cases u; decide
  · fin_cases j <;> decide

theorem embed_grade (d : Inventory) : scheme.grade (embed d) = 1 := by
  rcases d with (_ | u) | j
  · rfl
  · rfl
  · fin_cases j <;> rfl

theorem controller_cell (j : Fin 2) :
    scheme.cell (embed (controller j)) = (Finset.univ, 1) := by
  fin_cases j <;> rfl

theorem below_grade_one {c d : Cell scheme} (hc : c ≠ 4)
    (hd : GradedLe (scheme.cell d) (scheme.cell c)) : scheme.grade d = 1 := by
  have h : ∀ c d : Fin 5, c ≠ 4 → GradedLe (scheme.cell d) (scheme.cell c) →
      scheme.grade d = 1 := by unfold GradedLe; decide
  exact h c d hc hd

theorem grade_one_ne_four {d : Cell scheme} (hd : scheme.grade d = 1) : d ≠ 4 := by
  rintro rfl
  contradiction

theorem singleton_below (i : Fin 2) (d : Cell scheme)
    (hd : GradedLe (scheme.cell d) (scheme.cell (Fin.castAdd 3 i))) :
    d = Fin.castAdd 3 i := by
  have h : ∀ i : Fin 2, ∀ d : Fin 5,
      GradedLe (scheme.cell d) (scheme.cell (Fin.castAdd 3 i)) → d = Fin.castAdd 3 i := by
    unfold GradedLe; decide
  exact h i d hd

noncomputable def table (c d : Cell scheme) : ExtOrd :=
  if c = 4 then ⊥ else if c = 0 ∨ c = 1 then SlotControllerFamily.value 1
  else DonorSlotAssembly.row source (if c = 2 then 0 else 1) (project d)

noncomputable def rows : Semantics scheme where
  E c d := table c d.1
  orderly c d := by
    by_cases hc : c = 4
    · simp only [table, hc, ↓reduceIte, extVisibilityReplace_bot]
    have hg := below_grade_one hc d.2
    change table c d.1 = extVisibilityReplace (table c d.1) (scheme.grade d.1) (scheme.grade d.1)
    rw [hg]
    unfold table
    rw [ite_eq_right hc]
    split
    · exact (SlotControllerFamily.value_visible 1).symm
    · exact ((DonorSlotAssembly.rows_joint source _).1 _).symm

theorem row_controller (j : Fin 2) (d : scheme.below (scheme.cell (embed (controller j)))) :
    rows.E (embed (controller j)) d = DonorSlotAssembly.row source j (project d.1) := by
  fin_cases j <;> rfl

theorem coded : rows.IsCoded := by
  intro c d
  change IsCodedLabel _ (table c d.1)
  by_cases hc : c = 4
  · exact Or.inl (by simp only [table, hc, ↓reduceIte])
  have hg : scheme.grade c = 1 := below_grade_one hc (GradedLe.refl _)
  rw [hg]
  unfold table
  rw [ite_eq_right hc]
  split
  · exact SlotControllerFamily.value_coded 1
  · exact DonorSlotAssembly.row_coded source _ _

def extend (r : Inventory → ExtOrd) (d : Cell scheme) : ExtOrd :=
  if d = 4 then ⊥ else r (project d)

theorem extend_embed (r : Inventory → ExtOrd) (d : Inventory) : extend r (embed d) = r d := by
  simp only [extend, embed_ne_four d, ↓reduceIte, project_embed]

private theorem controller_locality {r : Inventory → ExtOrd} (hr : Joint source r) (j : Fin 2) :
    TransformsTo
      (fun d : scheme.below (scheme.cell (embed (controller j))) => scheme.grade d.1)
      (rows.E (embed (controller j)))
      (fun d => min (extend r d.1) (extend r (embed (controller j)))) := by
  have ht := (hr.2.1 j).reindex
    (fun d : scheme.below (scheme.cell (embed (controller j))) => project d.1)
  convert ht using 1
  · funext d
    exact below_grade_one (embed_ne_four _) d.2
  · funext d
    exact row_controller j d
  · funext d
    rw [extend_embed]
    have hd := grade_one_ne_four (below_grade_one (embed_ne_four (controller j)) d.2)
    simp only [extend, hd, ↓reduceIte, Function.comp_apply]

private theorem singleton_locality (i : Fin 2) (p : Cell scheme → ExtOrd)
    (hv : SelfVis 1 (p (Fin.castAdd 3 i))) :
    TransformsTo (fun d : scheme.below (scheme.cell (Fin.castAdd 3 i)) => scheme.grade d.1)
      (rows.E (Fin.castAdd 3 i)) (fun d => min (p d.1) (p (Fin.castAdd 3 i))) := by
  have he : ∀ d : scheme.below (scheme.cell (Fin.castAdd 3 i)),
      d.1 = Fin.castAdd 3 i := fun d => singleton_below i d.1 d.2
  have ht := SlotControllerFamily.transforms_of_table
    (fun _ : scheme.below (scheme.cell (Fin.castAdd 3 i)) => 1)
    (fun _ => p (Fin.castAdd 3 i)) (fun _ => hv)
    (fun _ h => False.elim (by omega)) (fun _ _ _ => le_rfl)
  convert ht using 1
  · funext d
    rw [he d]
    fin_cases i <;> rfl
  · funext d
    fin_cases i <;> rfl
  · funext d
    rw [he d, min_self]

/-- Joint row-layer lawfulness supplies every locality and every actual
availability request of the installed whole scheme. -/
theorem extend_respects {r : Inventory → ExtOrd} (hr : Joint source r) :
    RespectsSemantics rows (extend r) where
  orderly d := by
    by_cases hd : d = 4
    · simp only [extend, hd, ↓reduceIte, extVisibilityReplace_bot]
    have hg : scheme.grade d = 1 := below_grade_one hd (GradedLe.refl _)
    simpa only [extend, hd, ↓reduceIte, hg] using (hr.1 (project d)).symm
  locality c := by
    fin_cases c
    · exact singleton_locality 0 _ (hr.1 _)
    · exact singleton_locality 1 _ (hr.1 _)
    · exact controller_locality hr 0
    · exact controller_locality hr 1
    · change TransformsTo (fun d : scheme.below (scheme.cell 4) => scheme.grade d.1)
        (rows.E 4) (fun d => min (extend r d.1) ⊥)
      simpa only [min_bot_right] using
        (TransformsTo.to_bot (grade := fun d : scheme.below (scheme.cell 4) => scheme.grade d.1)
          (rows.E 4))
  availability d e hs hg := by
    have proper : ∀ d e : Cell scheme, e = 0 ∨ e = 1 ∨ e = 4 →
        scheme.scope d ⊆ scheme.scope e → scheme.grade d = scheme.grade e → d = e := by
      decide
    by_cases he : e = 0 ∨ e = 1 ∨ e = 4
    · exact ⟨e, rfl, (proper d e he hs hg) ▸ le_rfl⟩
    have hec : ∃ j : Fin 2, e = embed (controller j) := by
      fin_cases e <;> simp_all [embed, controller]
    obtain ⟨j, rfl⟩ := hec
    have hd : d ≠ 4 := grade_one_ne_four (hg.trans (embed_grade _))
    obtain ⟨k, hk⟩ := hr.2.2 (project d)
    refine ⟨embed (controller k), (controller_cell k).trans (controller_cell j).symm, ?_⟩
    rw [extend_embed]
    simpa only [extend, hd, ↓reduceIte] using hk

def low {j : ℕ} (hj : 1 ≤ j) (d : Inventory) : scheme.below (Finset.univ, j) :=
  ⟨embed d, Finset.subset_univ _, (embed_grade d).le.trans hj⟩

def under (j : Fin 2) (d : Inventory) : scheme.below (scheme.cell (embed (controller j))) :=
  ⟨embed d, by rw [controller_cell]; exact ⟨Finset.subset_univ _, (embed_grade d).le⟩⟩

/-- Every actual target-local ambient supplies the row-layer hypotheses;
it is not assumed to extend to a larger domain or to be a selected row. -/
theorem joint_of_respects {j : ℕ} (hj : 1 ≤ j)
    {q : scheme.below (Finset.univ, j) → ExtOrd}
    (hq : RespectsSemanticsBelow rows (Finset.univ, j) q) :
    Joint source (fun d => q (low hj d)) := by
  refine ⟨fun d => ?_, ?_, ?_⟩
  · simpa only [low, embed_grade] using (hq.orderly (low hj d)).symm
  · intro c
    have ht := (hq.locality (low hj (controller c))).reindex (under c)
    convert ht using 1
    · funext d; exact (embed_grade d).symm
    · funext d
      exact ((row_controller c (under c d)).trans
        (congrArg (DonorSlotAssembly.row source c) (project_embed d))).symm
    · rfl
  · intro d
    obtain ⟨e, he, hle⟩ := hq.availability (low hj d) (low hj (controller 0))
      (by change scheme.scope (embed d) ⊆ Finset.univ; exact Finset.subset_univ _)
      (embed_grade d)
    have hcases : ∀ e : Cell scheme, scheme.cell e = scheme.cell 2 →
        e = embed (controller (0 : Fin 2)) ∨ e = embed (controller (1 : Fin 2)) := by decide
    rcases hcases e.1 he with h | h
    · refine ⟨0, ?_⟩
      simpa only [show e = low hj (controller 0) from Subtype.ext h] using hle
    · refine ⟨1, ?_⟩
      simpa only [show e = low hj (controller 1) from Subtype.ext h] using hle

theorem mute_label {BJ : Finset (Fin 2) × ℕ} {q : scheme.below BJ → ExtOrd}
    (hq : RespectsSemanticsBelow rows BJ q) (h : GradedLe (scheme.cell 4) BJ) :
    q ⟨4, h⟩ = ⊥ := by
  obtain ⟨g, σ, _, _, hb, _, _, hr⟩ := hq.locality ⟨4, h⟩
  have hh := hr ⟨4, GradedLe.refl _⟩
  change min (q ⟨4, h⟩) (q ⟨4, h⟩) = min (σ ⊥) (g 2) at hh
  simpa only [min_self, hb, min_bot_left] using hh

theorem full_recover {j : ℕ} (hj : 1 ≤ j)
    {q : scheme.below (Finset.univ, j) → ExtOrd}
    (hq : RespectsSemanticsBelow rows (Finset.univ, j) q) (d : scheme.below (Finset.univ, j)) :
    extend (fun e => q (low hj e)) d.1 = q d := by
  by_cases hd : d.1 = 4
  · rcases d with ⟨d, h⟩; dsimp only at hd; subst d
    simpa only [extend, ↓reduceIte] using (mute_label hq h).symm
  · simp only [extend, hd, ↓reduceIte]
    exact congrArg q (Subtype.ext (embed_project d.1 hd))

private theorem singleton_consistent (i : Fin 2) :
    RespectsSemanticsBelow rows (scheme.cell (Fin.castAdd 3 i))
      (rows.E (Fin.castAdd 3 i)) where
  orderly := rows.orderly _
  locality c := by
    have hc := singleton_below i c.1 c.2
    rcases c with ⟨c, h⟩
    dsimp only at hc
    subst c
    convert TransformsTo.refl (grade := fun d : scheme.below (scheme.cell (Fin.castAdd 3 i)) =>
      scheme.grade d.1) (rows.E (Fin.castAdd 3 i)) using 1
    funext d
    fin_cases i <;> exact min_self _
  availability d e _ _ := by
    refine ⟨e, rfl, ?_⟩
    fin_cases i <;> exact le_rfl

private theorem controller_consistent (j : Fin 2) :
    RespectsSemanticsBelow rows (scheme.cell (embed (controller j)))
      (rows.E (embed (controller j))) := by
  have hr := (extend_respects (DonorSlotAssembly.rows_joint source j)).toBelow
    (scheme.cell (embed (controller j)))
  convert hr using 1
  funext d
  rw [row_controller]
  have hd := grade_one_ne_four (below_grade_one (embed_ne_four (controller j)) d.2)
  exact (ite_eq_right hd).symm

/-- Consistency is proved on the actual complete lower domains, not merely
on the four-cell grade-one row layer. -/
theorem consistent : rows.IsConsistent := by
  intro c
  fin_cases c
  · exact singleton_consistent 0
  · exact singleton_consistent 1
  · exact controller_consistent 0
  · exact controller_consistent 1
  · refine ⟨rows.orderly 4, ?_, ?_⟩
    · intro d
      change TransformsTo (fun e : scheme.below (scheme.cell d.1) => scheme.grade e.1)
        (rows.E d.1) (fun _ => min ⊥ ⊥)
      simpa only [min_self] using
        (TransformsTo.to_bot (grade := fun e : scheme.below (scheme.cell d.1) => scheme.grade e.1)
          (rows.E d.1))
    · intro d e _ _
      exact ⟨e, rfl, le_rfl⟩

/-- Arbitrary independent singleton prescriptions have a simultaneous
whole-scheme section; a dominating serving label may also be prescribed. -/
theorem sections {u v U : ExtOrd} (hu : SelfVis 1 u) (hv : SelfVis 1 v)
    (hU : SelfVis 1 U) (huU : u ≤ U) (hvU : v ≤ U) :
    ∃ r : Cell scheme → ExtOrd, RespectsSemantics rows r ∧ r 0 = u ∧ r 1 = v ∧
      ∃ j : Fin 2, r (embed (controller j)) = U := by
  obtain ⟨r, hr, h0, h1, j, hUj⟩ := DonorSlotAssembly.exists_section
    (E := source) (p := fun _ : Unit => u) (fun _ => hu) hv hU (fun _ _ _ => le_rfl)
    (fun _ h => False.elim (ofOrd_ne_bot _ h)) (fun _ => huU) hvU
  refine ⟨extend r, extend_respects hr, ?_, ?_, j, ?_⟩
  · exact h0 ()
  · exact h1
  · simpa only [extend_embed] using hUj

/-- The two singleton faces can be prescribed simultaneously while retaining
every actual target-local ambient cap, including the two auxiliary controllers.
The target grade is arbitrary above one; no whole-ambient completion is used. -/
theorem simultaneous_lift {j : ℕ} (hj : 1 ≤ j)
    {q : scheme.below (Finset.univ, j) → ExtOrd} {u v γ : ExtOrd}
    (hq : RespectsSemanticsBelow rows (Finset.univ, j) q)
    (hu : SelfVis 1 u) (hv : SelfVis 1 v) (hγ : SelfVis 1 γ)
    (h0 : min (q (low hj (old ()))) γ = min u γ)
    (h1 : min (q (low hj fresh)) γ = min v γ) :
    ∃ r : Cell scheme → ExtOrd, RespectsSemantics rows r ∧ r 0 = u ∧ r 1 = v ∧
      ∀ d : scheme.below (Finset.univ, j), min (r d.1) γ = min (q d) γ := by
  obtain ⟨r, hr, hcap, hpres⟩ := SlotCappedLifting.lift
    (joint_of_respects hj hq) (p := fun _ : Unit => u) (fun _ => hu) hv hγ
    (fun _ _ _ => le_rfl) (fun _ h => False.elim (ofOrd_ne_bot _ h)) (by
      rintro (_ | d)
      · exact h1
      · exact h0)
  refine ⟨extend r, extend_respects hr, hpres (some ()), hpres none, ?_⟩
  intro d
  rw [← full_recover hj hq d]
  by_cases hd : d.1 = 4
  · simp only [extend, hd, ↓reduceIte]
  · simpa only [extend, hd, ↓reduceIte] using hcap (project d.1)

private theorem singleton_lift (i : Fin 2) {j : ℕ} (hj : 1 ≤ j)
    (h : GradedLe (scheme.cell (Fin.castAdd 3 i)) (Finset.univ, j))
    (p : scheme.below (scheme.cell (Fin.castAdd 3 i)) → ExtOrd)
    (q : scheme.below (Finset.univ, j) → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow rows (scheme.cell (Fin.castAdd 3 i)) p)
    (hq : RespectsSemanticsBelow rows (Finset.univ, j) q) (hγ : SelfVis j γ)
    (hag : ∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow rows (Finset.univ, j) r ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧
      (∀ d, r (CellScheme.below.mono h d) = p d) := by
  let o : scheme.below (scheme.cell (Fin.castAdd 3 i)) :=
    ⟨Fin.castAdd 3 i, GradedLe.refl _⟩
  have hv : SelfVis 1 (p o) := by
    have hh := (hp.orderly o).symm
    fin_cases i <;> exact hh
  let u := if i = 0 then p o else q (low hj (old ()))
  let v := if i = 1 then p o else q (low hj fresh)
  have hu : SelfVis 1 u := by
    unfold u
    split
    · exact hv
    · exact (hq.orderly (low hj (old ()))).symm
  have hv' : SelfVis 1 v := by
    unfold v
    split
    · exact hv
    · exact (hq.orderly (low hj fresh)).symm
  have h0 : min (q (low hj (old ()))) γ = min u γ := by
    fin_cases i
    · exact hag o
    · rfl
  have h1 : min (q (low hj fresh)) γ = min v γ := by
    fin_cases i
    · rfl
    · exact hag o
  obtain ⟨r, hr, hr0, hr1, hcap⟩ := simultaneous_lift hj hq hu hv' (hγ.mono hj) h0 h1
  refine ⟨fun d => r d.1, hr.toBelow _, hcap, ?_⟩
  intro d
  have hd : d = o := Subtype.ext (singleton_below i d.1 d.2)
  subst d
  fin_cases i
  · exact hr0
  · exact hr1

/-- Exhaustive unrestricted bountifulness of the installed scheme. There
are four singleton-to-full pairs and one full-scope grade-change pair. -/
theorem bountiful : rows.IsBountiful := by
  intro CI BJ hCI hBJ h hne p q γ hp hq hγ hag
  have pairs : ∀ CI ∈ Plan.gradedPlan scheme.plan, ∀ BJ ∈ Plan.gradedPlan scheme.plan,
      GradedLe CI BJ → CI ≠ BJ →
      (CI = scheme.cell 0 ∧ (BJ = scheme.cell 2 ∨ BJ = scheme.cell 4)) ∨
      (CI = scheme.cell 1 ∧ (BJ = scheme.cell 2 ∨ BJ = scheme.cell 4)) ∨
      (CI = scheme.cell 2 ∧ BJ = scheme.cell 4) := by
    unfold GradedLe; decide
  rcases pairs CI hCI BJ hBJ h hne with
    ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
  · exact singleton_lift 0 (by decide) h p q γ hp hq hγ hag
  · exact singleton_lift 0 (by decide) h p q γ hp hq hγ hag
  · exact singleton_lift 1 (by decide) h p q γ hp hq hγ hag
  · exact singleton_lift 1 (by decide) h p q γ hp hq hγ hag
  · exact bountiful_full_scope rows h p q γ hp hq hγ hag

/-- A complete coded legal domain, with actual two-point geometry and no
remaining lifting hypotheses. Higher-grade nonbottom requests are not served. -/
noncomputable def domain : SemScheme 2 :=
  ⟨scheme, rows, coded, consistent, bountiful, BranchAvailability.complete⟩

def face (i : Fin 2) : Fin 1 ↪ Fin 2 :=
  ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩

theorem face_visible (i : Fin 2) : Finset.univ.image (face i) ∈ scheme.plan := by
  fin_cases i <;> decide

theorem face_cell (i : Fin 2) (c : Cell (scheme.restrictFace (face i) (face_visible i))) :
    CellScheme.restrictFace.toCell scheme (face i) (face_visible i) c = Fin.castAdd 3 i := by
  have hs := CellScheme.restrictFace.scope_toCell_subset scheme (face i) (face_visible i) c
  have ht : ∀ i : Fin 2, ∀ d : Cell scheme,
      scheme.scope d ⊆ Finset.univ.image (face i) → d = Fin.castAdd 3 i := by decide
  exact ht i _ hs

/-- Both ordered singleton domains are literally the original non-mute
singleton faces. Only the two full controller rows have been replaced. -/
theorem faces_preserved (i : Fin 2) :
    domain.restrictFace (face i) (face_visible i) =
      BranchAvailability.domain.restrictFace (face i) (face_visible i) := by
  refine SemScheme.ext rfl ?_
  apply heq_of_eq
  apply Semantics.ext
  funext c d
  change rows.E (CellScheme.restrictFace.toCell scheme (face i) (face_visible i) c) _ =
    BranchAvailability.rows.E
      (CellScheme.restrictFace.toCell scheme (face i) (face_visible i) c) _
  have hrow : ∀ c : Cell scheme, c = 0 ∨ c = 1 →
      ∀ d : scheme.below (scheme.cell c), rows.E c d = BranchAvailability.rows.E c d := by
    rintro c (rfl | rfl) d <;>
      change SlotControllerFamily.value 1 = BranchAvailability.source 1 <;>
      simp [SlotControllerFamily.value, SeparatedGradeOne.band, BranchAvailability.source]
  apply hrow
  have hi : Fin.castAdd 3 i = 0 ∨ Fin.castAdd 3 i = 1 := by fin_cases i <;> simp
  exact hi.imp (fun h => (face_cell i c).trans h) (fun h => (face_cell i c).trans h)

/-- Actual lower-domain sections, not just two scalar readings, amalgamate
without an equality or order condition between the prescribed faces. -/
theorem amalgamate (p : scheme.below (scheme.cell 0) → ExtOrd)
    (q : scheme.below (scheme.cell 1) → ExtOrd)
    (hp : RespectsSemanticsBelow rows (scheme.cell 0) p)
    (hq : RespectsSemanticsBelow rows (scheme.cell 1) q) :
    ∃ r : Cell scheme → ExtOrd, RespectsSemantics rows r ∧
      (∀ d, r d.1 = p d) ∧ (∀ d, r d.1 = q d) := by
  let a : scheme.below (scheme.cell 0) := ⟨0, GradedLe.refl _⟩
  let b : scheme.below (scheme.cell 1) := ⟨1, GradedLe.refl _⟩
  obtain ⟨r, hr, h0, h1, _⟩ := sections (hp.orderly a).symm (hq.orderly b).symm
    (selfVis_max (hp.orderly a).symm (hq.orderly b).symm)
    (le_max_left _ _) (le_max_right _ _)
  refine ⟨r, hr, ?_, ?_⟩
  · intro d
    have hd : d = a := Subtype.ext (singleton_below 0 d.1 d.2)
    subst d
    exact h0
  · intro d
    have hd : d = b := Subtype.ext (singleton_below 1 d.1 d.2)
    subst d
    exact h1

private theorem row_nonbottom (d : Inventory) : DonorSlotAssembly.row source 0 d ≠ ⊥ := by
  rcases d with (_ | u) | j
  · rw [show Sum.inl (none : Option Unit) = fresh from rfl, fresh_reading]
    exact ofOrd_ne_bot _
  · rw [show Sum.inl (some u) = old u from rfl, old_reading]
    exact fun h => ofOrd_ne_bot _ ((FreshSourceSlots.oldSource_bot_iff source u).mp h)
  · change SlotControllerFamily.value (SlotControllerFamily.cross 0 j) ≠ ⊥
    rw [SlotControllerFamily.value,
      ite_eq_right (Nat.ne_of_gt (SlotControllerFamily.cross_pos 0 j))]
    exact ofOrd_ne_bot _

theorem constant_ambient {v : ExtOrd} (hv : SelfVis 1 v) :
    RespectsSemantics rows (extend (fun _ => v)) := by
  apply extend_respects
  apply ordered_joint source 0
  · exact fun _ => hv
  · exact fun d h => False.elim (row_nonbottom d h)
  · exact fun _ _ _ => le_rfl

private theorem nat_visible (n : ℕ) (hn : 1 ≤ n) : SelfVis 1 (ofOrd (n : Ordinal)) := by
  rwa [selfVis_ofOrd_iff, finitePart_natCast]

/-- The old and fresh labels rise independently above the original cap 2,
while every controller cap in the actual grade-two target stays unchanged. -/
theorem positive_cap_regression :
    ∃ r : Cell scheme → ExtOrd, RespectsSemantics rows r ∧
      r 0 = ofOrd 3 ∧ r 1 = ofOrd 4 ∧
      (∀ d, min (r d) (ofOrd 2) = min (extend (fun _ => ofOrd 2) d) (ofOrd 2)) := by
  have ha := (constant_ambient (nat_visible 2 (by decide))).toBelow (Finset.univ, 2)
  obtain ⟨r, hr, h0, h1, hcap⟩ := simultaneous_lift (by decide : 1 ≤ 2) ha
    (nat_visible 3 (by decide)) (nat_visible 4 (by decide)) (nat_visible 2 (by decide))
    (by exact (min_self _).trans (min_eq_right (ofOrd_le_ofOrd.mpr
      (Nat.cast_le.mpr (by decide : (2 : ℕ) ≤ 3)))).symm)
    (by exact (min_self _).trans (min_eq_right (ofOrd_le_ofOrd.mpr
      (Nat.cast_le.mpr (by decide : (2 : ℕ) ≤ 4)))).symm)
  refine ⟨r, hr, h0, h1, fun d => ?_⟩
  have hd : GradedLe (scheme.cell d) (Finset.univ, 2) := by
    have hh : ∀ d : Cell scheme, GradedLe (scheme.cell d) (Finset.univ, 2) := by
      unfold GradedLe; decide
    exact hh d
  exact hcap ⟨d, hd⟩

/-- Literal endpoints remain independent on the installed complete scheme. -/
theorem bottom_top_section :
    ∃ r : Cell scheme → ExtOrd, RespectsSemantics rows r ∧ r 0 = ⊥ ∧ r 1 = ⊤ := by
  obtain ⟨r, hr, h0, h1, _⟩ := sections (selfVis_bot 1) (extVisibilityReplace_top 1 1)
    (extVisibilityReplace_top 1 1) bot_le le_rfl
  exact ⟨r, hr, h0, h1⟩

theorem top_bottom_section :
    ∃ r : Cell scheme → ExtOrd, RespectsSemantics rows r ∧ r 0 = ⊤ ∧ r 1 = ⊥ := by
  obtain ⟨r, hr, h0, h1, _⟩ := sections (extVisibilityReplace_top 1 1) (selfVis_bot 1)
    (extVisibilityReplace_top 1 1) le_rfl bot_le
  exact ⟨r, hr, h0, h1⟩

/-- The output does not satisfy the unique-full-donor hypothesis of the
earlier generic source-refinement theorem. This is not a failure of lifting. -/
theorem no_unique_full_donor (o : Cell scheme)
    (ho : scheme.cell o = (Finset.univ, 1)) : ¬ DonorSourceRefinement.UniqueAt o := by
  have hc : ∀ o : Cell scheme, scheme.cell o = (Finset.univ, 1) → o = 2 ∨ o = 3 := by decide
  rcases hc o ho with rfl | rfl
  · intro h
    have hh := h ⟨3, by unfold GradedLe; decide⟩ rfl
    exact (by decide : (3 : Fin 5) ≠ 2) hh
  · intro h
    have hh := h ⟨2, by unfold GradedLe; decide⟩ rfl
    exact (by decide : (2 : Fin 5) ≠ 3) hh

/-- No one scalar source order accommodates all lawful output labellings:
the two independent singleton labels can occur in either strict order.
Iteration therefore cannot freeze this output into one old source profile. -/
theorem no_common_source_order :
    ¬ ∃ E : Cell scheme → ExtOrd, ∀ p : Cell scheme → ExtOrd,
      RespectsSemantics rows p → ∀ d e, E d ≤ E e → p d ≤ p e := by
  rintro ⟨E, hE⟩
  rcases le_total (E 0) (E 1) with h | h
  · obtain ⟨p, hp, h0, h1⟩ := top_bottom_section
    have hh := hE p hp 0 1 h
    rw [h0, h1] at hh
    exact (not_le_of_gt (bot_lt_top : (⊥ : ExtOrd) < ⊤)) hh
  · obtain ⟨p, hp, h0, h1⟩ := bottom_top_section
    have hh := hE p hp 1 0 h
    rw [h0, h1] at hh
    exact (not_le_of_gt (bot_lt_top : (⊥ : ExtOrd) < ⊤)) hh

end VaughtConjecture.Knight.TwoPointSlots
