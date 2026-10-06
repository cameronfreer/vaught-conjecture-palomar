/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.NormalForm
public import VaughtConjecture.Knight.Repair
public import VaughtConjecture.Knight.Domain
public import VaughtConjecture.Knight.CappedLifting

/-! # Original-cap extension on the two old coatom faces

The boundary operation in Plan 29 uses only two old lifting clauses. It
does not assume bountifulness, locality, or completion on a new full scope.
The indices and occurrences are those of an actual cell scheme; the rows
outside the two old faces are irrelevant. All grades and caps are variable.

`extend_left` constructs compatible lawful face labellings and preserves
every old boundary coordinate under the original cap. This is a boundary
producer, not yet a supported whole-section operator or an amalgam.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.CoatomBoundaryExtension

open Transform Value ExtOrd
open VaughtConjecture.AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable {sem : Semantics D} {I U V O : Finset ι × ℕ}


/-- The actual union of old occurrence domains, with their overlap
identified by cell identity rather than by equality of source readings. -/
abbrev Boundary (D : CellScheme A) (U V : Finset ι × ℕ) :=
  {d : Cell D // GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V}

def left (d : D.below U) : Boundary D U V := ⟨d.1, Or.inl d.2⟩
def right (d : D.below V) : Boundary D U V := ⟨d.1, Or.inr d.2⟩

/-- Compatible lawful labellings on the two physically retained faces. -/
structure Section (sem : Semantics D) (U V : Finset ι × ℕ) where
  onLeft : D.below U → ExtOrd
  onRight : D.below V → ExtOrd
  left_lawful : RespectsSemanticsBelow sem U onLeft
  right_lawful : RespectsSemanticsBelow sem V onRight
  overlap : ∀ (d : Cell D) (hu : GradedLe (D.cell d) U) (hv : GradedLe (D.cell d) V),
    onLeft ⟨d, hu⟩ = onRight ⟨d, hv⟩

namespace Section

variable (a : Section sem U V)

noncomputable def value (d : Boundary D U V) : ExtOrd := by
  classical
  exact if h : GradedLe (D.cell d.1) U then a.onLeft ⟨d.1, h⟩
    else a.onRight ⟨d.1, d.2.resolve_left h⟩

theorem value_left (d : D.below U) : a.value (left d) = a.onLeft d := by
  simp only [value, left, d.2, ↓reduceDIte]
  rfl

theorem value_right (d : D.below V) : a.value (right d) = a.onRight d := by
  classical
  by_cases h : GradedLe (D.cell d.1) U
  · simp only [value, right, h, ↓reduceDIte]
    exact a.overlap d.1 h d.2
  · simp only [value, right, h, ↓reduceDIte]
    rfl

/-- Both face readbacks include all original controllers and auxiliaries. -/
theorem value_lawful :
    RespectsSemanticsBelow sem U (fun d => a.value (left d)) ∧
    RespectsSemanticsBelow sem V (fun d => a.value (right d)) := by
  simpa only [a.value_left, a.value_right] using ⟨a.left_lawful, a.right_lawful⟩

/-- Read an actual boundary carrier whose every cell belongs to an old face. -/
noncomputable def whole
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (d : Cell D) : ExtOrd := a.value ⟨d, hcover d⟩

theorem whole_left
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (d : D.below U) : a.whole hcover d.1 = a.onLeft d := a.value_left d

theorem whole_right
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (d : D.below V) : a.whole hcover d.1 = a.onRight d := a.value_right d

/-- Lawfulness glues on the actual old boundary. For availability choose
the face containing the target; the requester and witness lie there too.
This does not assert lawfulness after adding a new full-scope owner. -/
theorem whole_respects
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V) :
    RespectsSemantics sem (a.whole hcover) where
  orderly d := by
    rcases hcover d with hd | hd
    · rw [a.whole_left hcover ⟨d, hd⟩]
      exact a.left_lawful.orderly ⟨d, hd⟩
    · rw [a.whole_right hcover ⟨d, hd⟩]
      exact a.right_lawful.orderly ⟨d, hd⟩
  locality c := by
    rcases hcover c with hc | hc
    · have ht := a.left_lawful.locality ⟨c, hc⟩
      have he : (fun d : D.below (D.cell c) =>
          min (a.whole hcover d.1) (a.whole hcover c)) =
          (fun d => min (a.onLeft (CellScheme.below.incl ⟨c, hc⟩ d))
            (a.onLeft ⟨c, hc⟩)) := by
        funext d
        exact congrArg₂ min (a.whole_left hcover ⟨d.1, d.2.trans hc⟩)
          (a.whole_left hcover ⟨c, hc⟩)
      rw [he]
      exact ht
    · have ht := a.right_lawful.locality ⟨c, hc⟩
      have he : (fun d : D.below (D.cell c) =>
          min (a.whole hcover d.1) (a.whole hcover c)) =
          (fun d => min (a.onRight (CellScheme.below.incl ⟨c, hc⟩ d))
            (a.onRight ⟨c, hc⟩)) := by
        funext d
        exact congrArg₂ min (a.whole_right hcover ⟨d.1, d.2.trans hc⟩)
          (a.whole_right hcover ⟨c, hc⟩)
      rw [he]
      exact ht
  availability c t hs hg := by
    have hct : GradedLe (D.cell c) (D.cell t) := ⟨hs, hg.le⟩
    rcases hcover t with ht | ht
    · obtain ⟨w, hw, hle⟩ := a.left_lawful.availability
        ⟨c, hct.trans ht⟩ ⟨t, ht⟩ hs hg
      exact ⟨w.1, hw, (a.whole_left hcover ⟨c, hct.trans ht⟩).trans_le
        (hle.trans_eq (a.whole_left hcover w).symm)⟩
    · obtain ⟨w, hw, hle⟩ := a.right_lawful.availability
        ⟨c, hct.trans ht⟩ ⟨t, ht⟩ hs hg
      exact ⟨w.1, hw, (a.whole_right hcover ⟨c, hct.trans ht⟩).trans_le
        (hle.trans_eq (a.whole_right hcover w).symm)⟩

end Section

/-- A constructed ambient for bottom-cap boundary completion. -/
def bottomSection (sem : Semantics D) (U V : Finset ι × ℕ) : Section sem U V where
  onLeft _ := ⊥
  onRight _ := ⊥
  left_lawful := {
    orderly _ := (extVisibilityReplace_bot _ _).symm
    locality d := by simpa only [min_self] using TransformsTo.to_bot (sem.E d.1)
    availability _ t _ _ := ⟨t, rfl, le_rfl⟩ }
  right_lawful := {
    orderly _ := (extVisibilityReplace_bot _ _).symm
    locality d := by simpa only [min_self] using TransformsTo.to_bot (sem.E d.1)
    availability _ t _ _ := ⟨t, rfl, le_rfl⟩ }
  overlap _ _ _ := rfl

/-- Lift in the left input, then install its overlap in the right input.
The overlap is an exact lower-domain intersection; no anchor is assumed.
Both lift premises are old-face clauses, obtainable by `lift_of_restrictFace`.
The conclusion retains the entire boundary cap vector, not just maxima. -/
theorem extend_left
    (hIU : GradedLe I U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hIU) (hright : CappedLift sem hOV)
    (a : Section sem U V) (p : D.below I → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow sem I p) (hγU : SelfVis U.2 γ) (hγV : SelfVis V.2 γ)
    (hag : ∀ d, min (a.onLeft (CellScheme.below.mono hIU d)) γ = min (p d) γ) :
    ∃ b : Section sem U V,
      (∀ d, min (b.value d) γ = min (a.value d) γ) ∧
      ∀ d, b.value (left (CellScheme.below.mono hIU d)) = p d := by
  obtain ⟨u, hu, hucap, hup⟩ := hleft p a.onLeft γ hp a.left_lawful hγU hag
  let o : D.below O → ExtOrd := fun d => u (CellScheme.below.mono hOU d)
  have ho : RespectsSemanticsBelow sem O o := hu.mono hOU
  have hocap : ∀ d : D.below O,
      min (a.onRight (CellScheme.below.mono hOV d)) γ = min (o d) γ := by
    intro d
    change min (a.onRight ⟨d.1, d.2.trans hOV⟩) γ =
      min (u (CellScheme.below.mono hOU d)) γ
    rw [hucap]
    exact congrArg (fun x => min x γ)
      (a.overlap d.1 (d.2.trans hOU) (d.2.trans hOV)).symm
  obtain ⟨v, hv, hvcap, hvread⟩ := hright o a.onRight γ ho a.right_lawful hγV hocap
  let b : Section sem U V := {
    onLeft := u
    onRight := v
    left_lawful := hu
    right_lawful := hv
    overlap := by
      intro d hdu hdv
      exact (hvread ⟨d, hinter d hdu hdv⟩).symm }
  refine ⟨b, ?_, ?_⟩
  · intro d
    rcases d with ⟨d, hd | hd⟩
    · change min (b.value (left ⟨d, hd⟩)) γ = min (a.value (left ⟨d, hd⟩)) γ
      exact (congrArg (fun x => min x γ) (b.value_left ⟨d, hd⟩)).trans
        ((hucap ⟨d, hd⟩).trans
          (congrArg (fun x => min x γ) (a.value_left ⟨d, hd⟩).symm))
    · change min (b.value (right ⟨d, hd⟩)) γ = min (a.value (right ⟨d, hd⟩)) γ
      exact (congrArg (fun x => min x γ) (b.value_right ⟨d, hd⟩)).trans
        ((hvcap ⟨d, hd⟩).trans
          (congrArg (fun x => min x γ) (a.value_right ⟨d, hd⟩).symm))
  · intro d
    rw [b.value_left]
    exact hup d

/-- Bottom-cap completion does not need an independently supplied ambient
or selected source row. Both old lifting clauses suffice. -/
theorem section_left
    (hIU : GradedLe I U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hIU) (hright : CappedLift sem hOV)
    (p : D.below I → ExtOrd) (hp : RespectsSemanticsBelow sem I p) :
    ∃ b : Section sem U V, ∀ d,
      b.value (left (CellScheme.below.mono hIU d)) = p d := by
  obtain ⟨b, _, hread⟩ := extend_left hIU hOU hOV hinter hleft hright
    (bottomSection sem U V) p ⊥ hp (extVisibilityReplace_bot _ _)
    (extVisibilityReplace_bot _ _) (fun _ => by simp)
  exact ⟨b, hread⟩

/-- The boundary extension is an actual lawful labelling when the carrier
contains exactly the old boundary inventory. It preserves every occurrence
at the original cap, without imposing any whole new-scope lifting premise. -/
theorem extend_boundary
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hIU : GradedLe I U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hIU) (hright : CappedLift sem hOV)
    (a : Section sem U V) (p : D.below I → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow sem I p) (hγU : SelfVis U.2 γ) (hγV : SelfVis V.2 γ)
    (hag : ∀ d, min (a.onLeft (CellScheme.below.mono hIU d)) γ = min (p d) γ) :
    ∃ r : Cell D → ExtOrd, RespectsSemantics sem r ∧
      (∀ d, min (r d) γ = min (a.whole hcover d) γ) ∧
      ∀ d : D.below I, r d.1 = p d := by
  obtain ⟨b, hcap, hread⟩ := extend_left hIU hOU hOV hinter hleft hright
    a p γ hp hγU hγV hag
  exact ⟨b.whole hcover, b.whole_respects hcover,
    fun d => hcap ⟨d, hcover d⟩, hread⟩

/-- The graded intersection is computed from scopes and grades, not from
selected labels. It may be empty or have an unrealized nominal grade. -/
def overlapIndex (U V : Finset ι × ℕ) : Finset ι × ℕ :=
  (U.1 ∩ V.1, min U.2 V.2)

theorem overlap_le_left : GradedLe (overlapIndex U V) U :=
  ⟨Finset.inter_subset_left, min_le_left _ _⟩

theorem overlap_le_right : GradedLe (overlapIndex U V) V :=
  ⟨Finset.inter_subset_right, min_le_right _ _⟩

theorem below_overlap_iff (d : Cell D) :
    GradedLe (D.cell d) (overlapIndex U V) ↔
      GradedLe (D.cell d) U ∧ GradedLe (D.cell d) V := by
  simp only [GradedLe, overlapIndex, Finset.subset_inter_iff, le_min_iff]
  tauto

/-- Clamp the overlap's nominal grade to its actual cardinality before
invoking an old face's graded-plan bountifulness clause. -/
def overlapTarget (U V : Finset ι × ℕ) : Finset ι × ℕ :=
  (U.1 ∩ V.1, min (min U.2 V.2) (U.1 ∩ V.1).card)

theorem target_le_left : GradedLe (overlapTarget U V) U :=
  ⟨Finset.inter_subset_left, (min_le_left _ _).trans (min_le_left _ _)⟩

theorem target_le_right : GradedLe (overlapTarget U V) V :=
  ⟨Finset.inter_subset_right, (min_le_left _ _).trans (min_le_right _ _)⟩

/-- Clamping drops no occurrence, including any high-grade auxiliary. -/
theorem below_target_iff (d : Cell D) :
    GradedLe (D.cell d) (overlapTarget U V) ↔
      GradedLe (D.cell d) U ∧ GradedLe (D.cell d) V := by
  constructor
  · intro h
    exact ⟨h.trans target_le_left, h.trans target_le_right⟩
  · rintro ⟨hu, hv⟩
    have hs : D.scope d ⊆ U.1 ∩ V.1 := Finset.subset_inter hu.1 hv.1
    exact ⟨hs, le_min (le_min hu.2 hv.2)
      ((D.grade_le_card_scope d).trans (Finset.card_le_card hs))⟩

theorem target_mem_gradedPlan (hR : U.1 ∩ V.1 ∈ D.plan)
    (hU : 0 < U.2) (hV : 0 < V.2) (hne : (U.1 ∩ V.1).Nonempty) :
    overlapTarget U V ∈ Plan.gradedPlan D.plan :=
  Plan.mem_gradedPlan.mpr ⟨hR,
    lt_min (lt_min hU hV) (Finset.card_pos.mpr hne), min_le_right _ _⟩

/-- Disjoint old faces have an empty actual overlap domain, regardless of
their nominal grades. `lift_empty` handles the second lifting step. -/
theorem target_empty (he : U.1 ∩ V.1 = ∅) : IsEmpty (D.below (overlapTarget U V)) := by
  refine ⟨fun d => ?_⟩
  have hg : D.grade d.1 ≤ 0 := by
    have h := d.2.2
    simpa only [overlapTarget, he, Finset.card_empty, min_zero, CellScheme.grade] using h
  exact (Nat.not_lt_of_ge hg) (D.grade_pos d.1)

end VaughtConjecture.Knight.CoatomBoundaryExtension
