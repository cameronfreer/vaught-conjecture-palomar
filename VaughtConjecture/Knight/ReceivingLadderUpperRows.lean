/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingLadderSources
public import VaughtConjecture.Knight.AmbientGradeCharts

/-! # Weighted rows on actual receiving upper domains

Every upper owner uses its complete constructed source, capped at its own
weight. The two mixed copies remain distinct. Orderliness, coding and every
upper-to-upper faithful incidence are proved on the actual lower domains.
Original-owner and ladder incidences remain separate from these results.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ReceivingLadderCarrier

open Transform Value ExtOrd

variable {L : ℕ} {X Q U : Type*} [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC

@[simp] theorem upper_grade (b : Bool) (a : U) (node : Bool) :
    (D).grade (added C hC (.upper b a node)) = 2 :=
  congrArg Prod.snd (added_index C hC (.upper b a node))

/-- Every grade-two owner at a mixed index is one of its actual leaves or nodes. -/
theorem at_upper_index (b : Bool) (d : Cell D) (hd : (D).cell d = (scope b, 2)) :
    ∃ a node, d = added C hC (.upper b a node) := by
  rcases cell_cases C hC d with ⟨a, rfl⟩ | ⟨x, rfl⟩
  · have he := congrArg Prod.fst hd
    rw [old_index] at he
    change (C.scope a).image Fin.castSuccEmb = scope b at he
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (he.symm ▸ fresh_scope b)
    have hv := congrArg Fin.val hi
    have hil := i.isLt
    change i.val = 2 at hv
    omega
  · rw [added_index] at hd
    cases x with
    | request => exact (by decide : (1 : ℕ) ≠ 2) (congrArg Prod.snd hd) |>.elim
    | ladder _ _ => exact (by decide : (1 : ℕ) ≠ 2) (congrArg Prod.snd hd) |>.elim
    | upper b' a node =>
        have he : b' = b := (by decide : ∀ x y : Bool, scope x = scope y → x = y)
          b' b (congrArg Prod.fst hd)
        subst b'
        exact ⟨a, node, rfl⟩
    | apex => exact (by decide : (3 : ℕ) ≠ 2) (congrArg Prod.snd hd) |>.elim

end VaughtConjecture.Knight.ReceivingLadderCarrier

namespace VaughtConjecture.Knight.ReceivingLadderUpperRows

open Transform Value ExtOrd ReceivingLadderCarrier LadderScalarRendering
noncomputable section

variable {L : ℕ} {X Q U : Type*} [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)
  (field : Cell C → X) (request high : X) (profile : Q → X → ℕ)
  (fields : U → X → ExtOrd) (anchor : U → Q) (G : Finset ExtOrd) (H : ExtOrd)

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC
local notation "src" =>
  ReceivingLadderSources.source (L := L) C hC field request high profile fields anchor G H

def weight (a : U) (node : Bool) : ExtOrd := if node then fields a high else H

/-- The new owner's actual row, not a source vector supplied by a completion hypothesis. -/
def row (a : U) (node : Bool) (d : Cell D) : ExtOrd :=
  min (src a d) (weight high fields H a node)

local notation "row₀" => row (L := L) C hC field request high profile fields anchor G H

omit [Fintype X] [Fintype U] in
theorem weight_le (hbound : ∀ a x, fields a x ≤ H) (a : U) (node : Bool) :
    weight high fields H a node ≤ H := by
  cases node
  · exact le_rfl
  · exact hbound a high

omit [Fintype X] [Fintype U] in
theorem weight_visible (hhigh : ∀ a, SelfVis 2 (fields a high)) (hH : SelfVis 2 H)
    (a : U) (node : Bool) : SelfVis 2 (weight high fields H a node) := by
  cases node
  · exact hH
  · exact hhigh a

theorem source_visible (hbot : ⊥ ∈ G) (hG : ∀ h ∈ G, SelfVis 2 h)
    (hH : SelfVis 2 H) (hfields : ∀ a x, SelfVis 1 (fields a x))
    (hold : ∀ a c, SelfVis (C.grade c) (fields a (field c)))
    (hhigh : ∀ a, SelfVis 2 (fields a high)) (a : U) (d : Cell D) :
    SelfVis ((D).grade d) (src a d) := by
  rcases ReceivingLadderCarrier.cell_cases C hC d with ⟨c, rfl⟩ | ⟨z, rfl⟩
  · rw [ReceivingLadderSources.source_old]
    simpa only [CellScheme.grade, old_index] using hold a c
  · cases z with
    | request =>
        rw [ReceivingLadderSources.source_request]
        simpa only [CellScheme.grade, added_index, newIndex] using hfields a request
    | ladder b v =>
        rw [ReceivingLadderSources.source_ladder, ladder_grade]
        exact level_visible (hfields a) (hH.mono (by decide)) _
    | upper b c node =>
        rw [ReceivingLadderSources.source_upper, upper_grade]
        exact selfVis_min (hG _ (SourcePrefixRows.cut_mem hbot _ _))
          (weight_visible high fields H hhigh hH c node)
    | apex => simpa only [ReceivingLadderSources.source, view_added] using
        (selfVis_bot ((D).grade (added C hC .apex)))

theorem row_orderly (hbot : ⊥ ∈ G) (hG : ∀ h ∈ G, SelfVis 2 h)
    (hH : SelfVis 2 H) (hfields : ∀ a x, SelfVis 1 (fields a x))
    (hold : ∀ a c, SelfVis (C.grade c) (fields a (field c)))
    (hhigh : ∀ a, SelfVis 2 (fields a high)) (b : Bool) (a : U) (node : Bool) :
    IsOrderly (fun d : (D).below ((D).cell (added C hC (.upper b a node))) =>
      (D).grade d.1) (fun d => row₀ a node d.1) := by
  intro d
  apply (selfVis_min
    (source_visible C hC field request high profile fields anchor G H
      hbot hG hH hfields hold hhigh a d.1) ?_).symm
  apply (weight_visible high fields H hhigh hH a node).mono
  simpa only [CellScheme.grade, added_index, newIndex] using d.2.2

private theorem coded_min {j : ℕ} {x y : ExtOrd}
    (hx : IsCodedLabel j x) (hy : IsCodedLabel j y) : IsCodedLabel j (min x y) := by
  rcases le_total x y with h | h
  · simpa only [min_eq_left h] using hx
  · simpa only [min_eq_right h] using hy

theorem source_coded (hbot : ⊥ ∈ G) (hG : ∀ h ∈ G, IsCodedLabel 2 h)
    (hH : IsCodedLabel 2 H) (hf : ∀ a x, IsCodedLabel 2 (fields a x))
    (a : U) (d : Cell D) : IsCodedLabel 2 (src a d) := by
  cases hv : view C hC d with
  | inl c => simpa only [ReceivingLadderSources.source, hv] using hf a (field c)
  | inr z =>
    cases z with
    | request => simpa only [ReceivingLadderSources.source, hv] using hf a request
    | ladder b v =>
        simp only [ReceivingLadderSources.source, hv]
        change IsCodedLabel 2
          (level (values (fields a)) H (SupportLadderRows.index profile (anchor a) v))
        rcases level_supported (values (fields a)) H
          (SupportLadderRows.index profile (anchor a) v) with hz | hp | hc
        · exact Or.inl hz
        · obtain ⟨_, x, hx⟩ := mem_values.mp hp
          exact hx ▸ hf a x
        · exact hc.symm ▸ hH
    | upper b c node =>
        simp only [ReceivingLadderSources.source, hv]
        apply coded_min (hG _ (SourcePrefixRows.cut_mem hbot _ _))
        cases node
        · exact hH
        · exact hf c high
    | apex => exact Or.inl (by simp only [ReceivingLadderSources.source, hv])

theorem row_coded (hbot : ⊥ ∈ G) (hG : ∀ h ∈ G, IsCodedLabel 2 h)
    (hH : IsCodedLabel 2 H) (hf : ∀ a x, IsCodedLabel 2 (fields a x))
    (a : U) (node : Bool) (d : Cell D) : IsCodedLabel 2 (row₀ a node d) := by
  apply coded_min (source_coded C hC field request high profile fields anchor G H hbot hG hH hf a d)
  cases node
  · exact hH
  · exact hf a high

theorem row_upper (a c : U) (node full other : Bool) :
    row₀ a node (added C hC (.upper full c other)) =
      min (min (SourcePrefixRows.cut G (fields a) (fields c)) (weight high fields H c other))
        (weight high fields H a node) := by
  rw [row, ReceivingLadderSources.source_upper]
  rfl

theorem diagonal (hH : H ∈ G) (hG : ∀ h ∈ G, h ≤ H)
    (hbound : ∀ a x, fields a x ≤ H) (a : U) (node full : Bool) :
    row₀ a node (added C hC (.upper full a node)) = weight high fields H a node := by
  rw [row_upper, SourcePrefixRows.cut_refl hH hG,
    min_eq_right (weight_le high fields H hbound a node), min_self]

theorem parent_read (hH : H ∈ G) (hG : ∀ h ∈ G, h ≤ H)
    (hbound : ∀ a x, fields a x ≤ H) (a : U) (node full : Bool) :
    row₀ a node (added C hC (.upper full a false)) = weight high fields H a node := by
  rw [row_upper, SourcePrefixRows.cut_refl hH hG]
  simp only [weight, Bool.false_eq_true, ite_false, min_self]
  exact min_eq_right (weight_le high fields H hbound a node)

theorem leaf_row (hbound : ∀ a x, fields a x ≤ H) (a : U) (d : Cell D) :
    row₀ a false d = src a d :=
  min_eq_left (ReceivingLadderSources.source_bound C hC field request high profile fields anchor G H
    hbound a d)

/-- Every new owner has a faithful incidence with every other new source,
using the actual target cap, not only the global ceiling. -/
theorem upper_locality (hbot : ⊥ ∈ G) (hGvis : ∀ h ∈ G, SelfVis 2 h)
    (hH : SelfVis 2 H) (hhigh : ∀ a, SelfVis 2 (fields a high))
    (hL : Fintype.card X + 1 ≤ L)
    (hrank : ∀ a x, profile (anchor a) x = fieldRank (fields a) x)
    (hbound : ∀ a x, fields a x ≤ H) (hG : ∀ h ∈ G, h ≤ H)
    (a c : U) (node full other : Bool) :
    TransformsTo
      (fun d : (D).below ((D).cell (added C hC (.upper full c other))) => (D).grade d.1)
      (fun d => row₀ c other d.1)
      (fun d => min (row₀ a node d.1) (row₀ a node (added C hC (.upper full c other)))) := by
  let t := min (min (SourcePrefixRows.cut G (fields a) (fields c)) (weight high fields H c other))
    (weight high fields H a node)
  have ht : SelfVis 2 t := selfVis_min
    (selfVis_min (hGvis _ (SourcePrefixRows.cut_mem hbot _ _))
      (weight_visible high fields H hhigh hH c other))
    (weight_visible high fields H hhigh hH a node)
  have he : (fun d : (D).below ((D).cell (added C hC (.upper full c other))) =>
      min (row₀ c other d.1) t) =
      (fun d => min (row₀ a node d.1) (row₀ a node (added C hC (.upper full c other)))) := by
    funext d
    have ha := ReceivingLadderSources.source_prefix C hC field request high profile
      fields anchor G H hbot hL hrank hbound hG (SourcePrefixRows.cut_mem hbot _ _)
      (SourcePrefixRows.agree_cut hbot (fields a) (fields c)) d.1
    rw [row_upper]
    simp only [row, t]
    grind
  have hcap := (TransformsTo.refl (grade := fun d => (D).grade d.1) (fun d :
    (D).below ((D).cell (added C hC (.upper full c other))) => row₀ c other d.1)).cap
    (K := 2) (fun d => by simpa only [CellScheme.grade, added_index, newIndex] using d.2.2) ht
  rw [he] at hcap
  exact hcap

/-- Exact upper-row installation only: no consistency or lifting premise. -/
def HasUpperRows (sem : Semantics D) : Prop :=
  ∀ (b : Bool) (a : U) (node : Bool)
    (d : (D).below ((D).cell (added C hC (.upper b a node)))),
    sem.E (added C hC (.upper b a node)) d = row₀ a node d.1

end
end VaughtConjecture.Knight.ReceivingLadderUpperRows
