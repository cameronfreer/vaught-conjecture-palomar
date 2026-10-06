/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LadderScalarRendering
public import VaughtConjecture.Knight.SourcePrefixRows

/-! # Constructed complete sources on the mixed receiving carrier

The first upper layer of new16 is evaluated on actual occurrences. Original
fields are literal, all ladder rungs and shadows use the constructed
ceiling-filled renderer, and upper leaves and numerical nodes use weighted
common-grid cuts. Both mixed copies remain distinct.

Scalar prefix agreement now implies agreement of the entire source, including
every unused rung and every weighted column. Its supported range also makes
prefix-fixing decoding preserve every coordinate. Neither theorem assumes a
completed lower vector. These are source-construction theorems, not a claim
that the complete semantics has been installed or is bountiful.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ReceivingLadderSources

open Transform Value ExtOrd ReceivingLadderCarrier
open LadderScalarRendering
noncomputable section

variable {L : ℕ} {X Q U : Type*} [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)
  (field : Cell C → X) (request high : X) (profile : Q → X → ℕ)
  (fields : U → X → ExtOrd) (anchor : U → Q) (G : Finset ExtOrd) (H : ExtOrd)

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC

/-- Every auxiliary reading is computed from the scalar profile and fixed
catalogues. The reserved grade-three apex has a separate bottom default. -/
def source (a : U) (d : Cell D) : ExtOrd :=
  match view C hC d with
  | .inl c => fields a (field c)
  | .inr .request => fields a request
  | .inr (.ladder _ v) => render profile (anchor a) (fields a) H v
  | .inr (.upper _ b node) =>
      min (SourcePrefixRows.cut G (fields a) (fields b)) (if node then fields b high else H)
  | .inr .apex => ⊥

local notation "src" => source (L := L) C hC field request high profile fields anchor G H

@[simp] theorem source_old (a : U) (d : Cell C) : src a (old C hC d) = fields a (field d) := by
  simp only [source, view_old]

@[simp] theorem source_request (a : U) : src a (added C hC .request) = fields a request := by
  simp only [source, view_added]

@[simp] theorem source_ladder (a : U) (b : Bool) (v : SupportLadderRows.Point L X Q) :
    src a (added C hC (.ladder b v)) = render profile (anchor a) (fields a) H v := by
  simp only [source, view_added]

@[simp] theorem source_upper (a b : U) (full node : Bool) :
    src a (added C hC (.upper full b node)) =
      min (SourcePrefixRows.cut G (fields a) (fields b)) (if node then fields b high else H) := by
  simp only [source, view_added]

/-- The new node's source can be written using the serving profile's own
field, rather than the other node's field. This is a source identity. -/
theorem source_node (hbot : ⊥ ∈ G) (a b : U) (full : Bool) :
    src a (added C hC (.upper full b true)) =
      min (SourcePrefixRows.cut G (fields a) (fields b)) (fields a high) := by
  rw [source_upper]
  simpa only [ite_true, min_comm] using
    (SourcePrefixRows.agree_cut hbot (fields a) (fields b) high).symm

/-- Whole-source agreement on the actual carrier: no physical-prefix or
auxiliary-repair conclusion occurs among the hypotheses. -/
theorem source_prefix (hbot : ⊥ ∈ G) (hL : Fintype.card X + 1 ≤ L)
    (hrank : ∀ a x, profile (anchor a) x = fieldRank (fields a) x)
    (hbound : ∀ a x, fields a x ≤ H) (hgrid : ∀ h ∈ G, h ≤ H)
    {a b : U} {h : ExtOrd} (hh : h ∈ G)
    (hag : ∀ x, min (fields a x) h = min (fields b x) h) (d : Cell D) :
    min (src a d) h = min (src b d) h := by
  have hcut := SourcePrefixRows.le_cut hh hag
  cases hv : view C hC d with
  | inl c => simpa only [source, hv] using hag (field c)
  | inr z =>
    cases z with
    | request => simpa only [source, hv] using hag request
    | ladder full v =>
        simpa only [source, hv] using render_cap_agreement profile hL (hrank a) (hrank b)
          (hbound a) (hbound b) (hgrid h hh) hag v
    | upper full c node =>
        have he := congrArg (fun x => min x h)
          (SourcePrefixRows.cross_agreement hbot (fields a) (fields b) (fields c))
        simp only [min_assoc, min_eq_right hcut] at he
        simpa only [source, hv, min_right_comm] using
          congrArg (fun x => min x (if node then fields c high else H)) he
    | apex => simp only [source, hv]

theorem source_bound (hbound : ∀ a x, fields a x ≤ H) (a : U) (d : Cell D) :
    src a d ≤ H := by
  cases hv : view C hC d with
  | inl c => simpa only [source, hv] using hbound a (field c)
  | inr z =>
    cases z with
    | request => simpa only [source, hv] using hbound a request
    | ladder full v =>
        simp only [source, hv]
        exact level_le (values_bound (hbound a)) _
    | upper full b node =>
        simp only [source, hv]
        apply (min_le_right _ _).trans
        cases node <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact le_rfl
        · exact hbound b high
    | apex => simpa only [source, hv] using (bot_le : (⊥ : ExtOrd) ≤ H)

/-- All current and lower source values are scalar values, grid points or
bottom. In particular spare rungs consume only the reserved ceiling. -/
theorem source_supported (hbot : ⊥ ∈ G) (hH : H ∈ G)
    (j : ℕ) (a : U) (d : Cell D) :
    SourcePrefixRows.Supported G j (fields a) (src a d) := by
  cases hv : view C hC d with
  | inl c =>
      simp only [source, hv]
      exact Or.inr (Or.inr (Or.inl ⟨field c, rfl⟩))
  | inr z =>
    cases z with
    | request =>
        simp only [source, hv]
        exact Or.inr (Or.inr (Or.inl ⟨request, rfl⟩))
    | ladder full v =>
        simp only [source, hv]
        change SourcePrefixRows.Supported G j (fields a)
          (level (values (fields a)) H (SupportLadderRows.index profile (anchor a) v))
        rcases level_supported (values (fields a)) H
          (SupportLadderRows.index profile (anchor a) v) with hz | hp | hc
        · exact Or.inl hz
        · obtain ⟨_, x, hx⟩ := mem_values.mp hp
          exact Or.inr (Or.inr (Or.inl ⟨x, hx.symm⟩))
        · exact Or.inr (Or.inl (hc.symm ▸ hH))
    | upper full b node =>
        have he : src a d = min (SourcePrefixRows.cut G (fields a) (fields b))
            (if node then fields a high else H) := by
          cases node
          · simp only [source, hv, Bool.false_eq_true, ite_false]
          · simpa only [source, hv, ite_true, min_comm] using
              (SourcePrefixRows.agree_cut hbot (fields a) (fields b) high).symm
        rw [he]
        rcases le_total (SourcePrefixRows.cut G (fields a) (fields b))
            (if node then fields a high else H) with hl | hr
        · rw [min_eq_left hl]
          exact Or.inr (Or.inl (SourcePrefixRows.cut_mem hbot _ _))
        · rw [min_eq_right hr]
          cases node
          · exact Or.inr (Or.inl hH)
          · exact Or.inr (Or.inr (Or.inl ⟨high, rfl⟩))
    | apex =>
        simp only [source, hv]
        exact Or.inl rfl

/-- The restriction to every actual ladder copy is a lawful table section,
including its long rows. Original-owner incidences are not asserted here. -/
theorem source_ladder_lawful (hvis : ∀ a x, SelfVis 1 (fields a x))
    (hH : SelfVis 1 H) (hbound : ∀ a x, fields a x ≤ H) (a : U) (b : Bool) :
    SupportLadderRows.Lawful profile
      (fun v => src a (added C hC (.ladder b v))) := by
  have he : (fun v => src a (added C hC (.ladder b v))) =
      render (L := L) profile (anchor a) (fields a) H :=
        funext (source_ladder _ _ _ _ _ _ _ _ _ _ a b)
  rw [he]
  exact render_lawful profile (anchor a) (hvis a) hH (hbound a)

/-- Prefix-fixing decoding retains all old physical caps of the constructed
replacement source. The grid and field receipts are the only scalar inputs. -/
theorem decoded_source_prefix (hbot : ⊥ ∈ G) (hH : H ∈ G)
    (hL : Fintype.card X + 1 ≤ L)
    (hrank : ∀ a x, profile (anchor a) x = fieldRank (fields a) x)
    (hbound : ∀ a x, fields a x ≤ H) (hgrid : ∀ h ∈ G, h ≤ H)
    {a b : U} {h : ExtOrd} (hhG : h ∈ G) {j : ℕ} (hh : SelfVis j h)
    (hag : ∀ x, min (fields a x) h = min (fields b x) h)
    {ν : ExtOrd → ExtOrd} (hν : Witness (gTop j) ν)
    (hfixG : ∀ t ∈ G, t < h → ν t = t)
    (hfix : ∀ x, fields b x < h → ν (fields b x) = fields b x)
    (hreach : h ≤ ν h) (d : Cell D) : min (ν (src b d)) h = min (src a d) h := by
  have he := SourcePrefixRows.decode_supported_prefix hν hh hfixG hfix hreach
    (source_supported (L := L) C hC field request high profile fields anchor G H hbot hH j b)
  exact (he d).trans (source_prefix C hC field request high profile fields anchor G H
    hbot hL hrank hbound hgrid hhG hag d).symm

end
end VaughtConjecture.Knight.ReceivingLadderSources
