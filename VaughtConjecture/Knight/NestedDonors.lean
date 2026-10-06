/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.MixedDonor

/-! # Two nested mixed incidences, and the mute top-grade case

The reviewer's task (2026-09-15): construct two nested mixed incidences together; give the
upper row its actual reading at the lower mixed controller and prove the lower row transforms
to the upper row's capped restriction, including the fresh column and both owner occurrences;
derive the fresh-column agreement across the two donor grades from the actual reference
witness, without assuming it or composing transformations; separately test the top-grade mute
case against larger owners.

**Source pinning at any donor** (`MixedDonor.rep_source_code`): a donor's exact witness reads
its source at the representative as the representative's actual label, a proper value whose
finite part is the representative's offset, below the donor's grade; the invisible-image
argument then pins the source to a proper code with that finite part.  Hence the fresh source
is a code with the requested offset as finite part (`mixedSource_fresh_code`).

**The nested pair** (`lowerRow`, `upperRead`, `nested_transformsTo`).  For donors `D₁ ≤ D₂` in
the graded order, the lower row lives on the lower donor's lower domain with the fresh cell
and **its own owner occurrence** (the lower mixed cell, `none`), reading the owner as the
lower donor's diagonal.  The upper row reads each old cell as the upper donor does, the fresh
cell as its own fresh source, and **the lower mixed cell as the upper donor's reading of the
lower donor**.  The lower row transforms to the upper row capped at that reading.  The
witness is the upper donor's exact bounded witness at the lower donor (`FreeDiagonal`'s
normalization of the receiver's own consistency locality at the lower donor), used **once**:
old cells by its reading equation; the lower owner occurrence by the same equation at the
lower donor itself; the fresh column by clause 5 at the lower donor's grade (its suppressor is
`⊤` there) followed by the **cross-grade agreement**: the upper source at the representative
is pinned to a code with finite part below both grades, so its replacements at the two grades
coincide, and a case split on whether the upper donor reads the representative below or above
its reading of the lower donor closes the capped equation (`fresh_column_agree`).  No
transformation is composed and no agreement is assumed.

**The mute top-grade case** (`transformsTo_bot_source_iff`, `mute_incoming_iff`): a constantly
`⊥` lower row transforms to a capped reading iff that reading is `⊥` at the owner — so a mute
top-grade cell is consistent inside every larger owner **exactly when the larger owner reads it
as `⊥`**; the absence of a same-grade requester removed the availability obstruction, and this
is the remaining incoming locality, satisfiable but not free.

Not here: bottom-cap sections on the resulting small carrier.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

/-! ## A constantly-`⊥` source transforms only to `⊥` -/

/-- A constantly-`⊥` source transforms to a labelling iff that labelling is `⊥`. -/
theorem transformsTo_bot_source_iff {D : Type*} (grade : D → ℕ) (q : D → ExtOrd) :
    TransformsTo grade (fun _ => (⊥ : ExtOrd)) q ↔ ∀ d, q d = ⊥ := by
  constructor
  · rintro ⟨g, σ, -, -, hσ, -, -, heq⟩ d
    rw [heq d, hσ]
    exact min_eq_left bot_le
  · intro h
    have := TransformsTo.to_bot (grade := grade) (fun _ => (⊥ : ExtOrd))
    convert this using 1
    funext d
    exact h d

/-- **The mute incoming locality**: a constantly-`⊥` lower row transforms to a reading capped
at a distinguished owner iff the reading is `⊥` at the owner. -/
theorem mute_incoming_iff {D : Type*} (grade : D → ℕ) (u : D → ExtOrd) (o : D) :
    TransformsTo grade (fun _ => (⊥ : ExtOrd)) (fun d => min (u d) (u o)) ↔ u o = ⊥ := by
  rw [transformsTo_bot_source_iff]
  constructor
  · intro h
    have := h o
    rwa [min_self] at this
  · intro h d
    rw [h]
    exact min_eq_right bot_le

namespace ReferenceContext

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} {C : ReferenceContext R t reqs}
  (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block) {i : Fin reqs.length}

namespace MixedDonor

variable (D : C.MixedDonor i)

include hblocks in
/-- **Source pinning**: the donor's source at the representative is a proper code whose finite
part is the representative's offset. -/
theorem rep_source_code : ∃ b : ℕ, C.p₀.scheme.rows.E D.cell D.rep =
    ofOrd (Ordinal.omega0 * b + C.repOff reqs[i.val].block) := by
  obtain ⟨τ, hτ, -, hread⟩ := D.exists_exact_witness
  have hr := List.getElem_mem i.isLt
  have hrep : τ (C.p₀.scheme.rows.E D.cell D.rep) =
      ofOrd (reqs[i.val].block + C.repOff reqs[i.val].block) := by
    rw [hread]
    change min (C.p₀.label (C.repBase reqs[i.val].block)) (C.p₀.label D.cell) = _
    rw [min_eq_left D.rep_le_label, C.rep_label _ hr]
  rcases C.p₀.scheme.rows_coded D.cell D.rep with hb | ⟨b, j, -, hs⟩
  · rw [hb, hτ.bot] at hrep
    exact False.elim ((ofOrd_ne_bot _) hrep.symm)
  · have hout := finitePart_limitPart_add_nat reqs[i.val].block (C.repOff reqs[i.val].block)
    rw [hblocks _ hr] at hout
    have hfp := finitePart_eq_of_nonvisible_image
      (fun x k hk => hτ.clause5 x (C.p₀.scheme.scheme.grade D.cell)
        (by rw [gTop_of_le le_rfl]; exact le_top) k hk)
      (hs ▸ hrep) (by simpa only [hout] using D.rep_off_lt)
    rw [finitePart_mul_add, hout] at hfp
    exact ⟨b, by simpa only [hfp] using hs⟩

include hblocks in
/-- The fresh source is a code with the requested offset as finite part. -/
theorem mixedSource_fresh_code : ∃ b : ℕ, D.mixedSource (Sum.inr ()) =
    ofOrd (Ordinal.omega0 * b + reqs[i.val].offset) := by
  obtain ⟨b, hb⟩ := D.rep_source_code hblocks
  refine ⟨b, ?_⟩
  rw [mixedSource_fresh, hb, extVisibilityReplace_of_finitePart_lt
    (by simpa only [finitePart_mul_add] using D.rep_off_lt), limitPart_mul_add]

end MixedDonor

/-! ## Two nested incidences -/

section Nested

variable (D₁ D₂ : C.MixedDonor i)
  (hle : GradedLe (C.p₀.scheme.scheme.cell D₁.cell) (C.p₀.scheme.scheme.cell D₂.cell))

/-- The lower donor as an occurrence in the upper donor's lower domain. -/
def lowerIn : D₂.Old := ⟨D₁.cell, hle⟩

/-- An occurrence of the lower domain, lifted to the upper. -/
def liftOld (d : D₁.Old) : D₂.Old := ⟨d.1, d.2.trans hle⟩

/-- **The lower row with its owner occurrence** (`none`): the lower donor's diagonal at the owner,
the lower mixed row elsewhere. -/
noncomputable def lowerRow : Option (D₁.Old ⊕ Unit) → ExtOrd
  | none => C.p₀.scheme.rows.E D₁.cell D₁.owner
  | some x => D₁.mixedSource x

/-- **The upper row's reading on the lower carrier**: the upper donor's reading of each old
cell, the upper fresh source, and at the lower mixed cell the upper donor's reading of the
lower donor. -/
noncomputable def upperRead : Option (D₁.Old ⊕ Unit) → ExtOrd
  | none => C.p₀.scheme.rows.E D₂.cell (lowerIn D₁ D₂ hle)
  | some (Sum.inl d) => C.p₀.scheme.rows.E D₂.cell (liftOld D₁ D₂ hle d)
  | some (Sum.inr _) => D₂.mixedSource (Sum.inr ())

/-- The grades on the lower carrier: the lower mixed cell at the lower donor's grade, the fresh
cell at `g₀`. -/
def nestedGrade (g₀ : ℕ) : Option (D₁.Old ⊕ Unit) → ℕ
  | none => C.p₀.scheme.scheme.grade D₁.cell
  | some (Sum.inl d) => C.p₀.scheme.scheme.grade d.1
  | some (Sum.inr _) => g₀

theorem liftOld_rep : liftOld D₁ D₂ hle D₁.rep = D₂.rep := Subtype.ext rfl

theorem liftOld_owner : liftOld D₁ D₂ hle D₁.owner = lowerIn D₁ D₂ hle := Subtype.ext rfl

/-- The upper donor's reading of the lower donor is self-visible at the lower donor's grade. -/
theorem upper_at_lower_selfVis :
    SelfVis (C.p₀.scheme.scheme.grade D₁.cell)
      (C.p₀.scheme.rows.E D₂.cell (lowerIn D₁ D₂ hle)) :=
  (C.p₀.scheme.rows.orderly D₂.cell (lowerIn D₁ D₂ hle)).symm

/-- **The upper donor's exact bounded witness at the lower donor**: the receiver's own
consistency locality at the lower donor, normalized. -/
theorem exists_nested_witness :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop (C.p₀.scheme.scheme.grade D₁.cell)) τ ∧
      (∀ x, τ x ≤ C.p₀.scheme.rows.E D₂.cell (lowerIn D₁ D₂ hle)) ∧
      (∀ d : D₁.Old, τ (C.p₀.scheme.rows.E D₁.cell d) =
        min (C.p₀.scheme.rows.E D₂.cell (liftOld D₁ D₂ hle d))
          (C.p₀.scheme.rows.E D₂.cell (lowerIn D₁ D₂ hle))) :=
  exists_bounded_exact_capped_witness (c := D₁.owner)
    (p := fun d : D₁.Old => C.p₀.scheme.rows.E D₂.cell (liftOld D₁ D₂ hle d))
    (fun d => d.2.2) (upper_at_lower_selfVis D₁ D₂ hle)
    ((C.p₀.scheme.consistent D₂.cell).locality (lowerIn D₁ D₂ hle))

include hblocks in
/-- **The cross-grade fresh-column agreement**: the replacement at the lower grade of the upper
reading of the representative capped at the upper reading of the lower donor equals the upper
fresh source capped there.  The upper source at the representative is a code with finite part
below both grades, so both replacements land on the same value; a case split on the cap
finishes. -/
theorem fresh_column_agree :
    extVisibilityReplace
      (min (C.p₀.scheme.rows.E D₂.cell D₂.rep) (C.p₀.scheme.rows.E D₂.cell (lowerIn D₁ D₂ hle)))
      (C.p₀.scheme.scheme.grade D₁.cell) reqs[i.val].offset =
    min (D₂.mixedSource (Sum.inr ())) (C.p₀.scheme.rows.E D₂.cell (lowerIn D₁ D₂ hle)) := by
  obtain ⟨b, hb⟩ := D₂.rep_source_code hblocks
  have hb' : D₂.mixedSource (Sum.inr ()) =
      ofOrd (Ordinal.omega0 * b + reqs[i.val].offset) := by
    rw [MixedDonor.mixedSource_fresh, hb, extVisibilityReplace_of_finitePart_lt
      (by simpa only [finitePart_mul_add] using D₂.rep_off_lt), limitPart_mul_add]
  set L := C.p₀.scheme.rows.E D₂.cell (lowerIn D₁ D₂ hle) with hL
  have hj' : C.repOff reqs[i.val].block < C.p₀.scheme.scheme.grade D₁.cell := D₁.rep_off_lt
  have hvis := upper_at_lower_selfVis D₁ D₂ hle
  rw [← hL] at hvis
  rcases ExtOrd.cases L with h0 | h0 | ⟨ℓ, h0⟩
  · rw [h0, min_bot_right, extVisibilityReplace_bot, min_bot_right]
  · exact absurd h0 ((C.p₀.scheme.rows_coded D₂.cell (lowerIn D₁ D₂ hle)).ne_top)
  · rw [h0] at hvis ⊢
    have hfp : C.p₀.scheme.scheme.grade D₁.cell ≤ finitePart ℓ := selfVis_ofOrd_iff.mp hvis
    rw [hb, hb']
    rcases le_or_gt (Ordinal.omega0 * b + (C.repOff reqs[i.val].block : Ordinal)) ℓ with hx | hx
    · -- the representative is read below the lower donor: both sides are the replaced code
      rw [min_eq_left (ofOrd_le_ofOrd.mpr hx), extVisibilityReplace_of_finitePart_lt
        (by simpa only [finitePart_mul_add] using hj'), limitPart_mul_add]
      have hlp : Ordinal.omega0 * b ≤ limitPart ℓ := by
        have := limitPart_mono hx
        rwa [limitPart_mul_add] at this
      refine (min_eq_left (ofOrd_le_ofOrd.mpr ?_)).symm
      calc Ordinal.omega0 * b + (reqs[i.val].offset : Ordinal)
          ≤ limitPart ℓ + (reqs[i.val].offset : Ordinal) := add_le_add_left hlp _
        _ ≤ limitPart ℓ + (finitePart ℓ : Ordinal) :=
            add_le_add_right (Nat.cast_le.mpr (D₁.offset_le.trans hfp)) _
        _ = ℓ := decomposition ℓ
    · -- the representative is read above the lower donor: the cap is below the code's block
      rw [min_eq_right (ofOrd_le_ofOrd.mpr hx.le), extVisibilityReplace_of_le_finitePart hfp]
      have hlp : limitPart ℓ < Ordinal.omega0 * b := by
        by_contra hcon
        have hcon' := not_lt.mp hcon
        have : Ordinal.omega0 * b + (C.repOff reqs[i.val].block : Ordinal) ≤ ℓ :=
          calc Ordinal.omega0 * b + (C.repOff reqs[i.val].block : Ordinal)
              ≤ limitPart ℓ + (finitePart ℓ : Ordinal) :=
                add_le_add hcon' (Nat.cast_le.mpr (hj'.le.trans hfp))
            _ = ℓ := decomposition ℓ
        exact absurd this (not_le.mpr hx)
      refine (min_eq_right (ofOrd_le_ofOrd.mpr ?_)).symm
      have hstep : limitPart ℓ + (finitePart ℓ : Ordinal) ≤ Ordinal.omega0 * b := by
        have := limitPart_add_nat_le_of_lt (α := ℓ)
          (β := Ordinal.omega0 * b + (reqs[i.val].offset : Ordinal))
          (by rwa [limitPart_mul_add]) (finitePart ℓ)
        rwa [limitPart_mul_add] at this
      calc ℓ = limitPart ℓ + (finitePart ℓ : Ordinal) := (decomposition ℓ).symm
        _ ≤ Ordinal.omega0 * b := hstep
        _ ≤ Ordinal.omega0 * b + (reqs[i.val].offset : Ordinal) := le_self_add

include hblocks in
/-- **The lower row transforms to the upper row's capped restriction** on its whole carrier —
old cells, the fresh column, and both owner occurrences — by the upper donor's exact witness at
the lower donor, used once. -/
theorem nested_transformsTo (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D₁.cell) :
    TransformsTo (nestedGrade D₁ g₀) (lowerRow D₁)
      (fun x => min (upperRead D₁ D₂ hle x) (upperRead D₁ D₂ hle none)) := by
  obtain ⟨τ, hτ, -, hread⟩ := exists_nested_witness D₁ D₂ hle
  apply hτ.transformsTo
  intro x
  rcases x with _ | d | u
  · change min (C.p₀.scheme.rows.E D₂.cell (lowerIn D₁ D₂ hle))
        (C.p₀.scheme.rows.E D₂.cell (lowerIn D₁ D₂ hle)) =
      min (τ (C.p₀.scheme.rows.E D₁.cell D₁.owner))
        (gTop (C.p₀.scheme.scheme.grade D₁.cell) (C.p₀.scheme.scheme.grade D₁.cell))
    rw [gTop_of_le le_rfl, min_top_right, hread, liftOld_owner]
  · change min (C.p₀.scheme.rows.E D₂.cell (liftOld D₁ D₂ hle d))
        (C.p₀.scheme.rows.E D₂.cell (lowerIn D₁ D₂ hle)) =
      min (τ (C.p₀.scheme.rows.E D₁.cell d))
        (gTop (C.p₀.scheme.scheme.grade D₁.cell) (C.p₀.scheme.scheme.grade d.1))
    rw [gTop_of_le (show C.p₀.scheme.scheme.grade d.1 ≤ C.p₀.scheme.scheme.grade D₁.cell from
      d.2.2), min_top_right, hread]
  · change min (D₂.mixedSource (Sum.inr ())) (C.p₀.scheme.rows.E D₂.cell (lowerIn D₁ D₂ hle)) =
      min (τ (D₁.mixedSource (Sum.inr ()))) (gTop (C.p₀.scheme.scheme.grade D₁.cell) g₀)
    rw [gTop_of_le hg₀, min_top_right, MixedDonor.mixedSource_fresh D₁,
      hτ.clause5 _ (C.p₀.scheme.scheme.grade D₁.cell)
        (by rw [gTop_of_le le_rfl]; exact le_top) _ D₁.offset_le, hread, liftOld_rep]
    exact (fresh_column_agree hblocks D₁ D₂ hle).symm

end Nested

end ReferenceContext

end VaughtConjecture.Knight
