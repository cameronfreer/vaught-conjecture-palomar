/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SupportLadderRows

/-! # Removing duplicate shadows from the complete ladder table

The rung-only table keeps every rank of every anchor, including unused ranks
and the spare top rung. Its rows are literal restrictions of
`SupportLadderRows.row`. A positive-rank shadow is a duplicate of its rung;
a rank-zero shadow is forced bottom.

Restriction and the constructed extension are inverse on lawful sections and
commute with every numerical cap. This proves the base-table equivalence
needed by the new43 shadow-elimination audit. It does not construct a
mixed-scope carrier or prove its bountifulness.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.RungOnlyLadder

open Transform Value ExtOrd

abbrev Point (H : ℕ) (Q : Type*) := Q × Fin H

variable {X Q : Type*} {H : ℕ} {profile : Q → X → ℕ}

/-- The literal inclusion retains all rungs, not just represented fields. -/
def toFull (v : Point H Q) : SupportLadderRows.Point H X Q :=
  SupportLadderRows.rung v.1 v.2

noncomputable def row (profile : Q → X → ℕ) (c v : Point H Q) : ExtOrd :=
  SupportLadderRows.row profile (toFull c) (toFull v)

def Lawful (profile : Q → X → ℕ) (q : Point H Q → ExtOrd) : Prop :=
  (∀ v, SelfVis 1 (q v)) ∧ ∀ c,
    TransformsTo (fun _ : Point H Q => 1) (row profile c)
      (fun v => min (q v) (q c))

def restrict (q : SupportLadderRows.Point H X Q → ExtOrd) : Point H Q → ExtOrd :=
  fun v => q (toFull v)

/-- The rung with the same anchor and positive ceiling as a full-table point. -/
def representative (hbound : ∀ a d, profile a d ≤ H)
    (v : SupportLadderRows.Point H X Q) (hv : 0 < SupportLadderRows.ceiling profile v) :
    Point H Q :=
  (SupportLadderRows.parent v,
    ⟨SupportLadderRows.ceiling profile v - 1, by
      have := SupportLadderRows.ceiling_le hbound v
      omega⟩)

@[simp] theorem representative_parent (hbound : ∀ a d, profile a d ≤ H)
    (v : SupportLadderRows.Point H X Q) (hv : 0 < SupportLadderRows.ceiling profile v) :
    SupportLadderRows.parent (toFull (X := X) (representative hbound v hv)) =
      SupportLadderRows.parent v := rfl

@[simp] theorem representative_ceiling (hbound : ∀ a d, profile a d ≤ H)
    (v : SupportLadderRows.Point H X Q) (hv : 0 < SupportLadderRows.ceiling profile v) :
    SupportLadderRows.ceiling profile (toFull (representative hbound v hv)) =
      SupportLadderRows.ceiling profile v := by
  change SupportLadderRows.ceiling profile v - 1 + 1 = _
  omega

theorem row_congr {c c' v v' : SupportLadderRows.Point H X Q}
    (hc : SupportLadderRows.parent c = SupportLadderRows.parent c')
    (ht : SupportLadderRows.ceiling profile c = SupportLadderRows.ceiling profile c')
    (hv : SupportLadderRows.parent v = SupportLadderRows.parent v')
    (hs : SupportLadderRows.ceiling profile v = SupportLadderRows.ceiling profile v') :
    SupportLadderRows.row profile c v = SupportLadderRows.row profile c' v' := by
  simp only [SupportLadderRows.row, SupportLadderRows.index, hc, ht, hv, hs]

theorem column_zero (c v : SupportLadderRows.Point H X Q)
    (hv : SupportLadderRows.ceiling profile v = 0) :
    SupportLadderRows.row profile c v = ⊥ := by
  simp [SupportLadderRows.row, SupportLadderRows.index, hv]

/-- Positive shadows copy their rung; zero shadows are filled with bottom. -/
noncomputable def extend (hbound : ∀ a d, profile a d ≤ H)
    (q : Point H Q → ExtOrd) (v : SupportLadderRows.Point H X Q) : ExtOrd :=
  if hv : 0 < SupportLadderRows.ceiling profile v then
    q (representative hbound v hv) else ⊥

@[simp] theorem extend_toFull (hbound : ∀ a d, profile a d ≤ H)
    (q : Point H Q → ExtOrd) (v : Point H Q) :
    extend hbound q (toFull v) = q v := by
  simp [extend, representative, toFull, SupportLadderRows.rung,
    SupportLadderRows.ceiling, SupportLadderRows.parent]

@[simp] theorem restrict_extend (hbound : ∀ a d, profile a d ≤ H)
    (q : Point H Q → ExtOrd) : restrict (extend hbound q) = q := by
  funext v
  exact extend_toFull hbound q v

theorem Lawful.restrict {q : SupportLadderRows.Point H X Q → ExtOrd}
    (hq : SupportLadderRows.Lawful profile q) : Lawful profile (restrict q) :=
  ⟨fun v => hq.1 (toFull v), fun c => (hq.2 (toFull c)).reindex toFull⟩

theorem extend_lawful (hbound : ∀ a d, profile a d ≤ H)
    {q : Point H Q → ExtOrd} (hq : Lawful profile q) :
    SupportLadderRows.Lawful profile (extend hbound q) := by
  refine ⟨?_, ?_⟩
  · intro v
    unfold extend
    split_ifs
    · exact hq.1 _
    · rfl
  · intro c
    by_cases hc : 0 < SupportLadderRows.ceiling profile c
    · obtain ⟨g, σ, hg, hgv, hb, hm, hv, hr⟩ :=
        hq.2 (representative hbound c hc)
      refine ⟨g, σ, hg, hgv, hb, hm, hv, ?_⟩
      intro v
      by_cases hp : 0 < SupportLadderRows.ceiling profile v
      · have hs := row_congr (profile := profile)
          (representative_parent hbound c hc) (representative_ceiling hbound c hc)
          (representative_parent hbound v hp) (representative_ceiling hbound v hp)
        simpa only [extend, dite_eq_left hc, dite_eq_left hp, row, hs] using
          hr (representative hbound v hp)
      · have hz : SupportLadderRows.ceiling profile v = 0 := by omega
        simp only [extend, dite_eq_right hp, min_bot_left, column_zero c v hz, hb]
    · have hz : extend hbound q c = ⊥ := dite_eq_right hc
      simpa only [hz, min_bot_right] using
        (TransformsTo.to_bot (grade := fun _ : SupportLadderRows.Point H X Q => 1)
          (SupportLadderRows.row profile c))

/-- Equal columns give equality of their labels, using locality at both owners. -/
theorem full_eq_of_same_parent_ceiling
    {q : SupportLadderRows.Point H X Q → ExtOrd}
    (hq : SupportLadderRows.Lawful profile q)
    {c v : SupportLadderRows.Point H X Q}
    (hp : SupportLadderRows.parent c = SupportLadderRows.parent v)
    (ht : SupportLadderRows.ceiling profile c = SupportLadderRows.ceiling profile v) :
    q c = q v := by
  have hle (a b : SupportLadderRows.Point H X Q)
      (hab : SupportLadderRows.row profile a a = SupportLadderRows.row profile a b) :
      q a ≤ q b := by
    obtain ⟨g, σ, _, _, _, _, _, hr⟩ := hq.2 a
    have he := (hr b).trans ((congrArg (fun z => min (σ z) (g 1)) hab.symm).trans
      (hr a).symm)
    exact min_eq_right_iff.mp (by simpa only [min_self] using he)
  exact le_antisymm
    (hle c v (row_congr rfl rfl hp ht))
    (hle v c (row_congr rfl rfl hp.symm ht.symm))

theorem full_bot_of_zero_ceiling
    {q : SupportLadderRows.Point H X Q → ExtOrd}
    (hq : SupportLadderRows.Lawful profile q)
    (c : SupportLadderRows.Point H X Q)
    (hc : SupportLadderRows.ceiling profile c = 0) : q c = ⊥ := by
  obtain ⟨g, σ, _, _, hb, _, _, hr⟩ := hq.2 c
  simpa only [min_self, column_zero c c hc, hb, min_bot_left] using hr c

/-- Lawfulness forces every deleted coordinate, including zero-rank shadows. -/
theorem extend_restrict (hbound : ∀ a d, profile a d ≤ H)
    {q : SupportLadderRows.Point H X Q → ExtOrd}
    (hq : SupportLadderRows.Lawful profile q) :
    extend hbound (restrict q) = q := by
  funext v
  unfold extend
  split_ifs with hv
  · exact full_eq_of_same_parent_ceiling hq
      (representative_parent hbound v hv) (representative_ceiling hbound v hv)
  · exact (full_bot_of_zero_ceiling hq v (by omega)).symm

theorem lawful_extend_iff (hbound : ∀ a d, profile a d ≤ H)
    (q : Point H Q → ExtOrd) :
    SupportLadderRows.Lawful profile (extend hbound q) ↔ Lawful profile q := by
  constructor
  · intro h
    simpa only [restrict_extend] using Lawful.restrict h
  · exact extend_lawful hbound

/-- The equivalence retains every cap, not only the field readout. -/
theorem extend_cap (hbound : ∀ a d, profile a d ≤ H)
    (q : Point H Q → ExtOrd) (γ : ExtOrd) :
    extend hbound (fun v => min (q v) γ) = fun v => min (extend hbound q v) γ := by
  funext v
  unfold extend
  split_ifs <;> simp

theorem restrict_cap (q : SupportLadderRows.Point H X Q → ExtOrd) (γ : ExtOrd) :
    restrict (fun v => min (q v) γ) = fun v => min (restrict q v) γ := rfl

theorem full_cap_eq_iff (hbound : ∀ a d, profile a d ≤ H)
    {p q : SupportLadderRows.Point H X Q → ExtOrd}
    (hp : SupportLadderRows.Lawful profile p) (hq : SupportLadderRows.Lawful profile q)
    (γ : ExtOrd) :
    (∀ v, min (p v) γ = min (q v) γ) ↔
      ∀ v, min (restrict p v) γ = min (restrict q v) γ := by
  refine ⟨fun h v => h (toFull v), ?_⟩
  intro h v
  have he := congrArg (fun f => extend hbound f v) (funext h)
  rw [extend_cap, extend_cap, extend_restrict hbound hp, extend_restrict hbound hq] at he
  exact he

theorem row_coded (c v : Point H Q) : IsCodedLabel 1 (row profile c v) :=
  SupportLadderRows.row_coded _ _

theorem rows_lawful [Finite X] [Finite Q] (c : Point H Q) :
    Lawful profile (row profile c) :=
  Lawful.restrict (SupportLadderRows.rows_lawful (toFull c))

/-- Row extension restores the original row literally, not just up to lawfulness. -/
theorem extend_row [Finite X] [Finite Q] (hbound : ∀ a d, profile a d ≤ H)
    (c : Point H Q) :
    extend hbound (row profile c) = SupportLadderRows.row profile (toFull c) :=
  extend_restrict hbound (SupportLadderRows.rows_lawful (toFull c))

/-- No shadows, unused rungs, or zero-height exceptions are hidden in this equivalence. -/
noncomputable def lawfulEquiv (hbound : ∀ a d, profile a d ≤ H) :
    {q : Point H Q → ExtOrd // Lawful profile q} ≃
      {q : SupportLadderRows.Point H X Q → ExtOrd // SupportLadderRows.Lawful profile q} where
  toFun q := ⟨extend hbound q.1, extend_lawful hbound q.2⟩
  invFun q := ⟨restrict q.1, Lawful.restrict q.2⟩
  left_inv q := Subtype.ext (restrict_extend hbound q.1)
  right_inv q := Subtype.ext (extend_restrict hbound q.2)

/-- A scalar table on the actual rung-only carrier. -/
noncomputable def image (profile : Q → X → ℕ) (a : Q) (f : ℕ → ExtOrd)
    (v : Point H Q) : ExtOrd :=
  SupportLadderRows.image profile a f (toFull v)

theorem image_lawful [Finite X] [Finite Q] (a : Q) (f : ℕ → ExtOrd)
    (hf : Monotone f) (h0 : f 0 = ⊥) (hv : ∀ i, SelfVis 1 (f i))
    (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥) :
    Lawful (H := H) profile (image profile a f) :=
  Lawful.restrict (SupportLadderRows.image_lawful a f hf h0 hv hp)

/-- The existing long-rung shape theorem applies to the smaller table without
assuming bottom reflection or omitting any unused rank. -/
theorem lawful_iff_shape [Finite X] [Finite Q] [Nonempty Q]
    (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H) (q : Point H Q → ExtOrd) :
    Lawful profile q ↔ (∀ v, q v = ⊥) ∨
      ∃ a f, Monotone f ∧ f 0 = ⊥ ∧ (∀ i, SelfVis 1 (f i)) ∧
        (∀ i, 0 < i → i ≤ H → f i ≠ ⊥) ∧ ∀ v, q v = image profile a f v := by
  constructor
  · intro hq
    rcases (SupportLadderRows.lawful_iff_shape hbound hH _).mp
        (extend_lawful hbound hq) with hz | ⟨a, f, hf, h0, hv, hp, he⟩
    · exact Or.inl (fun v => (extend_toFull hbound q v).symm.trans (hz (toFull v)))
    · exact Or.inr ⟨a, f, hf, h0, hv, hp,
        fun v => (extend_toFull hbound q v).symm.trans (he (toFull v))⟩
  · rintro (hz | ⟨a, f, hf, h0, hv, hp, he⟩)
    · rw [funext hz]
      exact ⟨fun _ => selfVis_bot _, fun c => by
        simpa only [min_self] using
          (TransformsTo.to_bot (grade := fun _ : Point H Q => 1) (row profile c))⟩
    · rw [funext he]
      exact image_lawful a f hf h0 hv hp

/-- Numerical field readout uses the reconstructed duplicates, not new cells. -/
noncomputable def readout [Finite Q] (hbound : ∀ a d, profile a d ≤ H)
    (q : Point H Q → ExtOrd) (d : X) : ExtOrd :=
  SupportLadderRows.readout (extend hbound q) d

theorem readout_image [Finite X] [Finite Q] (hbound : ∀ a d, profile a d ≤ H)
    (a : Q) (f : ℕ → ExtOrd) (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, SelfVis 1 (f i)) (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥) (d : X) :
    readout hbound (image profile a f) d = f (profile a d) := by
  unfold readout
  change SupportLadderRows.readout
    (extend hbound (restrict (SupportLadderRows.image profile a f))) d = _
  rw [extend_restrict hbound (SupportLadderRows.image_lawful a f hf h0 hv hp)]
  exact SupportLadderRows.readout_image hbound a hf d

theorem row_readout [Finite X] [Finite Q] (hbound : ∀ a d, profile a d ≤ H)
    (c : Point H Q) (d : X) :
    readout hbound (row profile c) d =
      SupportLadderRows.source (c.2.val + 1) (profile c.1 d) := by
  rw [readout, extend_row hbound]
  exact SupportLadderRows.row_readout hbound (toFull c) d

end VaughtConjecture.Knight.RungOnlyLadder
