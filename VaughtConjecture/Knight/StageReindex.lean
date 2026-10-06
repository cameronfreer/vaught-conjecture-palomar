/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Type
public import VaughtConjecture.Knight.PartialSections

/-! # Reindexing of labelled types, and the transport theorem for face restrictions

**Reindexing** (`StageType.Reindex q q'`): a bijection of the cells preserving the plan, the
graded indices, the labels and the rows.  It is the literal "same labelled type up to the
enumeration of the cells".

**The transport theorem** (`reindex_restrictFace`): a labelled type `q` whose cells are in
bijection with the visible cells of `t` along a face `f` — graded indices, labels and rows
agreeing through the bijection — is a reindexing of the face restriction `t.restrictFace f`.
No monotonicity of the bijection is needed: the canonical enumeration of the restriction
(`toCell`, increasing) is absorbed by the reindexing.  `restrictEquiv` is the bijection between
the restricted cells and the visible cells.

Consumers: the fresh face of the two-context amalgam (`Knight/TwoContextPrescribedPair.lean`),
where the copy embedding is not monotone in the cell indices, so `typeMap` gives only the
restriction with the induced enumeration; the transport theorem turns it into the literal
face equation up to reindexing.  Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

section Reindex

variable {α : Ordinal.{0}} {m n : ℕ}

/-- **A reindexing of labelled types**: a bijection of cells preserving the plan, the graded
indices, the labels and the rows. -/
def StageType.Reindex (q q' : S α m) : Prop :=
  q'.scheme.scheme.plan = q.scheme.scheme.plan ∧
  ∃ e : Cell q.scheme.scheme ≃ Cell q'.scheme.scheme,
    (∀ c, q'.scheme.scheme.cell (e c) = q.scheme.scheme.cell c) ∧
    (∀ c, q'.label (e c) = q.label c) ∧
    (∀ (Sig : Cell q.scheme.scheme) (d : q.scheme.scheme.below (q.scheme.scheme.cell Sig))
      (hd : GradedLe (q'.scheme.scheme.cell (e d.1)) (q'.scheme.scheme.cell (e Sig))),
      q'.scheme.rows.E (e Sig) ⟨e d.1, hd⟩ = q.scheme.rows.E Sig d)

/-- The restricted cells are in bijection with the visible cells (the cell map, onto). -/
noncomputable def restrictEquiv (D : CellScheme (ι := Fin n) Finset.univ) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ D.plan) :
    Cell (D.restrictFace f hr) ≃ {d : Cell D // D.scope d ⊆ Finset.univ.image f} :=
  Equiv.ofBijective
    (fun i => ⟨toCell D f hr i, CellScheme.restrictFace.scope_toCell_subset D f hr i⟩)
    ⟨fun i j h => by
      have h' := congrArg Subtype.val h
      dsimp only at h'
      exact CellScheme.restrictFace.toCell_injective D f hr h',
     fun d => by
      obtain ⟨i, hi⟩ := CellScheme.restrictFace.exists_toCell_eq D f hr d.2
      exact ⟨i, Subtype.ext hi⟩⟩

theorem restrictEquiv_val (D : CellScheme (ι := Fin n) Finset.univ) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ D.plan) (i : Cell (D.restrictFace f hr)) :
    (restrictEquiv D f hr i).1 = toCell D f hr i := rfl

theorem toCell_restrictEquiv_symm (D : CellScheme (ι := Fin n) Finset.univ) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ D.plan) (d : {d : Cell D // D.scope d ⊆ Finset.univ.image f}) :
    toCell D f hr ((restrictEquiv D f hr).symm d) = d.1 := by
  rw [← restrictEquiv_val, Equiv.apply_symm_apply]

theorem restrictFace_cell_eq (D : CellScheme (ι := Fin n) Finset.univ) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ D.plan) (i : Cell (D.restrictFace f hr)) :
    (D.restrictFace f hr).cell i = D.pullCell f (toCell D f hr i) := rfl

/-- **The transport theorem**: a labelled type in bijection with the visible cells of `t` along
`f`, with agreeing indices, labels and rows, is a reindexing of the face restriction. -/
theorem reindex_restrictFace (t : S α n) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ t.scheme.scheme.plan) (q : S α m)
    (φ : Cell q.scheme.scheme ≃
      {d : Cell t.scheme.scheme // t.scheme.scheme.scope d ⊆ Finset.univ.image f})
    (hplan : (t.scheme.scheme.restrictFace f hr).plan = q.scheme.scheme.plan)
    (hcell : ∀ c, t.scheme.scheme.pullCell f (φ c).1 = q.scheme.scheme.cell c)
    (hlabel : ∀ c, t.label (φ c).1 = q.label c)
    (hrow : ∀ (Sig : Cell q.scheme.scheme) (d : q.scheme.scheme.below (q.scheme.scheme.cell Sig))
      (d' : t.scheme.scheme.below (t.scheme.scheme.cell (φ Sig).1)),
      d'.1 = (φ d.1).1 → t.scheme.rows.E (φ Sig).1 d' = q.scheme.rows.E Sig d) :
    StageType.Reindex q (t.restrictFace f hr) := by
  refine ⟨hplan, φ.trans (restrictEquiv t.scheme.scheme f hr).symm, ?_, ?_, ?_⟩
  · intro c
    change (t.scheme.scheme.restrictFace f hr).cell ((restrictEquiv _ f hr).symm (φ c)) = _
    rw [restrictFace_cell_eq, toCell_restrictEquiv_symm]
    exact hcell c
  · intro c
    change t.label (toCell t.scheme.scheme f hr ((restrictEquiv _ f hr).symm (φ c))) = _
    rw [toCell_restrictEquiv_symm]
    exact hlabel c
  · intro Sig d hd
    change t.scheme.rows.E (toCell t.scheme.scheme f hr ((restrictEquiv _ f hr).symm (φ Sig)))
      (belowMap t.scheme.scheme f hr _ ⟨_, hd⟩) = _
    have e1 := toCell_restrictEquiv_symm t.scheme.scheme f hr (φ Sig)
    have e2 := toCell_restrictEquiv_symm t.scheme.scheme f hr (φ d.1)
    have hle : GradedLe (t.scheme.scheme.cell (φ d.1).1) (t.scheme.scheme.cell (φ Sig).1) := by
      have h0 := (belowMap t.scheme.scheme f hr ((restrictEquiv _ f hr).symm (φ Sig))
        ⟨(restrictEquiv _ f hr).symm (φ d.1), hd⟩).2
      change GradedLe (t.scheme.scheme.cell (toCell _ f hr ((restrictEquiv _ f hr).symm (φ d.1))))
        (t.scheme.scheme.cell (toCell _ f hr ((restrictEquiv _ f hr).symm (φ Sig)))) at h0
      rw [e1, e2] at h0; exact h0
    refine (t.scheme.rows.E_congr' e1 (d' := ⟨(φ d.1).1, hle⟩) ?_).trans (hrow Sig d _ rfl)
    exact e2

end Reindex

end VaughtConjecture.Knight
