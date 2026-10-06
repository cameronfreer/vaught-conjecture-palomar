/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneConservativeLifting

/-! # Actual rows from a separated grade-one source profile

Grade-one rows are literal restrictions of one profile. Other rows are mute.
The profile is visible at grade one, monotone along same-grade availability
requests, and has at most one value in each source block. These are source
conditions, not assumptions of consistency, sections, or bountifulness.

Consistency and all inhabited grade-one lifts follow. The construction is
deliberately restricted: it does not preserve arbitrary pre-existing rows,
and it has no non-mute higher-grade controller.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SeparatedGradeOne

open AmalgamationPlan Transform Value ExtOrd FullRowLifting

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- The source data of the construction; cells are never quotiented by value. -/
structure Profile (D : CellScheme A) where
  source : Cell D → ExtOrd
  visible : ∀ d, SelfVis 1 (source d)
  separated : ∀ d e, blockFloor (source d) = blockFloor (source e) → source d = source e
  available : ∀ d e, D.scope d ⊆ D.scope e → D.grade d = 1 → D.grade e = 1 →
    source d ≤ source e

namespace Profile

variable (F : Profile D)

/-- All rows are actual functions: shared-profile restrictions at grade one,
and constant bottom at the other grades. -/
def rows : Semantics D where
  E c d := if D.grade c = 1 then F.source d.1 else ⊥
  orderly c d := by
    split_ifs with hc
    · have hd : D.grade d.1 = 1 := le_antisymm (hc ▸ d.2.2) (D.grade_pos d.1)
      simpa only [hd] using (F.visible d.1).symm
    · exact (selfVis_bot _).symm

@[simp] theorem row_one {c : Cell D} (hc : D.grade c = 1)
    (d : D.below (D.cell c)) : F.rows.E c d = F.source d.1 := by
  simp only [rows, hc, ↓reduceIte]

@[simp] theorem row_mute {c : Cell D} (hc : D.grade c ≠ 1)
    (d : D.below (D.cell c)) : F.rows.E c d = ⊥ := by
  simp only [rows, hc, ↓reduceIte]

/-- Joint consistency, including actual availability inside every owner's
lower domain, follows directly from the source profile. -/
theorem consistent : F.rows.IsConsistent := by
  intro c
  refine ⟨F.rows.orderly c, ?_, ?_⟩
  · intro d
    by_cases hc : D.grade c = 1
    · have hd : D.grade d.1 = 1 := le_antisymm (hc ▸ d.2.2) (D.grade_pos d.1)
      have ht := (TransformsTo.refl
        (grade := fun e : D.below (D.cell d.1) => D.grade e.1) (F.rows.E d.1)).cap
        (fun e => e.2.2.trans hd.le) (F.visible d.1)
      simpa only [rows, hc, hd, ↓reduceIte, CellScheme.below.incl] using ht
    · have ht := (TransformsTo.refl
        (grade := fun e : D.below (D.cell d.1) => D.grade e.1) (F.rows.E d.1)).cap
        (fun e => e.2.2) (selfVis_bot (D.grade d.1))
      simpa only [F.row_mute hc, min_bot_right] using ht
  · intro d e hs _
    refine ⟨e, rfl, ?_⟩
    by_cases hc : D.grade c = 1
    · rw [F.row_one hc, F.row_one hc]
      exact F.available d.1 e.1 hs
        (le_antisymm (hc ▸ d.2.2) (D.grade_pos d.1))
        (le_antisymm (hc ▸ e.2.2) (D.grade_pos e.1))
    · simp only [F.row_mute hc, le_refl]

variable {CI BJ : Finset ι × ℕ}

theorem controller_row (c : Controller D BJ) (hgrade : BJ.2 = 1) (d : D.below BJ) :
    c.row F.rows d = F.source d.1 :=
  F.row_one ((congrArg Prod.snd c.2).trans hgrade) _

/-- Every block implication is already downward in the common source order.
This is the property the failed agreement-cap tower does not supply. -/
theorem edge_le (hgrade : BJ.2 = 1) (c : Controller D BJ) (d e : D.below BJ)
    (h : CutGraph.Edge (c.row F.rows) (CutGraph.blocks F.rows) d e) :
    F.source e.1 ≤ F.source d.1 := by
  rcases h with h | ⟨b, f, hb, rfl⟩
  · simpa only [F.controller_row c hgrade] using h
  · obtain ⟨d', f', rfl, rfl, he⟩ := hb
    have hb : D.grade b.1 = 1 := grade_eq_one hgrade b
    rw [F.row_one hb, F.row_one hb] at he
    have heq := F.separated d'.1 f'.1 he
    have hlow := CutGraph.lower_le_right (c.row F.rows) b (CellScheme.below.incl b f')
    rw [F.controller_row c hgrade, F.controller_row c hgrade] at hlow
    exact hlow.trans_eq heq.symm

/-- No target path creates a new bottom consequence at a protected occurrence. -/
theorem conservative (h : GradedLe CI BJ) (hface : CI.2 = 1) (htarget : BJ.2 = 1)
    (b : Controller D CI) (c : Controller D BJ) :
    CutGraph.Conservative (b.row F.rows) (c.row F.rows)
      (CutGraph.blocks F.rows) (CutGraph.blocks F.rows) (CellScheme.below.mono h) := by
  intro a d hd
  obtain ⟨e, he, hed⟩ := hd
  have path_le : ∀ {u v : D.below BJ},
      Relation.ReflTransGen (CutGraph.Edge (c.row F.rows) (CutGraph.blocks F.rows)) u v →
      F.source v.1 ≤ F.source u.1 := by
    intro u v huv
    induction huv with
    | refl => exact le_rfl
    | tail _ hf ih => exact (F.edge_le htarget c _ _ hf).trans ih
  have hle : F.source d.1 ≤ F.source e.1 := path_le hed
  rcases he with he | he
  · have hed : b.row F.rows d = ⊥ := by
      rw [F.controller_row b hface]
      rw [F.controller_row c htarget] at he
      exact le_antisymm (he ▸ hle) bot_le
    exact CutGraph.forced_self (Or.inl hed)
  · cases a with
    | none => cases he
    | some a =>
      have hea : CellScheme.below.mono h a = e := Option.some.inj he
      subst e
      refine ⟨a, Or.inr rfl, .single (Or.inl ?_)⟩
      simpa only [F.controller_row b hface, CellScheme.below.mono_val] using hle

/-- All lawful grade-one face inputs lift against arbitrary target-local
ambients at every original cap, bottom and literal top included. -/
theorem liftsAt (hinj : Function.Injective D.cell) (h : GradedLe CI BJ)
    (hface : CI.2 = 1) (htarget : BJ.2 = 1)
    (b : Controller D CI) (c : Controller D BJ) : LiftsAt F.rows h := by
  apply (CutGraph.liftsAt_iff_conservative F.consistent h hface htarget b c
    (fun b' => Subtype.ext (hinj (b'.2.trans b.2.symm)))
    (fun c' => Subtype.ext (hinj (c'.2.trans c.2.symm)))).mpr
  refine ⟨rowTrace_of_restriction h b c ?_, F.conservative h hface htarget b c⟩
  intro d
  rw [F.controller_row c htarget, F.controller_row b hface]
  rfl

end Profile

end VaughtConjecture.Knight.SeparatedGradeOne
