/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneCutGraph

/-! # Semantic grade-one preservation from implication graphs

The block relation is extracted from every actual nested row and its lower
domain. A retraction fixing the protected occurrences, preserving bottom
sources, and sending target edges to face paths supplies the cut trace.
With source-order trace and unique full controllers this gives every
original-cap lift of every lawful face, not just an installed display.

The graph retraction is a sufficient structural test, not a necessary
condition or a proof that a particular proposed graft satisfies it.
Consistency and the literal source equations are still required. No
grade-two, request-service, or uniform successor claim is made.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ CI : Finset ι × ℕ}

namespace CutGraph

/-- All block triples on the actual target lower domain. Nested occurrences
are included by their own cell maps, not identified by source equality. -/
def blocks (sem : Semantics D) (c d e : D.below BJ) : Prop :=
  ∃ (d' e' : D.below (D.cell c.1)),
    CellScheme.below.incl c d' = d ∧ CellScheme.below.incl c e' = e ∧
      blockFloor (sem.E c.1 d') = blockFloor (sem.E c.1 e')

theorem compatible_iff_closed (z : D.below BJ → Bool) :
    BottomPattern.Compatible sem z ↔ BottomCut.Closed (blocks sem) z := by
  constructor
  · intro h c d e hb hz
    obtain ⟨d', e', rfl, rfl, he⟩ := hb
    exact h c d' e' he hz
  · intro h c d e he hz
    exact h c _ _ ⟨d, e, rfl, rfl, he⟩ hz

/-- The raw graph's admissibility is the previously proved semantic
cut criterion with exactly the same flags and bottom-source obligations. -/
theorem admissible_iff (c : Controller D BJ) (a : Option (D.below BJ)) :
    BottomCut.Admissible (sem := sem) c a ↔ Admissible (c.row sem) (blocks sem) a := by
  exact and_congr (compatible_iff_closed _) Iff.rfl

/-- No ordinal-label or table-witness search occurs in this exact cut test. -/
theorem cutTrace_iff_reachability (h : GradedLe CI BJ)
    (b : Controller D CI) (c : Controller D BJ) :
    CutTrace (sem := sem) h b c ↔
      ∀ a, BottomCut.Admissible (sem := sem) b a → ∀ x,
        Forced (Edge (c.row sem) (blocks sem))
          (Seeds (c.row sem) (CellScheme.below.mono h) (BottomCut.flag (b.row sem) a))
          (CellScheme.below.mono h x) → BottomCut.flag (b.row sem) a x = true := by
  unfold CutTrace
  simp only [admissible_iff c]
  exact forall_congr' fun a => imp_congr_right fun _ =>
    extension_iff (c.row sem) (blocks sem) _ _

/-- A purely source/graph retraction constructs the cut trace for every
admissible protected face pattern. -/
theorem cutTrace_of_retraction (h : GradedLe CI BJ)
    (b : Controller D CI) (c : Controller D BJ)
    (π : D.below BJ → D.below CI) (hπ : ∀ d, π (CellScheme.below.mono h d) = d)
    (hEdge : ∀ d e, Edge (c.row sem) (blocks sem) d e →
      Relation.ReflTransGen (Edge (b.row sem) (blocks sem)) (π d) (π e))
    (hBot : ∀ d, c.row sem d = ⊥ → b.row sem (π d) = ⊥) :
    CutTrace (sem := sem) h b c := by
  intro a ha
  obtain ⟨t, ht, he⟩ := extension_of_retraction (b.row sem) (c.row sem)
    (blocks sem) (blocks sem) (CellScheme.below.mono h) π hπ hEdge hBot a
      ((admissible_iff b a).mp ha)
  exact ⟨t, (admissible_iff c t).mpr ht, he⟩

/-- Every lawful face lifts against every compatible target-local ambient
at the original permitted cap. The inputs contain no section hypothesis. -/
theorem liftsAt_of_retraction (hc : sem.IsConsistent) (h : GradedLe CI BJ)
    (hface : CI.2 = 1) (htarget : BJ.2 = 1)
    (b : Controller D CI) (c : Controller D BJ)
    (hb : ∀ b' : Controller D CI, b' = b) (hc' : ∀ c' : Controller D BJ, c' = c)
    (hTrace : RowTrace (sem := sem) h b c)
    (π : D.below BJ → D.below CI) (hπ : ∀ d, π (CellScheme.below.mono h d) = d)
    (hEdge : ∀ d e, Edge (c.row sem) (blocks sem) d e →
      Relation.ReflTransGen (Edge (b.row sem) (blocks sem)) (π d) (π e))
    (hBot : ∀ d, c.row sem d = ⊥ → b.row sem (π d) = ⊥) :
    LiftsAt sem h :=
  (liftsAt_iff_traces_of_unique hc h hface htarget b c hb hc').mpr
    ⟨hTrace, cutTrace_of_retraction h b c π hπ hEdge hBot⟩

end CutGraph

end VaughtConjecture.Knight.FullRowLifting
