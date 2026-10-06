/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneGraphConservativity
public import VaughtConjecture.Knight.GradeOneGraphPreservation

/-! # Exact grade-one lifting from conservative bottom implications

Under consistency and unique grade-one full controllers, unrestricted
lifting is equivalent to source-order trace and reflection of inherited
rooted bottom consequences. The latter includes the no-assumption case
for mandatory bottom sources. There is no cut-extension, section, ambient
completion, or graph-retraction existence hypothesis in the criterion.

All block triples come from the actual semantic rows. The theorem does
not identify KVC's rows, construct geometry, or prove a successor theorem.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting.CutGraph

open AmalgamationPlan Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ CI : Finset ι × ℕ}

/-- The exact source-graph condition, with every actual row block retained. -/
theorem cutTrace_iff_conservative (h : GradedLe CI BJ)
    (b : Controller D CI) (c : Controller D BJ) :
    CutTrace (sem := sem) h b c ↔
      Conservative (b.row sem) (c.row sem) (blocks sem) (blocks sem)
        (CellScheme.below.mono h) := by
  unfold CutTrace
  simp only [admissible_iff]
  exact allCuts_iff_conservative (b.row sem) (c.row sem) _ _ _

/-- All lawful face inputs and target-local ambients, at all permitted
original caps, are governed exactly by these two source-data predicates. -/
theorem liftsAt_iff_conservative (hc : sem.IsConsistent) (h : GradedLe CI BJ)
    (hface : CI.2 = 1) (htarget : BJ.2 = 1)
    (b : Controller D CI) (c : Controller D BJ)
    (hb : ∀ b' : Controller D CI, b' = b) (hc' : ∀ c' : Controller D BJ, c' = c) :
    LiftsAt sem h ↔ RowTrace (sem := sem) h b c ∧
      Conservative (b.row sem) (c.row sem) (blocks sem) (blocks sem)
        (CellScheme.below.mono h) := by
  rw [liftsAt_iff_traces_of_unique hc h hface htarget b c hb hc',
    cutTrace_iff_conservative]

/-- A new rooted consequence supplies a lawful binary face with no section.
This is semantic impossibility, not failure of a chosen replay certificate. -/
theorem no_section_of_new_consequence (hc : sem.IsConsistent) (h : GradedLe CI BJ)
    (hface : CI.2 = 1) (htarget : BJ.2 = 1)
    (b : Controller D CI) (c : Controller D BJ) (Hc : CommonOrder (sem := sem) c)
    (hnew : ¬ Conservative (b.row sem) (c.row sem) (blocks sem) (blocks sem)
      (CellScheme.below.mono h)) :
    ∃ a : Option (D.below CI),
      RespectsSemanticsBelow sem CI (BottomPattern.seed (BottomCut.flag (b.row sem) a)) ∧
      ¬ ∃ s, RespectsSemanticsBelow sem BJ s ∧
        ∀ d, s (CellScheme.below.mono h d) =
          BottomPattern.seed (BottomCut.flag (b.row sem) a) d := by
  classical
  have hz : ¬ CutTrace (sem := sem) h b c :=
    fun hz => hnew ((cutTrace_iff_conservative h b c).mp hz)
  unfold CutTrace at hz
  push Not at hz
  obtain ⟨a, ha, hmiss⟩ := hz
  refine ⟨a, no_section_of_missing_cut hc h hface htarget b Hc a ha ?_⟩
  rintro ⟨t, ht, he⟩
  obtain ⟨d, hd⟩ := hmiss t ht
  exact hd (he d)

end VaughtConjecture.Knight.FullRowLifting.CutGraph
