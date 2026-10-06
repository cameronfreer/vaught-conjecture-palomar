/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.MasterChart
public import VaughtConjecture.Knight.Domain

/-! # Finite master states for fixed-height construction

These are the finite master states shared by the exact-family and top-free capped
clients. No request family, enumeration or infinite run is constructed here.
The historical partial-state fields are retained as a compatibility adapter; their
realization is uniquely determined by the finite master.
-/

@[expose] public section

namespace VaughtConjecture.Knight

universe w

open TypeTower
open Value ExtOrd

namespace FixedHeight

open KnightRealization

variable {β : LimitStage} {M : Type w}

/-! ### The run state -/

/-- The fair run's state: a partial state, its single master (tuple and evaluated type),
and the master discipline.  Construction-private bookkeeping — no receipt, failure
certificate, Karp trace, or source link. -/
structure RunState (β : LimitStage) (M : Type w) where
  /-- The partial realization. -/
  A : KnightRealization β M
  /-- It is a partial state. -/
  hA : IsPartialState A
  /-- The master arity. -/
  N : ℕ
  /-- The master tuple. -/
  tup : Fin N ↪ M
  /-- The master type. -/
  P : S β.1 N
  /-- The master is evaluated. -/
  htup : A.eval tup = some P
  /-- The master discipline. -/
  hM : MasteredBy A tup

/-- The historical run state is literally the face diagram of its master. -/
theorem RunState.eq_masterChart (st : RunState β M) :
    st.A = masterChart st.tup st.P :=
  FixedHeight.eq_masterChart st.hA.consistent st.tup st.P st.htup st.hM

/-- Used points of a run state are exactly, not merely contained in, its master. -/
theorem RunState.usedPoints_eq (st : RunState β M) : UsedPoints st.A = Set.range st.tup :=
  usedPoints_eq_range_master st.htup st.hM

/-- The data actually scheduled; all partial-state bookkeeping is derived from it. -/
def RunState.master (st : RunState β M) : FiniteMaster knightTower β M :=
  ⟨st.N, st.tup, st.P⟩

theorem RunState.chart_eq (st : RunState β M) : st.master.chart = st.A :=
  st.eq_masterChart.symm

theorem RunState.master_extends {st st' : RunState β M} (h : Extends st.A st'.A) :
    st.master ≤ st'.master := by
  apply (st.master.extends_iff st'.master).mpr
  intro n t p hp
  rw [RunState.chart_eq] at hp ⊢
  exact h t p hp

theorem RunState.extends_of_master {st st' : RunState β M} (h : st.master ≤ st'.master) :
    Extends st.A st'.A := by
  intro n t p hp
  rw [← st.chart_eq] at hp
  rw [← st'.chart_eq]
  exact ((st.master.extends_iff st'.master).mp h) t p hp

/-- Compatibility adapter from a finite master to the historical partial-state record. -/
noncomputable def RunState.ofMaster (s : FiniteMaster knightTower β M) : RunState β M where
  A := s.chart
  hA := ⟨s.consistent, by
    apply (Set.finite_range s.tuple).subset
    exact usedPoints_subset_of_masteredBy (fun {n} t ht => by
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp ht
      exact s.supported_of_eval hp)⟩
  N := s.n
  tup := s.tuple
  P := s.type
  htup := s.chart_self
  hM := by
    intro n t ht
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp ht
    exact s.supported_of_eval hp

/-- A limit stage is positive. -/
theorem LimitStage.pos (β : LimitStage) : (0 : Ordinal.{0}) < β.1 := by
  rcases eq_or_ne β.1 0 with h | h
  · exact absurd (by rw [h, ← Ordinal.bot_eq_zero]; exact isMin_bot) β.2.not_isMin
  · exact pos_iff_ne_zero.mpr h

/-! ### The initial state: an arity-0 master over the mute seed -/

/-- The first master event: an arbitrary arity-0 stage type at the empty tuple over the
mute seed. -/
noncomputable def initState (β : LimitStage) (M : Type w) : RunState β M := by
  exact RunState.ofMaster
    ⟨0, Function.Embedding.ofIsEmpty, Classical.choice (StageType.nonempty β.2 0)⟩

end FixedHeight
end VaughtConjecture.Knight
