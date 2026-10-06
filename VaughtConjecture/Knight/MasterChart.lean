/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FinitePartialState
public import VaughtConjecture.TypeTower.FiniteMaster

/-! # Literal master-chart normal form

An exactly consistent partial realization supported on an evaluated master is
literally its face diagram, including undefined invisible faces. No saturation,
modelhood or nonempty-master assumption is involved.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FixedHeight
open TypeTower KnightRealization
universe w
variable {β : LimitStage} {M : Type w} {N : ℕ}

noncomputable def masterChart (w : Fin N ↪ M) (P : S β.1 N) : KnightRealization β M :=
  (FiniteMaster.mk N w P : FiniteMaster knightTower β M).chart

theorem masterChart_eval_factor (w : Fin N ↪ M) (P : S β.1 N) {n : ℕ}
    (f : Fin n ↪ Fin N) : (masterChart w P).eval (f.trans w) = typeMap f P :=
  FiniteMaster.chart_factor (T := knightTower) ⟨N, w, P⟩ f

theorem masterChart_eval_nonfactor (w : Fin N ↪ M) (P : S β.1 N) {n : ℕ}
    (t : Fin n ↪ M) (ht : ¬ ∃ f : Fin n ↪ Fin N, f.trans w = t) :
    (masterChart w P).eval t = none :=
  FiniteMaster.chart_nonfactor (T := knightTower) ⟨N, w, P⟩ t ht

theorem eq_masterChart {A : KnightRealization β M}
    (hcons : A.IsExactParentConsistent) (w : Fin N ↪ M) (P : S β.1 N)
    (hw : A.eval w = some P) (hmaster : MasteredBy A w) : A = masterChart w P :=
  FiniteMaster.eq_chart (T := knightTower) ⟨N, w, P⟩ hcons hw (fun t ht => hmaster t ht)

theorem eval_invisible_of_master {A : KnightRealization β M}
    (hcons : A.IsExactParentConsistent) {w : Fin N ↪ M} {P : S β.1 N}
    (hw : A.eval w = some P) {n : ℕ} (f : Fin n ↪ Fin N)
    (hf : Finset.univ.image f ∉ P.scheme.scheme.plan) :
    A.eval (f.trans w) = none :=
  (hcons w P f hw).trans (typeMap_eq_none f P hf)

theorem usedPoints_eq_range_master {A : KnightRealization β M}
    {w : Fin N ↪ M} {P : S β.1 N} (hw : A.eval w = some P)
    (hmaster : MasteredBy A w) : UsedPoints A = Set.range w := by
  apply Set.Subset.antisymm (usedPoints_subset_of_masteredBy hmaster)
  intro x hx
  exact ⟨N, w, by rw [hw]; rfl, hx⟩

theorem usedPoints_empty_master {A : KnightRealization β M}
    {w : Fin 0 ↪ M} {P : S β.1 0} (hw : A.eval w = some P)
    (hmaster : MasteredBy A w) : UsedPoints A = ∅ := by
  rw [usedPoints_eq_range_master hw hmaster]
  exact Set.range_eq_empty w

end VaughtConjecture.Knight.FixedHeight
