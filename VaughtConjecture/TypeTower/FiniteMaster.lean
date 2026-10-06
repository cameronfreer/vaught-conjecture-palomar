/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.TypeTower.RealizationExtension

/-! # Finite master charts

A finite master is one labelled injective tuple. Its chart is derived, not additional
state: a tuple factoring through the master receives its partial pullback, and a tuple
outside the master receives `none`. Exact extension retains the whole old master.
Consequently every old supported tuple retains its entire option, including invisibility.

Only the tower's **conditional** composition law is used. An invisible intermediate
face need not have invisible subfaces. An arity-zero master is permitted and labelled;
it is not the everywhere-undefined realization.
-/

@[expose] public section

namespace VaughtConjecture.TypeTower

universe u v w
variable {Λ : Type v} [Preorder Λ] {T : TypeTower.{u} Λ} {α : Λ} {M : Type w}

/-- One labelled finite tuple; the partial realization is its derived chart. -/
structure FiniteMaster (T : TypeTower.{u} Λ) (α : Λ) (M : Type w) where
  n : ℕ
  tuple : Fin n ↪ M
  type : T.Ty α n

namespace FiniteMaster

variable (s : FiniteMaster T α M)

/-- Supported means inside the master, whether or not the face is visible. -/
def Supported {n : ℕ} (t : Fin n ↪ M) : Prop :=
  ∃ f : Fin n ↪ Fin s.n, f.trans s.tuple = t

theorem factor_unique {n : ℕ} {t : Fin n ↪ M} {f g : Fin n ↪ Fin s.n}
    (hf : f.trans s.tuple = t) (hg : g.trans s.tuple = t) : f = g := by
  apply Function.Embedding.ext
  intro i
  exact s.tuple.injective (congrArg (fun e : Fin n ↪ M => e i) (hf.trans hg.symm))

theorem supported_iff {n : ℕ} (t : Fin n ↪ M) :
    s.Supported t ↔ ∀ i, t i ∈ Set.range s.tuple := by
  classical
  constructor
  · rintro ⟨f, rfl⟩ i
    exact ⟨f i, rfl⟩
  · intro h
    choose f hf using h
    refine ⟨⟨f, fun i j hij => t.injective ?_⟩, ?_⟩
    · exact (hf i).symm.trans ((congrArg s.tuple hij).trans (hf j))
    · ext i
      exact hf i

open Classical in
/-- The face diagram of a master, undefined outside its support. -/
noncomputable def chart : T.Realization α M where
  eval t := if h : s.Supported t then T.pull h.choose s.type else none

theorem chart_factor {n : ℕ} (f : Fin n ↪ Fin s.n) :
    s.chart.eval (f.trans s.tuple) = T.pull f s.type := by
  have h : s.Supported (f.trans s.tuple) := ⟨f, rfl⟩
  have hf : h.choose = f := s.factor_unique h.choose_spec rfl
  simp only [chart, dite_eq_left h, hf]

theorem chart_nonfactor {n : ℕ} (t : Fin n ↪ M) (h : ¬ s.Supported t) :
    s.chart.eval t = none := dite_eq_right h

@[simp] theorem chart_self : s.chart.eval s.tuple = some s.type := by
  simpa using (s.chart_factor (Function.Embedding.refl _)).trans (T.pull_refl s.type)

theorem supported_of_eval {n : ℕ} {t : Fin n ↪ M} {p : T.Ty α n}
    (h : s.chart.eval t = some p) : s.Supported t := by
  by_contra ht
  rw [s.chart_nonfactor t ht] at h
  cases h

theorem consistent : s.chart.IsExactParentConsistent := by
  intro m n t p f hp
  obtain ⟨g, rfl⟩ := s.supported_of_eval hp
  rw [s.chart_factor] at hp
  rw [← Function.Embedding.trans_assoc, s.chart_factor]
  exact T.pull_trans g f s.type p hp

/-- Exact consistency and support determine the chart uniquely. -/
theorem eq_chart {A : T.Realization α M} (hA : A.IsExactParentConsistent)
    (hs : A.eval s.tuple = some s.type)
    (hsupport : ∀ {n} (t : Fin n ↪ M), (A.eval t).isSome → s.Supported t) :
    A = s.chart := by
  classical
  apply Realization.ext
  intro n t
  by_cases ht : s.Supported t
  · obtain ⟨f, rfl⟩ := ht
    exact (hA s.tuple s.type f hs).trans (s.chart_factor f).symm
  · rw [s.chart_nonfactor t ht]
    cases h : A.eval t with
    | none => rfl
    | some p => exact False.elim (ht (hsupport t (by rw [h]; rfl)))

/-- The larger master retains the old tuple and its type literally. -/
def Extends (s t : FiniteMaster T α M) : Prop :=
  ∃ f : Fin s.n ↪ Fin t.n, f.trans t.tuple = s.tuple ∧ T.pull f t.type = some s.type

theorem Extends.refl (s : FiniteMaster T α M) : s.Extends s :=
  ⟨Function.Embedding.refl _, rfl, T.pull_refl _⟩

theorem Extends.trans {s t r : FiniteMaster T α M} (h : s.Extends t)
    (h' : t.Extends r) : s.Extends r := by
  obtain ⟨f, hf, hp⟩ := h
  obtain ⟨g, hg, hq⟩ := h'
  refine ⟨f.trans g, ?_, (T.pull_trans g f r.type t.type hq).trans hp⟩
  rw [Function.Embedding.trans_assoc, hg, hf]

instance : Preorder (FiniteMaster T α M) where
  le := Extends
  le_refl := Extends.refl
  le_trans _ _ _ := Extends.trans

theorem Extends.range_mono {s t : FiniteMaster T α M} (h : s.Extends t) :
    Set.range s.tuple ⊆ Set.range t.tuple := by
  obtain ⟨f, hf, _⟩ := h
  rintro x ⟨i, rfl⟩
  exact ⟨f i, congrArg (fun e : Fin s.n ↪ M => e i) hf⟩

theorem Extends.supported {s t : FiniteMaster T α M} (h : s.Extends t)
    {n : ℕ} {a : Fin n ↪ M} (ha : s.Supported a) : t.Supported a :=
  (t.supported_iff a).mpr fun i => h.range_mono ((s.supported_iff a).mp ha i)

/-- Both visible labels and decided invisible faces persist. -/
theorem Extends.eval_eq {s t : FiniteMaster T α M} (h : s.Extends t)
    {n : ℕ} {a : Fin n ↪ M} (ha : s.Supported a) : t.chart.eval a = s.chart.eval a := by
  obtain ⟨f, hf, hp⟩ := h
  obtain ⟨g, rfl⟩ := ha
  rw [s.chart_factor, ← hf, ← Function.Embedding.trans_assoc, t.chart_factor]
  exact T.pull_trans f g t.type s.type hp

/-- Positive chart extension already forces literal retention of the full master. -/
theorem extends_iff (t : FiniteMaster T α M) : s.Extends t ↔ s.chart.Extends t.chart := by
  constructor
  · intro h n a p hp
    exact (h.eval_eq (s.supported_of_eval hp)).trans hp
  · intro h
    have hp := h s.tuple s.type s.chart_self
    obtain ⟨f, hf⟩ := t.supported_of_eval hp
    exact ⟨f, hf, (t.chart_factor f).symm.trans (hf ▸ hp)⟩

end FiniteMaster
end VaughtConjecture.TypeTower
