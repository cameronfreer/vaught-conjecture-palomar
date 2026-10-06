/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model

/-! # Coordinates of a finite cover of a one-point extension

Shared by ordinary one-block comparison and the historical total-chart service. -/

@[expose] public section

namespace VaughtConjecture.Knight

universe w

variable {n : ℕ}

/-! ## Initial segments -/

/-- The initial `n`-segment of `Fin (n + 1 + k)`. -/
def initSeg (n k : ℕ) : Fin n ↪ Fin (n + 1 + k) :=
  Fin.castSuccEmb.trans (Fin.castAddEmb k)

/-- The position of the `(n+1)`-st point in `Fin (n + 1 + k)`. -/
def newPos (n k : ℕ) : Fin (n + 1 + k) := Fin.castAdd k (Fin.last n)

theorem initSeg_apply (n k : ℕ) (i : Fin n) : initSeg n k i = Fin.castAdd k (Fin.castSucc i) :=
  rfl

theorem newPos_ne_initSeg (n k : ℕ) (i : Fin n) : newPos n k ≠ initSeg n k i := by
  intro h
  have := (Fin.castAddEmb k).injective h
  exact (Fin.castSucc_lt_last i).ne' this

/-- A tuple extending `t⌢m` extends `t`. -/
theorem initSeg_trans_of_castAdd {M : Type w} {k : ℕ} {t : Fin n ↪ M} {m : M}
    (hm : m ∉ Set.range t) {s : Fin (n + 1 + k) ↪ M}
    (hs : (Fin.castAddEmb k).trans s = snoc t m hm) :
    (initSeg n k).trans s = t := by
  rw [initSeg, Function.Embedding.trans_assoc, hs, castSuccEmb_trans_snoc]

/-- Restricting a `(k+1)`-point extension to `n + 1` points is concatenating the new point. -/
theorem snoc_eq_comp_castAdd {M : Type w} {k : ℕ} {t : Fin n ↪ M} {s : Fin (n + 1 + k) ↪ M}
    (hs : (initSeg n k).trans s = t) (hm : s (newPos n k) ∉ Set.range t) :
    ⇑(snoc t (s (newPos n k)) hm) = ⇑s ∘ Fin.castAdd k := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [newPos]
  | cast j =>
    rw [Function.comp_apply, snoc_apply_castSucc, ← hs]
    rfl

/-- The new point of an extension of `t` is fresh. -/
theorem newPos_not_mem_range {M : Type w} {k : ℕ} {t : Fin n ↪ M} {s : Fin (n + 1 + k) ↪ M}
    (hs : (initSeg n k).trans s = t) : s (newPos n k) ∉ Set.range t := by
  rintro ⟨i, hi⟩
  rw [← hs] at hi
  exact newPos_ne_initSeg n k i (s.injective hi).symm

end VaughtConjecture.Knight
