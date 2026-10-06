/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthStableCalibration
public import VaughtConjecture.Knight.GrowthFiniteCapTemplate

/-! # Calibrated requests for a chosen next-block donor

The finite cutoff is chosen from the entire donor vector, not only its root.
Correctness gives separate exact-proper and high-value receipts; it does not
force donor tops to remain top.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthFiniteCapRequests
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor
noncomputable section

theorem block_le {α : LimitStage} {β : Ordinal.{0}} (hβ : β < α.nextBlock.1) :
    limitPart β ≤ α.1 := by
  rcases lt_or_ge β α.1 with h | h
  · exact (limitPart_le β).trans h.le
  · obtain ⟨k, rfl⟩ := exists_nat_of_lt_add_omega h hβ
    rw [limitPart_add_nat_of_limit (limitPart_eq_self_of_isNonSuccessor (Or.inr α.2))]

theorem blocks_limit {α : LimitStage} {n : ℕ} (q : S α.nextBlock.1 (n + 1))
    (μ : Ordinal.{0}) (hμ : μ ∈ blocks q) : limitPart μ = μ := by
  obtain ⟨r, hr, rfl⟩ := mem_blocks.mp hμ
  exact limitPart_eq_self_of_isNonSuccessor (donorRequests_ok q r hr).1

theorem blocks_le {α : LimitStage} {n : ℕ} (q : S α.nextBlock.1 (n + 1))
    (μ : Ordinal.{0}) (hμ : μ ∈ blocks q) : μ ≤ α.1 := by
  obtain ⟨r, hr, rfl⟩ := mem_blocks.mp hμ
  obtain ⟨d, β, hd, rfl⟩ := mem_donorRequests.mp hr
  exact block_le (ofOrd_lt_ofOrd.mp (hd ▸ (q.label_bound d).resolve_right
    (hd ▸ ofOrd_ne_top _)))

/-- One finite cutoff dominates every proper donor label and every represented
offset, with an independently requested floor. -/
theorem exists_cut {α : LimitStage} {n : ℕ} (q : S α.nextBlock.1 (n + 1)) (floor : ℕ) :
    ∃ L : ℕ, floor < L ∧ n + 1 < L ∧
      (∀ d β, q.label d = ofOrd β → finitePart β < L) ∧
      ∀ d, q.label d ≠ ⊤ → q.label d < ofOrd (α.1 + L) := by
  classical
  let L := max floor (max (n + 1)
    (Finset.univ.sup (fun d : Cell q.scheme.scheme => finitePart (ordOf (q.label d))))) + 1
  have hfp (d) (β) (hd : q.label d = ofOrd β) : finitePart β < L := by
    have h := Finset.le_sup (f := fun d : Cell q.scheme.scheme =>
      finitePart (ordOf (q.label d))) (Finset.mem_univ d)
    rw [hd, ordOf_ofOrd] at h
    dsimp [L]; omega
  refine ⟨L, by dsimp [L]; omega, by dsimp [L]; omega, hfp, ?_⟩
  intro d hnt
  rcases ExtOrd.cases (q.label d) with hb | ht | ⟨β, hd⟩
  · rw [hb]; exact bot_lt_ofOrd _
  · exact (hnt ht).elim
  · have hb := block_le (ofOrd_lt_ofOrd.mp (hd ▸ (q.label_bound d).resolve_right hnt))
    rw [hd]
    apply ofOrd_lt_ofOrd.mpr
    calc β = limitPart β + finitePart β := (limitPart_add_finitePart β).symm
      _ < limitPart β + (L : Ordinal.{0}) := add_lt_add_right (Nat.cast_lt.mpr (hfp d β hd)) _
      _ ≤ α.1 + (L : Ordinal.{0}) := add_le_add_left hb _

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}

def requests (c : Cell DA) (L : ℕ) (hL : L < DA.grade c)
    (a : DA.below (DA.cell c)) (ref : Ordinal.{0} → DA.below (DA.cell c))
    (P : Cell DQ → ExtOrd) : Requests DA DQ where
  C := c
  N := DA.grade c
  R := L
  R_lt_N := hL
  Z := {d | P d = ⊥}
  F := {d | P d ≠ ⊥ ∧ P d ≠ ⊤}
  T := {d | P d = ⊤}
  ρ d := ref (limitPart (ordOf (P d)))
  off d := finitePart (ordOf (P d))
  a := a

variable (c : Cell DA) (L : ℕ) (hL : L < DA.grade c)
  (a : DA.below (DA.cell c)) (ref : Ordinal.{0} → DA.below (DA.cell c))
  (P : Cell DQ → ExtOrd) (w : Cell DA → ExtOrd)
  {α : Ordinal.{0}} (hα : limitPart α = α) {i : ℕ} (hi : i < DA.grade c)
  (ha : w a.1 = ofOrd (α + i)) (hcut : ofOrd (α + L) < w c)
  (off : Ordinal.{0} → ℕ)
  (href : ∀ d β, P d = ofOrd β → off (limitPart β) < DA.grade c ∧
    w (ref (limitPart β)).1 = ofOrd (limitPart β + off (limitPart β)))
  (hproper : ∀ d, P d ≠ ⊤ → P d < ofOrd (α + L))

include href in
theorem tOf_eq {d : Cell DQ} (hd : P d ≠ ⊥ ∧ P d ≠ ⊤) :
    (requests c L hL a ref P).tOf ((requests c L hL a ref P).sec w) d =
      min (P d) (w c) := by
  rcases ExtOrd.cases (P d) with hb | ht | ⟨β, hβ⟩
  · exact (hd.1 hb).elim
  · exact (hd.2 ht).elim
  obtain ⟨ho, hr⟩ := href d β hβ
  change min (extVisibilityReplace (w (ref (limitPart (ordOf (P d)))).1)
    (DA.grade c) (finitePart (ordOf (P d)))) (w c) = _
  rw [hβ, ordOf_ofOrd, hr, extVisibilityReplace_of_finitePart_lt (by
    rw [finitePart_limitPart_add_nat]; exact ho), limitPart_limitPart_add_nat,
    limitPart_add_finitePart]

include hα hi ha hcut in
theorem dOf_eq :
    (requests c L hL a ref P).dOf ((requests c L hL a ref P).sec w) = ofOrd (α + L) := by
  change min (extVisibilityReplace (w a.1) (DA.grade c) L) (w c) = _
  rw [ha, extVisibilityReplace_of_finitePart_lt (by
    rw [finitePart_add_nat_of_limit hα]; exact hi), limitPart_add_nat_of_limit hα,
    min_eq_left hcut.le]

include href in
/-- The same compatible vector satisfies the activated receiving relation.
This is derived from reference readings, not assumed as admission. -/
theorem correct : (requests c L hL a ref P).Correct
    ((requests c L hL a ref P).sec w) P := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    change min (P d) (w c) = ⊥
    rw [hd]; exact min_eq_left bot_le
  · intro d hd
    exact (tOf_eq c L hL a ref P w off href hd).symm
  · intro d hd
    change min (extVisibilityReplace (w a.1) (DA.grade c) L) (w c) ≤ min (P d) (w c)
    rw [hd, min_top_left]
    exact min_le_right _ _

include href hproper hcut in
/-- Exact proper readback is separate from the high-request inequality. -/
theorem proper_readback {v : Cell DQ → ExtOrd}
    (h : (requests c L hL a ref P).Correct ((requests c L hL a ref P).sec w) v)
    {d : Cell DQ} (hd : P d ≠ ⊥ ∧ P d ≠ ⊤) : v d = P d := by
  have he := h.2.1 d hd
  rw [tOf_eq c L hL a ref P w off href hd] at he
  have hlt := (hproper d hd.2).trans hcut
  rw [min_eq_left hlt.le] at he
  exact eq_of_min_eq_of_lt' he hlt

include hα hi ha hcut in
/-- High requests need not be literal tops: their separate receipt is a value
at least the calibrated cutoff. -/
theorem high_readback {v : Cell DQ → ExtOrd}
    (h : (requests c L hL a ref P).Correct ((requests c L hL a ref P).sec w) v)
    {d : Cell DQ} (hd : P d = ⊤) : ofOrd (α + L) ≤ v d := by
  have he := h.2.2 d hd
  rw [dOf_eq c L hL a ref P w hα hi ha hcut] at he
  exact he.trans (min_le_left _ _)

end
end VaughtConjecture.Knight.GrowthFiniteCapRequests
