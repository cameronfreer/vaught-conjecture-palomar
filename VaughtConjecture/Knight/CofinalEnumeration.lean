/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Rank

/-! # Cofinal enumeration of countable limits

The `ℕ`-indexed cofinal-sequence machinery for countable limit ordinals — enumeration below
`ω₁`, running maxima, cofinality, and its descent to block levels.  Extracted from
`LimitRankSupply.lean` so that the rank spine (intrinsic termination, the canonical stop
witness, the canonical tower) can assemble countable limits without the receipt cone. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

/-! ### An `ℕ`-indexed cofinal sequence in a countable limit ordinal -/

/-- **Enumeration of a countable ordinal**: below `ω₁`, the ordinals `< γ` are the range
of an `ℕ`-indexed sequence (surjective enumeration of `Set.Iio γ`; countable choice
only). -/
theorem exists_nat_enum_lt {γ : Ordinal.{0}} (hγ₁ : γ < (Cardinal.aleph 1).ord)
    (h0 : 0 < γ) :
    ∃ g : ℕ → Ordinal.{0}, (∀ n, g n < γ) ∧ ∀ ξ, ξ < γ → ∃ n, g n = ξ := by
  have hcard : γ.card ≤ Cardinal.aleph0 :=
    Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_ord.mp hγ₁)
  have hmk : Cardinal.mk (Set.Iio γ) ≤ Cardinal.aleph0 := by
    rw [Cardinal.mk_Iio_ordinal]
    exact Cardinal.lift_le_aleph0.mpr hcard
  have : Countable (Set.Iio γ) := Cardinal.mk_le_aleph0_iff.mp hmk
  have : Nonempty (Set.Iio γ) := ⟨⟨0, h0⟩⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat (Set.Iio γ)
  refine ⟨fun n => (f n).1, fun n => (f n).2, fun ξ hξ => ?_⟩
  obtain ⟨n, hn⟩ := hf ⟨ξ, hξ⟩
  exact ⟨n, congrArg Subtype.val hn⟩

/-- The running-maxima cofinal sequence over an enumeration `g`, with DEFINITIONAL base
`β` (`cofSeq β g 0` reduces to `β`, so the recursion state at index `0` is the base
model with no stage transport — the `succLadder`/`omegaLadder` discipline of
`Knight/ReceiptSupply.lean`). -/
noncomputable def cofSeq (β : Ordinal.{0}) (g : ℕ → Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => β
  | n + 1 => max (cofSeq β g n) (g n)

theorem cofSeq_le_succ (β : Ordinal.{0}) (g : ℕ → Ordinal.{0}) (n : ℕ) :
    cofSeq β g n ≤ cofSeq β g (n + 1) :=
  le_max_left _ _

theorem cofSeq_monotone (β : Ordinal.{0}) (g : ℕ → Ordinal.{0}) :
    Monotone (cofSeq β g) :=
  monotone_nat_of_le_succ (cofSeq_le_succ β g)

theorem le_cofSeq (β : Ordinal.{0}) (g : ℕ → Ordinal.{0}) (n : ℕ) : β ≤ cofSeq β g n :=
  cofSeq_monotone β g (Nat.zero_le n)

theorem cofSeq_lt {β γ : Ordinal.{0}} (hβ : β < γ) {g : ℕ → Ordinal.{0}}
    (hg : ∀ n, g n < γ) (n : ℕ) : cofSeq β g n < γ := by
  induction n with
  | zero => exact hβ
  | succ n ih => exact max_lt ih (hg n)

/-- **Cofinality of the running maxima in a limit**: every `ξ < γ` is strictly below
some `cofSeq β g n` — the successor `ξ + 1` is again `< γ` (limit), hence enumerated,
hence dominated by the next running maximum. -/
theorem lt_cofSeq {β γ : Ordinal.{0}} (hlim : Order.IsSuccLimit γ)
    {g : ℕ → Ordinal.{0}} (hg : ∀ ξ, ξ < γ → ∃ n, g n = ξ) {ξ : Ordinal.{0}}
    (hξ : ξ < γ) : ∃ n, ξ < cofSeq β g n := by
  have hξ1 : ξ + 1 < γ := by
    have := hlim.succ_lt hξ
    rwa [Order.succ_eq_add_one] at this
  obtain ⟨n, hn⟩ := hg (ξ + 1) hξ1
  exact ⟨n + 1, lt_of_lt_of_le (lt_add_one ξ) (hn ▸ le_max_right (cofSeq β g n) (g n))⟩

/-- **Cofinality descends to the block levels**: the levels `blockLevel ξ = ω + ω·ξ` of
a sequence cofinal in the limit `γ` are cofinal in `blockLevel γ` (the computation of
`exists_add_mul_natCast_lt`, at an arbitrary cofinal family). -/
theorem exists_lt_blockStage_of_cofinal {γ : Ordinal.{0}} (hlim : Order.IsSuccLimit γ)
    {c : ℕ → Ordinal.{0}} (hcof : ∀ ξ, ξ < γ → ∃ n, ξ < c n) {ξ' : Ordinal.{0}}
    (hξ' : ξ' < (blockStage γ).1) : ∃ n, ξ' < (blockStage (c n)).1 := by
  by_cases h0 : ξ' < Ordinal.omega0
  · exact ⟨0, h0.trans_le (le_add_right le_rfl)⟩
  · rw [not_lt] at h0
    have hsub : Ordinal.omega0 + (ξ' - Ordinal.omega0) = ξ' :=
      Ordinal.add_sub_cancel_of_le h0
    have hlt : ξ' - Ordinal.omega0 < Ordinal.omega0 * γ := by
      rw [← hsub] at hξ'
      exact (add_lt_add_iff_left _).mp hξ'
    obtain ⟨x, hx, hltx⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit hlim).mp hlt
    obtain ⟨n, hn⟩ := hcof x hx
    refine ⟨n, ?_⟩
    rw [← hsub]
    exact (add_lt_add_iff_left _).mpr (hltx.trans_le (mul_le_mul_right hn.le Ordinal.omega0))

end VaughtConjecture.Knight
