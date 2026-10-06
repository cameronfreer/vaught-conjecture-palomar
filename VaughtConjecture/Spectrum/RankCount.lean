/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # The ranked-realization cardinal kernel

The whole cardinal content of Knight's spectrum calculation is the following
elementary statement about a rank.  Let `X` be a set (in the application: the
isomorphism classes of countable models of the sentence) and `ρ : X → Ordinal`
a rank with

1. **totality**: `ρ x < ω₁` for every `x`;
2. **countable fibres**: `{x | ρ x = δ}` is countable for every `δ < ω₁`;
3. **cofinal range**: `ρ` is unbounded in `ω₁`.

Then `#X = ℵ₁`.  The upper bound is `ℵ₁ · ℵ₀ = ℵ₁`; the lower bound is that a
set of size `< ℵ₁` has bounded image in `ω₁` (regularity of `ℵ₁`).

In the application `ρ` is the *first failed canonical block* of a linked
coherent expansion history.  The point of isolating this kernel is that the
continuum issue becomes transparent: the upper bound is carried entirely by
totality plus countable fibres.  (Knight-VC analogue:
`PaperFaithfulScopedCountableRankUpper.lean`.) -/

@[expose] public section

namespace VaughtConjecture.Spectrum

open Cardinal Ordinal

universe u v w

variable {X : Type u}

/-- A map with countable fibres into `I` gives `#X ≤ #I * ℵ₀` (independent universes). -/
theorem lift_mk_le_lift_mk_mul_aleph0_of_countable_fibres {I : Type v} (f : X → I)
    (hf : ∀ i, Countable {x // f x = i}) : lift.{v} #X ≤ lift.{u} #I * ℵ₀ := by
  have h1 : lift.{v} #X = #(Σ i, {x // f x = i}) := by
    have := lift_mk_eq'.{u, max u v}.mpr ⟨(Equiv.sigmaFiberEquiv f).symm⟩
    rw [Cardinal.lift_umax] at this
    rw [this]
    exact Cardinal.lift_id' _
  calc lift.{v} #X = #(Σ i, {x // f x = i}) := h1
    _ = sum fun i => #{x // f x = i} := mk_sigma _
    _ ≤ lift.{u} #I * ⨆ i, lift.{v} #{x // f x = i} := sum_le_lift_mk_mul_iSup_lift _
    _ ≤ lift.{u} #I * ℵ₀ := mul_le_mul' le_rfl
        (ciSup_le' fun i => lift_le_aleph0.mpr (mk_le_aleph0_iff.mpr (hf i)))

/-- A map with countable fibres into `I` gives `#X ≤ #I * ℵ₀` (same universe). -/
theorem mk_le_mk_mul_aleph0_of_countable_fibres {I : Type u} (f : X → I)
    (hf : ∀ i, Countable {x // f x = i}) : #X ≤ #I * ℵ₀ := by
  simpa using lift_mk_le_lift_mk_mul_aleph0_of_countable_fibres f hf

/-- A rank on `X` with values below `ω₁` and countable fibres below `ω₁` gives `#X ≤ ℵ₁`.
The rank may take values in any universe. -/
theorem mk_le_aleph_one_of_countable_fibres (ρ : X → Ordinal.{w})
    (hlt : ∀ x, ρ x < (aleph 1).ord)
    (hfib : ∀ δ < (aleph 1).ord, Countable {x // ρ x = δ}) :
    #X ≤ aleph 1 := by
  -- transport the rank into the type `(aleph 1).ord.ToType` of ordinals below `ω₁`
  let ρ' : X → (aleph 1).ord.ToType := fun x => Ordinal.ToType.mk ⟨ρ x, hlt x⟩
  have hfib' : ∀ i, Countable {x // ρ' x = i} := by
    intro i
    let δ : Ordinal.{w} := (Ordinal.ToType.mk.symm i).1
    have hδ : δ < (aleph 1).ord := (Ordinal.ToType.mk.symm i).2
    have key : ∀ x : {x // ρ' x = i}, ρ x.1 = δ := by
      rintro ⟨x, hx⟩
      have h1 : Ordinal.ToType.mk.symm (ρ' x) = Ordinal.ToType.mk.symm i := by rw [hx]
      simpa [ρ', δ] using congrArg Subtype.val h1
    have := hfib δ hδ
    have hinj : Function.Injective (fun x : {x // ρ' x = i} => (⟨x.1, key x⟩ : {x // ρ x = δ})) :=
      fun a b h => Subtype.ext (Subtype.mk.inj h)
    exact hinj.countable
  have h := lift_mk_le_lift_mk_mul_aleph0_of_countable_fibres ρ' hfib'
  rw [mk_toType, card_ord, lift_aleph, Ordinal.lift_one,
    mul_eq_left (aleph0_le_aleph 1) (aleph0_le_aleph 1) aleph0_ne_zero] at h
  have h' : lift.{w} #X ≤ lift.{w} (aleph 1 : Cardinal.{u}) := by
    rwa [lift_aleph, Ordinal.lift_one]
  exact lift_le.mp h'

/-- A rank on `X` with values below `ω₁` and unbounded range gives `ℵ₁ ≤ #X`. -/
theorem aleph_one_le_mk_of_cofinal (ρ : X → Ordinal.{w})
    (hlt : ∀ x, ρ x < (aleph 1).ord)
    (hcof : ∀ δ < (aleph 1).ord, ∃ x, δ < ρ x) :
    aleph 1 ≤ #X := by
  refine le_of_not_gt fun h => ?_
  -- `X` is countable and nonempty, so enumerate the ranks by `ℕ`
  have hcount : Countable X := mk_le_aleph0_iff.mp (lt_aleph_one_iff.mp h)
  have hpos : (0 : Ordinal) < (aleph 1).ord :=
    pos_iff_ne_zero.mpr fun h0 => (aleph_pos 1).ne' (ord_eq_zero.mp h0)
  have hne : Nonempty X := let ⟨x, _⟩ := hcof 0 hpos; ⟨x⟩
  obtain ⟨e, he⟩ := exists_surjective_nat X
  have hsup : (⨆ n, ρ (e n)) < (aleph 1).ord :=
    Ordinal.lift_iSup_lt_of_lt_cof
      (by rw [Ordinal.lift_id', isRegular_aleph_one.cof_ord, mk_nat, lift_aleph0]
          exact aleph0_lt_aleph_one)
      fun n => hlt (e n)
  obtain ⟨x, hx⟩ := hcof _ hsup
  obtain ⟨n, rfl⟩ := he x
  exact absurd (Ordinal.le_iSup (fun n => ρ (e n)) n) (not_le.mpr hx)

/-- **Ranked-realization kernel.**  Totality, countable fibres and cofinal range of a
rank into `ω₁` give exactly `ℵ₁` points. -/
theorem mk_eq_aleph_one_of_rank (ρ : X → Ordinal.{w})
    (hlt : ∀ x, ρ x < (aleph 1).ord)
    (hfib : ∀ δ < (aleph 1).ord, Countable {x // ρ x = δ})
    (hcof : ∀ δ < (aleph 1).ord, ∃ x, δ < ρ x) :
    #X = aleph 1 :=
  le_antisymm (mk_le_aleph_one_of_countable_fibres ρ hlt hfib)
    (aleph_one_le_mk_of_cofinal ρ hlt hcof)

/-! ## The hybrid exact-cardinality kernel

On the exact-spectrum path the upper bound does not come from countable fibres
of the rank at all: it comes from an injective *receipt code* into a type of
cardinality `≤ ℵ₁` (the thin receipt-code injection, #57), while the lower
bound is the intrinsic-rank cofinality unchanged (#58); the two combine in #61.
`mk_eq_aleph_one_of_code_and_cofinal` states the combination; no
countable-fibre hypothesis appears.  The fibre-based `mk_eq_aleph_one_of_rank`
above remains for thinness and other consumers. -/

/-- An injection into a type of cardinality `≤ ℵ₁` gives `#X ≤ ℵ₁`
(independent universes). -/
theorem mk_le_aleph_one_of_injective {C : Type v} (code : X → C)
    (hinj : Function.Injective code) (hC : #C ≤ aleph 1) : #X ≤ aleph 1 := by
  have h : lift.{v} #X ≤ lift.{v} (aleph 1 : Cardinal.{u}) := by
    calc lift.{v} #X ≤ lift.{u} #C := lift_mk_le'.mpr ⟨⟨code, hinj⟩⟩
      _ ≤ lift.{u} (aleph 1) := lift_le.mpr hC
      _ = aleph 1 := by rw [lift_aleph, Ordinal.lift_one]
      _ = lift.{v} (aleph 1) := by rw [lift_aleph, Ordinal.lift_one]
  exact lift_le.mp h

/-- **Hybrid exact-cardinality kernel** (exact-spectrum path, #61): an injective
code into a type of cardinality `≤ ℵ₁` (upper bound: thin receipt-code
injection, #57) together with a rank below `ω₁` of cofinal range (lower bound:
intrinsic-rank cofinality, #58) gives exactly `ℵ₁` points.  No countable-fibre
hypothesis is needed. -/
theorem mk_eq_aleph_one_of_code_and_cofinal {C : Type v} (code : X → C)
    (hinj : Function.Injective code) (hC : #C ≤ aleph 1)
    (ρ : X → Ordinal.{w}) (hlt : ∀ x, ρ x < (aleph 1).ord)
    (hcof : ∀ δ < (aleph 1).ord, ∃ x, δ < ρ x) :
    #X = aleph 1 :=
  le_antisymm (mk_le_aleph_one_of_injective code hinj hC)
    (aleph_one_le_mk_of_cofinal ρ hlt hcof)

/-- The canonical receipt-code target: pairs of a countable ordinal and a
natural number.  Its cardinality is exactly `ℵ₁` (in `Cardinal.{v + 1}`; the
subtype of `Ordinal.{v}` lives in `Type (v + 1)` and the `lift.{v + 1}` from
`mk_Iio_ordinal` is absorbed by `lift_aleph`). -/
theorem mk_subtype_lt_ord_aleph_one_prod_nat :
    #({δ : Ordinal.{v} // δ < (aleph 1).ord} × ℕ) = aleph 1 := by
  have h1 : #{δ : Ordinal.{v} // δ < (aleph 1).ord} = aleph 1 := by
    have h : #{δ : Ordinal.{v} // δ < (aleph 1).ord} = #(Set.Iio (aleph 1).ord) := rfl
    rw [h, Cardinal.mk_Iio_ordinal, card_ord, lift_aleph, Ordinal.lift_one]
  rw [mk_prod, h1, mk_nat, lift_aleph, Ordinal.lift_one, lift_aleph0,
    mul_eq_left (aleph0_le_aleph 1) (aleph0_le_aleph 1) aleph0_ne_zero]

/-- Convenience instantiation of the hybrid kernel: the receipt code lands in
pairs of a countable ordinal and a natural number. -/
theorem mk_eq_aleph_one_of_pair_code_and_cofinal
    (code : X → {δ : Ordinal.{v} // δ < (aleph 1).ord} × ℕ)
    (hinj : Function.Injective code)
    (ρ : X → Ordinal.{w}) (hlt : ∀ x, ρ x < (aleph 1).ord)
    (hcof : ∀ δ < (aleph 1).ord, ∃ x, δ < ρ x) :
    #X = aleph 1 :=
  mk_eq_aleph_one_of_code_and_cofinal code hinj
    mk_subtype_lt_ord_aleph_one_prod_nat.le ρ hlt hcof

end VaughtConjecture.Spectrum
