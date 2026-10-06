/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model
public import VaughtConjecture.TypeTower.Slot

/-! # No countable model of `S^{ω₁}` (Knight, Lemma 11.1.1)

The Knight instance of the cardinal slot bound `TypeTower/Slot.lean` (#44; experiment A1,
`docs/DESIGN.md`).  Knight's Lemma 11.1.1 says that `S^{ω₁}` has no countable model; the
argument uses only covering (Def. 3.2.1(3)), the Uniformity clause (Def. 3.2.1(4)(b)) and counting,
so it is proved here
in the generalised form **every model of `S^{ω₁}` has carrier of size at least `ℵ₁`**
(`IsModel.aleph_one_le_mk_carrier`), with the countable case as the corollary
(`IsModel.not_countable_carrier`).

* The **bands** are the Uniformity intervals `[γ, γ + ω)` for non-successor `γ` (`band γ`);
  for distinct non-successors they are pairwise disjoint (`band_pairwise_disjoint`: a
  non-successor above `γ` is at least `γ + ω`, since both are multiples of `ω`).
* The **index set** is the non-successors below `ω₁` (`UniformityIndex`), of size at least `ℵ₁`
  (`aleph_one_le_mk_uniformityIndex`: the block levels `blockLevel ξ = ω + ω·ξ`, `ξ < ω₁`, inject
  into it).
* The **slots** over a realization are the pairs (labelled injective tuple `t`, cell of the type
  realized at `t`) — `SlotData (R.eval t)`, countable per tuple — with value the realized label
  of that cell (`slotLabel`).
* **Uniformity supplies the witnesses**: the empty tuple is an initial segment of some labelled
  tuple `s` (covering), and for each non-successor `γ < ω₁` clause (4)(b) realizes over `s` a
  type with a cell labelled in `[γ, γ + ω)` (`IsModel.exists_slot_mem_band`).

The generic theorem `lift_mk_le_max_aleph0_carrier_of_forall_exists_slot` then gives
`ℵ₁ ≤ #UniformityIndex ≤ max ℵ₀ #M`, i.e. `ℵ₁ ≤ #M`.  No Knight-specific cardinal argument
and no separate infinitude argument is needed; the carrier universe is arbitrary.  (Knight-VC:
`PaperExactWeakMarkerNonexistence.no_countable_core_uniformity_model_at_aleph1_ord`, stated
for countable carriers only.) -/

@[expose] public section

open Cardinal Ordinal

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe u

/-! ### The stage `ω₁` -/

/-- The stage `ω₁ = (aleph 1).ord`, the top of Knight's construction, as a limit stage. -/
noncomputable def omegaOneStage : LimitStage :=
  ⟨(aleph 1).ord, Cardinal.isSuccLimit_ord (aleph0_le_aleph 1)⟩

@[simp] theorem omegaOneStage_val : omegaOneStage.1 = (aleph 1).ord := rfl

/-! ### Uniformity bands -/

/-- The **Uniformity band** of a non-successor `γ`: the labels in `[γ, γ + ω)`
(the target interval of Def. 3.2.1(4)(b), `UniformityFamily γ`). -/
def band (γ : Ordinal.{0}) : Set ExtOrd :=
  {x | ofOrd γ ≤ x ∧ x < ofOrd (γ + ω)}

/-- A non-successor strictly above a non-successor `γ` is at least `γ + ω` (both are multiples
of `ω`). -/
theorem add_omega0_le_of_isNonSuccessor {γ γ' : Ordinal.{0}} (hγ : IsNonSuccessor γ)
    (hγ' : IsNonSuccessor γ') (h : γ < γ') : γ + ω ≤ γ' := by
  obtain ⟨a, rfl⟩ :=
    isSuccPrelimit_iff_omega0_dvd.mp (isNonSuccessor_iff_isSuccPrelimit.mp hγ)
  obtain ⟨b, rfl⟩ :=
    isSuccPrelimit_iff_omega0_dvd.mp (isNonSuccessor_iff_isSuccPrelimit.mp hγ')
  rw [← mul_succ]
  exact mul_le_mul_right (Order.succ_le_of_lt ((mul_lt_mul_iff_right₀ omega0_pos).mp h)) ω

/-- The bands of two non-successors `γ < γ'` are disjoint. -/
theorem band_disjoint_of_lt {γ γ' : Ordinal.{0}} (hγ : IsNonSuccessor γ)
    (hγ' : IsNonSuccessor γ') (h : γ < γ') : Disjoint (band γ) (band γ') := by
  rw [Set.disjoint_left]
  rintro x ⟨-, hx⟩ ⟨hx', -⟩
  exact absurd (hx'.trans_lt hx)
    (not_lt.mpr (ofOrd_le_ofOrd.mpr (add_omega0_le_of_isNonSuccessor hγ hγ' h)))

/-- The Uniformity bands of distinct non-successors are pairwise disjoint. -/
theorem band_pairwise_disjoint :
    Pairwise fun γ γ' : {γ : Ordinal.{0} // IsNonSuccessor γ} =>
      Disjoint (band γ.1) (band γ'.1) := by
  intro γ γ' hne
  rcases lt_or_gt_of_ne (Subtype.coe_ne_coe.mpr hne) with h | h
  · exact band_disjoint_of_lt γ.2 γ'.2 h
  · exact (band_disjoint_of_lt γ'.2 γ.2 h).symm

/-! ### The index set: non-successors below `ω₁` -/

/-- The **Uniformity index set** at `ω₁`: the non-successor ordinals `γ < ω₁` (the parameters
of Def. 3.2.1(4)(b) at stage `ω₁`). -/
abbrev UniformityIndex : Type 1 := {γ : Ordinal.{0} // IsNonSuccessor γ ∧ γ < (aleph 1).ord}

theorem UniformityIndex.band_pairwise_disjoint :
    Pairwise fun γ γ' : UniformityIndex => Disjoint (band γ.1) (band γ'.1) :=
  fun γ γ' hne =>
    Knight.band_pairwise_disjoint (i := ⟨γ.1, γ.2.1⟩) (j := ⟨γ'.1, γ'.2.1⟩)
      fun h => hne (Subtype.ext (Subtype.mk.inj h))

/-- The block levels below `ω₁` stay below `ω₁` (`card (ω + ω·ξ) = ℵ₀ + ℵ₀·card ξ < ℵ₁`). -/
theorem blockLevel_lt_ord_aleph_one {ξ : Ordinal.{0}} (hξ : ξ < (aleph 1).ord) :
    blockLevel ξ < (aleph 1).ord := by
  rw [lt_ord] at hξ ⊢
  unfold blockLevel
  rw [card_add, card_mul, card_omega0]
  exact add_lt_of_lt (aleph0_le_aleph 1) aleph0_lt_aleph_one
    (mul_lt_of_lt (aleph0_le_aleph 1) aleph0_lt_aleph_one hξ)

/-- There are at least `ℵ₁` non-successors below `ω₁`: `ξ ↦ blockLevel ξ` injects `ω₁` into
them. -/
theorem aleph_one_le_mk_uniformityIndex : aleph 1 ≤ #UniformityIndex := by
  let e : Set.Iio (aleph 1).ord ↪ UniformityIndex :=
    ⟨fun ξ => ⟨blockLevel ξ.1, Or.inr (isSuccLimit_blockLevel _), blockLevel_lt_ord_aleph_one ξ.2⟩,
      fun ξ η h => Subtype.ext (blockLevel_strictMono.injective (congrArg Subtype.val h))⟩
  have h := mk_le_of_injective e.injective
  rwa [Cardinal.mk_Iio_ordinal, card_ord, lift_aleph, Ordinal.lift_one] at h

/-! ### Slots: a labelled tuple together with a cell of its realized type -/

section Slot

variable {α : Ordinal.{0}} {n : ℕ}

/-- The per-tuple slot data of a (possibly undefined) realized type: a cell of the type when
it is defined, nothing otherwise. -/
def SlotData : Option (S α n) → Type
  | none => PEmpty
  | some q => Cell q.scheme.scheme

/-- The value of a slot datum: the realized label of the cell. -/
def slotValue : ∀ o : Option (S α n), SlotData o → ExtOrd
  | none, c => c.elim
  | some q, c => q.label c

/-- Each tuple carries countably many slot data. -/
theorem mk_slotData_le (o : Option (S α n)) : #(SlotData o) ≤ ℵ₀ := by
  cases o with
  | none => exact (lt_aleph0_of_finite PEmpty).le
  | some q => exact (lt_aleph0_of_finite (Cell q.scheme.scheme)).le

/-- A cell of a realized type is a slot datum of the tuple, with the label as value. -/
theorem exists_slotData_of_eq_some {o : Option (S α n)} {q : S α n} (h : o = some q)
    (c : Cell q.scheme.scheme) : ∃ d : SlotData o, slotValue o d = q.label c := by
  subst h
  exact ⟨c, rfl⟩

end Slot

variable {M : Type u}

/-- The **slots** of a Knight realization: an arity, an injective tuple, and a cell of the type
realized there. -/
abbrev Slot {α : LimitStage} (R : KnightRealization α M) : Type u :=
  Σ n : ℕ, Σ t : Fin n ↪ M, SlotData (R.eval t)

/-- The value of a slot: the realized label of its cell. -/
def slotLabel {α : LimitStage} {R : KnightRealization α M} (s : Slot R) : ExtOrd :=
  slotValue (R.eval s.2.1) s.2.2

namespace KnightRealization

variable {α : LimitStage} {R : KnightRealization α M}

/-- **Uniformity supplies a slot in every band**: in a model, for every non-successor `γ < α`
some slot has its value in `[γ, γ + ω)` (covering labels some tuple `s` over the empty tuple;
clause (4)(b) over `s`). -/
theorem IsModel.exists_slot_mem_band (hM : R.IsModel) (γ : Ordinal.{0})
    (hγ : IsNonSuccessor γ) (hγα : γ < α.1) : ∃ s : Slot R, slotLabel s ∈ band γ := by
  obtain ⟨k, s, -, hs⟩ := hM.covering (Function.Embedding.ofIsEmpty : Fin 0 ↪ M)
  obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨y, hy, q, ⟨Sig, h₁, h₂⟩, -, heq⟩ := hM.uniformity s p₀ hp₀ γ hγ hγα
  obtain ⟨d, hd⟩ := exists_slotData_of_eq_some heq Sig
  refine ⟨⟨_, snoc s y hy, d⟩, ?_⟩
  change ofOrd γ ≤ slotValue _ d ∧ slotValue _ d < ofOrd (γ + ω)
  rw [hd]
  exact ⟨h₁, h₂⟩

/-- **Lemma 11.1.1, generalised.**  Every model of `S^{ω₁}` has carrier of size at least
`ℵ₁`: the `ℵ₁` pairwise-disjoint Uniformity bands below `ω₁` are each witnessed by a slot,
and there are only `max ℵ₀ #M` slots (`lift_mk_le_max_aleph0_carrier_of_forall_exists_slot`). -/
theorem IsModel.aleph_one_le_mk_carrier {R : KnightRealization omegaOneStage M}
    (hM : R.IsModel) : aleph 1 ≤ #M := by
  have h := lift_mk_le_max_aleph0_carrier_of_forall_exists_slot M
    (fun n t => SlotData (R.eval t)) (fun _ t => mk_slotData_le _)
    UniformityIndex.band_pairwise_disjoint (slotLabel (R := R))
    (fun j => hM.exists_slot_mem_band j.1 j.2.1 j.2.2)
  have h₁ := (lift_le.mpr aleph_one_le_mk_uniformityIndex).trans h
  rw [lift_aleph, Ordinal.lift_one, lift_max, lift_aleph0] at h₁
  have h₂ : aleph 1 ≤ lift.{1} #M :=
    (le_max_iff.mp h₁).resolve_left (not_le.mpr aleph0_lt_aleph_one)
  have h₃ : lift.{1} (aleph 1 : Cardinal.{u}) ≤ lift.{1} #M := by
    rwa [lift_aleph, Ordinal.lift_one]
  exact lift_le.mp h₃

/-- **Lemma 11.1.1.**  `S^{ω₁}` has no countable model. -/
theorem IsModel.not_countable_carrier {R : KnightRealization omegaOneStage M}
    (hM : R.IsModel) : ¬ Countable M := fun h =>
  absurd (hM.aleph_one_le_mk_carrier.trans (mk_le_aleph0_iff.mpr h))
    (not_le.mpr aleph0_lt_aleph_one)

end KnightRealization

end VaughtConjecture.Knight
