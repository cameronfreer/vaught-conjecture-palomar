/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ControllerOrderCover
public import VaughtConjecture.Knight.WitnessAlgebra

/-! # A prefix-organized family of six controller rows

Three independent grade-one probes admit six strict orders. A controller is an
order, and its cross-entry at another controller is their first divergence.
All rows are fixed in advance. One sorted order supplies every controller label
coherently, including ties; choosing their largest caps independently fails.

This module verifies the joint row layer with actual faithful transformations.
It does not provide a support plan, arbitrary inherited rows, or bountifulness.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

namespace ControllerPrefixFamily

/-- The six permutations, in lexicographic order. -/
def order : Fin 6 → Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

/-- The inverse position map for each order. -/
def position : Fin 6 → Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![2, 0, 1], ![1, 2, 0], ![2, 1, 0]]

/-- Zero-based first divergence; the last level is used on the diagonal. -/
def overlap (p q : Fin 6) : Fin 3 :=
  if p = q then 2 else if order p 0 = order q 0 then 1 else 0

def probe (i : Fin 3) : Fin 9 := Fin.castAdd 6 i
def controller (p : Fin 6) : Fin 9 := ⟨p.val + 3, by omega⟩

/-- Proper sources use their position; cross-controller sources use the prefix. -/
def rank (p : Fin 6) (d : Fin 9) : Fin 3 :=
  if h : d.val < 3 then position p ⟨d.val, h⟩ else overlap p ⟨d.val - 3, by omega⟩

theorem order_position (p : Fin 6) (i : Fin 3) : order p (position p i) = i := by decide +revert
theorem rank_probe (p : Fin 6) (i : Fin 3) : rank p (probe i) = position p i := by decide +revert
theorem rank_diagonal (p : Fin 6) : rank p (controller p) = 2 := by decide +revert
theorem rank_at_order (p : Fin 6) (i : Fin 3) : rank p (probe (order p i)) = i := by
  decide +revert
theorem inventory_exhaustive (d : Fin 9) : (∃ i, d = probe i) ∨ ∃ p, d = controller p := by
  decide +revert

/-- The finite prefix identity supplies every capped source readback. -/
theorem rank_capped_readback (p q : Fin 6) (d : Fin 9) :
    min (rank q d) (rank q (controller p)) =
      min (rank q (probe (order p (rank p d)))) (rank q (controller p)) := by decide +revert

/-- All three capped output levels are ordered, even when the uncapped orders differ. -/
theorem rank_capped_mono (p q : Fin 6) :
    Monotone (fun i => min (rank q (probe (order p i))) (rank q (controller p))) := by
  decide +revert

open BranchAvailability (source source_visible source_coded)

/-- Three separated source blocks, not three offsets inside one block. -/
noncomputable def row (p : Fin 6) (d : Fin 9) : ExtOrd := source ((rank p d).val + 1)

theorem row_visible (p : Fin 6) (d : Fin 9) : SelfVis 1 (row p d) := source_visible _
theorem row_coded (p : Fin 6) (d : Fin 9) : IsCodedLabel 1 (row p d) := source_coded _ _

/-- A monotone list of three visible levels, read through one chosen order. -/
noncomputable def label (q : Fin 6) (v : Fin 3 → ExtOrd) (d : Fin 9) : ExtOrd := v (rank q d)

noncomputable def threeStep (v : Fin 3 → ExtOrd) (a : ExtOrd) : ExtOrd :=
  max (stepShifter 2 (v 0) (v 1) a) (stepShifter 3 (v 0) (v 2) a)

theorem threeStep_witness {v : Fin 3 → ExtOrd} (hm : Monotone v)
    (hv : ∀ i, SelfVis 1 (v i)) : Witness (gTop 1) (threeStep v) :=
  (Witness.stepLimit 1 2 (hm (by decide : (0 : Fin 3) ≤ 1)) (hv 0) (hv 1)).max
    (Witness.stepLimit 1 3 (hm (by decide : (0 : Fin 3) ≤ 2)) (hv 0) (hv 2))

private theorem source_lt_cut {i n : ℕ} (h : i < n) :
    source i < ofOrd (Ordinal.omega0 * (n : Ordinal)) := by
  change ofOrd (Ordinal.omega0 * (i : Ordinal) + 1) < _
  have hi : (i : Ordinal.{0}) < (n : Ordinal.{0}) := by exact_mod_cast h
  apply ofOrd_lt_ofOrd.mpr
  simpa only [Nat.cast_one] using code_add_lt_mul hi 1

private theorem source_ge_cut {i n : ℕ} (h : n ≤ i) :
    ofOrd (Ordinal.omega0 * (n : Ordinal)) ≤ source i := by
  apply ofOrd_le_ofOrd.mpr
  exact ((Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.monotone
    (by exact_mod_cast h)).trans (le_self_add)

theorem threeStep_source {v : Fin 3 → ExtOrd} (hm : Monotone v) (i : Fin 3) :
    threeStep v (source (i.val + 1)) = v i := by
  fin_cases i
  · change threeStep v (source 1) = v 0
    rw [threeStep,
      stepShifter_of_lt (show source 1 ≠ ⊥ from ofOrd_ne_bot _) (source_lt_cut (by decide : 1 < 2)),
      stepShifter_of_lt (show source 1 ≠ ⊥ from ofOrd_ne_bot _) (source_lt_cut (by decide : 1 < 3)),
      max_self]
  · change threeStep v (source 2) = v 1
    rw [threeStep, stepShifter_of_ge (source_ge_cut (by decide : 2 ≤ 2)),
      stepShifter_of_lt (show source 2 ≠ ⊥ from ofOrd_ne_bot _) (source_lt_cut (by decide : 2 < 3)),
      max_eq_left (hm (by decide : (0 : Fin 3) ≤ 1))]
  · change threeStep v (source 3) = v 2
    rw [threeStep, stepShifter_of_ge (source_ge_cut (by decide : 2 ≤ 3)),
      stepShifter_of_ge (source_ge_cut (by decide : 3 ≤ 3)),
      max_eq_right (hm (by decide : (1 : Fin 3) ≤ 2))]

/-- Every controller has a full faithful witness on all nine entries. -/
theorem label_locality (p q : Fin 6) {v : Fin 3 → ExtOrd} (hm : Monotone v)
    (hv : ∀ i, SelfVis 1 (v i)) :
    TransformsTo (fun _ : Fin 9 => 1) (row p)
      (fun d => min (label q v d) (label q v (controller p))) := by
  let w : Fin 3 → ExtOrd := fun i => v (min (rank q (probe (order p i))) (rank q (controller p)))
  have hw : Monotone w := hm.comp (rank_capped_mono p q)
  apply (threeStep_witness hw (fun i => hv _)).transformsTo
  intro d
  rw [show row p d = source ((rank p d).val + 1) from rfl, threeStep_source hw]
  simp only [gTop, ite_eq_left (le_refl 1), min_eq_left le_top]
  change min (v (rank q d)) (v (rank q (controller p))) =
    v (min (rank q (probe (order p (rank p d)))) (rank q (controller p)))
  rw [← hm.map_min, rank_capped_readback]

/-- The chosen controller dominates every entry, not just the proper probes. -/
theorem label_dominated (q : Fin 6) {v : Fin 3 → ExtOrd} (hm : Monotone v) (d : Fin 9) :
    label q v d ≤ label q v (controller q) := by
  unfold label
  rw [rank_diagonal]
  exact hm (by omega)

/-- The joint row-layer predicate: all localities, with alternatives only for
probe availability. This is not a complete cell-scheme interface. -/
def Joint (p : Fin 9 → ExtOrd) : Prop :=
  (∀ d, SelfVis 1 (p d)) ∧
  (∀ c, TransformsTo (fun _ : Fin 9 => 1) (row c)
    (fun d => min (p d) (p (controller c)))) ∧
  ∀ i, ∃ c, p (probe i) ≤ p (controller c)

theorem label_joint (q : Fin 6) {v : Fin 3 → ExtOrd} (hm : Monotone v)
    (hv : ∀ i, SelfVis 1 (v i)) : Joint (label q v) :=
  ⟨fun _ => hv _, fun p => label_locality p q hm hv,
    fun i => ⟨q, label_dominated q hm (probe i)⟩⟩

/-- Every triple has a weakly sorted order; ties may be resolved in more than one way. -/
theorem exists_sorted_order (a : Fin 3 → ExtOrd) :
    ∃ q : Fin 6, Monotone (fun i => a (order q i)) := by
  have hs : ∃ q : Fin 6, a (order q 0) ≤ a (order q 1) ∧ a (order q 1) ≤ a (order q 2) := by
    rcases le_total (a 0) (a 1) with h01 | h10
    · rcases le_total (a 1) (a 2) with h12 | h21
      · exact ⟨0, h01, h12⟩
      · rcases le_total (a 0) (a 2) with h02 | h20
        · exact ⟨1, h02, h21⟩
        · exact ⟨4, h20, h01⟩
    · rcases le_total (a 0) (a 2) with h02 | h20
      · exact ⟨2, h10, h02⟩
      · rcases le_total (a 1) (a 2) with h12 | h21
        · exact ⟨3, h12, h20⟩
        · exact ⟨5, h21, h10⟩
  obtain ⟨q, h01, h12⟩ := hs
  have h02 := h01.trans h12
  refine ⟨q, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Three arbitrary visible proper values have a simultaneous section through
the entire fixed family, including bottom and literal top in any coordinate. -/
theorem exists_joint_section (a : Fin 3 → ExtOrd) (ha : ∀ i, SelfVis 1 (a i)) :
    ∃ p, Joint p ∧ ∀ i, p (probe i) = a i := by
  obtain ⟨q, hm⟩ := exists_sorted_order a
  refine ⟨label q (fun i => a (order q i)), label_joint q hm (fun i => ha _), ?_⟩
  intro i
  change a (order q (rank q (probe i))) = a i
  rw [rank_probe, order_position]

private theorem source_mono : Monotone (fun i : Fin 3 => source (i.val + 1)) := by
  intro i j hij
  apply ofOrd_le_ofOrd.mpr
  apply add_le_add_left
  exact (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.monotone
    (by exact_mod_cast (show i.val + 1 ≤ j.val + 1 by omega))

/-- Every source row itself satisfies every other row's locality and probe
availability. This is mutual consistency of the nine-entry row layer. -/
theorem rows_joint (q : Fin 6) : Joint (row q) :=
  label_joint q source_mono (fun _ => source_visible _)

/-- A controller's diagonal shares its source with the last proper probe in its
order. Thus its label cannot exceed all the proper labels. -/
theorem Joint.controller_le_probe {p : Fin 9 → ExtOrd} (hp : Joint p) (c : Fin 6) :
    p (controller c) ≤ p (probe (order c 2)) := by
  obtain ⟨g, σ, _, _, _, _, _, he⟩ := hp.2.1 c
  have hrow : row c (controller c) = row c (probe (order c 2)) := by
    unfold row; rw [rank_diagonal, rank_at_order]
  have hc := he (controller c)
  have hd := he (probe (order c 2))
  dsimp only at hc hd
  rw [min_self, hrow, ← hd] at hc
  exact hc.le.trans (min_le_left _ _)

/-- Probe availability supplies a controller dominating the entire nine-entry
labelling, because every other controller is below its own last proper probe. -/
theorem Joint.exists_dominator {p : Fin 9 → ExtOrd} (hp : Joint p) :
    ∃ q, ∀ d, p d ≤ p (controller q) := by
  obtain ⟨i, hi⟩ := Finite.exists_max (fun i : Fin 3 => p (probe i))
  obtain ⟨q, hq⟩ := hp.2.2 i
  refine ⟨q, fun d => ?_⟩
  rcases inventory_exhaustive d with ⟨j, rfl⟩ | ⟨c, rfl⟩
  · exact (hi j).trans hq
  · exact (hp.controller_le_probe c).trans ((hi _).trans hq)

/-- A dominating controller determines every entry through one ordered list.
This is necessity from actual faithful localities, not assumed scalar laws. -/
theorem Joint.exists_shape {p : Fin 9 → ExtOrd} (hp : Joint p) :
    ∃ q v, Monotone v ∧ (∀ i, SelfVis 1 (v i)) ∧ p = label q v := by
  obtain ⟨q, hq⟩ := hp.exists_dominator
  obtain ⟨τ, _, hm, hr, _, _⟩ := exists_exact_capped_shifter
    (grade := fun _ : Fin 9 => 1) (c := controller q)
    (fun _ => le_refl 1) (hp.1 _) (hp.2.1 q)
  have hr' : ∀ d, τ (row q d) = p d := by
    intro d
    rw [hr, min_eq_left (hq d)]
  let v : Fin 3 → ExtOrd := fun i => p (probe (order q i))
  have hv : ∀ i, v i = τ (source (i.val + 1)) := by
    intro i
    dsimp only [v]
    rw [← hr' (probe (order q i))]
    unfold row
    rw [rank_at_order]
  refine ⟨q, v, ?_, fun i => hp.1 _, ?_⟩
  · intro i j hij
    rw [hv i, hv j]
    exact hm (source_mono hij)
  · funext d
    change p d = v (rank q d)
    rw [hv, ← hr' d]
    rfl

/-- The row layer is exactly the union of six ordered branches. No uniqueness
of the branch, and no logical extension-spectrum theorem, is asserted. -/
theorem joint_iff (p : Fin 9 → ExtOrd) : Joint p ↔
    ∃ q v, Monotone v ∧ (∀ i, SelfVis 1 (v i)) ∧ p = label q v := by
  constructor
  · exact Joint.exists_shape
  · rintro ⟨q, v, hm, hv, rfl⟩
    exact label_joint q hm hv

/-- The individually maximal proper-probe caps at `(⊥, ⊥, a)` are not a joint
section: the first and third controllers cannot both expose `a`. -/
theorem independent_caps_not_joint {a : ExtOrd} (ha : a ≠ ⊥) :
    ¬ Joint ![⊥, ⊥, a, a, ⊥, a, ⊥, ⊥, ⊥] := by
  intro hp
  obtain ⟨g, σ, _, _, _, _, _, he⟩ := hp.2.1 0
  have h0 := he (probe 0)
  have h2 := he (controller 2)
  change min ⊥ a = min (σ (source 1)) (g 1) at h0
  change min a a = min (σ (source 1)) (g 1) at h2
  rw [min_self, ← h0, min_eq_left bot_le] at h2
  exact ha h2

/-- Equal proper probes do not force equal auxiliary sections. Arbitrarily
choosing a new sorting convention can therefore lose existing capped data. -/
theorem distinct_tied_sections {a b : ExtOrd} (ha : SelfVis 1 a) (hb : SelfVis 1 b)
    (hab : a < b) : ∃ p q, Joint p ∧ Joint q ∧
      (∀ i, p (probe i) = q (probe i)) ∧ p ≠ q := by
  let v : Fin 3 → ExtOrd := ![a, a, b]
  have hm : Monotone v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [v, hab.le]
  have hv : ∀ i, SelfVis 1 (v i) := by
    intro i; fin_cases i <;> assumption
  refine ⟨label 0 v, label 2 v, label_joint 0 hm hv, label_joint 2 hm hv, ?_, ?_⟩
  · intro i; fin_cases i <;> rfl
  · intro he
    have hh := congrFun he (controller 0)
    change b = a at hh
    exact (ne_of_lt hab) hh.symm

end ControllerPrefixFamily
end VaughtConjecture.Knight
