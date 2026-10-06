/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingLadderLowerRows

/-! # Whole lower-coordinate extraction from actual receiving sections

Availability at a mixed grade-one index chooses an actual rung or shadow.
Its parent dominates it, and a maximal parent leaf therefore dominates every
present original field, the request and both eligible ladder copies. The
faithful witness of that leaf recovers all those coordinates simultaneously.

This is an arbitrary target-local input theorem conditional only on the
literal lower-row formula. No selected-display coverage, normalized ambient,
or extension of the ambient to the whole scheme is assumed. Upper rows and
the lawfulness of a newly constructed output remain separate obligations.

Ported unchanged from the reviewer's branch `rounded-meet-extension` at `78e0bf8` (the mixed
receiving candidate, its recognition, readouts, caps, constructed localities and availability;
V-C discharges the private-projection premise of `mixed_lift_of_private`).
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ReceivingLadderCarrier

open Transform Value ExtOrd

variable {L : ℕ} {X Q U : Type*} [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)
  (field : Cell C → X) (request : X) (profile : Q → X → ℕ)

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC
local notation "T" => SupportLadderRows.Point L X Q

/-- A single actual serving leaf reads the complete physical lower vector,
not merely the named fields or the maximum of the shadows. -/
theorem exists_lowerShapeBelow [Nonempty Q] (hL : 0 < L)
    (hbound : ∀ a x, profile a x ≤ L)
    {BJ : Finset (Fin 3) × ℕ} (b : Bool) (hb : GradedLe (scope b, 1) BJ)
    (sem : Semantics D) (hrows : HasLadderRows C hC field request profile sem)
    (p : (D).below BJ → ExtOrd) (hp : RespectsSemanticsBelow sem BJ p) :
    ∃ a f, Monotone f ∧ f 0 = ⊥ ∧ (∀ i, SelfVis 1 (f i)) ∧
      ∀ d : (D).below (scope b, 1),
        p ⟨d.1, d.2.trans hb⟩ = lowerImage C hC field request profile a f d.1 := by
  let q : T → ExtOrd := fun v => p (tableAt C hC b hb v)
  have hq : SupportLadderRows.Lawful profile q :=
    lawful_tableBelow C hC field request profile b hb sem hrows p hp
  obtain ⟨a, ha⟩ := Finite.exists_max (fun a : Q => q (SupportLadderRows.leaf hL a))
  let owner := tableAt (X := X) (U := U) C hC b hb (SupportLadderRows.leaf hL a)
  have htable (v : T) : q v ≤ p owner :=
    (hq.le_parent hbound hL v).trans (ha (SupportLadderRows.parent v))
  have hdom (d : (D).below ((D).cell owner.1)) :
      p (CellScheme.below.incl owner d) ≤ p owner := by
    have hg : (D).grade d.1 = (D).grade owner.1 := by
      exact (below_ladder_grade C hC b (SupportLadderRows.leaf hL a) d).trans
        (ladder_grade C hC b (SupportLadderRows.leaf hL a)).symm
    obtain ⟨e, he, hde⟩ := hp.availability (CellScheme.below.incl owner d) owner d.2.1 hg
    have hei : (D).cell e.1 = (scope b, 1) := he.trans (added_index C hC _)
    obtain ⟨v, hv⟩ := at_ladder_index C hC b e.1 hei
    have hev : e = tableAt C hC b hb v := Subtype.ext hv
    rw [hev] at hde
    exact hde.trans (htable v)
  obtain ⟨g, σ, _, hg, h0, hm, h5, hr⟩ := hp.locality owner
  let f : ℕ → ExtOrd := fun i => min (σ (SupportLadderRows.source L i)) (g 1)
  refine ⟨a, f, fun _ _ h => min_le_min_right _ (hm (SupportLadderRows.source_mono L h)),
    ?_, ?_, ?_⟩
  · simp only [f, SupportLadderRows.source_zero, h0, min_bot_left]
  · intro i
    change SelfVis 1 (min (σ (SupportLadderRows.source L i)) (g 1))
    by_cases hi : σ (SupportLadderRows.source L i) ≤ g 1
    · rw [min_eq_left hi]
      have he := h5 (SupportLadderRows.source L i) 1 hi 1 le_rfl
      rw [SupportLadderRows.source_visible L i] at he
      exact he.symm
    · rw [min_eq_right (not_le.mp hi).le]
      exact (hg 1).symm
  · intro d
    let x : (D).below ((D).cell owner.1) :=
      ⟨d.1, by change GradedLe ((D).cell d.1) ((D).cell (added C hC _))
               rw [added_index]; exact d.2⟩
    have hx := hr x
    dsimp only at hx
    rw [min_eq_left (hdom x)] at hx
    change p (CellScheme.below.incl owner x) =
      min (σ (sem.E owner.1 x)) (g ((D).grade x.1)) at hx
    have hrw : sem.E owner.1 x =
        ladderRow C hC field request profile (SupportLadderRows.leaf hL a) x.1 :=
      hrows b (SupportLadderRows.leaf hL a) x
    rw [below_ladder_grade C hC b (SupportLadderRows.leaf hL a) x, hrw] at hx
    rw [ladderRow, SupportLadderRows.ceiling_leaf] at hx
    exact hx

end VaughtConjecture.Knight.ReceivingLadderCarrier
