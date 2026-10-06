/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorReadback

/-! # One-chart capped readback

The readback calculation of the upper-only route (newapproach16 new29 §3, new31 §5): from the
**ordinary** numerical relation of an admissible source at a cutoff `j ≥ N`, one normalized
witness `σ` through `N` that reads the source's donor section as a section `u` capped at a height
`m ≥ H`, the actual cap and reference labels literally, and a positive gate, conclude the
**capped** donor equality

  `u d ∧ β = p d ∧ β`,  `β = R.cut R.vactL`.

No LOW clause, no low reference, no extracted two-threshold state, no synchronization and no
bottom reflection of `σ` are used, and the source's anchor is arbitrary.  For a donor top this
gives `u d ≥ β`, not literal top — exactly the distinction that lets LOW be omitted; literal
donor tops remain `LowRef.readback_of_actualFace`'s business.

* `gate_of_trigger`: one actual row inequality `x ≤ st.gate` with `σ x ≠ ⊥` activates the source.
* `capC_ne_bot_of_read`: the source cap is positive because its image is the actual cap.
* `capped_readback`: the calculation, through `cut_map`/`sel_map`, `cut_congr`/`sel_congr` and
  `sel_actual`. -/

@[expose] public section

namespace VaughtConjecture.Knight.CappedDonor.Ref

open Transform Value ExtOrd
noncomputable section

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-- One positive trigger activates the source: a row entry below the source gate with nonbottom
image forces the source gate nonbottom (monotonicity and `σ ⊥ = ⊥`). -/
theorem gate_of_trigger {j : ℕ} {st : R.State j} {σ : ExtOrd → ExtOrd} (hmono : Monotone σ)
    (hbot : σ ⊥ = ⊥) {x : ExtOrd} (hle : x ≤ st.gate) (hx : σ x ≠ ⊥) : st.gate ≠ ⊥ := by
  intro hz
  apply hx
  rw [hz] at hle
  exact le_bot_iff.mp ((hmono hle).trans_eq hbot)

/-- The source cap is positive once its image is the actual cap. -/
theorem capC_ne_bot_of_read {j : ℕ} (hj : N ≤ j) {st : R.State j} {σ : ExtOrd → ExtOrd}
    (hbot : σ ⊥ = ⊥) (hcap : σ (st.v (R.capC hj)) = R.vact R.cap) : st.v (R.capC hj) ≠ ⊥ := by
  intro hz
  rw [hz, hbot] at hcap
  exact (ne_bot_of_gt R.cap_pos) hcap.symm

/-- **One-chart capped readback.**  For an admissible source `st` at cutoff `j ≥ N` with positive
gate, a witness `σ` through `N` reading its donor section as `u` capped at `m ≥ vact cap`, and
the actual cap and reference labels literally:
`min (u d) (cut vactL) = min (p d) (cut vactL)` at every present donor cell. -/
theorem capped_readback {j : ℕ} (hj : N ≤ j) {st : R.State j} (hst : R.Admissible st)
    {Kσ : ℕ} (hK : N ≤ Kσ) {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop Kσ) σ)
    {m : ExtOrd} (hm : R.vact R.cap ≤ m) {u : P.scheme.below (effP nP j) → ExtOrd}
    (hu : ∀ d, σ (st.u d) = min (u d) m)
    (hcap : σ (st.v (R.capC hj)) = R.vact R.cap)
    (href : ∀ i, σ (st.v (CellScheme.below.mono (R.capLe hj) (R.lowRef i))) = R.vact (R.ref i))
    (hg : st.gate ≠ ⊥) (d : P.scheme.below (effP nP j)) :
    min (u d) (R.cut R.vactL) = min (R.p d.1) (R.cut R.vactL) := by
  have hvcap : st.v (R.capC hj) ≠ ⊥ := capC_ne_bot_of_read hj hσ.bot hcap
  have hrel := hst.relation hj hg hvcap d
  -- the cut and the selector of the source's image are the actual ones: they depend only on the
  -- cap and the references, which are read literally
  have hcut : σ (R.cut (R.lowC hj st.v)) = R.cut R.vactL := by
    rw [← cut_map hσ hK]
    exact cut_congr hcap href
  have hsel : σ (R.sel (R.lowC hj st.v) d.1) = min (R.p d.1) (R.cut R.vactL) := by
    rw [← sel_map hσ hK,
      sel_congr (v₁ := fun e => σ (R.lowC hj st.v e)) (v₂ := R.vactL) hcap href, sel_actual]
  have h := congrArg σ hrel
  rw [hσ.mono.map_min, hu, hcut, hsel] at h
  have hβm : R.cut R.vactL ≤ m := (cut_actual_lt_cap (R := R)).le.trans hm
  rwa [min_assoc, min_eq_right hβm] at h

end
end VaughtConjecture.Knight.CappedDonor.Ref
