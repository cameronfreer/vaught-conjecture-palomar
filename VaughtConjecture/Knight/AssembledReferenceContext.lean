/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteAssemblyInstance
public import VaughtConjecture.Knight.FiniteCutoffBound

/-! # The assembled scheme as an old reference context

A nonvacuous reference-data regression (2026-09-05): use the grade-three row of the capped cell
with cap `ω + 4` as a
respecting labelling of the whole scheme, and verify a finite reference context on it — an old
reference at `ω + 1` (the singleton cell), threshold `N = 3`, cutoff `ω`, cap and trigger the
capped cell itself — so that the cutoff readback (`FiniteReferenceData.CutoffBound.readback_top`)
applies to an **actual respecting labelling with the trigger active**, not vacuously.

Verified here:

* `rowA₂_respects`: the row respects the restricted semantics (consistency of the assembly);
* the reference labels: the representative reads `ω + 1`, the cap and trigger read `ω + 4`
  (`rowA₂_s0`, `rowA₂_cap`), the requested cells read `ω + 4`, `ω + 4`, `ω + 3`
  (`rowA₂_H₀`, `rowA₂_s₀`, `rowA₂_a₁`);
* `refData_cutoffBound`: the cutoff lower bound holds at every request (three requests: the
  level-one witness, the level-two witness, the other capped cell; block `ω`, offset `0`);
* `refData_readback`: hence `truncExt ω (f Θ) = ⊤` at every requested cell — exact readback
  below the cutoff `ω`, a lower bound above it;
* `rowA₂_stage_bound`: every label of the row is below the stage `ω·2`, so the row is a
  stage-`ω·2` labelling in the sense of the tower.

The fresh point, the fresh request and the comparison domain are `Knight/FourPointDuplication.lean`.
Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

section Reference

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-- The remaining members of the concrete families. -/
theorem mem_S₂_eq {s : Core2 (gradeP := Prop3.gradeP) (T := T₀)} (h : s ∈ family₀.S₂) : s = s₀c :=
  Finset.mem_singleton.mp h

theorem mem_S₃_cases {a : CappedCore3 Prop3.gradeP T₀} (h : a ∈ family₀.S₃) : a = a₁ ∨ a = a₂ := by
  have h' : a ∈ ({a₁, a₂} : Finset (CappedCore3 Prop3.gradeP T₀)) := h
  rcases Finset.mem_insert.mp h' with rfl | h''
  · exact Or.inl rfl
  · exact Or.inr (Finset.mem_singleton.mp h'')

/-- The capped cell with cap `ω + 4`, as a member of the family. -/
noncomputable def a₂c : ↥family₀.S₃ := ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
noncomputable def a₁c : ↥family₀.S₃ := ⟨a₁, Finset.mem_insert_self _ _⟩
noncomputable def s₀cc : ↥family₀.S₂ := ⟨s₀c, Finset.mem_singleton_self _⟩
noncomputable def H₀cc : ↥family₀.S₁ := ⟨H₀c, Finset.mem_insert_self _ _⟩

/-- The controlling cell of the reference context. -/
noncomputable def top : Cell family₀.scheme := family₀.e (.inr (.inr (.inr a₂c)))

/-- Its lower set: the whole scheme. -/
abbrev Dref : Type := family₀.scheme.below (family₀.scheme.cell top)

theorem cell_top : family₀.scheme.cell top = (Finset.univ, 3) := Family.cell_e _ _

/-- A cell of the lower set from an `X`-cell. -/
noncomputable def cellB (x : family₀.X) (h : GradedLe (family₀.cellX x) (Finset.univ, 3)) : Dref :=
  ⟨family₀.e x, by rw [Family.cell_e, cell_top]; exact h⟩

/-- **The labelling**: the row of the capped cell with cap `ω + 4`. -/
noncomputable def rowA₂ : Dref → ExtOrd := family₀.rows.E top

/-- The row respects the restricted semantics (consistency of the assembly). -/
theorem rowA₂_respects : RespectsSemanticsBelow family₀.rows (family₀.scheme.cell top) rowA₂ :=
  family₀.rows_isConsistent top

theorem rowA₂_cellB (x : family₀.X) (h : GradedLe (family₀.cellX x) (Finset.univ, 3)) :
    rowA₂ (cellB x h) = family₀.rowX (.inr (.inr (.inr a₂c))) x := by
  change family₀.rowX (family₀.e.symm (family₀.e _)) (family₀.e.symm (family₀.e x)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-! ### The reference labels -/

theorem hs0 : GradedLe (family₀.cellX (.inl .s0)) (Finset.univ, 3) :=
  ⟨Finset.subset_univ _, by decide⟩
theorem hH₀ : GradedLe (family₀.cellX (.inr (.inl H₀cc))) (Finset.univ, 3) :=
  ⟨Finset.subset_univ _, by decide⟩
theorem hs₀ : GradedLe (family₀.cellX (.inr (.inr (.inl s₀cc)))) (Finset.univ, 3) :=
  ⟨Finset.subset_univ _, by decide⟩
theorem ha₁ : GradedLe (family₀.cellX (.inr (.inr (.inr a₁c)))) (Finset.univ, 3) :=
  ⟨Finset.subset_univ _, le_rfl⟩
theorem ha₂ : GradedLe (family₀.cellX (.inr (.inr (.inr a₂c)))) (Finset.univ, 3) :=
  ⟨Finset.subset_univ _, le_rfl⟩

/-- The representative: the singleton cell reads `ω + 1`. -/
theorem rowA₂_s0 : rowA₂ (cellB (.inl .s0) hs0) = ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ)) := by
  rw [rowA₂_cellB, Family.rowX_a_inl]
  change min (t₀.F .s0) γ₀ = _
  rw [t₀_F_eq (by decide)]
  exact min_eq_left v₀_le_γ₀

/-- The cap and trigger: the capped cell reads its cap `ω + 4`. -/
theorem rowA₂_cap : rowA₂ (cellB (.inr (.inr (.inr a₂c))) ha₂) = γ₀ := by
  rw [rowA₂_cellB, Family.rowX_a_a]
  change min (meet₃ st₀ t₀ t₀) (min γ₀ γ₀) = γ₀
  rw [CappedCore3.meet₃_self']
  change min γ₀ (min γ₀ γ₀) = γ₀
  rw [min_self, min_self]

/-- The level-one witness reads `ω + 4`. -/
theorem rowA₂_H₀ : rowA₂ (cellB (.inr (.inl H₀cc)) hH₀) = γ₀ := by
  rw [rowA₂_cellB, Family.rowX_a_H]
  change min (t₀.rho1 st₀ (witness1 st₀.hT t₀.F (t₀.orderly st₀))) γ₀ = γ₀
  rw [Core3.rho1_wit1]
  change min γ₀ γ₀ = γ₀
  rw [min_self]

/-- The level-two witness reads `ω + 4`. -/
theorem rowA₂_s₀ : rowA₂ (cellB (.inr (.inr (.inl s₀cc))) hs₀) = γ₀ := by
  rw [rowA₂_cellB, Family.rowX_a_s]
  change min (t₀.rho2 st₀ (t₀.wit2 st₀)) γ₀ = γ₀
  rw [Core3.rho2_wit2]
  change min γ₀ γ₀ = γ₀
  rw [min_self]

/-- The other capped cell reads `ω + 3`. -/
theorem rowA₂_a₁ : rowA₂ (cellB (.inr (.inr (.inr a₁c))) ha₁) = η₁ := by
  rw [rowA₂_cellB, Family.rowX_a_a]
  change min (meet₃ st₀ t₀ t₀) (min γ₀ η₁) = η₁
  rw [CappedCore3.meet₃_self']
  change min γ₀ (min γ₀ η₁) = η₁
  rw [min_eq_right η₁_le_γ₀, min_eq_right η₁_le_γ₀]

/-! ### The reference data -/

theorem grade_cellB (x : family₀.X) (h : GradedLe (family₀.cellX x) (Finset.univ, 3)) :
    family₀.scheme.grade (cellB x h).1 = (family₀.cellX x).2 := by
  change (family₀.cellX (family₀.e.symm (family₀.e x))).2 = _
  rw [Equiv.symm_apply_apply]

/-- **The reference context**: threshold `3`, cap and trigger the capped cell, representative the
singleton cell (for every block), three requests at block `ω`, offset `0`. -/
noncomputable def refData : FiniteReferenceData Dref (fun d => family₀.scheme.grade d.1) where
  N := 3
  cap := cellB (.inr (.inr (.inr a₂c))) ha₂
  cap_grade := grade_cellB _ _
  trigger := cellB (.inr (.inr (.inr a₂c))) ha₂
  rep _ := cellB (.inl .s0) hs0
  requests := [⟨cellB (.inr (.inl H₀cc)) hH₀, Ordinal.omega0 * (1 : ℕ), 0⟩,
    ⟨cellB (.inr (.inr (.inl s₀cc))) hs₀, Ordinal.omega0 * (1 : ℕ), 0⟩,
    ⟨cellB (.inr (.inr (.inr a₁c))) ha₁, Ordinal.omega0 * (1 : ℕ), 0⟩]
  req_grade_le r hr := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [grade_cellB] <;> decide
  rep_grade_le r _ := by rw [grade_cellB]; decide
  offset_lt r hr := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide

/-- The trigger is active. -/
theorem refData_trigger : rowA₂ refData.trigger ≠ ⊥ := by
  change rowA₂ (cellB (.inr (.inr (.inr a₂c))) ha₂) ≠ ⊥
  rw [rowA₂_cap]; exact ofOrd_ne_bot _

theorem limitPart_omega_add_one :
    limitPart (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ)) = Ordinal.omega0 * (1 : ℕ) := by
  conv_lhs => rw [← limitPart_mul_nat 1]
  rw [limitPart_limitPart_add_nat, limitPart_mul_nat]

/-- **The cutoff lower bound** at every request: the normalized reference `ω` is at most every
requested label (`ω + 4`, `ω + 4`, `ω + 3`) under the cap `ω + 4`. -/
theorem refData_cutoffBound : refData.CutoffBound rowA₂ := by
  intro _ r hr
  have hrep : rowA₂ (refData.rep r.block) = ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ)) := rowA₂_s0
  have hcap : rowA₂ refData.cap = γ₀ := rowA₂_cap
  have hω : ofOrd (Ordinal.omega0 * (1 : ℕ)) ≤ γ₀ := by
    unfold γ₀; rw [ofOrd_le_ofOrd]; exact le_self_add
  simp only [refData, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
  · rw [hrep, hcap]
    change min (extVisibilityReplace (ofOrd (Ordinal.omega0 * (1 : ℕ) + (1 : ℕ))) 3 0) γ₀ ≤
      min (rowA₂ _) γ₀
    rw [extVisibilityReplace_ofOrd, visibilityReplace,
      ite_eq_left (by rw [finitePart_mul_add]; decide),
      ordinalReplace, limitPart_omega_add_one, Nat.cast_zero, add_zero, min_eq_left hω]
    first
      | rw [rowA₂_H₀, min_self]; exact hω
      | rw [rowA₂_s₀, min_self]; exact hω
      | rw [rowA₂_a₁, min_eq_left η₁_le_γ₀]
        unfold η₁; rw [ofOrd_le_ofOrd]; exact le_self_add

/-- **The readback** at every request: the requested label truncated at the cutoff `ω` is `⊤`. -/
theorem refData_readback (r : FiniteRequest Dref) (hr : r ∈ refData.requests) :
    truncExt (Ordinal.omega0 * (1 : ℕ)) (rowA₂ r.cell) = ⊤ := by
  refine refData_cutoffBound.readback_top refData_trigger hr ?_ (limitPart_mul_nat _) (j := 1)
    (by decide) rowA₂_s0 ?_
  · simp only [refData, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rfl
  · change ofOrd (Ordinal.omega0 * (1 : ℕ)) ≤ rowA₂ (cellB (.inr (.inr (.inr a₂c))) ha₂)
    rw [rowA₂_cap]
    unfold γ₀; rw [ofOrd_le_ofOrd]; exact le_self_add

/-! ### The stage bound -/

/-- The stage `ω + ω = ω·2`. -/
noncomputable abbrev stage : Ordinal.{0} := Ordinal.omega0 * (1 : ℕ) + Ordinal.omega0

/-- Every label of the row is below the stage `ω·2`. -/
theorem rowA₂_stage_bound (d : Dref) : rowA₂ d < ofOrd stage := by
  have hv : v₀ < ofOrd stage := by
    unfold v₀; rw [ofOrd_lt_ofOrd]
    exact add_lt_add_right (Ordinal.natCast_lt_omega0 1) _
  have hγ : γ₀ < ofOrd stage := by
    unfold γ₀; rw [ofOrd_lt_ofOrd]
    exact add_lt_add_right (Ordinal.natCast_lt_omega0 4) _
  have hη : η₁ < ofOrd stage := lt_of_le_of_lt η₁_le_γ₀ hγ
  have hbot : (⊥ : ExtOrd) < ofOrd stage := bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)
  obtain ⟨i, hi⟩ := d
  have hd : GradedLe (family₀.cellX (family₀.e.symm i)) (Finset.univ, 3) := by
    rw [cell_top] at hi; exact hi
  have hd_eq : (⟨i, hi⟩ : Dref) = cellB (family₀.e.symm i) hd := by
    apply Subtype.ext
    change i = family₀.e (family₀.e.symm i)
    rw [Equiv.apply_symm_apply]
  rw [hd_eq, rowA₂_cellB]
  rcases family₀.e.symm i with c | H | s | b
  · rw [Family.rowX_a_inl]
    change min (t₀.F c) γ₀ < _
    by_cases hc : c.gradeP ≤ 1
    · rw [t₀_F_eq hc]
      change min v₀ γ₀ < _
      rw [min_eq_left v₀_le_γ₀]; exact hv
    · rw [t₀_F_bot (by have := c.gradeP_le_two; omega), min_eq_left bot_le]; exact hbot
  · rw [Family.rowX_a_H, mem_S₁_eq H.2]
    change min (t₀.rho1 st₀ (witness1 st₀.hT t₀.F (t₀.orderly st₀))) γ₀ < _
    rw [Core3.rho1_wit1]
    change min γ₀ γ₀ < _
    rw [min_self]; exact hγ
  · rw [Family.rowX_a_s, mem_S₂_eq s.2]
    change min (t₀.rho2 st₀ (t₀.wit2 st₀)) γ₀ < _
    rw [Core3.rho2_wit2]
    change min γ₀ γ₀ < _
    rw [min_self]; exact hγ
  · rw [Family.rowX_a_a]
    rcases mem_S₃_cases b.2 with hb | hb
    · rw [hb]
      change min (meet₃ st₀ t₀ t₀) (min γ₀ η₁) < _
      rw [CappedCore3.meet₃_self']
      change min γ₀ (min γ₀ η₁) < _
      rw [min_eq_right η₁_le_γ₀, min_eq_right η₁_le_γ₀]; exact hη
    · rw [hb]
      change min (meet₃ st₀ t₀ t₀) (min γ₀ γ₀) < _
      rw [CappedCore3.meet₃_self']
      change min γ₀ (min γ₀ γ₀) < _
      rw [min_self, min_self]; exact hγ

end Reference

end VaughtConjecture.Knight

