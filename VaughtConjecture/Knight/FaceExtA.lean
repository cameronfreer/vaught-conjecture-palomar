/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TwoContextGlue
public import VaughtConjecture.Knight.WitnessSplice

/-! # The A-face obligation of the two-context glue

**Result** (`faceExtA'`): the A-face obligation `FaceExtA'` holds; hence the glued four-point
domain is legal conditional on the B-face obligation alone (`semSchemeGlue_of_B`).

**Constraints extracted before choosing the free value.**  From `p` respecting input A,
`p a₁ ≤ p a₂ ≤ p H₀, p s₀`; from `q` respecting the three-cell family,
`q a₁ ≤ q a₂ ≤ q b₁ ≤ q H₀, q s₀` — all by the antitone probe at a cell whose row value is the
controller's diagonal (`probe_diag₀`, `probe_diag₂`), using the mixed rows: `meet₃ t₀ t₁ = γ₀`
(the decoder depends on its cap only through its overflow value, `shift_min_cap`), so `a₂` reads
`ω+4` at `b₁` and `b₁` reads `ω+4` at `a₂`, `ω+3` at `a₁`.

**The free value** `x = q' b₁`, separated by role:
* preservation of input A's face: `ext₀ p x` is `p` on the image (`ext₀_emb`);
* agreement modulo `γ`: `x = p a₂` if `γ ≤ p a₂` or `q b₁ ≤ p a₂`; `x = q b₁` if `q b₁ ≤ γ`;
  `x = γ` otherwise;
* transformation witnesses: at input A's cells, `p`'s own transformation reindexed, `b₁` sent to
  the controller (`ext₀_locality_emb`); at `b₁`: source collapse of `a₂`'s transformation
  (`x = p a₂`), `q`'s own transformation (`x = q b₁`), or `q`'s transformation capped at `γ`.

No classification of respecting labellings is used.  Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## Stage 2: the mixed rows and the constraints they impose -/

section Rows

/-- The decoder's dependence on its cap is only through the overflow value. -/
theorem shift_min_cap {l : ℕ} {S : Finset Ordinal.{0}} {γ γ' : ExtOrd} (hle : γ ≤ γ') (x : ExtOrd) :
    min (shift l S γ x) γ = min (shift l S γ' x) γ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [shift_bot, shift_bot]
  · rw [shift_top, shift_top, min_self, min_eq_right hle]
  · rw [shift_ofOrd, shift_ofOrd]
    split_ifs
    · rw [min_self, min_eq_right hle]
    · rfl

theorem γ₀_le_γ₁ : γ₀ ≤ γ₁ := by
  unfold γ₀ γ₁
  rw [ofOrd_le_ofOrd]
  by_contra h
  rw [not_le] at h
  have := blockIdx_mono h.le
  rw [blockIdx_mul_add, blockIdx_mul_add] at this
  exact absurd (Nat.cast_le.mp this) (by decide)

/-- **The two bases agree up to input A's cap**: same proper row, same witnesses, and the decoders
differ only in their overflow value. -/
theorem agree₃_t₀_t₁ : agree₃ st₀ t₀ t₁ γ₀ := by
  refine ⟨fun c _ => rfl, fun H => ?_, fun s => ?_⟩
  · change min (shift 1 (valuesAt Prop3.gradeP t₀.F 1) γ₀
      (meet₁ (witness1 st₀.hT t₀.F (t₀.orderly st₀)) H)) γ₀ =
      min (shift 1 (valuesAt Prop3.gradeP t₀.F 1) γ₁
        (meet₁ (witness1 st₀.hT t₀.F (t₀.orderly st₀)) H)) γ₀
    exact shift_min_cap γ₀_le_γ₁ _
  · change min (shift 2 (valuesAt Prop3.gradeP t₀.F 2) γ₀ (meet₂ st₀ (t₀.wit2 st₀) s)) γ₀ =
      min (shift 2 (valuesAt Prop3.gradeP t₀.F 2) γ₁ (meet₂ st₀ (t₀.wit2 st₀) s)) γ₀
    exact shift_min_cap γ₀_le_γ₁ _

theorem meet₃_t₀_t₁ : meet₃ st₀ t₀ t₁ = γ₀ := by
  apply le_antisymm
  · exact (meet₃_le st₀ t₀ t₁).trans (min_le_left _ _)
  · apply le_meet₃ st₀
    rw [mem_agreeSet₃ st₀]
    exact ⟨γ₀_mem, le_min le_rfl γ₀_le_γ₁, γ₀_vis, agree₃_t₀_t₁⟩

theorem meet₃_t₁_t₀ : meet₃ st₀ t₁ t₀ = γ₀ := by rw [meet₃_comm, meet₃_t₀_t₁]

/-- The cells of the three-cell family, as `X`-values. -/
noncomputable abbrev a₁X : family₂.X := .inr (.inr (.inr ⟨a₁, Finset.mem_insert_self _ _⟩))
noncomputable abbrev a₂X : family₂.X :=
  .inr (.inr (.inr ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩))
noncomputable abbrev b₁X : family₂.X := .inr (.inr (.inr ⟨b₁,
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩))
noncomputable abbrev H₀X : family₂.X := .inr (.inl ⟨H₀c, Finset.mem_insert_self _ _⟩)
noncomputable abbrev s₀X : family₂.X := .inr (.inr (.inl ⟨s₀c, Finset.mem_singleton_self _⟩))

/-- Every level-one cell of the three-cell family is `H₀X`, every level-two cell is `s₀X`. -/
theorem eq_H₀X (H : ↥family₂.S₁) : (.inr (.inl H) : family₂.X) = H₀X := by
  have e : H = ⟨H₀c, Finset.mem_insert_self _ _⟩ := Subtype.ext (family₂_S₁ H.1 H.2)
  rw [e]
theorem eq_s₀X (s : ↥family₂.S₂) : (.inr (.inr (.inl s)) : family₂.X) = s₀X := by
  have e : s = ⟨s₀c, Finset.mem_singleton_self _⟩ := Subtype.ext (Finset.mem_singleton.mp s.2)
  rw [e]

/-- **The level-three rows at the witnesses**: each cell reads its cap. -/
theorem rowX_a₁_H : family₂.rowX a₁X H₀X = η₁ := by
  rw [Family.rowX_a_H]
  change min (t₀.rho1 st₀ (witness1 st₀.hT t₀.F (t₀.orderly st₀))) η₁ = η₁
  rw [Core3.rho1_wit1]
  exact min_eq_right η₁_le_γ₀
theorem rowX_a₂_H : family₂.rowX a₂X H₀X = γ₀ := by
  rw [Family.rowX_a_H]
  change min (t₀.rho1 st₀ (witness1 st₀.hT t₀.F (t₀.orderly st₀))) γ₀ = γ₀
  rw [Core3.rho1_wit1]
  change min γ₀ γ₀ = γ₀
  exact min_self _
theorem rowX_b₁_H : family₂.rowX b₁X H₀X = γ₁ := by
  rw [Family.rowX_a_H]
  change min (t₁.rho1 st₀ (witness1 st₀.hT t₁.F (t₁.orderly st₀))) γ₁ = γ₁
  rw [Core3.rho1_wit1]
  change min γ₁ γ₁ = γ₁
  exact min_self _
theorem rowX_a₁_s : family₂.rowX a₁X s₀X = η₁ := by
  rw [Family.rowX_a_s]
  exact CappedCore3.rho2_wit2C st₀ a₁
theorem rowX_a₂_s : family₂.rowX a₂X s₀X = γ₀ := by
  rw [Family.rowX_a_s]
  exact CappedCore3.rho2_wit2C st₀ a₂
theorem rowX_b₁_s : family₂.rowX b₁X s₀X = γ₁ := by
  rw [Family.rowX_a_s]
  exact CappedCore3.rho2_wit2C st₀ b₁

/-- **The level-three rows at the level-three cells.** -/
theorem rowX_a₁_a₁ : family₂.rowX a₁X a₁X = η₁ := by
  rw [Family.rowX_a_a]
  change min (meet₃ st₀ t₀ t₀) (min η₁ η₁) = η₁
  rw [CappedCore3.meet₃_self', min_self]
  exact min_eq_right η₁_le_γ₀
theorem rowX_a₁_a₂ : family₂.rowX a₁X a₂X = η₁ := by
  rw [Family.rowX_a_a]
  change min (meet₃ st₀ t₀ t₀) (min η₁ γ₀) = η₁
  rw [CappedCore3.meet₃_self', min_eq_left η₁_le_γ₀]
  exact min_eq_right η₁_le_γ₀
theorem rowX_a₁_b₁ : family₂.rowX a₁X b₁X = η₁ := by
  rw [Family.rowX_a_a]
  change min (meet₃ st₀ t₀ t₁) (min η₁ γ₁) = η₁
  rw [meet₃_t₀_t₁, min_eq_left (η₁_le_γ₀.trans γ₀_le_γ₁)]
  exact min_eq_right η₁_le_γ₀
theorem rowX_a₂_a₁ : family₂.rowX a₂X a₁X = η₁ := by
  rw [Family.rowX_a_a]
  change min (meet₃ st₀ t₀ t₀) (min γ₀ η₁) = η₁
  rw [CappedCore3.meet₃_self', min_eq_right η₁_le_γ₀]
  exact min_eq_right η₁_le_γ₀
theorem rowX_a₂_a₂ : family₂.rowX a₂X a₂X = γ₀ := by
  rw [Family.rowX_a_a]
  change min (meet₃ st₀ t₀ t₀) (min γ₀ γ₀) = γ₀
  rw [CappedCore3.meet₃_self', min_self]
  change min γ₀ γ₀ = γ₀
  exact min_self _
theorem rowX_a₂_b₁ : family₂.rowX a₂X b₁X = γ₀ := by
  rw [Family.rowX_a_a]
  change min (meet₃ st₀ t₀ t₁) (min γ₀ γ₁) = γ₀
  rw [meet₃_t₀_t₁, min_eq_left γ₀_le_γ₁, min_self]
theorem rowX_b₁_a₁ : family₂.rowX b₁X a₁X = η₁ := by
  rw [Family.rowX_a_a]
  change min (meet₃ st₀ t₁ t₀) (min γ₁ η₁) = η₁
  rw [meet₃_t₁_t₀, min_eq_right (η₁_le_γ₀.trans γ₀_le_γ₁)]
  exact min_eq_right η₁_le_γ₀
theorem rowX_b₁_a₂ : family₂.rowX b₁X a₂X = γ₀ := by
  rw [Family.rowX_a_a]
  change min (meet₃ st₀ t₁ t₀) (min γ₁ γ₀) = γ₀
  rw [meet₃_t₁_t₀, min_eq_right γ₀_le_γ₁, min_self]
theorem rowX_b₁_b₁ : family₂.rowX b₁X b₁X = γ₁ := by
  rw [Family.rowX_a_a]
  change min (meet₃ st₀ t₁ t₁) (min γ₁ γ₁) = γ₁
  rw [CappedCore3.meet₃_self', min_self]
  change min γ₁ γ₁ = γ₁
  exact min_self _

/-- Every row of the three-cell family reads input A's cap or less at every cell except the
level-three cells with a larger cap; the **collapse condition** for the two level-three rows. -/
theorem rowX_b₁_collapse (y : family₂.X) : min (family₂.rowX b₁X y) γ₀ = family₂.rowX a₂X y := by
  rcases y with c | H | s | a
  · rw [Family.rowX_a_inl, Family.rowX_a_inl]
    change min (min (t₀.F c) γ₁) γ₀ = min (t₀.F c) γ₀
    rw [min_assoc, min_eq_right γ₀_le_γ₁]
  · rw [eq_H₀X, rowX_b₁_H, rowX_a₂_H]; exact min_eq_right γ₀_le_γ₁
  · rw [eq_s₀X, rowX_b₁_s, rowX_a₂_s]; exact min_eq_right γ₀_le_γ₁
  · have ha : a.1 ∈ ({a₁, a₂, b₁} : Finset (CappedCore3 Prop3.gradeP T₀)) := a.2
    rcases Finset.mem_insert.mp ha with h | h
    · have e : a = ⟨a₁, Finset.mem_insert_self _ _⟩ := Subtype.ext h
      rw [e]
      change min (family₂.rowX b₁X a₁X) γ₀ = family₂.rowX a₂X a₁X
      rw [rowX_b₁_a₁, rowX_a₂_a₁]
      exact min_eq_left η₁_le_γ₀
    rcases Finset.mem_insert.mp h with h | h
    · have e : a = ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩ := Subtype.ext h
      rw [e]
      change min (family₂.rowX b₁X a₂X) γ₀ = family₂.rowX a₂X a₂X
      rw [rowX_b₁_a₂, rowX_a₂_a₂]
      exact min_self _
    · have e : a = ⟨b₁, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))⟩ := Subtype.ext (Finset.mem_singleton.mp h)
      rw [e]
      change min (family₂.rowX b₁X b₁X) γ₀ = family₂.rowX a₂X b₁X
      rw [rowX_b₁_b₁, rowX_a₂_b₁]
      exact min_eq_right γ₀_le_γ₁

end Rows

/-! ## Stage 3: the extension by one value -/

section Extension

/-- Every cell of a three-point family lies below `(univ, 3)`. -/
theorem le_top₀ (d : Cell C₀) : GradedLe (C₀.cell d) (Finset.univ, 3) :=
  ⟨Finset.subset_univ _, (C₀.grade_le_card_scope d).trans
    ((Finset.card_le_univ _).trans (by simp : Fintype.card (Fin 3) ≤ 3))⟩
theorem le_top₂ (d : Cell C₂) : GradedLe (C₂.cell d) (Finset.univ, 3) :=
  ⟨Finset.subset_univ _, (C₂.grade_le_card_scope d).trans
    ((Finset.card_le_univ _).trans (by simp : Fintype.card (Fin 3) ≤ 3))⟩

noncomputable abbrev cell₀ (x : family₀.X) : C₀.below (Finset.univ, 3) := ⟨family₀.e x, le_top₀ _⟩
noncomputable abbrev cell₂ (x : family₂.X) : C₂.below (Finset.univ, 3) := ⟨family₂.e x, le_top₂ _⟩

noncomputable abbrev a₁X₀ : family₀.X := .inr (.inr (.inr ⟨a₁, Finset.mem_insert_self _ _⟩))
noncomputable abbrev a₂X₀ : family₀.X :=
  .inr (.inr (.inr ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩))
noncomputable abbrev H₀X₀ : family₀.X := .inr (.inl ⟨H₀c, Finset.mem_insert_self _ _⟩)
noncomputable abbrev s₀X₀ : family₀.X := .inr (.inr (.inl ⟨s₀c, Finset.mem_singleton_self _⟩))

theorem embX₀_a₁ : embX₀ a₁X₀ = a₁X := rfl
theorem embX₀_a₂ : embX₀ a₂X₀ = a₂X := rfl
theorem embX₀_H₀ : embX₀ H₀X₀ = H₀X := rfl
theorem embX₀_s₀ : embX₀ s₀X₀ = s₀X := rfl

theorem embBelow₀_cell₀ (y : family₀.X) : embBelow₀ (cell₀ y) = cell₂ (embX₀ y) := by
  apply Subtype.ext
  change family₂.e (embX₀ (family₀.e.symm (family₀.e y))) = family₂.e (embX₀ y)
  rw [Equiv.symm_apply_apply]

/-- Rows of input A's family, read at two of its cells. -/
theorem rowX₀_eq (x y : family₀.X) : family₀.rowX x y = family₂.rowX (embX₀ x) (embX₀ y) :=
  (rowX_embX₀ x y).symm

/-- **Antitone probe, in a family**: a cell whose row value at the controller is the controller's
diagonal, of grade at most the controller's, is labelled at least the controller. -/
theorem probe_diag₀ {p : C₀.below (Finset.univ, 3) → ExtOrd}
    (hp : RespectsSemanticsBelow family₀.rows (Finset.univ, 3) p) (x y : family₀.X)
    (hs : (family₀.cellX y).1 ⊆ (family₀.cellX x).1)
    (hgr : (family₀.cellX y).2 ≤ (family₀.cellX x).2)
    (hrow : family₀.rowX x y = family₀.rowX x x) : p (cell₀ x) ≤ p (cell₀ y) := by
  have hle : GradedLe (family₀.scheme.cell (family₀.e y)) (family₀.scheme.cell (family₀.e x)) := by
    rw [Family.cell_e, Family.cell_e]; exact ⟨hs, hgr⟩
  have h := hp.ge_of_row_eq_diag (cell₀ x) ⟨family₀.e y, hle⟩ ?_ ?_
  · exact h
  · change family₀.rowX (family₀.e.symm (family₀.e x)) (family₀.e.symm (family₀.e y)) =
      family₀.rowX (family₀.e.symm (family₀.e x)) (family₀.e.symm (family₀.e x))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hrow]
  · change (family₀.scheme.cell (family₀.e y)).2 ≤ (family₀.scheme.cell (family₀.e x)).2
    rw [Family.cell_e, Family.cell_e]; exact hgr

theorem probe_diag₂ {q : C₂.below (Finset.univ, 3) → ExtOrd}
    (hq : RespectsSemanticsBelow family₂.rows (Finset.univ, 3) q) (x y : family₂.X)
    (hs : (family₂.cellX y).1 ⊆ (family₂.cellX x).1)
    (hgr : (family₂.cellX y).2 ≤ (family₂.cellX x).2)
    (hrow : family₂.rowX x y = family₂.rowX x x) : q (cell₂ x) ≤ q (cell₂ y) := by
  have hle : GradedLe (family₂.scheme.cell (family₂.e y)) (family₂.scheme.cell (family₂.e x)) := by
    rw [Family.cell_e, Family.cell_e]; exact ⟨hs, hgr⟩
  have h := hq.ge_of_row_eq_diag (cell₂ x) ⟨family₂.e y, hle⟩ ?_ ?_
  · exact h
  · change family₂.rowX (family₂.e.symm (family₂.e x)) (family₂.e.symm (family₂.e y)) =
      family₂.rowX (family₂.e.symm (family₂.e x)) (family₂.e.symm (family₂.e x))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hrow]
  · change (family₂.scheme.cell (family₂.e y)).2 ≤ (family₂.scheme.cell (family₂.e x)).2
    rw [Family.cell_e, Family.cell_e]; exact hgr

/-- **The constraints on input A's labelling `p`**: `p a₁ ≤ p a₂ ≤ p H₀, p s₀`. -/
theorem p_a₁_le_a₂ {p : C₀.below (Finset.univ, 3) → ExtOrd}
    (hp : RespectsSemanticsBelow family₀.rows (Finset.univ, 3) p) :
    p (cell₀ a₁X₀) ≤ p (cell₀ a₂X₀) :=
  probe_diag₀ hp a₁X₀ a₂X₀ (Finset.Subset.refl _) le_rfl
    (by rw [rowX₀_eq, rowX₀_eq, embX₀_a₁, embX₀_a₂, rowX_a₁_a₂, rowX_a₁_a₁])
theorem p_a₂_le_H {p : C₀.below (Finset.univ, 3) → ExtOrd}
    (hp : RespectsSemanticsBelow family₀.rows (Finset.univ, 3) p) :
    p (cell₀ a₂X₀) ≤ p (cell₀ H₀X₀) :=
  probe_diag₀ hp a₂X₀ H₀X₀ (Finset.Subset.refl _) (by change (1 : ℕ) ≤ 3; decide)
    (by rw [rowX₀_eq, rowX₀_eq, embX₀_a₂, embX₀_H₀, rowX_a₂_H, rowX_a₂_a₂])
theorem p_a₂_le_s {p : C₀.below (Finset.univ, 3) → ExtOrd}
    (hp : RespectsSemanticsBelow family₀.rows (Finset.univ, 3) p) :
    p (cell₀ a₂X₀) ≤ p (cell₀ s₀X₀) :=
  probe_diag₀ hp a₂X₀ s₀X₀ (Finset.Subset.refl _) (by change (2 : ℕ) ≤ 3; decide)
    (by rw [rowX₀_eq, rowX₀_eq, embX₀_a₂, embX₀_s₀, rowX_a₂_s, rowX_a₂_a₂])

/-- **The constraints on the three-cell labelling `q`**: `q a₁ ≤ q a₂ ≤ q b₁ ≤ q H₀, q s₀`. -/
theorem q_a₂_le_b₁ {q : C₂.below (Finset.univ, 3) → ExtOrd}
    (hq : RespectsSemanticsBelow family₂.rows (Finset.univ, 3) q) :
    q (cell₂ a₂X) ≤ q (cell₂ b₁X) :=
  probe_diag₂ hq a₂X b₁X (Finset.Subset.refl _) le_rfl (by rw [rowX_a₂_b₁, rowX_a₂_a₂])
theorem q_a₁_le_a₂ {q : C₂.below (Finset.univ, 3) → ExtOrd}
    (hq : RespectsSemanticsBelow family₂.rows (Finset.univ, 3) q) :
    q (cell₂ a₁X) ≤ q (cell₂ a₂X) :=
  probe_diag₂ hq a₁X a₂X (Finset.Subset.refl _) le_rfl (by rw [rowX_a₁_a₂, rowX_a₁_a₁])
theorem q_b₁_le_H {q : C₂.below (Finset.univ, 3) → ExtOrd}
    (hq : RespectsSemanticsBelow family₂.rows (Finset.univ, 3) q) :
    q (cell₂ b₁X) ≤ q (cell₂ H₀X) :=
  probe_diag₂ hq b₁X H₀X (Finset.Subset.refl _) (by change (1 : ℕ) ≤ 3; decide)
    (by rw [rowX_b₁_H, rowX_b₁_b₁])
theorem q_b₁_le_s {q : C₂.below (Finset.univ, 3) → ExtOrd}
    (hq : RespectsSemanticsBelow family₂.rows (Finset.univ, 3) q) :
    q (cell₂ b₁X) ≤ q (cell₂ s₀X) :=
  probe_diag₂ hq b₁X s₀X (Finset.Subset.refl _) (by change (2 : ℕ) ≤ 3; decide)
    (by rw [rowX_b₁_s, rowX_b₁_b₁])

/-! ### The extension by one value at `b₁` -/

theorem a₁_ne_b₁ : a₁ ≠ b₁ := fun h => η₁_ne_γ₁ (congrArg CappedCore3.η h)
theorem a₂_ne_b₁ : a₂ ≠ b₁ := fun h => γ₁_ne_γ₀ (congrArg CappedCore3.η h).symm

/-- The image of input A's cells misses exactly `b₁`. -/
theorem not_emb₀_b₁ (i : Cell C₀) : emb₀ i ≠ (cell₂ b₁X).1 := by
  intro h
  change family₂.e (embX₀ (family₀.e.symm i)) = family₂.e b₁X at h
  have h' := family₂.e.injective h
  rcases hw : family₀.e.symm i with c | H | s | a
  all_goals rw [hw] at h'
  · exact absurd h' (by simp [embX₀])
  · exact absurd h' (by simp [embX₀])
  · exact absurd h' (by simp [embX₀])
  · have h'' : a.1 = b₁ := by
      have := congrArg (fun z : family₂.X => match z with
        | .inr (.inr (.inr b)) => b.1 | _ => b₁) h'
      exact this
    have ha : a.1 ∈ ({a₁, a₂} : Finset (CappedCore3 Prop3.gradeP T₀)) := a.2
    rcases Finset.mem_insert.mp ha with h1 | h1
    · exact a₁_ne_b₁ (h1.symm.trans h'')
    · exact a₂_ne_b₁ ((Finset.mem_singleton.mp h1).symm.trans h'')

theorem embBelow₀_injective : Function.Injective embBelow₀ := fun _ _ h =>
  Subtype.ext (emb₀_injective (congrArg Subtype.val h))

/-- Every cell of the three-cell family is an image or `b₁`. -/
theorem cases₂ (d : C₂.below (Finset.univ, 3)) :
    (∃ c : C₀.below (Finset.univ, 3), embBelow₀ c = d) ∨ d = cell₂ b₁X := by
  by_cases h3 : C₂.grade d.1 ≤ 2
  · obtain ⟨i, hi⟩ := exists_emb₀_of_grade_le_two d.1 h3
    exact Or.inl ⟨⟨i, le_top₀ i⟩, Subtype.ext hi⟩
  · rcases hw : family₂.e.symm d.1 with c | H | s | a
    · exfalso; apply h3
      change (family₂.cellX (family₂.e.symm d.1)).2 ≤ 2
      rw [hw]; exact c.gradeP_le_two
    · exfalso; apply h3
      change (family₂.cellX (family₂.e.symm d.1)).2 ≤ 2
      rw [hw]; change (1 : ℕ) ≤ 2; decide
    · exfalso; apply h3
      change (family₂.cellX (family₂.e.symm d.1)).2 ≤ 2
      rw [hw]; change (2 : ℕ) ≤ 2; decide
    · have ha : a.1 ∈ ({a₁, a₂, b₁} : Finset (CappedCore3 Prop3.gradeP T₀)) := a.2
      have hd : d.1 = family₂.e (.inr (.inr (.inr a))) := by
        rw [← hw, Equiv.apply_symm_apply]
      rcases Finset.mem_insert.mp ha with h | h
      · left
        refine ⟨cell₀ a₁X₀, Subtype.ext ?_⟩
        rw [embBelow₀_cell₀, embX₀_a₁]
        change family₂.e a₁X = d.1
        rw [hd]
        have e : a = ⟨a₁, Finset.mem_insert_self _ _⟩ := Subtype.ext h
        rw [e]
      rcases Finset.mem_insert.mp h with h | h
      · left
        refine ⟨cell₀ a₂X₀, Subtype.ext ?_⟩
        rw [embBelow₀_cell₀, embX₀_a₂]
        change family₂.e a₂X = d.1
        rw [hd]
        have e : a = ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩ := Subtype.ext h
        rw [e]
      · right
        apply Subtype.ext
        change d.1 = family₂.e b₁X
        rw [hd]
        have e : a = ⟨b₁, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self _))⟩ := Subtype.ext (Finset.mem_singleton.mp h)
        rw [e]

open Classical in
/-- **The extension**: input A's labelling on its cells, the value `x` at `b₁`. -/
noncomputable def ext₀ (p : C₀.below (Finset.univ, 3) → ExtOrd) (x : ExtOrd)
    (d : C₂.below (Finset.univ, 3)) : ExtOrd :=
  if h : ∃ c, embBelow₀ c = d then p (Classical.choose h) else x

theorem ext₀_emb (p : C₀.below (Finset.univ, 3) → ExtOrd) (x : ExtOrd)
    (c : C₀.below (Finset.univ, 3)) : ext₀ p x (embBelow₀ c) = p c := by
  classical
  unfold ext₀
  rw [dite_of_pos ⟨c, rfl⟩]
  congr 1
  exact embBelow₀_injective (Classical.choose_spec (⟨c, rfl⟩ : ∃ c', embBelow₀ c' = embBelow₀ c))

theorem ext₀_b₁ (p : C₀.below (Finset.univ, 3) → ExtOrd) (x : ExtOrd) :
    ext₀ p x (cell₂ b₁X) = x := by
  classical
  unfold ext₀
  rw [dite_of_neg]
  rintro ⟨c, hc⟩
  exact not_emb₀_b₁ c.1 (congrArg Subtype.val hc)

end Extension

section Locality

open Classical in
/-- A left inverse of the inclusion of input A's cells (junk off the image). -/
noncomputable def inv₀ (c : Cell C₂) : Cell C₀ :=
  if h : ∃ i, emb₀ i = c then Classical.choose h else family₀.e a₂X₀

theorem emb₀_inv₀ {c : Cell C₂} (h : ∃ i, emb₀ i = c) : emb₀ (inv₀ c) = c := by
  classical
  unfold inv₀
  rw [dite_of_pos h]
  exact Classical.choose_spec h

theorem inv₀_emb₀ (i : Cell C₀) : inv₀ (emb₀ i) = i :=
  emb₀_injective (emb₀_inv₀ ⟨i, rfl⟩)

/-- A cell of the three-cell family other than `b₁` is an image. -/
theorem exists_emb₀_of_ne_b₁ (c : Cell C₂) (h : c ≠ (cell₂ b₁X).1) : ∃ i, emb₀ i = c := by
  rcases cases₂ ⟨c, le_top₂ c⟩ with ⟨c', hc'⟩ | hb
  · exact ⟨c'.1, congrArg Subtype.val hc'⟩
  · exact absurd (congrArg Subtype.val hb) h

theorem grade_b₁ : C₂.grade (cell₂ b₁X).1 = 3 := by
  change (C₂.cell (family₂.e b₁X)).2 = 3
  rw [Family.cell_e]; rfl

/-- The level-three cells of input A are `a₁` and `a₂`. -/
theorem grade3_cases₀ (c : Cell C₀) (h : C₀.grade c = 3) :
    c = family₀.e a₁X₀ ∨ c = family₀.e a₂X₀ := by
  have hc : family₀.cellX (family₀.e.symm c) = (Finset.univ, 3) := by
    rw [← Family.cell_eq]
    refine Prod.ext ?_ h
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin]
    have h3 := C₀.grade_le_card_scope c
    rw [h] at h3
    exact le_antisymm ((Finset.card_le_univ _).trans (by simp)) h3
  obtain ⟨a, ha⟩ := old_full_three hc
  have ha2 : a.1 ∈ ({a₁, a₂} : Finset (CappedCore3 Prop3.gradeP T₀)) := a.2
  have hc' : c = family₀.e (.inr (.inr (.inr a))) := by rw [← ha, Equiv.apply_symm_apply]
  rcases Finset.mem_insert.mp ha2 with h1 | h1
  · left
    rw [hc']
    have e : a = ⟨a₁, Finset.mem_insert_self _ _⟩ := Subtype.ext h1
    rw [e]
  · right
    rw [hc']
    have e : a = ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩ :=
      Subtype.ext (Finset.mem_singleton.mp h1)
    rw [e]

/-- **The row of `a₁` or `a₂` reads its diagonal at `b₁`.** -/
theorem rowX_at_b₁_eq_diag (c : Cell C₀) (h : C₀.grade c = 3) :
    family₂.rowX (embX₀ (family₀.e.symm c)) b₁X =
      family₂.rowX (embX₀ (family₀.e.symm c)) (embX₀ (family₀.e.symm c)) := by
  rcases grade3_cases₀ c h with rfl | rfl
  · rw [Equiv.symm_apply_apply, embX₀_a₁, rowX_a₁_b₁, rowX_a₁_a₁]
  · rw [Equiv.symm_apply_apply, embX₀_a₂, rowX_a₂_b₁, rowX_a₂_a₂]

/-- The label of `p` at a level-three cell of input A is at most `p a₂`. -/
theorem p_le_a₂_of_grade3 {p : C₀.below (Finset.univ, 3) → ExtOrd}
    (hp : RespectsSemanticsBelow family₀.rows (Finset.univ, 3) p) (c : C₀.below (Finset.univ, 3))
    (h : C₀.grade c.1 = 3) : p c ≤ p (cell₀ a₂X₀) := by
  rcases grade3_cases₀ c.1 h with hc | hc
  · have : c = cell₀ a₁X₀ := Subtype.ext hc
    rw [this]; exact p_a₁_le_a₂ hp
  · have : c = cell₀ a₂X₀ := Subtype.ext hc
    rw [this]

/-- **Locality of the extension at every cell of input A**: input A's transformation, reindexed
along the left inverse, with `b₁` sent to the controller itself (its row value there is the
diagonal's, and its label `x ≥ p a₂` does not lower the cap). -/
theorem ext₀_locality_emb {p : C₀.below (Finset.univ, 3) → ExtOrd}
    (hp : RespectsSemanticsBelow family₀.rows (Finset.univ, 3) p) {x : ExtOrd}
    (hx : p (cell₀ a₂X₀) ≤ x) (c : C₀.below (Finset.univ, 3)) :
    TransformsTo (fun d : C₂.below (C₂.cell (embBelow₀ c).1) => C₂.grade d.1)
      (family₂.rows.E (embBelow₀ c).1)
      (fun d => min (ext₀ p x (CellScheme.below.incl (embBelow₀ c) d))
        (ext₀ p x (embBelow₀ c))) := by
  classical
  -- the lower set of `emb c` maps to the lower set of `c`
  have hmem : ∀ d : C₂.below (C₂.cell (embBelow₀ c).1), d.1 ≠ (cell₂ b₁X).1 →
      GradedLe (C₀.cell (inv₀ d.1)) (C₀.cell c.1) := by
    intro d hd
    have h := d.2
    change GradedLe (C₂.cell d.1) (C₂.cell (emb₀ c.1)) at h
    rw [← emb₀_inv₀ (exists_emb₀_of_ne_b₁ d.1 hd), cell_emb₀, cell_emb₀] at h
    exact h
  have hb₁ : ∀ d : C₂.below (C₂.cell (embBelow₀ c).1), d.1 = (cell₂ b₁X).1 → C₀.grade c.1 = 3 := by
    intro d hd
    have h := d.2.2
    change C₂.grade d.1 ≤ C₂.grade (emb₀ c.1) at h
    rw [hd, grade_b₁] at h
    have h' : C₂.grade (emb₀ c.1) = C₀.grade c.1 := by
      change (C₂.cell (emb₀ c.1)).2 = (C₀.cell c.1).2; rw [cell_emb₀]
    rw [h'] at h
    exact le_antisymm ((C₀.grade_le_card_scope _).trans
      ((Finset.card_le_univ _).trans (by simp))) h
  let ψc : Cell C₂ → Cell C₀ := fun z => if z = (cell₂ b₁X).1 then c.1 else inv₀ z
  have hψc : ∀ d : C₂.below (C₂.cell (embBelow₀ c).1),
      GradedLe (C₀.cell (ψc d.1)) (C₀.cell c.1) := by
    intro d
    by_cases hd : d.1 = (cell₂ b₁X).1
    · change GradedLe (C₀.cell (if d.1 = (cell₂ b₁X).1 then c.1 else inv₀ d.1)) _
      rw [ite_eq_left hd]; exact ⟨Finset.Subset.refl _, le_rfl⟩
    · change GradedLe (C₀.cell (if d.1 = (cell₂ b₁X).1 then c.1 else inv₀ d.1)) _
      rw [ite_eq_right hd]; exact hmem d hd
  let ψ : C₂.below (C₂.cell (embBelow₀ c).1) → C₀.below (C₀.cell c.1) := fun d => ⟨ψc d.1, hψc d⟩
  have hψ_pos : ∀ d : C₂.below (C₂.cell (embBelow₀ c).1), d.1 = (cell₂ b₁X).1 → (ψ d).1 = c.1 :=
    fun d hd => by
      change (if d.1 = (cell₂ b₁X).1 then c.1 else inv₀ d.1) = c.1; rw [ite_eq_left hd]
  have hψ_neg : ∀ d : C₂.below (C₂.cell (embBelow₀ c).1), ¬ d.1 = (cell₂ b₁X).1 →
      (ψ d).1 = inv₀ d.1 := fun d hd => by
    change (if d.1 = (cell₂ b₁X).1 then c.1 else inv₀ d.1) = inv₀ d.1; rw [ite_eq_right hd]
  have key := (hp.locality c).reindex ψ
  refine transformsTo_congr ?_ ?_ ?_ key
  · funext d
    change C₀.grade (ψ d).1 = C₂.grade d.1
    by_cases hd : d.1 = (cell₂ b₁X).1
    · have e : (ψ d).1 = c.1 := hψ_pos d hd
      rw [e, hb₁ d hd, hd, grade_b₁]
    · have e : (ψ d).1 = inv₀ d.1 := hψ_neg d hd
      rw [e]
      change (C₀.cell (inv₀ d.1)).2 = (C₂.cell d.1).2
      rw [← cell_emb₀, emb₀_inv₀ (exists_emb₀_of_ne_b₁ d.1 hd)]
  · funext d
    change family₀.rowX (family₀.e.symm c.1) (family₀.e.symm (ψ d).1) =
      family₂.rowX (family₂.e.symm (emb₀ c.1)) (family₂.e.symm d.1)
    have hc : family₂.e.symm (emb₀ c.1) = embX₀ (family₀.e.symm c.1) := by
      change family₂.e.symm (family₂.e _) = _; rw [Equiv.symm_apply_apply]
    rw [hc]
    by_cases hd : d.1 = (cell₂ b₁X).1
    · have e : (ψ d).1 = c.1 := hψ_pos d hd
      rw [e, hd]
      change family₀.rowX _ _ = family₂.rowX _ (family₂.e.symm (family₂.e b₁X))
      rw [Equiv.symm_apply_apply, rowX_at_b₁_eq_diag c.1 (hb₁ d hd), ← rowX_embX₀]
    · have e : (ψ d).1 = inv₀ d.1 := hψ_neg d hd
      rw [e, ← emb₀_inv₀ (exists_emb₀_of_ne_b₁ d.1 hd)]
      change family₀.rowX _ _ = family₂.rowX _ (family₂.e.symm (family₂.e _))
      rw [Equiv.symm_apply_apply, rowX_embX₀, inv₀_emb₀]
  · funext d
    change min (p (CellScheme.below.incl c (ψ d))) (p c) =
      min (ext₀ p x (CellScheme.below.incl (embBelow₀ c) d)) (ext₀ p x (embBelow₀ c))
    rw [ext₀_emb]
    by_cases hd : d.1 = (cell₂ b₁X).1
    · have e : CellScheme.below.incl (embBelow₀ c) d = cell₂ b₁X := Subtype.ext hd
      have e' : CellScheme.below.incl c (ψ d) = c := Subtype.ext (hψ_pos d hd)
      rw [e, e', ext₀_b₁, min_self, min_eq_right ((p_le_a₂_of_grade3 hp c (hb₁ d hd)).trans hx)]
    · have e : CellScheme.below.incl (embBelow₀ c) d =
          embBelow₀ (CellScheme.below.incl c (ψ d)) := by
        apply Subtype.ext
        change d.1 = emb₀ (ψ d).1
        have e1 : (ψ d).1 = inv₀ d.1 := hψ_neg d hd
        rw [e1, emb₀_inv₀ (exists_emb₀_of_ne_b₁ d.1 hd)]
      rw [e, ext₀_emb]

end Locality

section Main

theorem cell_eq_univ_of_grade3₂ (z : Cell C₂) (h : C₂.grade z = 3) :
    C₂.cell z = (Finset.univ, 3) := by
  refine Prod.ext ?_ h
  apply Finset.eq_univ_of_card
  rw [Fintype.card_fin]
  have h3 := C₂.grade_le_card_scope z
  rw [h] at h3
  exact le_antisymm ((Finset.card_le_univ _).trans (by simp)) h3

theorem grade_emb₀ (c : C₀.below (Finset.univ, 3)) : C₂.grade (embBelow₀ c).1 = C₀.grade c.1 := by
  change (C₂.cell (emb₀ c.1)).2 = (C₀.cell c.1).2
  rw [cell_emb₀]

theorem grade_cell₀_a₂ : C₀.grade (cell₀ a₂X₀).1 = 3 := by
  change (C₀.cell (family₀.e a₂X₀)).2 = 3
  rw [Family.cell_e]; rfl

/-- **The extension respects the three-cell family**, given its locality at `b₁`. -/
theorem respects_ext₀ {p : C₀.below (Finset.univ, 3) → ExtOrd}
    (hp : RespectsSemanticsBelow family₀.rows (Finset.univ, 3) p) {x : ExtOrd}
    (hx_vis : extVisibilityReplace x 3 3 = x) (hx : p (cell₀ a₂X₀) ≤ x)
    (hb : TransformsTo (fun d : C₂.below (C₂.cell (cell₂ b₁X).1) => C₂.grade d.1)
      (family₂.rows.E (cell₂ b₁X).1)
      (fun d => min (ext₀ p x (CellScheme.below.incl (cell₂ b₁X) d)) (ext₀ p x (cell₂ b₁X)))) :
    RespectsSemanticsBelow family₂.rows (Finset.univ, 3) (ext₀ p x) where
  orderly d := by
    rcases cases₂ d with ⟨c, rfl⟩ | rfl
    · have := hp.orderly c
      dsimp only at this ⊢
      rw [ext₀_emb, grade_emb₀]
      exact this
    · dsimp only
      rw [ext₀_b₁, grade_b₁]
      exact hx_vis.symm
  locality Sig := by
    rcases cases₂ Sig with ⟨c, rfl⟩ | rfl
    · exact ext₀_locality_emb hp hx c
    · exact hb
  availability Sig Xi₀ hs hg := by
    by_cases hc : C₂.cell Sig.1 = C₂.cell Xi₀.1
    · exact ⟨Sig, hc, le_rfl⟩
    · have hne3 : C₂.grade Sig.1 ≠ 3 := by
        intro h3
        apply hc
        rw [cell_eq_univ_of_grade3₂ _ h3, cell_eq_univ_of_grade3₂ _ (hg ▸ h3)]
      rcases cases₂ Sig with ⟨c, rfl⟩ | rfl
      · rcases cases₂ Xi₀ with ⟨c', rfl⟩ | rfl
        · obtain ⟨Xi, hcell, hle⟩ := hp.availability c c'
            (by
              have := hs
              change (C₂.cell (emb₀ c.1)).1 ⊆ (C₂.cell (emb₀ c'.1)).1 at this
              rw [cell_emb₀, cell_emb₀] at this
              exact this)
            (by
              have := hg
              rw [grade_emb₀, grade_emb₀] at this
              exact this)
          refine ⟨embBelow₀ Xi, ?_, ?_⟩
          · change C₂.cell (emb₀ Xi.1) = C₂.cell (emb₀ c'.1)
            rw [cell_emb₀, cell_emb₀]; exact hcell
          · rw [ext₀_emb, ext₀_emb]; exact hle
        · exfalso
          apply hne3
          rw [hg, grade_b₁]
      · exact absurd grade_b₁ hne3

theorem hK₂ (d : C₂.below (C₂.cell (cell₂ b₁X).1)) : C₂.grade d.1 ≤ 3 :=
  (C₂.grade_le_card_scope _).trans ((Finset.card_le_univ _).trans (by simp))

theorem γ₀_eq : γ₀ = ofOrd (Ordinal.omega0 * (1 : ℕ) + (4 : ℕ)) := rfl

/-- **`FaceExtA'` holds.**  The free value at `b₁` is `p a₂` when `p a₂ ≥ γ` or `p a₂ ≥ q b₁`
(locality at `b₁` by source collapse of `a₂`'s transformation), `q b₁` when `q b₁ ≤ γ` (`q`'s own
transformation), and `γ` otherwise (`q`'s transformation capped at `γ`). -/
theorem faceExtA' : FaceExtA' := by
  intro p q γ hp hq hγ hagree
  have hq₂b := q_a₂_le_b₁ hq
  have hag₂ : min (q (cell₂ a₂X)) γ = min (p (cell₀ a₂X₀)) γ := by
    have := hagree (cell₀ a₂X₀)
    rw [embBelow₀_cell₀, embX₀_a₂] at this
    exact this
  have hvis₂ : extVisibilityReplace (p (cell₀ a₂X₀)) 3 3 = p (cell₀ a₂X₀) := by
    have := hp.orderly (cell₀ a₂X₀)
    dsimp only at this
    rw [grade_cell₀_a₂] at this
    exact this.symm
  have hvisb : extVisibilityReplace (q (cell₂ b₁X)) 3 3 = q (cell₂ b₁X) := by
    have := hq.orderly (cell₂ b₁X)
    dsimp only at this
    rw [grade_b₁] at this
    exact this.symm
  have hqloc := hq.locality (cell₂ b₁X)
  have hagree_img : ∀ (x : ExtOrd) (c : C₀.below (Finset.univ, 3)),
      min (ext₀ p x (embBelow₀ c)) γ = min (q (embBelow₀ c)) γ := by
    intro x c; rw [ext₀_emb]; exact (hagree c).symm
  by_cases hI : γ ≤ p (cell₀ a₂X₀) ∨ q (cell₂ b₁X) ≤ p (cell₀ a₂X₀)
  · -- the value `p a₂`: locality at `b₁` by source collapse
    refine ⟨ext₀ p (p (cell₀ a₂X₀)), respects_ext₀ hp hvis₂ le_rfl ?_, ?_,
      fun d => ext₀_emb p _ d⟩
    · have h₂ := ext₀_locality_emb hp le_rfl (cell₀ a₂X₀)
      have hcellA : C₂.cell (embBelow₀ (cell₀ a₂X₀)).1 = C₂.cell (cell₂ b₁X).1 := by
        rw [embBelow₀_cell₀, embX₀_a₂]
        change C₂.cell (family₂.e a₂X) = C₂.cell (family₂.e b₁X)
        rw [Family.cell_e, Family.cell_e]; rfl
      let φ : C₂.below (C₂.cell (cell₂ b₁X).1) → C₂.below (C₂.cell (embBelow₀ (cell₀ a₂X₀)).1) :=
        fun d => ⟨d.1, by rw [hcellA]; exact d.2⟩
      have key := h₂.reindex φ
      refine TransformsTo.collapse (K := 3) hK₂ (ξ := Ordinal.omega0 * (1 : ℕ) + (4 : ℕ))
        (by rw [finitePart_mul_add]; decide) ?_ (transformsTo_congr rfl rfl ?_ key)
      · intro d
        change min (family₂.rowX (family₂.e.symm (family₂.e b₁X)) (family₂.e.symm d.1))
          (ofOrd (Ordinal.omega0 * (1 : ℕ) + (4 : ℕ))) =
          family₂.rowX (family₂.e.symm (emb₀ (cell₀ a₂X₀).1)) (family₂.e.symm d.1)
        rw [Equiv.symm_apply_apply, ← γ₀_eq, rowX_b₁_collapse]
        change family₂.rowX a₂X _ = family₂.rowX (family₂.e.symm (family₂.e (embX₀ (family₀.e.symm
          (family₀.e a₂X₀))))) _
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, embX₀_a₂]
      · funext d
        change min (ext₀ p _ (CellScheme.below.incl (embBelow₀ (cell₀ a₂X₀)) (φ d)))
          (ext₀ p _ (embBelow₀ (cell₀ a₂X₀))) =
          min (ext₀ p _ (CellScheme.below.incl (cell₂ b₁X) d)) (ext₀ p _ (cell₂ b₁X))
        rw [ext₀_emb, ext₀_b₁]
        rfl
    · intro d
      rcases cases₂ d with ⟨c, rfl⟩ | rfl
      · exact hagree_img _ c
      · rw [ext₀_b₁]
        rcases hI with h | h
        · rw [min_eq_right h]
          have hγq : γ ≤ q (cell₂ a₂X) := by
            by_contra hlt
            rw [not_le] at hlt
            rw [min_eq_left hlt.le, min_eq_right h] at hag₂
            exact absurd hag₂ (ne_of_lt hlt)
          rw [min_eq_right (hγq.trans hq₂b)]
        · by_cases hγ' : γ ≤ p (cell₀ a₂X₀)
          · rw [min_eq_right hγ']
            have hγq : γ ≤ q (cell₂ a₂X) := by
              by_contra hlt
              rw [not_le] at hlt
              rw [min_eq_left hlt.le, min_eq_right hγ'] at hag₂
              exact absurd hag₂ (ne_of_lt hlt)
            rw [min_eq_right (hγq.trans hq₂b)]
          · rw [not_le] at hγ'
            rw [min_eq_left hγ'.le] at hag₂ ⊢
            have hq₂ : q (cell₂ a₂X) = p (cell₀ a₂X₀) := by
              rw [min_eq_left ((hq₂b.trans h).trans hγ'.le)] at hag₂
              exact hag₂
            have hqb : q (cell₂ b₁X) = p (cell₀ a₂X₀) := le_antisymm h (hq₂ ▸ hq₂b)
            rw [hqb, min_eq_left hγ'.le]
  · rw [not_or, not_le, not_le] at hI
    obtain ⟨hp₂γ, hp₂b⟩ := hI
    by_cases hbγ : q (cell₂ b₁X) ≤ γ
    · -- the value `q b₁`: `q`'s own transformation
      refine ⟨ext₀ p (q (cell₂ b₁X)), respects_ext₀ hp hvisb hp₂b.le ?_, ?_,
        fun d => ext₀_emb p _ d⟩
      · refine transformsTo_congr rfl rfl ?_ hqloc
        funext d
        change min (q (CellScheme.below.incl (cell₂ b₁X) d)) (q (cell₂ b₁X)) =
          min (ext₀ p _ (CellScheme.below.incl (cell₂ b₁X) d)) (ext₀ p _ (cell₂ b₁X))
        rw [ext₀_b₁]
        rcases cases₂ (CellScheme.below.incl (cell₂ b₁X) d) with ⟨c, hc⟩ | hc
        · rw [← hc, ext₀_emb]
          have h1 := hagree c
          calc min (q (embBelow₀ c)) (q (cell₂ b₁X))
              = min (min (q (embBelow₀ c)) γ) (q (cell₂ b₁X)) := by
                rw [min_assoc, min_eq_right hbγ]
            _ = min (min (p c) γ) (q (cell₂ b₁X)) := by rw [h1]
            _ = min (p c) (q (cell₂ b₁X)) := by rw [min_assoc, min_eq_right hbγ]
        · rw [hc, ext₀_b₁]
      · intro d
        rcases cases₂ d with ⟨c, rfl⟩ | rfl
        · exact hagree_img _ c
        · rw [ext₀_b₁]
    · rw [not_le] at hbγ
      -- the value `γ`: `q`'s transformation capped at `γ`
      refine ⟨ext₀ p γ, respects_ext₀ hp hγ hp₂γ.le ?_, ?_, fun d => ext₀_emb p _ d⟩
      · have hcap := hqloc.cap hK₂ hγ
        refine transformsTo_congr rfl rfl ?_ hcap
        funext d
        change min (min (q (CellScheme.below.incl (cell₂ b₁X) d)) (q (cell₂ b₁X))) γ =
          min (ext₀ p γ (CellScheme.below.incl (cell₂ b₁X) d)) (ext₀ p γ (cell₂ b₁X))
        rw [ext₀_b₁]
        rcases cases₂ (CellScheme.below.incl (cell₂ b₁X) d) with ⟨c, hc⟩ | hc
        · rw [← hc, ext₀_emb, min_assoc, min_eq_right hbγ.le, hagree c]
        · rw [hc, ext₀_b₁, min_self, min_eq_right hbγ.le, min_self]
      · intro d
        rcases cases₂ d with ⟨c, rfl⟩ | rfl
        · exact hagree_img _ c
        · rw [ext₀_b₁, min_self, min_eq_right hbγ.le]

/-- **The glued domain, conditional on the B-face obligation alone.** -/
noncomputable def semSchemeGlue_of_B (HB : FaceExtB') : SemScheme 4 := semSchemeGlue' faceExtA' HB

end Main

end VaughtConjecture.Knight
