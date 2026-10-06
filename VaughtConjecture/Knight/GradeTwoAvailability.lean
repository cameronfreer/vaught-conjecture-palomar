/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoConsistency

/-! # The two-level tower: availability, consistency, coding, completeness

* **Availability** of every new row toward every index of its lower set (`availability_new`):
  toward a proper index by the member's base availability; toward `(A, 1)` by a level-one member
  itself (its self-reading is its cap, `levelCap_self`) or by the owned witness of a level-two
  member (whose decoded reading of the witness is the member's cap, `dec_witness_cap`); toward
  `(A, 2)` by the level-two member itself.  Every reading of a member's row is under its cap
  (`row_le_cap_one`, `row_le_cap_two`).
* **Consistency** of every new row (`respects_new`, from the localities of
  `Knight/GradeTwoConsistency.lean`) and of the whole semantics (`towerSem_consistent`, with
  the base rows).
* **Coding** (`towerSem_isCoded`) and **completeness** (`tower_complete`).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}
  (sem₀ : Semantics D₀) (I M : ℕ) (P : (BaseCells D₀ 2 → ExtOrd) → Prop)
  (hAk : ∀ k, 1 ≤ k → k ≤ M + 2 → (A, k) ∈ Plan.gradedPlan D₀.plan)
  (hI : Fintype.card (Cell D₀) + 2 ≤ I) (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A)

include sem₀ I M P hAk hI hproper

/-- The tower semantics' rows. -/
local notation "SE" => Semantics.E (towerSem sem₀ I M P hAk hI hproper)
/-- The tower's lower sets. -/
local notation "Tbelow" => CellScheme.below (tower sem₀ I M P hAk)
/-- The tower's graded indices. -/
local notation "Tcell" => CellScheme.cell (tower sem₀ I M P hAk)
/-- The tower's grades. -/
local notation "Tgrade" => CellScheme.grade (tower sem₀ I M P hAk)
/-- The tower's scopes. -/
local notation "Tscope" => CellScheme.scope (tower sem₀ I M P hAk)
/-- A new cell. -/
local notation "NEW" => addFull.new (hlevel sem₀ I M P hAk)
/-- An old cell. -/
local notation "OLD" => addFull.old (hlevel sem₀ I M P hAk)
/-- The lower-set equivalence of a new cell. -/
local notation "BN" => addFull.belowNew (hlevel sem₀ I M P hAk)
/-- The level of a new cell. -/
local notation "LV" => level sem₀ I M P
/-- The member of a new cell. -/
local notation "MEM" => memOf sem₀ I M P
/-- The row of a new cell. -/
local notation "ROW" => newRow sem₀ I M P hI

/-! ## Every reading is under the cap -/

omit M hAk hproper in
theorem readOne_le_cap (m : Member sem₀ I 2 P) (m' : Member₁ sem₀ I) :
    readOne sem₀ I P hI m m' ≤ m.γ :=
  m.dec_le_cap (ne_top_of_mem_alph (levelCap_mem _ _ _ _ _ _))

omit hAk hproper in
theorem row_le_cap_one (m : Member₁ sem₀ I) (k : ℕ) (hk : lv sem₀ I M P (Sum.inl m) = k) (x) :
    rowOf sem₀ I M P hI (Sum.inl m) k hk x ≤ m.γ := by
  rcases x with b | j'
  · exact m.le_cap _
  · change (match MEM j'.1 with
      | Sum.inl m' => levelCap 1 I m.F m.γ m'.F m'.γ
      | Sum.inr _ => ⊥) ≤ m.γ
    rcases MEM j'.1 with m' | m'
    · exact levelCap_le_left _ _ _ _ _ _
    · exact bot_le

omit hAk hproper in
theorem row_le_cap_two (m : Member sem₀ I 2 P) (k : ℕ)
    (hk : lv sem₀ I M P (Sum.inr (Sum.inl m)) = k)
    (x) : rowOf sem₀ I M P hI (Sum.inr (Sum.inl m)) k hk x ≤ m.γ := by
  rcases x with b | j'
  · exact m.le_cap _
  · change (match MEM j'.1 with
      | Sum.inl m' => readOne sem₀ I P hI m m'
      | Sum.inr (Sum.inl m') =>
          levelCap 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ
      | Sum.inr (Sum.inr _) => ⊥) ≤ m.γ
    rcases MEM j'.1 with m' | m' | i'
    · exact readOne_le_cap sem₀ I P hI m m'
    · exact levelCap_le_left _ _ _ _ _ _
    · exact bot_le

/-- Every reading of a level-one row is under the member's cap. -/
theorem E_le_cap_one {j : Fin (famCard sem₀ I M P)} {m : Member₁ sem₀ I} (hm : MEM j = Sum.inl m)
    (d : Tbelow (Tcell (NEW j))) : SE (NEW j) d ≤ m.γ := by
  obtain ⟨x, rfl⟩ := (BN j).surjective d
  rw [E_new_apply, newRow_eq sem₀ I M P hI hm]
  exact row_le_cap_one sem₀ I M P hI m _ _ x

/-- Every reading of a level-two row is under the member's cap. -/
theorem E_le_cap_two {j : Fin (famCard sem₀ I M P)} {m : Member sem₀ I 2 P}
    (hm : MEM j = Sum.inr (Sum.inl m)) (d : Tbelow (Tcell (NEW j))) : SE (NEW j) d ≤ m.γ := by
  obtain ⟨x, rfl⟩ := (BN j).surjective d
  rw [E_new_apply, newRow_eq sem₀ I M P hI hm]
  exact row_le_cap_two sem₀ I M P hI m _ _ x

/-! ## The self-readings -/

/-- A level-one member reads itself at its cap. -/
theorem E_self_one {j : Fin (famCard sem₀ I M P)} {m : Member₁ sem₀ I} (hm : MEM j = Sum.inl m) :
    SE (NEW j) (BN j (Sum.inr ⟨j, le_rfl⟩)) = m.γ := by
  rw [E_new_apply, newRow_one_new sem₀ I M P hI hm, hm]
  exact levelCap_self _ _ _ _ m.γ_mem m.γ_vis

/-- A level-two member reads itself at its cap. -/
theorem E_self_two {j : Fin (famCard sem₀ I M P)} {m : Member sem₀ I 2 P}
    (hm : MEM j = Sum.inr (Sum.inl m)) : SE (NEW j) (BN j (Sum.inr ⟨j, le_rfl⟩)) = m.γ := by
  rw [E_new_apply, newRow_two_new sem₀ I M P hI hm, hm]
  exact levelCap_self _ _ _ _ m.γ_mem m.γ_vis

/-- A level-two member reads its owned witness at its cap. -/
theorem E_witness_two {j : Fin (famCard sem₀ I M P)} {m : Member sem₀ I 2 P}
    (hm : MEM j = Sum.inr (Sum.inl m)) :
    SE (NEW j) (witnessCell sem₀ I M P hAk hI hm) = m.γ := by
  unfold witnessCell
  rw [E_new_apply, newRow_two_new sem₀ I M P hI hm, memOf_witness sem₀ I M P hI m]
  change m.dec (levelCap 1 I (m.witness hI).F (m.witness hI).γ (m.witness hI).F (m.witness hI).γ) =
    m.γ
  rw [levelCap_self _ _ _ _ (m.witness hI).γ_mem (m.witness hI).γ_vis, Member.dec_witness_cap]

/-! ## Availability -/

omit hI in
/-- Below a new cell, a cell whose scope is contained in an old cell's scope is old. -/
theorem old_of_scope_subset {j : Fin (famCard sem₀ I M P)} (Sig : Tbelow (Tcell (NEW j)))
    (b₀ : Cell D₀) (hs : Tscope Sig.1 ⊆ Tscope (OLD b₀)) :
    ∃ (b : Cell D₀) (hb : D₀.grade b ≤ LV j), Sig = BN j (Sum.inl ⟨b, hb⟩) := by
  rcases below_new_cases sem₀ I M P hAk j Sig with ⟨b, hb, rfl⟩ | ⟨j', hj', rfl⟩
  · exact ⟨b, hb, rfl⟩
  · exfalso
    apply hproper b₀
    rw [addFull.belowNew_inr, addFull.scope_new, addFull.scope_old] at hs
    exact le_antisymm (D₀.isPlan.subset_of_mem (D₀.scope_mem_plan b₀)) hs

/-- **Availability toward a proper index**, from a member's base availability. -/
theorem availability_old {j : Fin (famCard sem₀ I M P)} {k : ℕ} (F : BaseCells D₀ k → ExtOrd)
    (hF : RespectsBase sem₀ k F) (hk : LV j = k)
    (hrow : ∀ (b' : Cell D₀) (hb' : D₀.grade b' ≤ LV j),
      ROW j (Sum.inl ⟨b', hb'⟩) = F ⟨b', hb'.trans_eq hk⟩)
    (Sig : Tbelow (Tcell (NEW j))) (b₀ : Cell D₀) (hb₀ : D₀.grade b₀ ≤ LV j)
    (hs : Tscope Sig.1 ⊆ Tscope (BN j (Sum.inl ⟨b₀, hb₀⟩)).1)
    (hg : Tgrade Sig.1 = Tgrade (BN j (Sum.inl ⟨b₀, hb₀⟩)).1) :
    ∃ Xi : Tbelow (Tcell (NEW j)), Tcell Xi.1 = Tcell (BN j (Sum.inl ⟨b₀, hb₀⟩)).1 ∧
      SE (NEW j) Sig ≤ SE (NEW j) Xi := by
  obtain ⟨b, hb, rfl⟩ := old_of_scope_subset sem₀ I M P hAk hproper Sig b₀ hs
  rw [addFull.belowNew_inl, addFull.belowNew_inl, addFull.scope_old, addFull.scope_old] at hs
  rw [addFull.belowNew_inl, addFull.belowNew_inl, addFull.grade_old, addFull.grade_old] at hg
  obtain ⟨Xi, hXi, hle⟩ := hF.availability ⟨b, hb.trans_eq hk⟩ ⟨b₀, hb₀.trans_eq hk⟩ hs hg
  have hgX : D₀.grade Xi.1 ≤ LV j := by
    unfold CellScheme.grade; rw [hXi]; exact hb₀
  refine ⟨BN j (Sum.inl ⟨Xi.1, hgX⟩), ?_, ?_⟩
  · rw [addFull.belowNew_inl, addFull.belowNew_inl, addFull.cell_old, addFull.cell_old, hXi]
  · rw [E_new_apply, E_new_apply, hrow, hrow]
    exact hle

/-- **Availability of every new row** toward every index of its lower set. -/
theorem availability_new (j : Fin (famCard sem₀ I M P)) (Sig Xi₀ : Tbelow (Tcell (NEW j)))
    (hs : Tscope Sig.1 ⊆ Tscope Xi₀.1) (hg : Tgrade Sig.1 = Tgrade Xi₀.1) :
    ∃ Xi : Tbelow (Tcell (NEW j)), Tcell Xi.1 = Tcell Xi₀.1 ∧ SE (NEW j) Sig ≤ SE (NEW j) Xi := by
  obtain ⟨t, hm⟩ : ∃ t, MEM j = t := ⟨_, rfl⟩
  rcases below_new_cases sem₀ I M P hAk j Xi₀ with ⟨b₀, hb₀, rfl⟩ | ⟨j₀, hj₀, rfl⟩
  · -- toward a proper index
    rcases t with m | m | i
    · exact availability_old sem₀ I M P hAk hI hproper m.F m.respects
        (level_eq_of_memOf_inl sem₀ I M P hm) (fun b' hb' => newRow_one_old sem₀ I M P hI hm b' hb')
        Sig b₀ hb₀ hs hg
    · exact availability_old sem₀ I M P hAk hI hproper m.F m.respects
        (level_eq_of_memOf_inr_inl sem₀ I M P hm)
        (fun b' hb' => newRow_two_old sem₀ I M P hI hm b' hb') Sig b₀ hb₀ hs hg
    · refine ⟨BN j (Sum.inl ⟨b₀, hb₀⟩), rfl, ?_⟩
      rw [addFull.addFullSem_E_new, addFull.addFullSem_E_new, newRow_mute sem₀ I M P hI hm,
        newRow_mute sem₀ I M P hI hm]
  · -- toward a full-scope index
    have hg' : Tgrade Sig.1 = LV j₀ := by rw [hg, grade_belowNew_new sem₀ I M P hAk]
    rcases t with m | m | i
    · -- a level-one member: itself
      have hl := level_eq_of_memOf_inl sem₀ I M P hm
      have hj₀' : LV j₀ = 1 := le_antisymm (hj₀.trans hl.le) (one_le_lv _ _ _ _ _)
      refine ⟨BN j (Sum.inr ⟨j, le_rfl⟩), ?_, ?_⟩
      · change Tcell (NEW j) = Tcell (NEW j₀)
        rw [addFull.cell_new, addFull.cell_new, hl, hj₀']
      · rw [E_self_one sem₀ I M P hAk hI hproper hm]
        exact E_le_cap_one sem₀ I M P hAk hI hproper hm Sig
    · -- a level-two member: its witness at level one, itself at level two
      have hl := level_eq_of_memOf_inr_inl sem₀ I M P hm
      have hj₀' : LV j₀ = 1 ∨ LV j₀ = 2 := by
        have h2 : LV j₀ ≤ 2 := hj₀.trans hl.le
        have h1 : 1 ≤ LV j₀ := one_le_lv sem₀ I M P (MEM j₀)
        omega
      rcases hj₀' with hj₀' | hj₀'
      · refine ⟨witnessCell sem₀ I M P hAk hI hm, ?_, ?_⟩
        · rw [cell_witnessCell sem₀ I M P hAk hI hm]
          change ((Tcell (NEW j)).1, 1) = Tcell (NEW j₀)
          rw [addFull.cell_new, addFull.cell_new, hj₀']
        · rw [E_witness_two sem₀ I M P hAk hI hproper hm]
          exact E_le_cap_two sem₀ I M P hAk hI hproper hm Sig
      · refine ⟨BN j (Sum.inr ⟨j, le_rfl⟩), ?_, ?_⟩
        · change Tcell (NEW j) = Tcell (NEW j₀)
          rw [addFull.cell_new, addFull.cell_new, hl, hj₀']
        · rw [E_self_two sem₀ I M P hAk hI hproper hm]
          exact E_le_cap_two sem₀ I M P hAk hI hproper hm Sig
    · refine ⟨BN j (Sum.inr ⟨j₀, hj₀⟩), rfl, ?_⟩
      rw [addFull.addFullSem_E_new, addFull.addFullSem_E_new, newRow_mute sem₀ I M P hI hm,
        newRow_mute sem₀ I M P hI hm]

/-! ## Consistency -/

/-- **Every new row respects the tower semantics** on its lower set. -/
theorem respects_new (j : Fin (famCard sem₀ I M P)) :
    RespectsSemanticsBelow (towerSem sem₀ I M P hAk hI hproper) (Tcell (NEW j)) (SE (NEW j)) where
  orderly := (towerSem sem₀ I M P hAk hI hproper).orderly (NEW j)
  locality Sig := by
    obtain ⟨t, hm⟩ : ∃ t, MEM j = t := ⟨_, rfl⟩
    rcases t with m | m | i
    · rcases below_new_cases sem₀ I M P hAk j Sig with ⟨b, hb, rfl⟩ | ⟨j', hj', rfl⟩
      · exact locality_at_old sem₀ I M P hAk hI hproper m.F m.respects
          (level_eq_of_memOf_inl sem₀ I M P hm)
          (fun b' hb' => newRow_one_old sem₀ I M P hI hm b' hb') b hb
      · obtain ⟨t', hm'⟩ : ∃ t', MEM j' = t' := ⟨_, rfl⟩
        rcases t' with m' | m' | i'
        · exact locality_one_one sem₀ I M P hAk hI hproper hm hm' hj'
        · exfalso
          have h1 := level_eq_of_memOf_inl sem₀ I M P hm
          have h2 := level_eq_of_memOf_inr_inl sem₀ I M P hm'
          omega
        · exfalso
          have h1 := level_eq_of_memOf_inl sem₀ I M P hm
          have h2 := level_eq_of_memOf_inr_inr sem₀ I M P hm'
          omega
    · rcases below_new_cases sem₀ I M P hAk j Sig with ⟨b, hb, rfl⟩ | ⟨j', hj', rfl⟩
      · exact locality_at_old sem₀ I M P hAk hI hproper m.F m.respects
          (level_eq_of_memOf_inr_inl sem₀ I M P hm)
          (fun b' hb' => newRow_two_old sem₀ I M P hI hm b' hb') b hb
      · obtain ⟨t', hm'⟩ : ∃ t', MEM j' = t' := ⟨_, rfl⟩
        rcases t' with m' | m' | i'
        · exact locality_two_one sem₀ I M P hAk hI hproper hm hm' hj'
        · exact locality_two_two sem₀ I M P hAk hI hproper hm hm' hj'
        · exfalso
          have h1 := level_eq_of_memOf_inr_inl sem₀ I M P hm
          have h2 := level_eq_of_memOf_inr_inr sem₀ I M P hm'
          omega
    · exact locality_mute sem₀ I M P hAk hI hproper hm Sig
  availability := availability_new sem₀ I M P hAk hI hproper j

/-- **The tower semantics is consistent**, given a consistent base. -/
theorem towerSem_consistent (hcons₀ : sem₀.IsConsistent) :
    (towerSem sem₀ I M P hAk hI hproper).IsConsistent := by
  intro Sig
  rcases addFull.cases (hlevel sem₀ I M P hAk) Sig with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact addFull.respects_old (hlevel sem₀ I M P hAk) hproper sem₀ _ _ hcons₀ i
  · exact respects_new sem₀ I M P hAk hI hproper j

/-! ## Coding -/

omit hAk hproper in
theorem rowOf_isCoded (t : Fam sem₀ I M P) (k : ℕ) (hk : lv sem₀ I M P t = k) (x) :
    IsCodedLabel k (rowOf sem₀ I M P hI t k hk x) := by
  rcases t with m | m | i
  · have hk1 : k = 1 := hk.symm
    subst hk1
    rcases x with b | j'
    · exact m.F_isCoded _
    · change IsCodedLabel 1 (match MEM j'.1 with
        | Sum.inl m' => levelCap 1 I m.F m.γ m'.F m'.γ
        | Sum.inr _ => ⊥)
      rcases MEM j'.1 with m' | m'
      · exact isCodedLabel_of_mem_alph (levelCap_mem _ _ _ _ _ _)
      · exact Or.inl rfl
  · have hk2 : k = 2 := hk.symm
    subst hk2
    rcases x with b | j'
    · exact m.F_isCoded _
    · change IsCodedLabel 2 (match MEM j'.1 with
        | Sum.inl m' => readOne sem₀ I P hI m m'
        | Sum.inr (Sum.inl m') =>
            levelCap 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ
        | Sum.inr (Sum.inr _) => ⊥)
      rcases MEM j'.1 with m' | m' | i'
      · exact m.dec_isCoded _
      · exact isCodedLabel_of_mem_alph (levelCap_mem _ _ _ _ _ _)
      · exact Or.inl rfl
  · exact Or.inl rfl

/-- **The tower semantics is coded**, given a coded base. -/
theorem towerSem_isCoded (hcoded₀ : sem₀.IsCoded) :
    (towerSem sem₀ I M P hAk hI hproper).IsCoded := by
  intro Sig d
  rcases addFull.cases (hlevel sem₀ I M P hAk) Sig with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · rw [addFull.grade_old, E_old sem₀ I M P hAk hI hproper]
    exact hcoded₀ i _
  · rw [addFull.grade_new, addFull.addFullSem_E_new]
    exact rowOf_isCoded sem₀ I M P hI (MEM j) (LV j) rfl _

/-! ## Completeness -/

omit hI hproper in
/-- **The tower is complete**, given a base complete at every proper index and enough mute
levels. -/
theorem tower_complete (m₀ : Member sem₀ I 2 P)
    (hcomp₀ : ∀ BJ ∈ Plan.gradedPlan D₀.plan, BJ.1 ≠ A → ∃ d, D₀.cell d = BJ)
    (hM : ∀ k, 3 ≤ k → k ≤ A.card → k - 3 < M) : (tower sem₀ I M P hAk).IsComplete := by
  intro BJ hBJ
  by_cases hB : BJ.1 = A
  · have h := Plan.mem_gradedPlan.mp hBJ
    have hcard : BJ.2 ≤ A.card := by rw [← hB]; exact h.2.2
    have hpos : 0 < BJ.2 := h.2.1
    rcases Nat.lt_or_ge BJ.2 3 with hk3 | hk3
    · rcases Nat.lt_or_ge BJ.2 2 with hk2 | hk2
      · have hk : BJ.2 = 1 := by omega
        refine ⟨NEW (idx sem₀ I M P (Sum.inl (Member.bot sem₀ I 1))), ?_⟩
        rw [addFull.cell_new, level_idx]
        exact Prod.ext hB.symm hk.symm
      · have hk : BJ.2 = 2 := by omega
        refine ⟨NEW (idx sem₀ I M P (Sum.inr (Sum.inl m₀))), ?_⟩
        rw [addFull.cell_new, level_idx]
        exact Prod.ext hB.symm hk.symm
    · refine ⟨NEW (idx sem₀ I M P (Sum.inr (Sum.inr ⟨BJ.2 - 3, hM BJ.2 hk3 hcard⟩))), ?_⟩
      rw [addFull.cell_new, level_idx]
      refine Prod.ext hB.symm ?_
      change BJ.2 - 3 + 3 = BJ.2
      omega
  · obtain ⟨d, hd⟩ := hcomp₀ BJ hBJ hB
    exact ⟨OLD d, by rw [addFull.cell_old, hd]⟩

end VaughtConjecture.Knight
