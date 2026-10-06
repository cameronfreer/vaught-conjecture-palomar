/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoTower

/-! # Consistency of the two-level tower: the localities

Every new row of the tower (`Knight/GradeTwoTower.lean`) is local at every lower controller,
derived from the actual rows:

* **at an old controller**: the member's base locality, reindexed along the old lower set
  (`locality_at_old`);
* **at a level-one controller from a level-one row**: the identity shifter with the step
  suppressor at the level cap — base cells agree below the cap (`min_eq_of_levelCap`), siblings
  by the capped ultrametric identity (`min_levelCap_eq`) (`locality_one_one`);
* **at a level-one controller from a level-two row**: `Factorization.locality` with the owned
  witness and the decoder — (13) holds by construction (`factor_old`, `factor_new`), (14) is the
  level-one cap identity between the witness and the controller (`locality_two_one`);
* **at a level-two controller from a level-two row**: the identity shifter with the step
  suppressor at the level cap of the full decoded vectors (`locality_two_two`);
* **from a mute row**: the bottom transformation (`locality_mute`).

The availability clauses and the assembly into `towerSem_consistent` follow in
`Knight/GradeTwoAvailability.lean`.

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
/-- A new cell. -/
local notation "NEW" => addFull.new (hlevel sem₀ I M P hAk)
/-- An old cell. -/
local notation "OLD" => addFull.old (hlevel sem₀ I M P hAk)
/-- The lower-set equivalence of a new cell. -/
local notation "BN" => addFull.belowNew (hlevel sem₀ I M P hAk)
/-- The lower-set equivalence of an old cell. -/
local notation "BO" => addFull.belowOld (hlevel sem₀ I M P hAk) hproper
/-- The level of a new cell. -/
local notation "LV" => level sem₀ I M P
/-- The member of a new cell. -/
local notation "MEM" => memOf sem₀ I M P
/-- The row of a new cell. -/
local notation "ROW" => newRow sem₀ I M P hI

/-! ## Evaluating the rows -/

theorem E_new_apply (j : Fin (famCard sem₀ I M P)) (x) : SE (NEW j) (BN j x) = ROW j x :=
  addFull.addFullSem_E_new_apply (hlevel sem₀ I M P hAk) hproper sem₀ _ _ j x

theorem E_new_old (j : Fin (famCard sem₀ I M P)) (b : Cell D₀) (hb : D₀.grade b ≤ LV j) (h) :
    SE (NEW j) ⟨OLD b, h⟩ = ROW j (Sum.inl ⟨b, hb⟩) := by
  have := addFull.addFullSem_E_new (hlevel sem₀ I M P hAk) hproper sem₀ (newRow sem₀ I M P hI)
    (newRow_orderly sem₀ I M P hI) j ⟨OLD b, h⟩
  rw [addFull.belowNew_symm_old (hlevel sem₀ I M P hAk) j b hb h] at this
  exact this

theorem E_new_new (j j' : Fin (famCard sem₀ I M P)) (hj' : LV j' ≤ LV j) (h) :
    SE (NEW j) ⟨NEW j', h⟩ = ROW j (Sum.inr ⟨j', hj'⟩) := by
  have := addFull.addFullSem_E_new (hlevel sem₀ I M P hAk) hproper sem₀ (newRow sem₀ I M P hI)
    (newRow_orderly sem₀ I M P hI) j ⟨NEW j', h⟩
  rw [addFull.belowNew_symm_new (hlevel sem₀ I M P hAk) j j' hj' h] at this
  exact this

theorem E_old (i : Cell D₀) (d) : SE (OLD i) d = sem₀.E i ((BO i).symm d) :=
  addFull.addFullSem_E_old (hlevel sem₀ I M P hAk) hproper sem₀ _ _ i d

omit hI in
theorem grade_old_cell (i : Cell D₀) (d : Tbelow (Tcell (OLD i))) :
    Tgrade d.1 = D₀.grade ((BO i).symm d).1 := by
  conv_lhs => rw [← Equiv.apply_symm_apply (BO i) d]
  rw [addFull.belowOld_val]
  exact addFull.grade_old (hlevel sem₀ I M P hAk) _

omit hI in
theorem val_old_cell (i : Cell D₀) (d : Tbelow (Tcell (OLD i))) :
    d.1 = OLD ((BO i).symm d).1 := by
  conv_lhs => rw [← Equiv.apply_symm_apply (BO i) d]
  rw [addFull.belowOld_val]

/-- The row of a new cell at the inclusion of an old cell below a new controller. -/
theorem E_new_incl_old (j j' : Fin (famCard sem₀ I M P)) (hj' : LV j' ≤ LV j) (b : Cell D₀)
    (hb : D₀.grade b ≤ LV j') :
    SE (NEW j) (CellScheme.below.incl (BN j (Sum.inr ⟨j', hj'⟩)) (BN j' (Sum.inl ⟨b, hb⟩))) =
      ROW j (Sum.inl ⟨b, hb.trans hj'⟩) :=
  E_new_old sem₀ I M P hAk hI hproper j b (hb.trans hj') _

/-- The row of a new cell at the inclusion of a new cell below a new controller. -/
theorem E_new_incl_new (j j' j'' : Fin (famCard sem₀ I M P)) (hj' : LV j' ≤ LV j)
    (hj'' : LV j'' ≤ LV j') :
    SE (NEW j) (CellScheme.below.incl (BN j (Sum.inr ⟨j', hj'⟩)) (BN j' (Sum.inr ⟨j'', hj''⟩))) =
      ROW j (Sum.inr ⟨j'', hj''.trans hj'⟩) :=
  E_new_new sem₀ I M P hAk hI hproper j j'' (hj''.trans hj') _

omit hI hproper in
theorem grade_belowNew_old (j : Fin (famCard sem₀ I M P)) (b : Cell D₀) (hb : D₀.grade b ≤ LV j) :
    Tgrade (BN j (Sum.inl ⟨b, hb⟩)).1 = D₀.grade b := by
  rw [addFull.belowNew_inl]; exact addFull.grade_old _ b

omit hI hproper in
theorem grade_belowNew_new (j j' : Fin (famCard sem₀ I M P)) (hj' : LV j' ≤ LV j) :
    Tgrade (BN j (Sum.inr ⟨j', hj'⟩)).1 = LV j' := by
  rw [addFull.belowNew_inr]; exact addFull.grade_new _ j'

omit hI hproper in
/-- A cell of the lower set of a new cell is an old cell or a new cell of no larger level. -/
theorem below_new_cases (j : Fin (famCard sem₀ I M P)) (Sig : Tbelow (Tcell (NEW j))) :
    (∃ (b : Cell D₀) (hb : D₀.grade b ≤ LV j), Sig = BN j (Sum.inl ⟨b, hb⟩)) ∨
    ∃ (j' : Fin (famCard sem₀ I M P)) (hj' : LV j' ≤ LV j), Sig = BN j (Sum.inr ⟨j', hj'⟩) := by
  obtain ⟨x, rfl⟩ := (BN j).surjective Sig
  rcases x with ⟨b, hb⟩ | ⟨j', hj'⟩
  · exact Or.inl ⟨b, hb, rfl⟩
  · exact Or.inr ⟨j', hj', rfl⟩

/-! ## Rows evaluated on identified members -/

omit hAk hproper in
theorem newRow_one_old {j : Fin (famCard sem₀ I M P)} {m : Member₁ sem₀ I} (hm : MEM j = Sum.inl m)
    (b : Cell D₀) (hb : D₀.grade b ≤ LV j) :
    ROW j (Sum.inl ⟨b, hb⟩) = m.F ⟨b, hb.trans_eq (level_eq_of_memOf_inl sem₀ I M P hm)⟩ := by
  rw [newRow_eq sem₀ I M P hI hm]; rfl

omit hAk hproper in
theorem newRow_two_old {j : Fin (famCard sem₀ I M P)} {m : Member sem₀ I 2 P}
    (hm : MEM j = Sum.inr (Sum.inl m)) (b : Cell D₀) (hb : D₀.grade b ≤ LV j) :
    ROW j (Sum.inl ⟨b, hb⟩) = m.F ⟨b, hb.trans_eq (level_eq_of_memOf_inr_inl sem₀ I M P hm)⟩ := by
  rw [newRow_eq sem₀ I M P hI hm]; rfl

omit hAk hproper in
theorem newRow_one_new {j : Fin (famCard sem₀ I M P)} {m : Member₁ sem₀ I} (hm : MEM j = Sum.inl m)
    (j' : Fin (famCard sem₀ I M P)) (hj' : LV j' ≤ LV j) :
    ROW j (Sum.inr ⟨j', hj'⟩) =
      match MEM j' with
      | Sum.inl m' => levelCap 1 I m.F m.γ m'.F m'.γ
      | Sum.inr _ => ⊥ := by
  rw [newRow_eq sem₀ I M P hI hm]; rfl

omit hAk hproper in
theorem newRow_two_new {j : Fin (famCard sem₀ I M P)} {m : Member sem₀ I 2 P}
    (hm : MEM j = Sum.inr (Sum.inl m)) (j' : Fin (famCard sem₀ I M P)) (hj' : LV j' ≤ LV j) :
    ROW j (Sum.inr ⟨j', hj'⟩) =
      match MEM j' with
      | Sum.inl m' => readOne sem₀ I P hI m m'
      | Sum.inr (Sum.inl m') =>
          levelCap 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ
      | Sum.inr (Sum.inr _) => ⊥ := by
  rw [newRow_eq sem₀ I M P hI hm]; rfl

omit hAk hproper in
theorem newRow_mute {j : Fin (famCard sem₀ I M P)} {i : Fin M} (hm : MEM j = Sum.inr (Sum.inr i))
    (x) : ROW j x = ⊥ := by
  rw [newRow_eq sem₀ I M P hI hm]
  rcases x with _ | _ <;> rfl

/-! ## Locality at an old controller -/

/-- **Locality of a new row at an old controller**, from the member's base locality. -/
theorem locality_at_old {j : Fin (famCard sem₀ I M P)} {k : ℕ} (F : BaseCells D₀ k → ExtOrd)
    (hF : RespectsBase sem₀ k F) (hk : LV j = k)
    (hrow : ∀ (b' : Cell D₀) (hb' : D₀.grade b' ≤ LV j),
      ROW j (Sum.inl ⟨b', hb'⟩) = F ⟨b', hb'.trans_eq hk⟩)
    (b : Cell D₀) (hb : D₀.grade b ≤ LV j) :
    TransformsTo (fun d : Tbelow (Tcell (OLD b)) => Tgrade d.1) (SE (OLD b))
      (fun d => min (SE (NEW j) (CellScheme.below.incl (BN j (Sum.inl ⟨b, hb⟩)) d))
        (SE (NEW j) (BN j (Sum.inl ⟨b, hb⟩)))) := by
  set e := BO b with he
  have loc := (hF.locality ⟨b, hb.trans_eq hk⟩).reindex e.symm
  convert loc using 1
  · funext d
    exact grade_old_cell sem₀ I M P hAk hproper b d
  · funext d
    exact E_old sem₀ I M P hAk hI hproper b d
  · funext d
    simp only [Function.comp]
    have h1 : SE (NEW j) (BN j (Sum.inl ⟨b, hb⟩)) = F ⟨b, hb.trans_eq hk⟩ := by
      rw [E_new_apply]
      exact hrow b hb
    have hgr : D₀.grade (e.symm d).1 ≤ LV j :=
      ((e.symm d).2.2 : D₀.grade (e.symm d).1 ≤ D₀.grade b).trans hb
    have hd : SE (NEW j) (CellScheme.below.incl (BN j (Sum.inl ⟨b, hb⟩)) d) =
        F ⟨(e.symm d).1, hgr.trans_eq hk⟩ := by
      have hval : CellScheme.below.incl (BN j (Sum.inl ⟨b, hb⟩)) d =
          ⟨OLD (e.symm d).1, by
            rw [← val_old_cell sem₀ I M P hAk hproper b d]
            exact (CellScheme.below.incl (BN j (Sum.inl ⟨b, hb⟩)) d).2⟩ :=
        Subtype.ext (val_old_cell sem₀ I M P hAk hproper b d)
      rw [hval, E_new_old sem₀ I M P hAk hI hproper j _ hgr, hrow _ hgr]
    rw [h1, hd]

/-! ## Locality at a level-one controller, from a level-one row -/

/-- **Sibling locality at level one**: the identity shifter with the step suppressor at the level
cap. -/
theorem locality_one_one {j : Fin (famCard sem₀ I M P)} {m : Member₁ sem₀ I}
    (hm : MEM j = Sum.inl m) {j' : Fin (famCard sem₀ I M P)} {m' : Member₁ sem₀ I}
    (hm' : MEM j' = Sum.inl m')
    (hj' : LV j' ≤ LV j) :
    TransformsTo (fun d : Tbelow (Tcell (NEW j')) => Tgrade d.1) (SE (NEW j'))
      (fun d => min (SE (NEW j) (CellScheme.below.incl (BN j (Sum.inr ⟨j', hj'⟩)) d))
        (SE (NEW j) (BN j (Sum.inr ⟨j', hj'⟩)))) := by
  have hl1' := level_eq_of_memOf_inl sem₀ I M P hm'
  set e := levelCap 1 I m.F m.γ m'.F m'.γ with he
  have hSig : SE (NEW j) (BN j (Sum.inr ⟨j', hj'⟩)) = e := by
    rw [E_new_apply, newRow_one_new sem₀ I M P hI hm, hm']
  refine ⟨stepSuppressor 1 e, id, fun n m hnm => stepSuppressor_anti _ _ hnm,
    fun n => (stepSuppressor_selfVis (levelCap_selfVis _ _ _ _ _ _) n).symm, rfl, monotone_id,
    fun _ _ _ _ _ => rfl, fun d => ?_⟩
  dsimp only
  rw [hSig]
  rcases below_new_cases sem₀ I M P hAk j' d with ⟨b, hb, rfl⟩ | ⟨j'', hj'', rfl⟩
  · have h1 := E_new_incl_old sem₀ I M P hAk hI hproper j j' hj' b hb
    rw [newRow_one_old sem₀ I M P hI hm] at h1
    have h2 := E_new_apply sem₀ I M P hAk hI hproper j' (Sum.inl ⟨b, hb⟩)
    rw [newRow_one_old sem₀ I M P hI hm'] at h2
    rw [h1, h2, grade_belowNew_old sem₀ I M P hAk, stepSuppressor_of_le (hb.trans hl1'.le)]
    exact min_eq_of_levelCap 1 I m.F m.γ m'.F m'.γ _
  · have h1 := E_new_incl_new sem₀ I M P hAk hI hproper j j' j'' hj' hj''
    rw [newRow_one_new sem₀ I M P hI hm] at h1
    have h2 := E_new_apply sem₀ I M P hAk hI hproper j' (Sum.inr ⟨j'', hj''⟩)
    rw [newRow_one_new sem₀ I M P hI hm'] at h2
    rw [h1, h2, grade_belowNew_new sem₀ I M P hAk, stepSuppressor_of_le (hj''.trans hl1'.le)]
    rcases hm'' : MEM j'' with m'' | m''
    · exact min_levelCap_eq 1 I m.F m.γ m'.F m'.γ m''.F m''.γ
    · simp

/-! ## Locality at a level-one controller, from a level-two row -/

omit hproper in
/-- The owned witness of a level-two member as a cell of the lower set of that member's cell. -/
noncomputable def witnessCell {j : Fin (famCard sem₀ I M P)} {m : Member sem₀ I 2 P}
    (hm : MEM j = Sum.inr (Sum.inl m)) : Tbelow (Tcell (NEW j)) :=
  BN j (Sum.inr ⟨idx sem₀ I M P (Sum.inl (m.witness hI)), by
    rw [level_idx, level_eq_of_memOf_inr_inl sem₀ I M P hm]; exact one_le_two⟩)

omit hAk hproper in
theorem memOf_witness (m : Member sem₀ I 2 P) :
    MEM (idx sem₀ I M P (Sum.inl (m.witness hI))) = Sum.inl (m.witness hI) :=
  memOf_idx _ _ _ _ _

omit hAk hproper in
theorem level_witness (m : Member sem₀ I 2 P) : LV (idx sem₀ I M P (Sum.inl (m.witness hI))) = 1 :=
  level_idx _ _ _ _ _

omit hproper in
theorem cell_witnessCell {j : Fin (famCard sem₀ I M P)} {m : Member sem₀ I 2 P}
    (hm : MEM j = Sum.inr (Sum.inl m)) :
    Tcell (witnessCell sem₀ I M P hAk hI hm).1 = ((Tcell (NEW j)).1, 1) := by
  unfold witnessCell
  rw [addFull.belowNew_inr, addFull.cell_new, addFull.cell_new, level_witness sem₀ I M P hI m]

/-- The witness row at an old cell below the controller. -/
theorem witness_at_old (m : Member sem₀ I 2 P) (b : Cell D₀) (hb1 : D₀.grade b ≤ 1) (h) :
    SE (NEW (idx sem₀ I M P (Sum.inl (m.witness hI)))) ⟨OLD b, h⟩ = (m.witness hI).F ⟨b, hb1⟩ := by
  have := E_new_old sem₀ I M P hAk hI hproper (idx sem₀ I M P (Sum.inl (m.witness hI))) b
    (by rw [level_witness sem₀ I M P hI m]; exact hb1) h
  rw [newRow_one_old sem₀ I M P hI (memOf_witness sem₀ I M P hI m)] at this
  exact this

/-- The witness row at a level-one cell below the controller. -/
theorem witness_at_new (m : Member sem₀ I 2 P) (j'' : Fin (famCard sem₀ I M P)) (hj1 : LV j'' ≤ 1)
    (h) :
    SE (NEW (idx sem₀ I M P (Sum.inl (m.witness hI)))) ⟨NEW j'', h⟩ =
      match MEM j'' with
      | Sum.inl m'' => levelCap 1 I (m.witness hI).F (m.witness hI).γ m''.F m''.γ
      | Sum.inr _ => ⊥ := by
  have := E_new_new sem₀ I M P hAk hI hproper (idx sem₀ I M P (Sum.inl (m.witness hI))) j''
    (by rw [level_witness sem₀ I M P hI m]; exact hj1) h
  rw [newRow_one_new sem₀ I M P hI (memOf_witness sem₀ I M P hI m)] at this
  exact this

/-- The witness row at the controller: the level-one cap of the witness and the controller. -/
theorem witness_at_controller (m : Member sem₀ I 2 P) {j' : Fin (famCard sem₀ I M P)}
    {m' : Member₁ sem₀ I} (hm' : MEM j' = Sum.inl m') (h) :
    SE (NEW (idx sem₀ I M P (Sum.inl (m.witness hI)))) ⟨NEW j', h⟩ =
      levelCap 1 I (m.witness hI).F (m.witness hI).γ m'.F m'.γ := by
  rw [witness_at_new sem₀ I M P hAk hI hproper m j' (level_eq_of_memOf_inl sem₀ I M P hm').le h,
    hm']

/-- **(13) at an old cell**: the level-two row is the decoded witness row. -/
theorem factor_old {j : Fin (famCard sem₀ I M P)} {m : Member sem₀ I 2 P}
    (hm : MEM j = Sum.inr (Sum.inl m)) (b : Cell D₀) (hb : D₀.grade b ≤ LV j)
    (hb1 : D₀.grade b ≤ 1) (h) :
    SE (NEW j) (BN j (Sum.inl ⟨b, hb⟩)) =
      m.dec (SE (NEW (idx sem₀ I M P (Sum.inl (m.witness hI)))) ⟨OLD b, h⟩) := by
  rw [witness_at_old sem₀ I M P hAk hI hproper m b hb1, E_new_apply,
    newRow_two_old sem₀ I M P hI hm, Member.dec_witness]
  rfl

/-- **(13) at a level-one cell**: the level-two row is the decoded witness row. -/
theorem factor_new {j : Fin (famCard sem₀ I M P)} {m : Member sem₀ I 2 P}
    (hm : MEM j = Sum.inr (Sum.inl m)) (j'' : Fin (famCard sem₀ I M P)) (hj'' : LV j'' ≤ LV j)
    (hj1 : LV j'' ≤ 1) (h) :
    SE (NEW j) (BN j (Sum.inr ⟨j'', hj''⟩)) =
      m.dec (SE (NEW (idx sem₀ I M P (Sum.inl (m.witness hI)))) ⟨NEW j'', h⟩) := by
  rw [witness_at_new sem₀ I M P hAk hI hproper m j'' hj1, E_new_apply,
    newRow_two_new sem₀ I M P hI hm]
  rcases hm'' : MEM j'' with m'' | m'' | i''
  · rfl
  · exfalso
    have := level_eq_of_memOf_inr_inl sem₀ I M P hm''
    omega
  · simp only
    unfold Member.dec
    rw [shift_bot]

/-- **The factorization of a level-two row at a level-one controller.** -/
noncomputable def factorization {j : Fin (famCard sem₀ I M P)} {m : Member sem₀ I 2 P}
    (hm : MEM j = Sum.inr (Sum.inl m)) {j' : Fin (famCard sem₀ I M P)} {m' : Member₁ sem₀ I}
    (hm' : MEM j' = Sum.inl m') (hj' : LV j' ≤ LV j) :
    Factorization (towerSem sem₀ I M P hAk hI hproper) (NEW j) (BN j (Sum.inr ⟨j', hj'⟩)) where
  j := 1
  grade_y := by rw [grade_belowNew_new sem₀ I M P hAk]; exact level_eq_of_memOf_inl sem₀ I M P hm'
  w := witnessCell sem₀ I M P hAk hI hm
  cell_w := cell_witnessCell sem₀ I M P hAk hI hm
  Dec := m.decoder _
  factor z hz := by
    rw [Member.decoder_toFun]
    rcases below_new_cases sem₀ I M P hAk j z with ⟨b, hb, rfl⟩ | ⟨j'', hj'', rfl⟩
    · exact factor_old sem₀ I M P hAk hI hproper hm b hb
        (by rw [grade_belowNew_old sem₀ I M P hAk] at hz; exact hz) _
    · exact factor_new sem₀ I M P hAk hI hproper hm j'' hj''
        (by rw [grade_belowNew_new sem₀ I M P hAk] at hz; exact hz) _
  meet z := by
    have hl1' := level_eq_of_memOf_inl sem₀ I M P hm'
    have ha := witness_at_controller sem₀ I M P hAk hI hproper m hm'
      (toWitness (cell_witnessCell sem₀ I M P hAk hI hm) (BN j (Sum.inr ⟨j', hj'⟩))
        (by rw [grade_belowNew_new sem₀ I M P hAk]; exact hl1'.le)).2
    rcases below_new_cases sem₀ I M P hAk j' z with ⟨b, hb, rfl⟩ | ⟨j'', hj'', rfl⟩
    · have hX := witness_at_old sem₀ I M P hAk hI hproper m b (hb.trans hl1'.le)
        (toWitness (cell_witnessCell sem₀ I M P hAk hI hm)
          (CellScheme.below.incl (BN j (Sum.inr ⟨j', hj'⟩)) (BN j' (Sum.inl ⟨b, hb⟩)))
          ((grade_belowNew_old sem₀ I M P hAk j' b hb).trans_le (hb.trans hl1'.le))).2
      have hY := E_new_apply sem₀ I M P hAk hI hproper j' (Sum.inl ⟨b, hb⟩)
      rw [newRow_one_old sem₀ I M P hI hm'] at hY
      exact (congrArg₂ min hX ha).trans
        ((min_eq_of_levelCap 1 I (m.witness hI).F (m.witness hI).γ m'.F m'.γ
          ⟨b, hb.trans hl1'.le⟩).trans (congrArg₂ min hY ha).symm)
    · have hX := witness_at_new sem₀ I M P hAk hI hproper m j'' (hj''.trans hl1'.le)
        (toWitness (cell_witnessCell sem₀ I M P hAk hI hm)
          (CellScheme.below.incl (BN j (Sum.inr ⟨j', hj'⟩)) (BN j' (Sum.inr ⟨j'', hj''⟩)))
          ((grade_belowNew_new sem₀ I M P hAk j' j'' hj'').trans_le (hj''.trans hl1'.le))).2
      have hY := E_new_apply sem₀ I M P hAk hI hproper j' (Sum.inr ⟨j'', hj''⟩)
      rw [newRow_one_new sem₀ I M P hI hm'] at hY
      rcases hm'' : MEM j'' with m'' | m''
      · rw [hm''] at hX hY
        dsimp only at hX hY
        exact (congrArg₂ min hX ha).trans
          ((min_levelCap_eq 1 I (m.witness hI).F (m.witness hI).γ m'.F m'.γ m''.F m''.γ).trans
            (congrArg₂ min hY ha).symm)
      · rw [hm''] at hX hY
        dsimp only at hX hY
        exact (congrArg₂ min hX ha).trans (congrArg₂ min hY ha).symm

/-- **Locality of a level-two row at a level-one controller**, by factorization. -/
theorem locality_two_one {j : Fin (famCard sem₀ I M P)} {m : Member sem₀ I 2 P}
    (hm : MEM j = Sum.inr (Sum.inl m)) {j' : Fin (famCard sem₀ I M P)} {m' : Member₁ sem₀ I}
    (hm' : MEM j' = Sum.inl m') (hj' : LV j' ≤ LV j) :
    TransformsTo (fun d : Tbelow (Tcell (NEW j')) => Tgrade d.1) (SE (NEW j'))
      (fun d => min (SE (NEW j) (CellScheme.below.incl (BN j (Sum.inr ⟨j', hj'⟩)) d))
        (SE (NEW j) (BN j (Sum.inr ⟨j', hj'⟩)))) :=
  (factorization sem₀ I M P hAk hI hproper hm hm' hj').locality

/-! ## Locality at a level-two controller, from a level-two row -/

/-- **Sibling locality at level two**: the identity shifter with the step suppressor at the level
cap of the full decoded vectors. -/
theorem locality_two_two {j : Fin (famCard sem₀ I M P)} {m : Member sem₀ I 2 P}
    (hm : MEM j = Sum.inr (Sum.inl m)) {j' : Fin (famCard sem₀ I M P)} {m' : Member sem₀ I 2 P}
    (hm' : MEM j' = Sum.inr (Sum.inl m')) (hj' : LV j' ≤ LV j) :
    TransformsTo (fun d : Tbelow (Tcell (NEW j')) => Tgrade d.1) (SE (NEW j'))
      (fun d => min (SE (NEW j) (CellScheme.below.incl (BN j (Sum.inr ⟨j', hj'⟩)) d))
        (SE (NEW j) (BN j (Sum.inr ⟨j', hj'⟩)))) := by
  have hl2' := level_eq_of_memOf_inr_inl sem₀ I M P hm'
  set e := levelCap 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ with he
  have hSig : SE (NEW j) (BN j (Sum.inr ⟨j', hj'⟩)) = e := by
    rw [E_new_apply, newRow_two_new sem₀ I M P hI hm, hm']
  refine ⟨stepSuppressor 2 e, id, fun n m hnm => stepSuppressor_anti _ _ hnm,
    fun n => (stepSuppressor_selfVis (levelCap_selfVis _ _ _ _ _ _) n).symm, rfl, monotone_id,
    fun _ _ _ _ _ => rfl, fun d => ?_⟩
  dsimp only
  rw [hSig]
  rcases below_new_cases sem₀ I M P hAk j' d with ⟨b, hb, rfl⟩ | ⟨j'', hj'', rfl⟩
  · have h1 := E_new_incl_old sem₀ I M P hAk hI hproper j j' hj' b hb
    rw [newRow_two_old sem₀ I M P hI hm] at h1
    have h2 := E_new_apply sem₀ I M P hAk hI hproper j' (Sum.inl ⟨b, hb⟩)
    rw [newRow_two_old sem₀ I M P hI hm'] at h2
    rw [h1, h2, grade_belowNew_old sem₀ I M P hAk, stepSuppressor_of_le (hb.trans hl2'.le)]
    exact min_eq_of_levelCap 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ
      (Sum.inl ⟨b, hb.trans hl2'.le⟩)
  · have h1 := E_new_incl_new sem₀ I M P hAk hI hproper j j' j'' hj' hj''
    rw [newRow_two_new sem₀ I M P hI hm] at h1
    have h2 := E_new_apply sem₀ I M P hAk hI hproper j' (Sum.inr ⟨j'', hj''⟩)
    rw [newRow_two_new sem₀ I M P hI hm'] at h2
    rw [h1, h2, grade_belowNew_new sem₀ I M P hAk, stepSuppressor_of_le (hj''.trans hl2'.le)]
    rcases hm'' : MEM j'' with m'' | m'' | i''
    · exact min_eq_of_levelCap 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ
        (Sum.inr m'')
    · exact min_levelCap_eq 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ
        (fullVec sem₀ I P hI m'') m''.γ
    · simp

/-! ## Locality from a mute row -/

theorem locality_mute {j : Fin (famCard sem₀ I M P)} {i : Fin M} (hm : MEM j = Sum.inr (Sum.inr i))
    (Sig : Tbelow (Tcell (NEW j))) :
    TransformsTo (fun d : Tbelow (Tcell Sig.1) => Tgrade d.1) (SE Sig.1)
      (fun d => min (SE (NEW j) (CellScheme.below.incl Sig d)) (SE (NEW j) Sig)) := by
  have hrow : ∀ d, SE (NEW j) d = ⊥ := by
    intro d
    rw [addFull.addFullSem_E_new, newRow_mute sem₀ I M P hI hm]
  refine ⟨fun _ => ⊤, fun _ => ⊥, fun _ _ _ => le_refl ⊤, fun _ => rfl, rfl, monotone_const,
    fun _ _ _ _ _ => (extVisibilityReplace_bot _ _).symm, fun d => ?_⟩
  simp [hrow]

end VaughtConjecture.Knight
