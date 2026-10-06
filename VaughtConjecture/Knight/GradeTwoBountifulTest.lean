/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoForcing

/-! # The two-level tower: the literal bountifulness clause, tested

The literal clause (Knight, Def. 2.5.14, `Semantics.IsBountiful`) at the proper-to-full pair
`⟨C,2⟩ ≺ ⟨A,2⟩`: a *prescribed* labelling `p` of `D⟨C,2⟩` respecting `E⟨C,2⟩`, an *ambient*
labelling `q` of `D⟨A,2⟩` respecting `E⟨A,2⟩`, a cap `γ` self-visible at grade two, and capped
agreement `(q ∧ γ) ↾ D⟨C,2⟩ = p ∧ γ`; required: `q'` on `D⟨A,2⟩` respecting `E⟨A,2⟩` with
`q' ∧ γ = q ∧ γ` and `q' ↾ D⟨C,2⟩ = p`.  On the tower, `D⟨C,2⟩` consists of base cells only
(`properCell`; the new cells have scope `A ≠ C`), and `D⟨A,2⟩` of the base cells of grade `≤ 2`,
the level-one cells and the level-two cells.  Nothing here demands that any particular controller
be activated: the controller is free to change.

**A genuine counterexample, at cap `⊥`** (`not_bountiful_of_incorrect_proper`).  On a tower whose
level-two family is cutoff-correct for the reference cells `(c, ρ, q)` lying under `C`, suppose
the base admits a lawful labelling `p` of `D⟨C,2⟩` carrying the reference — `p ρ = β + j`,
`β ≤ p c`, `p ρ ≤ p c` — with an *incorrect* request, `truncExt β (p q) ≠ ⊤`.  Then the clause
fails at `(⟨C,2⟩, ⟨A,2⟩, γ = ⊥)`: capped agreement is vacuous, so any lift `q'` extends `p`
literally; `q'` extended by `⊥` above grade two respects the tower; and the forcing through the
availability witness actually used (`tower_readback_of_availability`) reads the request at least
`β` — contradicting `p`.  The required activation is *derived* from the clause's premises
(availability of `q'` at the cap toward `⟨A,2⟩`), not assumed.  Consequently the correctness
thinning is bountiful only over a base that already forces correctness at every proper scope
containing the reference — the situation of the paper's inductive construction, where the base at
`⟨C,2⟩` is itself a forced tower over `C`.

**The lift at cap `⊥`** (`lift_of_member_extends`): whenever `p` extends to a *retained* member
`m` — `m.F = p` on the base cells under `C` — the member's row `memberRow m` is a lift (respect by
consistency; literal restriction by `memberRow_old`).  With the correct thinning this is exactly
the obligation that the counterexample shows can fail: the extension must be correct.

**The lift by controller change at a member's cap** (`lift_of_agreeing_member`).  Take the ambient
to be the row of a retained member `m` and the cap its own cap `m.γ` (self-visible, in the
alphabet).  If some retained member `m'` extends `p` literally and **agrees with `m` under `m`'s
cap** — `levelCap m m' = m.γ`, equivalently `m.γ ≤ agreeCap (fullVec m) (fullVec m')` and
`m.γ ≤ m'.γ` (`levelCap_eq_left_of`) — then `memberRow m'` is a lift: capped agreement holds at
every base cell and every level-one cell by the full-vector agreement
(`memberRow_agree_of_levelCap`), and at every level-two sibling by the capped ultrametric
identity `min_levelCap_eq` — the controller changes from `m` to `m'`, and every sibling's
capped reading is preserved.  The controller freedom that repaired the forcing is what makes this
lift possible: activating the designated `m` instead is exactly what the designated-display
obstruction of `Knight/GradeTwoForcing.lean` rules out.

**What remains open.**  (1) The existence of the retained member `m'` — an alphabet-valued,
correct extension of `p` to all base cells of grade `≤ 2` agreeing with the ambient's controller
under its cap — is a base-level extension obligation, not supplied here.  (2) Ambient labellings
that are not member rows: their controllers activated above the cap must be replaced by
controllers compatible with `p`, subject to the ambient's readings of the replacement cells under
the cap.  (3) Bountifulness at the other graded pairs.  None of these is claimed.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}

/-- A proper graded index at grade two lies below the full index. -/
theorem gradedLe_full_two {C : Finset ι} (hC : (C, 2) ∈ Plan.gradedPlan D₀.plan) :
    GradedLe (C, 2) (A, 2) :=
  ⟨D₀.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hC).1, le_rfl⟩

/-- The level cap of a pair is the first cap when the second member agrees with the first under
that cap and has at least that cap. -/
theorem levelCap_eq_left_of {Z : Type*} [Fintype Z] {I : ℕ} {F G : Z → ExtOrd} {γ δ : ExtOrd}
    (hγ : γ ∈ alph 2 I) (hs : SelfVis 2 γ) (hag : γ ≤ agreeCap F G) (hδ : γ ≤ δ) :
    levelCap 2 I F γ G δ = γ := by
  unfold levelCap
  rw [min_eq_left hδ, min_eq_right hag, roundDown_eq_self hγ hs]

/-! ## The tower -/

variable (sem₀ : Semantics D₀) (I M : ℕ) (P : (BaseCells D₀ 2 → ExtOrd) → Prop)
  (hAk : ∀ k, 1 ≤ k → k ≤ M + 2 → (A, k) ∈ Plan.gradedPlan D₀.plan)
  (hI : Fintype.card (Cell D₀) + 2 ≤ I) (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A)

include sem₀ I M P hAk hI hproper

/-- The tower semantics' rows. -/
local notation "SE" => Semantics.E (towerSem sem₀ I M P hAk hI hproper)
/-- The tower's lower sets. -/
local notation "Tbelow" => CellScheme.below (tower sem₀ I M P hAk)
/-- The tower's graded indices. -/
local notation "Tcell" => CellScheme.cell (tower sem₀ I M P hAk)
/-- A new cell. -/
local notation "NEW" => addFull.new (hlevel sem₀ I M P hAk)
/-- An old cell. -/
local notation "OLD" => addFull.old (hlevel sem₀ I M P hAk)
/-- The member of a new cell. -/
local notation "MEM" => memOf sem₀ I M P
/-- The member row of a level-two member. -/
local notation "MROW" => memberRow sem₀ I M P hAk hI hproper

omit hI hproper in
/-- A base cell of scope within `C` and grade `≤ 2` as a cell of the tower's lower set `D⟨C,2⟩`. -/
noncomputable def properCell (C : Finset ι) (b : Cell D₀) (hb : D₀.scope b ⊆ C)
    (hg : D₀.grade b ≤ 2) : Tbelow (C, 2) :=
  ⟨OLD b, by
    rw [addFull.cell_old]
    exact ⟨hb, hg⟩⟩

/-- The member row at an old cell is the member's label. -/
theorem memberRow_old (m : Member sem₀ I 2 P) (b : Cell D₀) (hg : D₀.grade b ≤ 2)
    (h : GradedLe (Tcell (OLD b)) (A, 2)) : MROW m ⟨OLD b, h⟩ = m.F ⟨b, hg⟩ := by
  unfold memberRow memberCell
  refine (E_new_old sem₀ I M P hAk hI hproper _ b (by rw [level_idx]; exact hg) _).trans ?_
  exact newRow_two_old sem₀ I M P hI (memOf_memberCell sem₀ I M P m) b _

/-- The member row at a new cell of level `≤ 2`, by the member of that cell. -/
theorem memberRow_new (m : Member sem₀ I 2 P) (j : Fin (famCard sem₀ I M P))
    (hj : level sem₀ I M P j ≤ 2) (h : GradedLe (Tcell (NEW j)) (A, 2)) :
    MROW m ⟨NEW j, h⟩ =
      match MEM j with
      | Sum.inl m' => readOne sem₀ I P hI m m'
      | Sum.inr (Sum.inl m') =>
          levelCap 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ
      | Sum.inr (Sum.inr _) => ⊥ := by
  have hj' : level sem₀ I M P j ≤ level sem₀ I M P (idx sem₀ I M P (Sum.inr (Sum.inl m))) := by
    rw [level_idx]; exact hj
  unfold memberRow memberCell
  refine (E_new_new sem₀ I M P hAk hI hproper _ j hj' _).trans ?_
  exact newRow_two_new sem₀ I M P hI (memOf_memberCell sem₀ I M P m) j hj'

/-- **Literal restriction**: a member extending the prescribed labelling on the base cells under
`C` has its row restrict to `p` on `D⟨C,2⟩`. -/
theorem memberRow_restrict (C : Finset ι) (hC : (C, 2) ∈ Plan.gradedPlan D₀.plan) (hCA : C ≠ A)
    (p : Tbelow (C, 2) → ExtOrd) (m : Member sem₀ I 2 P)
    (hm : ∀ (b : Cell D₀) (hb : D₀.scope b ⊆ C) (hg : D₀.grade b ≤ 2),
      m.F ⟨b, hg⟩ = p (properCell sem₀ I M P hAk C b hb hg))
    (d : Tbelow (C, 2)) : MROW m (CellScheme.below.mono (gradedLe_full_two hC) d) = p d := by
  obtain ⟨x, hx⟩ := d
  rcases addFull.cases (hlevel sem₀ I M P hAk) x with ⟨b, rfl⟩ | ⟨j, rfl⟩
  · have hx' : GradedLe (D₀.cell b) (C, 2) := by rw [addFull.cell_old] at hx; exact hx
    have hb : D₀.scope b ⊆ C := hx'.1
    have hg : D₀.grade b ≤ 2 := hx'.2
    change MROW m (CellScheme.below.mono (gradedLe_full_two hC)
      (properCell sem₀ I M P hAk C b hb hg)) = p (properCell sem₀ I M P hAk C b hb hg)
    rw [← hm b hb hg]
    exact memberRow_old sem₀ I M P hAk hI hproper m b hg _
  · exfalso
    have hx' : GradedLe (A, level sem₀ I M P j) (C, 2) := by rw [addFull.cell_new] at hx; exact hx
    exact hCA (Finset.Subset.antisymm (D₀.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hC).1)
      hx'.1)

/-! ## A genuine counterexample at cap `⊥` -/

/-- **The correct thinning is not bountiful over a base admitting an incorrect lawful proper
labelling.**  If a lawful labelling `p` of `D⟨C,2⟩` carries the reference `β + j` at `ρ` under a
cap at `c` at least `β` but reads the request `q` below the cut, then the literal clause fails at
`(⟨C,2⟩, ⟨A,2⟩, ⊥)`: any lift extends `p` literally and, extended by `⊥` above grade two, is a
respecting labelling of the tower, whose availability at the cap activates some correct member —
forcing the request at least `β`. -/
theorem not_bountiful_of_incorrect_proper (c ρ q : Cell D₀) (hc : D₀.grade c = 2)
    (hρ : D₀.grade ρ ≤ 2) (hq : D₀.grade q ≤ 2) (hP : ∀ F, P F → CutoffCorrect c ρ q hc.le hρ hq F)
    (m₀ : Member sem₀ I 2 P) (C : Finset ι) (hC : (C, 2) ∈ Plan.gradedPlan D₀.plan) (hCA : C ≠ A)
    (hcC : D₀.scope c ⊆ C) (hρC : D₀.scope ρ ⊆ C) (hqC : D₀.scope q ⊆ C) {β : Ordinal.{0}}
    (hβ : limitPart β = β) {j : ℕ} (hj : j < 2) (p : Tbelow (C, 2) → ExtOrd)
    (hp : RespectsSemanticsBelow (towerSem sem₀ I M P hAk hI hproper) (C, 2) p)
    (hpρ : p (properCell sem₀ I M P hAk C ρ hρC hρ) = ofOrd (β + j))
    (hpc : ofOrd β ≤ p (properCell sem₀ I M P hAk C c hcC hc.le))
    (hρc : p (properCell sem₀ I M P hAk C ρ hρC hρ) ≤ p (properCell sem₀ I M P hAk C c hcC hc.le))
    (hpq : truncExt β (p (properCell sem₀ I M P hAk C q hqC hq)) ≠ ⊤) :
    ¬ (towerSem sem₀ I M P hAk hI hproper).IsBountiful := by
  intro hB
  have h := gradedLe_full_two (D₀ := D₀) hC
  obtain ⟨q', hq', -, hres⟩ := hB (C, 2) (A, 2) hC (hAk 2 (by omega) (by omega)) h
    (fun e => hCA (congrArg Prod.fst e)) p (MROW m₀) ⊥ hp
    (memberRow_respects sem₀ I M P hAk hI hproper m₀) (extVisibilityReplace_bot _ _)
    (fun d => by rw [min_eq_right bot_le, min_eq_right bot_le])
  have hs := hq'.zeroAbove
  have hval : ∀ (b : Cell D₀) (hb : D₀.scope b ⊆ C) (hg : D₀.grade b ≤ 2),
      CellScheme.zeroAbove q' (OLD b) = p (properCell sem₀ I M P hAk C b hb hg) := fun b hb hg =>
    (CellScheme.zeroAbove_low q'
      (CellScheme.below.mono h (properCell sem₀ I M P hAk C b hb hg))).trans (hres _)
  have key := tower_readback_of_availability sem₀ I M P hAk hI hproper c ρ q hc hρ hq hP m₀ hβ hj hs
    ((hval ρ hρC hρ).trans hpρ) ((hval c hcC hc.le).symm ▸ hpc)
    (((hval ρ hρC hρ).trans_le hρc).trans_eq (hval c hcC hc.le).symm)
  rw [hval q hqC hq] at key
  exact hpq key

/-! ## The lift at cap `⊥`, and the lift by controller change at a member's cap -/

/-- **The lift at cap `⊥`**: whenever the prescribed labelling extends to a retained member, that
member's row is a lift — respecting, trivially capped-agreeing at `⊥` with any ambient, and
restricting literally to `p`. -/
theorem lift_of_member_extends (C : Finset ι) (hC : (C, 2) ∈ Plan.gradedPlan D₀.plan) (hCA : C ≠ A)
    (p : Tbelow (C, 2) → ExtOrd) (qa : Tbelow (A, 2) → ExtOrd) (m : Member sem₀ I 2 P)
    (hm : ∀ (b : Cell D₀) (hb : D₀.scope b ⊆ C) (hg : D₀.grade b ≤ 2),
      m.F ⟨b, hg⟩ = p (properCell sem₀ I M P hAk C b hb hg)) :
    ∃ q' : Tbelow (A, 2) → ExtOrd,
      RespectsSemanticsBelow (towerSem sem₀ I M P hAk hI hproper) (A, 2) q' ∧
      (∀ d, min (q' d) ⊥ = min (qa d) ⊥) ∧
      ∀ d : Tbelow (C, 2), q' (CellScheme.below.mono (gradedLe_full_two hC) d) = p d :=
  ⟨MROW m, memberRow_respects sem₀ I M P hAk hI hproper m,
    fun _ => by rw [min_eq_right bot_le, min_eq_right bot_le],
    memberRow_restrict sem₀ I M P hAk hI hproper C hC hCA p m hm⟩

/-- **Capped agreement of two member rows** under the first member's cap, when the pair's level
cap is that cap: at base and level-one cells by the full-vector agreement, at level-two cells by
the capped ultrametric identity. -/
theorem memberRow_agree_of_levelCap (m m' : Member sem₀ I 2 P)
    (hmm : levelCap 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ = m.γ)
    (d : Tbelow (A, 2)) : min (MROW m' d) m.γ = min (MROW m d) m.γ := by
  have hag : m.γ ≤ agreeCap (fullVec sem₀ I P hI m) (fullVec sem₀ I P hI m') :=
    hmm.symm.le.trans (levelCap_le_agreeCap _ _ _ _ _ _)
  rw [le_agreeCap_iff] at hag
  obtain ⟨x, hx⟩ := d
  rcases addFull.cases (hlevel sem₀ I M P hAk) x with ⟨b, rfl⟩ | ⟨j, rfl⟩
  · have hg : D₀.grade b ≤ 2 := by
      have hx' : GradedLe (D₀.cell b) (A, 2) := by rw [addFull.cell_old] at hx; exact hx
      exact hx'.2
    rw [memberRow_old sem₀ I M P hAk hI hproper m' b hg,
      memberRow_old sem₀ I M P hAk hI hproper m b hg]
    exact (hag (Sum.inl ⟨b, hg⟩)).symm
  · have hj : level sem₀ I M P j ≤ 2 := by
      have hx' : GradedLe (A, level sem₀ I M P j) (A, 2) := by rw [addFull.cell_new] at hx; exact hx
      exact hx'.2
    rw [memberRow_new sem₀ I M P hAk hI hproper m' j hj,
      memberRow_new sem₀ I M P hAk hI hproper m j hj]
    rcases hm : MEM j with m₁ | m'' | i
    · exact (hag (Sum.inr m₁)).symm
    · have := min_levelCap_eq (l := 2) (I := I) (F := fullVec sem₀ I P hI m) (γ := m.γ)
        (G := fullVec sem₀ I P hI m') (δ := m'.γ) (fullVec sem₀ I P hI m'') m''.γ
      rw [hmm] at this
      exact this.symm
    · exfalso
      have := level_eq_of_memOf_inr_inr sem₀ I M P hm
      omega

/-- **The lift by controller change at a member's cap.**  With the ambient the row of a retained
member `m` and the cap `m.γ`, any retained member `m'` extending `p` literally and agreeing with
`m` under `m`'s cap gives a lift: its row respects, agrees with the ambient under the cap at every
cell, and restricts to `p`. -/
theorem lift_of_agreeing_member (C : Finset ι) (hC : (C, 2) ∈ Plan.gradedPlan D₀.plan)
    (hCA : C ≠ A) (p : Tbelow (C, 2) → ExtOrd) (m m' : Member sem₀ I 2 P)
    (hmm : levelCap 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ = m.γ)
    (hm' : ∀ (b : Cell D₀) (hb : D₀.scope b ⊆ C) (hg : D₀.grade b ≤ 2),
      m'.F ⟨b, hg⟩ = p (properCell sem₀ I M P hAk C b hb hg)) :
    ∃ q' : Tbelow (A, 2) → ExtOrd,
      RespectsSemanticsBelow (towerSem sem₀ I M P hAk hI hproper) (A, 2) q' ∧
      (∀ d, min (q' d) m.γ = min (MROW m d) m.γ) ∧
      ∀ d : Tbelow (C, 2), q' (CellScheme.below.mono (gradedLe_full_two hC) d) = p d :=
  ⟨MROW m', memberRow_respects sem₀ I M P hAk hI hproper m',
    memberRow_agree_of_levelCap sem₀ I M P hAk hI hproper m m' hmm,
    memberRow_restrict sem₀ I M P hAk hI hproper C hC hCA p m' hm'⟩

end VaughtConjecture.Knight
