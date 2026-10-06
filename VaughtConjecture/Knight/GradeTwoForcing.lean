/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoCutoff

/-! # The two-level tower: forcing through the availability witness actually used

**The gap of `Knight/GradeTwoCutoff.lean`.**  `tower_readback` forces the request only for
labellings activating the *designated* display's cell above the cap; a respecting labelling may
activate it below the cap, or not at all, and satisfy availability at the cap through another
level-two member.  This module closes that gap by **thinning the level-two family** — the family
predicate `P` of `Member`, the thinning parameter of `Knight/GradeTwoTower.lean` — to
**cutoff-correct** members (`CutoffCorrect`: the cutoff bound at the representative, the cap and
the request, read on the base labels), and forcing through the availability witness the labelling
actually uses:

* `exists_member_of_cell_two`: every cell at `(A, 2)` is a level-two member's cell;
* `cutoffBound_of_correct`: a correct member's row satisfies the cutoff bound at its own cell;
* `tower_readback_of_availability`: on a tower whose level-two family is cutoff-correct, **every**
  respecting labelling carrying the reference `β + j` at `ρ` under the cap `c ≥ β` reads the
  request at least `β`.  Availability at the cap toward `(A, 2)` supplies a level-two cell
  activated at least at the cap, that cell is a correct member's, and `readback_at_controller`
  applies there.  No hypothesis on which member is activated, nor on the display, is needed.
* The display is a member of the correct family (`Member.select`, `cutoffCorrect_of_reference`).

**The retained subfamily keeps the owned witnesses and availability.**  The thinning is a
parameter of the whole construction: level one is never thinned (`Member₁`), each level-two
member's owned witness is its own counted recoding at level one, and its availability toward
`(A, 2)` is itself; so `towerSem_consistent`, `towerSem_isCoded` and `tower_complete` (given one
retained member) hold for **every** family predicate, in particular for the correct family.

**Designated-display lifting obstruction.**  Suppose a lift is required to carry the display's
base labels *and* to activate the display's own cell at its cap.  `sibling_ge_of_lift` shows what
locality at the display's cell then forces at every sibling member's cell: the lifted labelling,
capped at the display's cap, reads the sibling at least at every base label of the display lying
under their level cap; so an ambient sibling label `⊥` cannot be preserved when the display has a
base label in `(⊥, levelCap]` (`no_capped_lift_of_sibling_bot`).  This is an obstruction to lifts
*through the designated display only*: the literal bountifulness clause (Def. 2.5.14) does not
demand that activation, and both conclusions here are conditional on it.  The literal clause,
with the availability controller free to change, is tested in `Knight/GradeTwoBountifulTest.lean`.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}

/-! ## Cutoff-correct base labellings -/

/-- **Cutoff-correctness** of a grade-two base labelling for the reference cells `c` (cap), `ρ`
(representative) and `q` (request): the cutoff bound of `Knight/FiniteCutoffBound.lean` for the
one-reference data, read on the base labels. -/
def CutoffCorrect (c ρ q : Cell D₀) (hc : D₀.grade c ≤ 2) (hρ : D₀.grade ρ ≤ 2)
    (hq : D₀.grade q ≤ 2) (F : BaseCells D₀ 2 → ExtOrd) : Prop :=
  min (extVisibilityReplace (F ⟨ρ, hρ⟩) 2 0) (F ⟨c, hc⟩) ≤ min (F ⟨q, hq⟩) (F ⟨c, hc⟩)

/-- A labelling carrying the proper reference `β + j` at `ρ`, a cap at least `β` and a request at
least `β` is cutoff-correct. -/
theorem cutoffCorrect_of_reference {c ρ q : Cell D₀} {hc : D₀.grade c ≤ 2} {hρ : D₀.grade ρ ≤ 2}
    {hq : D₀.grade q ≤ 2} {F : BaseCells D₀ 2 → ExtOrd} {β : Ordinal.{0}} (hβ : limitPart β = β)
    {j : ℕ} (hj : j < 2) (hρF : F ⟨ρ, hρ⟩ = ofOrd (β + j)) (hcF : ofOrd β ≤ F ⟨c, hc⟩)
    (hqF : ofOrd β ≤ F ⟨q, hq⟩) : CutoffCorrect c ρ q hc hρ hq F := by
  unfold CutoffCorrect
  rw [hρF, extVisibilityReplace_rep hβ hj, Nat.cast_zero, add_zero, min_eq_left hcF]
  exact le_min hqF hcF

/-- Re-selecting a level-two member into another family whose predicate its labelling
satisfies. -/
def Member.select {sem₀ : Semantics D₀} {I : ℕ} {P : (BaseCells D₀ 2 → ExtOrd) → Prop}
    (m : Member sem₀ I 2 P) (P' : (BaseCells D₀ 2 → ExtOrd) → Prop) (h : P' m.F) :
    Member sem₀ I 2 P' :=
  { m with sel := h }

@[simp] theorem Member.select_F {sem₀ : Semantics D₀} {I : ℕ}
    {P : (BaseCells D₀ 2 → ExtOrd) → Prop} (m : Member sem₀ I 2 P)
    (P' : (BaseCells D₀ 2 → ExtOrd) → Prop) (h : P' m.F) : (m.select P' h).F = m.F := rfl

@[simp] theorem Member.select_γ {sem₀ : Semantics D₀} {I : ℕ}
    {P : (BaseCells D₀ 2 → ExtOrd) → Prop} (m : Member sem₀ I 2 P)
    (P' : (BaseCells D₀ 2 → ExtOrd) → Prop) (h : P' m.F) : (m.select P' h).γ = m.γ := rfl

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
/-- An old cell. -/
local notation "OLD" => addFull.old (hlevel sem₀ I M P hAk)
/-- The member of a new cell. -/
local notation "MEM" => memOf sem₀ I M P

omit hI in
/-- Every cell of the tower at the graded index `(A, 2)` is the cell of a level-two member. -/
theorem exists_member_of_cell_two (Xi : Cell (tower sem₀ I M P hAk)) (hXi : Tcell Xi = (A, 2)) :
    ∃ m : Member sem₀ I 2 P, Xi = memberCell sem₀ I M P hAk m := by
  rcases addFull.cases (hlevel sem₀ I M P hAk) Xi with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exfalso
    rw [addFull.cell_old] at hXi
    exact hproper i (congrArg Prod.fst hXi)
  · rw [addFull.cell_new] at hXi
    have hl : level sem₀ I M P j = 2 := congrArg Prod.snd hXi
    rcases hm : MEM j with m | m | i
    · exfalso
      have := level_eq_of_memOf_inl sem₀ I M P hm
      omega
    · refine ⟨m, ?_⟩
      unfold memberCell
      rw [← hm, idx_memOf]
    · exfalso
      have := level_eq_of_memOf_inr_inr sem₀ I M P hm
      omega

/-- **A correct member's row satisfies the cutoff bound** at its own cell. -/
theorem cutoffBound_of_correct (m : Member sem₀ I 2 P) (c ρ q : Cell D₀) (hc : D₀.grade c = 2)
    (hρ : D₀.grade ρ ≤ 2) (hq : D₀.grade q ≤ 2) (β : Ordinal.{0})
    (hm : CutoffCorrect c ρ q hc.le hρ hq m.F) :
    (oneReference sem₀ I M P hAk m c ρ q hc hρ hq β).CutoffBound
      (SE (memberCell sem₀ I M P hAk m)) := by
  intro _ r hr
  have hr' : r = ⟨baseBelow sem₀ I M P hAk m q hq, β, 0⟩ := List.mem_singleton.mp hr
  subst hr'
  change min (extVisibilityReplace
        (SE (memberCell sem₀ I M P hAk m) (baseBelow sem₀ I M P hAk m ρ hρ)) 2 0)
      (SE (memberCell sem₀ I M P hAk m) (baseBelow sem₀ I M P hAk m c hc.le)) ≤
    min (SE (memberCell sem₀ I M P hAk m) (baseBelow sem₀ I M P hAk m q hq))
      (SE (memberCell sem₀ I M P hAk m) (baseBelow sem₀ I M P hAk m c hc.le))
  rw [E_memberCell_base, E_memberCell_base, E_memberCell_base]
  exact hm

/-- **Forcing through the availability witness actually used.**  On a tower whose level-two
family is cutoff-correct for the reference cells `(c, ρ, q)` and nonempty, every respecting
labelling carrying the proper reference `β + j` at `ρ`, under a cap at `c` at least `β`, reads the
request at least `β` — whichever level-two member it activates. -/
theorem tower_readback_of_availability (c ρ q : Cell D₀) (hc : D₀.grade c = 2)
    (hρ : D₀.grade ρ ≤ 2) (hq : D₀.grade q ≤ 2) (hP : ∀ F, P F → CutoffCorrect c ρ q hc.le hρ hq F)
    (m₀ : Member sem₀ I 2 P) {β : Ordinal.{0}} (hβ : limitPart β = β) {j : ℕ} (hj : j < 2)
    {s : Cell (tower sem₀ I M P hAk) → ExtOrd}
    (hs : RespectsSemantics (towerSem sem₀ I M P hAk hI hproper) s)
    (hsρ : s (OLD ρ) = ofOrd (β + j)) (hsc : ofOrd β ≤ s (OLD c)) (hρc : s (OLD ρ) ≤ s (OLD c)) :
    truncExt β (s (OLD q)) = ⊤ := by
  have hscope : (tower sem₀ I M P hAk).scope (OLD c) ⊆
      (tower sem₀ I M P hAk).scope (memberCell sem₀ I M P hAk m₀) := by
    rw [addFull.scope_old]
    change D₀.scope c ⊆ (Tcell (memberCell sem₀ I M P hAk m₀)).1
    rw [cell_memberCell]
    exact D₀.isPlan.subset_of_mem (D₀.scope_mem_plan c)
  have hgrade : (tower sem₀ I M P hAk).grade (OLD c) =
      (tower sem₀ I M P hAk).grade (memberCell sem₀ I M P hAk m₀) := by
    rw [addFull.grade_old]
    change D₀.grade c = (Tcell (memberCell sem₀ I M P hAk m₀)).2
    rw [cell_memberCell]
    exact hc
  obtain ⟨Xi, hXi, hle⟩ := hs.availability (OLD c) (memberCell sem₀ I M P hAk m₀) hscope hgrade
  obtain ⟨m, rfl⟩ := exists_member_of_cell_two sem₀ I M P hAk hproper Xi
    (hXi.trans (cell_memberCell sem₀ I M P hAk m₀))
  have hSig : s (memberCell sem₀ I M P hAk m) ≠ ⊥ := by
    intro h
    have h1 : ofOrd β ≤ (⊥ : ExtOrd) := hsc.trans (hle.trans_eq h)
    exact ofOrd_ne_bot β (le_bot_iff.mp h1)
  exact readback_at_controller hs (memberCell sem₀ I M P hAk m)
    (oneReference sem₀ I M P hAk m c ρ q hc hρ hq β)
    (cutoffBound_of_correct sem₀ I M P hAk hI hproper m c ρ q hc hρ hq β (hP _ m.sel)) rfl hSig
    hle (List.mem_singleton_self _) rfl hβ hj hsρ hsc hρc

/-! ## Capped lifting from ambient sibling labels: the failed clause -/

omit hI hproper in
/-- A sibling member's cell as a cell of the lower set of a member's cell. -/
noncomputable def siblingBelow (m m' : Member sem₀ I 2 P) :
    Tbelow (Tcell (memberCell sem₀ I M P hAk m)) :=
  ⟨memberCell sem₀ I M P hAk m', by
    rw [cell_memberCell, cell_memberCell]
    exact GradedLe.refl _⟩

/-- The row of a member at a sibling's cell is their level cap. -/
theorem E_memberCell_sibling (m m' : Member sem₀ I 2 P) :
    SE (memberCell sem₀ I M P hAk m) (siblingBelow sem₀ I M P hAk m m') =
      levelCap 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ := by
  have hj' : level sem₀ I M P (idx sem₀ I M P (Sum.inr (Sum.inl m'))) ≤
      level sem₀ I M P (idx sem₀ I M P (Sum.inr (Sum.inl m))) := by
    rw [level_idx, level_idx]
    exact le_rfl
  have h := E_new_new sem₀ I M P hAk hI hproper (idx sem₀ I M P (Sum.inr (Sum.inl m)))
    (idx sem₀ I M P (Sum.inr (Sum.inl m'))) hj' (siblingBelow sem₀ I M P hAk m m').2
  rw [newRow_two_new sem₀ I M P hI (memOf_memberCell sem₀ I M P m) _ hj',
    memOf_memberCell] at h
  exact h

/-- **Designated-display lifting: what activating the display at its cap forces at a sibling.**
If a respecting labelling carries the display's base labels and activates the display's cell at
its cap, then at every sibling member's cell the labelling, capped at the display's cap, is at
least every base label of the display lying under their level cap.  (Conditional on the
activation; the bountifulness clause does not demand it.) -/
theorem sibling_ge_of_lift (m m' : Member sem₀ I 2 P) {s : Cell (tower sem₀ I M P hAk) → ExtOrd}
    (hs : RespectsSemantics (towerSem sem₀ I M P hAk hI hproper) s)
    (hbase : ∀ (b : Cell D₀) (hb : D₀.grade b ≤ 2), s (OLD b) = m.F ⟨b, hb⟩)
    (hself : s (memberCell sem₀ I M P hAk m) = m.γ) (b : Cell D₀) (hb : D₀.grade b ≤ 2)
    (hbℓ : m.F ⟨b, hb⟩ ≤
      levelCap 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ) :
    m.F ⟨b, hb⟩ ≤ min (s (memberCell sem₀ I M P hAk m')) (s (memberCell sem₀ I M P hAk m)) := by
  obtain ⟨g, σ, -, -, -, hσmono, -, hrow⟩ := hs.locality (memberCell sem₀ I M P hAk m)
  have hg : (tower sem₀ I M P hAk).grade (memberCell sem₀ I M P hAk m) = 2 :=
    congrArg Prod.snd (cell_memberCell sem₀ I M P hAk m)
  have hg' : (tower sem₀ I M P hAk).grade (memberCell sem₀ I M P hAk m') = 2 :=
    congrArg Prod.snd (cell_memberCell sem₀ I M P hAk m')
  have h1 : min (s (OLD b)) (s (memberCell sem₀ I M P hAk m)) =
      min (σ (SE (memberCell sem₀ I M P hAk m) (baseBelow sem₀ I M P hAk m b hb)))
        (g ((tower sem₀ I M P hAk).grade (OLD b))) := hrow (baseBelow sem₀ I M P hAk m b hb)
  rw [E_memberCell_base, hbase b hb, hself, min_eq_left (m.le_cap _)] at h1
  have h2 : min (s (memberCell sem₀ I M P hAk m)) (s (memberCell sem₀ I M P hAk m)) =
      min (σ (SE (memberCell sem₀ I M P hAk m) (selfBelow sem₀ I M P hAk m)))
        (g ((tower sem₀ I M P hAk).grade (memberCell sem₀ I M P hAk m))) :=
    hrow (selfBelow sem₀ I M P hAk m)
  rw [E_memberCell_self, hself, min_self, hg] at h2
  have h3 : min (s (memberCell sem₀ I M P hAk m')) (s (memberCell sem₀ I M P hAk m)) =
      min (σ (SE (memberCell sem₀ I M P hAk m) (siblingBelow sem₀ I M P hAk m m')))
        (g ((tower sem₀ I M P hAk).grade (memberCell sem₀ I M P hAk m'))) :=
    hrow (siblingBelow sem₀ I M P hAk m m')
  rw [E_memberCell_sibling, hg'] at h3
  rw [h3]
  refine le_min ?_ ?_
  · exact (h1.le.trans (min_le_left _ _)).trans (hσmono hbℓ)
  · exact (m.le_cap _).trans (h2.le.trans (min_le_right _ _))

/-- **Designated-display lifting obstruction.**  A labelling carrying the display's base labels and
activating the display at its cap cannot read a sibling member's cell at `⊥` as soon as the
display has a base label strictly above `⊥` under their level cap.  This obstructs only lifts
that activate the designated display; it is not a counterexample to the bountifulness clause. -/
theorem no_capped_lift_of_sibling_bot (m m' : Member sem₀ I 2 P)
    {s : Cell (tower sem₀ I M P hAk) → ExtOrd}
    (hs : RespectsSemantics (towerSem sem₀ I M P hAk hI hproper) s)
    (hbase : ∀ (b : Cell D₀) (hb : D₀.grade b ≤ 2), s (OLD b) = m.F ⟨b, hb⟩)
    (hself : s (memberCell sem₀ I M P hAk m) = m.γ) (b : Cell D₀) (hb : D₀.grade b ≤ 2)
    (hbℓ : m.F ⟨b, hb⟩ ≤
      levelCap 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ)
    (hb0 : m.F ⟨b, hb⟩ ≠ ⊥) : s (memberCell sem₀ I M P hAk m') ≠ ⊥ := by
  intro h0
  have h := sibling_ge_of_lift sem₀ I M P hAk hI hproper m m' hs hbase hself b hb hbℓ
  rw [h0, min_eq_left bot_le] at h
  exact hb0 (le_bot_iff.mp h)

end VaughtConjecture.Knight
