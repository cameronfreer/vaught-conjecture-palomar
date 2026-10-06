/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoBountifulTest

/-! # The two-level tower: proper-scope correctness as an inductive invariant

`Knight/GradeTwoBountifulTest.lean` showed that, at cap `⊥`, the literal bountifulness clause
cannot exclude an already-lawful proper-face input by imposing correctness only at full scope:
if the base admits a lawful labelling of `D⟨C,2⟩` carrying the reference with an incorrect
request, the correct thinning is not bountiful.  This module turns the missing condition into an
explicit invariant and proves its induction step.

* `CorrectAt sem BJ c ρ q`: every labelling of `D⟨BJ⟩` respecting `E⟨BJ⟩` that carries the proper
  reference `β + j` (`j < 2`) at `ρ` under a cap at `c` at least `β` reads the request `q` at
  least `β`.  `ProperCorrect` asks this at every *proper* grade-two index containing the
  reference cells; `FullCorrect` at every grade-two index.
* **Base case** (`properCorrect_of_no_proper_scope`): when no proper scope of the plan contains
  the three reference cells jointly — the reference is attached at full scope — the proper
  invariant holds vacuously.  This is a concrete base realizing the hypothesis; the paper's
  inductive situation (a base that is itself a forced tower) is *not* an available hypothesis and
  is not assumed.
* **Induction step** (`fullCorrect_tower`): over a base satisfying `ProperCorrect`, the tower
  with a cutoff-correct level-two family satisfies `FullCorrect` — at every proper index because
  its lower set consists of base cells only, whose lawful labellings are exactly the base's
  (`belowProper`, `respectsBelow_of_tower`, `respectsBelow_tower_of_base`), and at the full
  index by the forcing through the availability witness actually used
  (`tower_readback_of_availability`).  `FullCorrect` of the tower is `ProperCorrect` for any
  construction over a strictly larger scope: the invariant propagates.
* **Necessity** (`properCorrect_of_isBountiful`): if the thinned tower is bountiful, the base
  satisfies `ProperCorrect` at every proper scope containing the reference — the contrapositive
  of the bottom-cap counterexample.  So, at bottom cap, the invariant is exactly what
  bountifulness of the correctness thinning requires of its base.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

/-! ## The invariant, for any semantics -/

section Invariant

variable {D : CellScheme A}

/-- **Correctness below a graded index**: every labelling of `D⟨BJ⟩` respecting `E⟨BJ⟩` carrying
the proper reference `β + j`, `j < 2`, at `ρ` under a cap at `c` at least `β` reads the request
`q` at least `β`. -/
def CorrectAt (sem : Semantics D) (BJ : Finset ι × ℕ) (c ρ q : Cell D)
    (hc : GradedLe (D.cell c) BJ) (hρ : GradedLe (D.cell ρ) BJ) (hq : GradedLe (D.cell q) BJ) :
    Prop :=
  ∀ p : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ p →
    ∀ β : Ordinal.{0}, limitPart β = β → ∀ j : ℕ, j < 2 →
      p ⟨ρ, hρ⟩ = ofOrd (β + j) → ofOrd β ≤ p ⟨c, hc⟩ → p ⟨ρ, hρ⟩ ≤ p ⟨c, hc⟩ →
        truncExt β (p ⟨q, hq⟩) = ⊤

/-- **The proper-scope correctness invariant**: correctness at every proper grade-two index of
the plan containing the reference cells. -/
def ProperCorrect (sem : Semantics D) (c ρ q : Cell D) : Prop :=
  ∀ B : Finset ι, (B, 2) ∈ Plan.gradedPlan D.plan → B ≠ A →
    ∀ (hc : GradedLe (D.cell c) (B, 2)) (hρ : GradedLe (D.cell ρ) (B, 2))
      (hq : GradedLe (D.cell q) (B, 2)), CorrectAt sem (B, 2) c ρ q hc hρ hq

/-- **Full correctness**: at every grade-two index of the plan containing the reference cells. -/
def FullCorrect (sem : Semantics D) (c ρ q : Cell D) : Prop :=
  ∀ B : Finset ι, (B, 2) ∈ Plan.gradedPlan D.plan →
    ∀ (hc : GradedLe (D.cell c) (B, 2)) (hρ : GradedLe (D.cell ρ) (B, 2))
      (hq : GradedLe (D.cell q) (B, 2)), CorrectAt sem (B, 2) c ρ q hc hρ hq

theorem FullCorrect.properCorrect {sem : Semantics D} {c ρ q : Cell D} (h : FullCorrect sem c ρ q) :
    ProperCorrect sem c ρ q :=
  fun B hB _ hc hρ hq => h B hB hc hρ hq

/-- **Base case**: when no proper scope of the plan contains the three reference cells jointly,
the proper invariant holds vacuously. -/
theorem properCorrect_of_no_proper_scope (sem : Semantics D) {c ρ q : Cell D}
    (h : ∀ B ∈ D.plan, B ≠ A → ¬ (D.scope c ⊆ B ∧ D.scope ρ ⊆ B ∧ D.scope q ⊆ B)) :
    ProperCorrect sem c ρ q :=
  fun B hB hBA hc hρ hq =>
    absurd ⟨hc.1, hρ.1, hq.1⟩ (h B (Plan.mem_gradedPlan.mp hB).1 hBA)

end Invariant

/-! ## The tower -/

variable {D₀ : CellScheme A} (sem₀ : Semantics D₀) (I M : ℕ)
  (P : (BaseCells D₀ 2 → ExtOrd) → Prop)
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
/-- The lower-set equivalence of an old cell. -/
local notation "BO" => addFull.belowOld (hlevel sem₀ I M P hAk) hproper

omit hI hproper in
/-- **The lower set of a proper index is the base's**: the old cells embed onto it. -/
noncomputable def belowProper (B : Finset ι) (hB : (B, 2) ∈ Plan.gradedPlan D₀.plan)
    (hBA : B ≠ A) : D₀.below (B, 2) ≃ Tbelow (B, 2) :=
  Equiv.ofBijective (fun d => ⟨OLD d.1, by rw [addFull.cell_old]; exact d.2⟩)
    ⟨fun a b h => Subtype.ext (addFull.old_injective _ (congrArg Subtype.val h)), fun e => by
      rcases addFull.cases (hlevel sem₀ I M P hAk) e.1 with ⟨i, hi⟩ | ⟨j, hj⟩
      · refine ⟨⟨i, ?_⟩, Subtype.ext hi.symm⟩
        have := e.2
        rw [hi, addFull.cell_old] at this
        exact this
      · exfalso
        have := e.2
        rw [hj, addFull.cell_new] at this
        exact hBA (Finset.Subset.antisymm
          (D₀.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hB).1) this.1)⟩

omit hI hproper in
theorem belowProper_apply (B : Finset ι) (hB : (B, 2) ∈ Plan.gradedPlan D₀.plan) (hBA : B ≠ A)
    (d : D₀.below (B, 2)) :
    (belowProper sem₀ I M P hAk B hB hBA d).1 = OLD d.1 := rfl

omit hI hproper in
theorem belowProper_symm (B : Finset ι) (hB : (B, 2) ∈ Plan.gradedPlan D₀.plan) (hBA : B ≠ A)
    (b : Cell D₀) (hb : GradedLe (D₀.cell b) (B, 2)) (h : GradedLe (Tcell (OLD b)) (B, 2)) :
    (belowProper sem₀ I M P hAk B hB hBA).symm ⟨OLD b, h⟩ = ⟨b, hb⟩ :=
  (belowProper sem₀ I M P hAk B hB hBA).symm_apply_eq.mpr (Subtype.ext rfl)

/-- **Lawful labellings of a proper lower set of the tower are lawful for the base.** -/
theorem respectsBelow_of_tower (B : Finset ι) (hB : (B, 2) ∈ Plan.gradedPlan D₀.plan) (hBA : B ≠ A)
    {p : Tbelow (B, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow (towerSem sem₀ I M P hAk hI hproper) (B, 2) p) :
    RespectsSemanticsBelow sem₀ (B, 2)
      (fun d => p (belowProper sem₀ I M P hAk B hB hBA d)) where
  orderly d := by
    have h := hp.orderly (belowProper sem₀ I M P hAk B hB hBA d)
    have hg : (tower sem₀ I M P hAk).grade (OLD d.1) = D₀.grade d.1 := addFull.grade_old _ _
    change p (belowProper sem₀ I M P hAk B hB hBA d) =
      extVisibilityReplace (p (belowProper sem₀ I M P hAk B hB hBA d))
        ((tower sem₀ I M P hAk).grade (OLD d.1)) ((tower sem₀ I M P hAk).grade (OLD d.1)) at h
    rw [hg] at h
    exact h
  locality Sig := by
    obtain ⟨g, σ, h1, h2, h3, h4, h5, h6⟩ :=
      hp.locality (belowProper sem₀ I M P hAk B hB hBA Sig)
    refine ⟨g, σ, h1, h2, h3, h4, h5, fun d => ?_⟩
    have h := h6 (BO Sig.1 d)
    have hE : SE (OLD Sig.1) (BO Sig.1 d) = sem₀.E Sig.1 d :=
      addFull.addFullSem_E_old_apply (hlevel sem₀ I M P hAk) hproper sem₀ _ _ Sig.1 d
    have hg : (tower sem₀ I M P hAk).grade (OLD d.1) = D₀.grade d.1 := addFull.grade_old _ _
    change min (p (CellScheme.below.incl (belowProper sem₀ I M P hAk B hB hBA Sig)
        (BO Sig.1 d))) (p (belowProper sem₀ I M P hAk B hB hBA Sig)) =
      min (σ (SE (OLD Sig.1) (BO Sig.1 d))) (g ((tower sem₀ I M P hAk).grade (OLD d.1))) at h
    rw [hE, hg] at h
    exact h
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hXi, hle⟩ := hp.availability (belowProper sem₀ I M P hAk B hB hBA Sig)
      (belowProper sem₀ I M P hAk B hB hBA Xi₀)
      (by
        change (tower sem₀ I M P hAk).scope (OLD Sig.1) ⊆ (tower sem₀ I M P hAk).scope (OLD Xi₀.1)
        rw [addFull.scope_old, addFull.scope_old]
        exact hs)
      (by
        change (tower sem₀ I M P hAk).grade (OLD Sig.1) = (tower sem₀ I M P hAk).grade (OLD Xi₀.1)
        rw [addFull.grade_old, addFull.grade_old]
        exact hg)
    refine ⟨(belowProper sem₀ I M P hAk B hB hBA).symm Xi, ?_, ?_⟩
    · have h1 : Tcell (belowProper sem₀ I M P hAk B hB hBA
          ((belowProper sem₀ I M P hAk B hB hBA).symm Xi)).1 =
          D₀.cell ((belowProper sem₀ I M P hAk B hB hBA).symm Xi).1 :=
        addFull.cell_old _ _
      rw [Equiv.apply_symm_apply] at h1
      have h2 : Tcell (belowProper sem₀ I M P hAk B hB hBA Xi₀).1 = D₀.cell Xi₀.1 :=
        addFull.cell_old _ _
      rw [← h1, hXi, h2]
    · rw [Equiv.apply_symm_apply]
      exact hle

/-- **Lawful labellings of the base at a proper index are lawful for the tower.** -/
theorem respectsBelow_tower_of_base (B : Finset ι) (hB : (B, 2) ∈ Plan.gradedPlan D₀.plan)
    (hBA : B ≠ A) {r : D₀.below (B, 2) → ExtOrd} (hr : RespectsSemanticsBelow sem₀ (B, 2) r) :
    RespectsSemanticsBelow (towerSem sem₀ I M P hAk hI hproper) (B, 2)
      (fun d' => r ((belowProper sem₀ I M P hAk B hB hBA).symm d')) :=
  RespectsSemanticsBelow.of_lowerEquiv (sem := sem₀)
    (sem' := towerSem sem₀ I M P hAk hI hproper) (belowProper sem₀ I M P hAk B hB hBA)
    (fun d => addFull.cell_old _ d.1) (fun Sig => BO Sig.1) (fun _ d => addFull.cell_old _ d.1)
    (fun _ _ => Subtype.ext rfl)
    (fun Sig d => addFull.addFullSem_E_old_apply (hlevel sem₀ I M P hAk) hproper sem₀ _ _ Sig.1 d)
    hr

omit hI hproper in
/-- An old cell of grade `≤ 2` lies below the full index. -/
theorem oldFull (b : Cell D₀) (hg : D₀.grade b ≤ 2) : GradedLe (Tcell (OLD b)) (A, 2) := by
  rw [addFull.cell_old]
  exact ⟨D₀.isPlan.subset_of_mem (D₀.scope_mem_plan b), hg⟩

omit hI hproper in
/-- An old cell below a base index lies below it in the tower. -/
theorem oldProper {B : Finset ι} (b : Cell D₀) (h : GradedLe (D₀.cell b) (B, 2)) :
    GradedLe (Tcell (OLD b)) (B, 2) := by
  rw [addFull.cell_old]
  exact h

/-! ## The induction step -/

/-- **Correctness at the full index, by the forcing**: on a tower with a cutoff-correct level-two
family, every lawful labelling of `D⟨A,2⟩` carrying the reference reads the request at least the
cut — through whichever member availability at the cap activates. -/
theorem correctAt_full (c ρ q : Cell D₀) (hc : D₀.grade c = 2) (hρ : D₀.grade ρ ≤ 2)
    (hq : D₀.grade q ≤ 2) (hP : ∀ F, P F → CutoffCorrect c ρ q hc.le hρ hq F)
    (m₀ : Member sem₀ I 2 P) :
    CorrectAt (towerSem sem₀ I M P hAk hI hproper) (A, 2) (OLD c) (OLD ρ) (OLD q)
      (oldFull sem₀ I M P hAk c hc.le) (oldFull sem₀ I M P hAk ρ hρ)
      (oldFull sem₀ I M P hAk q hq) := by
  intro p hp β hβ j hj hpρ hpc hρc
  have hs := hp.zeroAbove
  have hv : ∀ (b : Cell D₀) (hg : D₀.grade b ≤ 2),
      CellScheme.zeroAbove p (OLD b) = p ⟨OLD b, oldFull sem₀ I M P hAk b hg⟩ := fun b hg =>
    CellScheme.zeroAbove_low p ⟨OLD b, oldFull sem₀ I M P hAk b hg⟩
  have key := tower_readback_of_availability sem₀ I M P hAk hI hproper c ρ q hc hρ hq hP m₀ hβ hj
    hs ((hv ρ hρ).trans hpρ) ((hv c hc.le).symm ▸ hpc)
    (((hv ρ hρ).trans_le hρc).trans_eq (hv c hc.le).symm)
  rw [hv q hq] at key
  exact key

/-- **Correctness at a proper index is inherited from the base.** -/
theorem correctAt_proper_of_base (B : Finset ι) (hB : (B, 2) ∈ Plan.gradedPlan D₀.plan)
    (hBA : B ≠ A) (c ρ q : Cell D₀) (hc : GradedLe (D₀.cell c) (B, 2))
    (hρ : GradedLe (D₀.cell ρ) (B, 2)) (hq : GradedLe (D₀.cell q) (B, 2))
    (h₀ : CorrectAt sem₀ (B, 2) c ρ q hc hρ hq) :
    CorrectAt (towerSem sem₀ I M P hAk hI hproper) (B, 2) (OLD c) (OLD ρ) (OLD q)
      (oldProper sem₀ I M P hAk c hc) (oldProper sem₀ I M P hAk ρ hρ)
      (oldProper sem₀ I M P hAk q hq) := by
  intro p hp β hβ j hj hpρ hpc hρc
  exact h₀ _ (respectsBelow_of_tower sem₀ I M P hAk hI hproper B hB hBA hp) β hβ j hj hpρ hpc hρc

/-- **The induction step**: over a base satisfying the proper-scope invariant, the tower with a
cutoff-correct level-two family is fully correct — at proper indices from the base, at the full
index by the forcing. -/
theorem fullCorrect_tower (c ρ q : Cell D₀) (hc : D₀.grade c = 2) (hρ : D₀.grade ρ ≤ 2)
    (hq : D₀.grade q ≤ 2) (hP : ∀ F, P F → CutoffCorrect c ρ q hc.le hρ hq F)
    (m₀ : Member sem₀ I 2 P) (h₀ : ProperCorrect sem₀ c ρ q) :
    FullCorrect (towerSem sem₀ I M P hAk hI hproper) (OLD c) (OLD ρ) (OLD q) := by
  intro B hB hcB hρB hqB
  by_cases hBA : B = A
  · subst hBA
    exact correctAt_full sem₀ I M P hAk hI hproper c ρ q hc hρ hq hP m₀
  · have hc' : GradedLe (D₀.cell c) (B, 2) := by rw [addFull.cell_old] at hcB; exact hcB
    have hρ' : GradedLe (D₀.cell ρ) (B, 2) := by rw [addFull.cell_old] at hρB; exact hρB
    have hq' : GradedLe (D₀.cell q) (B, 2) := by rw [addFull.cell_old] at hqB; exact hqB
    exact correctAt_proper_of_base sem₀ I M P hAk hI hproper B hB hBA c ρ q hc' hρ' hq'
      (h₀ B hB hBA hc' hρ' hq')

/-! ## Necessity: bountifulness of the thinning requires the invariant of the base -/

/-- **If the thinned tower is bountiful, the base satisfies the proper-scope invariant** at every
proper scope containing the reference: the contrapositive of the bottom-cap counterexample. -/
theorem properCorrect_of_isBountiful (c ρ q : Cell D₀) (hc : D₀.grade c = 2)
    (hρ : D₀.grade ρ ≤ 2) (hq : D₀.grade q ≤ 2) (hP : ∀ F, P F → CutoffCorrect c ρ q hc.le hρ hq F)
    (m₀ : Member sem₀ I 2 P) (hB : (towerSem sem₀ I M P hAk hI hproper).IsBountiful) :
    ProperCorrect sem₀ c ρ q := by
  intro B hBp hBA hcB hρB hqB p hp β hβ j hj hpρ hpc hρc
  by_contra hpq
  refine not_bountiful_of_incorrect_proper sem₀ I M P hAk hI hproper c ρ q hc hρ hq hP m₀ B hBp
    hBA hcB.1 hρB.1 hqB.1 hβ hj
    (fun d' => p ((belowProper sem₀ I M P hAk B hBp hBA).symm d'))
    (respectsBelow_tower_of_base sem₀ I M P hAk hI hproper B hBp hBA hp) ?_ ?_ ?_ ?_ hB
  · change p ((belowProper sem₀ I M P hAk B hBp hBA).symm ⟨OLD ρ, _⟩) = _
    rw [belowProper_symm sem₀ I M P hAk B hBp hBA ρ hρB]
    exact hpρ
  · change ofOrd β ≤ p ((belowProper sem₀ I M P hAk B hBp hBA).symm ⟨OLD c, _⟩)
    rw [belowProper_symm sem₀ I M P hAk B hBp hBA c hcB]
    exact hpc
  · change p ((belowProper sem₀ I M P hAk B hBp hBA).symm ⟨OLD ρ, _⟩) ≤
      p ((belowProper sem₀ I M P hAk B hBp hBA).symm ⟨OLD c, _⟩)
    rw [belowProper_symm sem₀ I M P hAk B hBp hBA ρ hρB,
      belowProper_symm sem₀ I M P hAk B hBp hBA c hcB]
    exact hρc
  · change truncExt β (p ((belowProper sem₀ I M P hAk B hBp hBA).symm ⟨OLD q, _⟩)) ≠ ⊤
    rw [belowProper_symm sem₀ I M P hAk B hBp hBA q hqB]
    exact hpq

end VaughtConjecture.Knight
