/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TwoContextPrescribedPair

/-!
# Separating the forced witness-copy identification: necessary conditions, and the local test

The fixed glue `rows₂` identifies the two occurrences of input A's level-one witness (`H₀old`
on the A face, `H₀new` on the fresh B face): every non-mute controller reads the same source at
both, so rigidity forces equal labels.  This scout records what **any** semantics on `D₂` must do
for the specified pair (`ω+4` at `H₀old`, `ω·2+3` at `H₀new`) to be realized by a respecting
labelling — with both input faces (cells, rows, labels) untouched:

* `exists_separating_controller`: at every grade `j ∈ {1,2,3}` at which the B face carries a
  label `≥ ω·2+3`, some full-scope controller `U` of grade `j` is labelled `≥ ω·2+3` and reads a
  **strictly smaller** source at `H₀old` than at `H₀new` (its row separates the occurrences);
* `le_γ₀_of_row_eq`: every controller reading equal sources at the two occurrences is labelled
  `≤ ω+4` (so the unmodified pulled-back controllers can never dominate the B-face labels);
* `IsConsistent.le_of_probe_eq`: at a separating consistent controller `c`, every intermediate
  cell `Sig` reading equal sources is read by `c` at most its `H₀old` value (the cross entries
  are bounded by the old value);
* `IsConsistent.exists_dominating`: at a consistent controller `c`, a value at a cell of the
  **same grade as `c`** is dominated by an entry of `c` at a cell of `c`'s own graded index.  For
  `H₀new` this is row availability at grade one only: at the grade-one controller the diagonal
  (the only full-scope grade-one cell) must be raised as well.  At the grade-two and grade-three
  controllers it says nothing about `H₀new`; there availability supplies domination of the
  separating value at a full-scope grade-one cell of the controller's lower set.

**The general no-go** (`not_realizable_of_grade_one_pullback`): the specified pair `(p₀, p₁)` is
realized by no respecting labelling of *any* semantics on `D₂` whose grade-one full-scope
controller reads equal sources at the two occurrences (the fixed glue `rows₂` is the special case,
`not_realizable_rows₂`).

**The local test, passed** (`separating_row_test`): at the grade-one full controller `U_H` (the
fresh full copy of the level-one witness) the request-dependent row `row₃` — the pulled-back row
with the separating value `ω·(k+1)+2` (the successor of the cap code `ω·(k+1)+1`, `k` the number of
keys of the level-one code) at the copy and at the diagonal — is orderly, coded at grade one,
dominated by its diagonal, strictly separates the two occurrences, and its locality clause at the
copy is witnessed by `Witness.raise` on the identity with cutoff `ω·k+2` (strictly between every
proper-cell code and the cap code, finite part `2 > 1`).  Both input faces are untouched.

Not done here: the full modified semantics (the same separation is forced at grades two and three
by input B's labels `ω·2+3` at `s₀` and `b₁`; the raised grade-one value must propagate coherently
through the higher rows' values at the grade-one full controller — a `Witness.lower` flattening
is a proposed proof route, not established), its bountifulness (for `rows₂` proved from the two face obligations
`rows₂_isBountiful_of`, which are stated against the glue's rows and would have to be re-proved
for modified rows), and the respecting labelling itself.  Construction-private. -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## Generic probe lemmas: strict and equal sources -/

section Probes
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}
  {BJ : Finset ι × ℕ} {q : D.below BJ → ExtOrd}

/-- **Strict probe**: strictly ordered probes at equal grades come from strictly ordered sources. -/
theorem RespectsSemanticsBelow.lt_of_probe_lt (hq : RespectsSemanticsBelow sem BJ q)
    (Sig : D.below BJ) (d d' : D.below (D.cell Sig.1)) (hgr : D.grade d.1 = D.grade d'.1)
    (hlt : min (q (CellScheme.below.incl Sig d)) (q Sig) <
      min (q (CellScheme.below.incl Sig d')) (q Sig)) :
    sem.E Sig.1 d < sem.E Sig.1 d' := by
  obtain ⟨g, σ, -, -, -, hσ, -, heq⟩ := hq.locality Sig
  have h1 := heq d
  have h2 := heq d'
  dsimp only at h1 h2
  rw [h1, h2, hgr] at hlt
  by_contra h
  rw [not_lt] at h
  exact absurd hlt (not_lt.mpr (min_le_min (hσ h) le_rfl))

/-- **Equal probe**: equal sources at equal grades give equal probes. -/
theorem RespectsSemanticsBelow.probe_eq_of_row_eq (hq : RespectsSemanticsBelow sem BJ q)
    (Sig : D.below BJ) (d d' : D.below (D.cell Sig.1)) (hrow : sem.E Sig.1 d = sem.E Sig.1 d')
    (hgr : D.grade d.1 = D.grade d'.1) :
    min (q (CellScheme.below.incl Sig d)) (q Sig) =
      min (q (CellScheme.below.incl Sig d')) (q Sig) := by
  obtain ⟨g, σ, -, -, -, -, -, heq⟩ := hq.locality Sig
  have h1 := heq d
  have h2 := heq d'
  dsimp only at h1 h2
  rw [h1, h2, hrow, hgr]

/-- Equal probes of strictly ordered labels bound the controller by the smaller label. -/
theorem le_of_min_eq_min {a b s : ExtOrd} (hab : a < b) (h : min a s = min b s) : s ≤ a := by
  by_contra hs
  rw [not_le] at hs
  rw [min_eq_left hs.le] at h
  have : a < min b s := lt_min hab hs
  rw [← h] at this
  exact lt_irrefl _ this

/-- **A controller reading equal sources at two cells of equal grade is labelled at most the
smaller of their labels.** -/
theorem RespectsSemanticsBelow.le_of_row_eq (hq : RespectsSemanticsBelow sem BJ q)
    (Sig : D.below BJ) (d d' : D.below (D.cell Sig.1)) (hrow : sem.E Sig.1 d = sem.E Sig.1 d')
    (hgr : D.grade d.1 = D.grade d'.1)
    (hlt : q (CellScheme.below.incl Sig d) < q (CellScheme.below.incl Sig d')) :
    q Sig ≤ q (CellScheme.below.incl Sig d) :=
  le_of_min_eq_min hlt (hq.probe_eq_of_row_eq Sig d d' hrow hgr)

end Probes

/-! ## Consequences of consistency for a separating controller -/

section Consistent
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- **Cross entries are bounded by the old value**: at a consistent controller `c` reading
strictly ordered sources at `d < d'`, every cell `Sig` below `c` above both, whose own row reads
equal sources there, is read by `c` at most `c`'s value at `d`. -/
theorem Semantics.IsConsistent.le_of_probe_eq (hc : sem.IsConsistent) (c : Cell D)
    (Sig : D.below (D.cell c)) (d d' : D.below (D.cell Sig.1))
    (hrow : sem.E Sig.1 d = sem.E Sig.1 d') (hgr : D.grade d.1 = D.grade d'.1)
    (hlt : sem.E c (CellScheme.below.incl Sig d) < sem.E c (CellScheme.below.incl Sig d')) :
    sem.E c Sig ≤ sem.E c (CellScheme.below.incl Sig d) :=
  (hc c).le_of_row_eq Sig d d' hrow hgr hlt

/-- **Row availability**: a consistent controller's value at any cell below it is dominated by its
value at some cell of the controller's own graded index. -/
theorem Semantics.IsConsistent.exists_dominating (hc : sem.IsConsistent) (c : Cell D)
    (d : D.below (D.cell c)) (hgr : D.grade d.1 = D.grade c) :
    ∃ Xi : D.below (D.cell c), D.cell Xi.1 = D.cell c ∧ sem.E c d ≤ sem.E c Xi :=
  (hc c).availability d ⟨c, GradedLe.refl _⟩ d.2.1 hgr

end Consistent

/-! ## The two occurrences in the glued domain -/

section Separating

/-- Input B's level-two and level-three cells on the fresh face. -/
noncomputable def s₀new : Cell D₂ := copyB (family₁.e s₀X₁)
noncomputable def b₁new : Cell D₂ := copyB (family₁.e b₁X₁)

theorem grade_H₀old : D₂.grade H₀old = 1 := by
  change (D₂.cell H₀old).2 = 1
  unfold H₀old
  rw [D₂_cell_castAdd, Family.cell_e]
  rfl

theorem grade_copyB_eq (x : family₁.X) : D₂.grade (copyB (family₁.e x)) = (family₁.cellX x).2 := by
  have h := cell_copyB (family₁.e x)
  rw [Family.cell_e] at h
  exact (congrArg Prod.snd h).symm

theorem grade_H₀new : D₂.grade H₀new = 1 := grade_copyB_eq H₀X₁
theorem grade_s₀new : D₂.grade s₀new = 2 := grade_copyB_eq s₀X₁
theorem grade_b₁new : D₂.grade b₁new = 3 := grade_copyB_eq b₁X₁

theorem γ₀_lt_γ₁ : γ₀ < γ₁ := lt_of_le_of_ne γ₀_le_γ₁ (Ne.symm γ₁_ne_γ₀)

theorem memA {j : ℕ} (hj : 1 ≤ j) : GradedLe (D₂.cell H₀old) (Finset.univ, j) :=
  ⟨Finset.subset_univ _, by change D₂.grade H₀old ≤ j; rw [grade_H₀old]; exact hj⟩
theorem memB {j : ℕ} (hj : 1 ≤ j) : GradedLe (D₂.cell H₀new) (Finset.univ, j) :=
  ⟨Finset.subset_univ _, by change D₂.grade H₀new ≤ j; rw [grade_H₀new]; exact hj⟩
theorem memB' (c : Cell C₁) : GradedLe (D₂.cell (copyB c)) (Finset.univ, 3) :=
  (copyB_mem c).trans ⟨Finset.subset_univ _, le_rfl⟩
theorem memA' (i : Cell C₀) :
    GradedLe (D₂.cell (Fin.castAdd (Fintype.card New₂) i)) (Finset.univ, 3) := by
  rw [D₂_cell_castAdd]
  refine ⟨Finset.subset_univ _, ?_⟩
  change C₀.grade i ≤ 3
  exact (C₀.grade_le_card_scope i).trans ((Finset.card_le_univ _).trans (by simp))

/-- Full-scope cells of every grade `1 ≤ i ≤ 4` exist. -/
theorem exists_full_cell {i : ℕ} (hi : 0 < i) (hi4 : i ≤ 4) :
    ∃ c : Cell D₂, D₂.cell c = (Finset.univ, i) :=
  D₂_complete _ (AmalgamationPlan.Plan.mem_gradedPlan.mpr ⟨D₂.isPlan.domain_mem, hi, by
    change i ≤ (Finset.univ : Finset (Fin 4)).card
    rw [Finset.card_univ, Fintype.card_fin]; exact hi4⟩)

theorem incl_H₀old {j : ℕ} (hj : 1 ≤ j) (U : D₂.below (Finset.univ, j))
    (hA : GradedLe (D₂.cell H₀old) (D₂.cell U.1)) :
    CellScheme.below.incl U ⟨H₀old, hA⟩ = ⟨H₀old, memA hj⟩ := Subtype.ext rfl
theorem incl_H₀new {j : ℕ} (hj : 1 ≤ j) (U : D₂.below (Finset.univ, j))
    (hB : GradedLe (D₂.cell H₀new) (D₂.cell U.1)) :
    CellScheme.below.incl U ⟨H₀new, hB⟩ = ⟨H₀new, memB hj⟩ := Subtype.ext rfl

/-- **Separation is forced** (any semantics on the glued domain): a respecting labelling of the
grade-`j` full lower set reading the specified labels at the two occurrences, and a label
`≥ ω·2+3` at some cell `Sig₀`, has a full-scope controller `U` of the grade of `Sig₀`, labelled
`≥ ω·2+3`, whose row reads a strictly smaller source at the old occurrence than at the copy. -/
theorem exists_separating_controller {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 3) {sem : Semantics D₂}
    {q : D₂.below (Finset.univ, j) → ExtOrd} (hq : RespectsSemanticsBelow sem (Finset.univ, j) q)
    (h₀ : q ⟨H₀old, memA hj1⟩ = γ₀) (h₁ : q ⟨H₀new, memB hj1⟩ = γ₁)
    (Sig₀ : D₂.below (Finset.univ, j)) (hSig₀ : γ₁ ≤ q Sig₀) :
    ∃ (U : D₂.below (Finset.univ, j)) (hA : GradedLe (D₂.cell H₀old) (D₂.cell U.1))
      (hB : GradedLe (D₂.cell H₀new) (D₂.cell U.1)),
      D₂.cell U.1 = (Finset.univ, D₂.grade Sig₀.1) ∧ γ₁ ≤ q U ∧
      sem.E U.1 ⟨H₀old, hA⟩ < sem.E U.1 ⟨H₀new, hB⟩ := by
  obtain ⟨c, hc⟩ := exists_full_cell (D₂.grade_pos Sig₀.1)
    ((Sig₀.2.2.trans hj).trans (by decide))
  have hcmem : GradedLe (D₂.cell c) (Finset.univ, j) := by
    rw [hc]; exact ⟨Finset.subset_univ _, Sig₀.2.2⟩
  obtain ⟨U, hU, hle⟩ := hq.availability Sig₀ ⟨c, hcmem⟩
    (by change D₂.scope Sig₀.1 ⊆ (D₂.cell c).1; rw [hc]; exact Finset.subset_univ _)
    (by change (D₂.cell Sig₀.1).2 = (D₂.cell c).2; rw [hc]; rfl)
  have hUc : D₂.cell U.1 = (Finset.univ, D₂.grade Sig₀.1) := hU.trans hc
  have hA : GradedLe (D₂.cell H₀old) (D₂.cell U.1) := by
    rw [hUc]
    exact ⟨Finset.subset_univ _, by
      change D₂.grade H₀old ≤ _; rw [grade_H₀old]; exact D₂.grade_pos _⟩
  have hB : GradedLe (D₂.cell H₀new) (D₂.cell U.1) := by
    rw [hUc]
    exact ⟨Finset.subset_univ _, by
      change D₂.grade H₀new ≤ _; rw [grade_H₀new]; exact D₂.grade_pos _⟩
  have hqU : γ₁ ≤ q U := hSig₀.trans hle
  refine ⟨U, hA, hB, hUc, hqU, ?_⟩
  refine hq.lt_of_probe_lt U ⟨H₀old, hA⟩ ⟨H₀new, hB⟩ (by rw [grade_H₀old, grade_H₀new]) ?_
  rw [incl_H₀old hj1, incl_H₀new hj1, h₀, h₁, min_eq_left (γ₀_lt_γ₁.le.trans hqU),
    min_eq_left hqU]
  exact γ₀_lt_γ₁

/-- **Controllers reading equal sources are bounded by `ω+4`**: no such controller can dominate a
B-face label `ω·2+3`. -/
theorem le_γ₀_of_row_eq {j : ℕ} (hj1 : 1 ≤ j) {sem : Semantics D₂}
    {q : D₂.below (Finset.univ, j) → ExtOrd} (hq : RespectsSemanticsBelow sem (Finset.univ, j) q)
    (h₀ : q ⟨H₀old, memA hj1⟩ = γ₀) (h₁ : q ⟨H₀new, memB hj1⟩ = γ₁)
    (U : D₂.below (Finset.univ, j)) (hA : GradedLe (D₂.cell H₀old) (D₂.cell U.1))
    (hB : GradedLe (D₂.cell H₀new) (D₂.cell U.1))
    (hrow : sem.E U.1 ⟨H₀old, hA⟩ = sem.E U.1 ⟨H₀new, hB⟩) : q U ≤ γ₀ := by
  have := hq.le_of_row_eq U ⟨H₀old, hA⟩ ⟨H₀new, hB⟩ hrow (by rw [grade_H₀old, grade_H₀new])
    (by rw [incl_H₀old hj1, incl_H₀new hj1, h₀, h₁]; exact γ₀_lt_γ₁)
  rw [incl_H₀old hj1, h₀] at this
  exact this

/-! ### The specified pair: input B's labels on the fresh face force separation at every grade -/

theorem p₁_label_s₀ : p₁.label (family₁.e s₀X₁) = γ₁ := by rw [p₁_label, embX₁_s₀, rowX_b₁_s]
theorem p₁_label_b₁ : p₁.label (family₁.e b₁X₁) = γ₁ := by rw [p₁_label, embX₁_b₁, rowX_b₁_b₁]

/-- A labelling of the full grade-three lower set **realizes the specified pair** when it reads
input A's labels on the A face and input B's labels on the fresh face. -/
structure RealizesPair (q : D₂.below (Finset.univ, 3) → ExtOrd) : Prop where
  faceA : ∀ i : Cell C₀, q ⟨Fin.castAdd (Fintype.card New₂) i, memA' i⟩ = p₀.label i
  faceB : ∀ c : Cell C₁, q ⟨copyB c, memB' c⟩ = p₁.label c

theorem RealizesPair.at_H₀old {q} (hq : RealizesPair q) : q ⟨H₀old, memA (by decide)⟩ = γ₀ :=
  (hq.faceA (family₀.e H₀X₀)).trans p₀_label_H₀
theorem RealizesPair.at_H₀new {q} (hq : RealizesPair q) : q ⟨H₀new, memB (by decide)⟩ = γ₁ :=
  (hq.faceB (family₁.e H₀X₁)).trans p₁_label_H₀
theorem RealizesPair.at_s₀new {q} (hq : RealizesPair q) : q ⟨s₀new, memB' _⟩ = γ₁ :=
  (hq.faceB (family₁.e s₀X₁)).trans p₁_label_s₀
theorem RealizesPair.at_b₁new {q} (hq : RealizesPair q) : q ⟨b₁new, memB' _⟩ = γ₁ :=
  (hq.faceB (family₁.e b₁X₁)).trans p₁_label_b₁

/-- **Every grade must separate**: a semantics on the glued domain realizing the specified pair
by a respecting labelling has, at each grade `i ∈ {1, 2, 3}`, a full-scope controller of grade
`i` labelled `≥ ω·2+3` whose row reads a strictly smaller source at `H₀old` than at `H₀new`. -/
theorem separating_controllers_of_realizes {sem : Semantics D₂}
    {q : D₂.below (Finset.univ, 3) → ExtOrd} (hq : RespectsSemanticsBelow sem (Finset.univ, 3) q)
    (hpair : RealizesPair q) :
    ∀ i ∈ ({1, 2, 3} : Finset ℕ),
      ∃ (U : D₂.below (Finset.univ, 3)) (hA : GradedLe (D₂.cell H₀old) (D₂.cell U.1))
        (hB : GradedLe (D₂.cell H₀new) (D₂.cell U.1)),
        D₂.cell U.1 = (Finset.univ, i) ∧ γ₁ ≤ q U ∧
        sem.E U.1 ⟨H₀old, hA⟩ < sem.E U.1 ⟨H₀new, hB⟩ := by
  intro i hi
  have key := fun (Sig₀ : D₂.below (Finset.univ, 3)) (hSig₀ : γ₁ ≤ q Sig₀) =>
    exists_separating_controller (by decide) le_rfl hq hpair.at_H₀old hpair.at_H₀new Sig₀ hSig₀
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · have := key ⟨H₀new, memB (by decide)⟩ hpair.at_H₀new.ge
    rwa [grade_H₀new] at this
  · have := key ⟨s₀new, memB' _⟩ hpair.at_s₀new.ge
    rwa [grade_s₀new] at this
  · have := key ⟨b₁new, memB' _⟩ hpair.at_b₁new.ge
    rwa [grade_b₁new] at this

/-- **The no-go, for every semantics with pulled-back grade-one controllers**: if every full-scope
controller of grade one reads equal sources at the two occurrences, the specified pair is
realized by no respecting labelling (the fixed glue `rows₂` is the special case). -/
theorem not_realizable_of_grade_one_pullback {sem : Semantics D₂}
    (hpull : ∀ U : Cell D₂, D₂.cell U = (Finset.univ, 1) →
      ∀ (hA : GradedLe (D₂.cell H₀old) (D₂.cell U)) (hB : GradedLe (D₂.cell H₀new) (D₂.cell U)),
      sem.E U ⟨H₀old, hA⟩ = sem.E U ⟨H₀new, hB⟩) :
    ¬ ∃ q : D₂.below (Finset.univ, 3) → ExtOrd,
      RespectsSemanticsBelow sem (Finset.univ, 3) q ∧ RealizesPair q := by
  rintro ⟨q, hq, hpair⟩
  obtain ⟨U, hA, hB, hU, -, hlt⟩ :=
    separating_controllers_of_realizes hq hpair 1 (by decide)
  exact absurd (hpull U.1 hU hA hB) hlt.ne

theorem rows₂_grade_one_pullback (U : Cell D₂) (hU : D₂.cell U = (Finset.univ, 1))
    (hA : GradedLe (D₂.cell H₀old) (D₂.cell U)) (hB : GradedLe (D₂.cell H₀new) (D₂.cell U)) :
    rows₂.E U ⟨H₀old, hA⟩ = rows₂.E U ⟨H₀new, hB⟩ := by
  have hm : ¬ mute₂ U := by
    intro h
    change D₂.cell U = _ at h
    rw [hU] at h
    exact absurd (congrArg Prod.snd h) (by decide)
  exact (rows₂_E_of_not_mute hm _).trans
    ((family₂.rows.E_congr' rfl ret₂_castAdd_H₀).trans (rows₂_E_of_not_mute hm _).symm)

/-- The fixed glue's no-go, recovered from the general one. -/
theorem not_realizable_rows₂ :
    ¬ ∃ q : D₂.below (Finset.univ, 3) → ExtOrd,
      RespectsSemanticsBelow rows₂ (Finset.univ, 3) q ∧ RealizesPair q :=
  not_realizable_of_grade_one_pullback rows₂_grade_one_pullback

end Separating

/-! ## The separating row at the grade-one full controller: the local test -/

section Construction

theorem cell_e₂_H₀ : C₂.cell (family₂.e H₀X) = (Finset.univ, 1) := Family.cell_e _ _

/-- **The grade-one full-scope controller**: the fresh full copy of the level-one witness cell
(the unique cell of `D₂` with graded index `(univ, 1)` reached by the glue). -/
noncomputable def U_H : Cell D₂ :=
  Fin.natAdd C₀.card ((Fintype.equivFin New₂) (.inr (.inl ⟨family₂.e H₀X, by
    change (C₂.cell (family₂.e H₀X)).1 = _; rw [cell_e₂_H₀]⟩)))

theorem cell_U_H : D₂.cell U_H = (Finset.univ, 1) := by
  unfold U_H
  rw [D₂_cell_natAdd, Equiv.symm_apply_apply]
  change (Finset.univ, (C₂.cell (family₂.e H₀X)).2) = _
  rw [cell_e₂_H₀]

theorem grade_U_H : D₂.grade U_H = 1 := by change (D₂.cell U_H).2 = 1; rw [cell_U_H]

theorem ret₂_U_H : ret₂ U_H = family₂.e H₀X := by
  unfold U_H; rw [ret₂_natAdd, Equiv.symm_apply_apply]; rfl

theorem not_mute_U_H : ¬ mute₂ U_H := by
  intro h
  change D₂.cell U_H = _ at h
  rw [cell_U_H] at h
  exact absurd (congrArg Prod.snd h) (by decide)

theorem ret₂_H₀old : ret₂ H₀old = family₂.e H₀X := by
  unfold H₀old
  rw [ret₂_castAdd]
  change family₂.e (embX₀ (family₀.e.symm (family₀.e H₀X₀))) = _
  rw [Equiv.symm_apply_apply, embX₀_H₀]

theorem ret₂_H₀new : ret₂ H₀new = family₂.e H₀X := by
  unfold H₀new
  rw [ret₂_copyB]
  change family₂.e (embX₁ (family₁.e.symm (family₁.e H₀X₁))) = _
  rw [Equiv.symm_apply_apply, embX₁_H₀]

theorem memA_U : GradedLe (D₂.cell H₀old) (D₂.cell U_H) := by rw [cell_U_H]; exact memA le_rfl
theorem memB_U : GradedLe (D₂.cell H₀new) (D₂.cell U_H) := by rw [cell_U_H]; exact memB le_rfl
theorem refl_U : GradedLe (D₂.cell U_H) (D₂.cell U_H) := GradedLe.refl _

/-- The pulled-back rows of the controller and of the copy both read the level-one witness's row
at the retraction. -/
theorem rows₂_U_H_eq (d : D₂.below (D₂.cell U_H)) :
    rows₂.E U_H d = family₂.rowX H₀X (family₂.e.symm (ret₂ d.1)) := by
  refine (rows₂_E_of_not_mute not_mute_U_H d).trans ?_
  change family₂.rowX (family₂.e.symm (ret₂ U_H)) (family₂.e.symm (ret₂ d.1)) = _
  rw [ret₂_U_H, Equiv.symm_apply_apply]

theorem not_mute_H₀new : ¬ mute₂ H₀new := not_mute_copyB _

theorem rows₂_H₀new_eq (d : D₂.below (D₂.cell H₀new)) :
    rows₂.E H₀new d = family₂.rowX H₀X (family₂.e.symm (ret₂ d.1)) := by
  refine (rows₂_E_of_not_mute not_mute_H₀new d).trans ?_
  change family₂.rowX (family₂.e.symm (ret₂ H₀new)) (family₂.e.symm (ret₂ d.1)) = _
  rw [ret₂_H₀new, Equiv.symm_apply_apply]

theorem rowX_H₀X_H₀X : family₂.rowX H₀X H₀X = H₀c.δ := meet₁_self _

/-- The witness row is bounded by its diagonal `δ`. -/
theorem rowX_H₀X_le (y : family₂.X) : family₂.rowX H₀X y ≤ H₀c.δ := by
  rcases y with c | H | s | a
  · by_cases hc : c.gradeP ≤ 1
    · rw [family₂.rowX_H_inl _ c hc]; exact H₀c.G_le c
    · change H₀c.row (if h : c.gradeP ≤ 1 then Sum.inl ⟨c, h⟩ else Sum.inr family₂.H₀) ≤ _
      rw [dite_of_neg hc]
      exact (meet₁_le _ _).trans (min_le_left _ _)
  · exact (meet₁_le _ _).trans (min_le_left _ _)
  · exact (meet₁_le _ _).trans (min_le_left _ _)
  · exact (meet₁_le _ _).trans (min_le_left _ _)

theorem rows₂_U_H_H₀old : rows₂.E U_H ⟨H₀old, memA_U⟩ = H₀c.δ := by
  refine (rows₂_U_H_eq ⟨H₀old, memA_U⟩).trans ?_
  change family₂.rowX H₀X (family₂.e.symm (ret₂ H₀old)) = _
  rw [ret₂_H₀old, Equiv.symm_apply_apply]; exact rowX_H₀X_H₀X

theorem rows₂_U_H_H₀new : rows₂.E U_H ⟨H₀new, memB_U⟩ = H₀c.δ := by
  refine (rows₂_U_H_eq ⟨H₀new, memB_U⟩).trans ?_
  change family₂.rowX H₀X (family₂.e.symm (ret₂ H₀new)) = _
  rw [ret₂_H₀new, Equiv.symm_apply_apply]; exact rowX_H₀X_H₀X

/-! ### The values: the cap code `ω·(k+1)+1`, the separating value `ω·(k+1)+2`, the cutoff -/

/-- The number of keys of the level-one code of `t₀`'s row. -/
noncomputable abbrev kSep : ℕ := (keys 1 (valuesAt Prop3.gradeP t₀.F 1)).card
/-- The limit below the cap code. -/
noncomputable abbrev limSep : Ordinal.{0} := Ordinal.omega0 * ((kSep + 1 : ℕ) : Ordinal)
/-- **The separating value** `ω·(k+1) + 2`: the successor of the cap code. -/
noncomputable def wSep : ExtOrd := ofOrd (limSep + ((2 : ℕ) : Ordinal))
/-- **The cutoff** `ω·k + 2`: strictly above every proper-cell code, strictly below the cap
code, with finite part `2 > 1`. -/
noncomputable abbrev cutSep : Ordinal.{0} :=
  Ordinal.omega0 * ((kSep : ℕ) : Ordinal) + ((2 : ℕ) : Ordinal)

theorem H₀c_δ_eq : H₀c.δ = ofOrd (limSep + ((1 : ℕ) : Ordinal)) := rfl

theorem δ_lt_wSep : H₀c.δ < wSep := by
  rw [H₀c_δ_eq]
  exact ofOrd_lt_ofOrd.mpr (add_lt_add_right (Nat.cast_lt.mpr (by decide)) _)

theorem δ_le_wSep : H₀c.δ ≤ wSep := δ_lt_wSep.le

theorem cutSep_le_δ : ofOrd cutSep ≤ H₀c.δ := by
  rw [H₀c_δ_eq, ofOrd_le_ofOrd]
  calc Ordinal.omega0 * ((kSep : ℕ) : Ordinal) + ((2 : ℕ) : Ordinal)
      ≤ Ordinal.omega0 * ((kSep : ℕ) : Ordinal) + Ordinal.omega0 :=
        add_le_add_right (Ordinal.natCast_lt_omega0 2).le _
    _ = limSep := by unfold limSep; rw [Nat.cast_add_one, mul_add_one]
    _ ≤ limSep + ((1 : ℕ) : Ordinal) := le_self_add

theorem H₀c_G_eq {c : Prop3} (hc : c.gradeP ≤ 1) :
    H₀c.G c = ofOrd (code 1 (valuesAt Prop3.gradeP t₀.F 1)
      (Ordinal.omega0 * ((1 : ℕ) : Ordinal) + ((1 : ℕ) : Ordinal))) := by
  change witnessRow Prop3.gradeP t₀.F 1 _ c = _
  exact witnessRow_ofOrd Prop3.gradeP hc (show t₀.F c = ofOrd _ from by
    change (if c.gradeP ≤ 1 then v₀ else ⊥) = _
    rw [ite_eq_left hc]; rfl)

theorem code_lt_cutSep (v : Ordinal.{0}) : code 1 (valuesAt Prop3.gradeP t₀.F 1) v < cutSep := by
  unfold code
  calc Ordinal.omega0 * ((blockOf 1 (valuesAt Prop3.gradeP t₀.F 1) v : ℕ) : Ordinal) +
        ((min (finitePart v) 1 : ℕ) : Ordinal)
      ≤ Ordinal.omega0 * ((kSep : ℕ) : Ordinal) + ((1 : ℕ) : Ordinal) :=
        add_le_add (mul_le_mul_right (Nat.cast_le.mpr (blockOfKey_le _ _ _)) _)
          (Nat.cast_le.mpr (min_le_right _ _))
    _ < cutSep := add_lt_add_right (Nat.cast_lt.mpr (by decide)) _

theorem G_lt_cutSep {c : Prop3} (hc : c.gradeP ≤ 1) : H₀c.G c < ofOrd cutSep := by
  rw [H₀c_G_eq hc]; exact ofOrd_lt_ofOrd.mpr (code_lt_cutSep _)

theorem G_le_wSep (c : Prop3) : H₀c.G c ≤ wSep := (H₀c.G_le c).trans δ_le_wSep

theorem wSep_selfVis : SelfVis 1 wSep :=
  selfVis_ofOrd_iff.mpr (by rw [finitePart_mul_add]; omega)

/-! ### Distinctness of the three cells -/

theorem zero_mem_scope_H₀old : (0 : Fin 4) ∈ D₂.scope H₀old := by
  unfold H₀old
  rw [D₂_scope_castAdd, Family.scope_eq, Equiv.symm_apply_apply]
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

theorem three_not_mem_scope_H₀old : (3 : Fin 4) ∉ D₂.scope H₀old := by
  unfold H₀old
  rw [D₂_scope_castAdd]
  intro h
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp h
  exact absurd hx (Fin.ne_of_lt (Fin.castSucc_lt_last x))

theorem zero_not_mem_scope_H₀new : (0 : Fin 4) ∉ D₂.scope H₀new := fun h =>
  absurd ((copyB_mem _).1 h) (by decide)

theorem H₀old_ne_H₀new : H₀old ≠ H₀new := fun h =>
  zero_not_mem_scope_H₀new (h ▸ zero_mem_scope_H₀old)

theorem H₀old_ne_U_H : H₀old ≠ U_H := fun h => by
  apply three_not_mem_scope_H₀old
  rw [h]
  change (3 : Fin 4) ∈ (D₂.cell U_H).1
  rw [cell_U_H]; exact Finset.mem_univ _

/-! ### The cells below the copy -/

theorem below_H₀new_mem (d : D₂.below (D₂.cell H₀new)) :
    GradedLe (D₂.cell d.1) (({1, 2, 3} : Finset (Fin 4)), 1) :=
  ⟨d.2.1.trans (copyB_mem _).1, d.2.2.trans grade_H₀new.le⟩

/-- A cell below the copy is the copy itself or a proper cell of grade at most one (read at a
proper cell of the three-cell family). -/
theorem below_H₀new_cases (d : D₂.below (D₂.cell H₀new)) :
    d.1 = H₀new ∨ ∃ c : Prop3, c.gradeP ≤ 1 ∧ family₂.e.symm (ret₂ d.1) = .inl c := by
  have hr := ret₂_eq_emb₁_retB zero_not_mem_B ⟨d.1, below_H₀new_mem d⟩
  have hcell := cell_retB zero_not_mem_B ⟨d.1, below_H₀new_mem d⟩
  have h2 : C₁.grade (retB d.1) = D₂.grade d.1 := congrArg Prod.snd hcell
  have h3 : D₂.grade d.1 ≤ 1 := (below_H₀new_mem d).2
  rcases img_cases (family₁.e.symm (retB d.1)) with ⟨c, hc⟩ | hc | hc | hc
  · right
    refine ⟨c, ?_, ?_⟩
    · have h1 : C₁.grade (retB d.1) = c.gradeP := by rw [Family.grade_eq, hc]; rfl
      omega
    · rw [hr]
      change family₂.e.symm (family₂.e (embX₁ (family₁.e.symm (retB d.1)))) = _
      rw [Equiv.symm_apply_apply, hc]; rfl
  · left
    have h1 : retB d.1 = family₁.e H₀X₁ := by rw [← hc, Equiv.apply_symm_apply]
    have := retB_inj zero_not_mem_B ⟨d.1, below_H₀new_mem d⟩
      ⟨H₀new, ⟨(copyB_mem _).1, grade_H₀new.le⟩⟩ (h1.trans (retB_copyB _).symm)
    exact congrArg Subtype.val this
  · exfalso
    have h1 : C₁.grade (retB d.1) = 2 := by rw [Family.grade_eq, hc]; rfl
    omega
  · exfalso
    have h1 : C₁.grade (retB d.1) = 3 := by rw [Family.grade_eq, hc]; rfl
    omega

/-! ### The separating row -/

/-- **The request-dependent row at the grade-one full controller**: the separating value at the
copy and at the diagonal, the pulled-back row elsewhere (both input faces untouched). -/
noncomputable def row₃ (d : D₂.below (D₂.cell U_H)) : ExtOrd :=
  if d.1 = H₀new ∨ d.1 = U_H then wSep else rows₂.E U_H d

theorem row₃_of_eq (d : D₂.below (D₂.cell U_H)) (h : d.1 = H₀new ∨ d.1 = U_H) :
    row₃ d = wSep := by
  unfold row₃; rw [ite_eq_left h]
theorem row₃_of_ne (d : D₂.below (D₂.cell U_H)) (h₁ : d.1 ≠ H₀new) (h₂ : d.1 ≠ U_H) :
    row₃ d = rows₂.E U_H d := by
  unfold row₃; rw [ite_eq_right (by rintro (h | h); exacts [h₁ h, h₂ h])]

theorem row₃_H₀new : row₃ ⟨H₀new, memB_U⟩ = wSep := row₃_of_eq _ (Or.inl rfl)
theorem row₃_diag : row₃ ⟨U_H, refl_U⟩ = wSep := row₃_of_eq _ (Or.inr rfl)
theorem row₃_H₀old : row₃ ⟨H₀old, memA_U⟩ = H₀c.δ :=
  (row₃_of_ne _ H₀old_ne_H₀new H₀old_ne_U_H).trans rows₂_U_H_H₀old

/-- **The row separates the two occurrences.** -/
theorem row₃_separates : row₃ ⟨H₀old, memA_U⟩ < row₃ ⟨H₀new, memB_U⟩ := by
  rw [row₃_H₀old, row₃_H₀new]; exact δ_lt_wSep

/-- **Row availability at the diagonal**: every entry is dominated by the diagonal. -/
theorem row₃_le_diag (d : D₂.below (D₂.cell U_H)) : row₃ d ≤ row₃ ⟨U_H, refl_U⟩ := by
  rw [row₃_diag]
  unfold row₃
  split_ifs
  · exact le_rfl
  · rw [rows₂_U_H_eq]; exact (rowX_H₀X_le _).trans δ_le_wSep

/-- **Orderly.** -/
theorem row₃_orderly : IsOrderly (fun d : D₂.below (D₂.cell U_H) => D₂.grade d.1) row₃ := by
  intro d
  unfold row₃
  split_ifs with h
  · have hg : D₂.grade d.1 = 1 := by
      rcases h with h | h
      · rw [h]; exact grade_H₀new
      · rw [h]; exact grade_U_H
    dsimp only
    rw [hg]; exact wSep_selfVis.symm
  · exact rows₂.orderly U_H d

/-- **Coded at the controller's grade.** -/
theorem row₃_coded (d : D₂.below (D₂.cell U_H)) : IsCodedLabel (D₂.grade U_H) (row₃ d) := by
  unfold row₃
  split_ifs
  · rw [grade_U_H]; exact Or.inr ⟨kSep + 1, 2, by omega, rfl⟩
  · exact rows₂_isCoded U_H d

/-! ### The locality at the copy, witnessed by `Witness.raise` -/

/-- The trivial suppressor at grades `≤ 1` with the identity shifter. -/
theorem witness_id_top : Witness (fun k => if k ≤ 1 then (⊤ : ExtOrd) else ⊥) id where
  anti n m h := by
    split_ifs <;> first | exact le_rfl | exact bot_le | omega
  vis n := by
    split_ifs <;> rfl
  bot := rfl
  mono := monotone_id
  clause5 _ _ _ _ _ := rfl

/-- **The separating witness**: the identity raised to `ω·(k+1)+2` above the cutoff `ω·k+2`. -/
theorem witness_sep :
    Witness (fun k => if k ≤ 1 then (⊤ : ExtOrd) else ⊥) (raiseShifter id cutSep wSep) :=
  witness_id_top.raise 1 (fun k hk => by rw [ite_eq_right (by omega)])
    (by rw [finitePart_mul_add]; omega) wSep_selfVis

theorem ret_ne_of_inl {d : Cell D₂} {c : Prop3} (hc : family₂.e.symm (ret₂ d) = .inl c)
    (hr : ret₂ d = family₂.e H₀X) : False := by
  rw [hr, Equiv.symm_apply_apply] at hc
  change Sum.inr (Sum.inl _) = Sum.inl c at hc
  cases hc

/-- **The locality clause at the copy**: the copy's (unchanged, input-B) row transforms to the
separating row's probes, by the raised identity. -/
theorem locality_H₀new :
    TransformsTo (fun d : D₂.below (D₂.cell H₀new) => D₂.grade d.1) (rows₂.E H₀new)
      (fun d => min (row₃ (CellScheme.below.incl ⟨H₀new, memB_U⟩ d)) (row₃ ⟨H₀new, memB_U⟩)) := by
  refine witness_sep.transformsTo fun d => ?_
  have hg : D₂.grade d.1 ≤ 1 := (below_H₀new_mem d).2
  rw [ite_eq_left hg, min_eq_left le_top, row₃_H₀new]
  rcases below_H₀new_cases d with h | ⟨c, hc1, hc⟩
  · have e1 : row₃ (CellScheme.below.incl ⟨H₀new, memB_U⟩ d) = wSep := row₃_of_eq _ (Or.inl h)
    have e2 : rows₂.E H₀new d = H₀c.δ := by
      refine (rows₂_H₀new_eq d).trans ?_
      rw [h, ret₂_H₀new, Equiv.symm_apply_apply]; exact rowX_H₀X_H₀X
    rw [e1, e2, min_self, raiseShifter_of_ge cutSep_le_δ H₀c_δ_ne_bot]
    change wSep = max H₀c.δ wSep
    rw [max_eq_right δ_le_wSep]
  · have hne1 : d.1 ≠ H₀new := fun h => ret_ne_of_inl hc (by rw [h]; exact ret₂_H₀new)
    have hne2 : d.1 ≠ U_H := fun h => ret_ne_of_inl hc (by rw [h]; exact ret₂_U_H)
    have e1 : row₃ (CellScheme.below.incl ⟨H₀new, memB_U⟩ d) = H₀c.G c := by
      refine (row₃_of_ne _ hne1 hne2).trans ((rows₂_U_H_eq _).trans ?_)
      change family₂.rowX H₀X (family₂.e.symm (ret₂ d.1)) = _
      rw [hc]; exact family₂.rowX_H_inl _ c hc1
    have e2 : rows₂.E H₀new d = H₀c.G c := by
      refine (rows₂_H₀new_eq d).trans ?_
      rw [hc]; exact family₂.rowX_H_inl _ c hc1
    rw [e1, e2, min_eq_left (G_le_wSep c), raiseShifter_of_lt (G_lt_cutSep hc1)]
    rfl

/-- **The local test, banked**: an orderly row at the grade-one full controller, coded at its
grade, dominated by its diagonal, strictly separating the two occurrences of the level-one
witness, whose locality clause at the copy is witnessed — with both input faces untouched. -/
theorem separating_row_test :
    IsOrderly (fun d : D₂.below (D₂.cell U_H) => D₂.grade d.1) row₃ ∧
    (∀ d, IsCodedLabel (D₂.grade U_H) (row₃ d)) ∧
    (∀ d, row₃ d ≤ row₃ ⟨U_H, refl_U⟩) ∧
    row₃ ⟨H₀old, memA_U⟩ < row₃ ⟨H₀new, memB_U⟩ ∧
    TransformsTo (fun d : D₂.below (D₂.cell H₀new) => D₂.grade d.1) (rows₂.E H₀new)
      (fun d => min (row₃ (CellScheme.below.incl ⟨H₀new, memB_U⟩ d)) (row₃ ⟨H₀new, memB_U⟩)) :=
  ⟨row₃_orderly, row₃_coded, row₃_le_diag, row₃_separates, locality_H₀new⟩

end Construction

end VaughtConjecture.Knight
