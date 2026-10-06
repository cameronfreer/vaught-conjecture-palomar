/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CodedWitness
public import VaughtConjecture.Knight.AddFullScope

/-! # The two-level full-scope tower over a parameterized base

The **first constructed one-reference mixed family**: over an arbitrary base scheme `D₀` on `A`
whose cells all have proper scope (the union of a context and a request), with a consistent coded
base semantics `sem₀`, the tower adds

* at `(A, 1)` the **level-one members**: base labellings of the cells of grade `≤ 1` with values in
  the coded alphabet at grade one, respecting the base semantics, under a self-visible cap;
* at `(A, 2)` the **level-two members**: the same at grade two;
* at `(A, k)`, `k ≥ 3`, mute cells.

**The rows are actual functions of the members.**  A level-one row reads a base cell at the
member's own label and a sibling at their **level cap** (`levelCap`, the rounded agreement cap).
A level-two row reads a base cell at its label, a sibling at the level cap of their **full
decoded vectors** (`fullVec`), and a level-one cell through its **owned witness** — the counted
recoding of its grade-`≤ 1` part (`Member.witness`) — decoded by `shift` (`Member.dec`): the
factorization equation (13) of `Knight/RowFactorization.lean` holds by construction
(`factor_base`, `factor_new`).

**Proved from those rows** (no legality or factorization record is assumed), in this module and
its two sequels:
* orderliness of every row (`rowOf_orderly`, here);
* **incoming localities** of every new row at every lower controller — at base controllers from
  the member's respect, at level-one controllers from a level-two row by `Factorization.locality`
  with the same-grade meet agreement (14) supplied by the level-one cap identities, at siblings by
  the capped ultrametric identity `min_levelCap_eq` (`Knight/GradeTwoConsistency.lean`);
* **availability** toward both full-scope indices, by the member itself and by its owned witness,
  hence **consistency** of every new row and of the whole semantics (`towerSem_consistent`),
  **codedness** (`towerSem_isCoded`) and **completeness** (`tower_complete`)
  (`Knight/GradeTwoAvailability.lean`);
* the **intended section** and the **cutoff forcing at the display's controller**
  (`Knight/GradeTwoCutoff.lean`).

The level-two family carries a **thinning parameter** `P` (the field `Member.sel`): every result
holds for every family predicate, and `Knight/GradeTwoForcing.lean` thins to the cutoff-correct
members to force the readback through the availability witness actually used.

**Not proved**: bountifulness of the tower (the designated-display lifting obstruction of
`Knight/GradeTwoForcing.lean` is conditional on activating the display; the literal clause is
tested in `Knight/GradeTwoBountifulTest.lean`).  Coverage: bases mute above grade
two (or with `|A| = 2`), two full-scope levels; the third level needs the coherent iteration of
the counted recoding (16).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}

/-! ## Members -/

/-- A **level-`k` member**: a base labelling of the cells of grade `≤ k` with values in the coded
alphabet at grade `k`, respecting the base semantics, dominated by a self-visible alphabet cap. -/
structure Member (sem₀ : Semantics D₀) (I k : ℕ) (P : (BaseCells D₀ k → ExtOrd) → Prop) where
  /-- The base labelling. -/
  F : BaseCells D₀ k → ExtOrd
  /-- The cap. -/
  γ : ExtOrd
  /-- The labels lie in the alphabet. -/
  F_mem : ∀ d, F d ∈ alph k I
  /-- The cap lies in the alphabet. -/
  γ_mem : γ ∈ alph k I
  /-- The cap is self-visible at `k`. -/
  γ_vis : SelfVis k γ
  /-- The labels are under the cap. -/
  le_cap : ∀ d, F d ≤ γ
  /-- The labelling respects the base semantics. -/
  respects : RespectsBase sem₀ k F
  /-- The labelling is selected by the family predicate `P` (the thinning parameter). -/
  sel : P F

namespace Member

variable {sem₀ : Semantics D₀} {I k : ℕ} {P : (BaseCells D₀ k → ExtOrd) → Prop}

theorem ext {m m' : Member sem₀ I k P} (hF : m.F = m'.F) (hγ : m.γ = m'.γ) : m = m' := by
  obtain ⟨F, γ, _, _, _, _, _, _⟩ := m
  obtain ⟨F', γ', _, _, _, _, _, _⟩ := m'
  dsimp only at hF hγ
  subst hF hγ
  rfl

/-- The member as a pair of alphabet-valued data. -/
def toData (m : Member sem₀ I k P) : (BaseCells D₀ k → {x // x ∈ alph k I}) × {x // x ∈ alph k I} :=
  (fun d => ⟨m.F d, m.F_mem d⟩, ⟨m.γ, m.γ_mem⟩)

theorem toData_injective :
    Function.Injective (toData (sem₀ := sem₀) (I := I) (k := k) (P := P)) := by
  intro m m' h
  refine Member.ext (funext fun d => ?_) ?_
  · exact congrArg Subtype.val (congrFun (congrArg Prod.fst h) d)
  · exact congrArg Subtype.val (congrArg Prod.snd h)

noncomputable instance : Fintype (Member sem₀ I k P) :=
  Fintype.ofInjective _ toData_injective

end Member

/-- The **level-one members**: unthinned (`P` trivial). -/
abbrev Member₁ (sem₀ : Semantics D₀) (I : ℕ) : Type 1 := Member sem₀ I 1 (fun _ => True)

namespace Member

variable {sem₀ : Semantics D₀} {I k : ℕ} {P : (BaseCells D₀ k → ExtOrd) → Prop}

/-- The **bottom member**. -/
def bot (sem₀ : Semantics D₀) (I k : ℕ) : Member sem₀ I k (fun _ => True) where
  F _ := ⊥
  γ := ⊥
  F_mem _ := bot_mem_alph _ _
  γ_mem := bot_mem_alph _ _
  γ_vis := selfVis_bot _
  le_cap _ := le_rfl
  respects := respectsBase_bot sem₀ k
  sel := trivial

theorem F_ne_top (m : Member sem₀ I k P) (d : BaseCells D₀ k) : m.F d ≠ ⊤ :=
  ne_top_of_mem_alph (m.F_mem d)

theorem F_isCoded (m : Member sem₀ I k P) (d : BaseCells D₀ k) : IsCodedLabel k (m.F d) :=
  isCodedLabel_of_mem_alph (m.F_mem d)

end Member

namespace Member

variable {sem₀ : Semantics D₀} {I : ℕ} {P : (BaseCells D₀ 2 → ExtOrd) → Prop}

/-! ### The owned witness and the decoder of a level-two member -/

/-- The grade-`≤ 1` part of a level-two member. -/
def low (m : Member sem₀ I 2 P) : BaseCells D₀ 1 → ExtOrd := BaseCells.restrict (by omega) m.F

theorem low_apply (m : Member sem₀ I 2 P) (d : BaseCells D₀ 1) :
    m.low d = m.F ⟨d.1, d.2.trans (by omega)⟩ := rfl

theorem low_le_cap (m : Member sem₀ I 2 P) (d : BaseCells D₀ 1) : m.low d ≤ m.γ := by
  rw [low_apply]; exact m.le_cap _

theorem low_ne_top (m : Member sem₀ I 2 P) (d : BaseCells D₀ 1) : m.low d ≠ ⊤ := by
  rw [low_apply]; exact m.F_ne_top _

theorem low_isCoded (m : Member sem₀ I 2 P) (d : BaseCells D₀ 1) : IsCodedLabel 2 (m.low d) := by
  rw [low_apply]; exact m.F_isCoded _

theorem card_baseCells_le (k : ℕ) : Fintype.card (BaseCells D₀ k) ≤ Fintype.card (Cell D₀) :=
  Fintype.card_subtype_le _

/-- **The owned witness** at level one: the counted recoding of the grade-`≤ 1` part, capped at the
cap code. -/
noncomputable def witness (hI : Fintype.card (Cell D₀) + 2 ≤ I) (m : Member sem₀ I 2 P) :
    Member₁ sem₀ I where
  F d := encT 1 (baseRange m.low) (m.low d)
  γ := ofOrd (capCode 1 (baseRange m.low))
  F_mem d := encT_mem_alph ((Nat.add_le_add_right (card_baseCells_le 1) 2).trans hI) m.low d
    (m.low_ne_top _)
  γ_mem := capCode_mem_alph ((Nat.add_le_add_right (card_baseCells_le 1) 2).trans hI) m.low
  γ_vis := capCode_selfVis _ _
  le_cap d := by
    rcases ExtOrd.cases (m.low d) with hb | ht | ⟨v, hv⟩
    · rw [hb, encT_bot]; exact bot_le
    · exact absurd ht (m.low_ne_top _)
    · rw [hv, encT_ofOrd, encOrdK_eq_code]
      exact ofOrd_le_ofOrd.mpr (code_le_capCode _ _ _)
  respects := (m.respects.restrict (by omega)).encode
  sel := trivial

variable (hI : Fintype.card (Cell D₀) + 2 ≤ I)

theorem witness_F (m : Member sem₀ I 2 P) (d : BaseCells D₀ 1) :
    (m.witness hI).F d = encT 1 (baseRange m.low) (m.low d) := rfl

theorem witness_γ (m : Member sem₀ I 2 P) :
    (m.witness hI).γ = ofOrd (capCode 1 (baseRange m.low)) := rfl

theorem exists_of_mem_baseRange {l : ℕ} {F : BaseCells D₀ l → ExtOrd} {v : Ordinal.{0}}
    (hv : v ∈ baseRange F) : ∃ d, F d = ofOrd v := by
  unfold baseRange primRange at hv
  obtain ⟨d, -, hd⟩ := Finset.mem_biUnion.mp hv
  refine ⟨d, ?_⟩
  rcases ExtOrd.cases (F d) with hb | ht | ⟨w, hw⟩
  · rw [hb] at hd; exact absurd hd (Finset.notMem_empty _)
  · rw [ht] at hd; exact absurd hd (Finset.notMem_empty _)
  · rw [hw] at hd
    rw [hw, Finset.mem_singleton.mp hd]

theorem γ_vis_one (m : Member sem₀ I 2 P) : SelfVis 1 m.γ := selfVis_mono m.γ_vis (by omega)

theorem baseRange_le_cap (m : Member sem₀ I 2 P) : ∀ v ∈ baseRange m.low, ofOrd v ≤ m.γ := by
  intro v hv
  obtain ⟨d, hd⟩ := exists_of_mem_baseRange hv
  rw [← hd]
  exact m.low_le_cap d

/-- **The decoder** of a level-two member. -/
noncomputable def dec (m : Member sem₀ I 2 P) : ExtOrd → ExtOrd :=
  shift 1 (baseRange m.low) m.γ

/-- The decoder decodes the witness's labels to the member's labels. -/
theorem dec_witness (m : Member sem₀ I 2 P) (d : BaseCells D₀ 1) :
    m.dec ((m.witness hI).F d) = m.low d := by
  rw [witness_F]
  unfold dec
  rcases ExtOrd.cases (m.low d) with hb | ht | ⟨v, hv⟩
  · rw [hb, encT_bot, shift_bot]
  · exact absurd ht (m.low_ne_top _)
  · rw [hv, encT_ofOrd, encOrdK_eq_code]
    exact shift_code _ _ _ (mem_primRange_of_eq hv)

/-- The decoder sends the witness's cap to the member's cap. -/
theorem dec_witness_cap (m : Member sem₀ I 2 P) : m.dec (m.witness hI).γ = m.γ := by
  rw [witness_γ]
  exact shift_capCode _ _ _

theorem dec_le_cap (m : Member sem₀ I 2 P) {x : ExtOrd} (hx : x ≠ ⊤) : m.dec x ≤ m.γ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · unfold dec; rw [shift_bot]; exact bot_le
  · exact absurd rfl hx
  · exact shift_ofOrd_le_γ _ _ _ m.γ_vis_one m.baseRange_le_cap α

theorem dec_selfVis (m : Member sem₀ I 2 P) {x : ExtOrd} (hx : SelfVis 1 x) : SelfVis 1 (m.dec x) :=
  shift_selfVis_one _ m.γ_vis_one hx

theorem dec_isCoded (m : Member sem₀ I 2 P) (x : ExtOrd) : IsCodedLabel 2 (m.dec x) :=
  shift_isCoded_two _ (isCodedLabel_of_mem_alph m.γ_mem) (fun v hv => by
    obtain ⟨d, hd⟩ := exists_of_mem_baseRange hv
    rw [← hd]
    exact m.low_isCoded _) x

/-- The decoder as a `Decoder` under any cap. -/
noncomputable def decoder (m : Member sem₀ I 2 P) (c : ExtOrd) : Decoder 1 c :=
  shiftDecoder (baseRange m.low) m.γ_vis_one m.baseRange_le_cap c

theorem decoder_toFun (m : Member sem₀ I 2 P) (c : ExtOrd) : (m.decoder c).toFun = m.dec := rfl

end Member

/-! ## The family and the scheme -/

section Tower

variable (sem₀ : Semantics D₀) (I M : ℕ) (P : (BaseCells D₀ 2 → ExtOrd) → Prop)

/-- The **family**: the level-one members, the level-two members, and `M` mute cells at levels
`3, …, M + 2`. -/
abbrev Fam : Type 1 := Member₁ sem₀ I ⊕ (Member sem₀ I 2 P ⊕ Fin M)

/-- The level of a family member. -/
def lv : Fam sem₀ I M P → ℕ := Sum.elim (fun _ => 1) (Sum.elim (fun _ => 2) fun i => i.1 + 3)

/-- The number of new cells. -/
noncomputable def famCard : ℕ := Fintype.card (Fam sem₀ I M P)

/-- The member indexed by a new cell. -/
noncomputable def memOf (j : Fin (famCard sem₀ I M P)) : Fam sem₀ I M P :=
  (Fintype.equivFin (Fam sem₀ I M P)).symm j

/-- The index of a member. -/
noncomputable def idx (t : Fam sem₀ I M P) : Fin (famCard sem₀ I M P) :=
  Fintype.equivFin (Fam sem₀ I M P) t

@[simp] theorem memOf_idx (t : Fam sem₀ I M P) : memOf sem₀ I M P (idx sem₀ I M P t) = t :=
  Equiv.symm_apply_apply _ _

@[simp] theorem idx_memOf (j : Fin (famCard sem₀ I M P)) :
    idx sem₀ I M P (memOf sem₀ I M P j) = j :=
  Equiv.apply_symm_apply _ _

/-- The level of a new cell. -/
noncomputable def level (j : Fin (famCard sem₀ I M P)) : ℕ := lv sem₀ I M P (memOf sem₀ I M P j)

theorem level_idx (t : Fam sem₀ I M P) : level sem₀ I M P (idx sem₀ I M P t) = lv sem₀ I M P t := by
  unfold level; rw [memOf_idx]

theorem one_le_lv (t : Fam sem₀ I M P) : 1 ≤ lv sem₀ I M P t := by
  rcases t with _ | _ | _ <;> simp [lv]

theorem lv_le (t : Fam sem₀ I M P) : lv sem₀ I M P t ≤ M + 2 := by
  rcases t with _ | _ | i
  · simp [lv]
  · simp [lv]
  · simp only [lv, Sum.elim_inr]; omega

variable (hAk : ∀ k, 1 ≤ k → k ≤ M + 2 → (A, k) ∈ Plan.gradedPlan D₀.plan)

include hAk in
theorem hlevel (j : Fin (famCard sem₀ I M P)) : (A, level sem₀ I M P j) ∈ Plan.gradedPlan D₀.plan :=
  hAk _ (one_le_lv _ _ _ _ _) (lv_le _ _ _ _ _)

/-- **The tower scheme.** -/
noncomputable abbrev tower : CellScheme A := addFull D₀ (level sem₀ I M P) (hlevel sem₀ I M P hAk)

/-! ## The rows -/

variable (hI : Fintype.card (Cell D₀) + 2 ≤ I)

/-- The **full decoded vector** of a level-two member: its labels on the base cells of grade `≤ 2`
and its decoded readings of the level-one members. -/
noncomputable def fullVec (m : Member sem₀ I 2 P) : BaseCells D₀ 2 ⊕ Member₁ sem₀ I → ExtOrd :=
  Sum.elim m.F fun m' =>
    m.dec (levelCap 1 I (m.witness hI).F (m.witness hI).γ m'.F m'.γ)

/-- The reading of a level-two member at a level-one member: its decoded level cap with the owned
witness. -/
noncomputable def readOne (m : Member sem₀ I 2 P) (m' : Member₁ sem₀ I) : ExtOrd :=
  m.dec (levelCap 1 I (m.witness hI).F (m.witness hI).γ m'.F m'.γ)

theorem fullVec_inl (m : Member sem₀ I 2 P) (b : BaseCells D₀ 2) :
    fullVec sem₀ I P hI m (Sum.inl b) = m.F b := rfl

theorem fullVec_inr (m : Member sem₀ I 2 P) (m' : Member₁ sem₀ I) :
    fullVec sem₀ I P hI m (Sum.inr m') = readOne sem₀ I P hI m m' := rfl

/-- **The rows of the family**, on the lower set of each new cell, with the level as an explicit
parameter (so that a row can be computed once the member of a cell is identified). -/
noncomputable def rowOf : (t : Fam sem₀ I M P) → (k : ℕ) → lv sem₀ I M P t = k →
    addFull.LowerOf (D₀ := D₀) (level sem₀ I M P) k → ExtOrd
  | Sum.inl m, _, hk, Sum.inl b => m.F ⟨b.1, b.2.trans_eq hk.symm⟩
  | Sum.inl m, _, _, Sum.inr j' =>
      match memOf sem₀ I M P j'.1 with
      | Sum.inl m' => levelCap 1 I m.F m.γ m'.F m'.γ
      | Sum.inr _ => ⊥
  | Sum.inr (Sum.inl m), _, hk, Sum.inl b => m.F ⟨b.1, b.2.trans_eq hk.symm⟩
  | Sum.inr (Sum.inl m), _, _, Sum.inr j' =>
      match memOf sem₀ I M P j'.1 with
      | Sum.inl m' => readOne sem₀ I P hI m m'
      | Sum.inr (Sum.inl m') =>
          levelCap 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ
      | Sum.inr (Sum.inr _) => ⊥
  | Sum.inr (Sum.inr _), _, _, _ => ⊥

/-- The row of a new cell. -/
noncomputable def newRow (j : Fin (famCard sem₀ I M P)) :
    addFull.LowerOf (D₀ := D₀) (level sem₀ I M P) (level sem₀ I M P j) → ExtOrd :=
  rowOf sem₀ I M P hI (memOf sem₀ I M P j) (level sem₀ I M P j) rfl

/-- The row of a new cell, once its member is identified. -/
theorem newRow_eq {j : Fin (famCard sem₀ I M P)} {t : Fam sem₀ I M P}
    (hm : memOf sem₀ I M P j = t) :
    newRow sem₀ I M P hI j = rowOf sem₀ I M P hI t (level sem₀ I M P j) (by rw [← hm]; rfl) := by
  subst hm; rfl

theorem level_eq_of_memOf_inl {j : Fin (famCard sem₀ I M P)} {m : Member₁ sem₀ I}
    (h : memOf sem₀ I M P j = Sum.inl m) : level sem₀ I M P j = 1 := by
  unfold level; rw [h]; rfl

theorem level_eq_of_memOf_inr_inl {j : Fin (famCard sem₀ I M P)} {m : Member sem₀ I 2 P}
    (h : memOf sem₀ I M P j = Sum.inr (Sum.inl m)) : level sem₀ I M P j = 2 := by
  unfold level; rw [h]; rfl

theorem level_eq_of_memOf_inr_inr {j : Fin (famCard sem₀ I M P)} {i : Fin M}
    (h : memOf sem₀ I M P j = Sum.inr (Sum.inr i)) : level sem₀ I M P j = i.1 + 3 := by
  unfold level; rw [h]; rfl

/-- Every row is orderly. -/
theorem rowOf_orderly (t : Fam sem₀ I M P) (k : ℕ) (hk : lv sem₀ I M P t = k) :
    IsOrderly (addFull.lowerGrade (D₀ := D₀) (level sem₀ I M P) k)
      (rowOf sem₀ I M P hI t k hk) := by
  rintro (b | j')
  · rcases t with m | m | i
    · exact (m.respects.orderly _).symm
    · exact (m.respects.orderly _).symm
    · exact (extVisibilityReplace_bot _ _).symm
  · rcases t with m | m | i
    · change rowOf sem₀ I M P hI (Sum.inl m) k hk (Sum.inr j') =
        extVisibilityReplace (rowOf sem₀ I M P hI (Sum.inl m) k hk (Sum.inr j'))
          (level sem₀ I M P j'.1) (level sem₀ I M P j'.1)
      rcases hm : memOf sem₀ I M P j'.1 with m' | m'
      · rw [level_eq_of_memOf_inl sem₀ I M P hm]
        simp only [rowOf, hm]
        exact (levelCap_selfVis _ _ _ _ _ _).symm
      · simp only [rowOf, hm]
        exact (extVisibilityReplace_bot _ _).symm
    · change rowOf sem₀ I M P hI (Sum.inr (Sum.inl m)) k hk (Sum.inr j') =
        extVisibilityReplace (rowOf sem₀ I M P hI (Sum.inr (Sum.inl m)) k hk (Sum.inr j'))
          (level sem₀ I M P j'.1) (level sem₀ I M P j'.1)
      rcases hm : memOf sem₀ I M P j'.1 with m' | m' | i'
      · rw [level_eq_of_memOf_inl sem₀ I M P hm]
        simp only [rowOf, hm]
        exact (m.dec_selfVis (levelCap_selfVis _ _ _ _ _ _)).symm
      · rw [level_eq_of_memOf_inr_inl sem₀ I M P hm]
        simp only [rowOf, hm]
        exact (levelCap_selfVis _ _ _ _ _ _).symm
      · simp only [rowOf, hm]
        exact (extVisibilityReplace_bot _ _).symm
    · exact (extVisibilityReplace_bot _ _).symm

theorem newRow_orderly (j : Fin (famCard sem₀ I M P)) :
    IsOrderly (addFull.lowerGrade (D₀ := D₀) (level sem₀ I M P) (level sem₀ I M P j))
      (newRow sem₀ I M P hI j) :=
  rowOf_orderly sem₀ I M P hI (memOf sem₀ I M P j) _ rfl

variable (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A)

/-- **The tower semantics.** -/
noncomputable abbrev towerSem : Semantics (tower sem₀ I M P hAk) :=
  addFull.addFullSem (hlevel sem₀ I M P hAk) hproper sem₀ (newRow sem₀ I M P hI)
    (newRow_orderly sem₀ I M P hI)

end Tower

end VaughtConjecture.Knight
