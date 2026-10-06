/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model

/-! # Positive-arity domains: mute schemes and their one-point extension

PR 1 of #41.  `Knight.SemScheme` defines domains with their associated semantics (Def. 2.6.1)
but constructs only the empty one (`StageType.emptySemScheme`, arity 0).  This module builds
domains on plans of **every** arity, with a one-point extension whose face equation is the one
`Knight.Model` consumes (`ExtendsDomain`, `IsCoface`).

## The construction

* **Plans.**  `Plan.extendOnePlan P` is a plan on `Fin (n+1)` in which the initial segment
  `ι_{n,n+1} = Fin.castSuccEmb` is visible and whose restriction to it is `P`
  (`Plan.isPlan_extend_one`, transported to `Fin`; the face equation on plans is
  `Plan.image_castSucc_mem_extendOnePlan_iff`).
* **Cell schemes.**  `CellScheme.extendOne C` is the scheme on that plan whose cells are the
  cells of `C` (scopes pushed along `castSucc`; indices `Fin.castAdd`) followed by **one new
  cell for every graded pair `⟨B,j⟩ ∈ P̂'` with `n ∈ B`** (indices `Fin.natAdd`).  The old cells
  are exactly the cells visible through the initial face, in order, so the face restriction is
  `C` again — `CellScheme.restrictFace_extendOne`, a propositional equality proved by
  components (`CellScheme.ext_of_components`; no `HEq` receipts) — and completeness is
  preserved (`CellScheme.IsComplete.extendOne`).
* **Rows.**  The rows of the new cells are the crux of Knight's §4.3 ("how do we extend a
  bountiful semantics for which all sets `D^{A,k}` are empty to one in which they are not?",
  Defs 4.3.3–4.3.6: standard functions and efficient stacks, Lemma 4.3.20), and for a general
  `D` no cheap choice works: bountifulness (Def. 2.5.14) at `γ = −∞` demands that *every*
  labelling respecting `E⟨C,i⟩` extend to one respecting `E⟨B,j⟩` for `⟨C,i⟩ ≺ ⟨B,j⟩`, so the
  new cells must carry enough rows to accommodate every respecting labelling of the old ones
  — Knight's stacks are the paper's known route.  In particular the naive choice "new rows `−∞`"
  is **refuted** for every non-mute `D` (a prose argument recorded here, not a compiled theorem): a cell whose row is `−∞` on its own diagonal is forced to the label `−∞` by
  locality (`RespectsSemanticsBelow.eq_bot_of_mute`), and availability (Def. 2.5.4(2)) at
  the new scope `B ∋ n` then forces every old cell below `⟨B,j⟩` to `−∞` as well, so a non-`⊥`
  respecting labelling of `D⟨C,i⟩` has no extension.
  What is built here is therefore the **mute** semantics (`Semantics.mute`: every row
  constantly `−∞`, the last clause of Knight's Lemma 4.2.2 at every arity): its only respecting
  labelling is `−∞` (`RespectsSemantics.eq_bot_of_mute`), hence it is coded, consistent and
  bountiful for free (`SemScheme.mute`), and the mute one-point extension
  `SemScheme.muteExtendOne` of a mute domain is again mute with the face equation
  `SemScheme.restrictFace_muteExtendOne`: `D.muteExtendOne.restrictFace Fin.castSuccEmb _ = D` —
  the relation `ExtendsDomain p D` of `Knight.Model` asks for.  (For a non-mute `D`,
  `muteExtendOne` discards the old semantics and is *not* an extension of `D`; hence the name.)
  Precisely what is shown: **the all-`⊥` new-row construction cannot extend a non-mute domain.**
  Knight's stacks (§4.3) are the paper's known solution for the rows of the new cells; the
  obstruction does not show that stacks are the only possible solution.
* **Existence.**  `SemScheme.muteChain n` is the chain `D₀ ⊂ D₁ ⊂ ⋯` of mute domains from the
  empty one, so `Nonempty (SemScheme n)` for every `n` (`SemScheme.nonempty`).

## Stage types

* `StageType.ofScheme` is Knight's Prop. 4.3.24 in full generality: **every** domain `D` on
  `Fin (n+1)` carries a stage type at every limit stage `α` — the row of a full-grade cell
  `Σ ∈ D^{A,|A|}` (completeness), which respects `E⟨A,|A|⟩ = E` by consistency
  (`RespectsSemanticsBelow.toRespects`), reduced to stage `α` (`RespectsSemantics.truncate`).
  Hence `Nonempty (S α n)` for every `n` at every limit stage (`StageType.nonempty`).
* `StageType.mute` is the (unique) stage type on a mute domain at any stage, and
  `StageType.exists_isCoface_of_isMute`: every stage type on a mute domain has a coface
  (Def. 3.2.1(4)), on the one-point extension of its domain; hence an extension domain in the
  sense of `ExtendsDomain` (`StageType.exists_extendsDomain_of_isMute`).  The coface for a
  stage type on a **general** domain is Knight's Prop. 4.3.23, which rests on Cor. 4.3.22 /
  Lemma 4.3.21 / Lemma 4.3.19 (the §4.3 completion; Lemma 4.3.19 is a recorded proof-gap,
  `docs/CONCORDANCE.md` §4) — not built here, and not obtainable by any choice of `−∞` rows
  on the new cells (see above). -/

@[expose] public section

namespace VaughtConjecture.Knight

open VaughtConjecture.AmalgamationPlan
open Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap)

/-! ### Extensionality by components -/

/-- Two cell schemes are equal when their plans, sizes and cells agree, the cells of the
first read through `Fin.cast` (so no `HEq` on the cell function). -/
theorem CellScheme.ext_of_components {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {D₁ D₂ : CellScheme A} (h_plan : D₁.plan = D₂.plan) (h_card : D₁.card = D₂.card)
    (h_cell : ∀ i, D₁.cell (Fin.cast h_card.symm i) = D₂.cell i) : D₁ = D₂ := by
  obtain ⟨P₁, ip₁, c₁, cl₁, cm₁⟩ := D₁
  obtain ⟨P₂, ip₂, c₂, cl₂, cm₂⟩ := D₂
  dsimp only at h_plan h_card h_cell
  subst h_plan h_card
  simp only [Fin.cast_eq_self] at h_cell
  obtain rfl := funext h_cell
  rfl

/-- The cells of propositionally equal schemes correspond along `Fin.cast`. -/
theorem CellScheme.cell_cast_of_eq {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {D₁ D₂ : CellScheme A} (h : D₁ = D₂) (i : Cell D₂) :
    D₁.cell (Fin.cast (congrArg CellScheme.card h).symm i) = D₂.cell i := by
  subst h; rfl

/-- Two domains with associated semantics are equal when their plans, sizes, cells and rows
agree, the components of the first read through `Fin.cast` (the analogue of
`StageType.ext_of_components`; no `HEq`). -/
theorem SemScheme.ext_of_components {n : ℕ} {D₁ D₂ : SemScheme n}
    (h_plan : D₁.scheme.plan = D₂.scheme.plan) (h_card : D₁.scheme.card = D₂.scheme.card)
    (h_cell : ∀ i, D₁.scheme.cell (Fin.cast h_card.symm i) = D₂.scheme.cell i)
    (h_row : ∀ (Sig : Cell D₂.scheme) (d : D₂.scheme.below (D₂.scheme.cell Sig)),
      D₁.rows.E (Fin.cast h_card.symm Sig)
        ⟨Fin.cast h_card.symm d.1, by rw [h_cell d.1, h_cell Sig]; exact d.2⟩ =
      D₂.rows.E Sig d) :
    D₁ = D₂ := by
  obtain ⟨⟨P₁, ip₁, c₁, cl₁, cm₁⟩, s₁, _, _, _, _⟩ := D₁
  obtain ⟨⟨P₂, ip₂, c₂, cl₂, cm₂⟩, s₂, _, _, _, _⟩ := D₂
  dsimp only at h_plan h_card h_cell h_row
  subst h_plan h_card
  simp only [Fin.cast_eq_self] at h_cell h_row
  obtain rfl := funext h_cell
  obtain rfl : s₁ = s₂ := Semantics.ext (funext fun Sig => funext fun d => h_row Sig d)
  rfl

/-! ### One-point extension of a plan on `Fin n` -/

end VaughtConjecture.Knight

namespace VaughtConjecture.AmalgamationPlan.Plan

variable {n : ℕ}

/-- One-point extension of a plan on `Fin n` to `Fin (n+1)` (Knight, Def. 2.1.1 step at the
new point; `Plan.isPlan_extend_one` transported to `Fin`): a plan on `Fin (n+1)` in which the
initial segment `ι_{n,n+1}[Fin n]` is visible and the visible faces inside it are exactly the
pushed-forward faces of `P`. -/
theorem exists_extendOne_fin {P : Finset (Finset (Fin n))} (hP : IsPlan Finset.univ P) :
    ∃ Q : Finset (Finset (Fin (n + 1))), IsPlan Finset.univ Q ∧
      Finset.univ.image Fin.castSuccEmb ∈ Q ∧
      ∀ C : Finset (Fin n), C.image Fin.castSuccEmb ∈ Q ↔ C ∈ P := by
  set A : Finset (Fin (n + 1)) := Finset.univ.image Fin.castSuccEmb with hA
  have hx : Fin.last n ∉ A := by
    simp only [hA, Finset.mem_image, Finset.mem_univ, true_and, Fin.coe_castSuccEmb,
      not_exists]
    exact fun i => Fin.castSucc_ne_last i
  have hP₀ : IsPlan A (P.image (Finset.image Fin.castSuccEmb)) := isPlan_image _ hP
  obtain ⟨Q, hQ, hAQ, hres⟩ := isPlan_extend_one hx hP₀
  have huniv : A ∪ {Fin.last n} = Finset.univ := by
    ext y
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_univ, iff_true, hA,
      Finset.mem_image, Finset.mem_univ, true_and, Fin.coe_castSuccEmb]
    rcases Fin.eq_castSucc_or_eq_last y with ⟨j, rfl⟩ | rfl
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr rfl
  refine ⟨Q, huniv ▸ hQ, hAQ, fun C => ?_⟩
  have hsub : C.image Fin.castSuccEmb ⊆ A :=
    Finset.image_subset_image (Finset.subset_univ _)
  constructor
  · intro hC
    have hmem : C.image Fin.castSuccEmb ∈ restrictPlan Q A :=
      Finset.mem_inter.mpr ⟨hC, Finset.mem_powerset.mpr hsub⟩
    rw [hres, Finset.mem_image] at hmem
    obtain ⟨B, hB, hBC⟩ := hmem
    rwa [← Finset.image_injective Fin.castSuccEmb.injective hBC]
  · intro hC
    have hmem : C.image Fin.castSuccEmb ∈ restrictPlan Q A := by
      rw [hres]; exact Finset.mem_image_of_mem _ hC
    exact (Finset.mem_inter.mp hmem).1

/-- A chosen one-point extension of a plan on `Fin n` to `Fin (n+1)`. -/
noncomputable def extendOnePlan (P : Finset (Finset (Fin n))) (hP : IsPlan Finset.univ P) :
    Finset (Finset (Fin (n + 1))) :=
  (exists_extendOne_fin hP).choose

variable (P : Finset (Finset (Fin n))) (hP : IsPlan Finset.univ P)

theorem extendOnePlan_isPlan : IsPlan Finset.univ (extendOnePlan P hP) :=
  (exists_extendOne_fin hP).choose_spec.1

/-- The initial segment is visible in the extended plan. -/
theorem castSucc_mem_extendOnePlan : Finset.univ.image Fin.castSuccEmb ∈ extendOnePlan P hP :=
  (exists_extendOne_fin hP).choose_spec.2.1

/-- The face equation on plans: a face of `Fin n` is visible in `P` iff its push-forward is
visible in the extension. -/
theorem image_castSucc_mem_extendOnePlan_iff (C : Finset (Fin n)) :
    C.image Fin.castSuccEmb ∈ extendOnePlan P hP ↔ C ∈ P :=
  (exists_extendOne_fin hP).choose_spec.2.2 C

end VaughtConjecture.AmalgamationPlan.Plan

namespace VaughtConjecture.Knight

open VaughtConjecture.AmalgamationPlan
open Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap)

/-! ### One-point extension of a cell scheme -/

namespace CellScheme

open CellScheme.restrictFace (pushGraded)

variable {n : ℕ} (C : CellScheme (ι := Fin n) Finset.univ)

/-- The **new graded pairs** of the one-point extension: the pairs `⟨B,j⟩ ∈ P̂'` of the
extended plan whose scope contains the new point `n`. -/
noncomputable def newPairs : Finset (Finset (Fin (n + 1)) × ℕ) :=
  (Plan.gradedPlan (Plan.extendOnePlan C.plan C.isPlan)).filter (fun BJ => Fin.last n ∈ BJ.1)

/-- The **one-point extension** of a cell scheme on `Fin n` to `Fin (n+1)`: the extended plan
`Plan.extendOnePlan`, the old cells with their scopes pushed along `castSucc` (indices
`Fin.castAdd`), and one new cell for every new graded pair (indices `Fin.natAdd`). -/
noncomputable def extendOne : CellScheme (ι := Fin (n + 1)) Finset.univ where
  plan := Plan.extendOnePlan C.plan C.isPlan
  isPlan := Plan.extendOnePlan_isPlan _ _
  card := C.card + C.newPairs.card
  cell := Fin.append (fun i => pushGraded Fin.castSuccEmb (C.cell i))
    (fun j => (C.newPairs.equivFin.symm j).1)
  cell_mem i := by
    induction i using Fin.addCases with
    | left i =>
      rw [Fin.append_left]
      have h := Plan.mem_gradedPlan.mp (C.cell_mem i)
      refine Plan.mem_gradedPlan.mpr ⟨?_, h.2.1, ?_⟩
      · exact (Plan.image_castSucc_mem_extendOnePlan_iff C.plan C.isPlan _).mpr h.1
      · show (C.cell i).2 ≤ ((C.cell i).1.image Fin.castSuccEmb).card
        rw [Finset.card_image_of_injective _ Fin.castSuccEmb.injective]
        exact h.2.2
    | right j =>
      rw [Fin.append_right]
      exact (Finset.mem_filter.mp (C.newPairs.equivFin.symm j).2).1

theorem extendOne_plan : C.extendOne.plan = Plan.extendOnePlan C.plan C.isPlan := rfl

theorem extendOne_card : C.extendOne.card = C.card + C.newPairs.card := rfl

/-- The initial segment is a visible face of the extension. -/
theorem extendOne_visible : Finset.univ.image Fin.castSuccEmb ∈ C.extendOne.plan :=
  Plan.castSucc_mem_extendOnePlan C.plan C.isPlan

@[simp] theorem extendOne_cell_castAdd (i : Cell C) :
    C.extendOne.cell (Fin.castAdd C.newPairs.card i) = pushGraded Fin.castSuccEmb (C.cell i) :=
  Fin.append_left (fun i => pushGraded Fin.castSuccEmb (C.cell i))
    (fun j => (C.newPairs.equivFin.symm j).1) i

@[simp] theorem extendOne_scope_castAdd (i : Cell C) :
    C.extendOne.scope (Fin.castAdd C.newPairs.card i) = (C.scope i).image Fin.castSuccEmb :=
  congrArg Prod.fst (extendOne_cell_castAdd C i)

@[simp] theorem extendOne_grade_castAdd (i : Cell C) :
    C.extendOne.grade (Fin.castAdd C.newPairs.card i) = C.grade i :=
  congrArg Prod.snd (extendOne_cell_castAdd C i)

@[simp] theorem extendOne_cell_natAdd (j : Fin C.newPairs.card) :
    C.extendOne.cell (Fin.natAdd C.card j) = (C.newPairs.equivFin.symm j).1 :=
  Fin.append_right (fun i => pushGraded Fin.castSuccEmb (C.cell i))
    (fun j => (C.newPairs.equivFin.symm j).1) j

/-- Every new cell sees the new point. -/
theorem last_mem_extendOne_scope_natAdd (j : Fin C.newPairs.card) :
    Fin.last n ∈ C.extendOne.scope (Fin.natAdd C.card j) := by
  change Fin.last n ∈ (C.extendOne.cell (Fin.natAdd C.card j)).1
  rw [extendOne_cell_natAdd]
  exact (Finset.mem_filter.mp (C.newPairs.equivFin.symm j).2).2

/-- The cells of the extension visible through the initial face are exactly the old cells. -/
theorem extendOne_scope_subset_iff (d : Cell C.extendOne) :
    C.extendOne.scope d ⊆ Finset.univ.image Fin.castSuccEmb ↔
      ∃ i, Fin.castAdd C.newPairs.card i = d := by
  induction d using Fin.addCases with
  | left i =>
    refine ⟨fun _ => ⟨i, rfl⟩, fun _ => ?_⟩
    rw [extendOne_scope_castAdd]
    exact Finset.image_subset_image (Finset.subset_univ _)
  | right j =>
    refine ⟨fun h => ?_, fun ⟨i, hi⟩ => ?_⟩
    · have := h (last_mem_extendOne_scope_natAdd C j)
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Fin.coe_castSuccEmb] at this
      obtain ⟨i, hi⟩ := this
      exact absurd hi (Fin.castSucc_ne_last i)
    · exact absurd hi (Fin.ne_of_val_ne (by simp [Fin.castAdd, Fin.natAdd]; omega))

/-- Pulling an old cell of the extension back along the initial face recovers its graded
index in `C`. -/
theorem pullCell_extendOne_castAdd (i : Cell C) :
    C.extendOne.pullCell Fin.castSuccEmb (Fin.castAdd C.newPairs.card i) = C.cell i := by
  unfold pullCell
  refine Prod.ext ?_ (extendOne_grade_castAdd C i)
  ext x
  simp [extendOne_scope_castAdd]

/-- **The face equation** (cell schemes): the face restriction of the one-point extension
along the initial segment is `C` itself — the old cells are exactly the visible ones, in
order (`Fin.castAdd` is the canonical enumeration), and their pulled-back indices are their
indices in `C`. -/
theorem restrictFace_extendOne :
    C.extendOne.restrictFace Fin.castSuccEmb (extendOne_visible C) = C := by
  have hvis : ∀ c, C.extendOne.scope (Fin.castAdd C.newPairs.card c) ⊆
      Finset.univ.image Fin.castSuccEmb :=
    fun c => (extendOne_scope_subset_iff C _).mpr ⟨c, rfl⟩
  have hsurj : ∀ d, C.extendOne.scope d ⊆ Finset.univ.image Fin.castSuccEmb →
      ∃ c, Fin.castAdd C.newPairs.card c = d :=
    fun d hd => (extendOne_scope_subset_iff C d).mp hd
  have hcard : (C.extendOne.restrictFace Fin.castSuccEmb (extendOne_visible C)).card = C.card :=
    restrictFace.card_restrictFace_of_emb _ _ _ (Fin.strictMono_castAdd _) hvis hsurj
  refine ext_of_components ?_ hcard fun i => ?_
  · ext B
    simp only [restrictFace_plan, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
      true_and, extendOne_plan, Plan.image_castSucc_mem_extendOnePlan_iff]
  · rw [restrictFace.cell_eq, restrictFace.toCell_cast_eq_of_emb C.extendOne Fin.castSuccEmb
      (extendOne_visible C) (e := Fin.castAdd C.newPairs.card) (Fin.strictMono_castAdd _) hvis
      hcard, pullCell_extendOne_castAdd]

/-- The one-point extension of a complete scheme is complete (Def. 2.5.15): a graded pair
seeing the new point has its new cell; one inside the initial segment is the push-forward of a
graded pair of `P̂`, which has a cell in `C`. -/
theorem IsComplete.extendOne (hC : C.IsComplete) : C.extendOne.IsComplete := by
  intro BJ hBJ
  by_cases hlast : Fin.last n ∈ BJ.1
  · refine ⟨Fin.natAdd C.card (C.newPairs.equivFin ⟨BJ, Finset.mem_filter.mpr ⟨hBJ, hlast⟩⟩), ?_⟩
    rw [extendOne_cell_natAdd, Equiv.symm_apply_apply]
  · -- the scope lies in the initial segment: pull it back
    set C₀ : Finset (Fin n) := Finset.univ.filter (fun x => Fin.castSucc x ∈ BJ.1) with hC₀
    have himg : C₀.image Fin.castSuccEmb = BJ.1 := by
      ext y
      simp only [Finset.mem_image, hC₀, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.coe_castSuccEmb]
      refine ⟨fun ⟨x, hx, hxy⟩ => hxy ▸ hx, fun hy => ?_⟩
      rcases Fin.eq_castSucc_or_eq_last y with ⟨x, rfl⟩ | rfl
      · exact ⟨x, hy, rfl⟩
      · exact absurd hy hlast
    have h := Plan.mem_gradedPlan.mp hBJ
    have hmem : (C₀, BJ.2) ∈ Plan.gradedPlan C.plan := by
      refine Plan.mem_gradedPlan.mpr ⟨?_, h.2.1, ?_⟩
      · exact (Plan.image_castSucc_mem_extendOnePlan_iff C.plan C.isPlan C₀).mp
          (by rw [himg]; exact h.1)
      · show BJ.2 ≤ C₀.card
        rw [← Finset.card_image_of_injective C₀ Fin.castSuccEmb.injective, himg]
        exact h.2.2
    obtain ⟨d, hd⟩ := hC _ hmem
    refine ⟨Fin.castAdd C.newPairs.card d, ?_⟩
    rw [extendOne_cell_castAdd, hd]
    exact Prod.ext himg rfl

end CellScheme

/-! ### The mute semantics -/

section Mute

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- The **mute semantics** on a cell scheme: every row is constantly `−∞` (Knight, Lemma 4.2.2,
last clause — "assigning the value `−∞` to `E(Σ)(Σ)`" — at every cell).  Orderliness is
`−∞ = −∞ ⊔⁺_k k`. -/
def Semantics.mute (D : CellScheme A) : Semantics D where
  E _ _ := ⊥
  orderly _ _ := (extVisibilityReplace_bot _ _).symm

@[simp] theorem Semantics.mute_E (Sig : Cell D) (d : D.below (D.cell Sig)) :
    (Semantics.mute D).E Sig d = ⊥ := rfl

/-- The constantly-`−∞` labelling of a lower set respects the mute semantics there. -/
theorem RespectsSemanticsBelow.mute (BJ : Finset ι × ℕ) :
    RespectsSemanticsBelow (Semantics.mute D) BJ (fun _ => ⊥) :=
  RespectsSemanticsBelow.bot _ _

/-- The constantly-`−∞` labelling respects the mute semantics. -/
theorem RespectsSemantics.mute : RespectsSemantics (Semantics.mute D) (fun _ => ⊥) :=
  RespectsSemantics.bot _

/-- A cell whose row is `−∞` on its own diagonal is forced to the label `−∞`: locality at the
cell itself reads `min (r Σ) (r Σ) = min (σ ⊥) (g _) = ⊥`.  So the only labelling of a lower set
respecting the mute semantics is `−∞`. -/
theorem RespectsSemanticsBelow.eq_bot_of_mute {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    (h : RespectsSemanticsBelow (Semantics.mute D) BJ r) (d : D.below BJ) : r d = ⊥ :=
  h.eq_bot_of_diagonal d rfl

/-- The only labelling respecting the mute semantics is `−∞`. -/
theorem RespectsSemantics.eq_bot_of_mute {p : Cell D → ExtOrd}
    (h : RespectsSemantics (Semantics.mute D) p) (d : Cell D) : p d = ⊥ :=
  h.eq_bot_of_diagonal d rfl

end Mute

/-! ### Mute domains and their one-point extension -/

namespace SemScheme

variable {n : ℕ}

/-- The **mute domain** on a complete cell scheme: the scheme with the mute semantics.  Coding:
`−∞` is coded at every grade; consistency: every row is the `−∞` labelling, which respects the
mute semantics of its lower set; bountifulness (Def. 2.5.14): the only respecting labellings
are `−∞`, so `q' = −∞` always works. -/
noncomputable def mute (C : CellScheme (ι := Fin n) Finset.univ) (hC : C.IsComplete) :
    SemScheme n where
  scheme := C
  rows := Semantics.mute C
  rows_coded _ _ := Or.inl rfl
  consistent _ := RespectsSemanticsBelow.mute _
  bountiful _ _ _ _ _ _ p q _ hp hq _ _ :=
    ⟨fun _ => ⊥, RespectsSemanticsBelow.mute _, fun d => by rw [hq.eq_bot_of_mute d],
      fun d => (hp.eq_bot_of_mute d).symm⟩
  complete := hC

@[simp] theorem mute_scheme (C : CellScheme (ι := Fin n) Finset.univ) (hC : C.IsComplete) :
    (mute C hC).scheme = C := rfl

/-- A domain is **mute** when all its rows are constantly `−∞`. -/
def IsMute (D : SemScheme n) : Prop :=
  ∀ (Sig : Cell D.scheme) (d : D.scheme.below (D.scheme.cell Sig)), D.rows.E Sig d = ⊥

theorem mute_isMute (C : CellScheme (ι := Fin n) Finset.univ) (hC : C.IsComplete) :
    (mute C hC).IsMute :=
  fun _ _ => rfl

theorem IsMute.rows_eq {D : SemScheme n} (hD : D.IsMute) : D.rows = Semantics.mute D.scheme :=
  Semantics.ext (funext fun Sig => funext fun d => hD Sig d)

/-- A mute domain is the mute domain on its scheme. -/
theorem IsMute.eq_mute {D : SemScheme n} (hD : D.IsMute) : D = mute D.scheme D.complete :=
  SemScheme.ext rfl (heq_of_eq hD.rows_eq)

/-- The empty domain is mute (no cells). -/
theorem emptySemScheme_isMute : StageType.emptySemScheme.IsMute := fun Sig => Sig.elim0

/-- **One-point extension**: the mute domain on the one-point extension of the cell scheme of
`D` (`CellScheme.extendOne`).  It is a domain on `n+1` whose face restriction along the initial
segment is the mute domain on `D`'s scheme — so it extends `D` itself (`ExtendsDomain`) exactly
when `D` is mute (`restrictFace_muteExtendOne`); for a non-mute `D` it discards the old semantics
and is not an extension.  For a general `D` the rows of the new cells must accommodate every
respecting labelling of the old ones; all-`⊥` new rows are refuted (module docstring), and Knight's
§4.3 completion (stacks) is the paper's known — not necessarily the only — solution. -/
noncomputable def muteExtendOne (D : SemScheme n) : SemScheme (n + 1) :=
  mute D.scheme.extendOne (D.complete.extendOne)

variable (D : SemScheme n)

@[simp] theorem muteExtendOne_scheme : D.muteExtendOne.scheme = D.scheme.extendOne := rfl

theorem muteExtendOne_isMute : D.muteExtendOne.IsMute := fun _ _ => rfl

/-- The initial segment is a visible face of the extension. -/
theorem muteExtendOne_visible : Finset.univ.image Fin.castSuccEmb ∈ D.muteExtendOne.scheme.plan :=
  CellScheme.extendOne_visible D.scheme

/-- **The face equation**: for a mute domain `D`, the face restriction of its one-point
extension along the initial segment `ι_{n,n+1}` is `D` — exactly `ExtendsDomain.restrict`.
Scheme by `CellScheme.restrictFace_extendOne`; rows: both sides are `−∞`. -/
theorem restrictFace_muteExtendOne (hD : D.IsMute) :
    D.muteExtendOne.restrictFace Fin.castSuccEmb (muteExtendOne_visible D) = D := by
  have hE := CellScheme.restrictFace_extendOne D.scheme
  refine ext_of_components (congrArg CellScheme.plan hE) (congrArg CellScheme.card hE)
    (fun i => CellScheme.cell_cast_of_eq hE i) (fun Sig d => ?_)
  exact (hD Sig d).symm

/-- `p.scheme.muteExtendOne` extends the domain of every stage type `p` on a mute domain, in the
sense of `Knight.Model` (the side condition of Def. 3.2.1(4)(a)). -/
theorem extendsDomain_muteExtendOne {α : Ordinal.{0}} (p : S α n) (hp : p.scheme.IsMute) :
    ExtendsDomain p p.scheme.muteExtendOne :=
  ⟨muteExtendOne_visible _, restrictFace_muteExtendOne _ hp⟩

/-- The chain of mute domains `D₀ ⊂ D₁ ⊂ ⋯`: the empty domain, extended one point at a
time. -/
noncomputable def muteChain : (n : ℕ) → SemScheme n
  | 0 => StageType.emptySemScheme
  | n + 1 => (muteChain n).muteExtendOne

theorem muteChain_isMute : ∀ n, (muteChain n).IsMute
  | 0 => emptySemScheme_isMute
  | n + 1 => muteExtendOne_isMute (muteChain n)

theorem restrictFace_muteChain_succ (n : ℕ) :
    (muteChain (n + 1)).restrictFace Fin.castSuccEmb (muteExtendOne_visible _) = muteChain n :=
  restrictFace_muteExtendOne _ (muteChain_isMute n)

/-- Domains with associated semantics exist at every arity (the positive-arity obligation of
#41; Knight: Lemma 4.2.2 at arity 1, amalgamation beyond). -/
instance nonempty (n : ℕ) : Nonempty (SemScheme n) := ⟨muteChain n⟩

end SemScheme

/-! ### Stage types on every domain, and cofaces over mute domains -/

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-- Every cell of a scheme on `Fin (n+1)` lies below the full-grade pair `(univ, n+1)`. -/
theorem gradedLe_univ_succ (C : CellScheme (ι := Fin (n + 1)) Finset.univ) (d : Cell C) :
    GradedLe (C.cell d) (Finset.univ, n + 1) :=
  ⟨Finset.subset_univ _, (C.grade_le_card_scope d).trans
    (by simpa using Finset.card_le_univ (C.scope d))⟩

/-- The full-grade pair `(univ, n+1)` lies in the graded plan of every scheme on `Fin (n+1)`. -/
theorem univ_succ_mem_gradedPlan (C : CellScheme (ι := Fin (n + 1)) Finset.univ) :
    (Finset.univ, n + 1) ∈ Plan.gradedPlan C.plan :=
  Plan.mem_gradedPlan.mpr ⟨C.isPlan.domain_mem, Nat.succ_pos _, by simp⟩

/-- **Every domain carries a stage type** (Knight, Prop. 4.3.24): for a domain `D` on
`Fin (n+1)` and a limit stage `α`, the row `E(Σ)` of a full-grade cell `Σ ∈ D^{A,|A|}` (which
exists by completeness) is a labelling of `D⟨A,|A|⟩ = D` respecting `E` (consistency,
Def. 2.5.12, read through `RespectsSemanticsBelow.toRespects`); its reduction to stage `α`
(`truncExt α`, Def. 3.1.2) respects `E` at stage `α` (`RespectsSemantics.truncate`). -/
noncomputable def ofScheme (hα : Order.IsSuccLimit α) (D : SemScheme (n + 1)) : S α (n + 1) :=
  let Sig := (D.complete _ (univ_succ_mem_gradedPlan D.scheme)).choose
  have hSig : D.scheme.cell Sig = (Finset.univ, n + 1) :=
    (D.complete _ (univ_succ_mem_gradedPlan D.scheme)).choose_spec
  have hall : ∀ d : Cell D.scheme, GradedLe (D.scheme.cell d) (D.scheme.cell Sig) :=
    fun d => hSig ▸ gradedLe_univ_succ D.scheme d
  { scheme := D
    label := fun d => truncExt α (D.rows.E Sig ⟨d, hall d⟩)
    label_bound := fun _ => truncExt_bound α _
    respects := ((D.consistent Sig).toRespects hall).truncate hα }

@[simp] theorem ofScheme_scheme (hα : Order.IsSuccLimit α) (D : SemScheme (n + 1)) :
    (ofScheme hα D).scheme = D := rfl

/-- The stage types of every arity are nonempty at every limit stage: `emptyType` at arity 0,
`ofScheme` on the mute domain `SemScheme.muteChain` beyond. -/
theorem nonempty (hα : Order.IsSuccLimit α) (n : ℕ) : Nonempty (S α n) := by
  cases n with
  | zero => exact ⟨emptyType⟩
  | succ n => exact ⟨ofScheme hα (SemScheme.muteChain (n + 1))⟩

/-- The stage type on a mute domain at any stage: all labels `−∞`. -/
noncomputable def mute (D : SemScheme n) (hD : D.IsMute) : S α n where
  scheme := D
  label _ := ⊥
  label_bound _ := Or.inl (bot_lt_ofOrd α)
  respects := by rw [hD.rows_eq]; exact RespectsSemantics.mute

@[simp] theorem mute_scheme (D : SemScheme n) (hD : D.IsMute) :
    (mute (α := α) D hD).scheme = D := rfl

/-- A stage type on a mute domain has all labels `−∞` (so `StageType.mute` is the only one). -/
theorem label_eq_bot_of_isMute (t : S α n) (ht : t.scheme.IsMute) (d : Cell t.scheme.scheme) :
    t.label d = ⊥ := by
  have h := t.respects
  rw [ht.rows_eq] at h
  exact h.eq_bot_of_mute d

/-- **Cofaces over mute domains** (the ∃-part of Def. 3.2.1(4) for stage types on mute
domains): a stage type `p` on a mute domain has a coface (`IsCoface`, `typeMap ι_{n,n+1} q =
some p`) on the one-point extension of its domain — the mute stage type there.  The restriction
is computed by `typeMap_eq_some_of_emb` with the old cells `Fin.castAdd` as the enumeration of
the visible cells.  (For a general domain this is Knight's Prop. 4.3.23, via the §4.3
completion; not built here.) -/
theorem exists_isCoface_of_isMute (p : S α n) (hp : p.scheme.IsMute) :
    ∃ q : S α (n + 1), IsCoface p q ∧ q.scheme = p.scheme.muteExtendOne := by
  refine ⟨mute p.scheme.muteExtendOne (SemScheme.muteExtendOne_isMute _), ?_, rfl⟩
  have hE := CellScheme.restrictFace_extendOne p.scheme.scheme
  refine typeMap_eq_some_of_emb Fin.castSuccEmb _ p (SemScheme.muteExtendOne_visible _)
    (Fin.castAdd _) (Fin.strictMono_castAdd _)
    (fun c => (CellScheme.extendOne_scope_subset_iff _ _).mpr ⟨c, rfl⟩)
    (fun d hd => (CellScheme.extendOne_scope_subset_iff _ _).mp hd)
    (congrArg CellScheme.plan hE)
    (fun c => CellScheme.pullCell_extendOne_castAdd _ c)
    (fun c => (label_eq_bot_of_isMute p hp c).symm)
    (fun Sig d _ _ => (hp Sig d).symm)

/-- Every stage type on a mute domain has an extension domain in the sense of
`ExtendsDomain` (and its coface on it). -/
theorem exists_extendsDomain_of_isMute (p : S α n) (hp : p.scheme.IsMute) :
    ∃ D : SemScheme (n + 1), ExtendsDomain p D ∧ ∃ q : S α (n + 1), IsCoface p q ∧ q.scheme = D :=
  ⟨_, SemScheme.extendsDomain_muteExtendOne p hp, exists_isCoface_of_isMute p hp⟩

end StageType

end VaughtConjecture.Knight
