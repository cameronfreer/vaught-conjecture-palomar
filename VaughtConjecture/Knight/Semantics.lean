/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Cell
public import VaughtConjecture.Knight.Transform

/-! # Knight's semantic rows, respect of semantics, and consistent semantics

Ported from Knight-VC `KnightVC/Semantics.lean` @ f7c7847d (`Sem.Semantics`,
`Sem.Semantics.ext`, `Sem.RespectsSemantics`), over the cell schemes of `Knight.Cell`
(Knight-VC's `Domain`, here `CellScheme`; `arity` is `grade`), and extended by the clauses of
Knight's Defs. 2.5.4 and 2.5.12 that Knight-VC left out.

A **semantics** on a cell scheme `D` (Knight, Def. 2.5.3, lightweight version) assigns to each
cell `Sig` its **semantic row** `E Sig`: a labelling of the lower set `D.below (D.cell Sig)` of
cells below `Sig` in the graded preorder, orderly at the grades of those cells.  Knight calls
`Sig` the controlling cell and the row `E(Σ)` its local entailment profile.

A labelling `p : Cell D → ExtOrd` **respects** a semantics `sem` (Def. 2.5.4) when

* `p` is orderly (Def. 2.5.4 presupposes it);
* **locality** (clause 1): for every cell `Sig`, the semantic row `sem.E Sig` transforms
  (`Transform.TransformsTo`, Def. 2.3.9) to the labelling `d ↦ min (p d) (p Sig)` of the cells
  below `Sig` — Knight's `E(Σ) ⇒ (p ↾ D⟨B,j⟩) ∧ p(Σ)`, with `∧ γ` the pointwise cap at `γ`
  and the grade function the restriction of `D.grade`;
* **availability** (clause 2): if `C ⊆ B`, `Σ ∈ D^{C,i}` and `D^{B,i} ≠ ∅`, there is
  `Ξ ∈ D^{B,i}` with `p Ξ ≥ p Σ`.  Encoded with a witness of non-emptiness: for cells
  `Sig Xi₀` with `D.scope Sig ⊆ D.scope Xi₀` and `D.grade Sig = D.grade Xi₀` (so `Xi₀` shows
  `D^{scope Xi₀, grade Sig} ≠ ∅`), there is a cell `Xi` with `D.cell Xi = D.cell Xi₀` and
  `p Sig ≤ p Xi`.

A semantics is **consistent** (Def. 2.5.12, `Semantics.IsConsistent`) when every row `E Σ`,
as a labelling of `D⟨B,j⟩ = D.below (D.cell Σ)`, respects the restricted semantics `E⟨B,j⟩`
of `D⟨B,j⟩`.  The restricted scheme has cells `D.below BJ` and, for each such cell `Sig'`, the
row `E Sig'` on `D⟨B,j⟩⟨Sig'⟩ = D.below (D.cell Sig')` (a subset of `D.below BJ` by
`GradedLe.trans`); respect of it by a labelling of `D.below BJ` is spelled out as
`RespectsSemanticsBelow sem BJ r` (the same three clauses, read on the lower set), so that
`IsConsistent` is literally "every row respects the restricted semantics".

## Fidelity status

`RespectsSemantics` (all clauses of Def. 2.5.4, with the faithful `TransformsTo`) and
`Semantics.IsConsistent` (Def. 2.5.12) are the notions in use (#85); Knight-VC's predicate
(orderliness and locality only, with Knight-VC's guarded, inflationary relation) was kept here
transitionally (as `LegacyRespectsSemantics`) and **retired** with #88 (2/2)/#89: the stage types
(`Knight.Type`) carry the faithful `RespectsSemantics` of the associated semantics
(`Knight.SemScheme`), and vertical reduction transports it **with the semantics fixed**
(`RespectsSemantics.truncate`, at a limit stage, via `TransformsTo.truncExt_target`), which is
the paper's reading of Lemma 3.1.3 (rows kept).  No lemmas about `IsConsistent` are proved yet.

**Transport along face restriction** (`CellScheme.restrictFace`, the scheme part of Knight-VC's
`typeMap`): the rows of `D` restrict to rows of `D.restrictFace f hr` by reading each row at the
underlying visible cell (`Semantics.restrictFace`, via `restrictFace.belowMap`), and respect of
semantics transports to the restricted labelling `p ∘ toCell` (`RespectsSemantics.restrictFace`,
used by `Knight.Type.typeMap`; locality by `TransformsTo.reindex`, availability by lifting the
witness along `toCell`).  `Semantics.E_congr` is the congruence lemma for rows at
propositionally equal indices (Knight-VC `sem_E_congr`). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

/-- A semantics on a cell scheme `D` (Knight, Def. 2.5.3, lightweight version): for each cell
`Sig`, the **semantic row** `E Sig` is a labelling of the cells below `Sig`, orderly at their
grades. -/
structure Semantics (D : CellScheme A) where
  /-- The semantic row of each cell, a labelling of the cells below it. -/
  E : (Sig : Cell D) → (D.below (D.cell Sig) → ExtOrd)
  /-- Each semantic row is orderly at the grades of its cells. -/
  orderly : ∀ Sig : Cell D,
    IsOrderly (fun d : D.below (D.cell Sig) => D.grade d.1) (E Sig)

variable {D : CellScheme A}

/-- Extensionality: two semantics on the same scheme are equal when their rows agree
(`orderly` is a proof). -/
@[ext]
theorem Semantics.ext {s₁ s₂ : Semantics D} (h_E : s₁.E = s₂.E) : s₁ = s₂ := by
  obtain ⟨E₁, _⟩ := s₁
  obtain ⟨E₂, _⟩ := s₂
  subst h_E; rfl

/-- A labelling `p` of the cells **respects** the semantics `sem` (Knight, Def. 2.5.4, all
clauses): `p` is orderly; **locality** — for every cell `Sig` the semantic row `sem.E Sig`
transforms (Def. 2.3.9) to the labelling `d ↦ min (p d) (p Sig)` of the cells below `Sig`;
**availability** — whenever `Sig` and `Xi₀` are cells with `D.scope Sig ⊆ D.scope Xi₀` and the
same grade (so `Xi₀` witnesses that `D^{scope Xi₀, grade Sig}` is non-empty), some cell `Xi`
with the graded index of `Xi₀` has `p Sig ≤ p Xi`. -/
structure RespectsSemantics (sem : Semantics D) (p : Cell D → ExtOrd) : Prop where
  /-- `p` is orderly on the whole scheme. -/
  orderly : IsOrderly D.grade p
  /-- Locality (Def. 2.5.4(1)): each semantic row transforms to `p` below `Sig`, capped by
  `p Sig`. -/
  locality :
    ∀ Sig : Cell D,
      TransformsTo (fun d : D.below (D.cell Sig) => D.grade d.1)
        (sem.E Sig)
        (fun d => min (p d.1) (p Sig))
  /-- Availability (Def. 2.5.4(2)): a label at scope `C` and grade `i` is dominated by a label
  at every larger scope `B ⊇ C` (in the plan) at which grade `i` occurs. -/
  availability :
    ∀ Sig Xi₀ : Cell D, D.scope Sig ⊆ D.scope Xi₀ → D.grade Sig = D.grade Xi₀ →
      ∃ Xi : Cell D, D.cell Xi = D.cell Xi₀ ∧ p Sig ≤ p Xi

/-- The identically bottom labelling respects every semantics. -/
theorem RespectsSemantics.bot {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    (sem : Semantics D) : RespectsSemantics sem (fun _ => ⊥) where
  orderly _ := (Value.extVisibilityReplace_bot _ _).symm
  locality c := TransformsTo.to_bot (sem.E c)
  availability _ Xi₀ _ _ := ⟨Xi₀, rfl, le_rfl⟩

/-! ### Restricted semantics and consistent semantics -/

/-- The row of `sem` at a cell `Sig` of the lower set `D.below BJ` has domain
`D.below (D.cell Sig)`, which embeds in `D.below BJ` (`GradedLe.trans`): this is the
restricted scheme's own "below" of `Sig`, `D⟨B,j⟩⟨Sig⟩ = D⟨Sig⟩`. -/
def CellScheme.below.incl {BJ : Finset ι × ℕ} (Sig : D.below BJ)
    (d : D.below (D.cell Sig.1)) : D.below BJ :=
  ⟨d.1, d.2.trans Sig.2⟩

/-- A labelling `r` of the lower set `D.below BJ` respects the **restricted semantics**
`E⟨B,j⟩` of `D⟨B,j⟩` (Knight, Def. 2.5.4 applied to the restricted scheme `D⟨B,j⟩`, whose
cells are `D.below BJ` and whose rows are the rows of `sem` at those cells): `r` is orderly
at the grades; locality — for each `Sig` below `BJ`, the row `sem.E Sig` transforms to
`d ↦ min (r d) (r Sig)` on `D.below (D.cell Sig)`; availability within `D.below BJ`. -/
structure RespectsSemanticsBelow (sem : Semantics D) (BJ : Finset ι × ℕ)
    (r : D.below BJ → ExtOrd) : Prop where
  /-- `r` is orderly on the lower set. -/
  orderly : IsOrderly (fun d : D.below BJ => D.grade d.1) r
  /-- Locality in the restricted scheme. -/
  locality :
    ∀ Sig : D.below BJ,
      TransformsTo (fun d : D.below (D.cell Sig.1) => D.grade d.1)
        (sem.E Sig.1)
        (fun d => min (r (CellScheme.below.incl Sig d)) (r Sig))
  /-- Availability in the restricted scheme. -/
  availability :
    ∀ Sig Xi₀ : D.below BJ, D.scope Sig.1 ⊆ D.scope Xi₀.1 → D.grade Sig.1 = D.grade Xi₀.1 →
      ∃ Xi : D.below BJ, D.cell Xi.1 = D.cell Xi₀.1 ∧ r Sig ≤ r Xi

/-- A labelling respecting the semantics of the whole scheme (Def. 2.5.4) respects the
restricted semantics `E⟨B,j⟩` on every lower set (the converse of
`RespectsSemanticsBelow.toRespects`, with no hypothesis on `BJ`): locality and orderliness
are read off the underlying cells, and the availability witness — which has the graded index of
`Xi₀` — lies in the lower set. -/
theorem RespectsSemantics.toBelow {sem : Semantics D} {p : Cell D → ExtOrd}
    (h : RespectsSemantics sem p) (BJ : Finset ι × ℕ) :
    RespectsSemanticsBelow sem BJ (fun d => p d.1) where
  orderly d := h.orderly d.1
  locality Sig := h.locality Sig.1
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hc, hle⟩ := h.availability Sig.1 Xi₀.1 hs hg
    exact ⟨⟨Xi, hc ▸ Xi₀.2⟩, hc, hle⟩

/-- A labelling of a lower set containing every cell respects the semantics (Def. 2.5.4) as a
labelling of the whole scheme when it respects the restricted semantics `E⟨B,j⟩`
(`RespectsSemanticsBelow`).  This is the case `D⟨A,|A|⟩ = D` used by Prop. 4.3.24. -/
theorem RespectsSemanticsBelow.toRespects {sem : Semantics D} {BJ : Finset ι × ℕ}
    {r : D.below BJ → ExtOrd} (h : RespectsSemanticsBelow sem BJ r)
    (hall : ∀ d : Cell D, GradedLe (D.cell d) BJ) :
    RespectsSemantics sem (fun d => r ⟨d, hall d⟩) where
  orderly d := h.orderly ⟨d, hall d⟩
  locality Sig := h.locality ⟨Sig, hall Sig⟩
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hc, hle⟩ := h.availability ⟨Sig, hall Sig⟩ ⟨Xi₀, hall Xi₀⟩ hs hg
    exact ⟨Xi.1, hc, hle⟩

/-- The all-bottom labelling is lawful on every lower set of any semantics. -/
theorem RespectsSemanticsBelow.bot (sem : Semantics D) (BJ : Finset ι × ℕ) :
    RespectsSemanticsBelow sem BJ (fun _ => ⊥) :=
  (RespectsSemantics.bot sem).toBelow BJ

/-- A bottom diagonal forces a bottom label, regardless of the other rows. -/
theorem RespectsSemanticsBelow.eq_bot_of_diagonal {sem : Semantics D} {BJ : Finset ι × ℕ}
    {r : D.below BJ → ExtOrd} (h : RespectsSemanticsBelow sem BJ r) (c : D.below BJ)
    (hc : sem.E c.1 ⟨c.1, GradedLe.refl _⟩ = ⊥) : r c = ⊥ := by
  obtain ⟨g, σ, _, _, hbot, _, _, heq⟩ := h.locality c
  have hread := heq ⟨c.1, GradedLe.refl _⟩
  change min (r c) (r c) = min (σ (sem.E c.1 ⟨c.1, GradedLe.refl _⟩)) _ at hread
  simpa only [min_self, hc, hbot, min_eq_left bot_le] using hread

/-- The whole-scheme form of bottom-diagonal rigidity. -/
theorem RespectsSemantics.eq_bot_of_diagonal {sem : Semantics D} {p : Cell D → ExtOrd}
    (h : RespectsSemantics sem p) (c : Cell D)
    (hc : sem.E c ⟨c, GradedLe.refl _⟩ = ⊥) : p c = ⊥ :=
  (h.toBelow (D.cell c)).eq_bot_of_diagonal ⟨c, GradedLe.refl _⟩ hc

/-- A semantics is **consistent** (Knight, Def. 2.5.12): for every cell `Sig` with graded
index `(B, j)`, the row `E Sig`, a labelling of `D⟨B,j⟩ = D.below (D.cell Sig)`, respects the
restricted semantics `E⟨B,j⟩` (`RespectsSemanticsBelow`).  (Orderliness of the row is already
`sem.orderly Sig`.) -/
def Semantics.IsConsistent (sem : Semantics D) : Prop :=
  ∀ Sig : Cell D, RespectsSemanticsBelow sem (D.cell Sig) (sem.E Sig)

/-- Two values of a semantic row at propositionally equal indices are equal (Knight-VC
`sem_E_congr`; the index of `E` is dependent, so this is stated with both equalities). -/
theorem Semantics.E_congr (sem : Semantics D) {a b : Cell D} (hab : a = b) {c d : Cell D}
    {hc : GradedLe (D.cell c) (D.cell a)} {hd : GradedLe (D.cell d) (D.cell b)} (hcd : c = d) :
    sem.E a ⟨c, hc⟩ = sem.E b ⟨d, hd⟩ := by
  subst hab; subst hcd; rfl

/-! ### Transport along vertical truncation (semantics fixed) -/

/-- Faithful respect of semantics is preserved by the strict vertical truncation of the
labelling at a limit stage `α`, **with the semantics fixed** (the reduction half of
Lemma 3.1.3, rows kept as in the paper): if `p` respects `sem` then so does `truncExt α ∘ p`.
Orderliness is `truncExt_preserves_selfVis`; locality is `TransformsTo.truncExt_target`
(the truncated labelling below `Sig` capped at the truncated `p Sig` is the truncation of the
capped labelling, `truncExt_min`); availability is monotonicity of `truncExt α`. -/
theorem RespectsSemantics.truncate {sem : Semantics D} {p : Cell D → ExtOrd}
    {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) (h : RespectsSemantics sem p) :
    RespectsSemantics sem (Value.truncExt α ∘ p) where
  orderly d := (Value.truncExt_preserves_selfVis α (p d) (D.grade d) (h.orderly d).symm).symm
  locality Sig := by
    have key := (h.locality Sig).truncExt_target hα
    have heq : Value.truncExt α ∘ (fun d : D.below (D.cell Sig) => min (p d.1) (p Sig)) =
        fun d => min ((Value.truncExt α ∘ p) d.1) ((Value.truncExt α ∘ p) Sig) := by
      funext d
      simp only [Function.comp_apply, Value.truncExt_min]
    rwa [heq] at key
  availability Sig Xi₀ hscope hgrade := by
    obtain ⟨Xi, hcell, hle⟩ := h.availability Sig Xi₀ hscope hgrade
    exact ⟨Xi, hcell, Value.truncExt_mono α hle⟩

/-! ### Transport along face restriction -/

section RestrictFace

open CellScheme.restrictFace (toCell belowMap)

variable {m n : ℕ} {D : CellScheme (ι := Fin n) Finset.univ} {f : Fin m ↪ Fin n}
  {hr : Finset.univ.image f ∈ D.plan}

/-- The rows of `D` restricted to the face `f`: the row of a restricted cell `Sig` is the row
of its underlying cell `toCell Sig`, read at the underlying cells (Knight, Def. 3.1.5; the
row part of Knight-VC `typeMap`). -/
noncomputable def Semantics.restrictFace (sem : Semantics D) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ D.plan) : Semantics (D.restrictFace f hr) where
  E Sig d := sem.E (toCell D f hr Sig) (belowMap D f hr Sig d)
  orderly Sig d := sem.orderly (toCell D f hr Sig) (belowMap D f hr Sig d)

@[simp] theorem Semantics.restrictFace_E (sem : Semantics D) (Sig : Cell (D.restrictFace f hr))
    (d : (D.restrictFace f hr).below ((D.restrictFace f hr).cell Sig)) :
    (sem.restrictFace f hr).E Sig d = sem.E (toCell D f hr Sig) (belowMap D f hr Sig d) := rfl

/-- Faithful respect of semantics (Def. 2.5.4, both clauses) transports along face
restriction: the restricted labelling `p ∘ toCell` respects the restricted rows.  Locality is
`TransformsTo.reindex` along `belowMap`; availability lifts the witness: the scopes of
restricted cells are the `f`-preimages of the scopes of the underlying cells, so an inclusion of
restricted scopes is an inclusion of the underlying scopes, the paper's witness `Xi` has the
graded index of the underlying cell of `Xi₀`, hence is visible, hence is `toCell` of a restricted
cell (`exists_toCell_eq`), whose pulled-back index is that of `Xi₀` (`pullCell_congr`). -/
theorem RespectsSemantics.restrictFace {sem : Semantics D} {p : Cell D → ExtOrd}
    (h : RespectsSemantics sem p) (f : Fin m ↪ Fin n) (hr : Finset.univ.image f ∈ D.plan) :
    RespectsSemantics (sem.restrictFace f hr) (fun i => p (toCell D f hr i)) where
  orderly i := h.orderly (toCell D f hr i)
  locality Sig := (h.locality (toCell D f hr Sig)).reindex (belowMap D f hr Sig)
  availability Sig Xi₀ hscope hgrade := by
    have hscope' : D.scope (toCell D f hr Sig) ⊆ D.scope (toCell D f hr Xi₀) := by
      rw [← CellScheme.restrictFace.image_scope_restrictFace D f hr Sig,
        ← CellScheme.restrictFace.image_scope_restrictFace D f hr Xi₀]
      exact Finset.image_subset_image hscope
    obtain ⟨Xi', hcell, hle⟩ :=
      h.availability (toCell D f hr Sig) (toCell D f hr Xi₀) hscope' hgrade
    have hvis : D.scope Xi' ⊆ Finset.univ.image f := by
      change (D.cell Xi').1 ⊆ _
      rw [hcell]
      exact CellScheme.restrictFace.scope_toCell_subset D f hr Xi₀
    obtain ⟨Xi, rfl⟩ := CellScheme.restrictFace.exists_toCell_eq D f hr hvis
    exact ⟨Xi, CellScheme.pullCell_congr D f hcell, hle⟩

end RestrictFace

end VaughtConjecture.Knight
