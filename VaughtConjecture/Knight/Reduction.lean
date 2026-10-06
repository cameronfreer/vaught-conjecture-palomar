/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Type

/-! # Knight's vertical reduction of stage types

Ported from Knight-VC `KnightVC/ReductionExpansion.lean` @ f7c7847d (`truncateType`,
`truncateType_dom`, `truncateType_p`, `truncateType_sem_E`, `truncateType_preserves_locality`,
`typeMap_truncateType_comm`), with the hypothesis `α < β` of Knight-VC's `truncateType`
relaxed to `α ≤ β` (the formula is the same; at `α = β` reduction is the identity, which is the
reflexivity law the `TypeTower` needs), the target stage `α` required to be a **limit ordinal**
(as in Def. 3.1.1), and — the content of #88/#89 — Knight-VC's truncation of the semantic rows
removed: the rows are the associated semantics of the scheme and are **fixed** under reduction,
as in the paper.

**Vertical reduction** `S^{ι_{α,β}} : S^β_n → S^α_n` (Knight, Def. 3.1.2 / 5.1.1):
`reduceType hα h t` keeps the domain with its associated semantics (`t.scheme`, rows included)
and truncates every label at stage `α` with the **strict** truncation `Value.truncExt α`
(decision #84: ordinals `≥ α` become `⊤`, ordinals `< α` are kept), so the result satisfies the
strict stage bound (`truncExt_bound`).  Respect of the associated semantics (faithful, Def. 2.5.4)
is preserved **with the semantics fixed** by `RespectsSemantics.truncate` (the reduction half of
Lemma 3.1.3, from the direct witness `TransformsTo.truncExt_target`, #89); this is where the
limit hypothesis `hα : Order.IsSuccLimit α` enters, and why the tower (`Knight.Tower`) is
indexed by limit stages.  The laws: `reduceType_refl` (by the strict bound `label_bound`,
truncation at the stage of the type is the identity — `truncExt_id_of_bound`),
`reduceType_trans` (`truncExt_compose`), and the commutation with horizontal restriction
`typeMap_reduceType_comm` (`typeMap f (reduceType hα h t) = (typeMap f t).map (reduceType hα h)`,
by `rfl` on each branch of the guard: reduction never changes the scheme, hence never changes
visibility).  These are `reduce_refl`, `reduce_trans` and `pull_reduce` of the Knight
`TypeTower` instance (`Knight.Tower.knightTower`).  Nothing beyond `IsSuccLimit α` is needed
for the laws themselves (they are pointwise identities of `truncExt`). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Value Transform

variable {α β γ : Ordinal.{0}} {m n : ℕ}

/-- **Vertical reduction** of a stage type from stage `β` to a limit stage `α ≤ β` (Knight,
Def. 3.1.2 / 5.1.1; Knight-VC `truncateType`, there for `α < β` and with the rows truncated
too): the same domain with its associated semantics (rows **fixed**), every label strictly
truncated at `α` (`truncExt α`; the strict bound of the result is `truncExt_bound`), respect
transported by `RespectsSemantics.truncate` (Lemma 3.1.3, reduction half).  This is the
`reduce` of the Knight `TypeTower` instance. -/
noncomputable def reduceType (hα : Order.IsSuccLimit α) (_h : α ≤ β) (t : S β n) : S α n where
  scheme := t.scheme
  label d := truncExt α (t.label d)
  label_bound d := truncExt_bound α (t.label d)
  respects := t.respects.truncate hα

@[simp] theorem reduceType_scheme (hα : Order.IsSuccLimit α) (h : α ≤ β) (t : S β n) :
    (reduceType hα h t).scheme = t.scheme :=
  rfl

@[simp] theorem reduceType_label (hα : Order.IsSuccLimit α) (h : α ≤ β) (t : S β n)
    (d : Cell t.scheme.scheme) : (reduceType hα h t).label d = truncExt α (t.label d) := rfl

/-- The rows are fixed under reduction (the paper's Def. 3.1.2: only `p` is truncated). -/
@[simp] theorem reduceType_rows_E (hα : Order.IsSuccLimit α) (h : α ≤ β) (t : S β n)
    (Sig : Cell t.scheme.scheme) (d : t.scheme.scheme.below (t.scheme.scheme.cell Sig)) :
    (reduceType hα h t).scheme.rows.E Sig d = t.scheme.rows.E Sig d := rfl

/-- Reduction to the stage of the type is the identity: labels are already strictly bounded
at `α` (`< ofOrd α` or `⊤`), and `truncExt α` fixes them (`truncExt_id_of_bound`). -/
theorem reduceType_refl (hα : Order.IsSuccLimit α) (t : S α n) : reduceType hα le_rfl t = t :=
  StageType.ext rfl (heq_of_eq (funext fun d => truncExt_id_of_bound (t.label_bound d)))

/-- Reductions compose (`truncExt_compose`). -/
theorem reduceType_trans (hα : Order.IsSuccLimit α) (hβ : Order.IsSuccLimit β)
    (hαβ : α ≤ β) (hβγ : β ≤ γ) (t : S γ n) :
    reduceType hα hαβ (reduceType hβ hβγ t) = reduceType hα (hαβ.trans hβγ) t :=
  StageType.ext rfl (heq_of_eq (funext fun d => truncExt_compose hαβ (t.label d)))

/-- Reduction commutes with horizontal restriction, including definedness (Knight-VC
`typeMap_truncateType_comm`): reduction does not change the scheme, so a face is visible in
`reduceType hα h t` iff it is visible in `t`, and on a visible face the two operations
commute on the nose. -/
theorem typeMap_reduceType_comm (hα : Order.IsSuccLimit α) (h : α ≤ β) (f : Fin m ↪ Fin n)
    (t : S β n) : typeMap f (reduceType hα h t) = (typeMap f t).map (reduceType hα h) := by
  by_cases hr : Finset.univ.image f ∈ t.scheme.scheme.plan
  · rw [typeMap_eq_some f t hr, typeMap_eq_some f (reduceType hα h t) hr, Option.map_some]
    rfl
  · rw [typeMap_eq_none f t hr, typeMap_eq_none f (reduceType hα h t) hr, Option.map_none]

end VaughtConjecture.Knight
