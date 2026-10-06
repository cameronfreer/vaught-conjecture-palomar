/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Order.WithBot

/-! # Knight's ordinal labels: finite/limit parts, visibility replacement, truncation

Ported from Knight-VC `KnightVC/Basic.lean` (`ExtOrd`) and `KnightVC/OrdinalOps.lean`
@ f7c7847d (plus `IsNonSuccessor` from `PaperProtoFiber.lean`); `lemma_2_2_4` is renamed
`extVisibilityReplace_self_iff`.  The canonical block levels `blockLevel` are new.

The **label** of a cell (Knight, Def. 2.2.1) is a point of the extended ordinal line
`{-∞} ∪ Ordinal ∪ {∞}`: the bottom label `-∞`, an ordinal, or the top label `∞`.  Here this is
`ExtOrd := WithBot (WithTop Ordinal.{0})` with `⊥ = -∞`, `⊤ = ∞`, and `ExtOrd.ofOrd α` the
ordinal `α`.  The ordinal universe is fixed at `Ordinal.{0}`, as in Knight-VC: the labels of
the finite stage types are countable-ordinal data (every stage `α < ω₁` is an `Ordinal.{0}`),
and a universe-polymorphic variant can be added later if a consumer needs it.

The paper's idiosyncratic ordinal operations (Defs. 2.2.1–2.2.4) all rest on the unique
decomposition `α = μ + n` of an ordinal into a **limit part** `μ` (zero or a limit) and a
**finite part** `n < ω`:

* `limitPart α := ω * (α / ω)`, `finitePart α` = the natural number `α % ω`, with
  `decomposition : limitPart α + finitePart α = α`;
* `ordinalReplace α m := limitPart α + m` (Def. 2.2.2) replaces the finite part by `m`;
* `visibilityReplace α K m` (Def. 2.2.3) replaces it only when `finitePart α < K` (the
  visibility threshold `K`), and `extVisibilityReplace` lifts this to labels, fixing `⊥`
  and `⊤`; `extVisibilityReplace_self_iff` is Lemma 2.2.4 (self-visibility);
* `truncExt α` is the (strict) vertical truncation of a label at stage `α` (Def. 3.1.2):
  ordinals `≥ α` become the top label, ordinals `< α` are kept.  Its calculus
  (`truncExt_compose`, `truncExt_truncExt`, `truncExt_mono`, `truncExt_id_of_bound`,
  …) is what the vertical `reduce` of the Knight `TypeTower` instance (`Knight.Reduction`)
  is built from; `truncExt_evr_comm` records that truncation commutes with visibility
  replacement at every limit stage.  Knight-VC's non-strict truncation (which keeps the
  boundary label `ofOrd α`, and does not commute with visibility replacement there) is not
  used (decision #84; its comparison copy `legacyTruncExt` was retired with #88 (2/2));
* `IsNonSuccessor` (zero or a limit) and the canonical block levels
  `blockLevel ξ := ω + ω * ξ` (the ω-blocks of `docs/TERMINOLOGY.md`). -/

@[expose] public section

namespace VaughtConjecture.Knight

/-- The extended ordinal line `{-∞} ∪ Ordinal ∪ {∞}` of labels (Knight, Def. 2.2.1):
`⊥` is the bottom label `-∞`, `⊤` is the top label `∞`, and `ExtOrd.ofOrd α` is the ordinal
`α`.  Fixed at `Ordinal.{0}` (see the module docstring). -/
abbrev ExtOrd : Type 1 := WithBot (WithTop Ordinal.{0})

namespace ExtOrd

/-- Embed an ordinal into the extended ordinal line as an ordinal label. -/
def ofOrd (α : Ordinal.{0}) : ExtOrd := ((α : WithTop Ordinal.{0}) : ExtOrd)

@[simp] theorem ofOrd_ne_bot (α : Ordinal.{0}) : ofOrd α ≠ (⊥ : ExtOrd) :=
  WithBot.coe_ne_bot

@[simp] theorem ofOrd_ne_top (α : Ordinal.{0}) : ofOrd α ≠ (⊤ : ExtOrd) :=
  fun h => WithTop.coe_ne_top (WithBot.coe_injective h)

@[simp] theorem ofOrd_inj {α β : Ordinal.{0}} : ofOrd α = ofOrd β ↔ α = β := by
  simp [ofOrd]

@[simp] theorem ofOrd_le_ofOrd {α β : Ordinal.{0}} : ofOrd α ≤ ofOrd β ↔ α ≤ β := by
  simp [ofOrd]

@[simp] theorem ofOrd_lt_ofOrd {α β : Ordinal.{0}} : ofOrd α < ofOrd β ↔ α < β := by
  simp [ofOrd]

@[simp] theorem bot_lt_ofOrd (α : Ordinal.{0}) : (⊥ : ExtOrd) < ofOrd α :=
  WithBot.bot_lt_coe _

@[simp] theorem ofOrd_lt_top (α : Ordinal.{0}) : ofOrd α < (⊤ : ExtOrd) :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top α)

@[simp] theorem not_top_le_ofOrd (α : Ordinal.{0}) : ¬ (⊤ : ExtOrd) ≤ ofOrd α :=
  not_le_of_gt (ofOrd_lt_top α)

@[simp] theorem not_ofOrd_le_bot (α : Ordinal.{0}) : ¬ ofOrd α ≤ (⊥ : ExtOrd) :=
  not_le_of_gt (bot_lt_ofOrd α)

/-- Every label is the bottom label, the top label, or an ordinal label. -/
theorem cases (x : ExtOrd) : x = ⊥ ∨ x = ⊤ ∨ ∃ α : Ordinal.{0}, x = ofOrd α := by
  induction x using WithBot.recBotCoe with
  | bot => exact Or.inl rfl
  | coe y =>
    induction y using WithTop.recTopCoe with
    | top => exact Or.inr (Or.inl rfl)
    | coe α => exact Or.inr (Or.inr ⟨α, rfl⟩)

end ExtOrd

namespace Value

open Ordinal ExtOrd

/-! ### Limit and finite parts -/

/-- The limit part `μ` in the decomposition `α = μ + n` (`n < ω`), defined as `ω * (α / ω)`
by the ordinal division algorithm. -/
noncomputable def limitPart (α : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.omega0 * (α / Ordinal.omega0)

/-- The finite part `n` in the decomposition `α = μ + n`, the natural number `α % ω`. -/
noncomputable def finitePart (α : Ordinal.{0}) : ℕ :=
  (Ordinal.lt_omega0.mp (Ordinal.mod_lt α Ordinal.omega0_ne_zero)).choose

/-- The residue `α % ω` is the finite part, as an ordinal. -/
theorem finitePart_spec (α : Ordinal.{0}) :
    (α % Ordinal.omega0 : Ordinal) = ↑(finitePart α) :=
  (Ordinal.lt_omega0.mp (Ordinal.mod_lt α Ordinal.omega0_ne_zero)).choose_spec

/-- The fundamental decomposition `α = limitPart α + finitePart α`. -/
theorem decomposition (α : Ordinal.{0}) : limitPart α + ↑(finitePart α) = α := by
  rw [limitPart, ← finitePart_spec]
  exact Ordinal.div_add_mod α Ordinal.omega0

/-- `limitPart` is monotone. -/
theorem limitPart_mono {γ δ : Ordinal.{0}} (h : γ ≤ δ) : limitPart γ ≤ limitPart δ :=
  mul_le_mul_right (Ordinal.div_le_left h _) _

/-- `limitPart δ ≤ δ`. -/
theorem limitPart_le (δ : Ordinal.{0}) : limitPart δ ≤ δ :=
  Ordinal.mul_div_le δ Ordinal.omega0

/-- A limit ordinal `α ≤ δ` lies below the limit part of `δ`: `α = ω * k` for some `k`, and
`ω * k ≤ δ` forces `k ≤ δ / ω`. -/
theorem succLimit_le_limitPart {α δ : Ordinal.{0}}
    (hα : Order.IsSuccLimit α) (h : α ≤ δ) :
    α ≤ limitPart δ := by
  unfold limitPart
  obtain ⟨k, rfl⟩ : Ordinal.omega0 ∣ α :=
    Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hα.isSuccPrelimit
  exact mul_le_mul_right ((Ordinal.mul_le_iff_le_div Ordinal.omega0_ne_zero).mp h) Ordinal.omega0

/-- The finite part of `limitPart ξ + i` is `i`: `(ω * q + i) % ω = i % ω = i`. -/
theorem finitePart_limitPart_add_nat (ξ : Ordinal.{0}) (i : ℕ) :
    finitePart (limitPart ξ + i) = i := by
  have h := finitePart_spec (limitPart ξ + i)
  rw [limitPart, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (Ordinal.natCast_lt_omega0 i)] at h
  exact_mod_cast h.symm

/-- The limit part of `limitPart ξ + i` is `limitPart ξ`: `(ω * q + i) / ω = q + i / ω = q`. -/
theorem limitPart_limitPart_add_nat (ξ : Ordinal.{0}) (i : ℕ) :
    limitPart (limitPart ξ + i) = limitPart ξ := by
  have h := decomposition (limitPart ξ + i)
  rw [finitePart_limitPart_add_nat] at h
  exact (Ordinal.add_right_cancel i).mp h

/-! ### Replacement of the finite part and visibility replacement -/

/-- Replace the finite part of `α` by `m` (Knight, Def. 2.2.2). -/
noncomputable def ordinalReplace (α : Ordinal.{0}) (m : ℕ) : Ordinal.{0} :=
  limitPart α + m

/-- Visibility replacement (Knight, Def. 2.2.3): if the finite part of `α` is below the
visibility threshold `K`, replace it by `m`; otherwise leave `α` unchanged. -/
noncomputable def visibilityReplace (α : Ordinal.{0}) (K m : ℕ) : Ordinal.{0} :=
  if finitePart α < K then ordinalReplace α m else α

/-- Visibility replacement on labels (Knight, Def. 2.2.1 together with Def. 2.2.3): the
bottom and top labels are fixed, and an ordinal label is replaced by `visibilityReplace`. -/
noncomputable def extVisibilityReplace (γ : ExtOrd) (K m : ℕ) : ExtOrd :=
  match γ with
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some α) => ExtOrd.ofOrd (visibilityReplace α K m)

@[simp] theorem extVisibilityReplace_bot (K m : ℕ) :
    extVisibilityReplace ⊥ K m = ⊥ := rfl

@[simp] theorem extVisibilityReplace_top (K m : ℕ) :
    extVisibilityReplace ⊤ K m = ⊤ := rfl

@[simp] theorem extVisibilityReplace_ofOrd (α : Ordinal.{0}) (K m : ℕ) :
    extVisibilityReplace (ofOrd α) K m = ofOrd (visibilityReplace α K m) := rfl

/-- `α` is a `K`-times successor: its finite part is exactly `K`.  (Ported for the record —
Knight-VC's original skeleton of Lemma 2.2.4 was stated with this predicate, which is the
wrong characterisation; see `extVisibilityReplace_self_iff`.  Currently unused.) -/
def IsKTimesSucc (α : Ordinal.{0}) (K : ℕ) : Prop := finitePart α = K

/-- `visibilityReplace α K K = α` iff `K ≤ finitePart α`, i.e. iff the visibility threshold
does not trigger.  (If it triggers, the finite part becomes `K ≠ finitePart α`, and ordinal
addition cancels on the left.) -/
theorem visibilityReplace_self_iff (α : Ordinal.{0}) (K : ℕ) :
    visibilityReplace α K K = α ↔ K ≤ finitePart α := by
  unfold visibilityReplace
  split_ifs with hlt
  · refine ⟨fun h => ?_, fun hge => absurd hlt (not_lt.mpr hge)⟩
    exfalso
    have key : limitPart α + ↑K = limitPart α + ↑(finitePart α) :=
      h.trans (decomposition α).symm
    have h2 : K = finitePart α := by exact_mod_cast add_left_cancel key
    omega
  · exact ⟨fun _ => not_lt.mp hlt, fun _ => rfl⟩

/-- Self-visibility (Knight, Lemma 2.2.4): a label `γ` satisfies `γ = γ ⊔⁺_K K` iff it is the
bottom label, the top label, or an ordinal whose finite part is at least `K`.

Knight-VC's original skeleton stated the ordinal case as `finitePart α = K`
(`IsKTimesSucc`); the correct characterisation is `K ≤ finitePart α`: for `K ≤ finitePart α`
the replacement is a no-op, and for `finitePart α < K` it changes the finite part to `K`,
which never gives back `α` (left cancellation of ordinal addition).  Knight-VC's name was
`lemma_2_2_4`. -/
theorem extVisibilityReplace_self_iff (γ : ExtOrd) (K : ℕ) :
    extVisibilityReplace γ K K = γ ↔
      (γ = (⊥ : ExtOrd) ∨ γ = (⊤ : ExtOrd) ∨
        ∃ α : Ordinal.{0}, γ = ofOrd α ∧ K ≤ finitePart α) := by
  rcases ExtOrd.cases γ with rfl | rfl | ⟨α, rfl⟩
  · simp
  · simp
  · simp [visibilityReplace_self_iff]

/-- Self-visibility at threshold `k` implies self-visibility at every `k' ≤ k`. -/
theorem extVisReplace_self_of_le {v : ExtOrd} {k k' : ℕ}
    (h : extVisibilityReplace v k k = v) (hle : k' ≤ k) :
    extVisibilityReplace v k' k' = v := by
  rw [extVisibilityReplace_self_iff] at h ⊢
  rcases h with rfl | rfl | ⟨α, rfl, hfp⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨α, rfl, hle.trans hfp⟩)

/-- For a limit ordinal `α`, visibility replacement of an ordinal `≥ α` stays `≥ α`:
`limitPart δ ≥ α`, so `ordinalReplace δ i = limitPart δ + i ≥ α`. -/
theorem visReplace_ge_of_ge_limit {α : Ordinal.{0}}
    (hα : Order.IsSuccLimit α)
    {δ : Ordinal.{0}} (hδ : α ≤ δ) (k i : ℕ) :
    α ≤ visibilityReplace δ k i := by
  unfold visibilityReplace
  split_ifs with hfp
  · exact le_trans (succLimit_le_limitPart hα hδ) le_self_add
  · exact hδ

/-- For a limit ordinal `α`, visibility replacement of an ordinal `< α` stays `< α`
(`β < α → β + 1 < α`, iterated finitely often). -/
theorem visReplace_lt_of_lt_limit {α : Ordinal.{0}}
    (hα : Order.IsSuccLimit α)
    {δ : Ordinal.{0}} (hδ : δ < α) (k i : ℕ) :
    visibilityReplace δ k i < α := by
  unfold visibilityReplace
  split_ifs with hfp
  · unfold ordinalReplace
    have hlp_lt : limitPart δ < α := lt_of_le_of_lt (limitPart_le δ) hδ
    induction i with
    | zero => simpa using hlp_lt
    | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc]
      exact hα.succ_lt ih
  · exact hδ

/-- For a limit ordinal `α`, visibility replacement on labels preserves `ofOrd α ≤ ·`
(`visReplace_ge_of_ge_limit` on ordinal labels; `⊤` is fixed). -/
theorem extVisReplace_ge_of_ge_limit {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {x : ExtOrd} (hx : ofOrd α ≤ x) (k i : ℕ) :
    ofOrd α ≤ extVisibilityReplace x k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨δ, rfl⟩
  · exact absurd hx (not_ofOrd_le_bot α)
  · exact le_top
  · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
    exact visReplace_ge_of_ge_limit hα (ofOrd_le_ofOrd.mp hx) k i

/-- For a limit ordinal `α`, visibility replacement on labels preserves `· < ofOrd α`
(`visReplace_lt_of_lt_limit` on ordinal labels; `⊥` is fixed). -/
theorem extVisReplace_lt_of_lt_limit {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {x : ExtOrd} (hx : x < ofOrd α) (k i : ℕ) :
    extVisibilityReplace x k i < ofOrd α := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨δ, rfl⟩
  · exact bot_lt_ofOrd α
  · exact absurd hx (not_lt.mpr le_top)
  · rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
    exact visReplace_lt_of_lt_limit hα (ofOrd_lt_ofOrd.mp hx) k i

/-- Visibility replacement stays `≤ δ` when `γ ≤ δ`, `δ` is self-visible at `k`, and the
replacement value is `≤ k`. -/
theorem visReplace_le_of_le_selfVis {γ δ : Ordinal.{0}} {k i : ℕ}
    (hγδ : γ ≤ δ) (hδ_sv : k ≤ finitePart δ) (hi : i ≤ k) :
    visibilityReplace γ k i ≤ δ := by
  unfold visibilityReplace
  split_ifs with h
  · unfold ordinalReplace
    have hi' : (i : Ordinal) ≤ (k : Ordinal) := by exact_mod_cast hi
    have hk' : (k : Ordinal) ≤ (finitePart δ : Ordinal) := by exact_mod_cast hδ_sv
    calc limitPart γ + (i : Ordinal)
        ≤ limitPart δ + (k : Ordinal) := add_le_add (limitPart_mono hγδ) hi'
      _ ≤ limitPart δ + (finitePart δ : Ordinal) := add_le_add_right hk' (limitPart δ)
      _ = δ := decomposition δ
  · exact hγδ

/-- `extVisibilityReplace` stays `≤ ofOrd δ` when `x ≤ ofOrd γ`, `γ ≤ δ`, `δ` is self-visible
at `k`, and the replacement value is `≤ k`. -/
theorem extVisReplace_le_of_le {γ δ : Ordinal.{0}} {k i : ℕ} {x : ExtOrd}
    (hx : x ≤ ofOrd γ) (hγδ : γ ≤ δ) (hδ_sv : k ≤ finitePart δ) (hi : i ≤ k) :
    extVisibilityReplace x k i ≤ ofOrd δ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact bot_le
  · exact absurd hx (not_top_le_ofOrd γ)
  · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
    exact visReplace_le_of_le_selfVis ((ofOrd_le_ofOrd.mp hx).trans hγδ) hδ_sv hi

/-! ### Vertical truncation of labels -/

/-- Vertical truncation of a label at stage `α` (the pointwise content of Knight's reduction
map, Def. 3.1.2, on a single cell): ordinal labels `≥ α` become the top label `⊤`; ordinal
labels `< α`, and `⊥`, `⊤`, are kept.  This is the **strict** truncation (decision #84): the
boundary label `ofOrd α` is sent to `⊤`, so the labels of a stage-`α` type are `< ofOrd α` or
`⊤` (`truncExt_bound`), and truncation commutes with visibility replacement at every limit
stage without a boundary side condition (`truncExt_evr_comm`); Knight-VC's non-strict variant
(`β ≤ α` kept) fails there. -/
noncomputable def truncExt (α : Ordinal.{0}) (γ : ExtOrd) : ExtOrd :=
  match γ with
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some β) => if β < α then ExtOrd.ofOrd β else ⊤

@[simp] theorem truncExt_bot (α : Ordinal.{0}) : truncExt α ⊥ = ⊥ := rfl

@[simp] theorem truncExt_top (α : Ordinal.{0}) : truncExt α ⊤ = ⊤ := rfl

theorem truncExt_ofOrd (α β : Ordinal.{0}) :
    truncExt α (ofOrd β) = if β < α then ofOrd β else ⊤ := rfl

@[simp] theorem truncExt_ofOrd_of_lt {α β : Ordinal.{0}} (h : β < α) :
    truncExt α (ofOrd β) = ofOrd β := by
  rw [truncExt_ofOrd, ite_eq_left h]

@[simp] theorem truncExt_ofOrd_of_le {α β : Ordinal.{0}} (h : α ≤ β) :
    truncExt α (ofOrd β) = ⊤ := by
  rw [truncExt_ofOrd, ite_eq_right (not_lt_of_ge h)]

/-- A truncated label is `< ofOrd α` or the top label (the label bound of a stage-`α` type;
note `⊥ < ofOrd α`). -/
theorem truncExt_bound (α : Ordinal.{0}) (γ : ExtOrd) :
    truncExt α γ < ofOrd α ∨ truncExt α γ = (⊤ : ExtOrd) := by
  rcases ExtOrd.cases γ with rfl | rfl | ⟨β, rfl⟩
  · exact Or.inl (bot_lt_ofOrd α)
  · exact Or.inr rfl
  · rcases lt_or_ge β α with h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (truncExt_ofOrd_of_le h)

/-- `truncExt α` is the identity on labels `< ofOrd α`. -/
theorem truncExt_id_of_lt {α : Ordinal.{0}} {x : ExtOrd} (hx : x < ofOrd α) :
    truncExt α x = x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · rfl
  · exact absurd hx (not_lt.mpr le_top)
  · exact truncExt_ofOrd_of_lt (ofOrd_lt_ofOrd.mp hx)

/-- `truncExt α` is the identity on labels already bounded at stage `α`
(`x < ofOrd α ∨ x = ⊤`, the label bound of a stage-`α` type); together with
`truncExt_bound` this is the reflexivity law of vertical reduction. -/
theorem truncExt_id_of_bound {α : Ordinal.{0}} {x : ExtOrd}
    (h : x < ofOrd α ∨ x = ⊤) : truncExt α x = x := by
  rcases h with hlt | rfl
  · exact truncExt_id_of_lt hlt
  · rfl

/-- Labels `≥ ofOrd α` (the boundary label included) truncate to the top label. -/
theorem truncExt_eq_top_of_ge {α : Ordinal.{0}} {x : ExtOrd} (hx : ofOrd α ≤ x) :
    truncExt α x = ⊤ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact absurd hx (not_ofOrd_le_bot α)
  · rfl
  · exact truncExt_ofOrd_of_le (ofOrd_le_ofOrd.mp hx)

/-- A label truncates to the top label iff it is `≥ ofOrd α`. -/
theorem truncExt_eq_top_iff {α : Ordinal.{0}} {x : ExtOrd} :
    truncExt α x = ⊤ ↔ ofOrd α ≤ x := by
  refine ⟨fun h => ?_, truncExt_eq_top_of_ge⟩
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact absurd h bot_ne_top
  · exact le_top
  · rcases lt_or_ge β α with hβα | hβα
    · rw [truncExt_ofOrd_of_lt hβα] at h
      exact absurd h (ofOrd_ne_top β)
    · exact ofOrd_le_ofOrd.mpr hβα

/-- `truncExt α` is inflationary: `x ≤ truncExt α x`. -/
theorem truncExt_le_self (α : Ordinal.{0}) (x : ExtOrd) : x ≤ truncExt α x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact bot_le
  · exact le_rfl
  · rcases lt_or_ge β α with hβ | hβ
    · rw [truncExt_ofOrd_of_lt hβ]
    · rw [truncExt_ofOrd_of_le hβ]; exact le_top

/-- `truncExt α` is monotone. -/
theorem truncExt_mono (α : Ordinal.{0}) : Monotone (truncExt α) := by
  intro x y hxy
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact bot_le
  · rw [top_le_iff.mp hxy]
  · rcases lt_or_ge β α with hβ | hβ
    · rw [truncExt_ofOrd_of_lt hβ]
      exact hxy.trans (truncExt_le_self α y)
    · rw [truncExt_ofOrd_of_le hβ,
        truncExt_eq_top_of_ge ((ofOrd_le_ofOrd.mpr hβ).trans hxy)]

/-- Self-visibility is preserved by truncation: an ordinal label `< α` is unchanged, and one
`≥ α` becomes `⊤`, which is self-visible. -/
theorem truncExt_preserves_selfVis (α : Ordinal.{0}) (γ : ExtOrd) (K : ℕ)
    (h : extVisibilityReplace γ K K = γ) :
    extVisibilityReplace (truncExt α γ) K K = truncExt α γ := by
  rcases ExtOrd.cases γ with rfl | rfl | ⟨β, rfl⟩
  · rfl
  · rfl
  · rcases lt_or_ge β α with hβ | hβ
    · rwa [truncExt_ofOrd_of_lt hβ]
    · rw [truncExt_ofOrd_of_le hβ, extVisibilityReplace_top]

/-- `truncExt α` distributes over `min`. -/
theorem truncExt_min (α : Ordinal.{0}) (x y : ExtOrd) :
    truncExt α (min x y) = min (truncExt α x) (truncExt α y) := by
  rcases le_total x y with hle | hle
  · rw [min_eq_left hle, min_eq_left (truncExt_mono α hle)]
  · rw [min_eq_right hle, min_eq_right (truncExt_mono α hle)]

/-- Truncations compose: for `γ ≤ α`, truncating at `γ` after truncating at `α` is truncating
at `γ` (the transitivity law of vertical reduction). -/
theorem truncExt_compose {γ α : Ordinal.{0}} (hle : γ ≤ α) (x : ExtOrd) :
    truncExt γ (truncExt α x) = truncExt γ x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · rfl
  · rfl
  · rcases lt_or_ge β α with hβα | hβα
    · rw [truncExt_ofOrd_of_lt hβα]
    · rw [truncExt_ofOrd_of_le hβα, truncExt_top, truncExt_ofOrd_of_le (hle.trans hβα)]

/-- Truncation is idempotent. -/
theorem truncExt_truncExt (α : Ordinal.{0}) (x : ExtOrd) :
    truncExt α (truncExt α x) = truncExt α x :=
  truncExt_compose le_rfl x

/-- For an inflationary monotone `σ`, `truncExt α ∘ σ ∘ truncExt α = truncExt α ∘ σ`. -/
theorem truncExt_comp_infl {α : Ordinal.{0}} {σ : ExtOrd → ExtOrd}
    (hσ_mono : Monotone σ) (hσ_infl : ∀ x, x ≤ σ x) (x : ExtOrd) :
    truncExt α (σ (truncExt α x)) = truncExt α (σ x) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · rfl
  · rfl
  · rcases lt_or_ge β α with hβα | hβα
    · rw [truncExt_ofOrd_of_lt hβα]
    · rw [truncExt_ofOrd_of_le hβα]
      have h1 : ofOrd α ≤ σ (ofOrd β) := (ofOrd_le_ofOrd.mpr hβα).trans (hσ_infl _)
      rw [truncExt_eq_top_of_ge (h1.trans (hσ_mono le_top)), truncExt_eq_top_of_ge h1]

/-- Truncation preserves and reflects the bottom label. -/
theorem truncExt_eq_bot_iff {α : Ordinal.{0}} {x : ExtOrd} :
    truncExt α x = ⊥ ↔ x = ⊥ := by
  refine ⟨fun h => ?_, fun h => by rw [h, truncExt_bot]⟩
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · rfl
  · exact absurd h top_ne_bot
  · rcases lt_or_ge β α with hβα | hβα
    · rw [truncExt_ofOrd_of_lt hβα] at h
      exact absurd h (ofOrd_ne_bot β)
    · rw [truncExt_ofOrd_of_le hβα] at h
      exact absurd h top_ne_bot

/-- Truncation commutes with visibility replacement at every limit stage `α`, for every label
and every threshold and replacement value (Knight, Def. 2.3.9(5) for the reduction map):
`truncExt α (evr x k i) = evr (truncExt α x) k i`.  For an ordinal label `δ < α` the
replacement stays `< α` (`visReplace_lt_of_lt_limit`) and both sides are the replacement; for
`δ ≥ α` it stays `≥ α` (`visReplace_ge_of_ge_limit`) and both sides are `⊤`.  (With
Knight-VC's non-strict truncation `T`, keeping `ofOrd α`, this fails at the boundary label,
e.g. `α = ω`, `k = i = 1`: `T ω (evr (ofOrd ω) 1 1) = ⊤` but
`evr (T ω (ofOrd ω)) 1 1 = ofOrd (ω + 1)`; that was the reason for decision #84.) -/
theorem truncExt_evr_comm {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    (x : ExtOrd) (k i : ℕ) :
    truncExt α (extVisibilityReplace x k i) =
    extVisibilityReplace (truncExt α x) k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨δ, rfl⟩
  · rfl
  · rfl
  · rcases lt_or_ge δ α with hδ | hδ
    · rw [truncExt_ofOrd_of_lt hδ, extVisibilityReplace_ofOrd,
        truncExt_ofOrd_of_lt (visReplace_lt_of_lt_limit hα hδ k i)]
    · rw [truncExt_ofOrd_of_le hδ, extVisibilityReplace_ofOrd,
        truncExt_ofOrd_of_le (visReplace_ge_of_ge_limit hα hδ k i), extVisibilityReplace_top]

/-! ### Non-successor stages and canonical block levels -/

/-- A non-successor ordinal: zero or a limit.  Knight's Def. 3.2.1(4)(b) quantifies over
"non-successor `γ` with `0 ≤ γ < α`", which includes `γ = 0`, excluded by Mathlib's
`Order.IsSuccLimit` (`Ordinal.not_isSuccLimit_zero`). -/
def IsNonSuccessor (γ : Ordinal.{0}) : Prop := γ = 0 ∨ Order.IsSuccLimit γ

/-- For ordinals, "non-successor" is exactly Mathlib's `Order.IsSuccPrelimit`. -/
theorem isNonSuccessor_iff_isSuccPrelimit {γ : Ordinal.{0}} :
    IsNonSuccessor γ ↔ Order.IsSuccPrelimit γ := by
  unfold IsNonSuccessor
  rw [Ordinal.isSuccLimit_iff]
  constructor
  · rintro (rfl | ⟨-, h⟩)
    · exact Order.isSuccPrelimit_bot
    · exact h
  · intro h
    by_cases h0 : γ = 0
    · exact Or.inl h0
    · exact Or.inr ⟨h0, h⟩

/-- The canonical block levels `ω + ω * ξ` (the ω-blocks of `docs/TERMINOLOGY.md`): block `ξ`
is the step from `blockLevel ξ` to `blockLevel (ξ + 1) = blockLevel ξ + ω`. -/
noncomputable def blockLevel (ξ : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.omega0 + Ordinal.omega0 * ξ

theorem blockLevel_succ (ξ : Ordinal.{0}) :
    blockLevel (Order.succ ξ) = blockLevel ξ + Ordinal.omega0 := by
  unfold blockLevel
  rw [Ordinal.mul_succ, add_assoc]

theorem blockLevel_strictMono : StrictMono blockLevel := by
  intro ξ η h
  unfold blockLevel
  exact add_lt_add_right ((Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono h) _

theorem blockLevel_lt_blockLevel {ξ η : Ordinal.{0}} (h : ξ < η) :
    blockLevel ξ < blockLevel η :=
  blockLevel_strictMono h

@[simp] theorem blockLevel_zero : blockLevel 0 = Ordinal.omega0 := by
  simp [blockLevel]

/-- Every canonical block level is a limit ordinal. -/
theorem isSuccLimit_blockLevel (ξ : Ordinal.{0}) : Order.IsSuccLimit (blockLevel ξ) := by
  unfold blockLevel
  rw [Ordinal.isSuccLimit_iff, Ordinal.isSuccPrelimit_iff_omega0_dvd]
  exact ⟨(Ordinal.omega0_pos.trans_le le_self_add).ne',
    (Ordinal.dvd_add_iff dvd_rfl).mpr (dvd_mul_right _ _)⟩

end Value

end VaughtConjecture.Knight
