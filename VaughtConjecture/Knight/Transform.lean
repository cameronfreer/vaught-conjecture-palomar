/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.MinMax
public import VaughtConjecture.Knight.Value

/-! # Knight's transformation calculus on labelled cells

Ported from Knight-VC `KnightVC/Transforms.lean` @ f7c7847d, with Knight-VC's `arity`
renamed `grade` (the grade function `D → ℕ` of a family of cells; see `docs/TERMINOLOGY.md`).

A family of cells `D` with grades `grade : D → ℕ` carries labellings `p : D → ExtOrd`
(Knight, Defs. 2.3.*):

* `IsOrderly grade p` (Def. 2.3.4): every label is self-visible at the grade of its cell,
  `p d = p d ⊔⁺_{grade d} grade d`;
* `IsGradeSuppression grade p q g` (Def. 2.3.5): `q` is `p` capped by an antitone, self-visible
  suppressor `g` evaluated at the grade of each cell;
* `TransformsTo grade p q` (Def. 2.3.9, the directed approximation `p ⇒ q`): there are a
  suppressor `g` and a "shifter" `σ : ExtOrd → ExtOrd` (fixing `⊥`, monotone, and commuting
  with visibility replacement `⊔⁺_k i`, `i ≤ k`, on labels `α` with `σ α ≤ g k`) with
  `q d = min (σ (p d)) (g (grade d))`;
* `Equivalent grade p q` is `p ⇒ q ∧ q ⇒ p` (the two-sided relation, analogous to Def. 2.3.2's
  `⇔_K` for `⇒_K`; the paper does not name it separately).

## Fidelity status

`TransformsTo` is the **faithful** transcription of Def. 2.3.9 (and `Equivalent` its two-sided
form); these are the only relations in the repository (#85).  Knight-VC's relation — the shifter
additionally **inflationary** (`∀ x, x ≤ σ x`) and clause 5 **guarded** by `g k ≠ ⊤` — was kept
here transitionally (as `LegacyTransformsTo`) while faithful closure under vertical reduction was
blocked, because the stage-type instance then truncated labels *and* rows and the transport
needed inflationarity (`truncExt_comp_infl`); it was **retired** (#88 (2/2), #89) once the
faithful closure with the semantics fixed landed (`TransformsTo.truncExt_target`).  The paper
argues Lemma 3.1.3 through transitivity of `⇒` (Lemma 2.3.14), whose printed composite witness
`(min (h, τ ∘ g), τ ∘ σ)` is refuted at the equality orbit (Knight-VC
`docs/paper/formalization-discrepancies.md`, Section 2.3 / item 5); the reduction half of
Lemma 3.1.3 with the rows kept is nevertheless available, by a direct witness and without
transitivity (`TransformsTo.truncExt_target`, #89; see its docstring).

Facts.  `TransformsTo` is reflexive (`TransformsTo.refl`, witnesses `σ = id`, `g = ⊤`),
pulls back along any reindexing of the cells (`TransformsTo.reindex`), every labelling
transforms to its truncation at a limit stage (`TransformsTo.truncExt_self`, witnesses
`σ = truncExt α`, `g = ⊤`, by `truncExt_evr_comm`), and `⇒` is closed under strict truncation
of the target at a limit stage, source fixed (`TransformsTo.truncExt_target`, witnesses
`truncExt α ∘ g`, `truncExt α ∘ σ`). General existential transitivity is false:
`SharpWitnessCompositionControls.not_transitive` proves a counterexample. Restricted
post-composition remains available in `RestrictedComposition.lean`; the counterexample
does not invalidate those guarded statements. -/

@[expose] public section

namespace VaughtConjecture.Knight

namespace Transform

open Value ExtOrd

section

variable {D : Type*} (grade : D → ℕ)

/-- Orderliness (Knight, Def. 2.3.4): each label of `p` is self-visible at the grade of its
cell, `p d = extVisibilityReplace (p d) (grade d) (grade d)`. -/
def IsOrderly (p : D → ExtOrd) : Prop :=
  ∀ d : D, p d = extVisibilityReplace (p d) (grade d) (grade d)

/-- Grade suppression (Knight, Def. 2.3.5): `q d = min (p d) (g (grade d))` for an antitone,
self-visible suppressor `g : ℕ → ExtOrd` (`g n` is self-visible at threshold `n`). -/
def IsGradeSuppression (p q : D → ExtOrd) (g : ℕ → ExtOrd) : Prop :=
  (∀ n m : ℕ, n < m → g m ≤ g n) ∧
  (∀ n : ℕ, g n = extVisibilityReplace (g n) n n) ∧
  (∀ d : D, q d = min (p d) (g (grade d)))

/-- The transformation relation `p ⇒ q` (Knight, Def. 2.3.9, verbatim): there are a
suppressor `g : ℕ → ExtOrd` and a shifter `σ : ExtOrd → ExtOrd` with

1. `g` antitone: `n < m → g m ≤ g n`;
2. `g` self-visible: `g n = g n ⊔⁺_n n`;
3. `σ ⊥ = ⊥`;
4. `σ` monotone;
5. for all `α` and `k` with `σ α ≤ g k` and all `i ≤ k`, `σ (α ⊔⁺_k i) = σ α ⊔⁺_k i`;

such that `q d = min (σ (p d)) (g (grade d))` for every cell `d`.  (No inflationarity of `σ`
and no guard on clause 5, unlike Knight-VC's relation; see the module docstring.) -/
def TransformsTo (p q : D → ExtOrd) : Prop :=
  ∃ (g : ℕ → ExtOrd) (σ : ExtOrd → ExtOrd),
    (∀ n m : ℕ, n < m → g m ≤ g n) ∧
    (∀ n : ℕ, g n = extVisibilityReplace (g n) n n) ∧
    (σ (⊥ : ExtOrd) = ⊥) ∧
    Monotone σ ∧
    (∀ (α : ExtOrd) (k : ℕ),
        σ α ≤ g k →
        ∀ i : ℕ, i ≤ k →
          σ (extVisibilityReplace α k i) = extVisibilityReplace (σ α) k i) ∧
    (∀ d : D, q d = min (σ (p d)) (g (grade d)))

/-- Two-sided transformation `p ⇔ q`: `p ⇒ q` and `q ⇒ p` (analogous to Def. 2.3.2's `⇔_K`). -/
def Equivalent (p q : D → ExtOrd) : Prop :=
  TransformsTo grade p q ∧ TransformsTo grade q p

end

variable {D : Type*} {grade : D → ℕ}

/-! ### The faithful relation -/

/-- Reflexivity: every labelling transforms to itself, with witnesses `σ = id` and `g = ⊤`
(clause 5 holds for `id` trivially). -/
theorem TransformsTo.refl (p : D → ExtOrd) : TransformsTo grade p p :=
  ⟨fun _ => ⊤, id,
    fun _ _ _ => le_refl ⊤,
    fun _ => rfl,
    rfl,
    monotone_id,
    fun _ _ _ _ _ => rfl,
    fun d => (min_top_right (p d)).symm⟩

/-- Reindexing: a transformation on cells `D` pulls back along any map `φ : D' → D` of cell
families (same witnesses `g`, `σ`; used to transport locality along face restriction). -/
theorem TransformsTo.reindex {D' : Type*} {p q : D → ExtOrd} (h : TransformsTo grade p q)
    (φ : D' → D) : TransformsTo (grade ∘ φ) (p ∘ φ) (q ∘ φ) := by
  obtain ⟨g, σ, hg_dec, hg_vis, hσ_bot, hσ_mono, hσ_vis, hσ_eq⟩ := h
  exact ⟨g, σ, hg_dec, hg_vis, hσ_bot, hσ_mono, hσ_vis, fun d => hσ_eq (φ d)⟩

/-- Every labelling transforms to its vertical truncation at a limit stage `α`:
`p ⇒ truncExt α ∘ p`, with witnesses `σ = truncExt α` and `g = ⊤` (clause 5 is
`truncExt_evr_comm`).  This is the reduction map as a transformation; the paper combines it
with transitivity (Lemma 2.3.14) to keep the rows under reduction (Lemma 3.1.3). -/
theorem TransformsTo.truncExt_self {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    (p : D → ExtOrd) : TransformsTo grade p (truncExt α ∘ p) :=
  ⟨fun _ => ⊤, truncExt α,
    fun _ _ _ => le_refl ⊤,
    fun _ => rfl,
    rfl,
    truncExt_mono α,
    fun x k _ i _ => truncExt_evr_comm hα x k i,
    fun _ => (min_top_right _).symm⟩

/-- **Faithful closure under strict truncation of the target, source fixed** (the reduction
half of Lemma 3.1.3, proved directly at a limit stage `α`, without transitivity): if `p ⇒ q`
then `p ⇒ truncExt α ∘ q`, with the truncated witnesses `(truncExt α ∘ g, truncExt α ∘ σ)`.

Clause 5 for the truncated witnesses, given `truncExt α (σ x) ≤ truncExt α (g k)` and `i ≤ k`:
the right-hand side is `truncExt α (evr (σ x) k i)` (`truncExt_evr_comm`).  If `σ x ≤ g k`
the original clause applies.  Otherwise `g k < σ x`, so the two truncations coincide and are
`⊤` (if they were `< ofOrd α` both labels would be fixed and equal), i.e. `ofOrd α ≤ g k` and
`ofOrd α ≤ σ x`.  The right-hand side is then `⊤` (`extVisReplace_ge_of_ge_limit`), and the
left-hand side is `⊤` once `ofOrd α ≤ σ (evr x k i)`: clear if `evr x k i ≥ x` (monotonicity
of `σ`; this covers `x = ⊤`, the untriggered case `k ≤ finitePart ξ`, and `i ≥ finitePart ξ`),
and otherwise `x = ofOrd ξ` with `i < finitePart ξ =: m < k`, `y := evr x k i =
ofOrd (limitPart ξ + i)` satisfies `evr y k m = x`; if `σ y < ofOrd α ≤ g k`, the original
clause at `y` gives `σ x = evr (σ y) k m < ofOrd α` (`extVisReplace_lt_of_lt_limit`), a
contradiction.  This is exactly the case Knight-VC's guard `g k ≠ ⊤` excludes (there
`truncExt α (g k) = ⊤` makes the clause vacuous), which is why the route needed the faithful
relation. -/
theorem TransformsTo.truncExt_target {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {p q : D → ExtOrd} (h : TransformsTo grade p q) :
    TransformsTo grade p (truncExt α ∘ q) := by
  obtain ⟨g, σ, hg_dec, hg_vis, hσ_bot, hσ_mono, hσ_vis, hσ_eq⟩ := h
  refine ⟨truncExt α ∘ g, truncExt α ∘ σ,
    fun n m h => truncExt_mono α (hg_dec n m h),
    fun k => (truncExt_preserves_selfVis α _ _ (hg_vis k).symm).symm,
    by rw [Function.comp_apply, hσ_bot]; rfl,
    fun x y hxy => truncExt_mono α (hσ_mono hxy),
    ?_,
    fun d => by simp only [Function.comp_apply]; rw [hσ_eq d, truncExt_min]⟩
  intro x k hle i hi
  simp only [Function.comp_apply] at hle ⊢
  rw [← truncExt_evr_comm hα (σ x) k i]
  by_cases hxk : σ x ≤ g k
  · -- the original clause applies
    rw [hσ_vis x k hxk i hi]
  -- `g k < σ x`: both truncations are `⊤`
  have hlt : g k < σ x := not_le.mp hxk
  have htop : truncExt α (g k) = ⊤ := by
    have heq : truncExt α (g k) = truncExt α (σ x) :=
      le_antisymm (truncExt_mono α hlt.le) hle
    rcases truncExt_bound α (g k) with hb | hb
    · exfalso
      have hgk : truncExt α (g k) = g k :=
        truncExt_id_of_lt ((truncExt_le_self α (g k)).trans_lt hb)
      have hσx : truncExt α (σ x) = σ x :=
        truncExt_id_of_lt ((truncExt_le_self α (σ x)).trans_lt (heq ▸ hb))
      exact hlt.ne (by rw [← hgk, heq, hσx])
    · exact hb
  have hαg : ofOrd α ≤ g k := truncExt_eq_top_iff.mp htop
  have hασ : ofOrd α ≤ σ x := hαg.trans hlt.le
  rw [truncExt_eq_top_of_ge (extVisReplace_ge_of_ge_limit hα hασ k i)]
  apply truncExt_eq_top_of_ge
  -- it remains to see `ofOrd α ≤ σ (evr x k i)`
  rcases ExtOrd.cases x with rfl | rfl | ⟨ξ, rfl⟩
  · exact absurd (hσ_bot ▸ hlt) (not_lt_bot)
  · simpa [extVisibilityReplace_top] using hασ
  rw [extVisibilityReplace_ofOrd]
  unfold visibilityReplace
  split_ifs with hfp
  · unfold ordinalReplace
    rcases le_or_gt (finitePart ξ) i with hmi | him
    · -- `i ≥ finitePart ξ`: the replaced label dominates `x`
      have hxy : ofOrd ξ ≤ ofOrd (limitPart ξ + i) := by
        rw [ofOrd_le_ofOrd]
        calc ξ = limitPart ξ + (finitePart ξ : Ordinal) := (decomposition ξ).symm
          _ ≤ limitPart ξ + (i : Ordinal) :=
              add_le_add_right (Nat.cast_le.mpr hmi : (finitePart ξ : Ordinal) ≤ i) _
      exact hασ.trans (hσ_mono hxy)
    · -- `i < finitePart ξ < k`: replacing back at `finitePart ξ` recovers `x`
      by_contra hcon
      have hσy_lt : σ (ofOrd (limitPart ξ + i)) < ofOrd α := not_le.mp hcon
      have hback : extVisibilityReplace (ofOrd (limitPart ξ + i)) k (finitePart ξ) = ofOrd ξ := by
        rw [extVisibilityReplace_ofOrd, visibilityReplace,
          ite_eq_left (by rw [finitePart_limitPart_add_nat]; exact him.trans hfp),
          ordinalReplace, limitPart_limitPart_add_nat, decomposition]
      have hclause := hσ_vis (ofOrd (limitPart ξ + i)) k (hσy_lt.le.trans hαg)
        (finitePart ξ) hfp.le
      rw [hback] at hclause
      exact absurd (hclause ▸ hασ)
        (not_le.mpr (extVisReplace_lt_of_lt_limit hα hσy_lt k (finitePart ξ)))
  · exact hασ

/-- `Equivalent` is reflexive. -/
theorem Equivalent.refl (p : D → ExtOrd) : Equivalent grade p p :=
  ⟨TransformsTo.refl p, TransformsTo.refl p⟩

/-- Every labelling transforms to the constantly-`−∞` labelling (witnesses `σ ≡ ⊥`, `g ≡ ⊤`;
clause 5 is `⊥ = ⊥`). -/
theorem TransformsTo.to_bot {X : Type*} {grade : X → ℕ} (p : X → ExtOrd) :
    TransformsTo grade p (fun _ => ⊥) :=
  ⟨fun _ => ⊤, fun _ => ⊥,
    fun _ _ _ => le_refl ⊤,
    fun _ => rfl,
    rfl,
    monotone_const,
    fun _ _ _ _ _ => (extVisibilityReplace_bot _ _).symm,
    fun _ => (min_eq_left bot_le).symm⟩

end Transform

end VaughtConjecture.Knight
