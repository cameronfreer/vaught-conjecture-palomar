/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TraceBoundary

/-! # The empty-seed boundary (#57 — the rank-zero branch of the terminal boundary)

Companion to `Knight/TraceBoundary.lean` (kept stable as merged by PR #198): the RANK-ZERO
branch of the terminal trace/menu boundary.

## Scope correction (2026-08-26)

PR #199 supplies, for every countable block-zero source model, the disjunction
`RankZeroStoppedReceipt R ∨ Nonempty (StoppedReceipt R)` — but `TraceBoundary`'s
`exists_seed_iso_of_menuIntersection` consumes two POSITIVE `StoppedReceipt`s, so its
"menu intersection is the only missing hypothesis" record covers the positive branch only.
This module closes the gap: on the rank-zero branch NO receipt data are needed to seed the
pairing —

* `exists_eval_empty`: every block-zero model evaluates the empty tuple (`hR.covering`
  pulled back along the empty embedding);
* `exists_empty_pairedSeed`: any TWO countable block-zero source models admit the EMPTY
  `PairedCover` seed — the empty common chart.  `S α 0` is a subsingleton
  (`subsingleton_zero`), so the two empty labels agree and the `red_eq` matching field is
  definitional; no run level, no cutoff, no `RankZeroCode` payload enters;
* `exists_empty_seed_iso_of_menuIntersection` — **the rank-zero boundary record**: from the
  empty seed, two-sided `MenuIntersectionSupply` is the ONLY hypothesis missing for
  `Nonempty (R₁.Iso R₂)`.  The proof consumes the SAME conditional bridge as the positive
  record (`menuIntersection_iff_jointSupply` + `nonempty_iso_of_jointTraceSupply`, with the
  sources as their own witnesses through `Realization.reduct_refl`): no new Karp machinery,
  no separate back-and-forth, no rank-zero classifier.

## The completed boundary story

Together, `TraceBoundary.exists_seed_iso_of_menuIntersection` (positive receipts, the
code-matched seed) and this module's `exists_empty_seed_iso_of_menuIntersection` (the empty
seed, receipt-free) cover BOTH branches of #199's disjunction: for ANY two countable
block-zero source models there is a paired seed for which two-sided menu intersection is
the only missing hypothesis for isomorphism.  This module therefore covers the RANK-ZERO
CONDITIONAL KARP INTERFACE — it does not complete rank-zero classification.  The empty
seed is ONE sufficient receipt-free rank-zero route: the eventual producer/selector
theorem for `MenuIntersectionSupply` — the open residual, whatever genuinely new input
reopens it (see the terminal ruling in `Knight/TraceBoundary.lean`) — may supply the
two-sided intersection from this empty seed or from another construction-selected seed
covering the rank-zero branch; rank zero adds no other obligation.

Staleness note (#179): the pre-#181 `RankZeroWitness` (¬STP-based, `origin/e7/rankzero-class`)
is a stale witness basis — post-#181 a certified block-zero stop may have `SourceTopProduction`
(`RankZeroStoppedReceipt.ofNoProlongation` vs the demoted `ofNotSourceTopProduction`) — and
cannot be treated as the completed rank-zero branch; this module is its replacement.

**Mainline placement**: like `Knight/PairedTrace.lean` and `Knight/TraceBoundary.lean`,
deliberately NOT root-exported (construction-facing); mainline, fully compiled, covered by
the build and the axiom audit. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

namespace KnightRealization

variable {M M₁ M₂ : Type w}

/-- **Every block-zero model evaluates the empty tuple**: covering at the empty embedding
produces some evaluated extension, and exact consistency pulls its label back along the
empty face — no receipt data are involved. -/
theorem exists_eval_empty {R : KnightRealization (blockStage 0) M} (hR : R.IsModel) :
    ∃ p₀ : S (blockStage 0).1 0,
      R.eval (Function.Embedding.ofIsEmpty : Fin 0 ↪ M) = some p₀ := by
  obtain ⟨k, s, -, hsome⟩ := hR.covering (Function.Embedding.ofIsEmpty : Fin 0 ↪ M)
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hsome
  let f : Fin 0 ↪ Fin (0 + k) := Function.Embedding.ofIsEmpty
  have hcons := hR.consistent s Q f hQ
  have hsome' : (knightTower.pull f Q).isSome := by
    change (typeMap f Q).isSome
    apply (typeMap_isSome_iff f Q).mpr
    have h0 : Finset.univ.image f = (∅ : Finset (Fin (0 + k))) := by
      simp [Finset.univ_eq_empty]
    rw [h0]
    exact Q.scheme.scheme.isPlan.empty_mem
  obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp hsome'
  have hft : f.trans s = (Function.Embedding.ofIsEmpty : Fin 0 ↪ M) :=
    Function.Embedding.ext fun i => i.elim0
  exact ⟨p₀, by rw [← hft, hcons, hp₀]; rfl⟩

/-- **The empty paired seed**: any two block-zero source models — as their own witnesses,
at the identity stage links — admit the empty `PairedCover`.  The two empty labels agree
because `S α 0` is a subsingleton, so the `red_eq` matching field is definitional; no
receipt, code, or `RankZeroCode` payload enters. -/
theorem exists_empty_pairedSeed {R₁ : KnightRealization (blockStage 0) M₁}
    {R₂ : KnightRealization (blockStage 0) M₂} (hR₁ : R₁.IsModel) (hR₂ : R₂.IsModel) :
    ∃ s : PairedCover (le_refl (blockStage 0)) (le_refl (blockStage 0)) R₁ R₂,
      s.arity = 0 := by
  obtain ⟨p₁, hp₁⟩ := exists_eval_empty hR₁
  obtain ⟨p₂, hp₂⟩ := exists_eval_empty hR₂
  have hp : p₁ = p₂ := Subsingleton.elim _ _
  subst p₂
  exact ⟨⟨0, Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty,
    p₁, p₁, hp₁, hp₂, rfl⟩, rfl⟩

/-- **THE RANK-ZERO BOUNDARY RECORD** (the empty-seed analogue of
`exists_seed_iso_of_menuIntersection`), a CONDITIONAL theorem: any two countable
block-zero source models admit the EMPTY paired seed, for which the two-sided
menu-intersection property is the ONLY hypothesis missing for isomorphism of the sources.
Together with the positive-receipt record this covers BOTH branches of #199's
`RankZeroStoppedReceipt ∨ Nonempty StoppedReceipt` disjunction — see the module
docstring.  Same conditional bridge, no new machinery; `MenuIntersectionSupply` itself
remains the open residual. -/
theorem exists_empty_seed_iso_of_menuIntersection [Countable M₁] [Countable M₂]
    {R₁ : KnightRealization (blockStage 0) M₁} {R₂ : KnightRealization (blockStage 0) M₂}
    (hR₁ : R₁.IsModel) (hR₂ : R₂.IsModel) :
    ∃ s : PairedCover (le_refl (blockStage 0)) (le_refl (blockStage 0)) R₁ R₂,
      s.arity = 0 ∧
      (MenuIntersectionSupply R₁ R₂ s → MenuIntersectionSupply R₂ R₁ s.swap →
        Nonempty (R₁.Iso R₂)) := by
  obtain ⟨s, hs⟩ := exists_empty_pairedSeed hR₁ hR₂
  refine ⟨s, hs, fun hf hb => ?_⟩
  exact nonempty_iso_of_jointTraceSupply hR₁ hR₂
    (Realization.reduct_refl R₁) (Realization.reduct_refl R₂) s
    ((menuIntersection_iff_jointSupply (Realization.reduct_refl R₁)
      (Realization.reduct_refl R₂) s).mp hf)
    ((menuIntersection_iff_jointSupply (Realization.reduct_refl R₂)
      (Realization.reduct_refl R₁) s.swap).mp hb)

end KnightRealization

end VaughtConjecture.Knight
