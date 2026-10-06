/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.TypeTower.Basic

/-! # Prolongation up to isomorphism

The public, isomorphism-invariant **prolongation** predicate on realizations of a type tower
(issue #29; TERMINOLOGY: *prolongation*, never "expansion" except when quoting Knight).

Knight's Def. 5.1.1 says that a model `N` of `S^β` is an *expansion* of a model `M` of `S^α`
(`α < β`) when `M = S ι_{α,β} ∘ N` — literally, on the same carrier.  Counting arguments only
ever use this up to isomorphism of the source (Knight-VC's `PaperExactModelExpandsTo`:
"some model at `β` whose truncation is isomorphic to `M`"), and that is the notion fixed here:

* `Realization.ProlongsTo R hβ` — some stage-`β` realization (on some carrier) reduces, up to
  isomorphism, to `R`;
* `Realization.ProlongsToOn R hβ` — the literal Def. 5.1.1 shape: some stage-`β` realization on
  the *same carrier* reduces *exactly* to `R`.  The two are equivalent
  (`prolongsTo_iff_prolongsToOn`): a target on any carrier is pushed forward along the
  isomorphism onto the carrier of `R` (`Realization.map`, `IsIso.map_eq`);
* `Realization.NoProlongationTo R hβ` — the negation (Knight-VC's `NoExpansionTo`; its instance
  at `β = α + ω` is Knight-VC's `FailsAtAlphaOmega`);
* `Realization.ProlongsToIn C R hβ` — prolongation **within a target class** `C` (a predicate on
  realizations at every stage and carrier, e.g. "is a model", Def. 3.2.1): the target is
  required to satisfy `C`.  `ProlongsTo` is the case `C := ⊤` (`prolongsToIn_true_iff`), and
  Knight's Def. 5.1.1 is literally `ProlongsToOnIn IsModel`.

The generic predicates carry no model axioms (those are Knight-specific and enter through `C`);
the acceptance property of #29 is **isomorphism invariance** (`IsIso.prolongsTo_iff`,
`Iso.prolongsTo_iff`, and the lift to the isomorphism classes `ProlongsToClass`), together with
downward monotonicity in the target stage (`ProlongsTo.mono`) and reflexivity (`ProlongsTo.refl`).

**Two levels (deliberate).**
1. *Raw / structural prolongation* `ProlongsTo`: isomorphism-invariant and downward monotone in
   the target stage **structurally** (`ProlongsTo.mono`, by `reduct_reduct`) — no model axioms.
2. *Certified model prolongation* `ProlongsToIn C` with `C := IsModel`: the rank-relevant
   notion (histories, `stopRank`, #70/#30) must prolong through **actual models**.  Its downward
   monotonicity `ProlongsToIn.mono` is *not* inherited from level 1: it needs the target class
   to be closed under reduction (`hC`).  For Knight that closure is the strict model-reduction
   theorem `KnightRealization.IsModel.reduct` (#101, `Knight/ReductModel.lean`): full modelhood,
   including the `⊥`-pattern clause, is preserved by `reduct` for arbitrary models, so
   `ProlongsToIn IsModel` is downward closed as a theorem (Knight façade), not via a
   `ProlongationStep` receipt or a coherent history.  Had (a)(ii) been construction-specific,
   downward closure would have had to come from a receipt; that fallback is no longer needed.

**Universes.**  The target carrier is quantified over `Type w`, the universe of the source
carrier `M`, so `ProlongsTo` has no universe parameter beyond those of `R` and isomorphism
invariance needs no `ULift`.  Nothing is lost: a target on a carrier of any universe `w'` is
isomorphic (through its reduct) to `R`, hence is a push-forward of a realization on `M`, and
`ProlongsTo.of_reduct_iso` accepts such a target directly.  (The target-class variant
`ProlongsToIn C` takes `C` on carriers of universe `w` only, and its invariance is stated for
sources in that universe.)

**Non-goals.**  No uniqueness of prolongations (Knight's Lemma 5.5.2 is *avoided*, CONCORDANCE
§5); no construction of prolongations (the construction datum `ProlongationStep` is #51/#30);
no coherent histories (`∀ β, ProlongsTo` is *not* a history — TERMINOLOGY, banned
identification 4). -/

@[expose] public section

namespace VaughtConjecture

universe u v w w'

namespace TypeTower.Realization

variable {Λ : Type v} [Preorder Λ] {T : TypeTower.{u} Λ} {α β γ : Λ} {M : Type w}

/-! ### The predicates -/

/-- `R` **prolongs to stage `β`**: some stage-`β` realization (on some carrier in the universe of
`M`) reduces, up to isomorphism, to `R`.  The public, isomorphism-invariant form of Knight's
Def. 5.1.1 (Knight-VC `PaperExactModelExpandsTo`, without the model axioms, which enter through
`ProlongsToIn`). -/
def ProlongsTo (R : T.Realization α M) (hβ : α ≤ β) : Prop :=
  ∃ (N : Type w) (R' : T.Realization β N), Nonempty ((R'.reduct hβ).Iso R)

/-- `R` **prolongs to stage `β` on its own carrier**: some stage-`β` realization on `M` reduces
*exactly* to `R` — the literal shape of Knight's Def. 5.1.1 (`M = S ι_{α,β} ∘ N`). -/
def ProlongsToOn (R : T.Realization α M) (hβ : α ≤ β) : Prop :=
  ∃ R' : T.Realization β M, R'.reduct hβ = R

/-- `R` has **no prolongation** to stage `β` (Knight-VC `NoExpansionTo`; at `β = α + ω` this is
Knight-VC's `FailsAtAlphaOmega`, the paper's no-expansion failure of §5.5 / §11.1). -/
def NoProlongationTo (R : T.Realization α M) (hβ : α ≤ β) : Prop :=
  ¬ R.ProlongsTo hβ

/-! ### Entry points: any carrier, any universe -/

/-- A stage-`β` realization on a carrier `N` of *any* universe whose reduct is isomorphic to `R`
witnesses `ProlongsTo`: push it forward along the isomorphism onto `M`. -/
theorem ProlongsTo.of_reduct_iso {N : Type w'} (R : T.Realization α M) (hβ : α ≤ β)
    (R' : T.Realization β N) (i : (R'.reduct hβ).Iso R) : R.ProlongsTo hβ :=
  ⟨M, R'.map i.1, ⟨by rw [reduct_map, IsIso.map_eq i.2]; exact Iso.refl R⟩⟩

/-- Every realization at stage `β` prolongs its own reduct (the witness is the realization
itself). -/
theorem prolongsTo_reduct {N : Type w'} (hβ : α ≤ β) (R' : T.Realization β N) :
    (R'.reduct hβ).ProlongsTo hβ :=
  ProlongsTo.of_reduct_iso _ hβ R' (Iso.refl _)

theorem ProlongsToOn.prolongsTo {R : T.Realization α M} {hβ : α ≤ β} (h : R.ProlongsToOn hβ) :
    R.ProlongsTo hβ := by
  obtain ⟨R', rfl⟩ := h
  exact prolongsTo_reduct hβ R'

theorem ProlongsTo.prolongsToOn {R : T.Realization α M} {hβ : α ≤ β} (h : R.ProlongsTo hβ) :
    R.ProlongsToOn hβ := by
  obtain ⟨N, R', ⟨i⟩⟩ := h
  exact ⟨R'.map i.1, by rw [reduct_map, IsIso.map_eq i.2]⟩

/-- Prolongation up to isomorphism on any carrier is the same as literal prolongation on the
carrier of the source: the target is pushed forward along the isomorphism.  (So the universe
choice in `ProlongsTo` is immaterial, and Knight's literal Def. 5.1.1 shape is available
whenever the up-to-isomorphism one is.) -/
theorem prolongsTo_iff_prolongsToOn (R : T.Realization α M) (hβ : α ≤ β) :
    R.ProlongsTo hβ ↔ R.ProlongsToOn hβ :=
  ⟨ProlongsTo.prolongsToOn, ProlongsToOn.prolongsTo⟩

/-! ### Isomorphism invariance (the acceptance property of #29) -/

theorem ProlongsTo.of_isIso {N : Type w'} {R : T.Realization α M} {R₂ : T.Realization α N}
    {e : M ≃ N} (hi : R.IsIso R₂ e) {hβ : α ≤ β} (h : R.ProlongsTo hβ) : R₂.ProlongsTo hβ := by
  obtain ⟨K, R', ⟨i⟩⟩ := h
  exact ProlongsTo.of_reduct_iso R₂ hβ R' (i.trans ⟨e, hi⟩)

/-- **Isomorphism invariance** of prolongation (Knight-VC `paperExactModelExpandsTo_iff_of_iso`,
generalised to any tower, any carriers, any universes). -/
theorem IsIso.prolongsTo_iff {N : Type w'} {R : T.Realization α M} {R₂ : T.Realization α N}
    {e : M ≃ N} (hi : R.IsIso R₂ e) (hβ : α ≤ β) : R.ProlongsTo hβ ↔ R₂.ProlongsTo hβ :=
  ⟨ProlongsTo.of_isIso hi, ProlongsTo.of_isIso (IsIso.symm hi)⟩

theorem Iso.prolongsTo_iff {N : Type w'} {R : T.Realization α M} {R₂ : T.Realization α N}
    (i : R.Iso R₂) (hβ : α ≤ β) : R.ProlongsTo hβ ↔ R₂.ProlongsTo hβ :=
  IsIso.prolongsTo_iff i.2 hβ

theorem prolongsTo_iff_of_iso {N : Type w'} {R : T.Realization α M} {R₂ : T.Realization α N}
    (h : Nonempty (R.Iso R₂)) (hβ : α ≤ β) : R.ProlongsTo hβ ↔ R₂.ProlongsTo hβ :=
  h.elim fun i => i.prolongsTo_iff hβ

theorem IsIso.noProlongationTo_iff {N : Type w'} {R : T.Realization α M} {R₂ : T.Realization α N}
    {e : M ≃ N} (hi : R.IsIso R₂ e) (hβ : α ≤ β) :
    R.NoProlongationTo hβ ↔ R₂.NoProlongationTo hβ :=
  not_congr (IsIso.prolongsTo_iff hi hβ)

theorem Iso.noProlongationTo_iff {N : Type w'} {R : T.Realization α M} {R₂ : T.Realization α N}
    (i : R.Iso R₂) (hβ : α ≤ β) : R.NoProlongationTo hβ ↔ R₂.NoProlongationTo hβ :=
  not_congr (i.prolongsTo_iff hβ)

theorem noProlongationTo_iff_of_iso {N : Type w'} {R : T.Realization α M}
    {R₂ : T.Realization α N} (h : Nonempty (R.Iso R₂)) (hβ : α ≤ β) :
    R.NoProlongationTo hβ ↔ R₂.NoProlongationTo hβ :=
  not_congr (prolongsTo_iff_of_iso h hβ)

/-! ### Reflexivity and downward monotonicity in the target stage -/

/-- Every realization prolongs to its own stage (`reduct_refl`). -/
theorem ProlongsTo.refl (R : T.Realization α M) : R.ProlongsTo le_rfl :=
  ProlongsToOn.prolongsTo ⟨R, reduct_refl R⟩

/-- Prolongability is **downward closed** in the target stage: a prolongation to `γ` reduces to
a prolongation to every `β` with `α ≤ β ≤ γ` (`reduct_reduct`).  This is what makes a first
failed stage meaningful (Knight-VC `noExpansionTo_of_isPaperExactExpansion`). -/
theorem ProlongsTo.mono {R : T.Realization α M} {hβ : α ≤ β} (hβγ : β ≤ γ)
    (h : R.ProlongsTo (hβ.trans hβγ)) : R.ProlongsTo hβ := by
  obtain ⟨N, R', ⟨i⟩⟩ := h
  exact ProlongsTo.of_reduct_iso R hβ (R'.reduct hβγ) (by rw [reduct_reduct]; exact i)

/-- `ProlongsTo.mono` for arbitrary proofs of the two inequalities (proof irrelevance identifies
`hγ` with `hβ.trans hβγ`). -/
theorem ProlongsTo.mono' {R : T.Realization α M} {hβ : α ≤ β} {hγ : α ≤ γ} (hβγ : β ≤ γ)
    (h : R.ProlongsTo hγ) : R.ProlongsTo hβ :=
  ProlongsTo.mono hβγ h

/-- Failure of prolongation is **upward closed** in the target stage. -/
theorem NoProlongationTo.mono {R : T.Realization α M} {hβ : α ≤ β} (hβγ : β ≤ γ)
    (h : R.NoProlongationTo hβ) : R.NoProlongationTo (hβ.trans hβγ) :=
  fun h' => h (h'.mono hβγ)

/-- A prolongation target prolongs to every intermediate stage: if `R'` at stage `γ` witnesses a
prolongation of `R`, then `R'.reduct hβγ` at stage `β` does too. -/
theorem ProlongsTo.of_reduct_iso_reduct {N : Type w'} (R : T.Realization α M) {hβ : α ≤ β}
    (hβγ : β ≤ γ) (R' : T.Realization γ N) (i : (R'.reduct (hβ.trans hβγ)).Iso R) :
    R.ProlongsTo hβ :=
  ProlongsTo.mono hβγ (ProlongsTo.of_reduct_iso R _ R' i)

/-! ### The isomorphism-class lift

`ProlongsTo` descends to the isomorphism classes of stage-`α` realizations on `M`
(`Realization.isoSetoid`), so that a stopping rank (#70) can be defined on classes. -/

/-- Prolongability of an **isomorphism class** of realizations (well defined by
`Iso.prolongsTo_iff`). -/
def ProlongsToClass (hβ : α ≤ β) (q : Quotient (isoSetoid T α M)) : Prop :=
  Quotient.lift (fun R : T.Realization α M => R.ProlongsTo hβ)
    (fun _ _ h => propext (prolongsTo_iff_of_iso h hβ)) q

@[simp]
theorem prolongsToClass_mk (hβ : α ≤ β) (R : T.Realization α M) :
    ProlongsToClass hβ (Quotient.mk (isoSetoid T α M) R) ↔ R.ProlongsTo hβ := Iff.rfl

theorem ProlongsToClass.mono {hβ : α ≤ β} (hβγ : β ≤ γ) {q : Quotient (isoSetoid T α M)}
    (h : ProlongsToClass (hβ.trans hβγ) q) : ProlongsToClass hβ q := by
  induction q using Quotient.inductionOn with
  | h R => exact ProlongsTo.mono hβγ h

theorem ProlongsToClass.refl (q : Quotient (isoSetoid T α M)) : ProlongsToClass le_rfl q := by
  induction q using Quotient.inductionOn with
  | h R => exact ProlongsTo.refl R

/-! ### Prolongation within a target class

A *target class* is a predicate on realizations at every stage and on every carrier of the
universe of `M` (for Knight: "is a model of `S^β`", Def. 3.2.1).  `ProlongsToIn C` requires
the prolongation target to lie in `C`; it is invariant under isomorphism of the source without
any hypothesis on `C`, is downward monotone when `C` is closed under reduction, and coincides
with the carrier-fixed literal form when `C` is closed under push-forward along bijections. -/

section TargetClass

variable (C : ∀ {δ : Λ} {N : Type w}, T.Realization δ N → Prop)

/-- `R` prolongs to stage `β` **within the target class `C`**: some stage-`β` realization in `C`
reduces, up to isomorphism, to `R`.  With `C := IsModel` this is Knight-VC's
`PaperExactModelExpandsTo` (Knight's Def. 5.1.1 up to isomorphism of the source). -/
def ProlongsToIn (R : T.Realization α M) (hβ : α ≤ β) : Prop :=
  ∃ (N : Type w) (R' : T.Realization β N), C R' ∧ Nonempty ((R'.reduct hβ).Iso R)

/-- `R` prolongs to stage `β` within `C` **on its own carrier**: Knight's Def. 5.1.1 verbatim
when `C := IsModel`. -/
def ProlongsToOnIn (R : T.Realization α M) (hβ : α ≤ β) : Prop :=
  ∃ R' : T.Realization β M, C R' ∧ R'.reduct hβ = R

/-- No prolongation within `C` (Knight-VC `NoExpansionTo` / `FailsAtAlphaOmega` with the model
axioms, for `C := IsModel`). -/
def NoProlongationToIn (R : T.Realization α M) (hβ : α ≤ β) : Prop :=
  ¬ R.ProlongsToIn C hβ

variable {C}

theorem ProlongsToIn.prolongsTo {R : T.Realization α M} {hβ : α ≤ β} (h : R.ProlongsToIn C hβ) :
    R.ProlongsTo hβ := by
  obtain ⟨N, R', -, hi⟩ := h
  exact ⟨N, R', hi⟩

theorem NoProlongationTo.noProlongationToIn {R : T.Realization α M} {hβ : α ≤ β}
    (h : R.NoProlongationTo hβ) : R.NoProlongationToIn C hβ :=
  fun h' => h h'.prolongsTo

theorem ProlongsToOnIn.prolongsToIn {R : T.Realization α M} {hβ : α ≤ β}
    (h : R.ProlongsToOnIn C hβ) : R.ProlongsToIn C hβ := by
  obtain ⟨R', hC, rfl⟩ := h
  exact ⟨M, R', hC, ⟨Iso.refl _⟩⟩

/-- Within the trivial target class, prolongation is plain prolongation. -/
theorem prolongsToIn_true_iff (R : T.Realization α M) (hβ : α ≤ β) :
    R.ProlongsToIn (fun _ => True) hβ ↔ R.ProlongsTo hβ :=
  ⟨ProlongsToIn.prolongsTo, fun ⟨N, R', hi⟩ => ⟨N, R', trivial, hi⟩⟩

/-- A target in `C` (on any carrier of universe `w`) whose reduct is isomorphic to `R`. -/
theorem ProlongsToIn.of_reduct_iso {N : Type w} (R : T.Realization α M) (hβ : α ≤ β)
    (R' : T.Realization β N) (hC : C R') (i : (R'.reduct hβ).Iso R) : R.ProlongsToIn C hβ :=
  ⟨N, R', hC, ⟨i⟩⟩

theorem ProlongsToIn.of_isIso {N : Type w} {R : T.Realization α M} {R₂ : T.Realization α N}
    {e : M ≃ N} (hi : R.IsIso R₂ e) {hβ : α ≤ β} (h : R.ProlongsToIn C hβ) :
    R₂.ProlongsToIn C hβ := by
  obtain ⟨K, R', hC, ⟨i⟩⟩ := h
  exact ⟨K, R', hC, ⟨i.trans ⟨e, hi⟩⟩⟩

/-- **Isomorphism invariance** of prolongation within a target class — no hypothesis on `C`. -/
theorem IsIso.prolongsToIn_iff {N : Type w} {R : T.Realization α M} {R₂ : T.Realization α N}
    {e : M ≃ N} (hi : R.IsIso R₂ e) (hβ : α ≤ β) :
    R.ProlongsToIn C hβ ↔ R₂.ProlongsToIn C hβ :=
  ⟨ProlongsToIn.of_isIso hi, ProlongsToIn.of_isIso (IsIso.symm hi)⟩

theorem Iso.prolongsToIn_iff {N : Type w} {R : T.Realization α M} {R₂ : T.Realization α N}
    (i : R.Iso R₂) (hβ : α ≤ β) : R.ProlongsToIn C hβ ↔ R₂.ProlongsToIn C hβ :=
  IsIso.prolongsToIn_iff i.2 hβ

theorem prolongsToIn_iff_of_iso {N : Type w} {R : T.Realization α M} {R₂ : T.Realization α N}
    (h : Nonempty (R.Iso R₂)) (hβ : α ≤ β) : R.ProlongsToIn C hβ ↔ R₂.ProlongsToIn C hβ :=
  h.elim fun i => i.prolongsToIn_iff hβ

theorem Iso.noProlongationToIn_iff {N : Type w} {R : T.Realization α M}
    {R₂ : T.Realization α N} (i : R.Iso R₂) (hβ : α ≤ β) :
    R.NoProlongationToIn C hβ ↔ R₂.NoProlongationToIn C hβ :=
  not_congr (i.prolongsToIn_iff hβ)

/-- If `C` is closed under push-forward along bijections of carriers, prolongation within `C` up
to isomorphism is literal prolongation within `C` on the carrier of the source. -/
theorem ProlongsToIn.prolongsToOnIn
    (hC : ∀ {δ : Λ} {N N' : Type w} (e : N ≃ N') (R' : T.Realization δ N), C R' → C (R'.map e))
    {R : T.Realization α M} {hβ : α ≤ β} (h : R.ProlongsToIn C hβ) : R.ProlongsToOnIn C hβ := by
  obtain ⟨N, R', hR', ⟨i⟩⟩ := h
  exact ⟨R'.map i.1, hC i.1 R' hR', by rw [reduct_map, IsIso.map_eq i.2]⟩

theorem prolongsToIn_iff_prolongsToOnIn
    (hC : ∀ {δ : Λ} {N N' : Type w} (e : N ≃ N') (R' : T.Realization δ N), C R' → C (R'.map e))
    (R : T.Realization α M) (hβ : α ≤ β) : R.ProlongsToIn C hβ ↔ R.ProlongsToOnIn C hβ :=
  ⟨ProlongsToIn.prolongsToOnIn hC, ProlongsToOnIn.prolongsToIn⟩

/-- A realization in `C` prolongs to its own stage within `C`. -/
theorem ProlongsToIn.refl {R : T.Realization α M} (hR : C R) : R.ProlongsToIn C le_rfl :=
  ProlongsToOnIn.prolongsToIn ⟨R, hR, reduct_refl R⟩

/-- If `C` is closed under reduction, prolongation within `C` is **downward closed** in the target
stage. -/
theorem ProlongsToIn.mono
    (hC : ∀ {δ δ' : Λ} (h : δ ≤ δ') {N : Type w} (R' : T.Realization δ' N),
      C R' → C (R'.reduct h))
    {R : T.Realization α M} {hβ : α ≤ β} (hβγ : β ≤ γ) (h : R.ProlongsToIn C (hβ.trans hβγ)) :
    R.ProlongsToIn C hβ := by
  obtain ⟨N, R', hR', ⟨i⟩⟩ := h
  exact ⟨N, R'.reduct hβγ, hC hβγ R' hR', ⟨by rw [reduct_reduct]; exact i⟩⟩

theorem NoProlongationToIn.mono
    (hC : ∀ {δ δ' : Λ} (h : δ ≤ δ') {N : Type w} (R' : T.Realization δ' N),
      C R' → C (R'.reduct h))
    {R : T.Realization α M} {hβ : α ≤ β} (hβγ : β ≤ γ) (h : R.NoProlongationToIn C hβ) :
    R.NoProlongationToIn C (hβ.trans hβγ) :=
  fun h' => h (ProlongsToIn.mono hC hβγ h')

variable (C) in
/-- Prolongability within `C` of an isomorphism class of realizations. -/
def ProlongsToClassIn (hβ : α ≤ β) (q : Quotient (isoSetoid T α M)) : Prop :=
  Quotient.lift (fun R : T.Realization α M => R.ProlongsToIn C hβ)
    (fun _ _ h => propext (prolongsToIn_iff_of_iso h hβ)) q

@[simp]
theorem prolongsToClassIn_mk (hβ : α ≤ β) (R : T.Realization α M) :
    ProlongsToClassIn C hβ (Quotient.mk (isoSetoid T α M) R) ↔ R.ProlongsToIn C hβ := Iff.rfl

end TargetClass

end TypeTower.Realization

end VaughtConjecture
