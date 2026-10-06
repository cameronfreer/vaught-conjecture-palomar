/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ObstructionInstance

/-! # A family of refined rows with independent fresh sources

The reviewer's task (2026-09-16): freeze the obstruction instance as a regression test; on the
same old domain attempt a jointly consistent family of refined rows with independent fresh
sources, preserving every old row literally; construct sections for both the intended request
and the newly refuted prescription; test positive-cap lifting against arbitrary lawful
ambients; track reference readback separately, so that recovering section supply does not
silently discard the forcing needed for certificates.

**The spliced witness** (`spliceAt`, `witness_spliceAt`).  A witness below a block floor and a
self-visible constant from the floor on is again a witness: replacement never crosses a block
floor in either direction (`extVisibilityReplace_lt_floor`, `floor_le_extVisibilityReplace`),
and a self-visible constant is fixed by every replacement at a threshold at most its own.

**The refined row** (`topSource`).  The donor's row on its old lower domain — literally — and
at the fresh cell a block floor above every old source (`exists_block_above`: the sources are
finitely many codes).  The fresh source is independent of the representative.  Its faithful
capped targets read the fresh cell at least the donor (`topSource_fresh_ge`), and it serves
**every** fresh label at least its cap: for any lawful old face, any self-visible cap at most
the face's donor value, and any fresh label at least the cap (`topSource_transformsTo`; the
witness is the exact capped witness of the face spliced with the cap).

**The family** (`FamilySection`): two controllers at the mixed index over the same old lower
domain — the donor row with the representative-forced fresh source and the refined row with the
independent one — each transforming to the joint labelling capped at its own self-visible
label, with the old controller dominated at the index.  Both prescriptions have sections on the
same old domain, old rows literal: the intended request through the donor controller with the
refined controller mute (`family_intended`), and every fresh label at least the face's donor
value — the refuted prescriptions included — through the refined controller with the donor
controller mute (`family_top`).

**Positive caps** (`topSource_positiveCap`).  Against an arbitrary lawful ambient served by the
refined row, with a cap self-visible at the donor's grade and prescribed data agreeing with the
ambient under it, the old face completes by the receiver's own bountifulness and the refined
controller, labelled the smaller of the prescribed fresh label and the completed donor value,
agrees with the ambient under the cap and serves the literal fresh label.  No low/high split
is needed: the refined row imposes no equation.

**Readback, tracked separately.**  The refined row forces nothing: every fresh label at least
the cap is admitted (`topSource_transformsTo` itself).  The donor row forces the readback
equation at every self-visible cap at most the donor value (`donorSource_capped_at`): the fresh
label capped at the controller is the replacement of the capped representative value — the
forcing certificates need.  So the family recovers section supply exactly by letting sections
activate the refined controller, and forcing survives only in sections whose active controller
is the donor one.  The family itself does not select the controller; whether the intended
receiver's availability and bottom pattern can force that selection is the open question, not
answered here.

**Regression** (`ObstructionInstance.regression_family_intended`, `regression_family_top`).  On
the repaired coupled domain with the mixed display: the intended request `ω + off` is served
by the donor controller, and every fresh label at least the display's donor value `κ'` by the
refined controller.  The refuted prescriptions strictly between `κ` and `κ'` are not served by
either controller labelled at least `κ'` (the donor row by `concrete_obstruction`, the refined
row because the fresh source lies above sources read `κ'`); serving them needs a completion
whose donor value is at most the fresh label, which is again a constrained completion.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

/-! ## Block floors and replacement -/

/-- Replacement never crosses a block floor downward. -/
theorem extVisibilityReplace_lt_floor {μ : Ordinal.{0}} (hμ : limitPart μ = μ) {x : ExtOrd}
    (hx : x < ofOrd μ) (k i : ℕ) : extVisibilityReplace x k i < ofOrd μ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · rw [extVisibilityReplace_bot]; exact bot_lt_ofOrd _
  · exact absurd hx (not_lt.mpr le_top)
  · rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
    have hβ : β < μ := ofOrd_lt_ofOrd.mp hx
    unfold visibilityReplace
    split_ifs
    · unfold ordinalReplace
      have h1 : limitPart β < limitPart μ := by
        rw [hμ]; exact (limitPart_le β).trans_lt hβ
      have h2 := limitPart_add_omega0_le h1
      rw [hμ] at h2
      exact (add_lt_add_right (Ordinal.natCast_lt_omega0 i) _).trans_le h2
    · exact hβ

/-- Replacement never crosses a block floor upward. -/
theorem floor_le_extVisibilityReplace {μ : Ordinal.{0}} (hμ : limitPart μ = μ) {x : ExtOrd}
    (hx : ofOrd μ ≤ x) (k i : ℕ) : ofOrd μ ≤ extVisibilityReplace x k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact absurd hx (not_ofOrd_le_bot _)
  · rw [extVisibilityReplace_top]; exact le_top
  · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
    have hβ : μ ≤ β := ofOrd_le_ofOrd.mp hx
    unfold visibilityReplace
    split_ifs
    · unfold ordinalReplace
      calc μ = limitPart μ := hμ.symm
        _ ≤ limitPart β := limitPart_mono hβ
        _ ≤ limitPart β + (i : Ordinal) := le_self_add
    · exact hβ

/-- A self-visible value is fixed by every replacement at a threshold at most its own. -/
theorem extVisibilityReplace_eq_of_selfVis {K k i : ℕ} {w : ExtOrd} (hw : SelfVis K w)
    (hk : k ≤ K) : extVisibilityReplace w k i = w := by
  rcases ExtOrd.cases w with rfl | rfl | ⟨c, rfl⟩
  · exact extVisibilityReplace_bot _ _
  · exact extVisibilityReplace_top _ _
  · exact extVisibilityReplace_of_le_finitePart (hk.trans (selfVis_ofOrd_iff.mp hw)) i

/-! ## The spliced witness -/

/-- A witness below a block floor, a constant from the floor on. -/
noncomputable def spliceAt (μ : Ordinal.{0}) (τ : ExtOrd → ExtOrd) (w x : ExtOrd) : ExtOrd :=
  if x < ofOrd μ then τ x else w

theorem spliceAt_of_lt {μ : Ordinal.{0}} {τ : ExtOrd → ExtOrd} {w x : ExtOrd}
    (hx : x < ofOrd μ) : spliceAt μ τ w x = τ x := by
  unfold spliceAt; exact ite_eq_left hx

theorem spliceAt_of_le {μ : Ordinal.{0}} {τ : ExtOrd → ExtOrd} {w x : ExtOrd}
    (hx : ofOrd μ ≤ x) : spliceAt μ τ w x = w := by
  unfold spliceAt; exact ite_eq_right (not_lt.mpr hx)

/-- **Splicing preserves witnesses**: a witness below a block floor and a self-visible constant
dominating it from the floor on is a witness, clause 5 included. -/
theorem witness_spliceAt {K : ℕ} {μ : Ordinal.{0}} (hμ : limitPart μ = μ)
    {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop K) τ) {w : ExtOrd} (hw : SelfVis K w)
    (hle : ∀ x, x < ofOrd μ → τ x ≤ w) : Witness (gTop K) (spliceAt μ τ w) where
  anti := hτ.anti
  vis := hτ.vis
  bot := by rw [spliceAt_of_lt (bot_lt_ofOrd μ)]; exact hτ.bot
  mono := by
    intro x y hxy
    by_cases hx : x < ofOrd μ
    · rw [spliceAt_of_lt hx]
      by_cases hy : y < ofOrd μ
      · rw [spliceAt_of_lt hy]; exact hτ.mono hxy
      · rw [spliceAt_of_le (not_lt.mp hy)]; exact hle x hx
    · have hx' := not_lt.mp hx
      rw [spliceAt_of_le hx', spliceAt_of_le (hx'.trans hxy)]
  clause5 := by
    intro α k hα i hi
    by_cases hx : α < ofOrd μ
    · rw [spliceAt_of_lt hx] at hα
      rw [spliceAt_of_lt hx, spliceAt_of_lt (extVisibilityReplace_lt_floor hμ hx k i)]
      exact hτ.clause5 α k hα i hi
    · have hx' := not_lt.mp hx
      rw [spliceAt_of_le hx'] at hα
      rw [spliceAt_of_le hx', spliceAt_of_le (floor_le_extVisibilityReplace hμ hx' k i)]
      by_cases hk : k ≤ K
      · exact (extVisibilityReplace_eq_of_selfVis hw hk).symm
      · rw [gTop_of_gt (not_le.mp hk)] at hα
        rw [le_bot_iff.mp hα, extVisibilityReplace_bot]

private theorem min_min_right_distrib'' (a b γ : ExtOrd) :
    min (min a b) γ = min (min a γ) (min b γ) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (min_le_min_right γ h)]
  · rw [min_eq_right h, min_eq_right (min_le_min_right γ h)]

/-! ## The refined row -/

section Generic

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} (sem : Semantics D)

/-- **The refined row**: the donor's row on its old lower domain, literally, and at the fresh
cell of grade `g₀` the code `ω·b + g₀` in block `b`, independent of the representative.  (The
offset `g₀` is the source-legality repair: a block floor has finite part zero and is not orderly
at a positive fresh grade.) -/
noncomputable def topSource (o : Cell D) (b g₀ : ℕ) : D.below (D.cell o) ⊕ Unit → ExtOrd :=
  Sum.elim (sem.E o) (fun _ => ofOrd (Ordinal.omega0 * b + g₀))

/-- The refined row's fresh source is orderly at the fresh grade. -/
theorem topSource_fresh_selfVis (o : Cell D) (b g₀ : ℕ) :
    SelfVis g₀ (topSource sem o b g₀ (Sum.inr ())) := by
  change SelfVis g₀ (ofOrd (Ordinal.omega0 * b + g₀))
  rw [selfVis_ofOrd_iff, finitePart_mul_add]

/-- The refined row is coded at the donor's grade when its old part is and the fresh grade is at
most the donor's. -/
theorem topSource_coded (o : Cell D) (b : ℕ) {g₀ : ℕ} (hg₀ : g₀ ≤ D.grade o)
    (hc : ∀ d : D.below (D.cell o), IsCodedLabel (D.grade o) (sem.E o d)) :
    ∀ x, IsCodedLabel (D.grade o) (topSource sem o b g₀ x) := by
  intro x
  rcases x with d | u
  · exact hc d
  · exact Or.inr ⟨b, g₀, by omega, rfl⟩

/-- The fresh source lies above every old source once the block does. -/
theorem old_lt_topSource {o : Cell D} {b : ℕ}
    (hb : ∀ d : D.below (D.cell o), sem.E o d < ofOrd (Ordinal.omega0 * b)) (g₀ : ℕ)
    (d : D.below (D.cell o)) : sem.E o d < ofOrd (Ordinal.omega0 * b + g₀) :=
  (hb d).trans_le (ofOrd_le_ofOrd.mpr le_self_add)

/-- A block above every old source exists: the sources are finitely many codes. -/
theorem exists_block_above (o : Cell D)
    (hc : ∀ d : D.below (D.cell o), IsCodedLabel (D.grade o) (sem.E o d)) :
    ∃ b : ℕ, ∀ d : D.below (D.cell o), sem.E o d < ofOrd (Ordinal.omega0 * b) := by
  classical
  let _ := Fintype.ofFinite (D.below (D.cell o))
  have hblk : ∀ d : D.below (D.cell o), ∃ b : ℕ, sem.E o d < ofOrd (Ordinal.omega0 * b) := by
    intro d
    rcases hc d with h | ⟨i, j, -, h⟩
    · exact ⟨1, by rw [h]; exact bot_lt_ofOrd _⟩
    · refine ⟨i + 1, ?_⟩
      rw [h, ofOrd_lt_ofOrd, Nat.cast_succ, mul_add, mul_one]
      exact add_lt_add_right (Ordinal.natCast_lt_omega0 j) _
  choose f hf using hblk
  refine ⟨Finset.univ.sup f, fun d => (hf d).trans_le ?_⟩
  rw [ofOrd_le_ofOrd]
  exact (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.monotone
    (Nat.cast_le.mpr (Finset.le_sup (f := f) (Finset.mem_univ d)))

variable {sem}

/-- Any faithful capped target of the refined row reads the fresh cell at least the donor,
capped. -/
theorem topSource_fresh_ge {o : Cell D} {b : ℕ}
    (hb : ∀ d : D.below (D.cell o), sem.E o d < ofOrd (Ordinal.omega0 * b))
    {g₀ : ℕ} (hg₀ : g₀ ≤ D.grade o) {Q : D.below (D.cell o) ⊕ Unit → ExtOrd} {w : ExtOrd}
    (h : TransformsTo (Sum.elim (fun d : D.below (D.cell o) => D.grade d.1) (fun _ => g₀))
      (topSource sem o b g₀) (fun x => min (Q x) w)) :
    min (Q (Sum.inl ⟨o, GradedLe.refl _⟩)) w ≤ min (Q (Sum.inr ())) w := by
  obtain ⟨g, σ, hanti, -, -, hmono, -, heq⟩ := h
  have h1 := heq (Sum.inl ⟨o, GradedLe.refl _⟩)
  have h2 := heq (Sum.inr ())
  change min (Q _) w = min (σ (sem.E o ⟨o, GradedLe.refl _⟩)) (g (D.grade o)) at h1
  change min (Q _) w = min (σ (ofOrd (Ordinal.omega0 * b + g₀))) (g g₀) at h2
  rw [h1, h2]
  have hg : g (D.grade o) ≤ g g₀ := by
    rcases eq_or_lt_of_le hg₀ with h | h
    · rw [h]
    · exact hanti _ _ h
  exact min_le_min (hmono (old_lt_topSource sem hb g₀ _).le) hg

/-- **The refined row serves every fresh label at least its cap**: for a lawful old face `p`, a
self-visible cap `w` at most `p`'s donor value, and a fresh label at least `w`, the refined row
transforms to `(p, φ)` capped at `w`.  Witness: the exact capped witness of `p` spliced with
`w` above the old sources. -/
theorem topSource_transformsTo {o : Cell D} {b : ℕ}
    (hb : ∀ d : D.below (D.cell o), sem.E o d < ofOrd (Ordinal.omega0 * b))
    (p : D.below (D.cell o) → ExtOrd) (hp : RespectsSemanticsBelow sem (D.cell o) p)
    {w : ExtOrd} (hw : SelfVis (D.grade o) w) (hwo : w ≤ p ⟨o, GradedLe.refl _⟩)
    {φ : ExtOrd} (hφ : w ≤ φ) (g₀ : ℕ) (hg₀ : g₀ ≤ D.grade o) :
    TransformsTo (Sum.elim (fun d : D.below (D.cell o) => D.grade d.1) (fun _ => g₀))
      (topSource sem o b g₀) (fun x => min (Sum.elim p (fun _ => φ) x) w) := by
  have hKvis : SelfVis (D.grade o) (p ⟨o, GradedLe.refl _⟩) :=
    (hp.orderly ⟨o, GradedLe.refl _⟩).symm
  have hPo : min (p ⟨o, GradedLe.refl _⟩) w = w := min_eq_right hwo
  have hkey : ∀ y : ExtOrd, min (min y w) (min (p ⟨o, GradedLe.refl _⟩) w) = min y w := by
    intro y; rw [hPo, min_assoc, min_self]
  have hloc : TransformsTo (fun d : D.below (D.cell o) => D.grade d.1) (sem.E o)
      (fun d => min (min (p d) w) (min (p ⟨o, GradedLe.refl _⟩) w)) := by
    have h := (hp.locality ⟨o, GradedLe.refl _⟩).cap (K := D.grade o) (γ := w)
      (fun d => d.2.2) hw
    convert h using 1
    funext d
    rw [show CellScheme.below.incl (⟨o, GradedLe.refl _⟩ : D.below (D.cell o)) d = d from
      Subtype.ext rfl, hkey, min_assoc, hPo]
  obtain ⟨τ, hτ, hbound, hread⟩ : ∃ τ : ExtOrd → ExtOrd, Witness (gTop (D.grade o)) τ ∧
      (∀ x, τ x ≤ min (p ⟨o, GradedLe.refl _⟩) w) ∧
      ∀ d, τ (sem.E o d) = min (min (p d) w) (min (p ⟨o, GradedLe.refl _⟩) w) :=
    exists_bounded_exact_capped_witness (p := fun d => min (p d) w) (c := ⟨o, GradedLe.refl _⟩)
      (fun d => d.2.2) (selfVis_min hKvis hw) hloc
  have hμ : limitPart (Ordinal.omega0 * b) = Ordinal.omega0 * b := limitPart_omega0_mul _
  have hle : ∀ x, x < ofOrd (Ordinal.omega0 * b) → τ x ≤ w :=
    fun x _ => (hbound x).trans (min_le_right _ _)
  apply (witness_spliceAt hμ hτ hw hle).transformsTo
  intro x
  rcases x with d | u
  · change min (p d) w = min (spliceAt _ τ w (sem.E o d)) (gTop (D.grade o) (D.grade d.1))
    rw [gTop_of_le (show D.grade d.1 ≤ D.grade o from d.2.2), min_top_right,
      spliceAt_of_lt (hb d), hread d, hkey]
  · change min φ w = min (spliceAt _ τ w (ofOrd (Ordinal.omega0 * b + g₀))) (gTop (D.grade o) g₀)
    rw [gTop_of_le hg₀, min_top_right, spliceAt_of_le (ofOrd_le_ofOrd.mpr le_self_add),
      min_eq_right hφ]

/-! ## The forced readback of the donor row at a general cap -/

/-- **The donor row forces the readback equation at every self-visible cap at most the donor
value**: the fresh label capped at the controller is the replacement of the capped
representative value. -/
theorem donorSource_capped_at {o : Cell D} {r : D.below (D.cell o)} {off g₀ : ℕ}
    (hoff : off ≤ D.grade o) (hg₀ : g₀ ≤ D.grade o) (p : D.below (D.cell o) → ExtOrd)
    (hp : RespectsSemanticsBelow sem (D.cell o) p) {w : ExtOrd} (hw : SelfVis (D.grade o) w)
    (hwo : w ≤ p ⟨o, GradedLe.refl _⟩) {φ : ExtOrd}
    (h : TransformsTo (Sum.elim (fun d : D.below (D.cell o) => D.grade d.1) (fun _ => g₀))
      (donorSource sem o r off) (fun x => min (Sum.elim p (fun _ => φ) x) w)) :
    min φ w = extVisibilityReplace (min (p r) w) (D.grade o) off := by
  have hKvis : SelfVis (D.grade o) (p ⟨o, GradedLe.refl _⟩) :=
    (hp.orderly ⟨o, GradedLe.refl _⟩).symm
  have hmax : ∀ x : D.below (D.cell o) ⊕ Unit,
      Sum.elim (fun d : D.below (D.cell o) => D.grade d.1) (fun _ : Unit => g₀) x ≤
        D.grade o := by
    intro x
    rcases x with d | u
    · exact d.2.2
    · exact hg₀
  have hPo : min (p ⟨o, GradedLe.refl _⟩) w = w := min_eq_right hwo
  have hkey : ∀ y : ExtOrd, min (min y w) (min (p ⟨o, GradedLe.refl _⟩) w) = min y w := by
    intro y; rw [hPo, min_assoc, min_self]
  obtain ⟨τ, hτ, -, hread⟩ : ∃ τ : ExtOrd → ExtOrd, Witness (gTop (D.grade o)) τ ∧
      (∀ x, τ x ≤ min (p ⟨o, GradedLe.refl _⟩) w) ∧
      ∀ d, τ (donorSource sem o r off d) =
        min (min (Sum.elim p (fun _ => φ) d) w) (min (p ⟨o, GradedLe.refl _⟩) w) :=
    exists_bounded_exact_capped_witness
      (p := fun x => min (Sum.elim p (fun _ => φ) x) w) (c := Sum.inl ⟨o, GradedLe.refl _⟩)
      hmax (selfVis_min hKvis hw) (by
        convert h using 1
        funext x
        change min (min (Sum.elim p (fun _ => φ) x) w) (min (p ⟨o, GradedLe.refl _⟩) w) =
          min (Sum.elim p (fun _ => φ) x) w
        exact hkey _)
  have hnew := hread (Sum.inr ())
  have href := hread (Sum.inl r)
  change τ (extVisibilityReplace (sem.E o r) (D.grade o) off) =
    min (min φ w) (min (p ⟨o, GradedLe.refl _⟩) w) at hnew
  change τ (sem.E o r) = min (min (p r) w) (min (p ⟨o, GradedLe.refl _⟩) w) at href
  rw [hkey] at hnew href
  rw [hτ.clause5 _ (D.grade o) (by rw [gTop_of_le le_rfl]; exact le_top) _ hoff, href] at hnew
  exact hnew.symm

/-- The donor row with the forced fresh label is a faithful capped target (the sufficiency
half of the readback equation, at the donor value). -/
theorem donorSource_forced {o : Cell D} {r : D.below (D.cell o)} {off g₀ : ℕ}
    (hoff : off ≤ D.grade o) (hg₀ : g₀ ≤ D.grade o) (p : D.below (D.cell o) → ExtOrd)
    (hp : RespectsSemanticsBelow sem (D.cell o) p) :
    TransformsTo (Sum.elim (fun d : D.below (D.cell o) => D.grade d.1) (fun _ => g₀))
      (donorSource sem o r off)
      (fun x => min (Sum.elim p (fun _ => extVisibilityReplace
        (min (p r) (p ⟨o, GradedLe.refl _⟩)) (D.grade o) off) x) (p ⟨o, GradedLe.refl _⟩)) := by
  have hKvis : SelfVis (D.grade o) (p ⟨o, GradedLe.refl _⟩) :=
    (hp.orderly ⟨o, GradedLe.refl _⟩).symm
  have hloc : TransformsTo (fun d : D.below (D.cell o) => D.grade d.1) (sem.E o)
      (fun d => min (p d) (p ⟨o, GradedLe.refl _⟩)) := hp.locality ⟨o, GradedLe.refl _⟩
  obtain ⟨τ, hτ, -, hread⟩ : ∃ τ : ExtOrd → ExtOrd, Witness (gTop (D.grade o)) τ ∧
      (∀ x, τ x ≤ p ⟨o, GradedLe.refl _⟩) ∧
      ∀ d, τ (sem.E o d) = min (p d) (p ⟨o, GradedLe.refl _⟩) :=
    exists_bounded_exact_capped_witness (c := ⟨o, GradedLe.refl _⟩) (p := p)
      (fun d => d.2.2) hKvis hloc
  apply hτ.transformsTo
  intro x
  rcases x with d | u
  · change min (p d) (p ⟨o, GradedLe.refl _⟩) =
      min (τ (sem.E o d)) (gTop (D.grade o) (D.grade d.1))
    rw [gTop_of_le (show D.grade d.1 ≤ D.grade o from d.2.2), min_top_right, hread]
  · change min (extVisibilityReplace (min (p r) (p ⟨o, GradedLe.refl _⟩)) (D.grade o) off)
      (p ⟨o, GradedLe.refl _⟩) =
      min (τ (extVisibilityReplace (sem.E o r) (D.grade o) off)) (gTop (D.grade o) g₀)
    rw [gTop_of_le hg₀, min_top_right, hτ.clause5 _ _
      (by rw [gTop_of_le le_rfl]; exact le_top) _ hoff, hread]
    exact min_eq_left (extVisibilityReplace_le_of_le_selfVis hoff hKvis (min_le_right _ _))

/-! ## The family -/

variable (sem) in
/-- **A family section**: two controllers at the mixed index over the same old lower domain —
the donor row (representative-forced fresh source) labelled `wd` and the refined row
(independent fresh source in block `b`) labelled `wt` — each a faithful capped target of the
joint labelling `(p, φ)` at its own self-visible label, with the old controller dominated at
the index. -/
structure FamilySection (o : Cell D) (r : D.below (D.cell o)) (off b g₀ : ℕ)
    (p : D.below (D.cell o) → ExtOrd) (φ wd wt : ExtOrd) : Prop where
  /-- The donor controller's row. -/
  donor : TransformsTo (Sum.elim (fun d : D.below (D.cell o) => D.grade d.1) (fun _ => g₀))
    (donorSource sem o r off) (fun x => min (Sum.elim p (fun _ => φ) x) wd)
  /-- The refined controller's row. -/
  top : TransformsTo (Sum.elim (fun d : D.below (D.cell o) => D.grade d.1) (fun _ => g₀))
    (topSource sem o b g₀) (fun x => min (Sum.elim p (fun _ => φ) x) wt)
  /-- The donor controller's label is self-visible. -/
  donor_vis : SelfVis (D.grade o) wd
  /-- The refined controller's label is self-visible. -/
  top_vis : SelfVis (D.grade o) wt
  /-- The old controller is dominated at the mixed index. -/
  avail : p ⟨o, GradedLe.refl _⟩ ≤ max wd wt

/-- A mute controller: any row transforms to the bottom-capped labelling. -/
theorem transformsTo_min_bot {E : Type*} (grade : E → ℕ) (src q : E → ExtOrd) :
    TransformsTo grade src (fun x => min (q x) ⊥) := by
  have h := TransformsTo.to_bot (grade := grade) src
  convert h using 1
  funext x
  exact min_bot_right _

/-- **The intended request has a family section**: the donor controller at the face's donor
value serves the forced fresh label; the refined controller is mute. -/
theorem family_intended {o : Cell D} {r : D.below (D.cell o)} {off b g₀ : ℕ}
    (hoff : off ≤ D.grade o) (hg₀ : g₀ ≤ D.grade o) (p : D.below (D.cell o) → ExtOrd)
    (hp : RespectsSemanticsBelow sem (D.cell o) p) :
    FamilySection sem o r off b g₀ p
      (extVisibilityReplace (min (p r) (p ⟨o, GradedLe.refl _⟩)) (D.grade o) off)
      (p ⟨o, GradedLe.refl _⟩) ⊥ where
  donor := donorSource_forced hoff hg₀ p hp
  top := transformsTo_min_bot _ _ _
  donor_vis := (hp.orderly ⟨o, GradedLe.refl _⟩).symm
  top_vis := extVisibilityReplace_bot _ _
  avail := le_max_left _ _

/-- **Every fresh label at least the face's donor value has a family section** — the refuted
prescriptions included: the refined controller at the donor value serves it; the donor
controller is mute. -/
theorem family_top {o : Cell D} {r : D.below (D.cell o)} {off b g₀ : ℕ}
    (hb : ∀ d : D.below (D.cell o), sem.E o d < ofOrd (Ordinal.omega0 * b))
    (hg₀ : g₀ ≤ D.grade o) (p : D.below (D.cell o) → ExtOrd)
    (hp : RespectsSemanticsBelow sem (D.cell o) p) {φ : ExtOrd}
    (hφ : p ⟨o, GradedLe.refl _⟩ ≤ φ) :
    FamilySection sem o r off b g₀ p φ ⊥ (p ⟨o, GradedLe.refl _⟩) where
  donor := transformsTo_min_bot _ _ _
  top := topSource_transformsTo hb p hp (hp.orderly ⟨o, GradedLe.refl _⟩).symm le_rfl hφ g₀ hg₀
  donor_vis := extVisibilityReplace_bot _ _
  top_vis := (hp.orderly ⟨o, GradedLe.refl _⟩).symm
  avail := le_max_right _ _

/-! ## Positive caps for the refined row -/

/-- **Positive-cap lifting for the refined row against an arbitrary lawful ambient**: for an
ambient `(qo, F)` served by the refined row at the cap `qo`'s donor value, a cap self-visible at
the donor's grade, and prescribed data on a proper old sub-index with a self-visible fresh
label agreeing with the ambient under the cap, bountifulness completes the old face and the
refined controller — labelled the smaller of the fresh label and the completed donor value —
agrees with the ambient under the cap and serves the literal fresh label. -/
theorem topSource_positiveCap {o : Cell D} {b : ℕ}
    (hb : ∀ d : D.below (D.cell o), sem.E o d < ofOrd (Ordinal.omega0 * b))
    (hbount : sem.IsBountiful) {g₀ : ℕ} (hg₀ : g₀ ≤ D.grade o)
    {CI : Finset ι × ℕ} (hCI : CI ∈ Plan.gradedPlan D.plan) (hle : GradedLe CI (D.cell o))
    (hne : CI ≠ D.cell o) (p : D.below CI → ExtOrd) (hp : RespectsSemanticsBelow sem CI p)
    (qo : D.below (D.cell o) → ExtOrd) (hqo : RespectsSemanticsBelow sem (D.cell o) qo)
    {F : ExtOrd}
    (hamb : TransformsTo (Sum.elim (fun d : D.below (D.cell o) => D.grade d.1) (fun _ => g₀))
      (topSource sem o b g₀) (fun x => min (Sum.elim qo (fun _ => F) x) (qo ⟨o, GradedLe.refl _⟩)))
    {γ : ExtOrd} (hγ : SelfVis (D.grade o) γ)
    (hagree : ∀ d : D.below CI, min (qo (CellScheme.below.mono hle d)) γ = min (p d) γ)
    {φ : ExtOrd} (hφvis : SelfVis (D.grade o) φ) (hφ : min F γ = min φ γ) :
    ∃ (p' : D.below (D.cell o) → ExtOrd) (wt : ExtOrd),
      RespectsSemanticsBelow sem (D.cell o) p' ∧
      (∀ d : D.below (D.cell o), min (p' d) γ = min (qo d) γ) ∧
      (∀ d : D.below CI, p' (CellScheme.below.mono hle d) = p d) ∧
      SelfVis (D.grade o) wt ∧ min wt γ = min (qo ⟨o, GradedLe.refl _⟩) γ ∧
      TransformsTo (Sum.elim (fun d : D.below (D.cell o) => D.grade d.1) (fun _ => g₀))
        (topSource sem o b g₀) (fun x => min (Sum.elim p' (fun _ => φ) x) wt) := by
  -- the ambient's fresh reading is at least its donor value
  have hF : qo ⟨o, GradedLe.refl _⟩ ≤ F := by
    have h := topSource_fresh_ge hb hg₀ hamb
    change min (qo _) (qo _) ≤ min F (qo _) at h
    rw [min_self] at h
    exact (le_min_iff.mp h).1
  obtain ⟨p', hp', hagree', hres⟩ := hbount CI _ hCI (D.cell_mem o) hle hne p qo γ hp hqo hγ hagree
  have hKvis : SelfVis (D.grade o) (p' ⟨o, GradedLe.refl _⟩) :=
    (hp'.orderly ⟨o, GradedLe.refl _⟩).symm
  refine ⟨p', min φ (p' ⟨o, GradedLe.refl _⟩), hp', hagree', hres, selfVis_min hφvis hKvis, ?_,
    topSource_transformsTo hb p' hp' (selfVis_min hφvis hKvis) (min_le_right _ _)
      (min_le_left _ _) g₀ hg₀⟩
  calc min (min φ (p' ⟨o, GradedLe.refl _⟩)) γ
      = min (min φ γ) (min (p' ⟨o, GradedLe.refl _⟩) γ) := min_min_right_distrib'' _ _ _
    _ = min (min F γ) (min (qo ⟨o, GradedLe.refl _⟩) γ) := by
        rw [← hφ, hagree' ⟨o, GradedLe.refl _⟩]
    _ = min (min F (qo ⟨o, GradedLe.refl _⟩)) γ := (min_min_right_distrib'' _ _ _).symm
    _ = min (qo ⟨o, GradedLe.refl _⟩) γ := by rw [min_eq_right hF]

end Generic

/-! ## The regression instance -/

namespace ObstructionInstance

open MixedReferenceEntailment

/-- A block above every source of the donor's row on the repaired coupled domain. -/
theorem exists_block_above_U_S :
    ∃ b : ℕ, ∀ d : D₂.below (D₂.cell U_S), rowsR.E U_S d < ofOrd (Ordinal.omega0 * b) :=
  exists_block_above rowsR U_S (fun d => rowsR_coded U_S d)

/-- The display's value at the donor is `κ'`. -/
theorem display_U_S (κ κ' : ExtOrd) (hle : κ ≤ κ') :
    display κ κ' (CellScheme.below.mono memU_S₃ ⟨U_S, GradedLe.refl _⟩) = κ' :=
  (shape κ κ' hle).at_U_S

/-- **Regression, the intended request**: on the repaired coupled domain with the mixed
display, the donor controller at `κ'` serves the request `ω + off` at the representative
`({1}, 1)`; the refined controller is mute. -/
theorem regression_family_intended {κ κ' : ExtOrd} (hκ : γ₀ ≤ κ) (hle : κ ≤ κ')
    (hvκ : SelfVis 3 κ) (hvκ' : SelfVis 3 κ') {off : ℕ} (hoff : off ≤ 2) {g₀ : ℕ}
    (hg₀ : g₀ ≤ 2) (b : ℕ) :
    ∃ r : D₂.below (D₂.cell U_S), D₂.cell r.1 = ({1}, 1) ∧
      FamilySection rowsR U_S r off b g₀
        (fun d => display κ κ' (CellScheme.below.mono memU_S₃ d))
        (ofOrd (Ordinal.omega0 * (1 : ℕ) + off)) κ' ⊥ := by
  obtain ⟨x, hx⟩ := exists_rep
  have hxU : GradedLe (D₂.cell x) (D₂.cell U_S) := (rep_below_s₀old hx).trans s₀old_below_U_S
  have hK : D₂.grade U_S = 2 := congrArg Prod.snd cell_U_S
  have hoff' : off ≤ D₂.grade U_S := by rw [hK]; exact hoff
  have hg₀' : g₀ ≤ D₂.grade U_S := by rw [hK]; exact hg₀
  have h := family_intended (r := ⟨x, hxU⟩) (b := b) hoff' hg₀'
    (fun d => display κ κ' (CellScheme.below.mono memU_S₃ d))
    ((display_respects hκ hle hvκ hvκ').mono memU_S₃)
  refine ⟨⟨x, hxU⟩, hx, ?_⟩
  have hrep : display κ κ' (CellScheme.below.mono memU_S₃ ⟨x, hxU⟩) = v₀ :=
    display_rep κ κ' hle hx _
  have hforced : extVisibilityReplace (min v₀ κ') (D₂.grade U_S) off =
      ofOrd (Ordinal.omega0 * (1 : ℕ) + off) := by
    rw [min_eq_left (v₀_le_donor hκ hle), hK]
    unfold v₀
    exact extVisibilityReplace_rep (limitPart_omega0_mul _) (by decide : 1 < 2)
  simp only [hrep, display_U_S κ κ' hle] at h
  rw [hforced] at h
  exact h

/-- **Regression, the refuted prescriptions at or above `κ'`**: every fresh label at least the
display's donor value has a family section — the refined controller at `κ'` serves it, the
donor controller mute. -/
theorem regression_family_top {κ κ' : ExtOrd} (hκ : γ₀ ≤ κ) (hle : κ ≤ κ')
    (hvκ : SelfVis 3 κ) (hvκ' : SelfVis 3 κ') (off : ℕ) {g₀ : ℕ} (hg₀ : g₀ ≤ 2)
    {φ : ExtOrd} (hφ : κ' ≤ φ) :
    ∃ (r : D₂.below (D₂.cell U_S)) (b : ℕ), D₂.cell r.1 = ({1}, 1) ∧
      FamilySection rowsR U_S r off b g₀
        (fun d => display κ κ' (CellScheme.below.mono memU_S₃ d)) φ ⊥ κ' := by
  obtain ⟨x, hx⟩ := exists_rep
  obtain ⟨b, hb⟩ := exists_block_above_U_S
  have hxU : GradedLe (D₂.cell x) (D₂.cell U_S) := (rep_below_s₀old hx).trans s₀old_below_U_S
  have hK : D₂.grade U_S = 2 := congrArg Prod.snd cell_U_S
  have hg₀' : g₀ ≤ D₂.grade U_S := by rw [hK]; exact hg₀
  have hφ' : display κ κ' (CellScheme.below.mono memU_S₃ ⟨U_S, GradedLe.refl _⟩) ≤ φ := by
    rw [display_U_S κ κ' hle]; exact hφ
  have h := family_top (r := ⟨x, hxU⟩) (off := off) hb hg₀'
    (fun d => display κ κ' (CellScheme.below.mono memU_S₃ d))
    ((display_respects hκ hle hvκ hvκ').mono memU_S₃) (φ := φ) hφ'
  simp only [display_U_S κ κ' hle] at h
  exact ⟨⟨x, hxU⟩, b, hx, h⟩

end ObstructionInstance

end VaughtConjecture.Knight
