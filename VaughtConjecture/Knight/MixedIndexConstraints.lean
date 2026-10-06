/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.MixedIndexSection
public import VaughtConjecture.Knight.CoupledRepairSufficiency

/-! # Necessary source constraints at a mixed index, and the joint controller-family test

A candidate controller family at the first mixed index is fixed from the context and request
data **before** the universally quantified labelling.  This module extracts what every
respecting labelling then forces, in two layers.

**At one cell** (`capped_le_of_row_le`, `capped_eq_of_row_eq'`, `capped_bot_of_row_bot`,
`capped_orbit`, `capped_bottom_orbit`; from the locality witness alone): the capped labels
below a cell are read through one monotone shifter of the row's sources and an antitone grade
suppressor, so **source order forces capped order** when the grades are compatible, **equal
sources force equal capped labels** at equal grades, **bottom sources force bottom capped
labels**, and **a source orbit within an `ω`-block is exact** on the capped labels up to the
cell's grade (the capped-probe laws of `CoupledRepairSufficiency`, instantiated at an arbitrary
cell with its own label as the cap).  These are the necessary constraints: equal-source
collisions, order conflicts between required capped targets, and bottom/nonbottom distinctions
within a block.

**For a family** (`le_of_family_row_le`, `eq_of_family_row_eq`, `bot_of_family_row_bot`): at a
graded index reached by availability from a lower cell of the same grade, **every** controller
at that index reads the lower cells; a source order shared by the whole family forces the same
order on the labels themselves (not merely below a cap), a shared equal-source collision forces
equal labels, and a shared bottom source forces a bottom label.  Hence
`no_extension_of_family_order_conflict` / `no_extension_of_family_collision`: a prescribed face
labelling that orders two same-grade cells against the family's shared source order, or
separates two cells the family fails to separate, has **no** respecting extension through any
index the family fills — additional controllers are alternatives for availability, not for
locality, and the family is judged jointly.

**The coupled instance** (`no_realization_of_diagonal_family`): the diagonal family at the
grade-one full index reads `H₀old` and `H₀new` equally (`diagonal_H₀old_eq_H₀new`), the
prescribed pair separates them, so the family admits no respecting labelling realizing the pair
— by the family collision theorem, a second route to `no_realization_of_equal_H₀_rows`.  The
separating family of the repaired semantics passes the order test (`ω·2+3 < ω·2+4` at the two
cells, and `x₀ ≤ x₁` in every admissible labelling), and its sections over the protected faces
are the compiled `faceA_extendsR` and `faceB_extendsR`.

**Sections over the protected faces, attempted.**  A section of the old face through a fixed
family exists only if the family's source order, collisions and bottom pattern are compatible
with every permitted face labelling in the sense above; the theorems here are that test.  They
do not construct a family for the model-produced context: choosing sources so that each
controller separates what its own capped targets separate, and orders them as its own capped
targets order them, is the semantic construction that remains — the joint controller-family
search (fixed rows, actual permitted face inputs, all locality constraints simultaneously, a
dominating controller for availability).  No single source order compatible with every uncapped
labelling is asked for: different controllers may expose different orders, a controller with a
lower cap hiding a distinction another controller exposes (#351), and each must respect its own
capped targets.
Realization of the prescribed pair is kept as a separate acceptance test; no relative lift and
no reduced-projection theorem is attempted here.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value

/-! ## Necessary constraints at one cell -/

section OneCell

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}
  {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd} (h : RespectsSemanticsBelow sem BJ r)
  (Sig : D.below BJ)

include h

/-- **Source order forces capped order** when the second cell's grade is at most the first's. -/
theorem RespectsSemanticsBelow.capped_le_of_row_le (d₁ d₂ : D.below (D.cell Sig.1))
    (hrow : sem.E Sig.1 d₁ ≤ sem.E Sig.1 d₂) (hgr : D.grade d₂.1 ≤ D.grade d₁.1) :
    min (r (CellScheme.below.incl Sig d₁)) (r Sig) ≤
      min (r (CellScheme.below.incl Sig d₂)) (r Sig) := by
  obtain ⟨g, σ, hanti, -, -, hmono, -, heq⟩ := h.locality Sig
  have h1 := heq d₁
  have h2 := heq d₂
  dsimp only at h1 h2
  rw [h1, h2]
  refine min_le_min (hmono hrow) ?_
  rcases lt_or_eq_of_le hgr with hlt | heq'
  · exact hanti _ _ hlt
  · rw [heq']

/-- **Equal sources force equal capped labels** at equal grades. -/
theorem RespectsSemanticsBelow.capped_eq_of_row_eq' (d₁ d₂ : D.below (D.cell Sig.1))
    (hrow : sem.E Sig.1 d₁ = sem.E Sig.1 d₂) (hgr : D.grade d₁.1 = D.grade d₂.1) :
    min (r (CellScheme.below.incl Sig d₁)) (r Sig) =
      min (r (CellScheme.below.incl Sig d₂)) (r Sig) :=
  le_antisymm (h.capped_le_of_row_le Sig d₁ d₂ hrow.le hgr.ge)
    (h.capped_le_of_row_le Sig d₂ d₁ hrow.ge hgr.le)

/-- **A bottom source forces a bottom capped label.** -/
theorem RespectsSemanticsBelow.capped_bot_of_row_bot (d : D.below (D.cell Sig.1))
    (hrow : sem.E Sig.1 d = ⊥) : min (r (CellScheme.below.incl Sig d)) (r Sig) = ⊥ := by
  obtain ⟨g, σ, -, -, hσ, -, -, heq⟩ := h.locality Sig
  have h1 := heq d
  dsimp only at h1
  rw [h1, hrow, hσ]
  exact min_eq_left bot_le

/-- The locality witness at `Sig`, in the form of the capped-probe laws: the cap is the cell's
own label. -/
theorem RespectsSemanticsBelow.locality_self :
    TransformsTo (fun d : D.below (D.cell Sig.1) => D.grade d.1) (sem.E Sig.1)
      (fun d => min (r (CellScheme.below.incl Sig d))
        (r (CellScheme.below.incl Sig ⟨Sig.1, GradedLe.refl _⟩))) := by
  have hincl : CellScheme.below.incl Sig ⟨Sig.1, GradedLe.refl _⟩ = Sig := Subtype.ext rfl
  rw [hincl]
  exact h.locality Sig

/-- **A source orbit within an `ω`-block is exact on the capped labels**, up to the cell's
grade. -/
theorem RespectsSemanticsBelow.capped_orbit {d e : D.below (D.cell Sig.1)} {k i : ℕ}
    (hk : k ≤ D.grade Sig.1) (hi : i ≤ k)
    (he : sem.E Sig.1 e = extVisibilityReplace (sem.E Sig.1 d) k i) :
    min (r (CellScheme.below.incl Sig e)) (r Sig) =
      extVisibilityReplace (min (r (CellScheme.below.incl Sig d)) (r Sig)) k i := by
  have hincl : CellScheme.below.incl Sig ⟨Sig.1, GradedLe.refl _⟩ = Sig := Subtype.ext rfl
  have key := probe_orbit (grade := fun d : D.below (D.cell Sig.1) => D.grade d.1)
    (E := sem.E Sig.1) (p := fun d => r (CellScheme.below.incl Sig d))
    (c := ⟨Sig.1, GradedLe.refl _⟩) (fun d => d.2.2)
    (by rw [hincl]; exact (h.orderly Sig).symm) (h.locality_self Sig) hk hi he
  rwa [hincl] at key

/-- **Bottom propagates along a source orbit** at every threshold. -/
theorem RespectsSemanticsBelow.capped_bottom_orbit {d e : D.below (D.cell Sig.1)} {k i : ℕ}
    (hi : i ≤ k) (he : sem.E Sig.1 e = extVisibilityReplace (sem.E Sig.1 d) k i)
    (hd : min (r (CellScheme.below.incl Sig d)) (r Sig) = ⊥) :
    min (r (CellScheme.below.incl Sig e)) (r Sig) = ⊥ := by
  have hincl : CellScheme.below.incl Sig ⟨Sig.1, GradedLe.refl _⟩ = Sig := Subtype.ext rfl
  have key := probe_bottom_orbit (grade := fun d : D.below (D.cell Sig.1) => D.grade d.1)
    (E := sem.E Sig.1) (p := fun d => r (CellScheme.below.incl Sig d))
    (c := ⟨Sig.1, GradedLe.refl _⟩) (fun d => d.2.2)
    (by rw [hincl]; exact (h.orderly Sig).symm) (h.locality_self Sig) hi he
    (by rw [hincl]; exact hd)
  rwa [hincl] at key

end OneCell

/-! ## The joint controller-family test -/

section Family

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}
  {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd} (h : RespectsSemanticsBelow sem BJ r)
  (d₁ d₂ Xi₀ : D.below BJ) (hs₁ : D.scope d₁.1 ⊆ D.scope Xi₀.1)
  (hs₂ : D.scope d₂.1 ⊆ D.scope Xi₀.1) (hg₁ : D.grade d₁.1 = D.grade Xi₀.1)

include h hs₁ hs₂ hg₁

/-- **A shared source order forces the label order**: if every controller at the index of
`Xi₀` reads `d₁` at most `d₂`, and `d₁` reaches that index by availability, then
`r d₁ ≤ r d₂`. -/
theorem RespectsSemanticsBelow.le_of_family_row_le (hg₂ : D.grade d₂.1 ≤ D.grade d₁.1)
    (hfam : ∀ (Xi : D.below BJ), D.cell Xi.1 = D.cell Xi₀.1 →
      ∀ (h₁ : GradedLe (D.cell d₁.1) (D.cell Xi.1)) (h₂ : GradedLe (D.cell d₂.1) (D.cell Xi.1)),
        sem.E Xi.1 ⟨d₁.1, h₁⟩ ≤ sem.E Xi.1 ⟨d₂.1, h₂⟩) :
    r d₁ ≤ r d₂ := by
  obtain ⟨Xi, hXi, hle⟩ := h.availability d₁ Xi₀ hs₁ hg₁
  have h₁ : GradedLe (D.cell d₁.1) (D.cell Xi.1) := by
    rw [hXi]; exact ⟨hs₁, hg₁.le⟩
  have h₂ : GradedLe (D.cell d₂.1) (D.cell Xi.1) := by
    rw [hXi]; exact ⟨hs₂, hg₂.trans hg₁.le⟩
  have key := h.capped_le_of_row_le Xi ⟨d₁.1, h₁⟩ ⟨d₂.1, h₂⟩ (hfam Xi hXi h₁ h₂) hg₂
  have e₁ : CellScheme.below.incl Xi ⟨d₁.1, h₁⟩ = d₁ := Subtype.ext rfl
  have e₂ : CellScheme.below.incl Xi ⟨d₂.1, h₂⟩ = d₂ := Subtype.ext rfl
  rw [e₁, e₂, min_eq_left hle] at key
  exact key.trans (min_le_left _ _)

/-- **A shared equal-source collision forces equal labels.** -/
theorem RespectsSemanticsBelow.eq_of_family_row_eq (hg₂ : D.grade d₂.1 = D.grade Xi₀.1)
    (hfam : ∀ (Xi : D.below BJ), D.cell Xi.1 = D.cell Xi₀.1 →
      ∀ (h₁ : GradedLe (D.cell d₁.1) (D.cell Xi.1)) (h₂ : GradedLe (D.cell d₂.1) (D.cell Xi.1)),
        sem.E Xi.1 ⟨d₁.1, h₁⟩ = sem.E Xi.1 ⟨d₂.1, h₂⟩) :
    r d₁ = r d₂ :=
  le_antisymm
    (h.le_of_family_row_le d₁ d₂ Xi₀ hs₁ hs₂ hg₁ (hg₂.trans hg₁.symm).le
      fun Xi hXi h₁ h₂ => (hfam Xi hXi h₁ h₂).le)
    (h.le_of_family_row_le d₂ d₁ Xi₀ hs₂ hs₁ hg₂ (hg₁.trans hg₂.symm).le
      fun Xi hXi h₂ h₁ => (hfam Xi hXi h₁ h₂).ge)

end Family

section FamilyBot

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}
  {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd} (h : RespectsSemanticsBelow sem BJ r)

include h

/-- **A shared bottom source forces a bottom label.** -/
theorem RespectsSemanticsBelow.bot_of_family_row_bot (d₁ Xi₀ : D.below BJ)
    (hs₁ : D.scope d₁.1 ⊆ D.scope Xi₀.1) (hg₁ : D.grade d₁.1 = D.grade Xi₀.1)
    (hfam : ∀ (Xi : D.below BJ), D.cell Xi.1 = D.cell Xi₀.1 →
      ∀ (h₁ : GradedLe (D.cell d₁.1) (D.cell Xi.1)), sem.E Xi.1 ⟨d₁.1, h₁⟩ = ⊥) :
    r d₁ = ⊥ := by
  obtain ⟨Xi, hXi, hle⟩ := h.availability d₁ Xi₀ hs₁ hg₁
  have h₁ : GradedLe (D.cell d₁.1) (D.cell Xi.1) := by
    rw [hXi]; exact ⟨hs₁, hg₁.le⟩
  have key := h.capped_bot_of_row_bot Xi ⟨d₁.1, h₁⟩ (hfam Xi hXi h₁)
  have e₁ : CellScheme.below.incl Xi ⟨d₁.1, h₁⟩ = d₁ := Subtype.ext rfl
  rwa [e₁, min_eq_left hle] at key

/-- **No extension across a family order conflict**: a labelling `p` of a lower index ordering
two same-grade cells against the family's shared source order has no respecting extension. -/
theorem RespectsSemanticsBelow.no_extension_of_family_order_conflict {CI : Finset ι × ℕ}
    (hCI : GradedLe CI BJ) (p : D.below CI → ExtOrd)
    (hext : ∀ d, r (CellScheme.below.mono hCI d) = p d)
    (c₁ c₂ : D.below CI) (Xi₀ : D.below BJ)
    (hs₁ : D.scope c₁.1 ⊆ D.scope Xi₀.1) (hs₂ : D.scope c₂.1 ⊆ D.scope Xi₀.1)
    (hg₁ : D.grade c₁.1 = D.grade Xi₀.1) (hg₂ : D.grade c₂.1 ≤ D.grade c₁.1)
    (hfam : ∀ (Xi : D.below BJ), D.cell Xi.1 = D.cell Xi₀.1 →
      ∀ (h₁ : GradedLe (D.cell c₁.1) (D.cell Xi.1)) (h₂ : GradedLe (D.cell c₂.1) (D.cell Xi.1)),
        sem.E Xi.1 ⟨c₁.1, h₁⟩ ≤ sem.E Xi.1 ⟨c₂.1, h₂⟩)
    (hp : p c₂ < p c₁) : False := by
  have := h.le_of_family_row_le (CellScheme.below.mono hCI c₁) (CellScheme.below.mono hCI c₂) Xi₀
    hs₁ hs₂ hg₁ hg₂ hfam
  rw [hext, hext] at this
  exact absurd this (not_le.mpr hp)

/-- **No extension across a family collision**: a labelling separating two same-grade cells the
family fails to separate has no respecting extension. -/
theorem RespectsSemanticsBelow.no_extension_of_family_collision {CI : Finset ι × ℕ}
    (hCI : GradedLe CI BJ) (p : D.below CI → ExtOrd)
    (hext : ∀ d, r (CellScheme.below.mono hCI d) = p d)
    (c₁ c₂ : D.below CI) (Xi₀ : D.below BJ)
    (hs₁ : D.scope c₁.1 ⊆ D.scope Xi₀.1) (hs₂ : D.scope c₂.1 ⊆ D.scope Xi₀.1)
    (hg₁ : D.grade c₁.1 = D.grade Xi₀.1) (hg₂ : D.grade c₂.1 = D.grade Xi₀.1)
    (hfam : ∀ (Xi : D.below BJ), D.cell Xi.1 = D.cell Xi₀.1 →
      ∀ (h₁ : GradedLe (D.cell c₁.1) (D.cell Xi.1)) (h₂ : GradedLe (D.cell c₂.1) (D.cell Xi.1)),
        sem.E Xi.1 ⟨c₁.1, h₁⟩ = sem.E Xi.1 ⟨c₂.1, h₂⟩)
    (hp : p c₁ ≠ p c₂) : False := by
  have := h.eq_of_family_row_eq (CellScheme.below.mono hCI c₁) (CellScheme.below.mono hCI c₂) Xi₀
    hs₁ hs₂ hg₁ hg₂ hfam
  rw [hext, hext] at this
  exact hp this

end FamilyBot

/-! ## The coupled instance: the diagonal family fails the joint test -/

section Instance

/-- **The diagonal family cannot realize the prescribed pair**, by the family collision test:
its controllers at the grade-one full index read `H₀old` and `H₀new` equally, and the pair
separates them. -/
theorem no_realization_of_diagonal_family (sem : Semantics D₂)
    (hdiag : ∀ (U : Cell D₂) (d : D₂.below (D₂.cell U)), sem.E U d = rowsR.diagonal d.1)
    {q : D₂.below (Finset.univ, 3) → ExtOrd}
    (hq : RespectsSemanticsBelow sem (Finset.univ, 3) q) : ¬ RealizesPair q := by
  intro hpair
  obtain ⟨c, hc⟩ := D₂_complete (Finset.univ, 1) (Plan.mem_gradedPlan.mpr
    ⟨D₂.isPlan.domain_mem, by decide, by rw [Finset.card_univ, Fintype.card_fin]; decide⟩)
  have hcU : GradedLe (D₂.cell c) (Finset.univ, 3) := by
    rw [hc]; exact ⟨Finset.Subset.refl _, by decide⟩
  have hgc : D₂.grade c = 1 := by change (D₂.cell c).2 = 1; rw [hc]
  have key := hq.eq_of_family_row_eq ⟨H₀old, memH₀old₃⟩ ⟨H₀new, memH₀new₃⟩ ⟨c, hcU⟩
    (by change D₂.scope H₀old ⊆ (D₂.cell c).1; rw [hc]; exact Finset.subset_univ _)
    (by change D₂.scope H₀new ⊆ (D₂.cell c).1; rw [hc]; exact Finset.subset_univ _)
    (by rw [hgc, grade_H₀old]) (by rw [hgc, grade_H₀new])
    (fun Xi _ h₁ h₂ => diagonal_candidate_equal_H₀ sem hdiag Xi.1 h₁ h₂)
  rw [hpair.at_H₀old, hpair.at_H₀new] at key
  exact absurd key (ne_of_lt γ₀_lt_γ₁)

end Instance

end VaughtConjecture.Knight
