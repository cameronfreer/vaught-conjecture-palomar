/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryFinalPrivateLift
public import VaughtConjecture.Knight.EffectiveGradeLifting

/-! # Bountifulness of the ordinary final rows

The graded-pair reduction on the reviewer's physical final-grade layer (`FinalGateLayer.Input`,
integration `44aa548`): every literal graded pair of the installed carrier lifts, from

* the predecessor's lifting on every pair whose target excludes the added index `(A, N)`
  (proper targets and every target below grade `N`), carried explicitly;
* the all-cap private-face lift `OrdinaryFinalPrivateLift.private_lift`;
* the coatom geometry `|A| = N + 1` (the private face `S` has `N` points, the carrier one more);
* mute diagonals at every non-private proper grade-`N` owner of the predecessor.

`EffectiveGradeLifting.bountiful_of_same_grade` reduces everything to same-grade pairs
`(C, i) ≤ (B, i)`, which exhaust as follows: equal indices are `lift_refl`; a target excluding the
added index transports the predecessor's lift (`inherited_lift`, which covers every target below
grade `N`); a target containing it is `(A, N)` itself, whose proper sources have grade exactly `N`
(a proper subset of `A` has at most `N` points), and are either the private face
(`private_lift`) or a scope not containing `S` — whose grade-`N` owners are all mute, so every
lawful prescription is bottom at grade `N` and `lift_inactive` applies.  Nominal grades above the
carrier's ceiling only occur at `(A, N + 1)` with source `(A, N + 1)`, an equal index.

No bountifulness of the predecessor at the final full index is assumed; apex installation and
ordered packaging are left to the integration lane. -/

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryFinalBountiful

open Transform Value ExtOrd CappedDonor CappedDonor.Ref CoatomBoundaryExtension
  AmalgamationPlan SharpWitnessComposition
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)
variable {ι : Type*} [DecidableEq ι] {A S : Finset ι} {D : CellScheme A}
variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))
variable (place : Fin N ↪ ι) (hS : Finset.univ.image place = S)
variable (E : ExactSemanticFace (PointImageSemantics.rows C.scheme place hS C.rows) F.sem)

omit [Fintype I] in
/-- The private face has exactly `N` points. -/
theorem card_S (place : Fin N ↪ ι) (hS : Finset.univ.image place = S) : S.card = N := by
  rw [← hS, Finset.card_image_of_injective _ place.injective, Finset.card_univ, Fintype.card_fin]

omit [Fintype I] in
/-- With one point beyond the private face, a proper subset of `A` containing `S` is `S`. -/
theorem eq_S_of_subset (place : Fin N ↪ ι) (hS : Finset.univ.image place = S)
    (hcard : A.card = N + 1) {B : Finset ι} (hBA : B ⊆ A) (hBne : B ≠ A) (hSB : S ⊆ B) :
    B = S := by
  have hlt : B.card < A.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hBA, hBne⟩)
  have hle : B.card ≤ S.card := by rw [card_S place hS]; omega
  exact (Finset.eq_of_subset_of_card_le hSB hle).symm

/-- A lawful section of the installed rows is bottom at every grade-`N` owner of a proper scope
not containing the private face: those owners are old, and their diagonals are mute. -/
theorem bot_of_mute (place : Fin N ↪ ι) (hS : Finset.univ.image place = S)
    (hcard : A.card = N + 1)
    (hmute : ∀ x : Cell D, D.grade x = N → D.scope x ≠ S →
      F.sem.E x ⟨x, GradedLe.refl _⟩ = ⊥)
    {B : Finset ι} (hBA : B ⊆ A) (hBne : B ≠ A) (hBS : B ≠ S)
    {p : F.carrier.below (B, N) → ExtOrd} (hp : RespectsSemanticsBelow F.rows (B, N) p)
    (e : F.carrier.below (B, N)) (he : F.carrier.grade e.1 = N) : p e = ⊥ := by
  obtain ⟨x, hx⟩ := F.proper_occurrence hBA hBne e
  have hxg : D.grade x.1 = N := by
    have h := congrArg Prod.snd (F.old_index x.1)
    change F.carrier.grade (F.old x.1) = D.grade x.1 at h
    rw [← hx, he] at h
    exact h.symm
  have hxS : D.scope x.1 ≠ S := by
    intro hxs
    exact hBS (eq_S_of_subset place hS hcard hBA hBne (hxs ▸ x.2.1))
  have hdiag : F.rows.E e.1 ⟨e.1, GradedLe.refl _⟩ = ⊥ := by
    rcases e with ⟨e, hE⟩
    change e = F.old x.1 at hx
    subst hx
    have h := F.inherited_row x.1 ⟨x.1, GradedLe.refl _⟩
    rw [hmute x.1 hxg hxS] at h
    exact h
  exact hp.eq_bot_of_diagonal e hdiag

/-- **Bountifulness of the ordinary final rows**, from the predecessor's lifting on every pair
whose target excludes the added index, the all-cap private-face lift, the coatom geometry and the
mute diagonals at non-private proper grade-`N` owners. -/
theorem bountiful
    (hfields : ∀ a f, F.fields a f = a.val f) (hgate : F.gate = .gate)
    (hgrid : F.grid = PairedSlotComparison.sourceGrid N (Fintype.card (Field P C)))
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (howners : ∀ a (c : D.below (A, N)),
      (∀ d : D.below (D.cell c.1), Short (D.grade c.1) (F.sem.E c.1 d)) ∨
      (∀ d : D.below (D.cell c.1), ∃ f : Field P C, F.lower a d.1 = a.val f))
    (hpriv : ∀ a d, F.lower a (E.map d) = a.val (.priv d))
    (hcard : A.card = N + 1)
    (hmute : ∀ x : Cell D, D.grade x = N → D.scope x ≠ S →
      F.sem.E x ⟨x, GradedLe.refl _⟩ = ⊥)
    (hpred : ∀ (I J : Finset ι × ℕ), I ∈ Plan.gradedPlan D.plan → J ∈ Plan.gradedPlan D.plan →
      (h : GradedLe I J) → ¬ GradedLe (A, N) J → CappedLift F.sem h) :
    F.rows.IsBountiful := by
  have hN : 2 ≤ N := by have := R.arity_lt; omega
  apply EffectiveGradeLifting.bountiful_of_same_grade
  intro B B' i hB hB' hsub
  by_cases hBB : B = B'
  · subst hBB
    exact lift_refl
  by_cases hJ : GradedLe (A, N) (B', i)
  · -- the target is the added index
    have hB'A : A = B' := (Finset.Subset.antisymm (D.isPlan.subset_of_mem
      (Plan.mem_gradedPlan.mp hB').1) hJ.1).symm
    subst hB'A
    have hBcard : B.card ≤ N := by
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hBB⟩)
      omega
    have hiN : N = i := (le_antisymm ((Plan.mem_gradedPlan.mp hB).2.2.trans hBcard) hJ.2).symm
    subst hiN
    -- the predecessor lifts the face one grade below
    have hlift : CappedLift F.sem (show GradedLe (B, N - 1) (A, N - 1) from ⟨hsub, le_rfl⟩) :=
      hpred (B, N - 1) (A, N - 1)
        (Plan.mem_gradedPlan.mpr ⟨(Plan.mem_gradedPlan.mp hB).1, by omega,
          (Nat.sub_le _ _).trans (Plan.mem_gradedPlan.mp hB).2.2⟩)
        (Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem, show 0 < N - 1 by omega,
          show N - 1 ≤ A.card by omega⟩)
        ⟨hsub, le_rfl⟩ (fun h => by have := h.2; omega)
    by_cases hBS : S = B
    · subst hBS
      exact OrdinaryFinalPrivateLift.private_lift R F place hS hsub hBB E hfields hgate hgrid
        hsupport howners hpriv hlift
    · intro p q γ hp hq hγ hag
      exact F.lift_inactive hsub hlift hp hq hγ hag
        (fun e he => by
          rw [bot_of_mute R F place hS hcard hmute hsub hBB (Ne.symm hBS) hp e he]
          exact bot_le)
  · exact F.inherited_lift (I := (B, i)) (J := (B', i)) ⟨hsub, le_rfl⟩ hJ
      (hpred (B, i) (B', i) hB hB' ⟨hsub, le_rfl⟩ hJ)

end
end VaughtConjecture.Knight.OrdinaryFinalBountiful
