/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepRendering

/-! # Iterated actual padded LOW rows and incoming renderings

Each successor returns the invariant it consumes. Starting at the unchanged
checked grade-two carrier therefore constructs the actual one-scope rows and
renderings through every available finite height. This is not a bountifulness
or model-receiving theorem.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedIteration
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder LowOnlyPaddedContract
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}

def successor (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card) :
    Layer I F hroot hA hB hC (k + 1) where
  carrier := LowOnlyPaddedStepRows.carrier P hnext
  rows := LowOnlyPaddedStepRows.rows P hk hnext
  consistent := LowOnlyPaddedStepRows.consistent P hk hnext
  baseMap := LowOnlyPaddedStepRendering.baseMap P hnext
  base_mono := (SourceLayerCarrier.old_order _ _ _ _ _).comp P.base_mono
  base_index := LowOnlyPaddedStepRendering.base_index P hnext
  base_row := LowOnlyPaddedStepRendering.base_row P hk hnext
  base_respects := LowOnlyPaddedStepRendering.base_respects P hk hnext
  cases := LowOnlyPaddedStepRendering.cell_cases P hk hnext
  higher_short := LowOnlyPaddedStepRendering.higher_short P hk hnext
  render := LowOnlyPaddedStepRendering.render P hk hnext
  birth := LowOnlyPaddedStepRendering.birth P
  birth_ranks := LowOnlyPaddedStepRendering.birth_ranks P
  render_base := LowOnlyPaddedStepRendering.render_base P hk hnext
  lawful := LowOnlyPaddedStepRendering.render_lawful P hk hnext
  bound := LowOnlyPaddedStepRendering.render_bound P hk hnext
  supported := LowOnlyPaddedStepRendering.render_supported P hk hnext
  agreement {_j} hj S _T hS hT hp ht :=
    LowOnlyPaddedStepRendering.render_agreement P hk hnext hj S hS hp hT ht
  ceiling_at := LowOnlyPaddedStepRendering.render_ceiling_at P hk hnext

variable (I F hroot hA hB hC)

/-- Closed finite recursion: no layer-readiness or source-lawfulness premise. -/
def build : (t : ℕ) → t + 2 ≤ A.card → Layer I F hroot hA hB hC (t + 2)
  | 0, _ => initial I F hroot hA hB hC
  | t + 1, ht => successor (build t (by omega)) (by omega) (by omega)

theorem build_zero (ht : 0 + 2 ≤ A.card) :
    build I F hroot hA hB hC 0 ht = initial I F hroot hA hB hC := rfl

theorem build_plan (t : ℕ) (ht : t + 2 ≤ A.card) :
    (build I F hroot hA hB hC t ht).carrier.plan = I.boundary.plan := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih (by omega)

theorem build_consistent (t : ℕ) (ht : t + 2 ≤ A.card) :
    (build I F hroot hA hB hC t ht).rows.IsConsistent :=
  (build I F hroot hA hB hC t ht).consistent

/-- A later step keeps every row of the preceding actual output, not only
the original boundary or its selected displays. -/
theorem build_inherited_row (t : ℕ) (ht : (t + 1) + 2 ≤ A.card)
    (c : Cell (build I F hroot hA hB hC t (by omega)).carrier)
    (d : (build I F hroot hA hB hC t (by omega)).carrier.below
      ((build I F hroot hA hB hC t (by omega)).carrier.cell c)) :
    (build I F hroot hA hB hC (t + 1) ht).rows.E
      (LowOnlyPaddedStepRows.old (build I F hroot hA hB hC t (by omega)) (by omega) c)
      (LowOnlyPaddedStepRows.ownerEquiv (build I F hroot hA hB hC t (by omega))
        (by omega) (by omega) c d) =
      (build I F hroot hA hB hC t (by omega)).rows.E c d :=
  LowOnlyPaddedStepRows.inherited_row _ _ _ c d

theorem build_render_lawful (t : ℕ) (ht : t + 2 ≤ A.card) {j : ℕ} (hj : t + 2 ≤ j)
    (S : State I.left I.right) (hS : F.Admissible j S) (hp : ∀ d, S.profile d ≠ ⊤)
    {G : Finset ExtOrd} {H : ExtOrd} (hG : ∀ z ∈ G, SelfVis (t + 2) z)
    (hH : SelfVis (t + 2) H) (hb : ∀ d, S.profile d ≤ H) :
    RespectsSemanticsBelow (build I F hroot hA hB hC t ht).rows (A, j)
      (fun d => (build I F hroot hA hB hC t ht).render hj S hS hp G H d.1) :=
  (build I F hroot hA hB hC t ht).lawful hj S hS hp hG hH hb

theorem build_original_readback (t : ℕ) (ht : t + 2 ≤ A.card) {j : ℕ} (hj : t + 2 ≤ j)
    (S : State I.left I.right) (hS : F.Admissible j S) (hp : ∀ d, S.profile d ≠ ⊤)
    {G : Finset ExtOrd} {H : ExtOrd} (hG : ∀ z ∈ G, SelfVis (t + 2) z)
    (hH : SelfVis (t + 2) H) (hb : ∀ d, S.profile d ≤ H) (d : Cell I.boundary) :
    (build I F hroot hA hB hC t ht).render hj S hS hp G H
      ((build I F hroot hA hB hC t ht).baseMap
        (RelativeLadderLayer.old I.boundary (by omega) d)) = S.profile (field I d) :=
  Layer.original_readback I F hroot hA hB hC _ hj S hS hp hG hH hb d

/-- Grade three and grade four use the same successor, without a separate
carrier or a supplied section contract. -/
def gradeThree (ht : 3 ≤ A.card) : Layer I F hroot hA hB hC 3 :=
  build I F hroot hA hB hC 1 ht

def gradeFour (ht : 4 ≤ A.card) : Layer I F hroot hA hB hC 4 :=
  build I F hroot hA hB hC 2 ht

end
end VaughtConjecture.Knight.LowOnlyPaddedIteration
