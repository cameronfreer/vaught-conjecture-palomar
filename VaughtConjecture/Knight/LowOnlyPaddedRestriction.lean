/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedEndpoints

/-! # Exact earlier lower sets inside every later recursive LOW layer

New full-scope owners have strictly larger grades. Thus every earlier lower
set is literally inherited, with a constructed occurrence equivalence and
lawfulness transport. These are row facts, independent of higher lifting.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedRestriction
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (t : ℕ) (ht : t + 2 ≤ A.card) (J : Finset ι × ℕ) (hJ : J.2 ≤ t + 2)

def belowEquiv : (r : ℕ) → (hr : t + r + 2 ≤ A.card) →
    (build I F hroot hA hB hC t ht).carrier.below J ≃
      (build I F hroot hA hB hC (t + r) hr).carrier.below J
  | 0, _ => Equiv.refl _
  | r + 1, hr =>
    (belowEquiv r (by omega)).trans
      (HighLayerBountiful.equiv (build I F hroot hA hB hC (t + r) (by omega)).carrier
        (F.Anchor (t + r + 2 + 1)) (t + r + 2 + 1) (by omega) (by omega) J
        (fun h => by have := h.2; omega))

theorem belowEquiv_index (r : ℕ) (hr : t + r + 2 ≤ A.card)
    (d : (build I F hroot hA hB hC t ht).carrier.below J) :
    (build I F hroot hA hB hC (t + r) hr).carrier.cell
        (belowEquiv I F hroot hA hB hC t ht J hJ r hr d).1 =
      (build I F hroot hA hB hC t ht).carrier.cell d.1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    exact (HighLayerBountiful.equiv_cell
      (build I F hroot hA hB hC (t + r) (by omega)).carrier
      (F.Anchor (t + r + 2 + 1)) (t + r + 2 + 1) (by omega) (by omega)
      J (fun h => by have := h.2; omega) _).trans (ih (by omega))

/-- Pullback of an arbitrary lawful section along the actual occurrence map.
No agreement of independently selected renderings is used. -/
theorem pullback (r : ℕ) (hr : t + r + 2 ≤ A.card)
    {q : (build I F hroot hA hB hC (t + r) hr).carrier.below J → ExtOrd}
    (hq : RespectsSemanticsBelow (build I F hroot hA hB hC (t + r) hr).rows J q) :
    RespectsSemanticsBelow (build I F hroot hA hB hC t ht).rows J
      (q ∘ belowEquiv I F hroot hA hB hC t ht J hJ r hr) := by
  induction r with
  | zero => exact hq
  | succ r ih =>
    let P := build I F hroot hA hB hC (t + r) (by omega)
    have hnot : ¬ GradedLe (A, t + r + 2 + 1) J := fun h => by have := h.2; omega
    let e := HighLayerBountiful.equiv P.carrier (F.Anchor (t + r + 2 + 1))
      (t + r + 2 + 1) (by omega) (by omega) J hnot
    have hp : RespectsSemanticsBelow P.rows J (q ∘ e) := by
      apply (SeparatedLayerFace.respects_iff P.carrier (F.Anchor (t + r + 2 + 1))
        (t + r + 2 + 1) (by omega) (by omega)
        (P.separated I F hroot hA hB hC (by omega)) P.rows
        (LowOnlyPaddedStepRows.rows P (by omega) (by omega))
        (LowOnlyPaddedStepRows.inherited_row P (by omega) (by omega)) J hnot _).mpr
      change RespectsSemanticsBelow (LowOnlyPaddedStepRows.rows P (by omega) (by omega))
        J (fun x => q (e (e.symm x)))
      simp only [Equiv.apply_symm_apply]
      exact hq
    exact ih (by omega) hp

/-- A whole lawful section restricts lawfully to every earlier native target. -/
theorem whole_pullback (r : ℕ) (hr : t + r + 2 ≤ A.card)
    {q : Cell (build I F hroot hA hB hC (t + r) hr).carrier → ExtOrd}
    (hq : RespectsSemantics (build I F hroot hA hB hC (t + r) hr).rows q) :
    RespectsSemanticsBelow (build I F hroot hA hB hC t ht).rows J
      (fun d => q (belowEquiv I F hroot hA hB hC t ht J hJ r hr d).1) :=
  pullback I F hroot hA hB hC t ht J hJ r hr (hq.toBelow J)

variable {t ht J hJ}

/-- Earlier original occurrences remain the same original occurrences after
transport through all later layers. -/
theorem belowEquiv_original (t : ℕ) (ht : t + 2 ≤ A.card) (J : Finset ι × ℕ)
    (hJ : J.2 ≤ t + 2) (r : ℕ) (hr : t + r + 2 ≤ A.card)
    (d : I.boundary.below J) :
    (belowEquiv I F hroot hA hB hC t ht J hJ r hr
      ⟨LowOnlyPaddedEndpoints.original I F hroot hA hB hC t ht d.1,
        by rw [LowOnlyPaddedEndpoints.original_index]; exact d.2⟩).1 =
      LowOnlyPaddedEndpoints.original I F hroot hA hB hC (t + r) hr d.1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change LowOnlyPaddedStepRows.old (build I F hroot hA hB hC (t + r) (by omega))
      (by omega) (belowEquiv I F hroot hA hB hC t ht J hJ r (by omega)
        ⟨LowOnlyPaddedEndpoints.original I F hroot hA hB hC t ht d.1,
          by rw [LowOnlyPaddedEndpoints.original_index]; exact d.2⟩).1 = _
    exact congrArg (LowOnlyPaddedStepRows.old
      (build I F hroot hA hB hC (t + r) (by omega)) (by omega)) (ih (by omega))

/-- The retained long grade-one base of any constructed layer is lawful on
restriction. Availability is supplied by an actual full-scope base tip. -/
theorem base_pullback {k : ℕ} (P : Layer I F hroot hA hB hC k)
    {q : Cell P.carrier → ExtOrd} (hq : RespectsSemantics P.rows q) :
    RespectsSemanticsBelow (baseRows I F hroot hA hB hC) (A, 1)
      (fun d => q (P.baseMap d.1)) := by
  obtain ⟨a, _⟩ := F.exists_rank_anchor le_rfl (F.zero_admissible 1)
  let c : Cell (base I F hroot hA hB hC) :=
    RelativeLadderLayer.added I.boundary (by omega) (SupportLadderRows.leaf (Nat.succ_pos _) a)
  have hc : (base I F hroot hA hB hC).cell c = (A, 1) :=
    RelativeLadderLayer.added_index I.boundary (by omega) _
  have hp := (P.base_respects c q).mp (hq.toBelow _)
  exact GradeCutLayerRows.cast_respects (base I F hroot hA hB hC)
    (baseRows I F hroot hA hB hC) hc hp

end
end VaughtConjecture.Knight.LowOnlyPaddedRestriction
