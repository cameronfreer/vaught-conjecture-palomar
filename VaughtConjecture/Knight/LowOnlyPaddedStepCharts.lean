/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepDecode
public import VaughtConjecture.Knight.LowOnlyPaddedCharts

/-! # Actual serving charts on higher padded rows

Locality and availability select an installed native leaf from an arbitrary
lawful target-local ambient. Its chart reads every physical coordinate.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedStepCharts
open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse
open LowOnlyPaddedContract LowOnlyPaddedStepRows LowOnlyOrderedLadder
open LowOnlyPaddedDecode (grid_fixed_below)
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

/-- Locality and availability choose an actual installed native leaf. -/
theorem exists_chart
    {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q) :
    ∃ a : F.Anchor (k + 1), ∃ σ : ExtOrd → ExtOrd, ∃ M : ExtOrd,
      Witness (gTop (k + 1)) σ ∧
      (∀ d, (carrier P hnext).grade d.1 = k + 1 → q d ≤ M) ∧
      ∀ d, σ (source P hk hnext a d.1) = min (q d) M := by
  obtain ⟨a₀, _⟩ := F.exists_rank_anchor (by omega : 1 ≤ k + 1)
    (F.zero_admissible (k + 1))
  obtain ⟨H⟩ := AmbientGradeCharts.exists_chart hq
    ⟨⟨(controller P hnext a₀).1, (controller P hnext a₀).2.symm ▸ GradedLe.refl _⟩,
      (controller P hnext a₀).2⟩
  let c : SourcePrefixLayer.Controller (carrier P hnext) (k + 1) := ⟨H.owner.1, H.index⟩
  let a := member P hk hnext c
  have ha : controller P hnext a = c :=
    (SeparatedSourceLayerCarrier.controllerEquiv P.carrier (F.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext
      (P.separated I F hroot hA hB hC (by omega))).apply_symm_apply c
  refine ⟨a, H.shift, q H.owner, H.witness, H.dominates, ?_⟩
  intro d
  have hr := H.read_capped d d.2.2
  have he : (rows P hk hnext).E H.owner.1 (H.occurrence d d.2.2) =
      source P hk hnext a d.1 := by
    change (data P hk hnext).rows.E c.1 _ = (data P hk hnext).profile _ _
    rw [ScopedSourcePrefixLayer.Data.row_new _ c]
    rw [ha]
    rfl
  rwa [he] at hr

end
end VaughtConjecture.Knight.LowOnlyPaddedStepCharts
