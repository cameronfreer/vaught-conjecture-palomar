/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepDecode
public import VaughtConjecture.Knight.LowOnlyPaddedLiftingReady

/-! # Literal original faces through the padded tower

Each original face retains its entire old domain and rows. Lower target-grade
lifting transports through the actual installation, without a global grade
bound on retained proper owners.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedStepFaces
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

/-- Literal faces survive the entire installed tower, not just its field readings. -/
def layerFace {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows P.rows := by
  let L := SeparatedLayerFace.face I.boundary
    (RelativeLadderLayer.Point (X := Field I.left I.right) (Q := F.Anchor 1))
    1 Nat.one_pos (by omega) (RelativeLadderLayer.separated I.boundary
      (LowOnlyOrderedLadder.proper I hB hC)) I.rows (baseRows I F hroot hA hB hC)
    (RelativeLadderLayer.inherited_row I.boundary I.rows (by omega)
      (field I) (F.fields 1) (LowOnlyOrderedLadder.proper I hB hC)) G hT
  exact {
    map := L.map.trans ⟨P.baseMap, P.base_mono.injective⟩
    index := fun d => (P.base_index _).trans (L.index d)
    exhaustive := fun z hz => by
      rcases P.cases z with ⟨d, rfl⟩ | ⟨hs, _, _⟩
      · obtain ⟨c, rfl⟩ := L.exhaustive d (by
          change (P.carrier.cell (P.baseMap d)).1 ⊆ T at hz
          rwa [P.base_index] at hz)
        exact ⟨c, rfl⟩
      · exact False.elim (hT (hs ▸ hz))
    row := fun c d => (P.base_row (L.map c)
      ⟨L.map d.1, by rw [L.index, L.index]; exact d.2⟩).trans (L.row c d) }

def face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows (rows P hk hnext) :=
  SeparatedLayerFace.face P.carrier (F.Anchor (k + 1)) (k + 1) (Nat.succ_pos k) hnext
    (P.separated I F hroot hA hB hC (by omega)) P.rows (rows P hk hnext)
    (inherited_row P hk hnext) (layerFace P G hT) hT

def privateFace : ExactSemanticFace I.rightRows (rows P hk hnext) :=
  face P hk hnext I.rightFace hC.not_ge

def donorFace : ExactSemanticFace I.leftRows (rows P hk hnext) :=
  face P hk hnext I.leftFace hB.not_ge

theorem private_map (d : Cell I.right.scheme) :
    (privateFace P hk hnext).map d =
      LowOnlyPaddedStepDecode.original P hnext (I.rightFace.map d) := rfl

theorem donor_map (d : Cell I.left.scheme) :
    (donorFace P hk hnext).map d =
      LowOnlyPaddedStepDecode.original P hnext (I.leftFace.map d) := rfl

/-- Every lower pair transfers through these actual installed rows. -/
theorem lower_lifting (hprev : TargetGradeLifting.Through P.rows k) :
    TargetGradeLifting.Through (rows P hk hnext) k :=
  TargetGradeLifting.through_separated P.rows (F.Anchor (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated I F hroot hA hB hC (by omega))
    (rows P hk hnext) (inherited_row P hk hnext) (Nat.lt_succ_self k) hprev

end
end VaughtConjecture.Knight.LowOnlyPaddedStepFaces
