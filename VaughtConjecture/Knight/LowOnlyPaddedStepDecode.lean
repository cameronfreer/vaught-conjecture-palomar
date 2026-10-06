/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedIteration
public import VaughtConjecture.Knight.LowOnlyPaddedDecode

/-! # Protected repair on every constructed padded LOW successor

The scalar repair's fixed grid and orbit receipts imply cap agreement at
every actual installed coordinate. Both source sections are lawful by the
constructed recursion, so positive-cut transport gives lawful decoding even
at long inherited rows. The input is a lawful prescription at the native
source cut, not an arbitrary external ambient.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedStepDecode
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedStepRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

def original (d : Cell I.boundary) : Cell (carrier P hnext) :=
  old P hnext (P.baseMap (RelativeLadderLayer.old I.boundary (by omega) d))

theorem original_index (d : Cell I.boundary) :
    (carrier P hnext).cell (original P hnext d) = I.boundary.cell d := by
  rw [original, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index,
    P.base_index, RelativeLadderLayer.old_index]

theorem source_original (a : F.Anchor (k + 1)) (d : Cell I.boundary) :
    source P hk hnext a (original P hnext d) = F.fields (k + 1) a (field I d) := by
  rw [original, source_old]
  exact (P.original_readback I F hroot hA hB hC (Nat.le_succ k)
    (state F a) (state_admissible F a) (state_proper F a)
    (fun _ hz => (PairedSlotComparison.sourceGrid_visible hz).mono (Nat.le_succ k))
    ((PairedSlotComparison.sourceGrid_visible
      (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    (fun f => by rw [state_profile]; exact LowOnlyRecursiveCharts.anchor_bound F a f) d).trans
    (congrFun (state_profile F a) (field I d))

theorem leaf_row (a : F.Anchor (k + 1))
    (d : (carrier P hnext).below ((carrier P hnext).cell (controller P hnext a).1)) :
    (rows P hk hnext).E (controller P hnext a).1 d = source P hk hnext a d.1 :=
  (data P hk hnext).row_new _ _

theorem source_ceiling (a : F.Anchor (k + 1)) :
    source P hk hnext a (controller P hnext a).1 = ceiling P :=
  (data P hk hnext).profile_diagonal _

theorem protected_caps {b : ℕ} {a : F.Anchor (k + 1)} {S : State I.left I.right}
    (r : F.ProtectedRepair a.val S (k + 1) b)
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1)
    (d : Cell (carrier P hnext)) :
    min (r.decoder (source P hk hnext r.anchor d)) (CanonicalPairedInverse.grid (k + 1) b) =
      min (source P hk hnext a d) (CanonicalPairedInverse.grid (k + 1) b) := by
  exact OrbitPrefixSupport.decode_agree r.witness (CanonicalPairedInverse.grid_visible _ _)
    (by rw [gTop_of_le le_rfl]; exact le_top) r.reaches
    (fun _ hz hlt => LowOnlyPaddedDecode.grid_fixed_below r hz hlt) r.boundary_fixed
    (source_supported P hk hnext a)
    (source_agreement P hk hnext r.anchor a
      (PairedSlotComparison.sourceGrid_endpoint hb) r.prefix_eq) d

theorem protected_lawful {b : ℕ} {a : F.Anchor (k + 1)} {S : State I.left I.right}
    (r : F.ProtectedRepair a.val S (k + 1) b)
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1) :
    RespectsSemanticsBelow (rows P hk hnext) (A, k + 1)
      (fun d => r.decoder (source P hk hnext r.anchor d.1)) := by
  exact (OrbitPrefixSupport.decode_respects_of_positive_cut r.witness
    (source_lawful P hk hnext a) (source_lawful P hk hnext r.anchor)
    (fun d => d.2.2) (CanonicalPairedInverse.grid_visible _ _) (ofOrd_ne_bot _) r.reaches
    (fun _ hz hlt => LowOnlyPaddedDecode.grid_fixed_below r hz hlt) r.boundary_fixed
    (fun d => source_supported P hk hnext a d.1)
    (fun d => source_agreement P hk hnext r.anchor a
      (PairedSlotComparison.sourceGrid_endpoint hb) r.prefix_eq d.1)).1

theorem original_decode {b : ℕ} {a : F.Anchor (k + 1)} {S : State I.left I.right}
    (r : F.ProtectedRepair a.val S (k + 1) b) (d : Cell I.boundary) :
    r.decoder (source P hk hnext r.anchor (original P hnext d)) =
      S.profile (field I d) := by
  rw [source_original]
  exact r.readback _

def privateAt (d : I.right.scheme.below (effC n (k + 1))) :
    (carrier P hnext).below (A, k + 1) :=
  ⟨original P hnext (I.rightFace.map d.1), by
    rw [original_index]
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    have hg := congrArg Prod.snd (I.rightFace.index d.1)
    exact hg.le.trans (d.2.2.trans (min_le_left _ _))⟩

def donorAt (d : I.left.scheme.below (effC n (k + 1))) :
    (carrier P hnext).below (A, k + 1) :=
  ⟨original P hnext (I.leftFace.map d.1), by
    rw [original_index]
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    have hg := congrArg Prod.snd (I.leftFace.index d.1)
    exact hg.le.trans (d.2.2.trans (min_le_left _ _))⟩

theorem private_source_repair {b : ℕ} {S : State I.left I.right}
    (hS : F.Admissible (k + 1) S)
    (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) (k + 1))
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1)
    {v : I.right.scheme.below (effC n (k + 1)) → ExtOrd}
    (hv : RespectsSemanticsBelow I.right.rows (effC n (k + 1)) v)
    (hag : ∀ d, min (v d) (CanonicalPairedInverse.grid (k + 1) b) =
      min (S.lowerC (k + 1) d) (CanonicalPairedInverse.grid (k + 1) b)) :
    ∃ w, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) w ∧
      (∀ d, w (privateAt P hnext d) = v d) ∧
      ∀ d, min (w d) (CanonicalPairedInverse.grid (k + 1) b) =
        min (source P hk hnext ⟨S.profile, hc, S, hS, rfl⟩ d.1)
          (CanonicalPairedInverse.grid (k + 1) b) := by
  obtain ⟨S', hS', he, _, _, ⟨r⟩⟩ := F.private_protected_repair (by omega) hS hc hv hag
  refine ⟨_, protected_lawful P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb, ?_,
    fun d => protected_caps P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb d.1⟩
  intro d
  change r.decoder (source P hk hnext r.anchor (original P hnext (I.rightFace.map d.1))) = v d
  exact (original_decode P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r
    (I.rightFace.map d.1)).trans
    ((field_private I F hroot
      (LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega) hS') d.1).trans
      (congrFun he d))

theorem donor_source_repair {b : ℕ} {S : State I.left I.right}
    (hS : F.Admissible (k + 1) S)
    (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) (k + 1))
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1)
    {u : I.left.scheme.below (effC n (k + 1)) → ExtOrd}
    (hu : RespectsSemanticsBelow I.left.rows (effC n (k + 1)) u)
    (hag : ∀ d, min (u d) (CanonicalPairedInverse.grid (k + 1) b) =
      min (S.lowerP (k + 1) d) (CanonicalPairedInverse.grid (k + 1) b)) :
    ∃ w, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) w ∧
      (∀ d, w (donorAt P hnext d) = u d) ∧
      ∀ d, min (w d) (CanonicalPairedInverse.grid (k + 1) b) =
        min (source P hk hnext ⟨S.profile, hc, S, hS, rfl⟩ d.1)
          (CanonicalPairedInverse.grid (k + 1) b) := by
  obtain ⟨S', _hS', he, _, _, ⟨r⟩⟩ := F.donor_protected_repair (by omega) hS hc hu hag
  refine ⟨_, protected_lawful P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb, ?_,
    fun d => protected_caps P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb d.1⟩
  intro d
  change r.decoder (source P hk hnext r.anchor (original P hnext (I.leftFace.map d.1))) = u d
  exact (original_decode P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r
    (I.leftFace.map d.1)).trans
    ((field_read I S' (I.leftFace.map d.1)).trans
      ((I.paste_left S'.u S'.v d.1).trans (congrFun he d)))

end
end VaughtConjecture.Knight.LowOnlyPaddedStepDecode
