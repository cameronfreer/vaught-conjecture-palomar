/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedSuccessor

/-! # Protected decoding on the actual padded LOW successor

Both physical source sections are constructed lawfully by the successor.
The protected inverse then retains every actual coordinate at the native cut,
including unused rungs and long tips. Its decoded output is lawful without a
shortness assumption on the inherited rows.

The two source-repair corollaries accept a lawful original-face prescription
at this native cut. They are not arbitrary-ambient lifting: constructing that
prescription from an external physical chart, and restoring above an owner,
are separate obligations.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedDecode
open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse
open LowOnlyPaddedSuccessor LowOnlyOrderedLadder
noncomputable section

section Grid
variable {n K j b : ℕ} {P C : SemScheme n} {F : LowOnly.Family P C K}
  {a : Field P C → ExtOrd} {S : State P C}

theorem grid_fixed_below (r : F.ProtectedRepair a S j b)
    {z : ExtOrd} (hz : z ∈ PairedSlotComparison.sourceGrid j (Fintype.card (Field P C)))
    (hlt : z < grid j b) : r.decoder z = z := by
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact r.witness.bot
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    apply r.grid_fixed
    by_contra hn
    have hi : b ≤ i := Nat.le_of_not_gt hn
    exact (not_le_of_gt hlt) (ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl))

end Grid

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem protected_caps {b : ℕ} {a : F.Anchor 2} {S : State I.left I.right}
    (r : F.ProtectedRepair a.val S 2 b)
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1)
    (d : Cell (carrier I F hroot hA hB hC)) :
    min (r.decoder (source I F hroot hA hB hC r.anchor d)) (grid 2 b) =
      min (source I F hroot hA hB hC a d) (grid 2 b) := by
  exact OrbitPrefixSupport.decode_agree r.witness (grid_visible 2 b)
    (by rw [gTop_of_le le_rfl]; exact le_top) r.reaches
    (fun _ hz hlt => grid_fixed_below r hz hlt) r.boundary_fixed
    (source_supported I F hroot hA hB hC a)
    (source_prefix I F hroot hA hB hC r.anchor a
      (PairedSlotComparison.sourceGrid_endpoint hb) r.prefix_eq) d

theorem protected_lawful {b : ℕ} {a : F.Anchor 2} {S : State I.left I.right}
    (r : F.ProtectedRepair a.val S 2 b)
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1) :
    RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2)
      (fun d => r.decoder (source I F hroot hA hB hC r.anchor d.1)) := by
  exact (OrbitPrefixSupport.decode_respects_of_positive_cut r.witness
    (source_lawful I F hroot hA hB hC a) (source_lawful I F hroot hA hB hC r.anchor)
    (fun d => d.2.2) (grid_visible 2 b) (ofOrd_ne_bot _) r.reaches
    (fun _ hz hlt => grid_fixed_below r hz hlt) r.boundary_fixed
    (fun d => source_supported I F hroot hA hB hC a d.1)
    (fun d => source_prefix I F hroot hA hB hC r.anchor a
      (PairedSlotComparison.sourceGrid_endpoint hb) r.prefix_eq d.1)).1

theorem original_decode {b : ℕ} {a : F.Anchor 2} {S : State I.left I.right}
    (r : F.ProtectedRepair a.val S 2 b) (d : Cell I.boundary) :
    r.decoder (source I F hroot hA hB hC r.anchor (original I F hroot hA hB hC d)) =
      S.profile (field I d) := by
  rw [original_readback]
  exact r.readback _

/-- Physical private occurrences in the grade-two target. -/
def privateAt (d : I.right.scheme.below (effC n 2)) :
    (carrier I F hroot hA hB hC).below (A, 2) :=
  ⟨original I F hroot hA hB hC (I.rightFace.map d.1), by
    rw [original_index]
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    have hg := congrArg Prod.snd (I.rightFace.index d.1)
    change I.boundary.grade (I.rightFace.map d.1) = I.right.scheme.grade d.1 at hg
    exact hg.le.trans (d.2.2.trans (min_le_left _ _))⟩

/-- Physical donor occurrences in the same target. -/
def donorAt (d : I.left.scheme.below (effC n 2)) :
    (carrier I F hroot hA hB hC).below (A, 2) :=
  ⟨original I F hroot hA hB hC (I.leftFace.map d.1), by
    rw [original_index]
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    have hg := congrArg Prod.snd (I.leftFace.index d.1)
    change I.boundary.grade (I.leftFace.map d.1) = I.left.scheme.grade d.1 at hg
    exact hg.le.trans (d.2.2.trans (min_le_left _ _))⟩

theorem private_source_repair {b : ℕ} {S : State I.left I.right}
    (hS : F.Admissible 2 S)
    (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) 2)
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1)
    {v : I.right.scheme.below (effC n 2) → ExtOrd}
    (hv : RespectsSemanticsBelow I.right.rows (effC n 2) v)
    (hag : ∀ d, min (v d) (grid 2 b) = min (S.lowerC 2 d) (grid 2 b)) :
    ∃ w, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) w ∧
      (∀ d, w (privateAt I F hroot hA hB hC d) = v d) ∧
      ∀ d, min (w d) (grid 2 b) =
        min (source I F hroot hA hB hC ⟨S.profile, hc, S, hS, rfl⟩ d.1) (grid 2 b) := by
  obtain ⟨S', hS', he, _, _, ⟨r⟩⟩ := F.private_protected_repair (by decide) hS hc hv hag
  refine ⟨_, protected_lawful I F hroot hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb, ?_,
    fun d => protected_caps I F hroot hA hB hC
      (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb d.1⟩
  intro d
  change r.decoder (source I F hroot hA hB hC r.anchor
    (original I F hroot hA hB hC (I.rightFace.map d.1))) = v d
  exact (original_decode I F hroot hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r (I.rightFace.map d.1)).trans
    ((field_private I F hroot
      (LowOnlyRecursiveCoverage.admissible_down F (by decide) (by decide) hS') d.1).trans
        (congrFun he d))

theorem donor_source_repair {b : ℕ} {S : State I.left I.right}
    (hS : F.Admissible 2 S)
    (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) 2)
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1)
    {u : I.left.scheme.below (effC n 2) → ExtOrd}
    (hu : RespectsSemanticsBelow I.left.rows (effC n 2) u)
    (hag : ∀ d, min (u d) (grid 2 b) = min (S.lowerP 2 d) (grid 2 b)) :
    ∃ w, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) w ∧
      (∀ d, w (donorAt I F hroot hA hB hC d) = u d) ∧
      ∀ d, min (w d) (grid 2 b) =
        min (source I F hroot hA hB hC ⟨S.profile, hc, S, hS, rfl⟩ d.1) (grid 2 b) := by
  obtain ⟨S', hS', he, _, _, ⟨r⟩⟩ := F.donor_protected_repair (by decide) hS hc hu hag
  refine ⟨_, protected_lawful I F hroot hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb, ?_,
    fun d => protected_caps I F hroot hA hB hC
      (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb d.1⟩
  intro d
  change r.decoder (source I F hroot hA hB hC r.anchor
    (original I F hroot hA hB hC (I.leftFace.map d.1))) = u d
  exact (original_decode I F hroot hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r (I.leftFace.map d.1)).trans
    ((field_read I S' (I.leftFace.map d.1)).trans
      ((I.paste_left S'.u S'.v d.1).trans (congrFun he d)))

end
end VaughtConjecture.Knight.LowOnlyPaddedDecode
