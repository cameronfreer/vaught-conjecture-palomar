/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedSuccessor

/-! # Protected decoding on the actual padded growth successor

Both physical source sections are constructed lawfully by the successor.
The protected inverse then retains every actual coordinate at the native cut,
including unused rungs and long tips. Its decoded output is lawful without a
shortness assumption on the inherited rows.

The two source-repair corollaries accept a lawful original-face prescription
at this native cut. They are not arbitrary-ambient lifting: constructing that
prescription from an external physical chart, and restoring above an owner,
are separate obligations. Adapted from `LowOnlyPaddedDecode`, consuming the
actual growth fibres rather than substituting LOW.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedDecode
open Transform Value ExtOrd CappedDonor Growth CanonicalPairedInverse
open GrowthPaddedSuccessor GrowthOrderedBase
noncomputable section

section Grid
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  {X : RelativeData DA semA DQ semQ} {j b : ℕ}
  {a : Field DA DQ → ExtOrd} {S : State DA DQ}

/-- The replacement indexes the existing fixed catalogue. -/
def repairAnchor (r : ProtectedRepair X a S j b) : Catalogue X j :=
  ⟨r.encoded.profile, r.canonical, r.encoded, r.admitted, rfl⟩

theorem grid_fixed_below (r : ProtectedRepair X a S j b)
    {z : ExtOrd} (hz : z ∈ PairedSlotComparison.sourceGrid j (Fintype.card (Field DA DQ)))
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
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem protected_caps {b : ℕ} {a : Catalogue X 2} {S : State I.right.scheme I.left.scheme}
    (r : ProtectedRepair X a.val S 2 b)
    (hb : b ≤ 2 * Fintype.card (Field I.right.scheme I.left.scheme) + 1)
    (d : Cell (carrier I X T hA hB hC)) :
    min (r.decoder (source I X T hA hB hC (repairAnchor r) d)) (grid 2 b) =
      min (source I X T hA hB hC a d) (grid 2 b) := by
  exact OrbitPrefixSupport.decode_agree r.witness (grid_visible 2 b)
    (by rw [gTop_of_le le_rfl]; exact le_top) r.reaches
    (fun _ hz hlt => grid_fixed_below r hz hlt) r.boundary_fixed
    (source_supported I X T hA hB hC a)
    (source_prefix I X T hA hB hC (repairAnchor r) a
      (PairedSlotComparison.sourceGrid_endpoint hb) r.prefix_eq) d

theorem protected_lawful {b : ℕ} {a : Catalogue X 2} {S : State I.right.scheme I.left.scheme}
    (r : ProtectedRepair X a.val S 2 b)
    (hb : b ≤ 2 * Fintype.card (Field I.right.scheme I.left.scheme) + 1) :
    RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2)
      (fun d => r.decoder (source I X T hA hB hC (repairAnchor r) d.1)) := by
  exact (OrbitPrefixSupport.decode_respects_of_positive_cut r.witness
    (source_lawful I X T hA hB hC a) (source_lawful I X T hA hB hC (repairAnchor r))
    (fun d => d.2.2) (grid_visible 2 b) (ofOrd_ne_bot _) r.reaches
    (fun _ hz hlt => grid_fixed_below r hz hlt) r.boundary_fixed
    (fun d => source_supported I X T hA hB hC a d.1)
    (fun d => source_prefix I X T hA hB hC (repairAnchor r) a
      (PairedSlotComparison.sourceGrid_endpoint hb) r.prefix_eq d.1)).1

theorem original_decode {b : ℕ} {a : Catalogue X 2} {S : State I.right.scheme I.left.scheme}
    (r : ProtectedRepair X a.val S 2 b) (d : Cell I.boundary) :
    r.decoder (source I X T hA hB hC (repairAnchor r) (original I X T hA hB hC d)) =
      S.profile (field I d) := by
  rw [original_readback]
  exact r.readback _

/-- Physical private occurrences in the grade-two target. -/
def privateAt (d : I.right.scheme.below (Finset.univ, 2)) :
    (carrier I X T hA hB hC).below (A, 2) :=
  ⟨original I X T hA hB hC (I.rightFace.map d.1), by
    rw [original_index]
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    have hg := congrArg Prod.snd (I.rightFace.index d.1)
    change I.boundary.grade (I.rightFace.map d.1) = I.right.scheme.grade d.1 at hg
    exact hg.le.trans d.2.2⟩

/-- Physical donor occurrences in the same target. -/
def donorAt (d : I.left.scheme.below (Finset.univ, 2)) :
    (carrier I X T hA hB hC).below (A, 2) :=
  ⟨original I X T hA hB hC (I.leftFace.map d.1), by
    rw [original_index]
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    have hg := congrArg Prod.snd (I.leftFace.index d.1)
    change I.boundary.grade (I.leftFace.map d.1) = I.left.scheme.grade d.1 at hg
    exact hg.le.trans d.2.2⟩

theorem private_source_repair {b : ℕ} {S : State I.right.scheme I.left.scheme}
    (hS : Admitted X 2 S)
    (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.right.scheme I.left.scheme) 2)
    (hb : b ≤ 2 * Fintype.card (Field I.right.scheme I.left.scheme) + 1)
    {v : I.right.scheme.below (Finset.univ, 2) → ExtOrd}
    (hv : RespectsSemanticsBelow I.right.rows (Finset.univ, 2) v)
    (hag : ∀ d, min (v d) (grid 2 b) = min (S.privateValues d.1) (grid 2 b)) :
    ∃ w, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) w ∧
      (∀ d, w (privateAt I X T hA hB hC d) = v d) ∧
      ∀ d, min (w d) (grid 2 b) =
        min (source I X T hA hB hC ⟨S.profile, hc, S, hS, rfl⟩ d.1) (grid 2 b) := by
  obtain ⟨S', hS', he, _, _, _, ⟨r⟩⟩ := T.private_protected_all (by decide) hS hc hv hag
  refine ⟨_, protected_lawful I X T hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb, ?_,
    fun d => protected_caps I X T hA hB hC
      (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb d.1⟩
  intro d
  change r.decoder (source I X T hA hB hC (repairAnchor r)
    (original I X T hA hB hC (I.rightFace.map d.1))) = v d
  exact (original_decode I X T hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r (I.rightFace.map d.1)).trans
    ((field_private I X T hS' d.1).trans
        (he d))

theorem donor_source_repair (hN : 2 < X.req.N) {b : ℕ} {S : State I.right.scheme I.left.scheme}
    (hS : Admitted X 2 S)
    (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.right.scheme I.left.scheme) 2)
    (hb : b ≤ 2 * Fintype.card (Field I.right.scheme I.left.scheme) + 1)
    {u : I.left.scheme.below (Finset.univ, 2) → ExtOrd}
    (hu : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) u)
    (hag : ∀ d, min (u d) (grid 2 b) = min (S.donorValues d.1) (grid 2 b)) :
    ∃ w, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) w ∧
      (∀ d, w (donorAt I X T hA hB hC d) = u d) ∧
      ∀ d, min (w d) (grid 2 b) =
        min (source I X T hA hB hC ⟨S.profile, hc, S, hS, rfl⟩ d.1) (grid 2 b) := by
  obtain ⟨S', hS', he, _, _, _, ⟨r⟩⟩ := T.donor_protected_before (by decide) hN hS hc hu hag
  refine ⟨_, protected_lawful I X T hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb, ?_,
    fun d => protected_caps I X T hA hB hC
      (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb d.1⟩
  intro d
  change r.decoder (source I X T hA hB hC (repairAnchor r)
    (original I X T hA hB hC (I.leftFace.map d.1))) = u d
  exact (original_decode I X T hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r (I.leftFace.map d.1)).trans
    ((field_donor I S' d.1).trans (he d))

end
end VaughtConjecture.Knight.GrowthPaddedDecode
