/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyTerminalSupport
public import VaughtConjecture.Knight.LowOnlyPaddedEndpoints

/-! # Stage-bounded displays on the actual recursive LOW carrier

Supported terminal decoding controls every physical coordinate, not only the
two original faces. Literal top is permitted. Neither higher bountifulness nor
the model's realization of the separator is assumed or asserted here.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedStage
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedInstallation
open LowOnlyPaddedEndpoints
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

/-- Native section supply with support at every installed coordinate. -/
theorem exists_native_supported (t : ℕ) (ht : t + 2 ≤ A.card)
    {S : State I.left I.right} (hS : F.Admissible (t + 2) S) :
    ∃ w, RespectsSemanticsBelow (build I F hroot hA hB hC t ht).rows (A, t + 2) w ∧
      (∀ d : I.boundary.below (A, t + 2),
        w ⟨original I F hroot hA hB hC t ht d.1, by rw [original_index]; exact d.2⟩ =
          S.profile (field I d.1)) ∧
      ∀ d, OrbitPrefixSupport.Supported (t + 2) ({⊤} : Set ExtOrd) S.profile (w d) := by
  obtain ⟨Q, hQ, hcanon, δ, hδ, hread, hreflect, hsupp⟩ :=
    F.exists_supported_decoder (by omega : 1 ≤ t + 2) hS
  let a : F.Anchor (t + 2) := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  have horiginal : RespectsSemanticsBelow I.rows (A, t + 2)
      (fun d => δ (a.val (field I d.1))) := by
    simpa only [a, hread] using LowOnlyOrderedSources.boundary_lawful_at I F hroot (t + 2) S hS
  cases t with
  | zero =>
    refine ⟨_, LowOnlyPaddedSupply.decoded_lawful I F hroot hA hB hC a hδ
      hreflect horiginal, ?_, fun d => hsupp _⟩
    intro d
    change δ (LowOnlyPaddedSuccessor.source I F hroot hA hB hC a
      (LowOnlyPaddedSuccessor.original I F hroot hA hB hC d.1)) = _
    rw [LowOnlyPaddedSuccessor.original_readback]
    exact hread _
  | succ t =>
    let P := build I F hroot hA hB hC t (by omega)
    refine ⟨_, LowOnlyPaddedStepSupply.decoded_lawful P (by omega) ht a hδ
      hreflect horiginal, ?_, fun d => hsupp _⟩
    intro d
    change δ (LowOnlyPaddedStepRows.source P (by omega) ht a
      (LowOnlyPaddedStepDecode.original P ht d.1)) = _
    rw [LowOnlyPaddedStepDecode.source_original]
    exact hread _

/-- Full-height support, with every original label retained literally. -/
theorem exists_whole_supported {S : State I.left I.right} (hS : F.Admissible A.card S) :
    ∃ w : Cell (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier → ExtOrd,
      RespectsSemantics (build I F hroot hA hB hC (A.card - 2) (by omega)).rows w ∧
      (∀ d : Cell I.boundary,
        w (original I F hroot hA hB hC (A.card - 2) (by omega) d) = S.profile (field I d)) ∧
      ∀ d, OrbitPrefixSupport.Supported A.card ({⊤} : Set ExtOrd) S.profile (w d) := by
  have hn : A.card - 2 + 2 = A.card := by omega
  obtain ⟨w, hw, hread, hsupp⟩ := exists_native_supported I F hroot hA hB hC
    (A.card - 2) (by omega) (hn.symm ▸ hS)
  let D := (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier
  have hall (d : Cell D) : GradedLe (D.cell d) (A, A.card - 2 + 2) := by
    have hs := D.isPlan.subset_of_mem (D.scope_mem_plan d)
    exact ⟨hs, ((D.grade_le_card_scope d).trans (Finset.card_le_card hs)).trans_eq hn.symm⟩
  refine ⟨fun d => w ⟨d, hall d⟩, hw.toRespects hall, ?_, ?_⟩
  · intro d
    have hd : GradedLe (I.boundary.cell d) (A, A.card - 2 + 2) := by
      have hs := I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan d)
      exact ⟨hs, ((I.boundary.grade_le_card_scope d).trans
        (Finset.card_le_card hs)).trans_eq hn.symm⟩
    exact hread ⟨d, hd⟩
  · intro d
    simpa only [hn] using hsupp ⟨d, hall d⟩

/-- A whole lawful display bounded by the same limit as the proper original
fields. Auxiliary values cannot escape that limit through unused codes. -/
theorem exists_whole_lt_limit {S : State I.left I.right} (hS : F.Admissible A.card S)
    {l : Ordinal.{0}} (hl : limitPart l = l)
    (hbound : ∀ f, S.profile f ≠ ⊤ → S.profile f < ofOrd l) :
    ∃ w : Cell (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier → ExtOrd,
      RespectsSemantics (build I F hroot hA hB hC (A.card - 2) (by omega)).rows w ∧
      (∀ d, w ((donorFace I F hroot hA hB hC (A.card - 2) (by omega)).map d) = S.u d) ∧
      (∀ d, w ((privateFace I F hroot hA hB hC (A.card - 2) (by omega)).map d) = S.v d) ∧
      ∀ d, w d ≠ ⊤ → w d < ofOrd l := by
  obtain ⟨w, hw, hread, hsupp⟩ := exists_whole_supported I F hroot hA hB hC hS
  refine ⟨w, hw, ?_, ?_, fun d hd =>
    CappedDonor.Ref.supported_top_lt_limit hl hbound (hsupp d) hd⟩
  · intro d
    rw [donorFace, face_map]
    exact (hread (I.leftFace.map d)).trans
      ((field_read I S (I.leftFace.map d)).trans (I.paste_left S.u S.v d))
  · intro d
    rw [privateFace, face_map]
    exact (hread (I.rightFace.map d)).trans
      (field_private I F hroot
        (LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega) hS) d)

end
end VaughtConjecture.Knight.LowOnlyPaddedStage
