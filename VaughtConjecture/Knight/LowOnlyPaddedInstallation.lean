/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedIteration
public import VaughtConjecture.Knight.LowOnlyPaddedPairLift
public import VaughtConjecture.Knight.CanonicalCodingSupport

/-! # Coding and literal ordered faces of the recursive padded LOW carrier

Each recursive output retains both original semantic faces, with their actual
ordered occurrences and exhaustive lower domains. Coding is derived from the
canonical fields and supported native grid, not merely from shortness. Under
the two-original scope cover, completeness holds through the installed height.
No bountifulness of higher outputs is claimed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedInstallation
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedStepRows
open AmalgamationPlan CoatomBoundaryExtension
noncomputable section

section Fields
variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

theorem field_coded {j : ℕ} (a : F.Anchor j) (d : Field P C) :
    IsCodedLabel j (F.fields j a d) := by
  rcases mem_codedAlphabet_iff.mp
      (CanonicalPairedProfiles.inventory_coded (Field P C) j a.property.1 d)
      with hb | ⟨b, i, _, hi, he⟩
  · exact Or.inl hb
  · exact Or.inr ⟨b, i, hi, he⟩
end Fields

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem initial_coded : (initial I F hroot hA hB hC).rows.IsCoded := by
  let J := LowOnlyPaddedSuccessor.input I F hroot hA hB hC
  apply CanonicalCodingSupport.layer J.lower
    (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty))
    2 (by decide) hA J.separation J.lowerRows J.rows
    (RelativeLadderLayer.coded I.boundary I.rows (by omega)
      (field I) (F.fields 1) (proper I hB hC) I.coded) J.inherited_row
  rintro ⟨a, v⟩ d
  cases v with
  | some v => exact Empty.elim v
  | none =>
    change IsCodedLabel 2 ((LowOnlyPaddedSuccessor.rows I F hroot hA hB hC).E
      (LowOnlyPaddedSuccessor.leaf I F hroot hA hB hC a) d)
    rw [LowOnlyPaddedSuccessor.leaf_row]
    exact CanonicalCodingSupport.supported
      (fun _ hz => CanonicalCodingSupport.grid _ _ hz) (field_coded F a)
      (LowOnlyPaddedSuccessor.source_supported I F hroot hA hB hC a d.1)

section Successor
variable {I F hroot hA hB hC} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

theorem successor_coded (hc : P.rows.IsCoded) : (successor P hk hnext).rows.IsCoded := by
  apply CanonicalCodingSupport.layer P.carrier (F.Anchor (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated I F hroot hA hB hC (by omega))
    P.rows (rows P hk hnext) hc (inherited_row P hk hnext)
  intro a d
  change IsCodedLabel (k + 1) ((rows P hk hnext).E (controller P hnext a).1 d)
  have he := (data P hk hnext).row_new (controller P hnext a) d
  exact he.symm ▸ CanonicalCodingSupport.supported
    (fun _ hz => CanonicalCodingSupport.grid _ _ hz) (field_coded F a)
    (source_supported P hk hnext a d.1)

def successor_face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows P.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows (successor P hk hnext).rows :=
  SeparatedLayerFace.face P.carrier (F.Anchor (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated I F hroot hA hB hC (by omega))
    P.rows (rows P hk hnext) (inherited_row P hk hnext) G hT

end Successor

theorem build_coded (t : ℕ) (ht : t + 2 ≤ A.card) :
    (build I F hroot hA hB hC t ht).rows.IsCoded := by
  induction t with
  | zero => exact initial_coded I F hroot hA hB hC
  | succ t ih => exact successor_coded _ _ _ (ih (by omega))

def face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    (t : ℕ) → (ht : t + 2 ≤ A.card) →
      ExactSemanticFace oldRows (build I F hroot hA hB hC t ht).rows
  | 0, _ => LowOnlyPaddedFaces.face I F hroot hA hB hC G hT
  | t + 1, ht => successor_face (build I F hroot hA hB hC t (by omega))
      (by omega) ht (face G hT t (by omega)) hT

theorem face_map {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T)
    (t : ℕ) (ht : t + 2 ≤ A.card) (d : Cell E) :
    (face I F hroot hA hB hC G hT t ht).map d =
      (build I F hroot hA hB hC t ht).baseMap
        (RelativeLadderLayer.old I.boundary (by omega) (G.map d)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    exact congrArg (old (build I F hroot hA hB hC t (by omega)) (by omega)) (ih (by omega))

def donorFace (t : ℕ) (ht : t + 2 ≤ A.card) :
    ExactSemanticFace I.leftRows (build I F hroot hA hB hC t ht).rows :=
  face I F hroot hA hB hC I.leftFace hB.not_ge t ht

def privateFace (t : ℕ) (ht : t + 2 ≤ A.card) :
    ExactSemanticFace I.rightRows (build I F hroot hA hB hC t ht).rows :=
  face I F hroot hA hB hC I.rightFace hC.not_ge t ht

theorem donor_order (t : ℕ) (ht : t + 2 ≤ A.card) :
    StrictMono (donorFace I F hroot hA hB hC t ht).map := by
  have he := funext (face_map I F hroot hA hB hC I.leftFace hB.not_ge t ht)
  change StrictMono (face I F hroot hA hB hC I.leftFace hB.not_ge t ht).map
  rw [he]
  exact (build I F hroot hA hB hC t ht).base_mono.comp
    ((SourceLayerCarrier.old_order _ _ _ _ _).comp I.left_order)

theorem private_order (t : ℕ) (ht : t + 2 ≤ A.card) :
    StrictMono (privateFace I F hroot hA hB hC t ht).map := by
  have he := funext (face_map I F hroot hA hB hC I.rightFace hC.not_ge t ht)
  change StrictMono (face I F hroot hA hB hC I.rightFace hC.not_ge t ht).map
  rw [he]
  exact (build I F hroot hA hB hC t ht).base_mono.comp
    ((SourceLayerCarrier.old_order _ _ _ _ _).comp I.right_order)

/-- Every installed full-scope grade has an actual owner, obtained from the
constructed ceiling receipt rather than an assumed completeness contract. -/
theorem full_occupied (t : ℕ) (ht : t + 2 ≤ A.card) (j : ℕ)
    (hj : 1 ≤ j) (hjt : j ≤ t + 2) :
    ∃ d, (build I F hroot hA hB hC t ht).carrier.cell d = (A, j) := by
  obtain ⟨a, _⟩ := F.exists_rank_anchor (show 1 ≤ t + 2 by omega) (F.zero_admissible (t + 2))
  obtain ⟨d, hd, _⟩ := (build I F hroot hA hB hC t ht).ceiling_at le_rfl
    (state F a) (state_admissible F a) (state_proper F a)
    (G := ∅) (H := ⊤) (by simp) (by simp [SelfVis]) (fun _ => le_top) j hj hjt
  exact ⟨d, hd⟩

theorem complete_through (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)
    (t : ℕ) (ht : t + 2 ≤ A.card) {J : Finset ι × ℕ}
    (hJ : J ∈ Plan.gradedPlan R) (hj : J.2 ≤ t + 2) :
    ∃ d, (build I F hroot hA hB hC t ht).carrier.cell d = J := by
  rcases J with ⟨T, j⟩
  by_cases hT : T = A
  · subst T
    exact full_occupied I F hroot hA hB hC t ht j (Plan.mem_gradedPlan.mp hJ).2.1 hj
  · obtain ⟨d, hd⟩ := (I.occupied_iff hJ).mpr (hcover T (Plan.mem_gradedPlan.mp hJ).1 hT)
    refine ⟨(build I F hroot hA hB hC t ht).baseMap
      (RelativeLadderLayer.old I.boundary (by omega) d), ?_⟩
    exact ((build I F hroot hA hB hC t ht).base_index _).trans
      ((RelativeLadderLayer.old_index I.boundary (by omega) d).trans hd)

/-- At the full available height every graded-plan index is occupied. This
packages completeness, not the still separate bountifulness assertion. -/
theorem complete (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C) :
    (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier.IsComplete := by
  intro J hJ
  have hp := build_plan I F hroot hA hB hC (A.card - 2) (by omega)
  have hJ' : J ∈ Plan.gradedPlan R := by rwa [hp] at hJ
  have hg := (Plan.mem_gradedPlan.mp hJ').2.2
  have hs := I.boundary.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hJ').1
  have hc := Finset.card_le_card hs
  exact complete_through I F hroot hA hB hC hcover (A.card - 2) (by omega) hJ' (by omega)

/-- The literal face transport also preserves the original bountiful clauses
for targets contained in either input, at all grades. -/
theorem inherited_lift (t : ℕ) (ht : t + 2 ≤ A.card) {U V : Finset ι × ℕ}
    (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V) (hv : V.1 ⊆ B ∨ V.1 ⊆ C) :
    CappedLift (build I F hroot hA hB hC t ht).rows h := by
  by_cases he : U = V
  · subst V; exact lift_refl
  rcases hv with hb | hc
  · exact (donorFace I F hroot hA hB hC t ht).lift hb
      (I.left_mem hU (h.1.trans hb)) (I.left_mem hV hb) h he
      (PointImageSemantics.bountiful _ _ _ _ I.left.complete I.left.bountiful)
  · exact (privateFace I F hroot hA hB hC t ht).lift hc
      (I.right_mem hU (h.1.trans hc)) (I.right_mem hV hc) h he
      (PointImageSemantics.bountiful _ _ _ _ I.right.complete I.right.bountiful)

end
end VaughtConjecture.Knight.LowOnlyPaddedInstallation
