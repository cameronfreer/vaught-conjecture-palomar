/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedDecode
public import VaughtConjecture.Knight.LowOnlyGradeOneSupply
public import VaughtConjecture.Knight.PrivateRowFactorization
public import VaughtConjecture.Knight.HighLayerBountiful

/-! # Actual charts and the literal lower domain of the padded successor

No shortness is imposed on inherited rows. The selected native source values
are short at grade two, including their readings at the retained long tips.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedCharts
open Transform Value ExtOrd CappedDonor LowOnly
open LowOnlyPaddedSuccessor LowOnlyPaddedDecode
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem source_short (a : F.Anchor 2) (d : Cell (carrier I F hroot hA hB hC)) :
    SharpWitnessComposition.Short 2 (source I F hroot hA hB hC a d) := by
  rcases source_supported I F hroot hA hB hC a d with hz | hg | ⟨f, i, hi, he⟩
  · exact Or.inl hz
  · rcases Finset.mem_insert.mp hg with hz | hg
    · exact Or.inl hz
    · obtain ⟨b, _, he⟩ := Finset.mem_image.mp hg
      rw [← he]
      exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)
  · rw [he]
    exact PrivateRowFactorization.short_replace
      (CanonicalPairedProfiles.inventory_short _ _ a.property.1 f) le_rfl hi

/-- An arbitrary lawful ambient supplies an actual installed serving leaf.
The chart reads the complete physical vector, not just the original fields. -/
theorem exists_chart
    {q : (carrier I F hroot hA hB hC).below (A, 2) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) q) :
    ∃ a : F.Anchor 2, ∃ σ : ExtOrd → ExtOrd, ∃ M : ExtOrd,
      Witness (gTop 2) σ ∧
      (∀ d, (carrier I F hroot hA hB hC).grade d.1 = 2 → q d ≤ M) ∧
      ∀ d, σ (source I F hroot hA hB hC a d.1) = min (q d) M := by
  obtain ⟨a₀, _⟩ := F.exists_rank_anchor (by decide : 1 ≤ 2) (F.zero_admissible 2)
  obtain ⟨H⟩ := AmbientGradeCharts.exists_chart hq
    ⟨⟨leaf I F hroot hA hB hC a₀, by rw [leaf_index]; exact GradedLe.refl _⟩,
      leaf_index I F hroot hA hB hC a₀⟩
  obtain ⟨x, hx⟩ | ⟨a, ha⟩ := LowOnlyPaddedSuccessor.cell_cases I F hroot hA hB hC H.owner.1
  · have he := H.index
    rw [hx, SourceLayerCarrier.cell_toCell] at he
    exact False.elim ((input I F hroot hA hB hC).separation x
      (he.symm ▸ GradedLe.refl _))
  · refine ⟨a, H.shift, q H.owner, H.witness, H.dominates, ?_⟩
    intro d
    have hr := H.read_capped d d.2.2
    have he : (rows I F hroot hA hB hC).E H.owner.1
        (H.occurrence d d.2.2) = source I F hroot hA hB hC a d.1 := by
      have hr' : ∀ e : (carrier I F hroot hA hB hC).below
          ((carrier I F hroot hA hB hC).cell H.owner.1),
          (rows I F hroot hA hB hC).E H.owner.1 e =
            source I F hroot hA hB hC a e.1 := by
        rw [ha]
        exact leaf_row I F hroot hA hB hC a
      exact hr' _
    rwa [he] at hr

/-- Grade one contains precisely the unchanged padded predecessor. -/
def lowerEquiv : (input I F hroot hA hB hC).lower.below (A, 1) ≃
    (carrier I F hroot hA hB hC).below (A, 1) :=
  HighLayerBountiful.equiv (input I F hroot hA hB hC).lower
    (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty))
    2 (by decide) hA (A, 1) (fun h => by have := h.2; omega)

theorem lower_respects_iff (p : (input I F hroot hA hB hC).lower.below (A, 1) → ExtOrd) :
    RespectsSemanticsBelow (input I F hroot hA hB hC).lowerRows (A, 1) p ↔
      RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 1)
        (p ∘ (lowerEquiv I F hroot hA hB hC).symm) := by
  apply respects_iff_of_equiv (lowerEquiv I F hroot hA hB hC)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell _ _ _ _ _ _ _ d)).symm)
    (fun d e => ?_) (fun b d _ => ?_) p
  · simp only [CellScheme.scope, lowerEquiv, HighLayerBountiful.equiv_cell]
  · exact (inherited_row I F hroot hA hB hC b.1 d).symm

end
end VaughtConjecture.Knight.LowOnlyPaddedCharts
