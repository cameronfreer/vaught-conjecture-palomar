/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OwnerwiseDecoding
public import VaughtConjecture.Knight.LowOnlyPaddedCharts
public import VaughtConjecture.Knight.LowOnlyDonorOrderedLift

/-! # Independent physical section supply on the padded grade-two carrier

Long inherited ladder rows are handled by their actual rank tables. Only the
new grade-two leaves use short-row composition. No positive-cap transport is
used to obtain bottom supply.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedSupply
open Transform Value ExtOrd CappedDonor LowOnly
open LowOnlyPaddedSuccessor LowOnlyPaddedDecode LowOnlyPaddedCharts
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem decoded_lower (a : F.Anchor 2) {δ : ExtOrd → ExtOrd}
    (hδ : Witness (gTop 2) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow I.rows (A, 2)
      (fun d => δ (a.val (LowOnlyOrderedLadder.field I d.1)))) :
    RespectsSemanticsBelow (input I F hroot hA hB hC).lowerRows (A, 2)
      (fun d => δ ((input I F hroot hA hB hC).predecessor a d.1)) := by
  let J := input I F hroot hA hB hC
  by_cases hz : δ J.ceiling = ⊥
  · have he (d) : δ (J.predecessor a d) = ⊥ :=
      le_bot_iff.mp ((hδ.mono (J.predecessor_bound a d)).trans_eq hz)
    change RespectsSemanticsBelow J.lowerRows (A, 2) (fun d => δ (J.predecessor a d.1))
    simp only [he]
    exact ⟨fun _ => (selfVis_bot _).symm, fun c => by
      simpa only [min_self] using TransformsTo.to_bot (J.lowerRows.E c.1),
      fun _ c _ _ => ⟨c, rfl, le_rfl⟩⟩
  · let f := fun i => δ (LadderScalarRendering.level
      (LadderScalarRendering.values (F.fields 2 a)) J.ceiling i)
    apply RelativeLadderLayer.image_respects I.boundary I.rows J.one
      (LowOnlyOrderedLadder.field I) (F.fields 1) (LowOnlyOrderedLadder.proper I hB hC)
      (baseAnchor F a) f
      (hδ.mono.comp (LadderScalarRendering.level_mono
        (LadderScalarRendering.values_bound (J.bounded a))))
      (by simp only [f, LadderScalarRendering.level_zero, hδ.bot])
    · intro i
      have hv := LadderScalarRendering.level_visible (J.visible a)
        ((J.grid_visible _ J.ceiling_mem).mono (by decide : 1 ≤ 2)) i
      have he := hδ.clause5
        (LadderScalarRendering.level (LadderScalarRendering.values (J.upper a)) J.ceiling i)
        1 (by rw [gTop_of_le (by decide : 1 ≤ 2)]; exact le_top) 1 le_rfl
      change SelfVis 1 (δ _)
      rw [hv] at he
      exact he.symm
    · intro i hi _
      have hp := LadderScalarRendering.level_pos
        (LadderScalarRendering.bot_not_values (F.fields 2 a))
        (LadderScalarRendering.values_bound (J.bounded a))
        (fun h => hz (h ▸ hδ.bot)) hi
      rcases LadderScalarRendering.level_supported
          (LadderScalarRendering.values (F.fields 2 a)) J.ceiling i with he | he | he
      · exact (hp he).elim
      · obtain ⟨_, x, hx⟩ := LadderScalarRendering.mem_values.mp he
        intro h
        have hb := hreflect x ((congrArg δ hx).trans h)
        exact hp (hx.symm.trans hb)
      · exact fun h => hz (he ▸ h)
    · simpa only [f, baseAnchor_ranks, LadderScalarRendering.field_readback,
        Family.fields] using horiginal

/-- Retained proper owners can have grade two or higher. Separation, rather
than a false global predecessor grade bound, identifies their domains. -/
theorem old_respects_iff (c : Cell (input I F hroot hA hB hC).lower)
    (p : (carrier I F hroot hA hB hC).below
      ((carrier I F hroot hA hB hC).cell (old I F hroot hA hB hC c)) → ExtOrd) :
    RespectsSemanticsBelow (rows I F hroot hA hB hC)
      ((carrier I F hroot hA hB hC).cell (old I F hroot hA hB hC c)) p ↔
    RespectsSemanticsBelow (input I F hroot hA hB hC).lowerRows
      ((input I F hroot hA hB hC).lower.cell c)
      (p ∘ SeparatedSourceLayerCarrier.ownerEquiv (input I F hroot hA hB hC).lower
        (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty))
        2 (by decide) hA (input I F hroot hA hB hC).separation c) := by
  let J := input I F hroot hA hB hC
  let e := SeparatedSourceLayerCarrier.ownerEquiv J.lower
    (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty))
    2 (by decide) hA J.separation c
  have hh := respects_iff_of_equiv e
    (fun d => (congrArg Prod.snd (SourceLayerCarrier.cell_toCell
      J.lower _ 2 (by decide) hA (.inl d.1))).symm)
    (fun d y => by simp only [e, CellScheme.scope,
      SeparatedSourceLayerCarrier.ownerEquiv_val, SourceLayerCarrier.cell_toCell,
      SourceLayerCarrier.index])
    (fun b d _ => (inherited_row I F hroot hA hB hC b.1 d).symm) (p ∘ e)
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hh.symm

theorem decoded_lawful (a : F.Anchor 2) {δ : ExtOrd → ExtOrd}
    (hδ : Witness (gTop 2) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow I.rows (A, 2)
      (fun d => δ (a.val (LowOnlyOrderedLadder.field I d.1)))) :
    RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2)
      (fun d => δ (source I F hroot hA hB hC a d.1)) := by
  let J := input I F hroot hA hB hC
  have hs := source_lawful I F hroot hA hB hC a
  have hl := decoded_lower I F hroot hA hB hC a hδ hreflect horiginal
  apply SharpWitnessComposition.map_respects_of_short_or_local hs (fun d => d.2.2) hδ
  intro c
  obtain ⟨x, hx⟩ | ⟨b, hb⟩ := LowOnlyPaddedSuccessor.cell_cases I F hroot hA hB hC c.1
  · right
    have hxc : GradedLe (J.lower.cell x) (A, 2) := by
      simpa only [hx, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using c.2
    have hp : RespectsSemanticsBelow (rows I F hroot hA hB hC)
        ((carrier I F hroot hA hB hC).cell (old I F hroot hA hB hC x))
        (fun d => δ (source I F hroot hA hB hC a d.1)) := by
      apply (old_respects_iff I F hroot hA hB hC x _).mpr
      simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
        LadderWeightedSuccessor.Input.source_old, CellScheme.below.mono] using hl.mono hxc
    rcases c with ⟨c, hc⟩
    dsimp only at hx
    subst c
    exact hp.locality ⟨_, GradedLe.refl _⟩
  · left
    have hgrade : (carrier I F hroot hA hB hC).grade c.1 = 2 := by
      rw [hb]; exact congrArg Prod.snd (leaf_index I F hroot hA hB hC b)
    rw [hgrade, hb]
    intro d
    rw [leaf_row]
    exact source_short I F hroot hA hB hC b d.1

/-- Terminal insertion constructs the finite bottom reflection needed by the
long ladder rows. No global bottom-reflecting decoder is assumed. -/
theorem exists_section {S : State I.left I.right} (hS : F.Admissible 2 S) :
    ∃ w, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) w ∧
      ∀ d : I.boundary.below (A, 2),
        w ⟨original I F hroot hA hB hC d.1, by rw [original_index]; exact d.2⟩ =
          S.profile (LowOnlyOrderedLadder.field I d.1) := by
  obtain ⟨S₀, Q, _, _, hcap, hQeq, hQ, hcanon, δ, hδ, hread⟩ :=
    F.terminal_insertion (by decide : 1 ≤ 2) hS 0
  let a : F.Anchor 2 := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  have hreflect (f) (hf : δ (a.val f) = ⊥) : a.val f = ⊥ := by
    have hSf : S.profile f = ⊥ := (hread f).symm.trans hf
    have he := State.capEq_iff_profile.mp hcap f
    rw [hSf, min_bot_left] at he
    have hS₀ : S₀.profile f = ⊥ :=
      (min_eq_bot.mp he).resolve_right (ofOrd_ne_bot 0)
    change Q.profile f = ⊥
    rw [hQeq, State.profile_normalize]
    exact (PairedSlotEncoding.normalize_bot_iff 2 S₀.profile f).mpr hS₀
  have horiginal : RespectsSemanticsBelow I.rows (A, 2)
      (fun d => δ (a.val (LowOnlyOrderedLadder.field I d.1))) := by
    simpa only [a, hread] using LowOnlyOrderedSources.boundary_lawful_at I F hroot 2 S hS
  refine ⟨_, decoded_lawful I F hroot hA hB hC a hδ hreflect horiginal, ?_⟩
  intro d
  change δ (source I F hroot hA hB hC a (original I F hroot hA hB hC d.1)) = _
  rw [original_readback]
  exact hread _

theorem private_bottom_supply
    {p : I.right.scheme.below (effC n 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (effC n 2) p) :
    ∃ w, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) w ∧
      ∀ d, w (privateAt I F hroot hA hB hC d) = p d := by
  obtain ⟨S, hS, hr, _, _⟩ := F.private_bottom_supply hp
  obtain ⟨w, hw, hread⟩ := exists_section I F hroot hA hB hC hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.rightFace.map d.1)) (A, 2) := by
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    have hg := congrArg Prod.snd (I.rightFace.index d.1)
    exact hg.le.trans (d.2.2.trans (min_le_left _ _))
  exact (hread ⟨_, hd⟩).trans
    ((LowOnlyOrderedLadder.field_private I F hroot
      (LowOnlyRecursiveCoverage.admissible_down F (by decide) (by decide) hS) d.1).trans
      (congrFun hr d))

theorem donor_bottom_supply
    {p : I.left.scheme.below (effC n 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n 2) p) :
    ∃ w, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) w ∧
      ∀ d, w (donorAt I F hroot hA hB hC d) = p d := by
  obtain ⟨S, hS, hr, _, _⟩ := F.donor_bottom_supply hp
  obtain ⟨w, hw, hread⟩ := exists_section I F hroot hA hB hC hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.leftFace.map d.1)) (A, 2) := by
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    have hg := congrArg Prod.snd (I.leftFace.index d.1)
    exact hg.le.trans (d.2.2.trans (min_le_left _ _))
  exact (hread ⟨_, hd⟩).trans
    ((LowOnlyOrderedLadder.field_donor I S d.1).trans (congrFun hr d))

end
end VaughtConjecture.Knight.LowOnlyPaddedSupply
