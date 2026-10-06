/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OwnerwiseDecoding
public import VaughtConjecture.Knight.GrowthPaddedCharts
public import VaughtConjecture.Knight.GrowthGradeOneLift

/-! # Independent physical section supply on the padded grade-two carrier

Long inherited ladder rows are handled by their actual rank tables. Only the
new grade-two leaves use short-row composition. No positive-cap transport is
used to obtain bottom supply. The owner-by-owner argument is adapted from
LowOnlyPaddedSupply and uses the growth terminal decoder and boundary theorem.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedSupply
open Transform Value ExtOrd CappedDonor Growth
open GrowthPaddedSuccessor GrowthPaddedDecode GrowthPaddedCharts
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem decoded_lower (a : Catalogue X 2) {δ : ExtOrd → ExtOrd}
    (hδ : Witness (gTop 2) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow I.rows (A, 2)
      (fun d => δ (a.val (GrowthOrderedBase.field I d.1)))) :
    RespectsSemanticsBelow (input I X T hA hB hC).lowerRows (A, 2)
      (fun d => δ ((input I X T hA hB hC).predecessor a d.1)) := by
  let J := input I X T hA hB hC
  by_cases hz : δ J.ceiling = ⊥
  · have he (d) : δ (J.predecessor a d) = ⊥ :=
      le_bot_iff.mp ((hδ.mono (J.predecessor_bound a d)).trans_eq hz)
    change RespectsSemanticsBelow J.lowerRows (A, 2) (fun d => δ (J.predecessor a d.1))
    simp only [he]
    exact ⟨fun _ => (selfVis_bot _).symm, fun c => by
      simpa only [min_self] using TransformsTo.to_bot (J.lowerRows.E c.1),
      fun _ c _ _ => ⟨c, rfl, le_rfl⟩⟩
  · let f := fun i => δ (LadderScalarRendering.level
      (LadderScalarRendering.values (GrowthHigherSources.fields X 2 a)) J.ceiling i)
    apply RelativeLadderLayer.image_respects I.boundary I.rows J.one
      (GrowthOrderedBase.field I) (GrowthHigherSources.fields X 1)
      (GrowthOrderedBase.proper I hB hC)
      (baseAnchor X a) f
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
        (LadderScalarRendering.bot_not_values (GrowthHigherSources.fields X 2 a))
        (LadderScalarRendering.values_bound (J.bounded a))
        (fun h => hz (h ▸ hδ.bot)) hi
      rcases LadderScalarRendering.level_supported
          (LadderScalarRendering.values (GrowthHigherSources.fields X 2 a))
          J.ceiling i with he | he | he
      · exact (hp he).elim
      · obtain ⟨_, x, hx⟩ := LadderScalarRendering.mem_values.mp he
        intro h
        have hb := hreflect x ((congrArg δ hx).trans h)
        exact hp (hx.symm.trans hb)
      · exact fun h => hz (he ▸ h)
    · simpa only [f, baseAnchor_ranks, LadderScalarRendering.field_readback,
        GrowthHigherSources.fields] using horiginal

/-- Retained proper owners can have grade two or higher. Separation, rather
than a false global predecessor grade bound, identifies their domains. -/
theorem old_respects_iff (c : Cell (input I X T hA hB hC).lower)
    (p : (carrier I X T hA hB hC).below
      ((carrier I X T hA hB hC).cell (old I X T hA hB hC c)) → ExtOrd) :
    RespectsSemanticsBelow (rows I X T hA hB hC)
      ((carrier I X T hA hB hC).cell (old I X T hA hB hC c)) p ↔
    RespectsSemanticsBelow (input I X T hA hB hC).lowerRows
      ((input I X T hA hB hC).lower.cell c)
      (p ∘ SeparatedSourceLayerCarrier.ownerEquiv (input I X T hA hB hC).lower
        (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty))
        2 (by decide) hA (input I X T hA hB hC).separation c) := by
  let J := input I X T hA hB hC
  let e := SeparatedSourceLayerCarrier.ownerEquiv J.lower
    (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty))
    2 (by decide) hA J.separation c
  have hh := respects_iff_of_equiv e
    (fun d => (congrArg Prod.snd (SourceLayerCarrier.cell_toCell
      J.lower _ 2 (by decide) hA (.inl d.1))).symm)
    (fun d y => by simp only [e, CellScheme.scope,
      SeparatedSourceLayerCarrier.ownerEquiv_val, SourceLayerCarrier.cell_toCell,
      SourceLayerCarrier.index])
    (fun b d _ => (inherited_row I X T hA hB hC b.1 d).symm) (p ∘ e)
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hh.symm

theorem decoded_lawful (a : Catalogue X 2) {δ : ExtOrd → ExtOrd}
    (hδ : Witness (gTop 2) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow I.rows (A, 2)
      (fun d => δ (a.val (GrowthOrderedBase.field I d.1)))) :
    RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2)
      (fun d => δ (source I X T hA hB hC a d.1)) := by
  let J := input I X T hA hB hC
  have hs := source_lawful I X T hA hB hC a
  have hl := decoded_lower I X T hA hB hC a hδ hreflect horiginal
  apply SharpWitnessComposition.map_respects_of_short_or_local hs (fun d => d.2.2) hδ
  intro c
  obtain ⟨x, hx⟩ | ⟨b, hb⟩ := GrowthPaddedSuccessor.cell_cases I X T hA hB hC c.1
  · right
    have hxc : GradedLe (J.lower.cell x) (A, 2) := by
      simpa only [hx, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using c.2
    have hp : RespectsSemanticsBelow (rows I X T hA hB hC)
        ((carrier I X T hA hB hC).cell (old I X T hA hB hC x))
        (fun d => δ (source I X T hA hB hC a d.1)) := by
      apply (old_respects_iff I X T hA hB hC x _).mpr
      simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
        LadderWeightedSuccessor.Input.source_old, CellScheme.below.mono] using hl.mono hxc
    rcases c with ⟨c, hc⟩
    dsimp only at hx
    subst c
    exact hp.locality ⟨_, GradedLe.refl _⟩
  · left
    have hgrade : (carrier I X T hA hB hC).grade c.1 = 2 := by
      rw [hb]; exact congrArg Prod.snd (leaf_index I X T hA hB hC b)
    rw [hgrade, hb]
    intro d
    rw [leaf_row]
    exact source_short I X T hA hB hC b d.1


/-- Terminal insertion reflects bottom on every represented field. The long
rungs use the resulting rank table, not short-row composition. -/
theorem exists_section {S : State I.right.scheme I.left.scheme}
    (hS : Admitted X 2 S) :
    ∃ w, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) w ∧
      ∀ d : I.boundary.below (A, 2),
        w ⟨original I X T hA hB hC d.1, by rw [original_index]; exact d.2⟩ =
          S.profile (GrowthOrderedBase.field I d.1) := by
  obtain ⟨Q, hQ, hcanon, δ, hδ, hread, hreflect, _⟩ :=
    Growth.exists_supported_decoder X (by decide : 1 ≤ 2) hS
  let a : Catalogue X 2 := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  have horiginal : RespectsSemanticsBelow I.rows (A, 2)
      (fun d => δ (a.val (GrowthOrderedBase.field I d.1))) := by
    simpa only [a, hread] using GrowthHigherSources.boundary_lawful_at I X T hS
  refine ⟨_, decoded_lawful I X T hA hB hC a hδ hreflect horiginal, ?_⟩
  intro d
  change δ (source I X T hA hB hC a (original I X T hA hB hC d.1)) = _
  rw [original_readback]
  exact hread _

/-- Independent bottom-cap private supply, allowing literal top. -/
theorem private_bottom_supply
    {p : I.right.scheme.below (Finset.univ, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 2) p) :
    ∃ w, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) w ∧
      ∀ d, w (privateAt I X T hA hB hC d) = p d := by
  obtain ⟨S, hS, hr⟩ := T.private_bottom_state hp
  obtain ⟨w, hw, hread⟩ := exists_section I X T hA hB hC hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.rightFace.map d.1)) (A, 2) := by
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    exact (congrArg Prod.snd (I.rightFace.index d.1)).le.trans d.2.2
  exact (hread ⟨_, hd⟩).trans
    ((GrowthOrderedBase.field_private I X T hS d.1).trans (hr d))

/-- Donor supply uses the pre-activation donor fibre, independently of any
positive-cap transport or symmetry assertion about growth admission. -/
theorem donor_bottom_supply (hN : 2 < X.req.N)
    {p : I.left.scheme.below (Finset.univ, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) p) :
    ∃ w, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) w ∧
      ∀ d, w (donorAt I X T hA hB hC d) = p d := by
  obtain ⟨S, hS, hr⟩ := T.donor_bottom_state hN hp
  obtain ⟨w, hw, hread⟩ := exists_section I X T hA hB hC hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.leftFace.map d.1)) (A, 2) := by
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    exact (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2
  exact (hread ⟨_, hd⟩).trans ((GrowthOrderedBase.field_donor I S d.1).trans (hr d))

end
end VaughtConjecture.Knight.GrowthPaddedSupply
