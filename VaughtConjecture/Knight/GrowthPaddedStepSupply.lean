/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedStepDecode
public import VaughtConjecture.Knight.OwnerwiseDecoding

/-! # Literal-top section supply on the recursive padded growth rows

Terminal insertion supplies finite bottom reflection on the complete field
vector. The exact padded-base table then transports long-row lawfulness;
higher full-scope rows use short-row composition. No positive external cap,
predecessor lift or bountifulness of the new output is assumed.
-/

/- The owner-by-owner argument adapts LowOnlyPaddedStepSupply; all scalar
admission, terminal insertion, and boundary lawfulness are growth results. -/
@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedStepSupply
open Transform Value ExtOrd CappedDonor Growth GrowthOrderedBase
open GrowthPaddedContract GrowthPaddedStepRows GrowthPaddedStepDecode
open GrowthPaddedStepRendering SharpWitnessComposition GrowthHigherSources
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

def birth (a : Catalogue X (k + 1)) : Catalogue X 1 :=
  P.birth (Nat.le_succ k) (state X a) (state_admitted X a) (state_proper X a)

theorem birth_ranks (a : Catalogue X (k + 1)) (d : Field I.right.scheme I.left.scheme) :
    RelativeLadderLayer.ranks (fields X 1) (birth P a) d =
      LadderScalarRendering.fieldRank (fields X (k + 1) a) d := by
  rw [birth, P.birth_ranks, state_profile]

theorem source_base (a : Catalogue X (k + 1)) (d : Cell (base I X T hA hB hC)) :
    source P hk hnext a (baseMap P hnext d) =
      RelativeLadderLayer.renderWith I.boundary (by omega : 0 < A.card)
        (field I) (fields X 1) (birth P a) (fields X (k + 1) a) (ceiling P) d := by
  rw [baseMap, source_old]
  have he := P.render_base (Nat.le_succ k) (state X a) (state_admitted X a)
    (state_proper X a) (G := grid P) (H := ceiling P)
    (fun _ hz => (PairedSlotComparison.sourceGrid_visible hz).mono (Nat.le_succ k))
    ((PairedSlotComparison.sourceGrid_visible
      (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    (fun f => by rw [state_profile]; exact anchor_bound X a f) d
  simpa only [selected, birth, state_profile] using he

theorem decoded_base (a : Catalogue X (k + 1)) {δ : ExtOrd → ExtOrd}
    (hδ : Witness (gTop (k + 1)) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow I.rows (A, k + 1)
      (fun d => δ (a.val (field I d.1)))) :
    RespectsSemanticsBelow (baseRows I X T hA hB hC) (A, k + 1)
      (fun d => δ (source P hk hnext a (baseMap P hnext d.1))) := by
  simp only [source_base]
  by_cases hz : δ (ceiling P) = ⊥
  · have he (d : Cell (base I X T hA hB hC)) :
        δ (RelativeLadderLayer.renderWith I.boundary (by omega) (field I) (fields X 1)
          (birth P a) (fields X (k + 1) a) (ceiling P) d) = ⊥ := by
      rw [← source_base P hk hnext a d]
      exact le_bot_iff.mp ((hδ.mono (source_bound P hk hnext a _)).trans_eq hz)
    simp only [he]
    exact ⟨fun _ => (selfVis_bot _).symm, fun c => by
      simpa only [min_self] using TransformsTo.to_bot ((baseRows I X T hA hB hC).E c.1),
      fun _ c _ _ => ⟨c, rfl, le_rfl⟩⟩
  · let f := fun i => δ (LadderScalarRendering.level
      (LadderScalarRendering.values (fields X (k + 1) a)) (ceiling P) i)
    apply RelativeLadderLayer.image_respects I.boundary I.rows (by omega : 0 < A.card)
      (field I) (fields X 1) (proper I hB hC) (birth P a) f
      (hδ.mono.comp (LadderScalarRendering.level_mono
        (LadderScalarRendering.values_bound (anchor_bound X a))))
      (by simp only [f, LadderScalarRendering.level_zero, hδ.bot])
    · intro i
      have hv := LadderScalarRendering.level_visible (C := ceiling P)
        (anchor_visible_one X a)
        ((PairedSlotComparison.sourceGrid_visible
          (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.succ_pos k)) i
      have he := hδ.clause5
        (LadderScalarRendering.level (LadderScalarRendering.values (fields X (k + 1) a))
          (ceiling P) i) 1
        (by rw [gTop_of_le (Nat.succ_pos k)]; exact le_top) 1 le_rfl
      change SelfVis 1 (δ _)
      rw [hv] at he
      exact he.symm
    · intro i hi _
      have hp := LadderScalarRendering.level_pos
        (LadderScalarRendering.bot_not_values (fields X (k + 1) a))
        (LadderScalarRendering.values_bound (anchor_bound X a))
        (fun h => hz (h ▸ hδ.bot)) hi
      rcases LadderScalarRendering.level_supported
          (LadderScalarRendering.values (fields X (k + 1) a)) (ceiling P) i with he | he | he
      · exact (hp he).elim
      · obtain ⟨_, x, hx⟩ := LadderScalarRendering.mem_values.mp he
        intro h
        have hb := hreflect x ((congrArg δ hx).trans h)
        exact hp (hx.symm.trans hb)
      · exact fun h => hz (he ▸ h)
    · simpa only [f, birth_ranks, LadderScalarRendering.field_readback,
        GrowthHigherSources.fields] using horiginal

theorem decoded_lawful (a : Catalogue X (k + 1)) {δ : ExtOrd → ExtOrd}
    (hδ : Witness (gTop (k + 1)) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow I.rows (A, k + 1)
      (fun d => δ (a.val (field I d.1)))) :
    RespectsSemanticsBelow (rows P hk hnext) (A, k + 1)
      (fun d => δ (source P hk hnext a d.1)) := by
  have hs := source_lawful P hk hnext a
  have hl := decoded_base P hk hnext a hδ hreflect horiginal
  apply map_respects_of_short_or_local hs (fun d => d.2.2) hδ
  intro c
  rcases GrowthPaddedStepRendering.cell_cases P hk hnext c.1 with
    ⟨b, he⟩ | ⟨hscope, hgrade, _⟩
  · right
    have hb : GradedLe ((base I X T hA hB hC).cell b) (A, k + 1) := by
      simpa only [he, base_index] using c.2
    have hr : RespectsSemanticsBelow (rows P hk hnext)
        ((carrier P hnext).cell (baseMap P hnext b))
        (fun d => δ (source P hk hnext a d.1)) :=
      (base_respects P hk hnext b (fun d => δ (source P hk hnext a d))).mpr (hl.mono hb)
    rcases c with ⟨c, hc⟩
    dsimp only at he
    subst c
    exact hr.locality ⟨_, GradedLe.refl _⟩
  · exact Or.inl (higher_short P hk hnext c.1 hscope hgrade)

/-- Independent native physical supply, including literal top. -/
theorem exists_section {S : State I.right.scheme I.left.scheme}
    (hS : Admitted X (k + 1) S) :
    ∃ w, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) w ∧
      ∀ d : I.boundary.below (A, k + 1),
        w ⟨original P hnext d.1, by rw [original_index]; exact d.2⟩ =
          S.profile (GrowthOrderedBase.field I d.1) := by
  obtain ⟨Q, hQ, hcanon, δ, hδ, hread, hreflect, _⟩ :=
    Growth.exists_supported_decoder X (Nat.succ_pos k) hS
  let a : Catalogue X (k + 1) := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  have horiginal : RespectsSemanticsBelow I.rows (A, k + 1)
      (fun d => δ (a.val (GrowthOrderedBase.field I d.1))) := by
    simpa only [a, hread] using boundary_lawful_at I X T hS
  refine ⟨_, decoded_lawful P hk hnext a hδ hreflect horiginal, ?_⟩
  intro d
  change δ (source P hk hnext a (original P hnext d.1)) = _
  rw [source_original]
  exact hread _

/-- Independent bottom-cap private supply, allowing literal top. -/
theorem private_bottom_supply
    {p : I.right.scheme.below (Finset.univ, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, k + 1) p) :
    ∃ w, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) w ∧
      ∀ d, w (privateAt P hnext d) = p d := by
  obtain ⟨S, hS, hr⟩ := T.private_bottom_state hp
  obtain ⟨w, hw, hread⟩ := exists_section P hk hnext hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.rightFace.map d.1)) (A, k + 1) := by
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    exact (congrArg Prod.snd (I.rightFace.index d.1)).le.trans d.2.2
  exact (hread ⟨_, hd⟩).trans
    ((GrowthOrderedBase.field_private I X T hS d.1).trans (hr d))

/-- Donor supply uses the pre-activation donor fibre, independently of any
positive-cap transport or symmetry assertion about growth admission. -/
theorem donor_bottom_supply (hN : k + 1 < X.req.N)
    {p : I.left.scheme.below (Finset.univ, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p) :
    ∃ w, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) w ∧
      ∀ d, w (donorAt P hnext d) = p d := by
  obtain ⟨S, hS, hr⟩ := T.donor_bottom_state hN hp
  obtain ⟨w, hw, hread⟩ := exists_section P hk hnext hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.leftFace.map d.1)) (A, k + 1) := by
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    exact (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2
  exact (hread ⟨_, hd⟩).trans ((GrowthOrderedBase.field_donor I S d.1).trans (hr d))

end
end VaughtConjecture.Knight.GrowthPaddedStepSupply
