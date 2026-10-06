/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthOrderedBase
public import VaughtConjecture.Knight.ReceivingCatalogueRanks

/-! # Independent physical supply on the growth padded base

As in `LowOnlyGradeOneSupply`, terminal insertion retains complete field ranks,
then the actual numerical table is rendered on the installed anchor. Long-row
lawfulness is proved directly, not by positive-cap transport at bottom.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.Growth
open Transform Value ExtOrd CappedDonor.Ref CanonicalPairedInverse
open LadderScalarRendering ReceivingCatalogueRanks
noncomputable section
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

theorem exists_rank_anchor {j : ℕ} (hj : 1 ≤ j) {S : State DA DQ}
    (hs : Admitted X j S) :
    ∃ a : Catalogue X j, ∀ d, fieldRank a.val d = fieldRank S.profile d := by
  let l := S.freshFloor 0
  have hl : limitPart l = l := S.freshFloor_limit 0
  let β : ExtOrd := ofOrd (l + j)
  have hv : SelfVis j β := by
    rw [selfVis_ofOrd_iff]
    have h := finitePart_limitPart_add_nat l j
    rw [hl] at h
    exact h.ge
  have hb : β ≠ ⊥ := ofOrd_ne_bot _
  let S₀ := S.map (fun x => min x β)
  have hs₀ : Admitted X j S₀ :=
    hs.map X (capWitness hv hb) hj (capWitness_reflects_bottom hb)
  have hp : ∀ d, S₀.profile d ≠ ⊤ := by
    intro d
    rw [State.profile_map]
    exact fun h => ofOrd_ne_top _ (min_eq_top.mp h).2
  have hi (d) : collapseBlock l (min (S.profile d) β) = S.profile d :=
    collapseBlock_min (ofOrd_le_ofOrd.mpr le_self_add) (S.profile_lt_freshFloor 0 d)
  have hc := collapseBlock_witness j hl
  have hr (d) : fieldRank S₀.profile d = fieldRank S.profile d := by
    have he : S₀.profile = fun d => min (S.profile d) β := funext (State.profile_map _ S)
    rw [he]
    exact fieldRank_of_leftInverse S.profile (fun _ _ h => min_le_min_right _ h)
      hc.mono (min_bot_left _) hc.bot hi d
  let U := S₀.normalize j
  refine ⟨⟨U.profile, normalize_inventory j hp, U, normalize_admitted X hj hs₀, rfl⟩, ?_⟩
  intro d
  have he : U.profile = PairedSlotEncoding.normalize j S₀.profile :=
    funext (State.profile_normalize j S₀)
  exact (congrArg (fun p => fieldRank p d) he).trans
    ((fieldRank_normalize j S₀.profile hp d).trans (hr d))

end
end VaughtConjecture.Knight.Growth

namespace VaughtConjecture.Knight.GrowthOrderedBase
open Transform Value ExtOrd AmalgamationPlan Growth RelativeLadderLayer
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev scheme := carrier I.boundary hA
  (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)
abbrev semantics := rows I.boundary I.rows hA (field I) (fields I X) (proper I hB hC)

def privateIncl (d : I.right.scheme.below (Finset.univ, 1)) : I.boundary.below (A, 1) :=
  ⟨I.rightFace.map d.1,
    I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
    (congrArg Prod.snd (I.rightFace.index d.1)).le.trans d.2.2⟩

def donorIncl (d : I.left.scheme.below (Finset.univ, 1)) : I.boundary.below (A, 1) :=
  ⟨I.leftFace.map d.1,
    I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
    (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2⟩

def oldAt (d : I.boundary.below (A, 1)) : (scheme I X hA).below (A, 1) :=
  ⟨old I.boundary hA d.1, by rw [old_index]; exact d.2⟩
abbrev privateAt (d : I.right.scheme.below (Finset.univ, 1)) := oldAt I X hA (privateIncl I d)
abbrev donorAt (d : I.left.scheme.below (Finset.univ, 1)) := oldAt I X hA (donorIncl I d)

/-- Even inherited owners above grade one keep their entire original row. -/
theorem inherited_row (c : Cell I.boundary) (d : I.boundary.below (I.boundary.cell c)) :
    (semantics I X hA hB hC).E (old I.boundary hA c)
      (ownerEquiv I.boundary hA (proper I hB hC) c d) = I.rows.E c d :=
  RelativeLadderLayer.inherited_row _ _ _ _ _ _ c d

def renderingAnchor (S : State I.right.scheme I.left.scheme) (hs : Admitted X 1 S) :
    Catalogue X 1 := (exists_rank_anchor X (by decide : 1 ≤ 1) hs).choose

theorem renderingAnchor_rank (S : State I.right.scheme I.left.scheme) (hs : Admitted X 1 S)
    (f : Field I.right.scheme I.left.scheme) :
    LadderScalarRendering.fieldRank (renderingAnchor I X S hs).val f =
      LadderScalarRendering.fieldRank S.profile f :=
  (exists_rank_anchor X (by decide : 1 ≤ 1) hs).choose_spec f

/-- The ceiling-filled complete table, including spare and foreign rungs. -/
def render (S : State I.right.scheme I.left.scheme) (hs : Admitted X 1 S) (β : ExtOrd) :
    Cell (scheme I X hA) → ExtOrd :=
  renderWith I.boundary hA (field I) (fields I X) (renderingAnchor I X S hs) S.profile β

theorem render_old (S : State I.right.scheme I.left.scheme) (hs : Admitted X 1 S)
    (β : ExtOrd) (d : Cell I.boundary) :
    render I X hA S hs β (old I.boundary hA d) = S.profile (field I d) :=
  renderWith_old _ _ _ _ _ _ _ (renderingAnchor_rank I X S hs) d

include T in
theorem render_lawful (S : State I.right.scheme I.left.scheme) (hs : Admitted X 1 S)
    {β : ExtOrd} (hβ : ∀ f, S.profile f ≤ β) (hv : SelfVis 1 β) :
    RespectsSemanticsBelow (semantics I X hA hB hC) (A, 1)
      (fun d => render I X hA S hs β d.1) :=
  renderWith_respects _ _ _ _ _ _ _ _ (renderingAnchor_rank I X S hs)
    hβ hs.visible hv (boundary_lawful I X T hs)

theorem render_bound (S : State I.right.scheme I.left.scheme) (hs : Admitted X 1 S)
    {β : ExtOrd} (hβ : ∀ f, S.profile f ≤ β) (d : Cell (scheme I X hA)) :
    render I X hA S hs β d ≤ β := renderWith_bound _ _ _ _ _ _ hβ d

theorem render_supported (S : State I.right.scheme I.left.scheme) (hs : Admitted X 1 S)
    (β : ExtOrd) (d : Cell (scheme I X hA)) :
    render I X hA S hs β d = ⊥ ∨
      (∃ f, render I X hA S hs β d = S.profile f) ∨ render I X hA S hs β d = β :=
  renderWith_supported _ _ _ _ _ _ _ d

/-- Agreement is at fixed outer ceiling and every physical coordinate. No
cross-grade exact restriction or upward admission is asserted. -/
theorem render_prefix {S U : State I.right.scheme I.left.scheme}
    (hs : Admitted X 1 S) (hu : Admitted X 1 U) {β γ : ExtOrd}
    (hS : ∀ f, S.profile f ≤ β) (hU : ∀ f, U.profile f ≤ β) (hγ : γ ≤ β)
    (hag : ∀ f, min (S.profile f) γ = min (U.profile f) γ)
    (d : Cell (scheme I X hA)) :
    min (render I X hA S hs β d) γ = min (render I X hA U hu β d) γ :=
  renderWith_agreement _ _ _ _ (renderingAnchor_rank I X S hs)
    (renderingAnchor_rank I X U hu) hS hU hγ hag d

include T in
theorem exists_physical_section {S : State I.right.scheme I.left.scheme}
    (hs : Admitted X 1 S) :
    ∃ w : (scheme I X hA).below (A, 1) → ExtOrd,
      RespectsSemanticsBelow (semantics I X hA hB hC) (A, 1) w ∧
      ∀ d : I.boundary.below (A, 1), w (oldAt I X hA d) = S.profile (field I d.1) := by
  obtain ⟨a, ha⟩ := exists_rank_anchor X (by decide : 1 ≤ 1) hs
  refine ⟨fun d => renderWith I.boundary hA (field I) (fields I X) a S.profile ⊤ d.1,
    renderWith_respects I.boundary I.rows hA (field I) (fields I X) (proper I hB hC)
      a S.profile ha (fun _ => le_top) hs.visible (extVisibilityReplace_top 1 1)
      (boundary_lawful I X T hs), ?_⟩
  intro d
  exact renderWith_old I.boundary hA (field I) (fields I X) a S.profile ⊤ ha d.1

include T in
theorem private_bottom_supply {p : I.right.scheme.below (Finset.univ, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 1) p) :
    ∃ w, RespectsSemanticsBelow (semantics I X hA hB hC) (A, 1) w ∧
      ∀ d, w (privateAt I X hA d) = p d := by
  obtain ⟨S, hs, he, _, _, _⟩ := T.private_all (zero_admitted X 1) hp
    (selfVis_bot 1) (fun _ => by simp)
  obtain ⟨w, hw, hr⟩ := exists_physical_section I X T hA hB hC hs
  exact ⟨w, hw, fun d => (hr (privateIncl I d)).trans
    ((field_private I X T hs d.1).trans (he d))⟩

include T in
theorem donor_bottom_supply (hN : 1 < X.req.N)
    {p : I.left.scheme.below (Finset.univ, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 1) p) :
    ∃ w, RespectsSemanticsBelow (semantics I X hA hB hC) (A, 1) w ∧
      ∀ d, w (donorAt I X hA d) = p d := by
  obtain ⟨S, hs, he, _, _, _⟩ := T.donor_before hN (zero_admitted X 1) hp
    (selfVis_bot 1) (fun _ => by simp)
  obtain ⟨w, hw, hr⟩ := exists_physical_section I X T hA hB hC hs
  exact ⟨w, hw, fun d => (hr (donorIncl I d)).trans
    ((field_donor I S d.1).trans (he d))⟩

end
end VaughtConjecture.Knight.GrowthOrderedBase
