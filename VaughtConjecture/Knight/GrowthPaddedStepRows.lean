/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedContract

/-! # A higher installed successor over the actual padded growth predecessor

The predecessor rendering constructs each incoming source. A fresh ceiling
leaf is installed for each member of the next native growth catalogue. Proper
old owners above that grade and the entire padded base retain their rows.
No ambient lifting or upward admission is used.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedStepRows
open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources GrowthPaddedContract
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {attach : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X attach hA hB hC k)

abbrev grid (_P : Layer I X attach hA hB hC k) :=
  sourceGrid (k + 1) (Fintype.card (Field I.right.scheme I.left.scheme))
abbrev ceiling (_P : Layer I X attach hA hB hC k) :=
  CanonicalFieldLayer.ceiling (k + 1) (Field I.right.scheme I.left.scheme)

def selected (a : Catalogue X (k + 1)) : Cell P.carrier → ExtOrd :=
  P.render (Nat.le_succ k) (state X a) (state_admitted X a) (state_proper X a)
    (grid P) (ceiling P)

theorem selected_lawful (a : Catalogue X (k + 1)) :
    RespectsSemanticsBelow P.rows (A, k + 1) (fun d => selected P a d.1) := by
  apply P.lawful (Nat.le_succ k) (state X a) (state_admitted X a) (state_proper X a)
    (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
  intro d
  rw [state_profile]
  exact GrowthHigherSources.anchor_bound X a d

theorem selected_bound (a : Catalogue X (k + 1)) (d : Cell P.carrier) :
    selected P a d ≤ ceiling P := by
  apply P.bound (Nat.le_succ k) (state X a) (state_admitted X a) (state_proper X a)
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
  intro f
  rw [state_profile]
  exact GrowthHigherSources.anchor_bound X a f

theorem selected_supported (a : Catalogue X (k + 1)) (d : Cell P.carrier) :
    OrbitPrefixSupport.Supported (k + 1) (grid P : Set ExtOrd) (fields X (k + 1) a)
      (selected P a d) := by
  simpa only [selected, state_profile] using P.supported (Nat.le_succ k) (state X a)
    (state_admitted X a) (state_proper X a) (Nat.le_succ k)
    (G := grid P) (H := ceiling P) (sourceGrid_endpoint le_rfl) d

theorem selected_agreement (a b : Catalogue X (k + 1)) {h : ExtOrd}
    (hh : h ∈ grid P) (hab : Agree (fields X (k + 1) a) (fields X (k + 1) b) h) :
    Agree (selected P a) (selected P b) h := by
  apply P.agreement (Nat.le_succ k) (state X a) (state X b)
    (state_admitted X a) (state_admitted X b) (state_proper X a) (state_proper X b)
    (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    hh (CanonicalFieldLayer.grid_bound _ _ hh)
  simpa only [state_profile] using hab

variable (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)
abbrev carrier := SourceLayerCarrier.scheme P.carrier (Catalogue X (k + 1))
  (k + 1) (Nat.succ_pos k) hnext
abbrev old (d : Cell P.carrier) := SourceLayerCarrier.toCell P.carrier (Catalogue X (k + 1))
  (k + 1) (Nat.succ_pos k) hnext (.inl d)
abbrev controller := SourceLayerCarrier.controller P.carrier (Catalogue X (k + 1))
  (k + 1) (Nat.succ_pos k) hnext
abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv P.carrier (Catalogue X (k + 1))
  (k + 1) (Nat.succ_pos k) hnext (P.separated I X attach hA hB hC (by omega))
abbrev member := (SeparatedSourceLayerCarrier.controllerEquiv P.carrier (Catalogue X (k + 1))
  (k + 1) (Nat.succ_pos k) hnext (P.separated I X attach hA hB hC (by omega))).symm

theorem member_controller (a : Catalogue X (k + 1)) :
    member P hk hnext (controller P hnext a) = a :=
  (SeparatedSourceLayerCarrier.controllerEquiv P.carrier (Catalogue X (k + 1))
    (k + 1) (Nat.succ_pos k) hnext
    (P.separated I X attach hA hB hC (by omega))).symm_apply_apply a

def lower (a : Catalogue X (k + 1)) (d : Cell (carrier P hnext)) : ExtOrd :=
  match SourceLayerCarrier.toOcc P.carrier (Catalogue X (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d with
  | .inl x => selected P a x
  | .inr _ => ⊥

theorem lower_old (a : Catalogue X (k + 1)) (d : Cell P.carrier) :
    lower P hnext a (old P hnext d) = selected P a d := by
  simp only [lower, old, SourceLayerCarrier.toOcc_toCell]

include hk in
theorem old_not_full (d : Cell P.carrier) :
    (carrier P hnext).cell (old P hnext d) ≠ (A, k + 1) :=
  SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _
    (P.separated I X attach hA hB hC (by omega)) d

def data : ScopedSourcePrefixLayer.Data (carrier P hnext) (k + 1)
    (Field I.right.scheme I.left.scheme) where
  base := SeparatedSourceLayerCarrier.base P.carrier (Catalogue X (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated I X attach hA hB hC (by omega)) P.rows
  separated c hc := by
    obtain ⟨d, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (Catalogue X (k + 1))
      (k + 1) (Nat.succ_pos k) hnext c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact P.separated I X attach hA hB hC (by omega) d
  grid := grid P
  bot_mem := sourceGrid_bot _ _
  ceiling := ceiling P
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound _ _ hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := fields X (k + 1) (member P hk hnext c)
  lower c := lower P hnext (member P hk hnext c)
  lower_bound c d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (Catalogue X (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d hd
    rw [lower_old]
    exact selected_bound P _ x
  lower_lawful c d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (Catalogue X (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff P.carrier (Catalogue X (k + 1))
      (k + 1) (Nat.succ_pos k) hnext (P.separated I X attach hA hB hC (by omega))
      P.rows x _).mpr
    have hx : GradedLe (P.carrier.cell x) (A, k + 1) :=
      ⟨P.carrier.isPlan.subset_of_mem (P.carrier.scope_mem_plan x), by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell,
          SourceLayerCarrier.index] using hg⟩
    simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
      lower_old, CellScheme.below.mono] using (selected_lawful P _).mono hx
  grid_agreement p q h hh hag d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (Catalogue X (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d hd
    simpa only [lower_old] using selected_agreement P _ _ hh hag x

abbrev rows := (data P hk hnext).rows
abbrev source (a : Catalogue X (k + 1)) := (data P hk hnext).profile (controller P hnext a)

theorem source_old (a : Catalogue X (k + 1)) (d : Cell P.carrier) :
    source P hk hnext a (old P hnext d) = selected P a d := by
  rw [source, ScopedSourcePrefixLayer.Data.profile_old _ _ (old_not_full P hk hnext d)]
  change lower P hnext (member P hk hnext (controller P hnext a)) _ = _
  rw [member_controller, lower_old]

theorem source_new (a b : Catalogue X (k + 1)) :
    source P hk hnext a (controller P hnext b).1 =
      cut (grid P) (fields X (k + 1) a) (fields X (k + 1) b) := by
  change (data P hk hnext).profile _ _ = _
  rw [ScopedSourcePrefixLayer.Data.profile_new]
  simp only [data, member_controller]

theorem source_lawful (a : Catalogue X (k + 1)) :
    RespectsSemanticsBelow (rows P hk hnext) (A, k + 1)
      (fun d => source P hk hnext a d.1) := (data P hk hnext).profile_respects _

theorem source_supported (a : Catalogue X (k + 1)) (d : Cell (carrier P hnext)) :
    OrbitPrefixSupport.Supported (k + 1) (grid P : Set ExtOrd) (fields X (k + 1) a)
      (source P hk hnext a d) := by
  by_cases hd : (carrier P hnext).cell d = (A, k + 1)
  · change OrbitPrefixSupport.Supported _ _ _ ((data P hk hnext).profile _ d)
    rw [show d = (⟨d, hd⟩ : SourcePrefixLayer.Controller _ (k + 1)).1 from rfl,
      ScopedSourcePrefixLayer.Data.profile_new]
    exact Or.inr (Or.inl (cut_mem (sourceGrid_bot _ _) _ _))
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (Catalogue X (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d hd
    rw [source_old]
    exact selected_supported P a x

theorem source_short (a : Catalogue X (k + 1)) (d : Cell (carrier P hnext)) :
    Short (k + 1) (source P hk hnext a d) :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short _ _ hh)
    (GrowthHigherSources.anchor_short X a) (source_supported P hk hnext a d)

theorem source_bound (a : Catalogue X (k + 1)) (d : Cell (carrier P hnext)) :
    source P hk hnext a d ≤ ceiling P := by
  by_cases hd : (carrier P hnext).cell d = (A, k + 1)
  · exact (data P hk hnext).profile_bound _ d (congrArg Prod.snd hd).le
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (Catalogue X (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d hd
    rw [source_old]
    exact selected_bound P a x

theorem source_agreement (a b : Catalogue X (k + 1)) {h : ExtOrd}
    (hh : h ∈ grid P) (hab : Agree (fields X (k + 1) a) (fields X (k + 1) b) h) :
    Agree (source P hk hnext a) (source P hk hnext b) h := by
  intro d
  by_cases hd : (carrier P hnext).cell d = (A, k + 1)
  · exact (data P hk hnext).profile_prefix hh
      (by simpa only [data, member_controller] using hab)
      ⟨d, hd.symm ▸ GradedLe.refl _⟩
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (Catalogue X (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d hd
    simpa only [source_old] using selected_agreement P a b hh hab x

theorem inherited_row (c : Cell P.carrier) (d : P.carrier.below (P.carrier.cell c)) :
    (rows P hk hnext).E (old P hnext c) (ownerEquiv P hk hnext c d) = P.rows.E c d := by
  rw [ScopedSourcePrefixLayer.Data.row_old _ (old_not_full P hk hnext c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem old_respects (c : Cell P.carrier) (p : Cell (carrier P hnext) → ExtOrd) :
    RespectsSemanticsBelow (rows P hk hnext) ((carrier P hnext).cell (old P hnext c))
      (fun d => p d.1) ↔
      RespectsSemanticsBelow P.rows (P.carrier.cell c) (fun d => p (old P hnext d.1)) := by
  rw [(data P hk hnext).old_respects_iff (old_not_full P hk hnext c)]
  exact SeparatedSourceLayerCarrier.base_respects_iff P.carrier (Catalogue X (k + 1))
    (k + 1) (Nat.succ_pos k) hnext (P.separated I X attach hA hB hC (by omega)) P.rows c _

theorem consistent : (rows P hk hnext).IsConsistent := by
  apply (data P hk hnext).consistent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (Catalogue X (k + 1))
    (k + 1) (Nat.succ_pos k) hnext c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff P.carrier (Catalogue X (k + 1))
    (k + 1) (Nat.succ_pos k) hnext (P.separated I X attach hA hB hC (by omega)) P.rows x _).mpr
  have he : (data P hk hnext).base.E (old P hnext x) ∘ ownerEquiv P hk hnext x = P.rows.E x :=
    funext (SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ x)
  rw [he]
  exact P.consistent x

end
end VaughtConjecture.Knight.GrowthPaddedStepRows
