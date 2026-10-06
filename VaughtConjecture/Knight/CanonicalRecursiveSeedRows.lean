/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveInventory
public import VaughtConjecture.Knight.CanonicalPairLocalSections

/-! # Actual rows for the recursive third catalogue

This is the semantic bridge from the banked seed pair to the recursive
inventory, including retained higher proper owners. New-controller locality,
availability and consistency are constructed from current-domain sections.
No whole-boundary completion or future-owner lawfulness is assumed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveSeedRows
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card) (hp : ∀ d : Cell D, D.scope d ≠ A)
abbrev two_le := (by decide : 2 ≤ 3).trans hA
abbrev predecessor := CanonicalPairLocalSections.carrier sem (two_le hA)
abbrev predecessorRows := CanonicalPairLocalSections.semantics sem (two_le hA) hp
abbrev Profile := CanonicalRecursiveInventory.Profile sem 3
abbrev carrier := SourceLayerCarrier.scheme (predecessor sem hA) (Profile sem) 3 (by decide) hA
abbrev old (d : Cell (predecessor sem hA)) :=
  SourceLayerCarrier.toCell (predecessor sem hA) (Profile sem) 3 (by decide) hA (.inl d)
abbrev controller := SourceLayerCarrier.controller (predecessor sem hA) (Profile sem)
  3 (by decide) hA
include hp in
theorem separation (d : Cell (predecessor sem hA)) :
    ¬ GradedLe (A, 3) ((predecessor sem hA).cell d) :=
  CanonicalRecursiveInventory.separated sem hp 2 (two_le hA) d
abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv (predecessor sem hA)
  (Profile sem) 3 (by decide) hA (separation sem hA hp)
abbrev controllerEquiv := SeparatedSourceLayerCarrier.controllerEquiv (predecessor sem hA)
  (Profile sem) 3 (by decide) hA (separation sem hA hp)
abbrev member := (controllerEquiv sem hA hp).symm
theorem member_controller (q : Profile sem) :
    member sem hA hp (controller sem hA q) = q :=
  (controllerEquiv sem hA hp).symm_apply_apply q
abbrev grid := sourceGrid 3 (Fintype.card (Cell D))
abbrev ceiling := CanonicalFieldLayer.ceiling 3 (Cell D)

theorem carrier_eq_recursive : carrier sem hA = CanonicalRecursiveInventory.scheme sem 3 hA := rfl

theorem old_eq_recursive (d : Cell (predecessor sem hA)) :
    old sem hA d = CanonicalRecursiveInventory.step sem 2 hA d := rfl

theorem profile_lawful (q : Profile sem) :
    RespectsSemanticsBelow sem (A, 3) (fun d => q.val d.1) := by
  have hr := (GradeCutBoundary.respects_iff D 3 sem (A, 3) le_rfl _).mp
    (q.property.1.toBelow (A, 3))
  convert hr using 1
  funext d
  exact (congrArg q.val (congrArg Subtype.val
    ((GradeCutBoundary.belowEquiv D 3 (A, 3) le_rfl).apply_symm_apply d))).symm

theorem profile_proper (q : Profile sem) (d : Cell D) : q.val d ≠ ⊤ := q.property.2.2 d

abbrev selected (q : Profile sem) := CanonicalPairLocalSections.sectionOf sem (two_le hA) hp
  (by decide : 2 ≤ 3) (profile_lawful sem q) (profile_proper sem q)
  (grid (D := D)) (ceiling (D := D))

theorem selected_lawful (q : Profile sem) :
    RespectsSemanticsBelow (predecessorRows sem hA hp) (A, 3)
      (fun d => selected sem hA hp q d.1) :=
  CanonicalPairLocalSections.section_lawful sem (two_le hA) hp (by decide)
    (profile_lawful sem q) (profile_proper sem q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by decide : 2 ≤ 3))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by decide : 2 ≤ 3))

theorem selected_bound (q : Profile sem) (d : Cell (predecessor sem hA)) :
    selected sem hA hp q d ≤ ceiling (D := D) :=
  CanonicalPairLocalSections.section_bound sem (two_le hA) hp (by decide)
    (profile_lawful sem q) (profile_proper sem q)
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by decide : 2 ≤ 3))
    (CanonicalFieldLayer.profile_bound (GradeCutBoundary.rows D 3 sem) 3
      (Cell D) (GradeCutBoundary.toCell D 3) q) d

theorem selected_agreement (p q : Profile sem) {h : ExtOrd}
    (hh : h ∈ grid (D := D)) (hag : Agree p.val q.val h) :
    Agree (selected sem hA hp p) (selected sem hA hp q) h :=
  CanonicalPairLocalSections.section_agreement sem (two_le hA) hp (by decide)
    (profile_lawful sem p) (profile_proper sem p) (profile_lawful sem q) (profile_proper sem q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by decide : 2 ≤ 3))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by decide : 2 ≤ 3))
    hh (CanonicalFieldLayer.grid_bound 3 (Cell D) hh) hag

theorem selected_supported (q : Profile sem) (d : Cell (predecessor sem hA)) :
    OrbitPrefixSupport.Supported 3 (grid (D := D) : Set ExtOrd) q.val
      (selected sem hA hp q d) :=
  CanonicalPairLocalSections.section_supported sem (two_le hA) hp (by decide)
    (profile_lawful sem q) (profile_proper sem q) (by decide)
    (sourceGrid_endpoint le_rfl) d

def lower (q : Profile sem) (d : Cell (carrier sem hA)) : ExtOrd :=
  match SourceLayerCarrier.toOcc (predecessor sem hA) (Profile sem) 3 (by decide) hA d with
  | .inl x => selected sem hA hp q x
  | .inr _ => ⊥

theorem lower_old (q : Profile sem) (d : Cell (predecessor sem hA)) :
    lower sem hA hp q (old sem hA d) = selected sem hA hp q d := by
  change lower sem hA hp q
    (SourceLayerCarrier.toCell (predecessor sem hA) (Profile sem) 3 (by decide) hA (.inl d)) = _
  simp only [lower, SourceLayerCarrier.toOcc_toCell]

def data : ScopedSourcePrefixLayer.Data (carrier sem hA) 3 (Cell D) where
  base := SeparatedSourceLayerCarrier.base (predecessor sem hA) (Profile sem) 3
    (by decide) hA (separation sem hA hp) (predecessorRows sem hA hp)
  separated c hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem hA)
      (Profile sem) 3 (by decide) hA c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact separation sem hA hp x
  grid := grid (D := D)
  bot_mem := sourceGrid_bot _ _
  ceiling := ceiling (D := D)
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound 3 (Cell D) hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := (member sem hA hp c).val
  lower c := lower sem hA hp (member sem hA hp c)
  lower_bound c d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem hA)
      (Profile sem) 3 (by decide) hA d hd
    rw [lower_old]
    exact selected_bound sem hA hp _ x
  lower_lawful c d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem hA)
      (Profile sem) 3 (by decide) hA d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff (predecessor sem hA)
      (Profile sem) 3 (by decide) hA (separation sem hA hp) (predecessorRows sem hA hp) x _).mpr
    change RespectsSemanticsBelow (predecessorRows sem hA hp) _
      (fun d => lower sem hA hp _ (old sem hA d.1))
    have hx : GradedLe ((predecessor sem hA).cell x) (A, 3) :=
      ⟨(predecessor sem hA).isPlan.subset_of_mem ((predecessor sem hA).scope_mem_plan x), by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]
          using hg⟩
    simpa only [lower_old, CellScheme.below.mono] using
      (selected_lawful sem hA hp _).mono hx
  grid_agreement p q h hh hag d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem hA)
      (Profile sem) 3 (by decide) hA d hd
    simpa only [lower_old] using selected_agreement sem hA hp _ _ hh hag x

abbrev rows := (data sem hA hp).rows
abbrev source (q : Profile sem) := (data sem hA hp).profile (controller sem hA q)
abbrev boundary (d : Cell D) := old sem hA (CanonicalPairLocalSections.original sem (two_le hA) d)

theorem source_old (q : Profile sem) (d : Cell (predecessor sem hA)) :
    source sem hA hp q (old sem hA d) = selected sem hA hp q d := by
  rw [source, ScopedSourcePrefixLayer.Data.profile_old _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ (separation sem hA hp) d)]
  change lower sem hA hp (member sem hA hp (controller sem hA q)) _ = _
  rw [member_controller, lower_old]

theorem source_boundary (q : Profile sem) (d : Cell D) :
    source sem hA hp q (boundary sem hA d) = q.val d := by
  rw [source_old]
  exact CanonicalPairLocalSections.section_old sem (two_le hA) hp (by decide)
    (profile_lawful sem q) (profile_proper sem q) d

theorem source_supported (q : Profile sem) (d : Cell (carrier sem hA)) :
    OrbitPrefixSupport.Supported 3 (grid (D := D) : Set ExtOrd) q.val
      (source sem hA hp q d) := by
  by_cases hd : (carrier sem hA).cell d = (A, 3)
  · exact Or.inr (Or.inl (by
      change (data sem hA hp).profile _ d ∈ _
      rw [show d = (⟨d, hd⟩ : SourcePrefixLayer.Controller _ 3).1 from rfl,
        ScopedSourcePrefixLayer.Data.profile_new]
      exact cut_mem (sourceGrid_bot _ _) _ _))
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem hA)
      (Profile sem) 3 (by decide) hA d hd
    rw [source_old]
    exact selected_supported sem hA hp q x

theorem source_short (q : Profile sem) (d : Cell (carrier sem hA)) :
    SharpWitnessComposition.Short 3 (source sem hA hp q d) :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short 3 (Cell D) hh)
    (CanonicalFieldLayer.profile_short (GradeCutBoundary.rows D 3 sem) 3
      (Cell D) (GradeCutBoundary.toCell D 3) q) (source_supported sem hA hp q d)

theorem source_agreement_all (p q : Profile sem) {h : ExtOrd}
    (hh : h ∈ grid (D := D)) (hag : Agree p.val q.val h) :
    Agree (source sem hA hp p) (source sem hA hp q) h := by
  intro d
  by_cases hd : (carrier sem hA).cell d = (A, 3)
  · have hb : GradedLe ((carrier sem hA).cell d) (A, 3) := by
      rw [hd]; exact GradedLe.refl _
    exact (data sem hA hp).profile_prefix hh
      (by simpa only [data, member_controller] using hag) ⟨d, hb⟩
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem hA)
      (Profile sem) 3 (by decide) hA d hd
    simpa only [source_old] using selected_agreement sem hA hp p q hh hag x

theorem inherited_row (c : Cell (predecessor sem hA))
    (d : (predecessor sem hA).below ((predecessor sem hA).cell c)) :
    (rows sem hA hp).E (old sem hA c) (ownerEquiv sem hA hp c d) =
      (predecessorRows sem hA hp).E c d := by
  rw [ScopedSourcePrefixLayer.Data.row_old _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ (separation sem hA hp) c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem source_lawful (q : Profile sem) :
    RespectsSemanticsBelow (rows sem hA hp) (A, 3) (fun d => source sem hA hp q d.1) :=
  (data sem hA hp).profile_respects _

theorem source_agreement (p q : Profile sem) {h : ExtOrd}
    (hh : h ∈ grid (D := D)) (hag : Agree p.val q.val h) :
    Agree (fun d : (carrier sem hA).below (A, 3) => source sem hA hp p d.1)
      (fun d : (carrier sem hA).below (A, 3) => source sem hA hp q d.1) h := by
  apply (data sem hA hp).profile_prefix hh
  change Agree (member sem hA hp (controller sem hA p)).val
    (member sem hA hp (controller sem hA q)).val h
  simpa only [member_controller] using hag

theorem consistent (hs : sem.IsConsistent) : (rows sem hA hp).IsConsistent := by
  apply ScopedSourcePrefixLayer.Data.consistent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem hA)
    (Profile sem) 3 (by decide) hA c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff (predecessor sem hA)
    (Profile sem) 3 (by decide) hA (separation sem hA hp) (predecessorRows sem hA hp) x _).mpr
  have he : (data sem hA hp).base.E (old sem hA x) ∘ ownerEquiv sem hA hp x =
      (predecessorRows sem hA hp).E x := by
    funext d
    exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ x d
  rw [he]
  exact CanonicalPairBoundary.consistent sem 1 2 (by decide)
    (CanonicalPairLocalSections.one_le (two_le hA)) (by decide) (two_le hA) hp (by decide) hs x

end
end VaughtConjecture.Knight.CanonicalRecursiveSeedRows
