/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveContract

/-! # Rows of the recursive semantic successor

The predecessor is the actual recursively enlarged lower carrier. Its proved
selected-section operator constructs all new source rows. No future locality
or serving-controller hypothesis is introduced.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveSuccessorRows
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)
abbrev predecessor := CanonicalRecursiveContract.carrier sem n (Nat.le_of_succ_le hA)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))
abbrev Profile := CanonicalRecursiveInventory.Profile sem (n + 4)
abbrev carrier := SourceLayerCarrier.scheme (predecessor sem n hA) (Profile sem n)
  (n + 4) (Nat.succ_pos (n + 3)) hA
abbrev old (d : Cell (predecessor sem n hA)) :=
  SourceLayerCarrier.toCell (predecessor sem n hA) (Profile sem n)
    (n + 4) (Nat.succ_pos (n + 3)) hA (.inl d)
abbrev controller := SourceLayerCarrier.controller (predecessor sem n hA) (Profile sem n)
  (n + 4) (Nat.succ_pos (n + 3)) hA
include hp in
theorem separation (d : Cell (predecessor sem n hA)) :
    ¬ GradedLe (A, (n + 4)) ((predecessor sem n hA).cell d) :=
  CanonicalRecursiveInventory.separated sem hp (n + 3) (Nat.le_of_succ_le hA) d
abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv (predecessor sem n hA)
  (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA (separation sem n hA hp)
abbrev controllerEquiv := SeparatedSourceLayerCarrier.controllerEquiv (predecessor sem n hA)
  (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA (separation sem n hA hp)
abbrev member := (controllerEquiv sem n hA hp).symm
theorem member_controller (q : Profile sem n) :
    member sem n hA hp (controller sem n hA q) = q :=
  (controllerEquiv sem n hA hp).symm_apply_apply q
abbrev grid := sourceGrid (n + 4) (Fintype.card (Cell D))
abbrev ceiling := CanonicalFieldLayer.ceiling (n + 4) (Cell D)

theorem carrier_eq_recursive :
    carrier sem n hA = CanonicalRecursiveInventory.scheme sem (n + 4) hA := rfl

theorem old_eq_recursive (d : Cell (predecessor sem n hA)) :
    old sem n hA d = CanonicalRecursiveInventory.step sem (n + 3) hA d := rfl

theorem profile_lawful (q : Profile sem n) :
    RespectsSemanticsBelow sem (A, (n + 4)) (fun d => q.val d.1) := by
  have hr := (GradeCutBoundary.respects_iff D (n + 4) sem (A, (n + 4)) le_rfl _).mp
    (q.property.1.toBelow (A, (n + 4)))
  convert hr using 1
  funext d
  exact (congrArg q.val (congrArg Subtype.val
    ((GradeCutBoundary.belowEquiv D (n + 4) (A, (n + 4)) le_rfl).apply_symm_apply d))).symm

theorem profile_proper (q : Profile sem n) (d : Cell D) : q.val d ≠ ⊤ := q.property.2.2 d

abbrev selected (q : Profile sem n) := P.sectionOf (by omega : n + 3 ≤ n + 4)
  (profile_lawful sem n q) (profile_proper sem n q)
  (grid (D := D) n) (ceiling (D := D) n)

theorem selected_lawful (q : Profile sem n) :
    RespectsSemanticsBelow P.rows (A, n + 4)
      (fun d => selected sem n hA P q d.1) :=
  P.section_lawful (by omega) (profile_lawful sem n q) (profile_proper sem n q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega : n + 3 ≤ n + 4))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega : n + 3 ≤ n + 4))

theorem selected_bound (q : Profile sem n) (d : Cell (predecessor sem n hA)) :
    selected sem n hA P q d ≤ ceiling (D := D) n :=
  P.section_bound (by omega) (profile_lawful sem n q) (profile_proper sem n q)
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega : n + 3 ≤ n + 4))
    (CanonicalFieldLayer.profile_bound (GradeCutBoundary.rows D (n + 4) sem) (n + 4)
      (Cell D) (GradeCutBoundary.toCell D (n + 4)) q) d

theorem selected_agreement (p q : Profile sem n) {h : ExtOrd}
    (hh : h ∈ grid (D := D) n) (hag : Agree p.val q.val h) :
    Agree (selected sem n hA P p) (selected sem n hA P q) h :=
  P.section_agreement (by omega) (profile_lawful sem n p) (profile_proper sem n p)
    (profile_lawful sem n q) (profile_proper sem n q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega : n + 3 ≤ n + 4))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega : n + 3 ≤ n + 4))
    hh (CanonicalFieldLayer.grid_bound (n + 4) (Cell D) hh) hag

theorem selected_supported (q : Profile sem n) (d : Cell (predecessor sem n hA)) :
    OrbitPrefixSupport.Supported (n + 4) (grid (D := D) n : Set ExtOrd) q.val
      (selected sem n hA P q d) :=
  P.section_supported (by omega) (profile_lawful sem n q) (profile_proper sem n q)
    (by omega) (sourceGrid_endpoint le_rfl) d

def lower (q : Profile sem n) (d : Cell (carrier sem n hA)) : ExtOrd :=
  match SourceLayerCarrier.toOcc (predecessor sem n hA) (Profile sem n)
      (n + 4) (Nat.succ_pos (n + 3)) hA d with
  | .inl x => selected sem n hA P q x
  | .inr _ => ⊥

theorem lower_old (q : Profile sem n) (d : Cell (predecessor sem n hA)) :
    lower sem n hA P q (old sem n hA d) = selected sem n hA P q d := by
  change lower sem n hA P q
    (SourceLayerCarrier.toCell (predecessor sem n hA) (Profile sem n)
      (n + 4) (Nat.succ_pos (n + 3)) hA (.inl d)) = _
  simp only [lower, SourceLayerCarrier.toOcc_toCell]

def data : ScopedSourcePrefixLayer.Data (carrier sem n hA) (n + 4) (Cell D) where
  base := SeparatedSourceLayerCarrier.base (predecessor sem n hA) (Profile sem n) (n + 4)
    (Nat.succ_pos (n + 3)) hA (separation sem n hA hp) P.rows
  separated c hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem n hA)
      (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact separation sem n hA hp x
  grid := grid (D := D) n
  bot_mem := sourceGrid_bot _ _
  ceiling := ceiling (D := D) n
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound (n + 4) (Cell D) hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := (member sem n hA hp c).val
  lower c := lower sem n hA P (member sem n hA hp c)
  lower_bound c d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem n hA)
      (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA d hd
    rw [lower_old]
    exact selected_bound sem n hA P _ x
  lower_lawful c d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem n hA)
      (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff (predecessor sem n hA)
      (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA (separation sem n hA hp) P.rows x _).mpr
    change RespectsSemanticsBelow P.rows _
      (fun d => lower sem n hA P _ (old sem n hA d.1))
    have hx : GradedLe ((predecessor sem n hA).cell x) (A, (n + 4)) :=
      ⟨(predecessor sem n hA).isPlan.subset_of_mem ((predecessor sem n hA).scope_mem_plan x), by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]
          using hg⟩
    simpa only [lower_old, CellScheme.below.mono] using
      (selected_lawful sem n hA P _).mono hx
  grid_agreement p q h hh hag d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem n hA)
      (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA d hd
    simpa only [lower_old] using selected_agreement sem n hA P _ _ hh hag x

abbrev rows := (data sem n hA hp P).rows
abbrev source (q : Profile sem n) := (data sem n hA hp P).profile (controller sem n hA q)
abbrev boundary (d : Cell D) :=
  old sem n hA (CanonicalRecursiveContract.boundary sem n (Nat.le_of_succ_le hA) d)

theorem source_old (q : Profile sem n) (d : Cell (predecessor sem n hA)) :
    source sem n hA hp P q (old sem n hA d) = selected sem n hA P q d := by
  rw [source, ScopedSourcePrefixLayer.Data.profile_old _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ (separation sem n hA hp) d)]
  change lower sem n hA P (member sem n hA hp (controller sem n hA q)) _ = _
  rw [member_controller, lower_old]

theorem source_boundary (q : Profile sem n) (d : Cell D) :
    source sem n hA hp P q (boundary sem n hA d) = q.val d := by
  rw [source_old]
  exact P.section_boundary (by omega) (profile_lawful sem n q) (profile_proper sem n q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega : n + 3 ≤ n + 4))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl))
      (by omega : n + 3 ≤ n + 4)) d

theorem source_supported (q : Profile sem n) (d : Cell (carrier sem n hA)) :
    OrbitPrefixSupport.Supported (n + 4) (grid (D := D) n : Set ExtOrd) q.val
      (source sem n hA hp P q d) := by
  by_cases hd : (carrier sem n hA).cell d = (A, (n + 4))
  · exact Or.inr (Or.inl (by
      change (data sem n hA hp P).profile _ d ∈ _
      rw [show d = (⟨d, hd⟩ : SourcePrefixLayer.Controller _ (n + 4)).1 from rfl,
        ScopedSourcePrefixLayer.Data.profile_new]
      exact cut_mem (sourceGrid_bot _ _) _ _))
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem n hA)
      (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA d hd
    rw [source_old]
    exact selected_supported sem n hA P q x

theorem source_short (q : Profile sem n) (d : Cell (carrier sem n hA)) :
    SharpWitnessComposition.Short (n + 4) (source sem n hA hp P q d) :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short (n + 4) (Cell D) hh)
    (CanonicalFieldLayer.profile_short (GradeCutBoundary.rows D (n + 4) sem) (n + 4)
      (Cell D) (GradeCutBoundary.toCell D (n + 4)) q) (source_supported sem n hA hp P q d)

theorem source_agreement_all (p q : Profile sem n) {h : ExtOrd}
    (hh : h ∈ grid (D := D) n) (hag : Agree p.val q.val h) :
    Agree (source sem n hA hp P p) (source sem n hA hp P q) h := by
  intro d
  by_cases hd : (carrier sem n hA).cell d = (A, (n + 4))
  · have hb : GradedLe ((carrier sem n hA).cell d) (A, (n + 4)) := by
      rw [hd]; exact GradedLe.refl _
    exact (data sem n hA hp P).profile_prefix hh
      (by simpa only [data, member_controller] using hag) ⟨d, hb⟩
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem n hA)
      (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA d hd
    simpa only [source_old] using selected_agreement sem n hA P p q hh hag x

theorem inherited_row (c : Cell (predecessor sem n hA))
    (d : (predecessor sem n hA).below ((predecessor sem n hA).cell c)) :
    (rows sem n hA hp P).E (old sem n hA c) (ownerEquiv sem n hA hp c d) =
      P.rows.E c d := by
  rw [ScopedSourcePrefixLayer.Data.row_old _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ (separation sem n hA hp) c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem source_lawful (q : Profile sem n) :
    RespectsSemanticsBelow (rows sem n hA hp P) (A, (n + 4))
      (fun d => source sem n hA hp P q d.1) :=
  (data sem n hA hp P).profile_respects _

theorem source_agreement (p q : Profile sem n) {h : ExtOrd}
    (hh : h ∈ grid (D := D) n) (hag : Agree p.val q.val h) :
    Agree (fun d : (carrier sem n hA).below (A, (n + 4)) => source sem n hA hp P p d.1)
      (fun d : (carrier sem n hA).below (A, (n + 4)) => source sem n hA hp P q d.1) h := by
  apply (data sem n hA hp P).profile_prefix hh
  change Agree (member sem n hA hp (controller sem n hA p)).val
    (member sem n hA hp (controller sem n hA q)).val h
  simpa only [member_controller] using hag

theorem consistent (hs : sem.IsConsistent) : (rows sem n hA hp P).IsConsistent := by
  apply ScopedSourcePrefixLayer.Data.consistent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem n hA)
    (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff (predecessor sem n hA)
    (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA (separation sem n hA hp) P.rows x _).mpr
  have he : (data sem n hA hp P).base.E (old sem n hA x) ∘ ownerEquiv sem n hA hp x =
      P.rows.E x := by
    funext d
    exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ x d
  rw [he]
  exact P.consistent hs x

end
end VaughtConjecture.Knight.CanonicalRecursiveSuccessorRows
