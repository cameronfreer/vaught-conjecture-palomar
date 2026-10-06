/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalPairLowerLifting
public import VaughtConjecture.Knight.SourcePrefixAmbient

/-! # An active upper layer retaining proper owners of its own grade

The lower pair is constructed over the grade-two cut and spliced with all old
proper owners. The new upper sources are its supported selected sections, at
one fixed outer grid and ceiling. No arbitrary positive continuation of a
lower physical section is required.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalProperOwnerLayer
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison
open SharpWitnessComposition
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (k : ℕ) (h2k : 2 < k) (hkA : k ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ k)

abbrev two_le := h2k.le.trans hkA
abbrev one_le := (by decide : 1 ≤ 2).trans (two_le k h2k hkA)
abbrev lowerScheme := CanonicalPairBoundary.scheme sem 1 2 (by decide)
  (one_le k h2k hkA) (by decide) (two_le k h2k hkA)
abbrev lowerSem := CanonicalPairBoundary.rows sem 1 2 (by decide)
  (one_le k h2k hkA) (by decide) (two_le k h2k hkA) hp (by decide)
abbrev boundaryCell := CanonicalPairBoundary.old sem 1 2 (by decide)
  (one_le k h2k hkA) (by decide) (two_le k h2k hkA)
abbrev Profile := CanonicalFieldLayer.Profile sem k (Cell D) id
abbrev grid := sourceGrid k (Fintype.card (Cell D))
abbrev ceiling := PairedBoundarySections.ceiling (D := D) k

include hg in
theorem lower_grade (d : Cell (lowerScheme sem k h2k hkA)) :
    (lowerScheme sem k h2k hkA).grade d ≤ k := by
  obtain ⟨x, rfl⟩ := (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
    (one_le k h2k hkA) (by decide) (two_le k h2k hkA)).surjective d
  change (lowerScheme sem k h2k hkA).grade (GradeCutPairCarrier.cell _ _ _ _ _ _ _ _ _ x) ≤ k
  rw [CellScheme.grade, GradeCutPairCarrier.cell_idx]
  rcases x with (c | q) | q
  · exact hg c
  · exact (by decide : 1 ≤ 2).trans h2k.le
  · exact h2k.le

include hp in
theorem separated (d : Cell (lowerScheme sem k h2k hkA)) :
    ¬ GradedLe (A, k) ((lowerScheme sem k h2k hkA).cell d) := by
  obtain ⟨x, rfl⟩ := (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
    (one_le k h2k hkA) (by decide) (two_le k h2k hkA)).surjective d
  change ¬ GradedLe (A, k)
    ((lowerScheme sem k h2k hkA).cell (GradeCutPairCarrier.cell _ _ _ _ _ _ _ _ _ x))
  rw [GradeCutPairCarrier.cell_idx]
  rcases x with (c | q) | q
  · exact fun h => GradeCutLayerRows.proper_scope D hp c h.1
  · exact fun h => (not_le_of_gt ((by decide : 1 < 2).trans h2k)) h.2
  · exact fun h => (not_le_of_gt h2k) h.2

abbrev lowerSection (q : Profile sem k) :=
  CanonicalPairBoundary.sectionOf sem 1 2 (by decide) (one_le k h2k hkA)
    (by decide) (two_le k h2k hkA) hp (by decide) q.property.1 q.property.2.2
    (grid (D := D) k) (ceiling (D := D) k)

theorem lower_lawful (q : Profile sem k) :
    RespectsSemantics (lowerSem sem k h2k hkA hp) (lowerSection sem k h2k hkA hp q) :=
  CanonicalPairBoundary.section_lawful sem 1 2 (by decide) (one_le k h2k hkA)
    (by decide) (two_le k h2k hkA) hp (by decide) q.property.1 q.property.2.2
    (fun _ hh => selfVis_mono (sourceGrid_visible hh) h2k.le)
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) h2k.le)

theorem lower_bound (q : Profile sem k) (d : Cell (lowerScheme sem k h2k hkA)) :
    lowerSection sem k h2k hkA hp q d ≤ ceiling (D := D) k :=
  CanonicalPairBoundary.section_bound sem 1 2 (by decide) (one_le k h2k hkA)
    (by decide) (two_le k h2k hkA) hp (by decide) q.property.1 q.property.2.2
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) h2k.le)
    (CanonicalFieldLayer.profile_bound sem k (Cell D) id q) d

theorem lower_supported (q : Profile sem k) (d : Cell (lowerScheme sem k h2k hkA)) :
    OrbitPrefixSupport.Supported k (grid (D := D) k : Set ExtOrd) q.val
      (lowerSection sem k h2k hkA hp q d) :=
  CanonicalPairBoundary.section_supported sem 1 2 (by decide) (one_le k h2k hkA)
    (by decide) (two_le k h2k hkA) hp (by decide) q.property.1 q.property.2.2
    h2k.le (sourceGrid_endpoint le_rfl) d

theorem lower_agreement (p q : Profile sem k) {h : ExtOrd}
    (hh : h ∈ grid (D := D) k) (hag : Agree p.val q.val h) :
    Agree (lowerSection sem k h2k hkA hp p) (lowerSection sem k h2k hkA hp q) h :=
  CanonicalPairBoundary.section_agreement sem 1 2 (by decide) (one_le k h2k hkA)
    (by decide) (two_le k h2k hkA) hp (by decide) p.property.1 p.property.2.2
    q.property.1 q.property.2.2
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) h2k.le)
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) h2k.le)
    hh (PairedBoundarySections.grid_bound k hh) hag

abbrev positive := (by decide : 0 < 2).trans h2k
abbrev scheme := SourceLayerCarrier.scheme (lowerScheme sem k h2k hkA)
  (Profile sem k) k (positive k h2k) hkA
abbrev old (d : Cell (lowerScheme sem k h2k hkA)) :=
  SourceLayerCarrier.toCell (lowerScheme sem k h2k hkA) (Profile sem k)
    k (positive k h2k) hkA (.inl d)
abbrev controller := SourceLayerCarrier.controller (lowerScheme sem k h2k hkA)
  (Profile sem k) k (positive k h2k) hkA
abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv (lowerScheme sem k h2k hkA)
  (Profile sem k) k (positive k h2k) hkA (separated sem k h2k hkA hp)
abbrev controllerEquiv := SeparatedSourceLayerCarrier.controllerEquiv (lowerScheme sem k h2k hkA)
  (Profile sem k) k (positive k h2k) hkA (separated sem k h2k hkA hp)
abbrev member := (controllerEquiv sem k h2k hkA hp).symm

theorem member_controller (q : Profile sem k) :
    member sem k h2k hkA hp (controller sem k h2k hkA q) = q :=
  (controllerEquiv sem k h2k hkA hp).symm_apply_apply q

def lower (q : Profile sem k) (d : Cell (scheme sem k h2k hkA)) : ExtOrd :=
  match SourceLayerCarrier.toOcc (lowerScheme sem k h2k hkA) (Profile sem k)
      k (positive k h2k) hkA d with
  | .inl x => lowerSection sem k h2k hkA hp q x
  | .inr _ => ⊥

theorem lower_old (q : Profile sem k) (d : Cell (lowerScheme sem k h2k hkA)) :
    lower sem k h2k hkA hp q (old sem k h2k hkA d) = lowerSection sem k h2k hkA hp q d := by
  simp only [lower, old, SourceLayerCarrier.toOcc_toCell]

def data : SourcePrefixLayer.Data (scheme sem k h2k hkA) k (Cell D) where
  base := SeparatedSourceLayerCarrier.base (lowerScheme sem k h2k hkA) (Profile sem k)
    k (positive k h2k) hkA (separated sem k h2k hkA hp) (lowerSem sem k h2k hkA hp)
  max_grade d := by
    rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
    cases SourceLayerCarrier.toOcc (lowerScheme sem k h2k hkA) (Profile sem k)
        k (positive k h2k) hkA d with
    | inl x => exact lower_grade sem k h2k hkA hg x
    | inr q => exact le_rfl
  grid := grid (D := D) k
  bot_mem := sourceGrid_bot _ _
  ceiling := ceiling (D := D) k
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := PairedBoundarySections.grid_bound k hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := (member sem k h2k hkA hp c).val
  lower c := lower sem k h2k hkA hp (member sem k h2k hkA hp c)
  lower_bound c d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem k h2k hkA)
      (Profile sem k) k (positive k h2k) hkA d hd
    rw [lower_old]
    exact lower_bound sem k h2k hkA hp _ x
  lower_lawful c d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem k h2k hkA)
      (Profile sem k) k (positive k h2k) hkA d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff (lowerScheme sem k h2k hkA)
      (Profile sem k) k (positive k h2k) hkA (separated sem k h2k hkA hp)
      (lowerSem sem k h2k hkA hp) x _).mpr
    change RespectsSemanticsBelow (lowerSem sem k h2k hkA hp) _
      (fun d => lower sem k h2k hkA hp _ (old sem k h2k hkA d.1))
    simpa only [lower_old] using (lower_lawful sem k h2k hkA hp _).toBelow _
  grid_agreement p q h hh hag d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem k h2k hkA)
      (Profile sem k) k (positive k h2k) hkA d hd
    simpa only [lower_old] using lower_agreement sem k h2k hkA hp _ _ hh hag x

abbrev rows := (data sem k h2k hkA hp hg).rows
abbrev source (q : Profile sem k) :=
  (data sem k h2k hkA hp hg).profile (controller sem k h2k hkA q)
abbrev boundary (d : Cell D) := old sem k h2k hkA (boundaryCell sem k h2k hkA d)

theorem boundary_index (d : Cell D) :
    (scheme sem k h2k hkA).cell (boundary sem k h2k hkA d) = D.cell d :=
  (SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl _)).trans
    (GradeCutPairCarrier.cell_idx _ _ _ _ _ _ _ _ _ (.inl (.inl d)))

theorem source_lower (q : Profile sem k) (d : Cell (lowerScheme sem k h2k hkA)) :
    source sem k h2k hkA hp hg q (old sem k h2k hkA d) =
      lowerSection sem k h2k hkA hp q d := by
  rw [source, SourcePrefixLayer.Data.profile_old _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ (separated sem k h2k hkA hp) d)]
  change lower sem k h2k hkA hp
    (member sem k h2k hkA hp (controller sem k h2k hkA q)) _ = _
  rw [member_controller, lower_old]

theorem source_boundary (q : Profile sem k) (d : Cell D) :
    source sem k h2k hkA hp hg q (boundary sem k h2k hkA d) = q.val d := by
  rw [source_lower]
  exact CanonicalPairBoundary.section_old sem 1 2 (by decide) (one_le k h2k hkA)
    (by decide) (two_le k h2k hkA) hp (by decide) q.property.1 q.property.2.2 d

theorem inherited_row (c : Cell (lowerScheme sem k h2k hkA))
    (d : (lowerScheme sem k h2k hkA).below ((lowerScheme sem k h2k hkA).cell c)) :
    (rows sem k h2k hkA hp hg).E (old sem k h2k hkA c)
      (ownerEquiv sem k h2k hkA hp c d) = (lowerSem sem k h2k hkA hp).E c d := by
  rw [SourcePrefixLayer.Data.row_old _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ (separated sem k h2k hkA hp) c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem source_lawful (q : Profile sem k) :
    RespectsSemantics (rows sem k h2k hkA hp hg) (source sem k h2k hkA hp hg q) :=
  (data sem k h2k hkA hp hg).profile_respects _

theorem source_agreement (p q : Profile sem k) {h : ExtOrd}
    (hh : h ∈ grid (D := D) k) (hag : Agree p.val q.val h) :
    Agree (source sem k h2k hkA hp hg p) (source sem k h2k hkA hp hg q) h := by
  apply (data sem k h2k hkA hp hg).profile_prefix hh
  change Agree (member sem k h2k hkA hp (controller sem k h2k hkA p)).val
    (member sem k h2k hkA hp (controller sem k h2k hkA q)).val h
  simpa only [member_controller] using hag

theorem source_supported (q : Profile sem k) (d : Cell (scheme sem k h2k hkA)) :
    OrbitPrefixSupport.Supported k (grid (D := D) k : Set ExtOrd) q.val
      (source sem k h2k hkA hp hg q d) := by
  by_cases hd : (scheme sem k h2k hkA).cell d = (A, k)
  · exact Or.inr (Or.inl (by
      change (data sem k h2k hkA hp hg).profile _ d ∈ _
      rw [show d = (⟨d, hd⟩ : SourcePrefixLayer.Controller _ k).1 from rfl,
        SourcePrefixLayer.Data.profile_new]
      exact cut_mem (sourceGrid_bot _ _) _ _))
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem k h2k hkA)
      (Profile sem k) k (positive k h2k) hkA d hd
    rw [source_lower]
    exact lower_supported sem k h2k hkA hp q x

theorem source_short (q : Profile sem k) (d : Cell (scheme sem k h2k hkA)) :
    Short k (source sem k h2k hkA hp hg q d) :=
  PairedCoupledSections.supported_short (fun _ hh => PairedBoundarySections.grid_short k hh)
    (CanonicalFieldLayer.profile_short sem k (Cell D) id q)
    (source_supported sem k h2k hkA hp hg q d)

theorem consistent (hs : sem.IsConsistent) : (rows sem k h2k hkA hp hg).IsConsistent := by
  apply SourcePrefixLayer.Data.consistent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem k h2k hkA)
    (Profile sem k) k (positive k h2k) hkA c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff (lowerScheme sem k h2k hkA)
    (Profile sem k) k (positive k h2k) hkA (separated sem k h2k hkA hp)
    (lowerSem sem k h2k hkA hp) x _).mpr
  have he : (data sem k h2k hkA hp hg).base.E (old sem k h2k hkA x) ∘
      ownerEquiv sem k h2k hkA hp x = (lowerSem sem k h2k hkA hp).E x := by
    funext d
    exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ x d
  rw [he]
  exact CanonicalPairBoundary.consistent sem 1 2 (by decide) (one_le k h2k hkA)
    (by decide) (two_le k h2k hkA) hp (by decide) hs x

end
end VaughtConjecture.Knight.CanonicalProperOwnerLayer
