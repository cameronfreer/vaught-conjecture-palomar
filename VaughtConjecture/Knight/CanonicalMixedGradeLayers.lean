/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalGradeCutSections
public import VaughtConjecture.Knight.PairedCoupledSections

/-! # Canonical coupled controller rows over the full field inventory

Retained proper owners may have the upper grade. Separation uses their scope,
not an artificial strict grade bound. The lower full-scope controllers and all
proper owners are retained literally; their source readings are constructed by
the grade-cut section operator on the entire enlarged lower carrier.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.CanonicalMixedGradeLayers

open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition
open PairedSlotEncoding PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)

abbrev lowerScheme := CanonicalGradeCutSections.scheme sem j hj hjA
abbrev lowerSem := CanonicalGradeCutSections.rows sem j hj hjA hproper
abbrev lowerOld := CanonicalGradeCutSections.old sem j hj hjA

variable (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
variable (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

include hg hjk in
theorem lower_grade (d : Cell (lowerScheme sem j hj hjA)) :
    (lowerScheme sem j hj hjA).grade d ≤ k := by
  rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
  cases SourceLayerCarrier.toOcc D (CanonicalGradeCutSections.Profiles sem j) j hj hjA d with
  | inl c => exact hg c
  | inr q => exact hjk.le

include hproper hjk in
theorem lower_separated (d : Cell (lowerScheme sem j hj hjA)) :
    ¬ GradedLe (A, k) ((lowerScheme sem j hj hjA).cell d) := by
  rw [SourceLayerCarrier.cell_eq]
  cases SourceLayerCarrier.toOcc D (CanonicalGradeCutSections.Profiles sem j) j hj hjA d with
  | inl c =>
    intro hc
    exact hproper c (Finset.Subset.antisymm
      (D.isPlan.subset_of_mem (D.scope_mem_plan c)) hc.1)
  | inr q => exact fun hc => (not_le_of_gt hjk) hc.2

abbrev upperGrid := sourceGrid k (Fintype.card (Cell D))
abbrev upperCeiling := PairedBoundarySections.ceiling (D := D) k

abbrev lowerSection (q : CanonicalFieldLayer.Profile sem k (Cell D) id) :
    Cell (lowerScheme sem j hj hjA) → ExtOrd :=
  CanonicalGradeCutSections.sectionOf sem j hj hjA hproper q.property.1
    q.property.2.2
    (upperGrid (D := D) k) (upperCeiling (D := D) k)

include hjk in
theorem grid_lower_visible {h : ExtOrd} (hh : h ∈ upperGrid (D := D) k) :
    SelfVis j h := selfVis_mono (sourceGrid_visible hh) hjk.le

include hjk in
theorem lowerSection_lawful (q : CanonicalFieldLayer.Profile sem k (Cell D) id) :
    RespectsSemantics (lowerSem sem j hj hjA hproper)
      (lowerSection sem j hj hjA hproper k q) :=
  CanonicalGradeCutSections.section_lawful sem j hj hjA hproper q.property.1 _
    (fun _ hh => grid_lower_visible j k hjk hh)
    (grid_lower_visible j k hjk (sourceGrid_endpoint le_rfl))

theorem lowerSection_old (q : CanonicalFieldLayer.Profile sem k (Cell D) id) (d : Cell D) :
    lowerSection sem j hj hjA hproper k q (lowerOld sem j hj hjA d) = q.val d :=
  CanonicalGradeCutSections.section_old sem j hj hjA hproper q.property.1 _ d

include hjk in
theorem lowerSection_bound (q : CanonicalFieldLayer.Profile sem k (Cell D) id)
    (d : Cell (lowerScheme sem j hj hjA)) :
    lowerSection sem j hj hjA hproper k q d ≤ upperCeiling (D := D) k :=
  CanonicalGradeCutSections.section_bound sem j hj hjA hproper q.property.1 _
    (grid_lower_visible j k hjk (sourceGrid_endpoint le_rfl))
    (CanonicalFieldLayer.profile_bound sem k (Cell D) id q) d

include hjk in
theorem lowerSection_supported (q : CanonicalFieldLayer.Profile sem k (Cell D) id)
    (d : Cell (lowerScheme sem j hj hjA)) :
    OrbitPrefixSupport.Supported k (upperGrid (D := D) k : Set ExtOrd) q.val
      (lowerSection sem j hj hjA hproper k q d) :=
  CanonicalGradeCutSections.section_supported sem j hj hjA hproper q.property.1 _ hjk.le
    (sourceGrid_endpoint le_rfl) d

include hjk in
theorem lowerSection_short (q : CanonicalFieldLayer.Profile sem k (Cell D) id)
    (d : Cell (lowerScheme sem j hj hjA)) :
    Short k (lowerSection sem j hj hjA hproper k q d) :=
  PairedCoupledSections.supported_short (fun _ hh => PairedBoundarySections.grid_short k hh)
    (CanonicalFieldLayer.profile_short sem k (Cell D) id q)
    (lowerSection_supported sem j hj hjA hproper k hjk q d)

include hjk in
theorem lowerSection_agreement (p q : CanonicalFieldLayer.Profile sem k (Cell D) id)
    {h : ExtOrd} (hh : h ∈ upperGrid (D := D) k) (hag : Agree p.val q.val h) :
    Agree (lowerSection sem j hj hjA hproper k p)
      (lowerSection sem j hj hjA hproper k q) h :=
  CanonicalGradeCutSections.section_agreement sem j hj hjA hproper p.property.1 _ q.property.1 _
    (fun _ hz => grid_lower_visible j k hjk hz)
    (grid_lower_visible j k hjk (sourceGrid_endpoint le_rfl)) hh
    (PairedBoundarySections.grid_bound k hh) hag

abbrev scheme := SourceLayerCarrier.scheme (lowerScheme sem j hj hjA)
  (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA

abbrev oldCell (d : Cell (lowerScheme sem j hj hjA)) : Cell (scheme sem j hj hjA k hk hkA) :=
  SourceLayerCarrier.toCell (lowerScheme sem j hj hjA)
    (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA (.inl d)

abbrev controller (q : CanonicalFieldLayer.Profile sem k (Cell D) id) :=
  SourceLayerCarrier.controller (lowerScheme sem j hj hjA)
    (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA q

def member (c : SourcePrefixLayer.Controller (scheme sem j hj hjA k hk hkA) k) :
    CanonicalFieldLayer.Profile sem k (Cell D) id :=
  (SeparatedSourceLayerCarrier.controllerEquiv (lowerScheme sem j hj hjA)
    (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA
    (lower_separated sem j hj hjA hproper k hjk)).symm c

theorem member_controller (q : CanonicalFieldLayer.Profile sem k (Cell D) id) :
    member sem j hj hjA hproper k hk hkA hjk (controller sem j hj hjA k hk hkA q) = q :=
  (SeparatedSourceLayerCarrier.controllerEquiv (lowerScheme sem j hj hjA)
    (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA
    (lower_separated sem j hj hjA hproper k hjk)).symm_apply_apply q

abbrev ownerEquiv (c : Cell (lowerScheme sem j hj hjA)) :=
  SeparatedSourceLayerCarrier.ownerEquiv (lowerScheme sem j hj hjA)
    (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA
    (lower_separated sem j hj hjA hproper k hjk) c

def lower (q : CanonicalFieldLayer.Profile sem k (Cell D) id)
    (d : Cell (scheme sem j hj hjA k hk hkA)) : ExtOrd :=
  match SourceLayerCarrier.toOcc (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA d with
  | .inl x => lowerSection sem j hj hjA hproper k q x
  | .inr _ => ⊥

theorem lower_old (q : CanonicalFieldLayer.Profile sem k (Cell D) id)
    (d : Cell (lowerScheme sem j hj hjA)) :
    lower sem j hj hjA hproper k hk hkA q (oldCell sem j hj hjA k hk hkA d) =
      lowerSection sem j hj hjA hproper k q d := by
  simp only [lower, oldCell, SourceLayerCarrier.toOcc_toCell]

def data : SourcePrefixLayer.Data (scheme sem j hj hjA k hk hkA) k (Cell D) where
  base := SeparatedSourceLayerCarrier.base (lowerScheme sem j hj hjA)
    (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA
    (lower_separated sem j hj hjA hproper k hjk) (lowerSem sem j hj hjA hproper)
  max_grade d := by
    rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
    cases SourceLayerCarrier.toOcc (lowerScheme sem j hj hjA)
        (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA d with
    | inl x => exact lower_grade sem j hj hjA k hg hjk x
    | inr q => exact le_rfl
  grid := upperGrid (D := D) k
  bot_mem := sourceGrid_bot _ _
  ceiling := upperCeiling (D := D) k
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := PairedBoundarySections.grid_bound k hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := (member sem j hj hjA hproper k hk hkA hjk c).val
  lower c := lower sem j hj hjA hproper k hk hkA
    (member sem j hj hjA hproper k hk hkA hjk c)
  lower_bound c d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA d hd
    rw [lower_old]
    exact lowerSection_bound sem j hj hjA hproper k hjk _ x
  lower_lawful c d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA
      (lower_separated sem j hj hjA hproper k hjk) (lowerSem sem j hj hjA hproper) x _).mpr
    change RespectsSemanticsBelow (lowerSem sem j hj hjA hproper) _ (fun d =>
      lower sem j hj hjA hproper k hk hkA _ (oldCell sem j hj hjA k hk hkA d.1))
    simpa only [lower_old] using
      (lowerSection_lawful sem j hj hjA hproper k hjk _).toBelow _
  grid_agreement p q h hh hag d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA d hd
    simpa only [lower_old] using
      lowerSection_agreement sem j hj hjA hproper k hjk _ _ hh hag x

abbrev rows := (data sem j hj hjA hproper k hg hk hkA hjk).rows
abbrev source (q : CanonicalFieldLayer.Profile sem k (Cell D) id) :=
  (data sem j hj hjA hproper k hg hk hkA hjk).profile (controller sem j hj hjA k hk hkA q)

theorem source_lower (q : CanonicalFieldLayer.Profile sem k (Cell D) id)
    (d : Cell (lowerScheme sem j hj hjA)) :
    source sem j hj hjA hproper k hg hk hkA hjk q (oldCell sem j hj hjA k hk hkA d) =
      lowerSection sem j hj hjA hproper k q d := by
  rw [source, SourcePrefixLayer.Data.profile_old _ _ (SeparatedSourceLayerCarrier.old_not_full
    (lowerScheme sem j hj hjA) (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA
    (lower_separated sem j hj hjA hproper k hjk) d)]
  change lower sem j hj hjA hproper k hk hkA
    (member sem j hj hjA hproper k hk hkA hjk (controller sem j hj hjA k hk hkA q)) _ = _
  rw [member_controller, lower_old]

theorem source_boundary (q : CanonicalFieldLayer.Profile sem k (Cell D) id) (d : Cell D) :
    source sem j hj hjA hproper k hg hk hkA hjk q
      (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA d)) = q.val d := by
  rw [source_lower, lowerSection_old sem j hj hjA hproper k]

theorem inherited_row (c : Cell (lowerScheme sem j hj hjA))
    (d : (lowerScheme sem j hj hjA).below ((lowerScheme sem j hj hjA).cell c)) :
    (rows sem j hj hjA hproper k hg hk hkA hjk).E (oldCell sem j hj hjA k hk hkA c)
      (ownerEquiv sem j hj hjA hproper k hk hkA hjk c d) =
      (lowerSem sem j hj hjA hproper).E c d := by
  rw [SourcePrefixLayer.Data.row_old _ (SeparatedSourceLayerCarrier.old_not_full
    (lowerScheme sem j hj hjA) (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA
    (lower_separated sem j hj hjA hproper k hjk) c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem inherited_order : StrictMono (oldCell sem j hj hjA k hk hkA) :=
  SourceLayerCarrier.old_order _ _ _ _ _

theorem original_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows sem j hj hjA hproper k hg hk hkA hjk).E
      (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA c))
      (ownerEquiv sem j hj hjA hproper k hk hkA hjk (lowerOld sem j hj hjA c)
        (GradeCutLayerCarrier.ownerEquiv D (CanonicalGradeCutSections.Profiles sem j)
          j hj hjA hproper c d)) = sem.E c d := by
  rw [inherited_row]
  exact CanonicalGradeCutSections.old_row sem j hj hjA hproper c d

theorem consistent (hs : sem.IsConsistent) :
    (rows sem j hj hjA hproper k hg hk hkA hjk).IsConsistent := by
  apply SourcePrefixLayer.Data.consistent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
    (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff (lowerScheme sem j hj hjA)
    (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA
    (lower_separated sem j hj hjA hproper k hjk) (lowerSem sem j hj hjA hproper) x _).mpr
  have he : (data sem j hj hjA hproper k hg hk hkA hjk).base.E
      (oldCell sem j hj hjA k hk hkA x) ∘ ownerEquiv sem j hj hjA hproper k hk hkA hjk x =
      (lowerSem sem j hj hjA hproper).E x := by
    funext d
    exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ x d
  rw [he]
  exact CanonicalGradeCutSections.consistent sem j hj hjA hproper hs x

theorem source_agreement (p q : CanonicalFieldLayer.Profile sem k (Cell D) id)
    {h : ExtOrd} (hh : h ∈ upperGrid (D := D) k) (hag : Agree p.val q.val h) :
    Agree (source sem j hj hjA hproper k hg hk hkA hjk p)
      (source sem j hj hjA hproper k hg hk hkA hjk q) h := by
  apply (data sem j hj hjA hproper k hg hk hkA hjk).profile_prefix hh
  change Agree (member sem j hj hjA hproper k hk hkA hjk
      (controller sem j hj hjA k hk hkA p)).val
    (member sem j hj hjA hproper k hk hkA hjk (controller sem j hj hjA k hk hkA q)).val h
  simpa only [member_controller] using hag

theorem source_supported (q : CanonicalFieldLayer.Profile sem k (Cell D) id)
    (d : Cell (scheme sem j hj hjA k hk hkA)) :
    OrbitPrefixSupport.Supported k (upperGrid (D := D) k : Set ExtOrd) q.val
      (source sem j hj hjA hproper k hg hk hkA hjk q d) := by
  by_cases hd : (scheme sem j hj hjA k hk hkA).cell d = (A, k)
  · have he := (data sem j hj hjA hproper k hg hk hkA hjk).profile_new
      (controller sem j hj hjA k hk hkA q) ⟨d, hd⟩
    apply Or.inr
    apply Or.inl
    change (data sem j hj hjA hproper k hg hk hkA hjk).profile
      (controller sem j hj hjA k hk hkA q) d ∈ upperGrid (D := D) k
    rw [he]
    exact cut_mem (sourceGrid_bot _ _) _ _
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA d hd
    rw [source_lower]
    exact lowerSection_supported sem j hj hjA hproper k hjk q x

theorem source_short (q : CanonicalFieldLayer.Profile sem k (Cell D) id)
    (d : Cell (scheme sem j hj hjA k hk hkA)) :
    Short k (source sem j hj hjA hproper k hg hk hkA hjk q d) :=
  PairedCoupledSections.supported_short
    (fun _ hh => PairedBoundarySections.grid_short k hh)
    (CanonicalFieldLayer.profile_short sem k (Cell D) id q)
    (source_supported sem j hj hjA hproper k hg hk hkA hjk q d)


theorem lower_full_short (c : Cell (lowerScheme sem j hj hjA))
    (hc : (lowerScheme sem j hj hjA).scope c = A)
    (d : (lowerScheme sem j hj hjA).below ((lowerScheme sem j hj hjA).cell c)) :
    Short ((lowerScheme sem j hj hjA).grade c)
      ((lowerSem sem j hj hjA hproper).E c d) := by
  have hjc : (lowerScheme sem j hj hjA).grade c ≤ j := by
    have hs := hc
    rw [CellScheme.scope, SourceLayerCarrier.cell_eq] at hs
    rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
    cases he : SourceLayerCarrier.toOcc D (CanonicalGradeCutSections.Profiles sem j) j hj hjA c with
    | inl a =>
      rw [he] at hs
      exact (hproper a hs).elim
    | inr q => exact le_rfl
  obtain ⟨a, rfl⟩ := GradeCutLayerCarrier.exhaustive D
    (CanonicalGradeCutSections.Profiles sem j) j hj hjA c hjc
  obtain ⟨e, rfl⟩ := (GradeCutLayerCarrier.belowEquiv D
    (CanonicalGradeCutSections.Profiles sem j) j hj hjA _ hjc).surjective d
  have he := CanonicalGradeCutSections.lower_row sem j hj hjA hproper a
    ⟨e.1, by simpa only [GradeCutLayerCarrier.embed_cell] using e.2⟩
  have hv := CanonicalFieldLayer.full_source_short
    (CanonicalGradeCutSections.boundaryRows sem j) j
    (Cell D) (GradeCutBoundary.toCell D j) hj hjA
    (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j) a
    (by simpa only [CellScheme.scope, GradeCutLayerCarrier.embed_cell] using hc)
    ⟨e.1, by simpa only [GradeCutLayerCarrier.embed_cell] using e.2⟩
  rw [← he] at hv
  exact (congrArg (fun i => Short i _) (congrArg Prod.snd
    (GradeCutLayerCarrier.embed_cell D (CanonicalGradeCutSections.Profiles sem j)
      j hj hjA a))).mpr hv

theorem lower_proper_respects {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    {r : Cell (lowerScheme sem j hj hjA) → ExtOrd}
    (hread : ∀ d, r (lowerOld sem j hj hjA d) = p d)
    (c : Cell (lowerScheme sem j hj hjA)) (hc : (lowerScheme sem j hj hjA).scope c ≠ A) :
    RespectsSemanticsBelow (lowerSem sem j hj hjA hproper)
      ((lowerScheme sem j hj hjA).cell c) (fun d => r d.1) := by
  have hc' : (lowerScheme sem j hj hjA).cell c ≠ (A, j) :=
    fun he => hc (congrArg Prod.fst he)
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D
    (CanonicalGradeCutSections.Profiles sem j) j hj hjA c hc'
  apply (GradeCutLayerRows.old_respects_iff D (CanonicalGradeCutSections.Profiles sem j) j hj hjA
    hproper sem (CanonicalGradeCutSections.lowerRows sem j hj hjA hproper) x _).mpr
  change RespectsSemanticsBelow sem (D.cell x) (fun d => r (lowerOld sem j hj hjA d.1))
  simpa only [hread] using hp.toBelow (D.cell x)

theorem full_source_short (c : Cell (scheme sem j hj hjA k hk hkA))
    (hc : (scheme sem j hj hjA k hk hkA).scope c = A)
    (d : (scheme sem j hj hjA k hk hkA).below ((scheme sem j hj hjA k hk hkA).cell c)) :
    Short ((scheme sem j hj hjA k hk hkA).grade c)
      ((rows sem j hj hjA hproper k hg hk hkA hjk).E c d) := by
  apply (data sem j hj hjA hproper k hg hk hkA hjk).full_source_short
    (fun _ hh => PairedBoundarySections.grid_short k hh) _ _ c hc d
  · intro q x hx
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA x hx
    change Short k (lower sem j hj hjA hproper k hk hkA _
      (oldCell sem j hj hjA k hk hkA y))
    rw [lower_old]
    exact lowerSection_short sem j hj hjA hproper k hjk _ y
  · intro x hs hx e
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA x hx
    obtain ⟨z, rfl⟩ := (ownerEquiv sem j hj hjA hproper k hk hkA hjk y).surjective e
    have he := SeparatedSourceLayerCarrier.base_old (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA
      (lower_separated sem j hj hjA hproper k hjk) (lowerSem sem j hj hjA hproper) y z
    change (data sem j hj hjA hproper k hg hk hkA hjk).base.E _ _ = _ at he
    rw [he]
    have hi := SourceLayerCarrier.cell_toCell (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA (.inl y)
    change Short ((scheme sem j hj hjA k hk hkA).grade (oldCell sem j hj hjA k hk hkA y)) _
    rw [show (scheme sem j hj hjA k hk hkA).grade (oldCell sem j hj hjA k hk hkA y) =
      (lowerScheme sem j hj hjA).grade y from congrArg Prod.snd hi]
    exact lower_full_short sem j hj hjA hproper y
      ((congrArg Prod.fst hi).symm.trans hs) z

abbrev normalized {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) : CanonicalFieldLayer.Profile sem k (Cell D) id :=
  CanonicalFieldLayer.encode sem k (Cell D) id hg hp ht

variable {G : Finset ExtOrd} {C : ExtOrd}

/-- The new selected section decodes the complete coupled source, including
all retained lower controllers. Lower sections are not supplied as parameters. -/
def sectionOf {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (G : Finset ExtOrd) (C : ExtOrd)
    (d : Cell (scheme sem j hj hjA k hk hkA)) : ExtOrd :=
  PairedSlotDecoder.decode k (values p) G C
    (source sem j hj hjA hproper k hg hk hkA hjk (normalized sem k hg hp ht) d)

theorem section_boundary {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis k z) (hC : SelfVis k C) (d : Cell D) :
    sectionOf sem j hj hjA hproper k hg hk hkA hjk hp ht G C
      (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA d)) = p d := by
  rw [sectionOf, source_boundary]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_lawful {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis k z) (hC : SelfVis k C) :
    RespectsSemantics (rows sem j hj hjA hproper k hg hk hkA hjk)
      (sectionOf sem j hj hjA hproper k hg hk hkA hjk hp ht G C) := by
  apply (data sem j hj hjA hproper k hg hk hkA hjk).decoded_respects
    (controller sem j hj hjA k hk hkA (normalized sem k hg hp ht)) le_rfl
    (PairedSlotDecoder.decode_witness hG hC) _
    (full_source_short sem j hj hjA hproper k hg hk hkA hjk)
  intro c hc
  have hc' : (scheme sem j hj hjA k hk hkA).cell c ≠ (A, k) :=
    fun he => hc (congrArg Prod.fst he)
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
    (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA c hc'
  apply (SeparatedSourceLayerCarrier.base_respects_iff (lowerScheme sem j hj hjA)
    (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA
    (lower_separated sem j hj hjA hproper k hjk) (lowerSem sem j hj hjA hproper) x _).mpr
  change RespectsSemanticsBelow (lowerSem sem j hj hjA hproper) _ (fun d =>
    PairedSlotDecoder.decode k (values p) G C
      (lower sem j hj hjA hproper k hk hkA
        (member sem j hj hjA hproper k hk hkA hjk
          (controller sem j hj hjA k hk hkA (normalized sem k hg hp ht)))
        (oldCell sem j hj hjA k hk hkA d.1)))
  simp only [member_controller, lower_old]
  apply lower_proper_respects sem j hj hjA hproper hp
    (r := fun y => PairedSlotDecoder.decode k (values p) G C
      (lowerSection sem j hj hjA hproper k (normalized sem k hg hp ht) y)) _ x
    (by simpa only [CellScheme.scope, oldCell, SourceLayerCarrier.cell_toCell,
      SourceLayerCarrier.index] using hc)
  intro d
  rw [lowerSection_old sem j hj hjA hproper k]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_bound {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hC : SelfVis k C) (hb : ∀ d, p d ≤ C)
    (d : Cell (scheme sem j hj hjA k hk hkA)) :
    sectionOf sem j hj hjA hproper k hg hk hkA hjk hp ht G C d ≤ C := by
  apply PairedSlotDecoder.decode_le hC
  intro a ha
  obtain ⟨x, hx⟩ := mem_values.mp ha
  simpa only [hx] using hb x

theorem section_supported {K : ℕ} (hkK : k ≤ K) (hCG : C ∈ G)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    (d : Cell (scheme sem j hj hjA k hk hkA)) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
      (sectionOf sem j hj hjA hproper k hg hk hkA hjk hp ht G C d) :=
  PairedSlotDecoder.decode_supported hkK hCG _

theorem section_diagonal {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hC : SelfVis k C) (hb : ∀ d, p d ≤ C) :
    sectionOf sem j hj hjA hproper k hg hk hkA hjk hp ht G C
      (controller sem j hj hjA k hk hkA (normalized sem k hg hp ht)).1 = C := by
  unfold sectionOf source
  rw [SourcePrefixLayer.Data.profile_diagonal]
  exact decode_reserved_ceiling hC hb

theorem section_agreement {p q : Cell D → ExtOrd}
    (hp : RespectsSemantics sem p) (hq : RespectsSemantics sem q)
    (htp : ∀ d, p d ≠ ⊤) (htq : ∀ d, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis k z)
    (hC : SelfVis k C) (hh : h ∈ G)
    (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf sem j hj hjA hproper k hg hk hkA hjk hp htp G C)
      (sectionOf sem j hj hjA hproper k hg hk hkA hjk hq htq G C) h := by
  obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
    largestCommonCut_spec hG hC hC hh hhC hhC htp htq hag
  have hs := source_agreement sem j hj hjA hproper k hg hk hkA hjk
    (normalized sem k hg hp htp) (normalized sem k hg hq htq) heG heAgree
  exact hs.decode (PairedSlotDecoder.decode_witness hG hC).mono
    (PairedSlotDecoder.decode_witness hG hC).mono hpReach hqReach (fun d _ => hcompare _)

/-- The constructed two-layer operator with independent owner grade k and
support grade K. The selected whole section is a conclusion, not an input. -/
theorem exists_supported_section {K : ℕ} (hkK : k ≤ K)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (hG : ∀ z ∈ G, SelfVis K z) (hCG : C ∈ G) (hCt : C ≠ ⊤)
    (hb : ∀ d, p d ≤ C) :
    ∃ r : Cell (scheme sem j hj hjA k hk hkA) → ExtOrd,
      RespectsSemantics (rows sem j hj hjA hproper k hg hk hkA hjk) r ∧
      (∀ d, r (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA d)) = p d) ∧
      (∀ d, r d ≤ C) ∧
      (∀ d, OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (r d)) := by
  have ht : ∀ d, p d ≠ ⊤ := by
    intro d hd
    exact hCt (top_le_iff.mp (hd ▸ hb d))
  have hv : ∀ z ∈ G, SelfVis k z := fun z hz => selfVis_mono (hG z hz) hkK
  exact ⟨sectionOf sem j hj hjA hproper k hg hk hkA hjk hp ht G C,
    section_lawful sem j hj hjA hproper k hg hk hkA hjk hp ht hv (hv C hCG),
    section_boundary sem j hj hjA hproper k hg hk hkA hjk hp ht hv (hv C hCG),
    section_bound sem j hj hjA hproper k hg hk hkA hjk hp ht (hv C hCG) hb,
    section_supported sem j hj hjA hproper k hg hk hkA hjk hkK hCG hp ht⟩

/-- Both coupled sections are constructed. All auxiliary capped values agree,
but no arbitrary lawful ambient on the coupled carrier is quantified here. -/
theorem exists_agreeing_sections {p q : Cell D → ExtOrd}
    (hp : RespectsSemantics sem p) (hq : RespectsSemantics sem q)
    (htp : ∀ d, p d ≠ ⊤) (htq : ∀ d, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis k z)
    (hC : SelfVis k C) (hh : h ∈ G)
    (hhC : h ≤ C) (hag : Agree p q h) :
    ∃ r s : Cell (scheme sem j hj hjA k hk hkA) → ExtOrd,
      RespectsSemantics (rows sem j hj hjA hproper k hg hk hkA hjk) r ∧
      RespectsSemantics (rows sem j hj hjA hproper k hg hk hkA hjk) s ∧
      (∀ d, r (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA d)) = p d) ∧
      (∀ d, s (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA d)) = q d) ∧
      Agree r s h :=
  ⟨sectionOf sem j hj hjA hproper k hg hk hkA hjk hp htp G C,
    sectionOf sem j hj hjA hproper k hg hk hkA hjk hq htq G C,
    section_lawful sem j hj hjA hproper k hg hk hkA hjk hp htp hG hC,
    section_lawful sem j hj hjA hproper k hg hk hkA hjk hq htq hG hC,
    section_boundary sem j hj hjA hproper k hg hk hkA hjk hp htp hG hC,
    section_boundary sem j hj hjA hproper k hg hk hkA hjk hq htq hG hC,
    section_agreement sem j hj hjA hproper k hg hk hkA hjk hp hq htp htq
      hG hC hh hhC hag⟩

end
end VaughtConjecture.Knight.CanonicalMixedGradeLayers
