/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PairedBoundarySections

/-! # Coupling paired controller layers on their actual carriers

The upper source family remains indexed by the original proper boundary.
Its readings at every lower controller are constructed by the lower paired
section operator. No lower-section existence, agreement or future locality
hypothesis is supplied. Both original long rows and the lower controller rows
remain literal. This is a two-layer construction, not arbitrary-ambient lifting.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.PairedCoupledSections

open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition
open PairedSlotEncoding PairedSlotComparison

noncomputable section

theorem short_replace {k i : ℕ} {x : ExtOrd} (hx : Short k x) (hi : i ≤ k) :
    Short k (extVisibilityReplace x k i) := by
  rcases hx with rfl | rfl | ⟨a, rfl, ha⟩
  · exact Or.inl (extVisibilityReplace_bot _ _)
  · exact Or.inr (Or.inl (extVisibilityReplace_top _ _))
  · by_cases hk : finitePart a < k
    · rw [extVisibilityReplace_of_finitePart_lt hk]
      exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_limitPart_add_nat]; exact hi⟩)
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hk)]
      exact Or.inr (Or.inr ⟨a, rfl, ha⟩)

theorem supported_short {X : Type*} {k : ℕ} {G : Finset ExtOrd} {p : X → ExtOrd}
    (hG : ∀ z ∈ G, Short k z) (hp : ∀ x, Short k (p x))
    {v : ExtOrd} (hv : OrbitPrefixSupport.Supported k (G : Set ExtOrd) p v) : Short k v := by
  rcases hv with rfl | hv | ⟨d, i, hi, rfl⟩
  · exact Or.inl rfl
  · exact hG _ hv
  · exact short_replace (hp d) hi

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ j)

abbrev lowerScheme := PairedBoundarySections.scheme sem j hj hjA
abbrev lowerSem := PairedBoundarySections.rows sem j hj hjA hproper hg
abbrev lowerOld (d : Cell D) := PairedBoundarySections.old sem j hj hjA d

variable (k : ℕ) (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

include hproper hg hjk in
theorem lower_grade (d : Cell (lowerScheme sem j hj hjA)) :
    (lowerScheme sem j hj hjA).grade d < k :=
  ((PairedBoundarySections.data sem j hj hjA hproper hg).max_grade d).trans_lt hjk

abbrev upperGrid := sourceGrid k (Fintype.card (Cell D))
abbrev upperCeiling := PairedBoundarySections.ceiling (D := D) k

theorem profile_proper (q : PairedBoundarySections.Profile sem k) (d : Cell D) :
    q.val d ≠ ⊤ := by
  intro ht
  exact ofOrd_ne_top _ (top_le_iff.mp (ht ▸ PairedBoundarySections.profile_bound sem k q d))

include hjk in
theorem grid_lower_visible {h : ExtOrd} (hh : h ∈ upperGrid (D := D) k) :
    SelfVis j h := selfVis_mono (sourceGrid_visible hh) hjk.le

abbrev lowerSection (q : PairedBoundarySections.Profile sem k) :
    Cell (lowerScheme sem j hj hjA) → ExtOrd :=
  PairedBoundarySections.sectionOf sem j hj hjA hproper hg q.property.1
    (profile_proper sem k q) (upperGrid (D := D) k) (upperCeiling (D := D) k)

include hjk in
theorem lowerSection_lawful (q : PairedBoundarySections.Profile sem k) :
    RespectsSemantics (lowerSem sem j hj hjA hproper hg)
      (lowerSection sem j hj hjA hproper hg k q) :=
  PairedBoundarySections.section_lawful sem j hj hjA hproper hg q.property.1
    (profile_proper sem k q) (fun _ hh => grid_lower_visible j k hjk hh)
    (grid_lower_visible j k hjk (sourceGrid_endpoint le_rfl))

include hjk in
theorem lowerSection_old (q : PairedBoundarySections.Profile sem k) (d : Cell D) :
    lowerSection sem j hj hjA hproper hg k q (lowerOld sem j hj hjA d) = q.val d :=
  PairedBoundarySections.section_old sem j hj hjA hproper hg q.property.1
    (profile_proper sem k q) (fun _ hh => grid_lower_visible j k hjk hh)
    (grid_lower_visible j k hjk (sourceGrid_endpoint le_rfl)) d

include hjk in
theorem lowerSection_bound (q : PairedBoundarySections.Profile sem k)
    (d : Cell (lowerScheme sem j hj hjA)) :
    lowerSection sem j hj hjA hproper hg k q d ≤ upperCeiling (D := D) k :=
  PairedBoundarySections.section_bound sem j hj hjA hproper hg q.property.1
    (profile_proper sem k q) (grid_lower_visible j k hjk (sourceGrid_endpoint le_rfl))
    (PairedBoundarySections.profile_bound sem k q) d

include hjk in
theorem lowerSection_supported (q : PairedBoundarySections.Profile sem k)
    (d : Cell (lowerScheme sem j hj hjA)) :
    OrbitPrefixSupport.Supported k (upperGrid (D := D) k : Set ExtOrd) q.val
      (lowerSection sem j hj hjA hproper hg k q d) :=
  PairedBoundarySections.section_supported sem j hj hjA hproper hg hjk.le
    (sourceGrid_endpoint le_rfl) q.property.1 (profile_proper sem k q) d

include hjk in
theorem lowerSection_short (q : PairedBoundarySections.Profile sem k)
    (d : Cell (lowerScheme sem j hj hjA)) :
    Short k (lowerSection sem j hj hjA hproper hg k q d) :=
  supported_short (fun _ hh => PairedBoundarySections.grid_short k hh) q.property.2.2
    (lowerSection_supported sem j hj hjA hproper hg k hjk q d)

include hjk in
theorem lowerSection_agreement (p q : PairedBoundarySections.Profile sem k)
    {h : ExtOrd} (hh : h ∈ upperGrid (D := D) k) (hag : Agree p.val q.val h) :
    Agree (lowerSection sem j hj hjA hproper hg k p)
      (lowerSection sem j hj hjA hproper hg k q) h :=
  PairedBoundarySections.section_agreement sem j hj hjA hproper hg p.property.1 q.property.1
    (profile_proper sem k p) (profile_proper sem k q)
    (fun _ hz => grid_lower_visible j k hjk hz)
    (grid_lower_visible j k hjk (sourceGrid_endpoint le_rfl))
    (grid_lower_visible j k hjk (sourceGrid_endpoint le_rfl)) hh
    (PairedBoundarySections.grid_bound k hh) (PairedBoundarySections.grid_bound k hh) hag

abbrev scheme := SourceLayerCarrier.scheme (lowerScheme sem j hj hjA)
  (PairedBoundarySections.Profile sem k) k hk hkA

abbrev oldCell (d : Cell (lowerScheme sem j hj hjA)) : Cell (scheme sem j hj hjA k hk hkA) :=
  SourceLayerCarrier.toCell (lowerScheme sem j hj hjA)
    (PairedBoundarySections.Profile sem k) k hk hkA (.inl d)

abbrev controller (q : PairedBoundarySections.Profile sem k) :=
  SourceLayerCarrier.controller (lowerScheme sem j hj hjA)
    (PairedBoundarySections.Profile sem k) k hk hkA q

def member (c : SourcePrefixLayer.Controller (scheme sem j hj hjA k hk hkA) k) :
    PairedBoundarySections.Profile sem k :=
  (SourceLayerCarrier.controllerEquiv (lowerScheme sem j hj hjA)
    (PairedBoundarySections.Profile sem k) k hk hkA
    (lower_grade sem j hj hjA hproper hg k hjk)).symm c

theorem member_controller (q : PairedBoundarySections.Profile sem k) :
    member sem j hj hjA hproper hg k hk hkA hjk (controller sem j hj hjA k hk hkA q) = q :=
  (SourceLayerCarrier.controllerEquiv (lowerScheme sem j hj hjA)
    (PairedBoundarySections.Profile sem k) k hk hkA
    (lower_grade sem j hj hjA hproper hg k hjk)).symm_apply_apply q

abbrev ownerEquiv (c : Cell (lowerScheme sem j hj hjA)) :=
  SourceLayerCarrier.ownerEquiv (lowerScheme sem j hj hjA)
    (PairedBoundarySections.Profile sem k) k hk hkA
    (lower_grade sem j hj hjA hproper hg k hjk) c

def lower (q : PairedBoundarySections.Profile sem k)
    (d : Cell (scheme sem j hj hjA k hk hkA)) : ExtOrd :=
  match SourceLayerCarrier.toOcc (lowerScheme sem j hj hjA)
      (PairedBoundarySections.Profile sem k) k hk hkA d with
  | .inl x => lowerSection sem j hj hjA hproper hg k q x
  | .inr _ => ⊥

theorem lower_old (q : PairedBoundarySections.Profile sem k)
    (d : Cell (lowerScheme sem j hj hjA)) :
    lower sem j hj hjA hproper hg k hk hkA q (oldCell sem j hj hjA k hk hkA d) =
      lowerSection sem j hj hjA hproper hg k q d := by
  simp only [lower, oldCell, SourceLayerCarrier.toOcc_toCell]

def data : SourcePrefixLayer.Data (scheme sem j hj hjA k hk hkA) k (Cell D) where
  base := SourceLayerCarrier.base (lowerScheme sem j hj hjA)
    (PairedBoundarySections.Profile sem k) k hk hkA
    (lower_grade sem j hj hjA hproper hg k hjk) (lowerSem sem j hj hjA hproper hg)
  max_grade d := by
    rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
    cases SourceLayerCarrier.toOcc (lowerScheme sem j hj hjA)
        (PairedBoundarySections.Profile sem k) k hk hkA d with
    | inl x => exact (lower_grade sem j hj hjA hproper hg k hjk x).le
    | inr q => exact le_rfl
  grid := upperGrid (D := D) k
  bot_mem := sourceGrid_bot _ _
  ceiling := upperCeiling (D := D) k
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := PairedBoundarySections.grid_bound k hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := (member sem j hj hjA hproper hg k hk hkA hjk c).val
  lower c := lower sem j hj hjA hproper hg k hk hkA
    (member sem j hj hjA hproper hg k hk hkA hjk c)
  lower_bound c d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
      (PairedBoundarySections.Profile sem k) k hk hkA d hd
    rw [lower_old]
    exact lowerSection_bound sem j hj hjA hproper hg k hjk _ x
  lower_lawful c d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
      (PairedBoundarySections.Profile sem k) k hk hkA d hd
    apply (SourceLayerCarrier.base_respects_iff (lowerScheme sem j hj hjA)
      (PairedBoundarySections.Profile sem k) k hk hkA
      (lower_grade sem j hj hjA hproper hg k hjk) (lowerSem sem j hj hjA hproper hg) x _).mpr
    change RespectsSemanticsBelow (lowerSem sem j hj hjA hproper hg) _ (fun d =>
      lower sem j hj hjA hproper hg k hk hkA _ (oldCell sem j hj hjA k hk hkA d.1))
    simpa only [lower_old] using
      (lowerSection_lawful sem j hj hjA hproper hg k hjk _).toBelow _
  grid_agreement p q h hh hag d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
      (PairedBoundarySections.Profile sem k) k hk hkA d hd
    simpa only [lower_old] using
      lowerSection_agreement sem j hj hjA hproper hg k hjk _ _ hh hag x

abbrev rows := (data sem j hj hjA hproper hg k hk hkA hjk).rows
abbrev source (q : PairedBoundarySections.Profile sem k) :=
  (data sem j hj hjA hproper hg k hk hkA hjk).profile (controller sem j hj hjA k hk hkA q)

theorem source_lower (q : PairedBoundarySections.Profile sem k)
    (d : Cell (lowerScheme sem j hj hjA)) :
    source sem j hj hjA hproper hg k hk hkA hjk q (oldCell sem j hj hjA k hk hkA d) =
      lowerSection sem j hj hjA hproper hg k q d := by
  rw [source, SourcePrefixLayer.Data.profile_old _ _ (SourceLayerCarrier.old_not_full
    (lowerScheme sem j hj hjA) (PairedBoundarySections.Profile sem k) k hk hkA
    (lower_grade sem j hj hjA hproper hg k hjk) d)]
  change lower sem j hj hjA hproper hg k hk hkA
    (member sem j hj hjA hproper hg k hk hkA hjk (controller sem j hj hjA k hk hkA q)) _ = _
  rw [member_controller, lower_old]

theorem source_boundary (q : PairedBoundarySections.Profile sem k) (d : Cell D) :
    source sem j hj hjA hproper hg k hk hkA hjk q
      (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA d)) = q.val d := by
  rw [source_lower, lowerSection_old sem j hj hjA hproper hg k hjk]

theorem inherited_row (c : Cell (lowerScheme sem j hj hjA))
    (d : (lowerScheme sem j hj hjA).below ((lowerScheme sem j hj hjA).cell c)) :
    (rows sem j hj hjA hproper hg k hk hkA hjk).E (oldCell sem j hj hjA k hk hkA c)
      (ownerEquiv sem j hj hjA hproper hg k hk hkA hjk c d) =
      (lowerSem sem j hj hjA hproper hg).E c d := by
  rw [SourcePrefixLayer.Data.row_old _ (SourceLayerCarrier.old_not_full
    (lowerScheme sem j hj hjA) (PairedBoundarySections.Profile sem k) k hk hkA
    (lower_grade sem j hj hjA hproper hg k hjk) c)]
  exact SourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem inherited_order : StrictMono (oldCell sem j hj hjA k hk hkA) :=
  SourceLayerCarrier.old_order _ _ _ _ _

theorem original_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows sem j hj hjA hproper hg k hk hkA hjk).E
      (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA c))
      (ownerEquiv sem j hj hjA hproper hg k hk hkA hjk (lowerOld sem j hj hjA c)
        (PairedBoundarySections.ownerEquiv sem j hj hjA hproper c d)) = sem.E c d := by
  rw [inherited_row]
  exact PairedBoundarySections.inherited_row sem j hj hjA hproper hg c d

theorem consistent (hs : sem.IsConsistent) :
    (rows sem j hj hjA hproper hg k hk hkA hjk).IsConsistent := by
  apply SourcePrefixLayer.Data.consistent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
    (PairedBoundarySections.Profile sem k) k hk hkA c hc
  apply (SourceLayerCarrier.base_respects_iff (lowerScheme sem j hj hjA)
    (PairedBoundarySections.Profile sem k) k hk hkA
    (lower_grade sem j hj hjA hproper hg k hjk) (lowerSem sem j hj hjA hproper hg) x _).mpr
  have he : (data sem j hj hjA hproper hg k hk hkA hjk).base.E
      (oldCell sem j hj hjA k hk hkA x) ∘ ownerEquiv sem j hj hjA hproper hg k hk hkA hjk x =
      (lowerSem sem j hj hjA hproper hg).E x := by
    funext d
    exact SourceLayerCarrier.base_old _ _ _ _ _ _ _ x d
  rw [he]
  exact PairedBoundarySections.consistent sem j hj hjA hproper hg hs x

theorem source_agreement (p q : PairedBoundarySections.Profile sem k)
    {h : ExtOrd} (hh : h ∈ upperGrid (D := D) k) (hag : Agree p.val q.val h) :
    Agree (source sem j hj hjA hproper hg k hk hkA hjk p)
      (source sem j hj hjA hproper hg k hk hkA hjk q) h := by
  apply (data sem j hj hjA hproper hg k hk hkA hjk).profile_prefix hh
  simpa only [data, member_controller] using hag

theorem source_supported (q : PairedBoundarySections.Profile sem k)
    (d : Cell (scheme sem j hj hjA k hk hkA)) :
    OrbitPrefixSupport.Supported k (upperGrid (D := D) k : Set ExtOrd) q.val
      (source sem j hj hjA hproper hg k hk hkA hjk q d) := by
  by_cases hd : (scheme sem j hj hjA k hk hkA).cell d = (A, k)
  · have he := (data sem j hj hjA hproper hg k hk hkA hjk).profile_new
      (controller sem j hj hjA k hk hkA q) ⟨d, hd⟩
    apply Or.inr
    apply Or.inl
    change (data sem j hj hjA hproper hg k hk hkA hjk).profile
      (controller sem j hj hjA k hk hkA q) d ∈ upperGrid (D := D) k
    rw [he]
    exact cut_mem (sourceGrid_bot _ _) _ _
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
      (PairedBoundarySections.Profile sem k) k hk hkA d hd
    rw [source_lower]
    exact lowerSection_supported sem j hj hjA hproper hg k hjk q x

theorem source_short (q : PairedBoundarySections.Profile sem k)
    (d : Cell (scheme sem j hj hjA k hk hkA)) :
    Short k (source sem j hj hjA hproper hg k hk hkA hjk q d) :=
  supported_short (fun _ hh => PairedBoundarySections.grid_short k hh) q.property.2.2
    (source_supported sem j hj hjA hproper hg k hk hkA hjk q d)

/-- Retained full owners use their own grade's shortness, not the upper grade. -/
theorem full_source_short (c : Cell (scheme sem j hj hjA k hk hkA))
    (hc : (scheme sem j hj hjA k hk hkA).scope c = A)
    (d : (scheme sem j hj hjA k hk hkA).below ((scheme sem j hj hjA k hk hkA).cell c)) :
    Short ((scheme sem j hj hjA k hk hkA).grade c)
      ((rows sem j hj hjA hproper hg k hk hkA hjk).E c d) := by
  apply (data sem j hj hjA hproper hg k hk hkA hjk).full_source_short
    (fun _ hh => PairedBoundarySections.grid_short k hh) _ _ c hc d
  · intro q x hx
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
      (PairedBoundarySections.Profile sem k) k hk hkA x hx
    change Short k (lower sem j hj hjA hproper hg k hk hkA _
      (oldCell sem j hj hjA k hk hkA y))
    rw [lower_old]
    exact lowerSection_short sem j hj hjA hproper hg k hjk _ y
  · intro x hs hx e
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
      (PairedBoundarySections.Profile sem k) k hk hkA x hx
    obtain ⟨z, rfl⟩ := (ownerEquiv sem j hj hjA hproper hg k hk hkA hjk y).surjective e
    have he := SourceLayerCarrier.base_old (lowerScheme sem j hj hjA)
      (PairedBoundarySections.Profile sem k) k hk hkA
      (lower_grade sem j hj hjA hproper hg k hjk) (lowerSem sem j hj hjA hproper hg) y z
    change (data sem j hj hjA hproper hg k hk hkA hjk).base.E _ _ = _ at he
    rw [he]
    have hi := SourceLayerCarrier.cell_toCell (lowerScheme sem j hj hjA)
      (PairedBoundarySections.Profile sem k) k hk hkA (.inl y)
    change Short ((scheme sem j hj hjA k hk hkA).grade (oldCell sem j hj hjA k hk hkA y)) _
    rw [show (scheme sem j hj hjA k hk hkA).grade (oldCell sem j hj hjA k hk hkA y) =
      (lowerScheme sem j hj hjA).grade y from congrArg Prod.snd hi]
    exact PairedBoundarySections.full_source_short sem j hj hjA hproper hg y
      ((congrArg Prod.fst hi).symm.trans hs) z

/-- A proper old owner still sees exactly its original lower domain. This
recovers locality from literal readback even when the old semantic row is long. -/
theorem lower_proper_respects {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    {r : Cell (lowerScheme sem j hj hjA) → ExtOrd}
    (hread : ∀ d, r (lowerOld sem j hj hjA d) = p d)
    (c : Cell (lowerScheme sem j hj hjA)) (hc : (lowerScheme sem j hj hjA).scope c ≠ A) :
    RespectsSemanticsBelow (lowerSem sem j hj hjA hproper hg)
      ((lowerScheme sem j hj hjA).cell c) (fun d => r d.1) := by
  have hc' : (lowerScheme sem j hj hjA).cell c ≠ (A, j) :=
    fun he => hc (congrArg Prod.fst he)
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D
    (PairedBoundarySections.Profile sem j) j hj hjA c hc'
  apply ((PairedBoundarySections.data sem j hj hjA hproper hg).old_respects_iff
    (SeparatedSourceLayerCarrier.old_not_full D (PairedBoundarySections.Profile sem j) j hj hjA
      (SeparatedSourceLayerCarrier.separated_of_proper D j hproper) x)).mpr
  apply (SeparatedSourceLayerCarrier.base_respects_iff D
    (PairedBoundarySections.Profile sem j) j hj hjA
    (SeparatedSourceLayerCarrier.separated_of_proper D j hproper) sem x _).mpr
  change RespectsSemanticsBelow sem (D.cell x) (fun d => r (lowerOld sem j hj hjA d.1))
  simpa only [hread] using hp.toBelow (D.cell x)

abbrev normalized {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) : PairedBoundarySections.Profile sem k :=
  PairedBoundarySections.encode sem k (fun d => (hg d).trans hjk.le) hp ht

variable {G : Finset ExtOrd} {C : ExtOrd}

/-- The new selected section decodes the complete coupled source, including
all retained lower controllers. Lower sections are not supplied as parameters. -/
def sectionOf {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (G : Finset ExtOrd) (C : ExtOrd)
    (d : Cell (scheme sem j hj hjA k hk hkA)) : ExtOrd :=
  PairedSlotDecoder.decode k (values p) G C
    (source sem j hj hjA hproper hg k hk hkA hjk (normalized sem j hg k hjk hp ht) d)

theorem section_boundary {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis k z) (hC : SelfVis k C) (d : Cell D) :
    sectionOf sem j hj hjA hproper hg k hk hkA hjk hp ht G C
      (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA d)) = p d := by
  rw [sectionOf, source_boundary]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_lawful {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis k z) (hC : SelfVis k C) :
    RespectsSemantics (rows sem j hj hjA hproper hg k hk hkA hjk)
      (sectionOf sem j hj hjA hproper hg k hk hkA hjk hp ht G C) := by
  apply (data sem j hj hjA hproper hg k hk hkA hjk).decoded_respects
    (controller sem j hj hjA k hk hkA (normalized sem j hg k hjk hp ht)) le_rfl
    (PairedSlotDecoder.decode_witness hG hC) _
    (full_source_short sem j hj hjA hproper hg k hk hkA hjk)
  intro c hc
  have hc' : (scheme sem j hj hjA k hk hkA).cell c ≠ (A, k) :=
    fun he => hc (congrArg Prod.fst he)
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem j hj hjA)
    (PairedBoundarySections.Profile sem k) k hk hkA c hc'
  apply (SourceLayerCarrier.base_respects_iff (lowerScheme sem j hj hjA)
    (PairedBoundarySections.Profile sem k) k hk hkA
    (lower_grade sem j hj hjA hproper hg k hjk) (lowerSem sem j hj hjA hproper hg) x _).mpr
  change RespectsSemanticsBelow (lowerSem sem j hj hjA hproper hg) _ (fun d =>
    PairedSlotDecoder.decode k (values p) G C
      (lower sem j hj hjA hproper hg k hk hkA
        (member sem j hj hjA hproper hg k hk hkA hjk
          (controller sem j hj hjA k hk hkA (normalized sem j hg k hjk hp ht)))
        (oldCell sem j hj hjA k hk hkA d.1)))
  simp only [member_controller, lower_old]
  apply lower_proper_respects sem j hj hjA hproper hg hp
    (r := fun y => PairedSlotDecoder.decode k (values p) G C
      (lowerSection sem j hj hjA hproper hg k (normalized sem j hg k hjk hp ht) y)) _ x
    (by simpa only [CellScheme.scope, oldCell, SourceLayerCarrier.cell_toCell,
      SourceLayerCarrier.index] using hc)
  intro d
  rw [lowerSection_old sem j hj hjA hproper hg k hjk]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_bound {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hC : SelfVis k C) (hb : ∀ d, p d ≤ C)
    (d : Cell (scheme sem j hj hjA k hk hkA)) :
    sectionOf sem j hj hjA hproper hg k hk hkA hjk hp ht G C d ≤ C := by
  apply PairedSlotDecoder.decode_le hC
  intro a ha
  obtain ⟨x, hx⟩ := mem_values.mp ha
  simpa only [hx] using hb x

theorem section_supported {K : ℕ} (hkK : k ≤ K) (hCG : C ∈ G)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    (d : Cell (scheme sem j hj hjA k hk hkA)) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
      (sectionOf sem j hj hjA hproper hg k hk hkA hjk hp ht G C d) :=
  PairedSlotDecoder.decode_supported hkK hCG _

theorem section_diagonal {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hC : SelfVis k C) (hb : ∀ d, p d ≤ C) :
    sectionOf sem j hj hjA hproper hg k hk hkA hjk hp ht G C
      (controller sem j hj hjA k hk hkA (normalized sem j hg k hjk hp ht)).1 = C := by
  unfold sectionOf source
  rw [SourcePrefixLayer.Data.profile_diagonal]
  exact decode_reserved_ceiling hC hb

theorem section_agreement {p q : Cell D → ExtOrd}
    (hp : RespectsSemantics sem p) (hq : RespectsSemantics sem q)
    (htp : ∀ d, p d ≠ ⊤) (htq : ∀ d, q d ≠ ⊤)
    {C' h : ExtOrd} (hG : ∀ z ∈ G, SelfVis k z)
    (hC : SelfVis k C) (hC' : SelfVis k C') (hh : h ∈ G)
    (hhC : h ≤ C) (hhC' : h ≤ C') (hag : Agree p q h) :
    Agree (sectionOf sem j hj hjA hproper hg k hk hkA hjk hp htp G C)
      (sectionOf sem j hj hjA hproper hg k hk hkA hjk hq htq G C') h := by
  obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
    largestCommonCut_spec hG hC hC' hh hhC hhC' htp htq hag
  have hs := source_agreement sem j hj hjA hproper hg k hk hkA hjk
    (normalized sem j hg k hjk hp htp) (normalized sem j hg k hjk hq htq) heG heAgree
  exact hs.decode (PairedSlotDecoder.decode_witness hG hC).mono
    (PairedSlotDecoder.decode_witness hG hC').mono hpReach hqReach (fun d _ => hcompare _)

/-- The constructed two-layer operator with independent owner grade k and
support grade K. The selected whole section is a conclusion, not an input. -/
theorem exists_supported_section {K : ℕ} (hkK : k ≤ K)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (hG : ∀ z ∈ G, SelfVis K z) (hCG : C ∈ G) (hCt : C ≠ ⊤)
    (hb : ∀ d, p d ≤ C) :
    ∃ r : Cell (scheme sem j hj hjA k hk hkA) → ExtOrd,
      RespectsSemantics (rows sem j hj hjA hproper hg k hk hkA hjk) r ∧
      (∀ d, r (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA d)) = p d) ∧
      (∀ d, r d ≤ C) ∧
      (∀ d, OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (r d)) := by
  have ht : ∀ d, p d ≠ ⊤ := by
    intro d hd
    exact hCt (top_le_iff.mp (hd ▸ hb d))
  have hv : ∀ z ∈ G, SelfVis k z := fun z hz => selfVis_mono (hG z hz) hkK
  exact ⟨sectionOf sem j hj hjA hproper hg k hk hkA hjk hp ht G C,
    section_lawful sem j hj hjA hproper hg k hk hkA hjk hp ht hv (hv C hCG),
    section_boundary sem j hj hjA hproper hg k hk hkA hjk hp ht hv (hv C hCG),
    section_bound sem j hj hjA hproper hg k hk hkA hjk hp ht (hv C hCG) hb,
    section_supported sem j hj hjA hproper hg k hk hkA hjk hkK hCG hp ht⟩

/-- Both coupled sections are constructed. All auxiliary capped values agree,
but no arbitrary lawful ambient on the coupled carrier is quantified here. -/
theorem exists_agreeing_sections {p q : Cell D → ExtOrd}
    (hp : RespectsSemantics sem p) (hq : RespectsSemantics sem q)
    (htp : ∀ d, p d ≠ ⊤) (htq : ∀ d, q d ≠ ⊤)
    {C' h : ExtOrd} (hG : ∀ z ∈ G, SelfVis k z)
    (hC : SelfVis k C) (hC' : SelfVis k C') (hh : h ∈ G)
    (hhC : h ≤ C) (hhC' : h ≤ C') (hag : Agree p q h) :
    ∃ r s : Cell (scheme sem j hj hjA k hk hkA) → ExtOrd,
      RespectsSemantics (rows sem j hj hjA hproper hg k hk hkA hjk) r ∧
      RespectsSemantics (rows sem j hj hjA hproper hg k hk hkA hjk) s ∧
      (∀ d, r (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA d)) = p d) ∧
      (∀ d, s (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA d)) = q d) ∧
      Agree r s h :=
  ⟨sectionOf sem j hj hjA hproper hg k hk hkA hjk hp htp G C,
    sectionOf sem j hj hjA hproper hg k hk hkA hjk hq htq G C',
    section_lawful sem j hj hjA hproper hg k hk hkA hjk hp htp hG hC,
    section_lawful sem j hj hjA hproper hg k hk hkA hjk hq htq hG hC',
    section_boundary sem j hj hjA hproper hg k hk hkA hjk hp htp hG hC,
    section_boundary sem j hj hjA hproper hg k hk hkA hjk hq htq hG hC',
    section_agreement sem j hj hjA hproper hg k hk hkA hjk hp hq htp htq
      hG hC hC' hh hhC hhC' hag⟩

end
end VaughtConjecture.Knight.PairedCoupledSections
