/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalPairedProfiles
public import VaughtConjecture.Knight.ProperBoundarySourceLayer
public import VaughtConjecture.Knight.PairedCoupledSections

/-! # Canonical controllers normalized over the complete field inventory

`X` retains all fields, including fields not yet present at this grade. Both
normalization and controller agreement cuts use all of `X`. Only the actual
occurrence map is projected when checking inherited-row lawfulness. The new
controller family and its selected sections are constructed, not supplied.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalFieldLayer
open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition
open PairedSlotEncoding PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (X : Type*) [Fintype X] (occ : Cell D → X)

def Profile := {p : X → ExtOrd // RespectsSemantics sem (p ∘ occ) ∧
  p ∈ CanonicalPairedProfiles.inventory X j}

instance : Fintype (Profile sem j X occ) :=
  ((CanonicalPairedProfiles.inventory_finite X j).subset (fun _ h => h.2)).fintype

theorem profile_short (q : Profile sem j X occ) (x : X) : Short j (q.val x) :=
  CanonicalPairedProfiles.inventory_short X j q.property.2 x

def ceiling : ExtOrd := ofOrd (Ordinal.omega0 * (2 * Fintype.card X + 1 : ℕ) + j)

theorem grid_bound {h : ExtOrd} (hh : h ∈ sourceGrid j (Fintype.card X)) :
    h ≤ ceiling j X := by
  classical
  rcases Finset.mem_insert.mp hh with rfl | hh
  · exact bot_le
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hh
    have hb' : b ≤ 2 * Fintype.card X + 1 := by
      have := Finset.mem_range.mp hb
      omega
    exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl)

theorem profile_bound (q : Profile sem j X occ) (x : X) : q.val x ≤ ceiling j X := by
  apply (CanonicalPairedProfiles.inventory_bound X j q.property.2 x).trans
  exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr; omega) le_rfl)

theorem grid_short {h : ExtOrd} (hh : h ∈ sourceGrid j (Fintype.card X)) :
    Short j h := by
  classical
  rcases Finset.mem_insert.mp hh with rfl | hh
  · exact Or.inl rfl
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hh
    exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)

variable (hj : 0 < j) (hA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)
variable (hg : ∀ d : Cell D, D.grade d ≤ j)

def encode {p : X → ExtOrd} (hp : RespectsSemantics sem (p ∘ occ))
    (ht : ∀ x, p x ≠ ⊤) : Profile sem j X occ := by
  refine ⟨PairedSlotEncoding.normalize j p, ?_,
    CanonicalPairedProfiles.normalize_mem_inventory X j ht⟩
  have hr := FiniteOrbitEmbedding.map_respects (hp.toBelow (A, j))
    (fun d => hg d.1) (PairedSlotIncoming.encoder_witness j (values p))
    (PairedSlotIncoming.encoder_reflects_bottom j (values p))
  have hw := hr.toRespects
    (fun d => ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), hg d⟩)
  simpa only [Function.comp_def, PairedSlotIncoming.encoder_profile] using hw

abbrev scheme := SourceLayerCarrier.scheme D (Profile sem j X occ) j hj hA
abbrev old (d : Cell D) : Cell (scheme sem j X occ hj hA) :=
  SourceLayerCarrier.toCell D (Profile sem j X occ) j hj hA (.inl d)
abbrev controller (q : Profile sem j X occ) :=
  SourceLayerCarrier.controller D (Profile sem j X occ) j hj hA q
abbrev member := ProperBoundarySourceLayer.member D (Profile sem j X occ) j hj hA hproper
abbrev ownerEquiv := ProperBoundarySourceLayer.ownerEquiv D (Profile sem j X occ) j hj hA hproper
abbrev lower (q : Profile sem j X occ) :=
  ProperBoundarySourceLayer.lower D (Profile sem j X occ) j hj hA (fun q => q.val ∘ occ) q

def data : SourcePrefixLayer.Data (scheme sem j X occ hj hA) j X where
  base := ProperBoundarySourceLayer.base D sem (Profile sem j X occ) j hj hA hproper
  max_grade d := by
    rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
    cases SourceLayerCarrier.toOcc D (Profile sem j X occ) j hj hA d with
    | inl x => exact hg x
    | inr q => exact le_rfl
  grid := sourceGrid j (Fintype.card X)
  bot_mem := sourceGrid_bot _ _
  ceiling := ceiling j X
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := grid_bound j X hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := (member sem j X occ hj hA hproper c).val
  lower c := lower sem j X occ hj hA (member sem j X occ hj hA hproper c)
  lower_bound c d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j X occ) j hj hA d hd
    simpa only [lower, ProperBoundarySourceLayer.lower_old, Function.comp_apply] using
      profile_bound sem j X occ (member sem j X occ hj hA hproper c) (occ x)
  lower_lawful c d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j X occ) j hj hA d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff D (Profile sem j X occ) j hj hA
      (SeparatedSourceLayerCarrier.separated_of_proper D j hproper) sem x _).mpr
    change RespectsSemanticsBelow sem (D.cell x) (fun d =>
      lower sem j X occ hj hA (member sem j X occ hj hA hproper c)
        (old sem j X occ hj hA d.1))
    simpa only [lower, old, ProperBoundarySourceLayer.lower_old] using
      (member sem j X occ hj hA hproper c).property.1.toBelow (D.cell x)
  grid_agreement p q h _ hag d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j X occ) j hj hA d hd
    simpa only [lower, old, ProperBoundarySourceLayer.lower_old, Function.comp_apply]
      using hag (occ x)

abbrev rows := (data sem j X occ hj hA hproper hg).rows
abbrev source (q : Profile sem j X occ) :=
  (data sem j X occ hj hA hproper hg).profile (controller sem j X occ hj hA q)

theorem source_old (q : Profile sem j X occ) (d : Cell D) :
    source sem j X occ hj hA hproper hg q (old sem j X occ hj hA d) = q.val (occ d) := by
  rw [source, SourcePrefixLayer.Data.profile_old _ _ (SeparatedSourceLayerCarrier.old_not_full
    D (Profile sem j X occ) j hj hA
    (SeparatedSourceLayerCarrier.separated_of_proper D j hproper) d)]
  change lower sem j X occ hj hA
    (member sem j X occ hj hA hproper (controller sem j X occ hj hA q)) _ = _
  simp only [lower, member, controller, ProperBoundarySourceLayer.member_controller,
    ProperBoundarySourceLayer.lower_old, Function.comp_apply]

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows sem j X occ hj hA hproper hg).E (old sem j X occ hj hA c)
      (ownerEquiv sem j X occ hj hA hproper c d) = sem.E c d := by
  rw [SourcePrefixLayer.Data.row_old _ (SeparatedSourceLayerCarrier.old_not_full
    D (Profile sem j X occ) j hj hA
    (SeparatedSourceLayerCarrier.separated_of_proper D j hproper) c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem consistent (hs : sem.IsConsistent) : (rows sem j X occ hj hA hproper hg).IsConsistent := by
  apply SourcePrefixLayer.Data.consistent
  intro d hd
  obtain ⟨c, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j X occ) j hj hA d hd
  apply (SeparatedSourceLayerCarrier.base_respects_iff D (Profile sem j X occ) j hj hA
    (SeparatedSourceLayerCarrier.separated_of_proper D j hproper) sem c _).mpr
  have he : (data sem j X occ hj hA hproper hg).base.E (old sem j X occ hj hA c) ∘
      ownerEquiv sem j X occ hj hA hproper c = sem.E c := by
    funext d
    exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d
  rw [he]
  exact hs c

theorem source_prefix (p q : Profile sem j X occ) {h : ExtOrd}
    (hh : h ∈ sourceGrid j (Fintype.card X)) (hag : Agree p.val q.val h) :
    Agree (source sem j X occ hj hA hproper hg p)
      (source sem j X occ hj hA hproper hg q) h := by
  apply (data sem j X occ hj hA hproper hg).profile_prefix hh
  change Agree (member sem j X occ hj hA hproper (controller sem j X occ hj hA p)).val
    (member sem j X occ hj hA hproper (controller sem j X occ hj hA q)).val h
  simpa only [member, controller, ProperBoundarySourceLayer.member_controller] using hag

theorem full_source_short (c : Cell (scheme sem j X occ hj hA))
    (hc : (scheme sem j X occ hj hA).scope c = A)
    (d : (scheme sem j X occ hj hA).below ((scheme sem j X occ hj hA).cell c)) :
    Short ((scheme sem j X occ hj hA).grade c) ((rows sem j X occ hj hA hproper hg).E c d) := by
  apply (data sem j X occ hj hA hproper hg).full_source_short
    (fun _ hh => grid_short j X hh) _ _ c hc d
  · intro q x hx
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j X occ) j hj hA x hx
    change Short j (lower sem j X occ hj hA (member sem j X occ hj hA hproper q)
      (old sem j X occ hj hA y))
    simpa only [lower, ProperBoundarySourceLayer.lower_old, Function.comp_apply] using
      profile_short sem j X occ (member sem j X occ hj hA hproper q) (occ y)
  · intro x hs hx
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j X occ) j hj hA x hx
    exact (hproper y (by simpa only [CellScheme.scope, SourceLayerCarrier.cell_toCell,
      SourceLayerCarrier.index] using hs)).elim

variable {p : X → ExtOrd} (hp : RespectsSemantics sem (p ∘ occ)) (ht : ∀ x, p x ≠ ⊤)
variable {G : Finset ExtOrd} {C : ExtOrd}

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) (d : Cell (scheme sem j X occ hj hA)) : ExtOrd :=
  PairedSlotDecoder.decode j (values p) G C
    (source sem j X occ hj hA hproper hg (encode sem j X occ hg hp ht) d)

theorem section_old (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) (d : Cell D) :
    sectionOf sem j X occ hj hA hproper hg hp ht G C (old sem j X occ hj hA d) = p (occ d) := by
  rw [sectionOf, source_old]
  exact PairedSlotDecoder.decode_normalize hG hC ht (occ d)

theorem section_lawful (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) :
    RespectsSemantics (rows sem j X occ hj hA hproper hg)
      (sectionOf sem j X occ hj hA hproper hg hp ht G C) := by
  apply (data sem j X occ hj hA hproper hg).decoded_respects
    (controller sem j X occ hj hA (encode sem j X occ hg hp ht)) le_rfl
    (PairedSlotDecoder.decode_witness hG hC) _ (full_source_short sem j X occ hj hA hproper hg)
  intro c hc
  have hc' : (scheme sem j X occ hj hA).cell c ≠ (A, j) := fun he => hc (congrArg Prod.fst he)
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j X occ) j hj hA c hc'
  apply (SeparatedSourceLayerCarrier.base_respects_iff D (Profile sem j X occ) j hj hA
    (SeparatedSourceLayerCarrier.separated_of_proper D j hproper) sem x _).mpr
  change RespectsSemanticsBelow sem (D.cell x) (fun d =>
    PairedSlotDecoder.decode j (values p) G C
      (lower sem j X occ hj hA
        (member sem j X occ hj hA hproper
          (controller sem j X occ hj hA (encode sem j X occ hg hp ht)))
        (old sem j X occ hj hA d.1)))
  simp only [lower, member, controller, ProperBoundarySourceLayer.member_controller,
    ProperBoundarySourceLayer.lower_old, Function.comp_apply]
  change RespectsSemanticsBelow sem (D.cell x) (fun d =>
    PairedSlotDecoder.decode j (values p) G C (PairedSlotEncoding.normalize j p (occ d.1)))
  simpa only [PairedSlotDecoder.decode_normalize hG hC ht, Function.comp_apply] using
    hp.toBelow (D.cell x)

theorem section_bound (hC : SelfVis j C) (hb : ∀ x, p x ≤ C)
    (d : Cell (scheme sem j X occ hj hA)) :
    sectionOf sem j X occ hj hA hproper hg hp ht G C d ≤ C := by
  apply PairedSlotDecoder.decode_le hC
  intro a ha
  obtain ⟨x, hx⟩ := mem_values.mp ha
  simpa only [hx] using hb x

theorem section_supported {K : ℕ} (hjK : j ≤ K) (hCG : C ∈ G)
    (d : Cell (scheme sem j X occ hj hA)) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
      (sectionOf sem j X occ hj hA hproper hg hp ht G C d) :=
  PairedSlotDecoder.decode_supported hjK hCG _

/-- Both outer decoder parameters are held fixed. Agreement includes all
actual new controller coordinates, not just the projected old fields. -/
theorem section_agreement {q : X → ExtOrd} (hq : RespectsSemantics sem (q ∘ occ))
    (htq : ∀ x, q x ≠ ⊤) {h : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf sem j X occ hj hA hproper hg hp ht G C)
      (sectionOf sem j X occ hj hA hproper hg hq htq G C) h := by
  obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
    largestCommonCut_spec hG hC hC hh hhC hhC ht htq hag
  have hs := source_prefix sem j X occ hj hA hproper hg
    (encode sem j X occ hg hp ht) (encode sem j X occ hg hq htq) heG heAgree
  exact hs.decode (PairedSlotDecoder.decode_witness hG hC).mono
    (PairedSlotDecoder.decode_witness hG hC).mono hpReach hqReach (fun _ _ => hcompare _)

end
end VaughtConjecture.Knight.CanonicalFieldLayer
