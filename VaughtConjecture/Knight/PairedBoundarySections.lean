/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProperBoundarySourceLayer
public import VaughtConjecture.Knight.PairedSlotComparison
public import VaughtConjecture.Knight.CoatomBoundaryExtension

/-! # Constructed paired-decoded sections of a proper boundary layer

The finite controller family, incoming normalization, rows, and selected decoded
sections are constructed from the actual boundary semantics. Retained owners may
have the new grade and arbitrary long source rows. The new rows alone are short.

This is one layer, with every old occurrence in its proper boundary. It supplies
the decoder-to-carrier step of Plan 29, not the induction adding all lower full
indices, arbitrary-ambient lifting, or coatom amalgamation.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.PairedBoundarySections

open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition
open PairedSlotEncoding PairedSlotComparison

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ)

/-- All lawful short coded profiles, not a chosen list of displays. Including
non-normalized coded profiles avoids needing idempotence for family membership. -/
def Profile := {p : Cell D → ExtOrd // RespectsSemantics sem p ∧
  (∀ d, p d ∈ ExtOrd.codedAlphabet (2 * Fintype.card (Cell D)) j) ∧ ∀ d, Short j (p d)}

instance : Fintype (Profile sem j) :=
  ((codedLabellings_finite (Cell D) (2 * Fintype.card (Cell D)) j).subset
    (fun _ h => h.2.1)).fintype

theorem normalize_lawful (hg : ∀ d : Cell D, D.grade d ≤ j)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    RespectsSemantics sem (PairedSlotEncoding.normalize j p) := by
  have hr := FiniteOrbitEmbedding.map_respects (hp.toBelow (A, j))
    (fun d => hg d.1) (PairedSlotIncoming.encoder_witness j (values p))
    (PairedSlotIncoming.encoder_reflects_bottom j (values p))
  have hw := hr.toRespects
    (fun d => ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), hg d⟩)
  change RespectsSemantics sem (fun d => PairedSlotIncoming.encoder j (values p) (p d)) at hw
  simpa only [PairedSlotIncoming.encoder_profile] using hw

def encode (hg : ∀ d : Cell D, D.grade d ≤ j)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤) :
    Profile sem j :=
  ⟨PairedSlotEncoding.normalize j p, normalize_lawful sem j hg hp,
    fun d => normalize_mem j p d (ht d), PairedSlotProfiles.normalize_short j p⟩

def ceiling : ExtOrd :=
  ofOrd (Ordinal.omega0 * (2 * Fintype.card (Cell D) + 1 : ℕ) + j)

theorem grid_bound {h : ExtOrd} (hh : h ∈ sourceGrid j (Fintype.card (Cell D))) :
    h ≤ ceiling (D := D) j := by
  classical
  rcases Finset.mem_insert.mp hh with rfl | hh
  · exact bot_le
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hh
    have hb' : b ≤ 2 * Fintype.card (Cell D) + 1 := by
      have := Finset.mem_range.mp hb
      omega
    apply ofOrd_le_ofOrd.mpr
    gcongr

theorem grid_short {h : ExtOrd} (hh : h ∈ sourceGrid j (Fintype.card (Cell D))) :
    Short j h := by
  classical
  rcases Finset.mem_insert.mp hh with rfl | hh
  · exact Or.inl rfl
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hh
    exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)

theorem profile_bound (q : Profile sem j) (d : Cell D) : q.val d ≤ ceiling (D := D) j := by
  rcases ExtOrd.mem_codedAlphabet_iff.mp (q.property.2.1 d) with hb | ⟨b, i, hb, hi, he⟩
  · rw [hb]; exact bot_le
  · have hij : i ≤ j := by
      rcases q.property.2.2 d with hz | hz | ⟨a, ha, haj⟩
      · exact (ofOrd_ne_bot _ (he.symm.trans hz)).elim
      · exact (ofOrd_ne_top _ (he.symm.trans hz)).elim
      · have ha' := ofOrd_inj.mp (he.symm.trans ha)
        simpa only [← ha', finitePart_mul_add] using haj
    rw [he]
    apply ofOrd_le_ofOrd.mpr
    have hb' := hb.trans (Nat.le_succ (2 * Fintype.card (Cell D)))
    gcongr

variable (hj : 0 < j) (hA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)
variable (hg : ∀ d : Cell D, D.grade d ≤ j)

abbrev scheme := ProperBoundarySourceLayer.carrier D (Profile sem j) j hj hA

abbrev old (d : Cell D) : Cell (scheme sem j hj hA) :=
  ProperBoundarySourceLayer.old D (Profile sem j) j hj hA d

abbrev data := ProperBoundarySourceLayer.data D sem (Profile sem j) j hj hA hproper hg
  (sourceGrid j (Fintype.card (Cell D))) (ceiling (D := D) j)
  (sourceGrid_bot _ _) (sourceGrid_endpoint le_rfl) (fun _ hh => grid_bound j hh)
  (fun _ hh => sourceGrid_visible hh) (fun q => q.val) (fun q => q.property.1)
  (profile_bound sem j)

abbrev rows : Semantics (scheme sem j hj hA) := (data sem j hj hA hproper hg).rows

abbrev ownerEquiv (c : Cell D) :=
  ProperBoundarySourceLayer.ownerEquiv D (Profile sem j) j hj hA hproper c

abbrev controller (q : Profile sem j) :=
  SourceLayerCarrier.controller D (Profile sem j) j hj hA q

abbrev source (q : Profile sem j) : Cell (scheme sem j hj hA) → ExtOrd :=
  (data sem j hj hA hproper hg).profile (controller sem j hj hA q)

theorem source_old (q : Profile sem j) (d : Cell D) :
    source sem j hj hA hproper hg q (old sem j hj hA d) = q.val d :=
  ProperBoundarySourceLayer.section_old D sem (Profile sem j) j hj hA hproper hg
    _ _ _ _ _ _ _ _ _ q d

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows sem j hj hA hproper hg).E (old sem j hj hA c)
      (ownerEquiv sem j hj hA hproper c d) = sem.E c d :=
  ProperBoundarySourceLayer.inherited_row D sem (Profile sem j) j hj hA hproper hg
    _ _ _ _ _ _ _ _ _ c d

theorem consistent (hs : sem.IsConsistent) :
    (rows sem j hj hA hproper hg).IsConsistent :=
  ProperBoundarySourceLayer.consistent D sem (Profile sem j) j hj hA hproper hg
    _ _ _ _ _ _ _ _ _ hs

theorem source_agreement (p q : Profile sem j) :
    Agree (source sem j hj hA hproper hg p) (source sem j hj hA hproper hg q)
      (cut (sourceGrid j (Fintype.card (Cell D))) p.val q.val) := by
  apply ProperBoundarySourceLayer.section_prefix D sem (Profile sem j) j hj hA hproper hg
    _ _ _ _ _ _ _ _ _ p q
    (cut_mem (sourceGrid_bot _ _) _ _) (agree_cut (sourceGrid_bot _ _) _ _)

theorem full_source_short (c : Cell (scheme sem j hj hA))
    (hc : (scheme sem j hj hA).scope c = A)
    (d : (scheme sem j hj hA).below ((scheme sem j hj hA).cell c)) :
    Short ((scheme sem j hj hA).grade c) ((rows sem j hj hA hproper hg).E c d) := by
  apply (data sem j hj hA hproper hg).full_source_short
    (fun _ hh => grid_short j hh) _ _ c hc d
  · intro q x hx
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j) j hj hA x hx
    change Short j (ProperBoundarySourceLayer.lower D (Profile sem j) j hj hA
      (fun q => q.val) _ (old sem j hj hA y))
    rw [ProperBoundarySourceLayer.lower_old]
    exact (ProperBoundarySourceLayer.member D (Profile sem j) j hj hA hproper q).property.2.2 y
  · intro x hs hx
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j) j hj hA x hx
    exact (hproper y (by simpa only [CellScheme.scope, SourceLayerCarrier.cell_toCell,
      SourceLayerCarrier.index] using hs)).elim

variable {G : Finset ExtOrd} {C : ExtOrd}

/-- A selected whole section, with no whole-section or decoder-comparison input. -/
def sectionOf {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    (G : Finset ExtOrd) (C : ExtOrd) (d : Cell (scheme sem j hj hA)) : ExtOrd :=
  PairedSlotDecoder.decode j (values p) G C
    (source sem j hj hA hproper hg (encode sem j hg hp ht) d)

theorem section_old {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) (d : Cell D) :
    sectionOf sem j hj hA hproper hg hp ht G C (old sem j hj hA d) = p d := by
  rw [sectionOf, source_old]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_bound {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hC : SelfVis j C) (hb : ∀ d, p d ≤ C)
    (d : Cell (scheme sem j hj hA)) :
    sectionOf sem j hj hA hproper hg hp ht G C d ≤ C := by
  apply PairedSlotDecoder.decode_le hC
  intro a ha
  obtain ⟨x, hx⟩ := mem_values.mp ha
  simpa only [hx] using hb x

/-- Proper owners use the literal input's locality, not composition through
their possibly long source rows. New owners use short-source composition. -/
theorem section_lawful {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) :
    RespectsSemantics (rows sem j hj hA hproper hg)
      (sectionOf sem j hj hA hproper hg hp ht G C) := by
  apply (data sem j hj hA hproper hg).decoded_respects
    (controller sem j hj hA (encode sem j hg hp ht)) le_rfl
    (PairedSlotDecoder.decode_witness hG hC) _ (full_source_short sem j hj hA hproper hg)
  intro c hc
  have hc' : (scheme sem j hj hA).cell c ≠ (A, j) :=
    fun he => hc (congrArg Prod.fst he)
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j) j hj hA c hc'
  apply (SeparatedSourceLayerCarrier.base_respects_iff D (Profile sem j) j hj hA
    (SeparatedSourceLayerCarrier.separated_of_proper D j hproper) sem x _).mpr
  change RespectsSemanticsBelow sem (D.cell x) (fun d =>
    PairedSlotDecoder.decode j (values p) G C
      (ProperBoundarySourceLayer.lower D (Profile sem j) j hj hA (fun q => q.val)
        (ProperBoundarySourceLayer.member D (Profile sem j) j hj hA hproper
          (controller sem j hj hA (encode sem j hg hp ht))) (old sem j hj hA d.1)))
  simp only [controller, ProperBoundarySourceLayer.member_controller,
    ProperBoundarySourceLayer.lower_old]
  change RespectsSemanticsBelow sem (D.cell x)
    (fun d => PairedSlotDecoder.decode j (values p) G C (PairedSlotEncoding.normalize j p d.1))
  simpa only [PairedSlotDecoder.decode_normalize hG hC ht] using hp.toBelow (D.cell x)

theorem section_diagonal {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hC : SelfVis j C) (hb : ∀ d, p d ≤ C) :
    sectionOf sem j hj hA hproper hg hp ht G C
      (controller sem j hj hA (encode sem j hg hp ht)).1 = C := by
  unfold sectionOf source
  rw [SourcePrefixLayer.Data.profile_diagonal]
  exact decode_reserved_ceiling hC hb

theorem section_supported {K : ℕ} (hjK : j ≤ K) (hC : C ∈ G)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    (d : Cell (scheme sem j hj hA)) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
      (sectionOf sem j hj hA hproper hg hp ht G C d) :=
  PairedSlotDecoder.decode_supported hjK hC _

/-- The paired comparison includes unused gaps. It yields agreement of every
actual output coordinate, not only of the old boundary or selected diagonal. -/
theorem section_agreement {p q : Cell D → ExtOrd}
    (hp : RespectsSemantics sem p) (hq : RespectsSemantics sem q)
    (htp : ∀ d, p d ≠ ⊤) (htq : ∀ d, q d ≠ ⊤)
    {C' h : ExtOrd} (hG : ∀ z ∈ G, SelfVis j z)
    (hC : SelfVis j C) (hC' : SelfVis j C') (hh : h ∈ G)
    (hhC : h ≤ C) (hhC' : h ≤ C') (hag : Agree p q h) :
    Agree (sectionOf sem j hj hA hproper hg hp htp G C)
      (sectionOf sem j hj hA hproper hg hq htq G C') h := by
  obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
    largestCommonCut_spec hG hC hC' hh hhC hhC' htp htq hag
  have hs : Agree (source sem j hj hA hproper hg (encode sem j hg hp htp))
      (source sem j hj hA hproper hg (encode sem j hg hq htq)) (largestCommonCut j p q) :=
    ProperBoundarySourceLayer.section_prefix D sem (Profile sem j) j hj hA
      hproper hg _ _ _ _ _ _ _ _ _ (encode sem j hg hp htp) (encode sem j hg hq htq)
      heG heAgree
  exact hs.decode (PairedSlotDecoder.decode_witness hG hC).mono
    (PairedSlotDecoder.decode_witness hG hC').mono hpReach hqReach
    (fun d _ => hcompare _)

/-- A producer with the full grade/ceiling parameters of the coupled operator.
Properness follows from the finite ceiling; no coded whole section is supplied.
This still adds only one full-scope layer to a proper boundary. -/
theorem exists_supported_section {K : ℕ} (hjK : j ≤ K)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (hG : ∀ z ∈ G, SelfVis K z) (hCG : C ∈ G) (hCt : C ≠ ⊤)
    (hb : ∀ d, p d ≤ C) :
    ∃ r : Cell (scheme sem j hj hA) → ExtOrd,
      RespectsSemantics (rows sem j hj hA hproper hg) r ∧
      (∀ d, r (old sem j hj hA d) = p d) ∧
      (∀ d, r d ≤ C) ∧
      (∀ d, OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (r d)) := by
  have ht : ∀ d, p d ≠ ⊤ := by
    intro d hd
    exact hCt (top_le_iff.mp (hd ▸ hb d))
  have hv : ∀ z ∈ G, SelfVis j z := fun z hz => selfVis_mono (hG z hz) hjK
  exact ⟨sectionOf sem j hj hA hproper hg hp ht G C,
    section_lawful sem j hj hA hproper hg hp ht hv (hv C hCG),
    section_old sem j hj hA hproper hg hp ht hv (hv C hCG),
    section_bound sem j hj hA hproper hg hp ht (hv C hCG) hb,
    section_supported sem j hj hA hproper hg hjK hCG hp ht⟩

/-- Relative supply for two *constructed* sections. The ambient here is produced
from a second lawful boundary input; it is not an arbitrary ambient on the new
carrier. A retained owner above `h` remains literal, and every auxiliary capped
reading agrees with the constructed ambient at the original `h`. -/
theorem exists_agreeing_sections {p q : Cell D → ExtOrd}
    (hp : RespectsSemantics sem p) (hq : RespectsSemantics sem q)
    (htp : ∀ d, p d ≠ ⊤) (htq : ∀ d, q d ≠ ⊤)
    {C' h : ExtOrd} (hG : ∀ z ∈ G, SelfVis j z)
    (hC : SelfVis j C) (hC' : SelfVis j C') (hh : h ∈ G)
    (hhC : h ≤ C) (hhC' : h ≤ C') (hag : Agree p q h) :
    ∃ r s : Cell (scheme sem j hj hA) → ExtOrd,
      RespectsSemantics (rows sem j hj hA hproper hg) r ∧
      RespectsSemantics (rows sem j hj hA hproper hg) s ∧
      (∀ d, r (old sem j hj hA d) = p d) ∧
      (∀ d, s (old sem j hj hA d) = q d) ∧ Agree r s h :=
  ⟨sectionOf sem j hj hA hproper hg hp htp G C,
    sectionOf sem j hj hA hproper hg hq htq G C',
    section_lawful sem j hj hA hproper hg hp htp hG hC,
    section_lawful sem j hj hA hproper hg hq htq hG hC',
    section_old sem j hj hA hproper hg hp htp hG hC,
    section_old sem j hj hA hproper hg hq htq hG hC',
    section_agreement sem j hj hA hproper hg hp hq htp htq hG hC hC' hh hhC hhC' hag⟩

/-- Join the actual two-face boundary, then construct its section on the new
layer. The whole boundary's lawfulness is proved by gluing, not assumed. -/
theorem exists_over_faces {U V : Finset ι × ℕ}
    (a : CoatomBoundaryExtension.Section sem U V)
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    {K : ℕ} (hjK : j ≤ K) (hG : ∀ z ∈ G, SelfVis K z)
    (hCG : C ∈ G) (hCt : C ≠ ⊤)
    (hbU : ∀ d, a.onLeft d ≤ C) (hbV : ∀ d, a.onRight d ≤ C) :
    ∃ r : Cell (scheme sem j hj hA) → ExtOrd,
      RespectsSemantics (rows sem j hj hA hproper hg) r ∧
      (∀ d : D.below U, r (old sem j hj hA d.1) = a.onLeft d) ∧
      (∀ d : D.below V, r (old sem j hj hA d.1) = a.onRight d) ∧
      (∀ d, r d ≤ C) ∧
      (∀ d, OrbitPrefixSupport.Supported K (G : Set ExtOrd) (a.whole hcover) (r d)) := by
  have hb : ∀ d, a.whole hcover d ≤ C := by
    intro d
    rcases hcover d with hd | hd
    · rw [a.whole_left hcover ⟨d, hd⟩]
      exact hbU ⟨d, hd⟩
    · rw [a.whole_right hcover ⟨d, hd⟩]
      exact hbV ⟨d, hd⟩
  obtain ⟨r, hr, hread, hbound, hsupp⟩ :=
    exists_supported_section sem j hj hA hproper hg hjK
      (a.whole_respects hcover) hG hCG hCt hb
  exact ⟨r, hr, fun d => (hread d.1).trans (a.whole_left hcover d),
    fun d => (hread d.1).trans (a.whole_right hcover d), hbound, hsupp⟩

end
end VaughtConjecture.Knight.PairedBoundarySections
