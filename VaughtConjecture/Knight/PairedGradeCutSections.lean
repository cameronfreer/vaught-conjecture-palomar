/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutLayerRows

/-! # Constructed sections retaining higher proper owners

Construct the paired grade-j layer on the actual grade cut, then splice back
the entire proper boundary. The boundary may have higher-grade active owners.
Their rows and labels remain literal. No overlap compatibility, future locality
or lower completion is supplied as an input.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.PairedGradeCutSections

open Transform Value ExtOrd SourcePrefixRows
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)

abbrev boundary := GradeCutBoundary.scheme D j
abbrev boundaryRows := GradeCutBoundary.rows D j sem
abbrev Profiles := PairedBoundarySections.Profile (boundaryRows sem j) j
abbrev lower := PairedBoundarySections.scheme (boundaryRows sem j) j hj hA
abbrev lowerRows := PairedBoundarySections.rows (boundaryRows sem j) j hj hA
  (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
abbrev scheme := GradeCutLayerCarrier.enlarged D (Profiles sem j) j hj hA
abbrev rows := GradeCutLayerRows.rows D (Profiles sem j) j hj hA hproper sem
  (lowerRows sem j hj hA hproper)
abbrev old (c : Cell D) := SourceLayerCarrier.toCell D (Profiles sem j) j hj hA (.inl c)
abbrev lowerEmbed := GradeCutLayerCarrier.embed D (Profiles sem j) j hj hA

theorem overlap (c : Cell (boundary (D := D) j))
    (d : (boundary (D := D) j).below ((boundary (D := D) j).cell c)) :
    (lowerRows sem j hj hA hproper).E
      (SourceLayerCarrier.toCell (boundary (D := D) j) (Profiles sem j) j hj hA (.inl c))
      (GradeCutLayerCarrier.ownerEquiv (boundary (D := D) j) (Profiles sem j) j hj hA
        (GradeCutBoundary.proper D j hproper) c d) = (boundaryRows sem j).E c d :=
  PairedBoundarySections.inherited_row (boundaryRows sem j) j hj hA
    (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j) c d

theorem consistent (hs : sem.IsConsistent) : (rows sem j hj hA hproper).IsConsistent :=
  GradeCutLayerRows.consistent D (Profiles sem j) j hj hA hproper sem
    (lowerRows sem j hj hA hproper) (overlap sem j hj hA hproper) hs
    (PairedBoundarySections.consistent (boundaryRows sem j) j hj hA
      (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
      (GradeCutBoundary.consistent D j sem hs))

theorem old_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows sem j hj hA hproper).E (old sem j hj hA c)
      (GradeCutLayerCarrier.ownerEquiv D (Profiles sem j) j hj hA hproper c d) = sem.E c d :=
  GradeCutLayerRows.old_row D (Profiles sem j) j hj hA hproper sem _ c d

theorem lower_row (c : Cell (lower sem j hj hA))
    (d : (lower sem j hj hA).below ((lower sem j hj hA).cell c)) :
    (rows sem j hj hA hproper).E (lowerEmbed sem j hj hA c)
      ⟨lowerEmbed sem j hj hA d.1, by
        simpa only [GradeCutLayerCarrier.embed_cell] using d.2⟩ =
      (lowerRows sem j hj hA hproper).E c d :=
  GradeCutLayerRows.embedded_row D (Profiles sem j) j hj hA hproper sem _
    (overlap sem j hj hA hproper) c d

variable {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
variable (ht : ∀ d : Cell (boundary (D := D) j), p (GradeCutBoundary.toCell D j d) ≠ ⊤)

def lowerSection (G : Finset ExtOrd) (C : ExtOrd) : Cell (lower sem j hj hA) → ExtOrd :=
  PairedBoundarySections.sectionOf (boundaryRows sem j) j hj hA
    (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
    (GradeCutBoundary.restrict_respects D j sem hp) ht G C

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) : Cell (scheme sem j hj hA) → ExtOrd :=
  GradeCutLayerRows.glue D (Profiles sem j) j hj hA p
    (lowerSection sem j hj hA hproper hp ht G C)

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem section_old (d : Cell D) :
    sectionOf sem j hj hA hproper hp ht G C (old sem j hj hA d) = p d :=
  GradeCutLayerRows.glue_old D (Profiles sem j) j hj hA p _ d

theorem section_lower (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C)
    (d : Cell (lower sem j hj hA)) :
    sectionOf sem j hj hA hproper hp ht G C (lowerEmbed sem j hj hA d) =
      lowerSection sem j hj hA hproper hp ht G C d :=
  GradeCutLayerRows.glue_embed D (Profiles sem j) j hj hA p _
    (PairedBoundarySections.section_old (boundaryRows sem j) j hj hA
      (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
      (GradeCutBoundary.restrict_respects D j sem hp) ht hG hC) d

theorem section_lawful (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) :
    RespectsSemantics (rows sem j hj hA hproper) (sectionOf sem j hj hA hproper hp ht G C) :=
  GradeCutLayerRows.glue_respects D (Profiles sem j) j hj hA hproper sem _
    (overlap sem j hj hA hproper) hp
    (PairedBoundarySections.section_lawful (boundaryRows sem j) j hj hA
      (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
      (GradeCutBoundary.restrict_respects D j sem hp) ht hG hC)
    (PairedBoundarySections.section_old (boundaryRows sem j) j hj hA
      (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
      (GradeCutBoundary.restrict_respects D j sem hp) ht hG hC)

theorem section_bound (hC : SelfVis j C) (hb : ∀ d, p d ≤ C)
    (d : Cell (scheme sem j hj hA)) : sectionOf sem j hj hA hproper hp ht G C d ≤ C := by
  unfold sectionOf GradeCutLayerRows.glue
  cases SourceLayerCarrier.toOcc D (Profiles sem j) j hj hA d with
  | inl c => exact hb c
  | inr q =>
    exact PairedBoundarySections.section_bound (boundaryRows sem j) j hj hA
      (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
      (GradeCutBoundary.restrict_respects D j sem hp) ht hC
      (fun c => hb (GradeCutBoundary.toCell D j c)) _

private theorem boundary_supported {K : ℕ} {H : Set ExtOrd} (d : Cell D) :
    OrbitPrefixSupport.Supported K H p (p d) := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inr ⟨d, K, le_rfl, by rw [ht, extVisibilityReplace_top]⟩)
  · by_cases hk : finitePart a < K
    · exact Or.inr (Or.inr ⟨d, finitePart a, hk.le, by
        rw [ha, extVisibilityReplace_of_finitePart_lt hk, limitPart_add_finitePart]⟩)
    · exact Or.inr (Or.inr ⟨d, K, le_rfl, by
        rw [ha, extVisibilityReplace_of_le_finitePart (not_lt.mp hk)]⟩)

theorem section_supported {K : ℕ} (hjK : j ≤ K) (hCG : C ∈ G)
    (d : Cell (scheme sem j hj hA)) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
      (sectionOf sem j hj hA hproper hp ht G C d) := by
  unfold sectionOf GradeCutLayerRows.glue
  cases SourceLayerCarrier.toOcc D (Profiles sem j) j hj hA d with
  | inl c => exact boundary_supported c
  | inr q =>
    have hs := PairedBoundarySections.section_supported (boundaryRows sem j) j hj hA
      (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j) hjK hCG
      (GradeCutBoundary.restrict_respects D j sem hp) ht
      (SourceLayerCarrier.toCell (boundary (D := D) j) (Profiles sem j) j hj hA (.inr q))
    rcases hs with hz | hg | ⟨c, i, hi, hc⟩
    · exact Or.inl hz
    · exact Or.inr (Or.inl hg)
    · exact Or.inr (Or.inr ⟨GradeCutBoundary.toCell D j c, i, hi, hc⟩)

theorem section_agreement {q : Cell D → ExtOrd} (hq : RespectsSemantics sem q)
    (htq : ∀ d : Cell (boundary (D := D) j), q (GradeCutBoundary.toCell D j d) ≠ ⊤)
    {C' h : ExtOrd} (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) (hC' : SelfVis j C')
    (hh : h ∈ G) (hhC : h ≤ C) (hhC' : h ≤ C') (hag : Agree p q h) :
    Agree (sectionOf sem j hj hA hproper hp ht G C)
      (sectionOf sem j hj hA hproper hq htq G C') h := by
  have hl := PairedBoundarySections.section_agreement (boundaryRows sem j) j hj hA
    (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
    (GradeCutBoundary.restrict_respects D j sem hp) (GradeCutBoundary.restrict_respects D j sem hq)
    ht htq hG hC hC' hh hhC hhC' (fun d => hag (GradeCutBoundary.toCell D j d))
  intro d
  unfold sectionOf GradeCutLayerRows.glue
  cases SourceLayerCarrier.toOcc D (Profiles sem j) j hj hA d with
  | inl c => exact hag c
  | inr q => exact hl _

include hp ht in
/-- The lower layer is constructed, not supplied. Higher proper owners may be
active above the agreement cap, and even top; only the decoded grade cut is
required to be bottom/proper-valued. -/
theorem exists_supported_section {K : ℕ} (hjK : j ≤ K)
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) (hCG : C ∈ G) :
    ∃ r : Cell (scheme sem j hj hA) → ExtOrd,
      RespectsSemantics (rows sem j hj hA hproper) r ∧
      (∀ d, r (old sem j hj hA d) = p d) ∧
      (∀ d, OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (r d)) :=
  ⟨sectionOf sem j hj hA hproper hp ht G C,
    section_lawful sem j hj hA hproper hp ht hG hC,
    section_old sem j hj hA hproper hp ht,
    section_supported sem j hj hA hproper hp ht hjK hCG⟩

end
end VaughtConjecture.Knight.PairedGradeCutSections
