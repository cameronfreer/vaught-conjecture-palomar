/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutPairRows
public import VaughtConjecture.Knight.CanonicalSections

/-! # Two canonical lower layers retaining higher proper owners

Construct the canonical pair on the grade-k boundary cut, then retain every
higher proper owner with its literal original row and label. The selected
operator is lawful, orbit supported, and agrees on every lower auxiliary at
fixed outer parameters. The old boundary need not have grade at most k.

This constructs lower rows for the proper-grade-three problem; it does not
claim arbitrary cap-preserving extension of a joint boundary/controller history.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalPairBoundary
open Transform Value ExtOrd PairedSlotEncoding PairedSlotComparison SourcePrefixRows
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j k : ℕ)
variable (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A) (hjk : j < k)

abbrev boundary := GradeCutBoundary.scheme D k
abbrev boundaryRows := GradeCutBoundary.rows D k sem
abbrev firstProfiles := CanonicalGradeCutSections.Profiles (boundaryRows sem k) j
abbrev secondProfiles :=
  CanonicalFieldLayer.Profile (boundaryRows sem k) k (Cell (boundary (D := D) k)) id
abbrev lower := CanonicalMixedGradeLayers.scheme (boundaryRows sem k) j hj hjA k hk hkA
abbrev lowerRows := CanonicalMixedGradeLayers.rows (boundaryRows sem k) j hj hjA
  (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
abbrev scheme := GradeCutPairCarrier.enlarged D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA
abbrev old := GradeCutPairCarrier.old D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA
abbrev embed := GradeCutPairCarrier.embed D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA
abbrev rows := GradeCutPairRows.rows D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA hp hjk.le sem (lowerRows sem j k hj hjA hk hkA hp hjk)

theorem overlap (c : Cell (boundary (D := D) k))
    (d : (boundary (D := D) k).below ((boundary (D := D) k).cell c)) :
    (lowerRows sem j k hj hjA hk hkA hp hjk).E
      (GradeCutPairCarrier.old (boundary (D := D) k) (firstProfiles sem j k)
        (secondProfiles sem k) j k hj hjA hk hkA c)
      ⟨GradeCutPairCarrier.old (boundary (D := D) k) (firstProfiles sem j k)
        (secondProfiles sem k) j k hj hjA hk hkA d.1, by
          simpa only [GradeCutPairCarrier.old, GradeCutPairCarrier.cell_idx,
            GradeCutPairCarrier.idx] using d.2⟩ = (boundaryRows sem k).E c d :=
  CanonicalMixedGradeLayers.original_row (boundaryRows sem k) j hj hjA
    (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk c d

theorem consistent (hs : sem.IsConsistent) : (rows sem j k hj hjA hk hkA hp hjk).IsConsistent :=
  GradeCutPairRows.consistent D _ _ j k hj hjA hk hkA hp hjk.le sem _
    (overlap sem j k hj hjA hk hkA hp hjk) hs
    (CanonicalMixedGradeLayers.consistent (boundaryRows sem k) j hj hjA
      (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
      (GradeCutBoundary.consistent D k sem hs))

theorem old_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows sem j k hj hjA hk hkA hp hjk).E (old sem j k hj hjA hk hkA c)
      ⟨old sem j k hj hjA hk hkA d.1, by
        simpa only [old, GradeCutPairCarrier.old, GradeCutPairCarrier.cell_idx,
          GradeCutPairCarrier.idx] using d.2⟩ = sem.E c d :=
  GradeCutPairRows.old_row D _ _ j k hj hjA hk hkA hp hjk.le sem _ c d

theorem lower_row (c : Cell (lower sem j k hj hjA hk hkA))
    (d : (lower sem j k hj hjA hk hkA).below ((lower sem j k hj hjA hk hkA).cell c)) :
    (rows sem j k hj hjA hk hkA hp hjk).E (embed sem j k hj hjA hk hkA c)
      ⟨embed sem j k hj hjA hk hkA d.1, by
        simpa only [embed, GradeCutPairCarrier.embed_index] using d.2⟩ =
      (lowerRows sem j k hj hjA hk hkA hp hjk).E c d :=
  GradeCutPairRows.embedded_row D _ _ j k hj hjA hk hkA hp hjk.le sem _
    (overlap sem j k hj hjA hk hkA hp hjk) c d

variable {p : Cell D → ExtOrd} (hpr : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)

def lowerSection (G : Finset ExtOrd) (C : ExtOrd) : Cell (lower sem j k hj hjA hk hkA) → ExtOrd :=
  CanonicalMixedGradeLayers.sectionOf (boundaryRows sem k) j hj hjA (GradeCutBoundary.proper D k hp)
    k (GradeCutBoundary.grade_bound D k) hk hkA hjk
    (GradeCutBoundary.restrict_respects D k sem hpr)
    (fun d => ht (GradeCutBoundary.toCell D k d)) G C

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) : Cell (scheme sem j k hj hjA hk hkA) → ExtOrd :=
  GradeCutPairRows.glue D _ _ j k hj hjA hk hkA p
    (lowerSection sem j k hj hjA hk hkA hp hjk hpr ht G C)

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem section_old (d : Cell D) :
    sectionOf sem j k hj hjA hk hkA hp hjk hpr ht G C (old sem j k hj hjA hk hkA d) = p d :=
  GradeCutPairRows.glue_old D _ _ j k hj hjA hk hkA p _ d

theorem section_lower (hG : ∀ z ∈ G, SelfVis k z) (hC : SelfVis k C)
    (d : Cell (lower sem j k hj hjA hk hkA)) :
    sectionOf sem j k hj hjA hk hkA hp hjk hpr ht G C (embed sem j k hj hjA hk hkA d) =
      lowerSection sem j k hj hjA hk hkA hp hjk hpr ht G C d :=
  GradeCutPairRows.glue_embed D _ _ j k hj hjA hk hkA p _
    (CanonicalMixedGradeLayers.section_boundary (boundaryRows sem k) j hj hjA
      (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
      (GradeCutBoundary.restrict_respects D k sem hpr) _ hG hC) d

theorem section_lawful (hG : ∀ z ∈ G, SelfVis k z) (hC : SelfVis k C) :
    RespectsSemantics (rows sem j k hj hjA hk hkA hp hjk)
      (sectionOf sem j k hj hjA hk hkA hp hjk hpr ht G C) :=
  GradeCutPairRows.glue_respects D _ _ j k hj hjA hk hkA hp hjk.le sem _
    (overlap sem j k hj hjA hk hkA hp hjk) hpr
    (CanonicalMixedGradeLayers.section_lawful (boundaryRows sem k) j hj hjA
      (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
      (GradeCutBoundary.restrict_respects D k sem hpr) _ hG hC)
    (CanonicalMixedGradeLayers.section_boundary (boundaryRows sem k) j hj hjA
      (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
      (GradeCutBoundary.restrict_respects D k sem hpr) _ hG hC)

theorem section_bound (hC : SelfVis k C) (hb : ∀ d, p d ≤ C)
    (d : Cell (scheme sem j k hj hjA hk hkA)) :
    sectionOf sem j k hj hjA hk hkA hp hjk hpr ht G C d ≤ C := by
  unfold sectionOf GradeCutPairRows.glue
  rcases (GradeCutPairCarrier.occEquiv D _ _ j k hj hjA hk hkA).symm d with (a | q) | q
  · exact hb a
  all_goals
    exact CanonicalMixedGradeLayers.section_bound (boundaryRows sem k) j hj hjA
      (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
      (GradeCutBoundary.restrict_respects D k sem hpr) _ hC
      (fun a => hb (GradeCutBoundary.toCell D k a)) _

theorem section_supported {K : ℕ} (hkK : k ≤ K)
    (hCG : C ∈ G) (d : Cell (scheme sem j k hj hjA hk hkA)) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
      (sectionOf sem j k hj hjA hk hkA hp hjk hpr ht G C d) := by
  have hl (a : Cell (lower sem j k hj hjA hk hkA)) :
      OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
        (lowerSection sem j k hj hjA hk hkA hp hjk hpr ht G C a) := by
    rcases CanonicalMixedGradeLayers.section_supported (boundaryRows sem k) j hj hjA
      (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
      hkK hCG (GradeCutBoundary.restrict_respects D k sem hpr)
      (fun d => ht (GradeCutBoundary.toCell D k d)) a with hb | hm | ⟨e, i, hi, he⟩
    · exact Or.inl hb
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr ⟨GradeCutBoundary.toCell D k e, i, hi, he⟩)
  unfold sectionOf GradeCutPairRows.glue
  rcases (GradeCutPairCarrier.occEquiv D _ _ j k hj hjA hk hkA).symm d with (a | q) | q
  · change OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (p a)
    rcases ExtOrd.cases (p a) with hb | ht | ⟨v, hv⟩
    · exact Or.inl hb
    · exact Or.inr (Or.inr ⟨a, K, le_rfl, by rw [ht, extVisibilityReplace_top]⟩)
    · by_cases hi : finitePart v < K
      · exact Or.inr (Or.inr ⟨a, finitePart v, hi.le, by
          rw [hv, extVisibilityReplace_of_finitePart_lt hi, limitPart_add_finitePart]⟩)
      · exact Or.inr (Or.inr ⟨a, K, le_rfl, by
          rw [hv, extVisibilityReplace_of_le_finitePart (not_lt.mp hi)]⟩)
  · exact hl _
  · exact hl _

theorem section_agreement {q : Cell D → ExtOrd}
    (hqr : RespectsSemantics sem q) (htq : ∀ d, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis k z) (hC : SelfVis k C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf sem j k hj hjA hk hkA hp hjk hpr ht G C)
      (sectionOf sem j k hj hjA hk hkA hp hjk hqr htq G C) h := by
  have hl := CanonicalMixedGradeLayers.section_agreement (boundaryRows sem k) j hj hjA
    (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
    (GradeCutBoundary.restrict_respects D k sem hpr)
    (GradeCutBoundary.restrict_respects D k sem hqr)
    (fun d => ht (GradeCutBoundary.toCell D k d)) (fun d => htq (GradeCutBoundary.toCell D k d))
    hG hC hh hhC (fun d => hag (GradeCutBoundary.toCell D k d))
  intro d
  unfold sectionOf GradeCutPairRows.glue
  rcases (GradeCutPairCarrier.occEquiv D _ _ j k hj hjA hk hkA).symm d with (a | r) | r
  · exact hag a
  · exact hl _
  · exact hl _

/-- Ordinary whole-boundary sections also allow literal top, independently
of the proper-profile selected operator. There is no ambient-cap conclusion. -/
theorem exists_whole {p : Cell D → ExtOrd} (hpr : RespectsSemantics sem p) :
    ∃ r : Cell (scheme sem j k hj hjA hk hkA) → ExtOrd,
      RespectsSemantics (rows sem j k hj hjA hk hkA hp hjk) r ∧
      ∀ d, r (old sem j k hj hjA hk hkA d) = p d := by
  obtain ⟨u, hu, hread⟩ := CanonicalSections.exists_whole (boundaryRows sem k) j hj hjA
    (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
    (GradeCutBoundary.restrict_respects D k sem hpr)
  let all (d : Cell (lower sem j k hj hjA hk hkA)) :
      (lower sem j k hj hjA hk hkA).below (A, k) :=
    ⟨d, (lower sem j k hj hjA hk hkA).isPlan.subset_of_mem
        ((lower sem j k hj hjA hk hkA).scope_mem_plan d),
      GradeCutPairCarrier.small_grade D _ _ j k hj hjA hk hkA hjk.le d⟩
  let v := fun d => u (all d)
  have hv : RespectsSemantics (lowerRows sem j k hj hjA hk hkA hp hjk) v :=
    hu.toRespects (fun d => (all d).2)
  refine ⟨GradeCutPairRows.glue D _ _ j k hj hjA hk hkA p v,
    GradeCutPairRows.glue_respects D _ _ j k hj hjA hk hkA hp hjk.le sem _
      (overlap sem j k hj hjA hk hkA hp hjk) hpr hv ?_,
    GradeCutPairRows.glue_old D _ _ j k hj hjA hk hkA p v⟩
  exact hread

/-- Bottom-cap supply from one original proper face. Both boundary extension
calls are on the OLD semantics. In particular an active prescribed higher owner
is retained literally, not clipped away to make the lower completion possible. -/
theorem exists_section {I U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hIU : GradedLe I U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CoatomBoundaryExtension.CappedLift sem hIU)
    (hright : CoatomBoundaryExtension.CappedLift sem hOV)
    {p : D.below I → ExtOrd} (hpr : RespectsSemanticsBelow sem I p) :
    ∃ r : Cell (scheme sem j k hj hjA hk hkA) → ExtOrd,
      RespectsSemantics (rows sem j k hj hjA hk hkA hp hjk) r ∧
      ∀ d : D.below I, r (old sem j k hj hjA hk hkA d.1) = p d := by
  obtain ⟨b, hread⟩ := CoatomBoundaryExtension.section_left hIU hOU hOV hinter hleft hright p hpr
  obtain ⟨r, hr, hold⟩ := exists_whole sem j k hj hjA hk hkA hp hjk (b.whole_respects hcover)
  exact ⟨r, hr, fun d => (hold d.1).trans (hread d)⟩

end
end VaughtConjecture.Knight.CanonicalPairBoundary
