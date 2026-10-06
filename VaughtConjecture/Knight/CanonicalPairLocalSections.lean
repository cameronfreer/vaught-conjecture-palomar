/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalPairBoundary
public import VaughtConjecture.Knight.ScopedSourcePrefixLayer

/-! # Selected seed sections from actual current-domain lawfulness

The old profile need not be lawful at future higher proper owners. Their values
remain literal, but only owners through `K` are used in the current source row.
Both seed controller layers retain their existing rows and catalogues.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalPairLocalSections
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison
open CanonicalPairBoundary
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 2 ≤ A.card) (hp : ∀ d : Cell D, D.scope d ≠ A)
abbrev one_le := (by decide : 1 ≤ 2).trans hA
abbrev carrier := scheme sem 1 2 (by decide) (one_le hA) (by decide) hA
abbrev semantics := rows sem 1 2 (by decide) (one_le hA) (by decide) hA hp (by decide)
abbrev original := old sem 1 2 (by decide) (one_le hA) (by decide) hA
abbrev small := lower sem 1 2 (by decide) (one_le hA) (by decide) hA
abbrev smallRows := lowerRows sem 1 2 (by decide) (one_le hA) (by decide) hA hp (by decide)

variable {K : ℕ} (hK : 2 ≤ K) {p : Cell D → ExtOrd}
variable (hpr : RespectsSemanticsBelow sem (A, K) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤)

include hK hpr in
theorem cut_lawful : RespectsSemantics (GradeCutBoundary.rows D 2 sem)
    (fun d => p (GradeCutBoundary.toCell D 2 d)) := by
  have hr := GradeCutBoundary.pullback_respects D 2 sem le_rfl
    (hpr.mono (show GradedLe (A, 2) (A, K) from ⟨Finset.Subset.refl _, hK⟩))
  exact hr.toRespects (fun d =>
    ⟨D.isPlan.subset_of_mem (D.scope_mem_plan _), GradeCutBoundary.grade_bound D 2 d⟩)

def smallSection (G : Finset ExtOrd) (C : ExtOrd) : Cell (small sem hA) → ExtOrd :=
  CanonicalMixedGradeLayers.sectionOf (GradeCutBoundary.rows D 2 sem) 1 (by decide)
    (one_le hA) (GradeCutBoundary.proper D 2 hp) 2 (GradeCutBoundary.grade_bound D 2)
    (by decide) hA (by decide) (cut_lawful sem hK hpr)
    (fun d => ht (GradeCutBoundary.toCell D 2 d)) G C

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) : Cell (carrier sem hA) → ExtOrd :=
  GradeCutPairRows.glue D _ _ 1 2 (by decide) (one_le hA) (by decide) hA p
    (smallSection sem hA hp hK hpr ht G C)

theorem section_old {G : Finset ExtOrd} {C : ExtOrd} (d : Cell D) :
    sectionOf sem hA hp hK hpr ht G C (original sem hA d) = p d :=
  GradeCutPairRows.glue_old D _ _ 1 2 (by decide) (one_le hA) (by decide) hA p _ d

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem small_readback (hG : ∀ z ∈ G, SelfVis 2 z) (hC : SelfVis 2 C)
    (d : Cell (GradeCutBoundary.scheme D 2)) :
    smallSection sem hA hp hK hpr ht G C
      (GradeCutPairCarrier.old (GradeCutBoundary.scheme D 2) _ _ 1 2
        (by decide) (one_le hA) (by decide) hA d) = p (GradeCutBoundary.toCell D 2 d) :=
  CanonicalMixedGradeLayers.section_boundary (GradeCutBoundary.rows D 2 sem) 1 (by decide)
    (one_le hA) (GradeCutBoundary.proper D 2 hp) 2 (GradeCutBoundary.grade_bound D 2)
    (by decide) hA (by decide) (cut_lawful sem hK hpr) _ hG hC d

theorem section_embedded (hG : ∀ z ∈ G, SelfVis 2 z) (hC : SelfVis 2 C)
    (d : Cell (small sem hA)) :
    sectionOf sem hA hp hK hpr ht G C
      (embed sem 1 2 (by decide) (one_le hA) (by decide) hA d) =
      smallSection sem hA hp hK hpr ht G C d :=
  GradeCutPairRows.glue_embed D _ _ 1 2 (by decide) (one_le hA) (by decide) hA p _
    (small_readback sem hA hp hK hpr ht hG hC) d

theorem section_lawful (hG : ∀ z ∈ G, SelfVis 2 z) (hC : SelfVis 2 C) :
    RespectsSemanticsBelow (semantics sem hA hp) (A, K)
      (fun d => sectionOf sem hA hp hK hpr ht G C d.1) := by
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  obtain ⟨x, hx⟩ := (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
    (one_le hA) (by decide) hA).surjective c.1
  have hc := c.2
  rw [← hx] at hc ⊢
  change RespectsSemanticsBelow (semantics sem hA hp)
    ((carrier sem hA).cell (GradeCutPairCarrier.cell D _ _ 1 2
      (by decide) (one_le hA) (by decide) hA x))
    (fun d => sectionOf sem hA hp hK hpr ht G C d.1)
  have hlow (J : Finset ι × ℕ) (hJ : J.2 ≤ 2) :
      RespectsSemanticsBelow (semantics sem hA hp) J
        (fun d => sectionOf sem hA hp hK hpr ht G C d.1) := by
    have hr := CanonicalMixedGradeLayers.section_lawful (GradeCutBoundary.rows D 2 sem)
      1 (by decide) (one_le hA) (GradeCutBoundary.proper D 2 hp) 2
      (GradeCutBoundary.grade_bound D 2) (by decide) hA (by decide)
      (cut_lawful sem hK hpr) (fun d => ht (GradeCutBoundary.toCell D 2 d)) hG hC
    have hs := (GradeCutPairRows.lower_respects_iff D _ _ 1 2 (by decide)
      (one_le hA) (by decide) hA hp (by decide) sem (smallRows sem hA hp)
      (overlap sem 1 2 (by decide) (one_le hA) (by decide) hA hp (by decide)) J hJ _).mp
      (hr.toBelow J)
    convert hs using 1
    funext d
    let e := GradeCutPairCarrier.belowEquiv D (firstProfiles sem 1 2) (secondProfiles sem 2)
      1 2 (by decide) (one_le hA) (by decide) hA J hJ
    exact (congrArg (sectionOf sem hA hp hK hpr ht G C)
      (congrArg Subtype.val (e.apply_symm_apply d))).symm.trans
      (section_embedded sem hA hp hK hpr ht hG hC _)
  rcases x with (a | q) | q
  · have ha : GradedLe (D.cell a) (A, K) := by
      change GradedLe ((carrier sem hA).cell (GradeCutPairCarrier.cell D _ _ 1 2
        (by decide) (one_le hA) (by decide) hA (.inl (.inl a)))) (A, K) at hc
      simpa only [GradeCutPairCarrier.cell_idx, GradeCutPairCarrier.idx] using hc
    let e := GradeCutPairRows.ownerEquiv D (firstProfiles sem 1 2) (secondProfiles sem 2)
      1 2 (by decide)
      (one_le hA) (by decide) hA hp a
    have hr := (GradeCutPairRows.proper_respects_iff D _ _ 1 2 (by decide)
      (one_le hA) (by decide) hA hp (by decide) sem (smallRows sem hA hp)
      (D.cell a) (GradeCutLayerRows.proper_scope D hp a) _).mp (hpr.mono ha)
    have hs := GradeCutLayerRows.cast_respects _ _
      (GradeCutPairCarrier.cell_idx D (firstProfiles sem 1 2) (secondProfiles sem 2)
        1 2 (by decide) (one_le hA)
        (by decide) hA (.inl (.inl a))).symm hr
    change RespectsSemanticsBelow (semantics sem hA hp) _ _ at hs
    convert hs using 1
    funext d
    let d' : (carrier sem hA).below (D.cell a) := ⟨d.1, by
      simpa only [GradeCutPairCarrier.cell_idx, GradeCutPairCarrier.idx] using d.2⟩
    exact (congrArg (sectionOf sem hA hp hK hpr ht G C)
      (congrArg Subtype.val (e.apply_symm_apply d'))).symm.trans
      (section_old sem hA hp hK hpr ht (e.symm d').1)
  · exact hlow _ (by rw [GradeCutPairCarrier.cell_idx]; exact (by decide : 1 ≤ 2))
  · exact hlow _ (by rw [GradeCutPairCarrier.cell_idx]; exact le_rfl)

theorem section_bound (hC : SelfVis 2 C) (hb : ∀ d, p d ≤ C)
    (d : Cell (carrier sem hA)) : sectionOf sem hA hp hK hpr ht G C d ≤ C := by
  unfold sectionOf GradeCutPairRows.glue
  rcases (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
    (one_le hA) (by decide) hA).symm d with (a | q) | q
  · exact hb a
  all_goals
    exact CanonicalMixedGradeLayers.section_bound (GradeCutBoundary.rows D 2 sem)
      1 (by decide) (one_le hA) (GradeCutBoundary.proper D 2 hp) 2
      (GradeCutBoundary.grade_bound D 2) (by decide) hA (by decide)
      (cut_lawful sem hK hpr) _ hC (fun a => hb (GradeCutBoundary.toCell D 2 a)) _

theorem section_supported {L : ℕ} (hL : 2 ≤ L) (hCG : C ∈ G)
    (d : Cell (carrier sem hA)) :
    OrbitPrefixSupport.Supported L (G : Set ExtOrd) p
      (sectionOf sem hA hp hK hpr ht G C d) := by
  have hl (a : Cell (small sem hA)) : OrbitPrefixSupport.Supported L (G : Set ExtOrd) p
      (smallSection sem hA hp hK hpr ht G C a) := by
    rcases CanonicalMixedGradeLayers.section_supported (GradeCutBoundary.rows D 2 sem)
      1 (by decide) (one_le hA) (GradeCutBoundary.proper D 2 hp) 2
      (GradeCutBoundary.grade_bound D 2) (by decide) hA (by decide) hL hCG
      (cut_lawful sem hK hpr) (fun d => ht (GradeCutBoundary.toCell D 2 d)) a with
      hb | hm | ⟨e, i, hi, he⟩
    · exact Or.inl hb
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr ⟨GradeCutBoundary.toCell D 2 e, i, hi, he⟩)
  unfold sectionOf GradeCutPairRows.glue
  rcases (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
    (one_le hA) (by decide) hA).symm d with (a | q) | q
  · change OrbitPrefixSupport.Supported L (G : Set ExtOrd) p (p a)
    rcases ExtOrd.cases (p a) with hb | ht | ⟨v, hv⟩
    · exact Or.inl hb
    · exact Or.inr (Or.inr ⟨a, L, le_rfl, by rw [ht, extVisibilityReplace_top]⟩)
    · by_cases hi : finitePart v < L
      · exact Or.inr (Or.inr ⟨a, finitePart v, hi.le, by
          rw [hv, extVisibilityReplace_of_finitePart_lt hi, limitPart_add_finitePart]⟩)
      · exact Or.inr (Or.inr ⟨a, L, le_rfl, by
          rw [hv, extVisibilityReplace_of_le_finitePart (not_lt.mp hi)]⟩)
  · exact hl _
  · exact hl _

theorem section_agreement {q : Cell D → ExtOrd}
    (hqr : RespectsSemanticsBelow sem (A, K) (fun d => q d.1)) (htq : ∀ d, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis 2 z) (hC : SelfVis 2 C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf sem hA hp hK hpr ht G C) (sectionOf sem hA hp hK hqr htq G C) h := by
  have hl := CanonicalMixedGradeLayers.section_agreement (GradeCutBoundary.rows D 2 sem)
    1 (by decide) (one_le hA) (GradeCutBoundary.proper D 2 hp) 2
    (GradeCutBoundary.grade_bound D 2) (by decide) hA (by decide)
    (cut_lawful sem hK hpr) (cut_lawful sem hK hqr)
    (fun d => ht (GradeCutBoundary.toCell D 2 d))
    (fun d => htq (GradeCutBoundary.toCell D 2 d)) hG hC hh hhC
    (fun d => hag (GradeCutBoundary.toCell D 2 d))
  intro d
  unfold sectionOf GradeCutPairRows.glue
  rcases (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
    (one_le hA) (by decide) hA).symm d with (a | r) | r
  · exact hag a
  · exact hl _
  · exact hl _

end
end VaughtConjecture.Knight.CanonicalPairLocalSections
