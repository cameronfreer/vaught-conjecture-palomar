/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSeedRows
public import VaughtConjecture.Knight.CanonicalProperOwnerSections

/-! # Decoded selected sections on the actual recursive seed

Retained proper owners may exceed grade three. Input lawfulness is required
only through the current outer grade; all original fields remain literal.
The decoded operator includes every seed controller at fixed outer parameters.
This is selected-section supply, not arbitrary-ambient lifting.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveSeedSections
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison
open CanonicalRecursiveSeedRows SharpWitnessComposition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card) (hp : ∀ d : Cell D, D.scope d ≠ A)

abbrev equiv (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, 3) J) :=
  HighLayerBountiful.equiv (predecessor sem hA) (Profile sem) 3 (by decide) hA J hJ

theorem respects_iff (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, 3) J)
    (p : (predecessor sem hA).below J → ExtOrd) :
    RespectsSemanticsBelow (predecessorRows sem hA hp) J p ↔
      RespectsSemanticsBelow (rows sem hA hp) J (p ∘ (equiv sem hA J hJ).symm) := by
  apply respects_iff_of_equiv (equiv sem hA J hJ)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell
      (predecessor sem hA) (Profile sem) 3 (by decide) hA J hJ d)).symm)
    (fun d e => ?_) (fun b d _ => (inherited_row sem hA hp b.1 d).symm) p
  simp only [CellScheme.scope, equiv, HighLayerBountiful.equiv_cell]

def properEquiv (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) :
    D.below J ≃ (carrier sem hA).below J :=
  (GradeCutPairCarrier.properEquiv D
    (CanonicalPairBoundary.firstProfiles sem 1 2) (CanonicalPairBoundary.secondProfiles sem 2)
    1 2 (by decide) (CanonicalPairLocalSections.one_le (two_le hA)) (by decide)
    (two_le hA) J hJ).trans (equiv sem hA J (fun h => hJ h.1))

theorem proper_respects_iff (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1)
    (p : D.below J → ExtOrd) :
    RespectsSemanticsBelow sem J p ↔ RespectsSemanticsBelow (rows sem hA hp) J
      (p ∘ (properEquiv sem hA J hJ).symm) :=
  (GradeCutPairRows.proper_respects_iff D _ _ 1 2 (by decide)
    (CanonicalPairLocalSections.one_le (two_le hA)) (by decide) (two_le hA) hp (by decide)
    sem (CanonicalPairLocalSections.smallRows sem (two_le hA) hp) J hJ p).trans
    (respects_iff sem hA hp J (fun h => hJ h.1) _)

theorem proper_lawful {J : Finset ι × ℕ} (hJ : ¬ A ⊆ J.1) {p : Cell D → ExtOrd}
    (hpr : RespectsSemanticsBelow sem J (fun d => p d.1))
    {r : Cell (carrier sem hA) → ExtOrd} (hread : ∀ d, r (boundary sem hA d) = p d) :
    RespectsSemanticsBelow (rows sem hA hp) J (fun d => r d.1) := by
  let e := properEquiv sem hA J hJ
  have he : (fun d : (carrier sem hA).below J => r d.1) =
      (fun d : D.below J => p d.1) ∘ e.symm := by
    funext d
    obtain ⟨a, rfl⟩ := e.surjective d
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact hread a.1
  rw [he]
  exact (proper_respects_iff sem hA hp J hJ _).mp hpr

theorem full_source_short (c : Cell (carrier sem hA)) (hc : (carrier sem hA).scope c = A)
    (d : (carrier sem hA).below ((carrier sem hA).cell c)) :
    Short ((carrier sem hA).grade c) ((rows sem hA hp).E c d) := by
  by_cases he : (carrier sem hA).cell c = (A, 3)
  · have q := (controllerEquiv sem hA hp).surjective ⟨c, he⟩
    obtain ⟨q, hq⟩ := q
    have hv : (controller sem hA q).1 = c := congrArg Subtype.val hq
    have hr := (data sem hA hp).row_new (controller sem hA q)
    subst c
    rw [hr]
    rw [show (carrier sem hA).grade (controller sem hA q).1 = 3 from
      congrArg Prod.snd (controller sem hA q).2]
    change Short 3 (source sem hA hp q d.1)
    exact source_short sem hA hp q d.1
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem hA)
      (Profile sem) 3 (by decide) hA c he
    obtain ⟨e, rfl⟩ := (ownerEquiv sem hA hp x).surjective d
    rw [inherited_row]
    have hi := SourceLayerCarrier.cell_toCell (predecessor sem hA) (Profile sem)
      3 (by decide) hA (.inl x)
    change Short ((carrier sem hA).grade (old sem hA x)) _
    rw [show (carrier sem hA).grade (old sem hA x) = (predecessor sem hA).grade x
      from congrArg Prod.snd hi]
    exact CanonicalProperOwnerSections.lower_full_short sem 3 (by decide) hA hp x
      ((congrArg Prod.fst hi).symm.trans hc) e

variable {K : ℕ} (hK : 3 ≤ K) {p : Cell D → ExtOrd}
variable (hpr : RespectsSemanticsBelow sem (A, K) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤)

abbrev normalized : Profile sem := CanonicalRecursiveInventory.encode sem 0
  (hpr.mono (show GradedLe (A, 3) (A, K) from ⟨Finset.Subset.refl _, hK⟩)) ht

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) (d : Cell (carrier sem hA)) : ExtOrd :=
  PairedSlotDecoder.decode 3 (values p) G C (source sem hA hp (normalized sem hK hpr ht) d)

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem section_boundary (hG : ∀ z ∈ G, SelfVis 3 z) (hC : SelfVis 3 C) (d : Cell D) :
    sectionOf sem hA hp hK hpr ht G C (boundary sem hA d) = p d := by
  rw [sectionOf, source_boundary]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_lawful (hG : ∀ z ∈ G, SelfVis 3 z) (hC : SelfVis 3 C) :
    RespectsSemanticsBelow (rows sem hA hp) (A, K)
      (fun d => sectionOf sem hA hp hK hpr ht G C d.1) := by
  have hproper (c : Cell (carrier sem hA)) (hc : (carrier sem hA).scope c ≠ A)
      (hg : (carrier sem hA).grade c ≤ K) :
      RespectsSemanticsBelow (rows sem hA hp) ((carrier sem hA).cell c)
        (fun d => sectionOf sem hA hp hK hpr ht G C d.1) := by
    exact proper_lawful sem hA hp
      (fun ha => hc (Finset.Subset.antisymm
        ((carrier sem hA).isPlan.subset_of_mem ((carrier sem hA).scope_mem_plan c)) ha))
      (hpr.mono ⟨(carrier sem hA).isPlan.subset_of_mem ((carrier sem hA).scope_mem_plan c), hg⟩)
      (section_boundary sem hA hp hK hpr ht hG hC)
  have hl : RespectsSemanticsBelow (rows sem hA hp) (A, 3)
      (fun d => sectionOf sem hA hp hK hpr ht G C d.1) := by
    apply (data sem hA hp).decoded_respects (controller sem hA (normalized sem hK hpr ht))
      le_rfl (PairedSlotDecoder.decode_witness hG hC) _
      (fun c hc => full_source_short sem hA hp c.1 hc)
    intro c hc
    have he : (carrier sem hA).cell c.1 ≠ (A, 3) := fun he => hc (congrArg Prod.fst he)
    have hr := ((data sem hA hp).old_respects_iff he).mp (hproper c.1 hc (c.2.2.trans hK))
    change RespectsSemanticsBelow (data sem hA hp).base _
      (fun d => PairedSlotDecoder.decode 3 (values p) G C
        ((data sem hA hp).profile _ d.1)) at hr
    simpa only [ScopedSourcePrefixLayer.Data.profile_old _ _
      ((data sem hA hp).below_old he _)] using hr
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  by_cases hc : (carrier sem hA).scope c.1 = A
  · have hg := RecursiveSourceCarrier.full_grade D (CanonicalRecursiveInventory.Profile sem)
      hp 3 hA c.1 hc
    exact hl.mono ⟨(carrier sem hA).isPlan.subset_of_mem
      ((carrier sem hA).scope_mem_plan c.1), hg⟩
  · exact hproper c.1 hc c.2.2

theorem section_bound (hC : SelfVis 3 C) (hb : ∀ d, p d ≤ C)
    (d : Cell (carrier sem hA)) : sectionOf sem hA hp hK hpr ht G C d ≤ C := by
  apply PairedSlotDecoder.decode_le hC
  intro a ha
  obtain ⟨d, hd⟩ := mem_values.mp ha
  simpa only [hd] using hb d

theorem section_supported {L : ℕ} (hL : 3 ≤ L) (hCG : C ∈ G)
    (d : Cell (carrier sem hA)) :
    OrbitPrefixSupport.Supported L (G : Set ExtOrd) p
      (sectionOf sem hA hp hK hpr ht G C d) := PairedSlotDecoder.decode_supported hL hCG _

theorem section_agreement {q : Cell D → ExtOrd}
    (hqr : RespectsSemanticsBelow sem (A, K) (fun d => q d.1)) (htq : ∀ d, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis 3 z) (hC : SelfVis 3 C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf sem hA hp hK hpr ht G C) (sectionOf sem hA hp hK hqr htq G C) h := by
  obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
    largestCommonCut_spec hG hC hC hh hhC hhC ht htq hag
  have hs := source_agreement_all sem hA hp
    (normalized sem hK hpr ht) (normalized sem hK hqr htq) heG heAgree
  exact hs.decode (PairedSlotDecoder.decode_witness hG hC).mono
    (PairedSlotDecoder.decode_witness hG hC).mono hpReach hqReach (fun d _ => hcompare _)

theorem upper_profile_lawful (j : ℕ) (q : CanonicalRecursiveInventory.UpperProfile sem j) :
    RespectsSemanticsBelow sem (A, j) (fun d => q.val d.1) := by
  have hr := (GradeCutBoundary.respects_iff D j sem (A, j) le_rfl _).mp
    (q.property.1.toBelow (A, j))
  convert hr using 1
  funext d
  exact (congrArg q.val (congrArg Subtype.val
    ((GradeCutBoundary.belowEquiv D j (A, j) le_rfl).apply_symm_apply d))).symm

/-- Catalogue identification where the older whole-boundary interface applies.
It preserves the complete vector, not just its current visible readings.
This is not an identification of independently ordered controller carriers. -/
def upperProfileEquiv (j : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ j) :
    CanonicalRecursiveInventory.UpperProfile sem j ≃
      CanonicalFieldLayer.Profile sem j (Cell D) id where
  toFun q := ⟨q.val, (upper_profile_lawful sem j q).toRespects
    (fun d => ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), hg d⟩), q.property.2⟩
  invFun q := ⟨q.val, GradeCutBoundary.restrict_respects D j sem q.property.1, q.property.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem upperProfileEquiv_val (j : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ j)
    (q : CanonicalRecursiveInventory.UpperProfile sem j) :
    (upperProfileEquiv sem j hg q).val = q.val := rfl

/-- Construct the successor's selected lower section on the actual recursive
seed. Properness comes from the catalogue, not an extra request hypothesis. -/
def nextSection (j : ℕ) (hj : 3 ≤ j) (q : CanonicalRecursiveInventory.UpperProfile sem j) :
    Cell (carrier sem hA) → ExtOrd :=
  sectionOf sem hA hp hj (upper_profile_lawful sem j q) q.property.2.2
    (sourceGrid j (Fintype.card (Cell D))) (CanonicalFieldLayer.ceiling j (Cell D))

theorem next_lawful (j : ℕ) (hj : 3 ≤ j) (q : CanonicalRecursiveInventory.UpperProfile sem j) :
    RespectsSemanticsBelow (rows sem hA hp) (A, j) (fun d => nextSection sem hA hp j hj q d.1) :=
  section_lawful sem hA hp hj (upper_profile_lawful sem j q) q.property.2.2
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) hj)
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) hj)

theorem next_boundary (j : ℕ) (hj : 3 ≤ j) (q : CanonicalRecursiveInventory.UpperProfile sem j)
    (d : Cell D) : nextSection sem hA hp j hj q (boundary sem hA d) = q.val d :=
  section_boundary sem hA hp hj (upper_profile_lawful sem j q) q.property.2.2
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) hj)
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) hj) d

theorem next_bound (j : ℕ) (hj : 3 ≤ j) (q : CanonicalRecursiveInventory.UpperProfile sem j)
    (d : Cell (carrier sem hA)) :
    nextSection sem hA hp j hj q d ≤ CanonicalFieldLayer.ceiling j (Cell D) :=
  section_bound sem hA hp hj (upper_profile_lawful sem j q) q.property.2.2
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) hj)
    (CanonicalFieldLayer.profile_bound (GradeCutBoundary.rows D j sem) j
      (Cell D) (GradeCutBoundary.toCell D j) q) d

theorem next_supported (j : ℕ) (hj : 3 ≤ j) (q : CanonicalRecursiveInventory.UpperProfile sem j)
    (d : Cell (carrier sem hA)) :
    OrbitPrefixSupport.Supported j (sourceGrid j (Fintype.card (Cell D)) : Set ExtOrd) q.val
      (nextSection sem hA hp j hj q d) :=
  section_supported sem hA hp hj (upper_profile_lawful sem j q) q.property.2.2 hj
    (sourceGrid_endpoint le_rfl) d

theorem next_agreement (j : ℕ) (hj : 3 ≤ j)
    (p q : CanonicalRecursiveInventory.UpperProfile sem j) {h : ExtOrd}
    (hh : h ∈ sourceGrid j (Fintype.card (Cell D))) (hag : Agree p.val q.val h) :
    Agree (nextSection sem hA hp j hj p) (nextSection sem hA hp j hj q) h :=
  section_agreement sem hA hp hj (upper_profile_lawful sem j p) p.property.2.2
    (upper_profile_lawful sem j q) q.property.2.2
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) hj)
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) hj)
    hh (CanonicalFieldLayer.grid_bound j (Cell D) hh) hag

end
end VaughtConjecture.Knight.CanonicalRecursiveSeedSections
