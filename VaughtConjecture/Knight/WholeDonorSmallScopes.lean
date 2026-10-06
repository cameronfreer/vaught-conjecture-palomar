/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorOrdinaryLift
public import VaughtConjecture.Knight.CanonicalOneCoatom
public import VaughtConjecture.Knight.OrdinaryScopeMute

/-! # The actual height-one and height-two ordinary scope steps

Generalize the small seeds to placed legal input faces. Each lifting premise is
derived from those inputs. The selected operators use the existing rows and a
fixed external grid and ceiling; neither auxiliary values nor a chosen ambient
are substituted for arbitrary lawful lifting inputs.

These are local scope operations. Relocation into a larger ambient inventory and
iteration over an attached plan remain separate from these theorems.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.WholeDonorSmallScopes
open AmalgamationPlan Transform Value ExtOrd SourcePrefixRows OrbitPrefixSupport
open WholeDonorOrdinarySections WholeDonorOrdinaryLift
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
variable {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)
variable (hBA : B ≠ A) (hCA : C ≠ A)

include hBA hCA in
/-- Proper boundary geometry supplies the predecessor height in completed scopes. -/
theorem boundary_grade {k : ℕ} (hA : A.card ≤ k + 1) (d : Cell I.boundary) :
    I.boundary.grade d ≤ k := by
  have hs := I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan d)
  have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hs, proper_boundary I hBA hCA d⟩)
  have hg := I.boundary.grade_le_card_scope d
  omega

-- The same bottom catalogue member used by SmallCoatomSeeds, with arbitrary
-- placed point and field inventories rather than fixed Fin 2 geometry.
private def bottomProfile {X : Type*} [Fintype X] (j : ℕ) (occ : Cell I.boundary → X) :
    CanonicalFieldLayer.Profile I.rows j X occ := by
  refine ⟨fun _ => ⊥, ⟨?_, ?_, ?_⟩, rfl, fun _ => bot_ne_top⟩
  · intro d
    exact (extVisibilityReplace_bot _ _).symm
  · intro c
    simpa only [Function.comp_apply, min_self] using TransformsTo.to_bot (I.rows.E c)
  · intro _ b _ _
    exact ⟨b, rfl, le_rfl⟩

section One
variable (hA : 1 ≤ A.card) (hg : ∀ d : Cell I.boundary, I.boundary.grade d ≤ 1)

abbrev oneCarrier := CanonicalOneCoatom.scheme I.rows hA
abbrev oneRows := CanonicalOneCoatom.rows I.rows hA (proper_boundary I hBA hCA) hg
abbrev oneOld := CanonicalOneCoatom.old I.rows hA

theorem one_consistent : (oneRows I hBA hCA hA hg).IsConsistent :=
  CanonicalFieldLayer.consistent I.rows 1 (Cell I.boundary) id (by decide) hA
    (proper_boundary I hBA hCA) hg I.consistent

theorem one_coded : (oneRows I hBA hCA hA hg).IsCoded :=
  CanonicalSeedCoding.fieldLayer I.rows 1 (Cell I.boundary) id (by decide) hA
    (proper_boundary I hBA hCA) hg I.coded

include hBA hCA hg in
theorem one_grade (d : Cell (oneCarrier I hA)) : (oneCarrier I hA).grade d ≤ 1 :=
  (CanonicalFieldLayer.data I.rows 1 (Cell I.boundary) id (by decide) hA
    (proper_boundary I hBA hCA) hg).max_grade d

theorem one_row (c : Cell I.boundary) (d : I.boundary.below (I.boundary.cell c)) :
    (oneRows I hBA hCA hA hg).E (oneOld I hA c)
      (CanonicalFieldLayer.ownerEquiv I.rows 1 (Cell I.boundary) id (by decide) hA
        (proper_boundary I hBA hCA) c d) = I.rows.E c d :=
  CanonicalFieldLayer.inherited_row I.rows 1 (Cell I.boundary) id (by decide) hA
    (proper_boundary I hBA hCA) hg c d

theorem one_short (c : Cell (oneCarrier I hA)) (hc : (oneCarrier I hA).scope c = A)
    (d : (oneCarrier I hA).below ((oneCarrier I hA).cell c)) :
    SharpWitnessComposition.Short ((oneCarrier I hA).grade c)
      ((oneRows I hBA hCA hA hg).E c d) :=
  CanonicalFieldLayer.full_source_short I.rows 1 (Cell I.boundary) id (by decide) hA
    (proper_boundary I hBA hCA) hg c hc d

theorem one_bountiful (hB : 1 ≤ B.card) (hC : 1 ≤ C.card)
    (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C) :
    (oneRows I hBA hCA hA hg).IsBountiful :=
  CanonicalOneCoatom.bountiful I.rows hA (proper_boundary I hBA hCA) hg
    (old_lifts I hcover) (left_mem I) (right_mem I) hBA hCA hB hC (overlap_mem I)
    hcover (fun _ hS hSA hSc => proper_complete I hcover hS hSA (by decide) hSc)

theorem one_complete_through
    (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C) (J : Finset ι × ℕ)
    (hJ : J ∈ Plan.gradedPlan (oneCarrier I hA).plan) (hj : J.2 ≤ 1) :
    ∃ d, (oneCarrier I hA).cell d = J := by
  have hj1 : J.2 = 1 := by have := (Plan.mem_gradedPlan.mp hJ).2.1; omega
  by_cases hs : J.1 = A
  · let q := bottomProfile I 1 id
    exact ⟨(CanonicalFieldLayer.controller I.rows 1 (Cell I.boundary) id
      (by decide) hA q).1,
      (CanonicalFieldLayer.controller I.rows 1 (Cell I.boundary) id
        (by decide) hA q).2.trans (Prod.ext hs.symm hj1.symm)⟩
  · have hm := Plan.mem_gradedPlan.mp hJ
    obtain ⟨d, hd⟩ := proper_complete I hcover hm.1 hs hm.2.1 hm.2.2
    exact ⟨oneOld I hA d, (SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)).trans hd⟩

/-- Independent section supply includes literal top, unlike the proper-profile
selected renderer below. -/
theorem one_exists_whole {p : Cell I.boundary → ExtOrd} (hp : RespectsSemantics I.rows p) :
    ∃ r, RespectsSemantics (oneRows I hBA hCA hA hg) r ∧ ∀ d, r (oneOld I hA d) = p d :=
  CanonicalOneCoatom.exists_whole I.rows hA (proper_boundary I hBA hCA) hg hp

variable {p : Cell I.boundary → ExtOrd} (hp : RespectsSemantics I.rows p) (ht : ∀ d, p d ≠ ⊤)

def oneSection (G : Finset ExtOrd) (θ : ExtOrd) : Cell (oneCarrier I hA) → ExtOrd :=
  CanonicalFieldLayer.sectionOf I.rows 1 (Cell I.boundary) id (by decide) hA
    (proper_boundary I hBA hCA) hg hp ht G θ

variable {G : Finset ExtOrd} {θ : ExtOrd}

theorem one_readback (hG : ∀ z ∈ G, SelfVis 1 z) (hθ : SelfVis 1 θ) (d : Cell I.boundary) :
    oneSection I hBA hCA hA hg hp ht G θ (oneOld I hA d) = p d :=
  CanonicalFieldLayer.section_old I.rows 1 (Cell I.boundary) id (by decide) hA
    (proper_boundary I hBA hCA) hg hp ht hG hθ d

theorem one_lawful (hG : ∀ z ∈ G, SelfVis 1 z) (hθ : SelfVis 1 θ) :
    RespectsSemantics (oneRows I hBA hCA hA hg) (oneSection I hBA hCA hA hg hp ht G θ) :=
  CanonicalFieldLayer.section_lawful I.rows 1 (Cell I.boundary) id (by decide) hA
    (proper_boundary I hBA hCA) hg hp ht hG hθ

theorem one_bound (hθ : SelfVis 1 θ) (hb : ∀ d, p d ≤ θ) (d : Cell (oneCarrier I hA)) :
    oneSection I hBA hCA hA hg hp ht G θ d ≤ θ :=
  CanonicalFieldLayer.section_bound I.rows 1 (Cell I.boundary) id (by decide) hA
    (proper_boundary I hBA hCA) hg hp ht hθ hb d

theorem one_supported {X : Type*} {v : X → ExtOrd} {K : ℕ}
    (hK : 1 ≤ K) (hG : ∀ z ∈ G, SelfVis K z) (hθ : θ ∈ G)
    (hs : ∀ d, Supported K (G : Set ExtOrd) v (p d)) (d : Cell (oneCarrier I hA)) :
    Supported K (G : Set ExtOrd) v (oneSection I hBA hCA hA hg hp ht G θ d) :=
  (CanonicalFieldLayer.section_supported I.rows 1 (Cell I.boundary) id (by decide) hA
    (proper_boundary I hBA hCA) hg hp ht hK hθ d).substitute hG hs

theorem one_agreement {q : Cell I.boundary → ExtOrd} (hq : RespectsSemantics I.rows q)
    (htq : ∀ d, q d ≠ ⊤) {γ : ExtOrd} (hG : ∀ z ∈ G, SelfVis 1 z) (hθ : SelfVis 1 θ)
    (hγ : γ ∈ G) (hγθ : γ ≤ θ) (hag : Agree p q γ) :
    Agree (oneSection I hBA hCA hA hg hp ht G θ) (oneSection I hBA hCA hA hg hq htq G θ) γ :=
  CanonicalFieldLayer.section_agreement I.rows 1 (Cell I.boundary) id (by decide) hA
    (proper_boundary I hBA hCA) hg hp ht hq htq hG hθ hγ hγθ hag

end One

section Two
variable (hA : 2 ≤ A.card) (hg : ∀ d : Cell I.boundary, I.boundary.grade d ≤ 2)

abbrev twoCarrier := CanonicalPairLocalSections.carrier I.rows hA
abbrev twoRows := CanonicalPairLocalSections.semantics I.rows hA (proper_boundary I hBA hCA)
abbrev twoOld := CanonicalPairLocalSections.original I.rows hA

theorem two_consistent : (twoRows I hBA hCA hA).IsConsistent :=
  CanonicalPairBoundary.consistent I.rows 1 2 (by decide) (by omega) (by decide) hA
    (proper_boundary I hBA hCA) (by decide) I.consistent

theorem two_coded : (twoRows I hBA hCA hA).IsCoded :=
  CanonicalSeedCoding.pair I.rows hA (proper_boundary I hBA hCA) I.coded

include hg in
theorem two_grade (d : Cell (twoCarrier I hA)) : (twoCarrier I hA).grade d ≤ 2 :=
  CanonicalRecursiveCoverage.grade_bound I.rows 2 hA hg d

theorem two_row (c : Cell I.boundary) (d : I.boundary.below (I.boundary.cell c)) :
    (twoRows I hBA hCA hA).E (twoOld I hA c)
      ⟨twoOld I hA d.1, by
        simpa only [twoOld, CanonicalPairLocalSections.original, CanonicalPairBoundary.old,
          GradeCutPairCarrier.old, GradeCutPairCarrier.cell_idx,
          GradeCutPairCarrier.idx] using d.2⟩ =
      I.rows.E c d :=
  GradeCutPairRows.old_row I.boundary _ _ 1 2 (by decide)
    (CanonicalPairLocalSections.one_le hA) (by decide) hA (proper_boundary I hBA hCA)
    (by decide) I.rows
    (CanonicalPairLocalSections.smallRows I.rows hA (proper_boundary I hBA hCA)) c d

/-- No inherited row is required to be short. The three-point completion is
the height-two case of the same checked seed-row calculation. -/
theorem two_short (h3A : 3 ≤ A.card) (c : Cell (twoCarrier I hA))
    (hc : (twoCarrier I hA).scope c = A)
    (d : (twoCarrier I hA).below ((twoCarrier I hA).cell c)) :
    SharpWitnessComposition.Short ((twoCarrier I hA).grade c)
      ((twoRows I hBA hCA hA).E c d) :=
  CanonicalProperOwnerSections.lower_full_short I.rows 3 (by decide) h3A
    (proper_boundary I hBA hCA) c hc d

include hg in
theorem two_bountiful (hB : 2 ≤ B.card) (hC : 2 ≤ C.card)
    (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C) :
    (twoRows I hBA hCA hA).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (two_grade I hA hg) (by decide : 0 < 2)
  intro S T j hS hT hj hST
  exact CanonicalPairLowerLifting.lower_lift I.rows (proper_boundary I hBA hCA) hA
    (old_lifts I hcover) (left_mem I) (right_mem I) hBA hCA hB hC (overlap_mem I) hcover
    (fun _ hS hSA _ hi hiS _ => proper_complete I hcover hS hSA hi hiS)
    hS hT ⟨hST, le_rfl⟩ hj

theorem two_complete_through
    (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C) (J : Finset ι × ℕ)
    (hJ : J ∈ Plan.gradedPlan (twoCarrier I hA).plan) (hj : J.2 ≤ 2) :
    ∃ d, (twoCarrier I hA).cell d = J :=
  CanonicalRecursiveCoverage.complete_through I.rows 2 hA
    (fun _ hJ hJA => proper_complete I hcover (Plan.mem_gradedPlan.mp hJ).1 hJA
      (Plan.mem_gradedPlan.mp hJ).2.1 (Plan.mem_gradedPlan.mp hJ).2.2) J hJ hj

theorem two_exists_whole {p : Cell I.boundary → ExtOrd} (hp : RespectsSemantics I.rows p) :
    ∃ r, RespectsSemantics (twoRows I hBA hCA hA) r ∧ ∀ d, r (twoOld I hA d) = p d :=
  CanonicalPairBoundary.exists_whole I.rows 1 2 (by decide)
    (CanonicalPairLocalSections.one_le hA) (by decide) hA (proper_boundary I hBA hCA)
    (by decide) hp

variable {p : Cell I.boundary → ExtOrd} (hp : RespectsSemantics I.rows p) (ht : ∀ d, p d ≠ ⊤)

def twoSection (G : Finset ExtOrd) (θ : ExtOrd) : Cell (twoCarrier I hA) → ExtOrd :=
  CanonicalPairLocalSections.sectionOf I.rows hA (proper_boundary I hBA hCA) hA
    (hp.toBelow (A, A.card)) ht G θ

variable {G : Finset ExtOrd} {θ : ExtOrd}

theorem two_readback (d : Cell I.boundary) :
    twoSection I hBA hCA hA hp ht G θ (twoOld I hA d) = p d :=
  CanonicalPairLocalSections.section_old I.rows hA (proper_boundary I hBA hCA) hA _ ht d

theorem two_lawful (hG : ∀ z ∈ G, SelfVis 2 z) (hθ : SelfVis 2 θ) :
    RespectsSemantics (twoRows I hBA hCA hA) (twoSection I hBA hCA hA hp ht G θ) := by
  apply (CanonicalPairLocalSections.section_lawful I.rows hA (proper_boundary I hBA hCA)
    hA (hp.toBelow (A, A.card)) ht hG hθ).toRespects
  intro d
  exact ⟨(twoCarrier I hA).isPlan.subset_of_mem ((twoCarrier I hA).scope_mem_plan d),
    ((twoCarrier I hA).grade_le_card_scope d).trans
      (Finset.card_le_card
        ((twoCarrier I hA).isPlan.subset_of_mem ((twoCarrier I hA).scope_mem_plan d)))⟩

theorem two_bound (hθ : SelfVis 2 θ) (hb : ∀ d, p d ≤ θ) (d : Cell (twoCarrier I hA)) :
    twoSection I hBA hCA hA hp ht G θ d ≤ θ :=
  CanonicalPairLocalSections.section_bound I.rows hA (proper_boundary I hBA hCA) hA
    (hp.toBelow (A, A.card)) ht hθ hb d

theorem two_supported {X : Type*} {v : X → ExtOrd} {K : ℕ}
    (hK : 2 ≤ K) (hG : ∀ z ∈ G, SelfVis K z) (hθ : θ ∈ G)
    (hs : ∀ d, Supported K (G : Set ExtOrd) v (p d)) (d : Cell (twoCarrier I hA)) :
    Supported K (G : Set ExtOrd) v (twoSection I hBA hCA hA hp ht G θ d) :=
  (CanonicalPairLocalSections.section_supported I.rows hA (proper_boundary I hBA hCA) hA
    (hp.toBelow (A, A.card)) ht hK hθ d).substitute hG hs

theorem two_agreement {q : Cell I.boundary → ExtOrd} (hq : RespectsSemantics I.rows q)
    (htq : ∀ d, q d ≠ ⊤) {γ : ExtOrd} (hG : ∀ z ∈ G, SelfVis 2 z) (hθ : SelfVis 2 θ)
    (hγ : γ ∈ G) (hγθ : γ ≤ θ) (hag : Agree p q γ) :
    Agree (twoSection I hBA hCA hA hp ht G θ) (twoSection I hBA hCA hA hq htq G θ) γ :=
  CanonicalPairLocalSections.section_agreement I.rows hA (proper_boundary I hBA hCA) hA
    (hp.toBelow (A, A.card)) ht (hq.toBelow (A, A.card)) htq hG hθ hγ hγθ hag

end Two
end
end VaughtConjecture.Knight.WholeDonorSmallScopes
