/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.CanonicalRecursiveLiteralRows
public import VaughtConjecture.Knight.OrbitSupportSubstitution

/-! # Ordinary selected sections over two literal input faces

This is the first scope step for new31, independent of LOW/HIGH catalogues.
The original schemes supply consistency and lawful input sections. The ordinary
grade recursion constructs the output rows and all selected-section receipts.
One fixed external grid and ceiling are used, and support is stated over the two
original occurrence vectors, not over unidentified intermediate coordinates.

This module does not fill missing proper mixed scopes. Inherited-target lifting
is transported, but full mixed-target lifting still needs the scope induction.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.WholeDonorOrdinarySections
open AmalgamationPlan Transform Value ExtOrd SourcePrefixRows OrbitPrefixSupport
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
variable {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)

theorem covered (d : Cell I.boundary) :
    (∃ c, I.leftFace.map c = d) ∨ ∃ c, I.rightFace.map c = d :=
  OrderedFaceBoundaryRows.covered I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le d

/-- The scalar union preserves properness without imposing any visibility
condition on inherited labels. -/
theorem paste_proper {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
    (htp : ∀ d, p d ≠ ⊤) (htq : ∀ d, q d ≠ ⊤)
    (hroot : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∀ d, I.paste p q d ≠ ⊤ := by
  intro d
  rcases covered I d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (I.paste_left p q c) ▸ htp c
  · exact (I.paste_right p q hroot c) ▸ htq c

theorem paste_bound {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
    {θ : ExtOrd} (hp : ∀ d, p d ≤ θ) (hq : ∀ d, q d ≤ θ)
    (hroot : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∀ d, I.paste p q d ≤ θ := by
  intro d
  rcases covered I d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (I.paste_left p q c) ▸ hp c
  · exact (I.paste_right p q hroot c) ▸ hq c

theorem paste_agreement {p p' : Cell I.left.scheme → ExtOrd}
    {q q' : Cell I.right.scheme → ExtOrd} {h : ExtOrd}
    (hr : ∀ i, p (I.shared.f i) = q (I.shared.g i))
    (hr' : ∀ i, p' (I.shared.f i) = q' (I.shared.g i))
    (hp : Agree p p' h) (hq : Agree q q' h) : Agree (I.paste p q) (I.paste p' q') h := by
  intro d
  rcases covered I d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (congrArg (fun v => min v h) (I.paste_left p q c)).trans
      ((hp c).trans (congrArg (fun v => min v h) (I.paste_left p' q' c)).symm)
  · exact (congrArg (fun v => min v h) (I.paste_right p q hr c)).trans
      ((hq c).trans (congrArg (fun v => min v h) (I.paste_right p' q' hr' c)).symm)

/-- Substitute support by any earlier original-field inventory. This is the
cross-scope version, not just the first two input schemes. -/
theorem paste_supported {X : Type*} {v : X → ExtOrd} {K : ℕ} {G : Set ExtOrd}
    {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
    (hp : ∀ d, Supported K G v (p d)) (hq : ∀ d, Supported K G v (q d))
    (hroot : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∀ d, Supported K G v (I.paste p q d) := by
  intro d
  rcases covered I d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (I.paste_left p q c) ▸ hp c
  · exact (I.paste_right p q hroot c) ▸ hq c

variable (hBA : B ≠ A) (hCA : C ≠ A)

include hBA hCA in
theorem proper_boundary (d : Cell I.boundary) : I.boundary.scope d ≠ A := by
  rcases covered I d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · intro he
    have hc := I.leftScheme.isPlan.subset_of_mem (I.leftScheme.scope_mem_plan c)
    change (I.leftScheme.cell c).1 ⊆ B at hc
    rw [← I.leftFace.index c] at hc
    change I.boundary.scope (I.leftFace.map c) ⊆ B at hc
    rw [he] at hc
    exact hBA (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (I.leftPlan_le I.leftScheme.isPlan.domain_mem)) hc)
  · intro he
    have hc := I.rightScheme.isPlan.subset_of_mem (I.rightScheme.scope_mem_plan c)
    change (I.rightScheme.cell c).1 ⊆ C at hc
    rw [← I.rightFace.index c] at hc
    change I.boundary.scope (I.rightFace.map c) ⊆ C at hc
    rw [he] at hc
    exact hCA (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (I.rightPlan_le I.rightScheme.isPlan.domain_mem)) hc)

variable (n : ℕ) (hA : n + 3 ≤ A.card)

abbrev carrier := CanonicalRecursiveContract.carrier I.rows n hA
abbrev original := CanonicalRecursiveContract.boundary I.rows n hA
abbrev rows := CanonicalRecursiveSemantics.rows I.rows (proper_boundary I hBA hCA) n hA

theorem consistent : (rows I hBA hCA n hA).IsConsistent :=
  CanonicalRecursiveSemantics.consistent I.rows (proper_boundary I hBA hCA) I.consistent n hA

/-- Every new full-scope row is short at its own grade; no such assertion
is made about the inherited rows. -/
theorem new_short (c : Cell (carrier I n hA)) (hc : (carrier I n hA).scope c = A)
    (d : (carrier I n hA).below ((carrier I n hA).cell c)) :
    SharpWitnessComposition.Short ((carrier I n hA).grade c) ((rows I hBA hCA n hA).E c d) :=
  (CanonicalRecursiveSemantics.state I.rows (proper_boundary I hBA hCA) n hA).full_short c hc d

theorem original_row (c : Cell I.boundary) (d : I.boundary.below (I.boundary.cell c)) :
    (rows I hBA hCA n hA).E (original I n hA c)
      ⟨original I n hA d.1, by
        rw [CanonicalRecursiveInventory.boundary_cell, CanonicalRecursiveInventory.boundary_cell]
        exact d.2⟩ = I.rows.E c d :=
  CanonicalRecursiveLiteralRows.row I.rows (proper_boundary I hBA hCA) n hA c d

variable {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
variable (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
variable (hr : ∀ i, p (I.shared.f i) = q (I.shared.g i))
variable (htp : ∀ d, p d ≠ ⊤) (htq : ∀ d, q d ≠ ⊤)

/-- A specified operator, not a choice of an existential amalgamation witness. -/
def sectionOf (G : Finset ExtOrd) (θ : ExtOrd) : Cell (carrier I n hA) → ExtOrd :=
  (CanonicalRecursiveSemantics.state I.rows (proper_boundary I hBA hCA) n hA).sectionOf hA
    ((I.paste_respects hp hq hr).toBelow (A, A.card))
    (paste_proper I htp htq hr) G θ

variable {G : Finset ExtOrd} {θ : ExtOrd}
variable (hG : ∀ z ∈ G, SelfVis (n + 3) z) (hθ : SelfVis (n + 3) θ)

include hG hθ in
theorem section_boundary (d : Cell I.boundary) :
    sectionOf I hBA hCA n hA hp hq hr htp htq G θ (original I n hA d) = I.paste p q d :=
  (CanonicalRecursiveSemantics.state I.rows (proper_boundary I hBA hCA) n hA).section_boundary
    hA _ _ hG hθ d

include hG hθ in
theorem section_left (d : Cell I.left.scheme) :
    sectionOf I hBA hCA n hA hp hq hr htp htq G θ
      (original I n hA (I.leftFace.map d)) = p d :=
  (section_boundary I hBA hCA n hA hp hq hr htp htq hG hθ _).trans (I.paste_left p q d)

include hG hθ in
theorem section_right (d : Cell I.right.scheme) :
    sectionOf I hBA hCA n hA hp hq hr htp htq G θ
      (original I n hA (I.rightFace.map d)) = q d :=
  (section_boundary I hBA hCA n hA hp hq hr htp htq hG hθ _).trans
    (I.paste_right p q hr d)

include hG hθ in
theorem section_lawful : RespectsSemantics (rows I hBA hCA n hA)
    (sectionOf I hBA hCA n hA hp hq hr htp htq G θ) := by
  have hl :=
    (CanonicalRecursiveSemantics.state I.rows (proper_boundary I hBA hCA) n hA).section_lawful
      hA ((I.paste_respects hp hq hr).toBelow (A, A.card))
      (paste_proper I htp htq hr) hG hθ
  exact hl.toRespects (fun d =>
    ⟨(carrier I n hA).isPlan.subset_of_mem ((carrier I n hA).scope_mem_plan d),
      ((carrier I n hA).grade_le_card_scope d).trans (Finset.card_le_card
        ((carrier I n hA).isPlan.subset_of_mem ((carrier I n hA).scope_mem_plan d)))⟩)

include hθ in
theorem section_bound (hbp : ∀ d, p d ≤ θ) (hbq : ∀ d, q d ≤ θ)
    (d : Cell (carrier I n hA)) :
    sectionOf I hBA hCA n hA hp hq hr htp htq G θ d ≤ θ :=
  (CanonicalRecursiveSemantics.state I.rows (proper_boundary I hBA hCA) n hA).section_bound
    hA _ _ hθ (paste_bound I hbp hbq hr) d

include hθ in
theorem section_proper (hbp : ∀ d, p d ≤ θ) (hbq : ∀ d, q d ≤ θ) (hθtop : θ ≠ ⊤)
    (d : Cell (carrier I n hA)) :
    sectionOf I hBA hCA n hA hp hq hr htp htq G θ d ≠ ⊤ :=
  ne_top_of_le_ne_top hθtop (section_bound I hBA hCA n hA hp hq hr htp htq hθ hbp hbq d)

/-- Complete output support can be flattened to the inventory before either
input face was constructed. The grid is fixed, not enlarged with auxiliaries. -/
theorem section_supported_original {X : Type*} {v : X → ExtOrd} {K : ℕ}
    (hK : n + 3 ≤ K) (hGK : ∀ z ∈ G, SelfVis K z) (hθG : θ ∈ G)
    (hsp : ∀ d, Supported K (G : Set ExtOrd) v (p d))
    (hsq : ∀ d, Supported K (G : Set ExtOrd) v (q d))
    (d : Cell (carrier I n hA)) :
    Supported K (G : Set ExtOrd) v (sectionOf I hBA hCA n hA hp hq hr htp htq G θ d) :=
  ((CanonicalRecursiveSemantics.state I.rows (proper_boundary I hBA hCA) n hA).section_supported
    hA _ _ hK hθG d).substitute hGK (paste_supported I hsp hsq hr)

/-- In the first scope the support inventory is exactly the two original vectors. -/
theorem section_supported {K : ℕ} (hK : n + 3 ≤ K)
    (hGK : ∀ z ∈ G, SelfVis K z) (hθG : θ ∈ G) (d : Cell (carrier I n hA)) :
    Supported K (G : Set ExtOrd) (Sum.elim p q)
      (sectionOf I hBA hCA n hA hp hq hr htp htq G θ d) :=
  section_supported_original I hBA hCA n hA hp hq hr htp htq hK hGK hθG
    (fun c => supported_field K (G : Set ExtOrd) (Sum.elim p q) (.inl c))
    (fun c => supported_field K (G : Set ExtOrd) (Sum.elim p q) (.inr c)) d

include hG hθ in
/-- Agreement is on every actual output coordinate, at fixed outer parameters. -/
theorem section_agreement {p' : Cell I.left.scheme → ExtOrd}
    {q' : Cell I.right.scheme → ExtOrd}
    (hp' : RespectsSemantics I.left.rows p') (hq' : RespectsSemantics I.right.rows q')
    (hr' : ∀ i, p' (I.shared.f i) = q' (I.shared.g i))
    (htp' : ∀ d, p' d ≠ ⊤) (htq' : ∀ d, q' d ≠ ⊤)
    {h : ExtOrd} (hh : h ∈ G) (hhθ : h ≤ θ) (hap : Agree p p' h) (haq : Agree q q' h) :
    Agree (sectionOf I hBA hCA n hA hp hq hr htp htq G θ)
      (sectionOf I hBA hCA n hA hp' hq' hr' htp' htq' G θ) h :=
  CanonicalRecursiveSemantics.selected_agreement I.rows (proper_boundary I hBA hCA) n hA
    hA _ _ _ _ hG hθ hh hhθ (paste_agreement I hr hr' hap haq)

end
end VaughtConjecture.Knight.WholeDonorOrdinarySections
