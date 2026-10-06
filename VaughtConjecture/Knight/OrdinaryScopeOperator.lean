/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorSmallScopes

/-! # A constructed ordinary scope operator at every positive height

The output record below is populated by `build`, from the actual two legal
input facets. It is not a new induction hypothesis asserting future completion.
The grade-one, grade-two and recursive cases use their checked, unchanged rows.
The mute completion is separate, so no active maximal apex is introduced.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryScopeOperator
open AmalgamationPlan Transform Value ExtOrd SourcePrefixRows OrbitPrefixSupport
open WholeDonorOrdinarySections WholeDonorOrdinaryLift WholeDonorSmallScopes
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- Receipts for the actual rows and specified renderer returned by `build`. -/
structure Core (sem : Semantics D) (k : ℕ) where
  carrier : CellScheme A
  rows : Semantics carrier
  plan : carrier.plan = D.plan
  original : Cell D ↪o Cell carrier
  index : ∀ d, carrier.cell (original d) = D.cell d
  coverage : ∀ d, (∃ c, original c = d) ∨ carrier.scope d = A
  row : ∀ (c : Cell D) (d : D.below (D.cell c)),
    rows.E (original c) ⟨original d.1, by rw [index, index]; exact d.2⟩ = sem.E c d
  consistent : rows.IsConsistent
  coded : rows.IsCoded
  bountiful : rows.IsBountiful
  grade : ∀ d, carrier.grade d ≤ k
  complete : ∀ J ∈ Plan.gradedPlan carrier.plan, J.2 ≤ k → ∃ d, carrier.cell d = J
  short : ∀ c, carrier.scope c = A → ∀ d,
    SharpWitnessComposition.Short (carrier.grade c) (rows.E c d)
  render : ∀ {p : Cell D → ExtOrd}, RespectsSemantics sem p → (∀ d, p d ≠ ⊤) →
    Finset ExtOrd → ExtOrd → Cell carrier → ExtOrd
  readback : ∀ {p} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G θ}, (∀ z ∈ G, SelfVis k z) → SelfVis k θ → ∀ d, render hp ht G θ (original d) = p d
  lawful : ∀ {p} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G θ}, (∀ z ∈ G, SelfVis k z) → SelfVis k θ → RespectsSemantics rows (render hp ht G θ)
  bound : ∀ {p} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G θ}, SelfVis k θ → (∀ d, p d ≤ θ) → ∀ d, render hp ht G θ d ≤ θ
  support : ∀ {p} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G : Finset ExtOrd} {θ : ExtOrd} {K : ℕ}, k ≤ K → θ ∈ G → ∀ d,
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (render hp ht G θ d)
  agreement : ∀ {p q} (hp : RespectsSemantics sem p) (htp : ∀ d, p d ≠ ⊤)
    (hq : RespectsSemantics sem q) (htq : ∀ d, q d ≠ ⊤) {G θ γ},
    (∀ z ∈ G, SelfVis k z) → SelfVis k θ → γ ∈ G → γ ≤ θ → Agree p q γ →
    Agree (render hp htp G θ) (render hq htq G θ) γ

variable {B C : Finset ι} {R : Finset (Finset ι)} {m nL nR : ℕ}
variable (I : WholeDonorBoundary.Input A B C R m nL nR) (hBA : B ≠ A) (hCA : C ≠ A)
variable (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)

def one (hA : 1 ≤ A.card) (hg : ∀ d : Cell I.boundary, I.boundary.grade d ≤ 1)
    (hB : 1 ≤ B.card) (hC : 1 ≤ C.card) : Core I.rows 1 where
  carrier := oneCarrier I hA
  rows := oneRows I hBA hCA hA hg
  plan := rfl
  original := OrderEmbedding.ofStrictMono (oneOld I hA) (SourceLayerCarrier.old_order _ _ _ _ _)
  index d := SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)
  coverage d := by
    obtain ⟨x, rfl⟩ := (SourceLayerCarrier.enumeration I.boundary
      (CanonicalFieldLayer.Profile I.rows 1 (Cell I.boundary) id) 1 (by decide) hA).surjective d
    cases x with
    | inl c => exact Or.inl ⟨c, rfl⟩
    | inr q => exact Or.inr (congrArg Prod.fst (SourceLayerCarrier.cell_toCell _ _ _ _ _ _))
  row := one_row I hBA hCA hA hg
  consistent := one_consistent I hBA hCA hA hg
  coded := one_coded I hBA hCA hA hg
  bountiful := one_bountiful I hBA hCA hA hg hB hC hcover
  grade := one_grade I hBA hCA hA hg
  complete := one_complete_through I hA hcover
  short := one_short I hBA hCA hA hg
  render := oneSection I hBA hCA hA hg
  readback := one_readback I hBA hCA hA hg
  lawful := one_lawful I hBA hCA hA hg
  bound := one_bound I hBA hCA hA hg
  support := fun hp ht => CanonicalFieldLayer.section_supported I.rows 1 (Cell I.boundary) id
    (by decide) hA (proper_boundary I hBA hCA) hg hp ht
  agreement := fun hp ht hq htq => one_agreement I hBA hCA hA hg hp ht hq htq

def two (hA : 3 ≤ A.card) (hg : ∀ d : Cell I.boundary, I.boundary.grade d ≤ 2)
    (hB : 2 ≤ B.card) (hC : 2 ≤ C.card) : Core I.rows 2 where
  carrier := twoCarrier I (by omega)
  rows := twoRows I hBA hCA (by omega)
  plan := rfl
  original := CanonicalRecursiveInventory.boundary I.rows 2 (by omega)
  index := CanonicalRecursiveInventory.boundary_cell I.rows 2 (by omega)
  coverage d := by
    rcases RecursiveSourceCarrier.classify I.boundary (CanonicalRecursiveInventory.Profile I.rows)
      2 (by omega) d with ⟨c, rfl⟩ | ⟨j, _, _, he⟩
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr (congrArg Prod.fst he)
  row := two_row I hBA hCA (by omega)
  consistent := two_consistent I hBA hCA (by omega)
  coded := two_coded I hBA hCA (by omega)
  bountiful := two_bountiful I hBA hCA (by omega) hg hB hC hcover
  grade := two_grade I (by omega) hg
  complete := two_complete_through I (by omega) hcover
  short := two_short I hBA hCA (by omega) hA
  render := twoSection I hBA hCA (by omega)
  readback := fun {p} hp ht {G θ} _ _ =>
    two_readback I hBA hCA (by omega) (p := p) hp ht (G := G) (θ := θ)
  lawful := two_lawful I hBA hCA (by omega)
  bound := two_bound I hBA hCA (by omega)
  support := fun hp ht => CanonicalPairLocalSections.section_supported I.rows (by omega)
    (proper_boundary I hBA hCA) (by omega : 2 ≤ A.card) (hp.toBelow (A, A.card)) ht
  agreement := fun hp ht hq htq => two_agreement I hBA hCA (by omega) hp ht hq htq

def higher (n : ℕ) (hA : n + 3 ≤ A.card)
    (hg : ∀ d : Cell I.boundary, I.boundary.grade d ≤ n + 3)
    (hB : n + 3 ≤ B.card) (hC : n + 3 ≤ C.card) : Core I.rows (n + 3) where
  carrier := WholeDonorOrdinarySections.carrier I n hA
  rows := WholeDonorOrdinarySections.rows I hBA hCA n hA
  plan := CanonicalRecursiveBoundaryTransport.plan_eq I.rows (n + 3) hA
  original := WholeDonorOrdinarySections.original I n hA
  index := CanonicalRecursiveInventory.boundary_cell I.rows (n + 3) hA
  coverage d := by
    rcases RecursiveSourceCarrier.classify I.boundary (CanonicalRecursiveInventory.Profile I.rows)
      (n + 3) hA d with ⟨c, rfl⟩ | ⟨j, _, _, he⟩
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr (congrArg Prod.fst he)
  row := original_row I hBA hCA n hA
  consistent := WholeDonorOrdinarySections.consistent I hBA hCA n hA
  coded := WholeDonorOrdinaryLift.coded I hBA hCA n hA
  bountiful := by
    apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
      (CanonicalRecursiveCoverage.grade_bound I.rows (n + 3) hA hg) (by omega : 0 < n + 3)
    intro S T j hS hT hj hST
    rw [CanonicalRecursiveBoundaryTransport.plan_eq] at hS hT
    exact WholeDonorOrdinaryLift.lift I hBA hCA n hA hcover hB hC
      (CI := (S, j)) (BJ := (T, j)) hS hT ⟨hST, le_rfl⟩ hj
  grade := CanonicalRecursiveCoverage.grade_bound I.rows (n + 3) hA hg
  complete := complete_through I n hA hcover
  short := new_short I hBA hCA n hA
  render := fun hp ht => (CanonicalRecursiveSemantics.state I.rows
    (proper_boundary I hBA hCA) n hA).sectionOf hA (hp.toBelow (A, A.card)) ht
  readback := fun hp ht => (CanonicalRecursiveSemantics.state I.rows
    (proper_boundary I hBA hCA) n hA).section_boundary hA (hp.toBelow (A, A.card)) ht
  lawful := by
    intro p hp ht G θ hG hθ
    have hs := (CanonicalRecursiveSemantics.state I.rows
      (proper_boundary I hBA hCA) n hA).section_lawful
        hA (hp.toBelow (A, A.card)) ht hG hθ
    apply hs.toRespects
    intro d
    exact ⟨(WholeDonorOrdinarySections.carrier I n hA).isPlan.subset_of_mem
      ((WholeDonorOrdinarySections.carrier I n hA).scope_mem_plan d),
      (CanonicalRecursiveCoverage.grade_bound I.rows (n + 3) hA hg d).trans hA⟩
  bound := fun hp ht => (CanonicalRecursiveSemantics.state I.rows
    (proper_boundary I hBA hCA) n hA).section_bound hA (hp.toBelow (A, A.card)) ht
  support := fun hp ht => (CanonicalRecursiveSemantics.state I.rows
    (proper_boundary I hBA hCA) n hA).section_supported hA (hp.toBelow (A, A.card)) ht
  agreement := fun hp ht hq htq => (CanonicalRecursiveSemantics.state I.rows
    (proper_boundary I hBA hCA) n hA).section_agreement hA (hp.toBelow (A, A.card)) ht
      (hq.toBelow (A, A.card)) htq

/-- One local operation through the penultimate grade, including heights one
and two. All semantic and selected-section fields above are constructed. -/
def build (k : ℕ) (hk : 0 < k) (hcard : A.card = k + 1)
    (hB : k ≤ B.card) (hC : k ≤ C.card) : Core I.rows k := by
  have hg := boundary_grade I hBA hCA hcard.le
  rcases k with _ | _ | _ | n
  · omega
  · exact one I (hBA := hBA) (hCA := hCA) (hcover := hcover) (by omega) hg hB hC
  · exact two I (hBA := hBA) (hCA := hCA) (hcover := hcover) (by omega) hg hB hC
  · exact higher I (hBA := hBA) (hCA := hCA) (hcover := hcover) n (by omega) hg hB hC

namespace Core
variable {sem : Semantics D} {k : ℕ} (S : Core sem k)
variable (hk : 0 < k) (hcard : A.card = k + 1)

/-- Close this scope with its actual zero highest row. The selected renderer
is extended by bottom; no original or earlier auxiliary value is recoded. -/
def finish (S : Core sem k) (hk : 0 < k) (hcard : A.card = k + 1) : Core sem (k + 1) where
  carrier := OrdinaryScopeMute.carrier S.carrier k (k + 1) (by omega) hcard.ge
  rows := OrdinaryScopeMute.rows S.carrier S.rows k (k + 1) S.grade (by omega) hcard.ge
  plan := S.plan
  original := S.original.trans (OrderEmbedding.ofStrictMono
    (OrdinaryScopeMute.old S.carrier k (k + 1) (by omega) hcard.ge)
    (SourceLayerCarrier.old_order _ _ _ _ _))
  index d := (MaximalFullLayer.old_index S.carrier k (k + 1) (by omega) hcard.ge
    (S.original d)).trans (S.index d)
  coverage d := by
    rcases OrdinaryScopeMute.covered S.carrier k (k + 1) (by omega) hcard.ge d with
      ⟨c, rfl⟩ | rfl
    · rcases S.coverage c with ⟨a, rfl⟩ | ha
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inr ((congrArg Prod.fst
          (MaximalFullLayer.old_index S.carrier k (k + 1) (by omega) hcard.ge c)).trans ha)
    · exact Or.inr (congrArg Prod.fst
        (MaximalFullLayer.apex_index S.carrier k (k + 1) (by omega) hcard.ge))
  row c d := (OrdinaryScopeMute.inherited_row S.carrier S.rows k (k + 1) S.grade
    (by omega) hcard.ge (S.original c)
      ⟨S.original d.1, by rw [S.index, S.index]; exact d.2⟩).trans (S.row c d)
  consistent := OrdinaryScopeMute.consistent _ _ _ _ _ _ _ S.consistent
  coded := OrdinaryScopeMute.coded _ _ _ _ _ _ _ S.coded
  bountiful := OrdinaryScopeMute.bountiful _ _ _ _ _ _ _ hk S.bountiful
  grade d := by
    rcases OrdinaryScopeMute.covered S.carrier k (k + 1) (by omega) hcard.ge d with
      ⟨c, rfl⟩ | rfl
    · exact (congrArg Prod.snd
        (MaximalFullLayer.old_index S.carrier k (k + 1) (by omega) hcard.ge c)).le.trans
          ((S.grade c).trans (Nat.le_succ k))
    · exact (congrArg Prod.snd
        (MaximalFullLayer.apex_index S.carrier k (k + 1) (by omega) hcard.ge)).le
  complete J hJ _ := OrdinaryScopeMute.complete_last S.carrier k (k + 1) (by omega)
    hcard.ge hcard rfl S.complete J hJ
  short c hc d := by
    rcases OrdinaryScopeMute.covered S.carrier k (k + 1) (by omega) hcard.ge c with
      ⟨c, rfl⟩ | rfl
    · apply OrdinaryScopeMute.inherited_short S.carrier S.rows k (k + 1) S.grade
        (by omega) hcard.ge c
      apply S.short c
      exact (congrArg Prod.fst
        (MaximalFullLayer.old_index S.carrier k (k + 1) (by omega) hcard.ge c)).symm.trans hc
    · have h := OrdinaryScopeMute.apex_short S.carrier S.rows k (k + 1) S.grade
        (by omega) hcard.ge d
      exact (congrArg (fun j => SharpWitnessComposition.Short j _)
        (congrArg Prod.snd (MaximalFullLayer.apex_index S.carrier k (k + 1)
          (by omega) hcard.ge))).mpr h
  render := fun hp ht G θ => OrdinaryScopeMute.render S.carrier k (k + 1)
    (by omega) hcard.ge (S.render hp ht G θ)
  readback := by
    intro p hp ht G θ hG hθ d
    exact (OrdinaryScopeMute.render_old S.carrier k (k + 1) (by omega) hcard.ge _ _).trans
      (S.readback hp ht (fun z hz => selfVis_mono (hG z hz) (Nat.le_succ k))
        (selfVis_mono hθ (Nat.le_succ k)) d)
  lawful := by
    intro p hp ht G θ hG hθ
    exact OrdinaryScopeMute.render_lawful S.carrier S.rows k (k + 1) S.grade (by omega) hcard.ge
      (S.lawful hp ht (fun z hz => selfVis_mono (hG z hz) (Nat.le_succ k))
        (selfVis_mono hθ (Nat.le_succ k)))
  bound := by
    intro p hp ht G θ hθ hb
    exact OrdinaryScopeMute.render_bound S.carrier k (k + 1)
      (by omega) hcard.ge (S.bound hp ht (selfVis_mono hθ (Nat.le_succ k)) hb)
  support := by
    intro p hp ht G θ K hK hθ
    exact OrdinaryScopeMute.render_supported S.carrier k (k + 1)
      (by omega) hcard.ge (S.support hp ht ((Nat.le_succ k).trans hK) hθ)
  agreement := by
    intro p q hp ht hq htq G θ γ hG hθ hγ hγθ hag
    exact OrdinaryScopeMute.render_agreement S.carrier k (k + 1) (by omega) hcard.ge
      (S.agreement hp ht hq htq (fun z hz => selfVis_mono (hG z hz) (Nat.le_succ k))
        (selfVis_mono hθ (Nat.le_succ k)) hγ hγθ hag)

theorem finish_complete : (S.finish hk hcard).carrier.IsComplete :=
  OrdinaryScopeMute.complete_last S.carrier k (k + 1) (by omega) hcard.ge hcard rfl S.complete

theorem finish_apex_inactive {p : Cell (S.finish hk hcard).carrier → ExtOrd}
    (hp : RespectsSemantics (S.finish hk hcard).rows p) :
    p (OrdinaryScopeMute.apex S.carrier k (k + 1) (by omega) hcard.ge) = ⊥ :=
  OrdinaryScopeMute.apex_inactive S.carrier S.rows k (k + 1) S.grade (by omega) hcard.ge hp

/-- The only newly possible highest-grade occurrence is the mute apex.
This is the local inactivity receipt for completed proper scopes. -/
theorem finish_highest_inactive {p : Cell (S.finish hk hcard).carrier → ExtOrd}
    (hp : RespectsSemantics (S.finish hk hcard).rows p)
    (d : Cell (S.finish hk hcard).carrier) (hd : (S.finish hk hcard).carrier.grade d = k + 1) :
    p d = ⊥ := by
  rcases OrdinaryScopeMute.covered S.carrier k (k + 1) (Nat.lt_succ_self k) hcard.ge d with
    ⟨c, rfl⟩ | rfl
  · have he := congrArg Prod.snd
      (MaximalFullLayer.old_index S.carrier k (k + 1) (Nat.lt_succ_self k) hcard.ge c)
    have hg : S.carrier.grade c = k + 1 := he.symm.trans hd
    have hc := S.grade c
    omega
  · exact S.finish_apex_inactive hk hcard hp

/-- Every literal proper face keeps its entire actual lower domains and rows,
not only the labels selected by the renderer. -/
def face {E : CellScheme B} {old : Semantics E} (F : ExactSemanticFace old sem)
    (hB : ¬ A ⊆ B) : ExactSemanticFace old S.rows where
  map := F.map.trans S.original.toEmbedding
  index c := (S.index (F.map c)).trans (F.index c)
  exhaustive z hz := by
    rcases S.coverage z with ⟨d, rfl⟩ | he
    · have hd : D.scope d ⊆ B := by
        change (D.cell d).1 ⊆ B
        change (S.carrier.cell (S.original d)).1 ⊆ B at hz
        simpa only [S.index] using hz
      obtain ⟨c, rfl⟩ := F.exhaustive d hd
      exact ⟨c, rfl⟩
    · exact (hB (he ▸ hz)).elim
  row c d := (S.row (F.map c) (F.belowMap c d)).trans (F.row c d)

theorem face_order {E : CellScheme B} {old : Semantics E} (F : ExactSemanticFace old sem)
    (hB : ¬ A ⊆ B) (hF : StrictMono F.map) : StrictMono (S.face F hB).map :=
  S.original.strictMono.comp hF

/-- Flatten support to the fields before either of this scope's facets was
constructed. Earlier controllers never become new original fields. -/
theorem supported_original {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) {G : Finset ExtOrd} {θ : ExtOrd} {K : ℕ} {X : Type*}
    {v : X → ExtOrd} (hK : k ≤ K) (hG : ∀ z ∈ G, SelfVis K z) (hθ : θ ∈ G)
    (hsp : ∀ d, OrbitPrefixSupport.Supported K (G : Set ExtOrd) v (p d))
    (d : Cell S.carrier) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) v (S.render hp ht G θ d) :=
  (S.support hp ht hK hθ d).substitute hG hsp

theorem render_proper {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) {G : Finset ExtOrd} {θ : ExtOrd}
    (hθ : SelfVis k θ) (hb : ∀ d, p d ≤ θ) (htop : θ ≠ ⊤) (d : Cell S.carrier) :
    S.render hp ht G θ d ≠ ⊤ :=
  ne_top_of_le_ne_top htop (S.bound hp ht hθ hb d)

end Core

/-- A complete local scope with literal old rows, full bountifulness and a
fixed-grid selected operator. This does not relocate it into a larger scheme. -/
def completed (k : ℕ) (hk : 0 < k) (hcard : A.card = k + 1)
    (hB : k ≤ B.card) (hC : k ≤ C.card) : Core I.rows (k + 1) :=
  (build I (hBA := hBA) (hCA := hCA) (hcover := hcover) k hk hcard hB hC).finish hk hcard

theorem completed_complete (k : ℕ) (hk : 0 < k) (hcard : A.card = k + 1)
    (hB : k ≤ B.card) (hC : k ≤ C.card) :
    (completed I (hBA := hBA) (hCA := hCA) (hcover := hcover)
      k hk hcard hB hC).carrier.IsComplete :=
  (build I (hBA := hBA) (hCA := hCA) (hcover := hcover)
    k hk hcard hB hC).finish_complete hk hcard

end
end VaughtConjecture.Knight.OrdinaryScopeOperator
