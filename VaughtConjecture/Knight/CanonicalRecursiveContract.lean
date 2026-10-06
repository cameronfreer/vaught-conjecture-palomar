/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSeedSections

/-! # The recursive selected-section contract

The original proper boundary is fixed. Stage `n` here means the actual
recursive carrier through grade `n + 3`. The contract is a semantic induction
invariant, not a hypothesis of future completion or bountifulness.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveContract
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison
open SharpWitnessComposition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

abbrev carrier (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card) :=
  CanonicalRecursiveInventory.scheme sem (n + 3) hA
abbrev boundary (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card) :=
  CanonicalRecursiveInventory.boundary sem (n + 3) hA

structure State (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card) where
  rows : Semantics (carrier sem n hA)
  consistent : sem.IsConsistent → rows.IsConsistent
  proper_lawful : ∀ {J : Finset ι × ℕ}, ¬ A ⊆ J.1 →
    ∀ {p : Cell D → ExtOrd}, RespectsSemanticsBelow sem J (fun d => p d.1) →
    ∀ {r : Cell (carrier sem n hA) → ExtOrd},
      (∀ d, r (boundary sem n hA d) = p d) →
      RespectsSemanticsBelow rows J (fun d => r d.1)
  full_short : ∀ c : Cell (carrier sem n hA), (carrier sem n hA).scope c = A →
    ∀ d : (carrier sem n hA).below ((carrier sem n hA).cell c),
      Short ((carrier sem n hA).grade c) (rows.E c d)
  sectionOf : ∀ {K : ℕ}, n + 3 ≤ K → ∀ {p : Cell D → ExtOrd},
    RespectsSemanticsBelow sem (A, K) (fun d => p d.1) → (∀ d, p d ≠ ⊤) →
    Finset ExtOrd → ExtOrd → Cell (carrier sem n hA) → ExtOrd
  section_boundary : ∀ {K} (hK : n + 3 ≤ K) {p : Cell D → ExtOrd} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd},
    (∀ z ∈ G, SelfVis (n + 3) z) → SelfVis (n + 3) C → ∀ d,
      sectionOf hK (p := p) hpr ht G C (boundary sem n hA d) = p d
  section_lawful : ∀ {K} (hK : n + 3 ≤ K) {p : Cell D → ExtOrd} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd},
    (∀ z ∈ G, SelfVis (n + 3) z) → SelfVis (n + 3) C →
      RespectsSemanticsBelow rows (A, K) (fun d => sectionOf hK (p := p) hpr ht G C d.1)
  section_bound : ∀ {K} (hK : n + 3 ≤ K) {p : Cell D → ExtOrd} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd},
    SelfVis (n + 3) C → (∀ d, p d ≤ C) → ∀ d, sectionOf hK (p := p) hpr ht G C d ≤ C
  section_supported : ∀ {K} (hK : n + 3 ≤ K) {p : Cell D → ExtOrd} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd} {L : ℕ},
    n + 3 ≤ L → C ∈ G → ∀ d,
      OrbitPrefixSupport.Supported L (G : Set ExtOrd) p (sectionOf hK (p := p) hpr ht G C d)
  section_agreement : ∀ {K} (hK : n + 3 ≤ K) {p q : Cell D → ExtOrd}
    (hpr) (htp) (hqr) (htq) {G : Finset ExtOrd} {C h : ExtOrd},
    (∀ z ∈ G, SelfVis (n + 3) z) → SelfVis (n + 3) C → h ∈ G → h ≤ C →
    Agree p q h → Agree (sectionOf hK (p := p) hpr htp G C)
      (sectionOf hK (p := q) hqr htq G C) h

/-- The initial state is the already constructed recursive third layer. -/
def seed (sem : Semantics D) (hA : 3 ≤ A.card) (hp : ∀ d : Cell D, D.scope d ≠ A) :
    State sem 0 hA where
  rows := CanonicalRecursiveSeedRows.rows sem hA hp
  consistent := CanonicalRecursiveSeedRows.consistent sem hA hp
  proper_lawful := CanonicalRecursiveSeedSections.proper_lawful sem hA hp
  full_short := CanonicalRecursiveSeedSections.full_source_short sem hA hp
  sectionOf := CanonicalRecursiveSeedSections.sectionOf sem hA hp
  section_boundary := CanonicalRecursiveSeedSections.section_boundary sem hA hp
  section_lawful := CanonicalRecursiveSeedSections.section_lawful sem hA hp
  section_bound := CanonicalRecursiveSeedSections.section_bound sem hA hp
  section_supported := CanonicalRecursiveSeedSections.section_supported sem hA hp
  section_agreement := fun {_} hK {_ _} hpr htp hqr htq =>
    CanonicalRecursiveSeedSections.section_agreement sem hA hp hK hpr htp hqr htq

end
end VaughtConjecture.Knight.CanonicalRecursiveContract
