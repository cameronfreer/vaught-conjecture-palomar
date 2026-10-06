/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedRendering

/-! # The retained-padded growth row-and-rendering invariant

The base rows stay literal, including long grade-one tips and proper original
owners of arbitrary grade. Only higher full-scope rows are required short at
their own grade. This is an invariant of a constructed semantic layer, not a
lifting or bountifulness hypothesis. The contract and its constructed seed
follow the checked LOW renderer, instantiated here with growth admission.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedContract
open Transform Value ExtOrd CappedDonor Growth GrowthOrderedBase GrowthHigherSources
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (attach : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev base := (GrowthPaddedSuccessor.input I X attach hA hB hC).lower
abbrev baseRows := (GrowthPaddedSuccessor.input I X attach hA hB hC).lowerRows

theorem base_full_grade (c : Cell (base I X attach hA hB hC))
    (hc : (base I X attach hA hB hC).scope c = A) :
    (base I X attach hA hB hC).grade c = 1 := by
  rcases RelativeLadderLayer.cell_cases I.boundary (by omega : 0 < A.card) c with
    ⟨d, rfl⟩ | ⟨v, rfl⟩
  · exact False.elim (proper I hB hC d
      ((congrArg Prod.fst (RelativeLadderLayer.old_index I.boundary (by omega) d)).symm.trans hc))
  · exact congrArg Prod.snd (RelativeLadderLayer.added_index I.boundary (by omega) v)

structure Layer (k : ℕ) where
  carrier : CellScheme A
  rows : Semantics carrier
  consistent : rows.IsConsistent
  baseMap : Cell (base I X attach hA hB hC) → Cell carrier
  base_mono : StrictMono baseMap
  base_index : ∀ c, carrier.cell (baseMap c) = (base I X attach hA hB hC).cell c
  base_row : ∀ c (d : (base I X attach hA hB hC).below
      ((base I X attach hA hB hC).cell c)),
    rows.E (baseMap c) ⟨baseMap d.1, by simpa only [base_index] using d.2⟩ =
      (baseRows I X attach hA hB hC).E c d
  base_respects : ∀ c (p : Cell carrier → ExtOrd),
    RespectsSemanticsBelow rows (carrier.cell (baseMap c)) (fun d => p d.1) ↔
      RespectsSemanticsBelow (baseRows I X attach hA hB hC)
        ((base I X attach hA hB hC).cell c) (fun d => p (baseMap d.1))
  cases : ∀ d, (∃ c, d = baseMap c) ∨
    carrier.scope d = A ∧ 2 ≤ carrier.grade d ∧ carrier.grade d ≤ k
  higher_short : ∀ c, carrier.scope c = A → 2 ≤ carrier.grade c →
    ∀ d : carrier.below (carrier.cell c), Short (carrier.grade c) (rows.E c d)
  render : ∀ {j : ℕ}, k ≤ j → ∀ S : State I.right.scheme I.left.scheme,
    Admitted X j S → (∀ d, S.profile d ≠ ⊤) →
    Finset ExtOrd → ExtOrd → Cell carrier → ExtOrd
  birth : ∀ {j : ℕ} (_hj : k ≤ j) (S : State I.right.scheme I.left.scheme)
    (_hS : Admitted X j S) (_hp : ∀ d, S.profile d ≠ ⊤), Catalogue X 1
  birth_ranks : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) d,
    RelativeLadderLayer.ranks (fields X 1) (birth hj S hS hp) d =
      LadderScalarRendering.fieldRank S.profile d
  render_base : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G H},
    (∀ z ∈ G, SelfVis k z) → SelfVis k H → (∀ d, S.profile d ≤ H) → ∀ d,
    render hj S hS hp G H (baseMap d) =
      RelativeLadderLayer.renderWith I.boundary (by omega : 0 < A.card)
        (field I) (fields X 1) (birth hj S hS hp) S.profile H d
  lawful : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G H},
    (∀ z ∈ G, SelfVis k z) → SelfVis k H → (∀ d, S.profile d ≤ H) →
      RespectsSemanticsBelow rows (A, j) (fun d => render hj S hS hp G H d.1)
  bound : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G H},
    SelfVis k H → (∀ d, S.profile d ≤ H) → ∀ d, render hj S hS hp G H d ≤ H
  supported : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G : Finset ExtOrd} {H : ExtOrd} {l : ℕ},
    k ≤ l → H ∈ G → ∀ d,
    OrbitPrefixSupport.Supported l (G : Set ExtOrd) S.profile (render hj S hS hp G H d)
  agreement : ∀ {j} (hj : k ≤ j) (S T) (hS) (hT) (hp) (ht) {G H h},
    (∀ z ∈ G, SelfVis k z) → SelfVis k H → h ∈ G → h ≤ H →
    Agree S.profile T.profile h → Agree (render hj S hS hp G H) (render hj T hT ht G H) h
  ceiling_at : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G H},
    (∀ z ∈ G, SelfVis k z) → SelfVis k H → (∀ d, S.profile d ≤ H) →
    ∀ i, 1 ≤ i → i ≤ k → ∃ c, carrier.cell c = (A, i) ∧ render hj S hS hp G H c = H

namespace Layer
variable {k : ℕ} (P : Layer I X attach hA hB hC k)

theorem full_grade (hk : 1 ≤ k) (d : Cell P.carrier) (hd : P.carrier.scope d = A) :
    P.carrier.grade d ≤ k := by
  rcases P.cases d with ⟨c, rfl⟩ | ⟨_, _, hg⟩
  · have hs : (base I X attach hA hB hC).scope c = A :=
      (congrArg Prod.fst (P.base_index c)).symm.trans hd
    exact (congrArg Prod.snd (P.base_index c)).le.trans
      ((base_full_grade I X attach hA hB hC c hs).le.trans hk)
  · exact hg

theorem separated (hk : 1 ≤ k) (d : Cell P.carrier) :
    ¬ GradedLe (A, k + 1) (P.carrier.cell d) := by
  intro hd
  have hs := Finset.Subset.antisymm
    (P.carrier.isPlan.subset_of_mem (P.carrier.scope_mem_plan d)) hd.1
  have hg := P.full_grade I X attach hA hB hC hk d hs
  have hk' : k + 1 ≤ P.carrier.grade d := hd.2
  omega

theorem original_readback {j : ℕ} (hj : k ≤ j) (S : State I.right.scheme I.left.scheme)
    (hS : Admitted X j S) (hp : ∀ d, S.profile d ≠ ⊤) {G H}
    (hG : ∀ z ∈ G, SelfVis k z) (hH : SelfVis k H) (hb : ∀ d, S.profile d ≤ H)
    (d : Cell I.boundary) :
    P.render hj S hS hp G H (P.baseMap (RelativeLadderLayer.old I.boundary (by omega) d)) =
      S.profile (field I d) := by
  rw [P.render_base hj S hS hp hG hH hb]
  exact RelativeLadderLayer.renderWith_old I.boundary (by omega) (field I) (fields X 1)
    _ _ _ (P.birth_ranks hj S hS hp) d
end Layer

/-- The existing actual first successor supplies the invariant without changing its rows. -/
def initial : Layer I X attach hA hB hC 2 where
  carrier := GrowthPaddedSuccessor.carrier I X attach hA hB hC
  rows := GrowthPaddedSuccessor.rows I X attach hA hB hC
  consistent := GrowthPaddedSuccessor.consistent I X attach hA hB hC
  baseMap := GrowthPaddedSuccessor.old I X attach hA hB hC
  base_mono := SourceLayerCarrier.old_order _ _ _ _ _
  base_index c := SourceLayerCarrier.cell_toCell _ _ _ _ _ _
  base_row := GrowthPaddedSuccessor.inherited_row I X attach hA hB hC
  base_respects c p := by
    let J := GrowthPaddedSuccessor.input I X attach hA hB hC
    rw [WeightedSourcePrefixLayer.old_respects_iff J.data J.weight J.weight_visible
      (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ J.separation c)]
    exact SeparatedSourceLayerCarrier.base_respects_iff J.lower
      (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty))
      2 (by decide) hA J.separation J.lowerRows c _
  cases d := by
    rcases GrowthPaddedSuccessor.cell_cases I X attach hA hB hC d with h | ⟨a, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨congrArg Prod.fst (GrowthPaddedSuccessor.leaf_index I X attach hA hB hC a),
        (congrArg Prod.snd (GrowthPaddedSuccessor.leaf_index I X attach hA hB hC a)).ge,
        (congrArg Prod.snd (GrowthPaddedSuccessor.leaf_index I X attach hA hB hC a)).le⟩
  higher_short c hc hg d := by
    rcases GrowthPaddedSuccessor.cell_cases I X attach hA hB hC c with ⟨b, rfl⟩ | ⟨a, rfl⟩
    · have hi := SourceLayerCarrier.cell_toCell
        (base I X attach hA hB hC)
        (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty))
        2 (by decide) hA (.inl b)
      have hb := base_full_grade I X attach hA hB hC b
        ((congrArg Prod.fst hi).symm.trans hc)
      have he := (congrArg Prod.snd hi).trans hb
      have he' : (GrowthPaddedSuccessor.carrier I X attach hA hB hC).grade
          (GrowthPaddedSuccessor.old I X attach hA hB hC b) = 1 := he
      exact False.elim (by omega)
    · simpa only [CellScheme.grade, GrowthPaddedSuccessor.leaf_index,
        GrowthPaddedSuccessor.leaf_row] using
        GrowthPaddedRendering.source_short I X attach hA hB hC a d.1
  render := GrowthPaddedRendering.render I X attach hA hB hC
  birth {j} hj S hS hp := GrowthPaddedSuccessor.baseAnchor X
    (GrowthPaddedRendering.anchor I X hj S hS hp)
  birth_ranks := GrowthPaddedRendering.birth_ranks I X
  render_base := GrowthPaddedRendering.render_old I X attach hA hB hC
  lawful := GrowthPaddedRendering.render_lawful I X attach hA hB hC
  bound := GrowthPaddedRendering.render_bound I X attach hA hB hC
  supported := GrowthPaddedRendering.render_supported I X attach hA hB hC
  agreement {j} hj S T hS hT hp ht :=
    GrowthPaddedRendering.render_prefix I X attach hA hB hC hj S hS hp hT ht
  ceiling_at {j} hj S hS hp {G H} hG hH hb i hi hik := by
    have he : i = 1 ∨ i = 2 := by omega
    rcases he with rfl | rfl
    · exact GrowthPaddedRendering.render_base_ceiling I X attach hA hB hC
        hj S hS hp hG hH hb
    · exact ⟨_, GrowthPaddedSuccessor.leaf_index I X attach hA hB hC _,
        GrowthPaddedRendering.render_ceiling I X attach hA hB hC hj S hS hp hH hb⟩

end
end VaughtConjecture.Knight.GrowthPaddedContract
