/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedRendering

/-! # The retained-padded LOW row-and-rendering invariant

The base rows stay literal, including long grade-one tips and proper original
owners of arbitrary grade. Only higher full-scope rows are required short at
their own grade. This is an invariant of a constructed semantic layer, not a
lifting or bountifulness hypothesis.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedContract
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison
noncomputable section

section Catalogue
variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

def state {j : ℕ} (a : F.Anchor j) : State P C := State.ofProfile a.val
theorem state_eq_chosen {j : ℕ} (a : F.Anchor j) :
    state F a = Classical.choose a.property.2 := by
  apply State.profile_injective
  exact (State.profile_ofProfile a.val).trans (Classical.choose_spec a.property.2).2.symm
theorem state_admissible {j : ℕ} (a : F.Anchor j) : F.Admissible j (state F a) :=
  by
    obtain ⟨S, hS, he⟩ := a.property.2
    have hs : state F a = S := State.profile_injective
      ((State.profile_ofProfile a.val).trans he.symm)
    exact hs.symm ▸ hS
theorem state_profile {j : ℕ} (a : F.Anchor j) : (state F a).profile = F.fields j a :=
  State.profile_ofProfile a.val
theorem state_proper {j : ℕ} (a : F.Anchor j) (d : Field P C) :
    (state F a).profile d ≠ ⊤ := by
  rw [state_profile]
  exact LowOnlyRecursiveCharts.anchor_proper F a d
end Catalogue

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev base := (LowOnlyPaddedSuccessor.input I F hroot hA hB hC).lower
abbrev baseRows := (LowOnlyPaddedSuccessor.input I F hroot hA hB hC).lowerRows

theorem base_full_grade (c : Cell (base I F hroot hA hB hC))
    (hc : (base I F hroot hA hB hC).scope c = A) :
    (base I F hroot hA hB hC).grade c = 1 := by
  rcases RelativeLadderLayer.cell_cases I.boundary (by omega : 0 < A.card) c with
    ⟨d, rfl⟩ | ⟨v, rfl⟩
  · exact False.elim (proper I hB hC d
      ((congrArg Prod.fst (RelativeLadderLayer.old_index I.boundary (by omega) d)).symm.trans hc))
  · exact congrArg Prod.snd (RelativeLadderLayer.added_index I.boundary (by omega) v)

structure Layer (k : ℕ) where
  carrier : CellScheme A
  rows : Semantics carrier
  consistent : rows.IsConsistent
  baseMap : Cell (base I F hroot hA hB hC) → Cell carrier
  base_mono : StrictMono baseMap
  base_index : ∀ c, carrier.cell (baseMap c) = (base I F hroot hA hB hC).cell c
  base_row : ∀ c (d : (base I F hroot hA hB hC).below
      ((base I F hroot hA hB hC).cell c)),
    rows.E (baseMap c) ⟨baseMap d.1, by simpa only [base_index] using d.2⟩ =
      (baseRows I F hroot hA hB hC).E c d
  base_respects : ∀ c (p : Cell carrier → ExtOrd),
    RespectsSemanticsBelow rows (carrier.cell (baseMap c)) (fun d => p d.1) ↔
      RespectsSemanticsBelow (baseRows I F hroot hA hB hC)
        ((base I F hroot hA hB hC).cell c) (fun d => p (baseMap d.1))
  cases : ∀ d, (∃ c, d = baseMap c) ∨
    carrier.scope d = A ∧ 2 ≤ carrier.grade d ∧ carrier.grade d ≤ k
  higher_short : ∀ c, carrier.scope c = A → 2 ≤ carrier.grade c →
    ∀ d : carrier.below (carrier.cell c), Short (carrier.grade c) (rows.E c d)
  render : ∀ {j : ℕ}, k ≤ j → ∀ S : State I.left I.right,
    F.Admissible j S → (∀ d, S.profile d ≠ ⊤) →
    Finset ExtOrd → ExtOrd → Cell carrier → ExtOrd
  birth : ∀ {j : ℕ} (_hj : k ≤ j) (S : State I.left I.right)
    (_hS : F.Admissible j S) (_hp : ∀ d, S.profile d ≠ ⊤), F.Anchor 1
  birth_ranks : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) d,
    RelativeLadderLayer.ranks (F.fields 1) (birth hj S hS hp) d =
      LadderScalarRendering.fieldRank S.profile d
  render_base : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G H},
    (∀ z ∈ G, SelfVis k z) → SelfVis k H → (∀ d, S.profile d ≤ H) → ∀ d,
    render hj S hS hp G H (baseMap d) =
      RelativeLadderLayer.renderWith I.boundary (by omega : 0 < A.card)
        (field I) (F.fields 1) (birth hj S hS hp) S.profile H d
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
variable {k : ℕ} (P : Layer I F hroot hA hB hC k)

theorem full_grade (hk : 1 ≤ k) (d : Cell P.carrier) (hd : P.carrier.scope d = A) :
    P.carrier.grade d ≤ k := by
  rcases P.cases d with ⟨c, rfl⟩ | ⟨_, _, hg⟩
  · have hs : (base I F hroot hA hB hC).scope c = A :=
      (congrArg Prod.fst (P.base_index c)).symm.trans hd
    exact (congrArg Prod.snd (P.base_index c)).le.trans
      ((base_full_grade I F hroot hA hB hC c hs).le.trans hk)
  · exact hg

theorem separated (hk : 1 ≤ k) (d : Cell P.carrier) :
    ¬ GradedLe (A, k + 1) (P.carrier.cell d) := by
  intro hd
  have hs := Finset.Subset.antisymm
    (P.carrier.isPlan.subset_of_mem (P.carrier.scope_mem_plan d)) hd.1
  have hg := P.full_grade I F hroot hA hB hC hk d hs
  have hk' : k + 1 ≤ P.carrier.grade d := hd.2
  omega

theorem original_readback {j : ℕ} (hj : k ≤ j) (S : State I.left I.right)
    (hS : F.Admissible j S) (hp : ∀ d, S.profile d ≠ ⊤) {G H}
    (hG : ∀ z ∈ G, SelfVis k z) (hH : SelfVis k H) (hb : ∀ d, S.profile d ≤ H)
    (d : Cell I.boundary) :
    P.render hj S hS hp G H (P.baseMap (RelativeLadderLayer.old I.boundary (by omega) d)) =
      S.profile (field I d) := by
  rw [P.render_base hj S hS hp hG hH hb]
  exact RelativeLadderLayer.renderWith_old I.boundary (by omega) (field I) (F.fields 1)
    _ _ _ (P.birth_ranks hj S hS hp) d
end Layer

/-- The existing actual first successor supplies the invariant without changing its rows. -/
def initial : Layer I F hroot hA hB hC 2 where
  carrier := LowOnlyPaddedSuccessor.carrier I F hroot hA hB hC
  rows := LowOnlyPaddedSuccessor.rows I F hroot hA hB hC
  consistent := LowOnlyPaddedSuccessor.consistent I F hroot hA hB hC
  baseMap := LowOnlyPaddedSuccessor.old I F hroot hA hB hC
  base_mono := SourceLayerCarrier.old_order _ _ _ _ _
  base_index c := SourceLayerCarrier.cell_toCell _ _ _ _ _ _
  base_row := LowOnlyPaddedSuccessor.inherited_row I F hroot hA hB hC
  base_respects c p := by
    let J := LowOnlyPaddedSuccessor.input I F hroot hA hB hC
    rw [WeightedSourcePrefixLayer.old_respects_iff J.data J.weight J.weight_visible
      (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ J.separation c)]
    exact SeparatedSourceLayerCarrier.base_respects_iff J.lower
      (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty))
      2 (by decide) hA J.separation J.lowerRows c _
  cases d := by
    rcases LowOnlyPaddedSuccessor.cell_cases I F hroot hA hB hC d with h | ⟨a, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨congrArg Prod.fst (LowOnlyPaddedSuccessor.leaf_index I F hroot hA hB hC a),
        (congrArg Prod.snd (LowOnlyPaddedSuccessor.leaf_index I F hroot hA hB hC a)).ge,
        (congrArg Prod.snd (LowOnlyPaddedSuccessor.leaf_index I F hroot hA hB hC a)).le⟩
  higher_short c hc hg d := by
    rcases LowOnlyPaddedSuccessor.cell_cases I F hroot hA hB hC c with ⟨b, rfl⟩ | ⟨a, rfl⟩
    · have hi := SourceLayerCarrier.cell_toCell
        (base I F hroot hA hB hC)
        (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty))
        2 (by decide) hA (.inl b)
      have hb := base_full_grade I F hroot hA hB hC b
        ((congrArg Prod.fst hi).symm.trans hc)
      have he := (congrArg Prod.snd hi).trans hb
      have he' : (LowOnlyPaddedSuccessor.carrier I F hroot hA hB hC).grade
          (LowOnlyPaddedSuccessor.old I F hroot hA hB hC b) = 1 := he
      exact False.elim (by omega)
    · simpa only [CellScheme.grade, LowOnlyPaddedSuccessor.leaf_index,
        LowOnlyPaddedSuccessor.leaf_row] using
        LowOnlyPaddedRendering.source_short I F hroot hA hB hC a d.1
  render := LowOnlyPaddedRendering.render I F hroot hA hB hC
  birth {j} hj S hS hp := LowOnlyPaddedSuccessor.baseAnchor F
    (LowOnlyPaddedRendering.anchor I F hj S hS hp)
  birth_ranks := LowOnlyPaddedRendering.birth_ranks I F
  render_base := LowOnlyPaddedRendering.render_old I F hroot hA hB hC
  lawful := LowOnlyPaddedRendering.render_lawful I F hroot hA hB hC
  bound := LowOnlyPaddedRendering.render_bound I F hroot hA hB hC
  supported := LowOnlyPaddedRendering.render_supported I F hroot hA hB hC
  agreement {j} hj S T hS hT hp ht :=
    LowOnlyPaddedRendering.render_prefix I F hroot hA hB hC hj S hS hp hT ht
  ceiling_at {j} hj S hS hp {G H} hG hH hb i hi hik := by
    have he : i = 1 ∨ i = 2 := by omega
    rcases he with rfl | rfl
    · exact LowOnlyPaddedRendering.render_base_ceiling I F hroot hA hB hC
        hj S hS hp hG hH hb
    · exact ⟨_, LowOnlyPaddedSuccessor.leaf_index I F hroot hA hB hC _,
        LowOnlyPaddedRendering.render_ceiling I F hroot hA hB hC hj S hS hp hH hb⟩

end
end VaughtConjecture.Knight.LowOnlyPaddedContract
