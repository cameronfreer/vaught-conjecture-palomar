/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedSuccessor
public import VaughtConjecture.Knight.RelativeLadderTableDecode

/-! # Incoming rendering on the installed padded LOW successor

A proper state admitted at a cutoff at least two is normalized downward into
the fixed grade-two catalogue, rendered by its actual source row, and decoded
with fixed outer grid and ceiling. The entire retained padded table is read
back directly. Long old rows are not subjected to a short-source composition
assumption; only the native grade-two leaf rows use that composition theorem.

This is a renderer contract on the unchanged first successor, not a lifting
theorem or an assertion that independent construction grades restrict equally.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedRendering
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedSuccessor SourcePrefixRows SharpWitnessComposition
open PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

/-- Native upper sources are short through two, even though the retained
grade-one semantic rows include long tips. -/
theorem source_short (a : F.Anchor 2) (d : Cell (carrier I F hroot hA hB hC)) :
    Short 2 (source I F hroot hA hB hC a d) := by
  let J := input I F hroot hA hB hC
  rcases LowOnlyPaddedSuccessor.cell_cases I F hroot hA hB hC d with ⟨x, rfl⟩ | ⟨b, rfl⟩
  · change Short 2 (J.source a (J.old x))
    rw [J.source_old]
    rcases RelativeLadderLayer.renderWith_supported I.boundary J.one (field I)
        (F.fields 1) (baseAnchor F a) (F.fields 2 a) J.ceiling x with hz | ⟨f, hf⟩ | hh
    · exact Or.inl hz
    · exact (congrArg (Short 2) hf).mpr (LowOnlyRecursiveCharts.anchor_short F a f)
    · exact (congrArg (Short 2) hh).mpr
        (CanonicalFieldLayer.grid_short 2 (Field I.left I.right) (sourceGrid_endpoint le_rfl))
  · rw [source_leaf]
    exact CanonicalFieldLayer.grid_short 2 (Field I.left I.right)
      (cut_mem (sourceGrid_bot _ _) _ _)

variable {j : ℕ} (hj : 2 ≤ j) (S : State I.left I.right)
  (hS : F.Admissible j S) (hp : ∀ d, S.profile d ≠ ⊤)

def anchor : F.Anchor 2 :=
  LowOnlyRecursiveCoverage.normalizedAnchor F (by decide) hj hS hp

theorem anchor_fields : F.fields 2 (anchor I F hj S hS hp) =
    PairedSlotEncoding.normalize 2 S.profile :=
  LowOnlyRecursiveCoverage.normalizedAnchor_fields F (by decide) hj hS hp

theorem birth_ranks (d : Field I.left I.right) :
    RelativeLadderLayer.ranks (F.fields 1) (baseAnchor F (anchor I F hj S hS hp)) d =
      LadderScalarRendering.fieldRank S.profile d := by
  rw [baseAnchor_ranks, anchor_fields]
  exact ReceivingCatalogueRanks.fieldRank_normalize 2 S.profile hp d

def render (G : Finset ExtOrd) (H : ExtOrd) (d : Cell (carrier I F hroot hA hB hC)) : ExtOrd :=
  PairedSlotDecoder.decode 2 (PairedSlotEncoding.values S.profile) G H
    (source I F hroot hA hB hC (anchor I F hj S hS hp) d)

def baseRender (H : ExtOrd) : Cell (input I F hroot hA hB hC).lower → ExtOrd :=
  RelativeLadderLayer.renderWith I.boundary (input I F hroot hA hB hC).one
    (field I) (F.fields 1) (baseAnchor F (anchor I F hj S hS hp)) S.profile H

variable {G : Finset ExtOrd} {H : ExtOrd}

theorem render_old (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H)
    (hb : ∀ d, S.profile d ≤ H) (d : Cell (input I F hroot hA hB hC).lower) :
    render I F hroot hA hB hC hj S hS hp G H (old I F hroot hA hB hC d) =
      baseRender I F hroot hA hB hC hj S hS hp H d := by
  let J := input I F hroot hA hB hC
  have he := congrArg (PairedSlotDecoder.decode 2 (PairedSlotEncoding.values S.profile) G H)
    (J.source_old (anchor I F hj S hS hp) d)
  refine he.trans ?_
  change PairedSlotDecoder.decode 2 (PairedSlotEncoding.values S.profile) G H
    (RelativeLadderLayer.renderWith I.boundary J.one (field I) (F.fields 1)
      (baseAnchor F (anchor I F hj S hS hp)) (F.fields 2 (anchor I F hj S hS hp)) J.ceiling d) = _
  rw [anchor_fields]
  exact RelativeLadderLayer.renderWith_decode_normalized I.boundary J.one
    (field I) (F.fields 1) 2 _ S.profile hp hG hH (decode_reserved_ceiling hH hb) d

theorem render_original (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H)
    (d : Cell I.boundary) :
    render I F hroot hA hB hC hj S hS hp G H (original I F hroot hA hB hC d) =
      S.profile (field I d) := by
  unfold render
  rw [original_readback, anchor_fields]
  exact PairedSlotDecoder.decode_normalize hG hH hp _

theorem baseRender_lawful (hH : SelfVis 2 H) (hb : ∀ d, S.profile d ≤ H) :
    RespectsSemanticsBelow (input I F hroot hA hB hC).lowerRows (A, j)
      (fun d => baseRender I F hroot hA hB hC hj S hS hp H d.1) :=
  RelativeLadderLayer.renderWith_respects I.boundary I.rows
    (input I F hroot hA hB hC).one (field I) (F.fields 1) (proper I hB hC)
    _ _ (birth_ranks I F hj S hS hp) hb
    (LowOnlyRecursiveCharts.profile_visible_one F (by omega) hS)
    (hH.mono (by decide)) (LowOnlyOrderedSources.boundary_lawful_at I F hroot j S hS)

theorem render_below_old (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H)
    (hb : ∀ d, S.profile d ≤ H) (c : Cell (input I F hroot hA hB hC).lower)
    (hc : GradedLe ((input I F hroot hA hB hC).lower.cell c) (A, j)) :
    RespectsSemanticsBelow (rows I F hroot hA hB hC)
      ((carrier I F hroot hA hB hC).cell (old I F hroot hA hB hC c))
      (fun d => render I F hroot hA hB hC hj S hS hp G H d.1) := by
  let J := input I F hroot hA hB hC
  apply (WeightedSourcePrefixLayer.old_respects_iff J.data J.weight J.weight_visible
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ J.separation c)).mpr
  apply (SeparatedSourceLayerCarrier.base_respects_iff J.lower
    (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty))
    2 (by decide) hA J.separation J.lowerRows c _).mpr
  have hl := (baseRender_lawful I F hroot hA hB hC hj S hS hp hH hb).mono hc
  simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
    render_old I F hroot hA hB hC hj S hS hp hG hH hb, CellScheme.below.mono] using hl

theorem render_lawful_two (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H)
    (hb : ∀ d, S.profile d ≤ H) :
    RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2)
      (fun d => render I F hroot hA hB hC hj S hS hp G H d.1) := by
  let J := input I F hroot hA hB hC
  let a := anchor I F hj S hS hp
  have hr := source_lawful I F hroot hA hB hC a
  have hν := PairedSlotDecoder.decode_witness (S := PairedSlotEncoding.values S.profile) hG hH
  refine ⟨?_, ?_, ?_⟩
  · intro d
    have hd : (carrier I F hroot hA hB hC).grade d.1 ≤ 2 := d.2.2
    have he := hν.clause5 (source I F hroot hA hB hC a d.1)
      ((carrier I F hroot hA hB hC).grade d.1)
      (le_top.trans_eq (gTop_of_le hd).symm)
      ((carrier I F hroot hA hB hC).grade d.1) le_rfl
    exact (congrArg (PairedSlotDecoder.decode 2
      (PairedSlotEncoding.values S.profile) G H) (hr.orderly d)).trans he
  · intro c
    rcases LowOnlyPaddedSuccessor.cell_cases I F hroot hA hB hC c.1 with
      ⟨x, hx⟩ | ⟨b, hc⟩
    · have hxc : GradedLe (J.lower.cell x) (A, j) := by
        have hg : J.lower.grade x ≤ 2 := by
          simpa only [hx, CellScheme.grade, SourceLayerCarrier.cell_toCell,
            SourceLayerCarrier.index] using c.2.2
        exact ⟨J.lower.isPlan.subset_of_mem (J.lower.scope_mem_plan x), hg.trans hj⟩
      have hl := render_below_old I F hroot hA hB hC hj S hS hp hG hH hb x hxc
      rcases c with ⟨c, h⟩
      dsimp only at hx
      subst c
      exact hl.locality ⟨old I F hroot hA hB hC x, GradedLe.refl _⟩
    · rcases c with ⟨c, h⟩
      dsimp only at hc
      subst c
      exact map_capped_locality
        (grade := fun d : (carrier I F hroot hA hB hC).below
          ((carrier I F hroot hA hB hC).cell (leaf I F hroot hA hB hC b)) =>
          (carrier I F hroot hA hB hC).grade d.1)
        (E := (rows I F hroot hA hB hC).E (leaf I F hroot hA hB hC b))
        (c := (⟨leaf I F hroot hA hB hC b, GradedLe.refl _⟩ :
          (carrier I F hroot hA hB hC).below
            ((carrier I F hroot hA hB hC).cell (leaf I F hroot hA hB hC b))))
        (p := fun d => source I F hroot hA hB hC a d.1)
        (fun d => d.2.2)
        (by simp only [CellScheme.grade, leaf_index, le_refl])
        (fun d => by
          simpa only [CellScheme.grade, leaf_index] using
            (congrArg (Short 2) (leaf_row I F hroot hA hB hC b d)).mpr
              (source_short I F hroot hA hB hC b d.1))
        (hr.orderly ⟨leaf I F hroot hA hB hC b, h⟩).symm
        (hr.locality ⟨leaf I F hroot hA hB hC b, h⟩) hν
  · intro c t hs hg
    obtain ⟨w, hw, hle⟩ := hr.availability c t hs hg
    exact ⟨w, hw, hν.mono hle⟩

/-- The original owners above grade two are read literally and use their own
lawful domains. No upper-grade commutation of the grade-two decoder is needed. -/
theorem render_lawful (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H)
    (hb : ∀ d, S.profile d ≤ H) :
    RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, j)
      (fun d => render I F hroot hA hB hC hj S hS hp G H d.1) := by
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  rcases LowOnlyPaddedSuccessor.cell_cases I F hroot hA hB hC c.1 with
    ⟨x, hx⟩ | ⟨a, ha⟩
  · have hxc : GradedLe ((input I F hroot hA hB hC).lower.cell x) (A, j) := by
      simpa only [hx, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using c.2
    rcases c with ⟨c, hc⟩
    dsimp only at hx
    subst c
    exact render_below_old I F hroot hA hB hC hj S hS hp hG hH hb x hxc
  · have he : (carrier I F hroot hA hB hC).cell c.1 = (A, 2) :=
      (congrArg (carrier I F hroot hA hB hC).cell ha).trans (leaf_index I F hroot hA hB hC a)
    exact GradeCutLayerRows.cast_respects _ _ he.symm
      (render_lawful_two I F hroot hA hB hC hj S hS hp hG hH hb)

theorem render_bound (hH : SelfVis 2 H) (hb : ∀ d, S.profile d ≤ H)
    (d : Cell (carrier I F hroot hA hB hC)) :
    render I F hroot hA hB hC hj S hS hp G H d ≤ H := by
  apply PairedSlotDecoder.decode_le hH
  intro v hv
  obtain ⟨x, hx⟩ := PairedSlotEncoding.mem_values.mp hv
  simpa only [hx] using hb x

theorem render_supported {l : ℕ} (hl : 2 ≤ l) (hH : H ∈ G)
    (d : Cell (carrier I F hroot hA hB hC)) :
    OrbitPrefixSupport.Supported l (G : Set ExtOrd) S.profile
      (render I F hroot hA hB hC hj S hS hp G H d) :=
  PairedSlotDecoder.decode_supported hl hH _

/-- At a later native catalogue grade, short fields and the native grid make
the entire rendered vector short. This does not change the retained long rows. -/
theorem render_short {l : ℕ} (hl : 2 ≤ l) (hH : H ∈ G)
    (hG : ∀ z ∈ G, Short l z) (hs : ∀ d, Short l (S.profile d))
    (d : Cell (carrier I F hroot hA hB hC)) :
    Short l (render I F hroot hA hB hC hj S hS hp G H d) :=
  PairedCoupledSections.supported_short hG hs
    (render_supported I F hroot hA hB hC hj S hS hp hl hH d)

/-- Whole-coordinate agreement at fixed outer parameters, not equality of
independently rendered sections at different construction grades. -/
theorem render_prefix {T : State I.left I.right} (hT : F.Admissible j T)
    (ht : ∀ d, T.profile d ≠ ⊤) {h : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H)
    (hh : h ∈ G) (hhH : h ≤ H) (hag : Agree S.profile T.profile h) :
    Agree (render I F hroot hA hB hC hj S hS hp G H)
      (render I F hroot hA hB hC hj T hT ht G H) h := by
  obtain ⟨e, heG, he, hpe, hqe, hcompare⟩ :=
    exists_common_cut hG hH hH hh hhH hhH hp ht hag
  have he' : Agree (F.fields 2 (anchor I F hj S hS hp))
      (F.fields 2 (anchor I F hj T hT ht)) e := by
    rw [anchor_fields, anchor_fields]
    exact he
  have hs := source_prefix I F hroot hA hB hC
    (anchor I F hj S hS hp) (anchor I F hj T hT ht) heG he'
  exact Agree.decode hs (PairedSlotDecoder.decode_witness hG hH).mono
    (PairedSlotDecoder.decode_witness hG hH).mono hpe hqe (fun _ _ => hcompare _)

theorem render_ceiling (hH : SelfVis 2 H) (hb : ∀ d, S.profile d ≤ H) :
    render I F hroot hA hB hC hj S hS hp G H
      (leaf I F hroot hA hB hC (anchor I F hj S hS hp)) = H := by
  unfold render
  rw [source_ceiling]
  exact decode_reserved_ceiling hH hb

/-- The retained padded base has its own actual full-scope ceiling occurrence. -/
theorem render_base_ceiling (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H)
    (hb : ∀ d, S.profile d ≤ H) :
    ∃ c : Cell (carrier I F hroot hA hB hC),
      (carrier I F hroot hA hB hC).cell c = (A, 1) ∧
      render I F hroot hA hB hC hj S hS hp G H c = H := by
  let J := input I F hroot hA hB hC
  let a := baseAnchor F (anchor I F hj S hS hp)
  let v := SupportLadderRows.leaf
    (H := RelativeLadderLayer.rungs (X := Field I.left I.right))
    (X := Field I.left I.right) (by unfold RelativeLadderLayer.rungs; omega) a
  let c := RelativeLadderLayer.added I.boundary J.one v
  refine ⟨old I F hroot hA hB hC c, ?_, ?_⟩
  · exact (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans
      (RelativeLadderLayer.added_index I.boundary J.one v)
  · rw [render_old I F hroot hA hB hC hj S hS hp hG hH hb]
    change LadderScalarRendering.level (LadderScalarRendering.values S.profile) H
      (RelativeLadderLayer.rankIndex I.boundary J.one (field I) (F.fields 1) a c) = H
    rw [RelativeLadderLayer.rankIndex_added, SupportLadderRows.index_leaf,
      FiniteProfileControllers.cut_refl]
    exact ite_eq_left (by
      have := LadderScalarRendering.values_card_le S.profile
      unfold RelativeLadderLayer.rungs
      omega)

end
end VaughtConjecture.Knight.LowOnlyPaddedRendering
