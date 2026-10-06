/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedNativeRows

/-! # Birth provenance for every inherited higher growth owner

The producer exhausts the actual installed inventory. Its returned maps preserve
occurrence order, every base coordinate, and the owner's entire native row.
No provenance or hidden-completion hypothesis is supplied by the caller.
-/
@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedOwnerProvenance
open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration GrowthPaddedNativeRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

/-- Constructed birth data for an actual owner on a fixed final carrier. -/
structure Origin (t : ℕ) (ht : t + 2 ≤ A.card)
    (c : Cell (build I X T hA hB hC t ht).carrier) where
  birth : ℕ
  birth_le : birth ≤ t
  height : birth + 2 ≤ A.card
  member : Catalogue X (birth + 2)
  map : Cell (build I X T hA hB hC birth height).carrier →
    Cell (build I X T hA hB hC t ht).carrier
  order : StrictMono map
  index : ∀ d, (build I X T hA hB hC t ht).carrier.cell (map d) =
    (build I X T hA hB hC birth height).carrier.cell d
  base : ∀ d, map ((build I X T hA hB hC birth height).baseMap d) =
    (build I X T hA hB hC t ht).baseMap d
  occurrence : map (owner I X T hA hB hC birth height member) = c
  domain : (build I X T hA hB hC birth height).carrier.below
      ((build I X T hA hB hC birth height).carrier.cell
        (owner I X T hA hB hC birth height member)) ≃
    (build I X T hA hB hC t ht).carrier.below
      ((build I X T hA hB hC t ht).carrier.cell c)
  domain_val : ∀ d, (domain d).1 = map d.1
  row : ∀ d, (build I X T hA hB hC t ht).rows.E c (domain d) =
    source I X T hA hB hC birth height member d.1

def native (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2)) :
    Origin I X T hA hB hC t ht (owner I X T hA hB hC t ht a) where
  birth := t
  birth_le := le_rfl
  height := ht
  member := a
  map := id
  order := strictMono_id
  index _ := rfl
  base _ := rfl
  occurrence := rfl
  domain := Equiv.refl _
  domain_val _ := rfl
  row := owner_row I X T hA hB hC t ht a

def inherit (t : ℕ) (ht : (t + 1) + 2 ≤ A.card)
    (c : Cell (build I X T hA hB hC t (by omega)).carrier)
    (O : Origin I X T hA hB hC t (by omega) c) :
    Origin I X T hA hB hC (t + 1) ht
      (GrowthPaddedStepRows.old (build I X T hA hB hC t (by omega)) (by omega) c) where
  birth := O.birth
  birth_le := O.birth_le.trans (Nat.le_succ t)
  height := O.height
  member := O.member
  map d := GrowthPaddedStepRows.old (build I X T hA hB hC t (by omega)) (by omega) (O.map d)
  order := (SourceLayerCarrier.old_order _ _ _ (Nat.succ_pos _) (by omega)).comp O.order
  index d := (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans (O.index d)
  base d := congrArg (GrowthPaddedStepRows.old _ _) (O.base d)
  occurrence := congrArg (GrowthPaddedStepRows.old _ _) O.occurrence
  domain := O.domain.trans (GrowthPaddedStepRows.ownerEquiv
    (build I X T hA hB hC t (by omega)) (by omega) (by omega) c)
  domain_val d := congrArg (GrowthPaddedStepRows.old _ _) (O.domain_val d)
  row d := (GrowthPaddedStepRows.inherited_row
    (build I X T hA hB hC t (by omega)) (by omega) (by omega) c (O.domain d)).trans (O.row d)

/-- Exhaustive actual-owner provenance, including every inherited layer. -/
theorem exists_origin (t : ℕ) (ht : t + 2 ≤ A.card)
    (c : Cell (build I X T hA hB hC t ht).carrier)
    (hc : (build I X T hA hB hC t ht).carrier.scope c = A)
    (hg : 2 ≤ (build I X T hA hB hC t ht).carrier.grade c) :
    Nonempty (Origin I X T hA hB hC t ht c) := by
  induction t with
  | zero =>
    rcases GrowthPaddedSuccessor.cell_cases I X T hA hB hC c with ⟨d, rfl⟩ | ⟨a, rfl⟩
    · have hi : (build I X T hA hB hC 0 ht).carrier.cell
          (GrowthPaddedSuccessor.old I X T hA hB hC d) =
          (base I X T hA hB hC).cell d :=
        SourceLayerCarrier.cell_toCell _ _ _ _ _ _
      have hs : (base I X T hA hB hC).scope d = A :=
        (congrArg Prod.fst hi).symm.trans hc
      have he := base_full_grade I X T hA hB hC d hs
      have hh : 2 ≤ (base I X T hA hB hC).grade d :=
        hg.trans_eq (congrArg Prod.snd hi)
      omega
    · exact ⟨native I X T hA hB hC 0 ht a⟩
  | succ t ih =>
    let P := build I X T hA hB hC t (by omega)
    obtain ⟨x, hx⟩ := (SourceLayerCarrier.enumeration P.carrier
      (Catalogue X (t + 2 + 1)) (t + 2 + 1) (Nat.succ_pos _) (by omega)).surjective c
    change SourceLayerCarrier.toCell _ _ _ _ _ x = c at hx
    rcases x with d | a
    · rw [← hx] at hc hg ⊢
      have hi : (build I X T hA hB hC (t + 1) ht).carrier.cell
          (SourceLayerCarrier.toCell P.carrier (Catalogue X (t + 2 + 1))
            (t + 2 + 1) (Nat.succ_pos _) (by omega) (.inl d)) = P.carrier.cell d :=
        SourceLayerCarrier.cell_toCell _ _ _ _ _ _
      obtain ⟨O⟩ := ih (by omega) d ((congrArg Prod.fst hi).symm.trans hc)
        (hg.trans_eq (congrArg Prod.snd hi))
      exact ⟨inherit I X T hA hB hC t ht d O⟩
    · rw [← hx]
      exact ⟨native I X T hA hB hC (t + 1) ht a⟩

/-- Canonical chosen provenance, constructed from the actual inventory. -/
def origin (t : ℕ) (ht : t + 2 ≤ A.card)
    (c : Cell (build I X T hA hB hC t ht).carrier)
    (hc : (build I X T hA hB hC t ht).carrier.scope c = A)
    (hg : 2 ≤ (build I X T hA hB hC t ht).carrier.grade c) :
    Origin I X T hA hB hC t ht c :=
  Classical.choice (exists_origin I X T hA hB hC t ht c hc hg)

/-- Arbitrary actual higher owner, arbitrary argument in its entire final
domain: the native source is recovered without supplied provenance. -/
theorem row_of_owner (t : ℕ) (ht : t + 2 ≤ A.card)
    (c : Cell (build I X T hA hB hC t ht).carrier)
    (hc : (build I X T hA hB hC t ht).carrier.scope c = A)
    (hg : 2 ≤ (build I X T hA hB hC t ht).carrier.grade c)
    (d : (build I X T hA hB hC t ht).carrier.below
      ((build I X T hA hB hC t ht).carrier.cell c)) :
    let O := origin I X T hA hB hC t ht c hc hg
    (build I X T hA hB hC t ht).rows.E c d =
      source I X T hA hB hC O.birth O.height O.member (O.domain.symm d).1 := by
  dsimp only
  let O := origin I X T hA hB hC t ht c hc hg
  exact (congrArg ((build I X T hA hB hC t ht).rows.E c)
    (O.domain.apply_symm_apply d)).symm.trans (O.row (O.domain.symm d))

namespace Origin
variable {I X T hA hB hC} {t : ℕ} {ht : t + 2 ≤ A.card}
  {c : Cell (build I X T hA hB hC t ht).carrier}
  (O : Origin I X T hA hB hC t ht c)

theorem owner_index : (build I X T hA hB hC t ht).carrier.cell c = (A, O.birth + 2) :=
  (congrArg _ O.occurrence).symm.trans ((O.index _).trans
    (GrowthPaddedNativeRows.owner_index I X T hA hB hC O.birth O.height O.member))

theorem row_bound (d : (build I X T hA hB hC t ht).carrier.below
    ((build I X T hA hB hC t ht).carrier.cell c)) :
    (build I X T hA hB hC t ht).rows.E c d ≤ ceiling I O.birth := by
  have he := O.row (O.domain.symm d)
  rw [O.domain.apply_symm_apply] at he
  exact he.le.trans (source_bound I X T hA hB hC O.birth O.height O.member _)

theorem row_diagonal :
    (build I X T hA hB hC t ht).rows.E c ⟨c, GradedLe.refl _⟩ =
      ceiling I O.birth := by
  let e : (build I X T hA hB hC O.birth O.height).carrier.below
      ((build I X T hA hB hC O.birth O.height).carrier.cell
        (owner I X T hA hB hC O.birth O.height O.member)) :=
    ⟨owner I X T hA hB hC O.birth O.height O.member, GradedLe.refl _⟩
  have he : O.domain e = ⟨c, GradedLe.refl _⟩ :=
    Subtype.ext ((O.domain_val e).trans O.occurrence)
  exact (congrArg ((build I X T hA hB hC t ht).rows.E c) he).symm.trans
    ((O.row e).trans (source_diagonal I X T hA hB hC O.birth O.height O.member))

/-- An actual base occurrence in this inherited owner's domain. -/
def baseArgument (d : Cell (GrowthPaddedContract.base I X T hA hB hC))
    (hd : GradedLe ((GrowthPaddedContract.base I X T hA hB hC).cell d) (A, O.birth + 2)) :
    (build I X T hA hB hC t ht).carrier.below
      ((build I X T hA hB hC t ht).carrier.cell c) :=
  ⟨(build I X T hA hB hC t ht).baseMap d, by rw [Layer.base_index, O.owner_index]; exact hd⟩

theorem row_base_source (d : Cell (GrowthPaddedContract.base I X T hA hB hC))
    (hd : GradedLe ((GrowthPaddedContract.base I X T hA hB hC).cell d) (A, O.birth + 2)) :
    (build I X T hA hB hC t ht).rows.E c (O.baseArgument d hd) =
      source I X T hA hB hC O.birth O.height O.member
        ((build I X T hA hB hC O.birth O.height).baseMap d) := by
  let e : (build I X T hA hB hC O.birth O.height).carrier.below
      ((build I X T hA hB hC O.birth O.height).carrier.cell
        (owner I X T hA hB hC O.birth O.height O.member)) :=
    ⟨(build I X T hA hB hC O.birth O.height).baseMap d, by
      rw [Layer.base_index, GrowthPaddedNativeRows.owner_index]; exact hd⟩
  have he : O.domain e = O.baseArgument d hd := Subtype.ext
    ((O.domain_val e).trans (O.base d))
  rw [← he, O.row]

/-- Present original fields are literal numerical columns. The membership
premise only asserts presence; absent future fields use the shadow theorem. -/
theorem row_original (d : Cell I.boundary)
    (hd : GradedLe (I.boundary.cell d) (A, O.birth + 2)) :
    (build I X T hA hB hC t ht).rows.E c
      (O.baseArgument (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)
        (by simpa only [RelativeLadderLayer.old_index] using hd)) =
      fields X (O.birth + 2) O.member (field I d) := by
  rw [row_base_source, source_original]

def ladderArgument (v : RelativeLadderLayer.Point
    (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :
    (build I X T hA hB hC t ht).carrier.below
      ((build I X T hA hB hC t ht).carrier.cell c) :=
  O.baseArgument (RelativeLadderLayer.added I.boundary (by omega : 0 < A.card) v)
    (by rw [RelativeLadderLayer.added_index]; exact ⟨le_rfl, by omega⟩)

theorem row_ladder_source (v : RelativeLadderLayer.Point
    (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :
    (build I X T hA hB hC t ht).rows.E c (O.ladderArgument v) =
      source I X T hA hB hC O.birth O.height O.member
        (ladder I X T hA hB hC O.birth O.height v) :=
  O.row_base_source _ _

/-- The full rank table, not merely represented-field readouts. -/
theorem row_ladder (v : RelativeLadderLayer.Point
    (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :
    (build I X T hA hB hC t ht).rows.E c (O.ladderArgument v) =
      SupportLadderRows.image (RelativeLadderLayer.ranks (fields X 1))
        (anchor I X T hA hB hC O.birth O.height O.member)
        (LadderScalarRendering.level
          (LadderScalarRendering.values (fields X (O.birth + 2) O.member))
          (ceiling I O.birth)) v := by
  rw [O.row_ladder_source, source_ladder]

theorem row_shadow_sup (f : Field I.right.scheme I.left.scheme) :
    (Finset.univ : Finset (Catalogue X 1)).sup
      (fun b => (build I X T hA hB hC t ht).rows.E c
        (O.ladderArgument (SupportLadderRows.shadow b f))) =
      fields X (O.birth + 2) O.member f := by
  simp only [O.row_ladder_source]
  exact source_shadow_sup I X T hA hB hC O.birth O.height O.member f

theorem row_spare :
    (build I X T hA hB hC t ht).rows.E c
      (O.ladderArgument (SupportLadderRows.leaf (by exact Nat.succ_pos _)
        (anchor I X T hA hB hC O.birth O.height O.member))) = ceiling I O.birth := by
  rw [O.row_ladder_source]
  exact source_spare I X T hA hB hC O.birth O.height O.member

theorem row_ceiling_at (i : ℕ) (hi : 1 ≤ i) (hib : i ≤ O.birth + 2) :
    ∃ d : (build I X T hA hB hC t ht).carrier.below
        ((build I X T hA hB hC t ht).carrier.cell c),
      (build I X T hA hB hC t ht).carrier.cell d.1 = (A, i) ∧
        (build I X T hA hB hC t ht).rows.E c d = ceiling I O.birth := by
  obtain ⟨d, hd, hv⟩ := source_ceiling_at I X T hA hB hC O.birth O.height O.member i hi hib
  let e : (build I X T hA hB hC O.birth O.height).carrier.below
      ((build I X T hA hB hC O.birth O.height).carrier.cell
        (owner I X T hA hB hC O.birth O.height O.member)) :=
    ⟨d, by rw [hd, GrowthPaddedNativeRows.owner_index]; exact ⟨le_rfl, hib⟩⟩
  exact ⟨O.domain e, (congrArg _ (O.domain_val e)).trans ((O.index d).trans hd),
    (O.row e).trans hv⟩

end Origin

open GrowthPaddedCutTransport

/-- Explicit provenance of a specified birth leaf after any suffix of
installations. This uses the existing literal occurrence embedding. -/
def retained (s : ℕ) (hs : s + 2 ≤ A.card) (a : Catalogue X (s + 2)) :
    (u : ℕ) → (hu : s + u + 2 ≤ A.card) →
      Origin I X T hA hB hC (s + u) hu
        (advanceMap I X T hA hB hC s hs u hu (owner I X T hA hB hC s hs a))
  | 0, _ => native I X T hA hB hC s hs a
  | u + 1, hu => inherit I X T hA hB hC (s + u) hu _
      (retained s hs a u (by omega))

theorem retained_birth (s : ℕ) (hs : s + 2 ≤ A.card) (a : Catalogue X (s + 2))
    (u : ℕ) (hu : s + u + 2 ≤ A.card) :
    (retained I X T hA hB hC s hs a u hu).birth = s := by
  induction u with
  | zero => rfl
  | succ u ih => exact ih (by omega)

/-- Literal native row in every later build, at every actual birth-domain
argument (the domain transport is an equivalence). -/
theorem retained_row (s : ℕ) (hs : s + 2 ≤ A.card) (a : Catalogue X (s + 2))
    (u : ℕ) (hu : s + u + 2 ≤ A.card)
    (d : (build I X T hA hB hC s hs).carrier.below
      ((build I X T hA hB hC s hs).carrier.cell (owner I X T hA hB hC s hs a))) :
    (build I X T hA hB hC (s + u) hu).rows.E
      (advanceMap I X T hA hB hC s hs u hu (owner I X T hA hB hC s hs a))
      ⟨advanceMap I X T hA hB hC s hs u hu d.1, by
        rw [advance_index, advance_index]; exact d.2⟩ =
      source I X T hA hB hC s hs a d.1 :=
  (advance_row I X T hA hB hC s hs u hu _ d).trans
    (GrowthPaddedNativeRows.owner_row I X T hA hB hC s hs a d)

theorem retained_ladder_row (s : ℕ) (hs : s + 2 ≤ A.card) (a : Catalogue X (s + 2))
    (u : ℕ) (hu : s + u + 2 ≤ A.card)
    (v : RelativeLadderLayer.Point
      (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :
    (build I X T hA hB hC (s + u) hu).rows.E
      (advanceMap I X T hA hB hC s hs u hu (owner I X T hA hB hC s hs a))
      ⟨ladder I X T hA hB hC (s + u) hu v, by
        rw [ladder_index, advance_index, GrowthPaddedNativeRows.owner_index]
        exact ⟨le_rfl, by omega⟩⟩ =
      SupportLadderRows.image (RelativeLadderLayer.ranks (fields X 1))
        (anchor I X T hA hB hC s hs a)
        (LadderScalarRendering.level (LadderScalarRendering.values (fields X (s + 2) a))
          (ceiling I s)) v := by
  have hr := retained_row I X T hA hB hC s hs a u hu
    ⟨ladder I X T hA hB hC s hs v, by
      rw [ladder_index, GrowthPaddedNativeRows.owner_index]; exact ⟨le_rfl, by omega⟩⟩
  have hv := advance_baseMap I X T hA hB hC s hs u hu
    (RelativeLadderLayer.added I.boundary (by omega : 0 < A.card) v)
  exact ((build I X T hA hB hC (s + u) hu).rows.E_congr' rfl hv.symm).trans
    (hr.trans (source_ladder I X T hA hB hC s hs a v))

/-- Acceptance regression: a grade-three owner inherited in grade four or
any later build retains its entire native padded table, unused rungs and
foreign shadows included. -/
theorem grade_three_in_later (h3 : 3 ≤ A.card) (u : ℕ)
    (hu : 1 + (u + 1) + 2 ≤ A.card) (a : Catalogue X 3)
    (v : RelativeLadderLayer.Point
      (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :
    (build I X T hA hB hC (1 + (u + 1)) hu).rows.E
      (advanceMap I X T hA hB hC 1 h3 (u + 1) hu (owner I X T hA hB hC 1 h3 a))
      ⟨ladder I X T hA hB hC (1 + (u + 1)) hu v, by
        rw [ladder_index, advance_index, GrowthPaddedNativeRows.owner_index]
        exact ⟨le_rfl, by omega⟩⟩ =
      SupportLadderRows.image (RelativeLadderLayer.ranks (fields X 1))
        (anchor I X T hA hB hC 1 h3 a)
        (LadderScalarRendering.level (LadderScalarRendering.values (fields X 3 a))
          (ceiling I 1)) v :=
  retained_ladder_row I X T hA hB hC 1 h3 a (u + 1) hu v

end
end VaughtConjecture.Knight.GrowthPaddedOwnerProvenance
