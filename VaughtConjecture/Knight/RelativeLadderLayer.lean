/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SeparatedSourceLayerCarrier
public import VaughtConjecture.Knight.ReceivingCatalogueIncidences

/-! # The first relative mixed layer

Append actual grade-one rungs and shadows to a proper inherited boundary.
The inputs are scalar sections lawful on that boundary, not lawful physical
predecessor vectors. Rank postprocessing constructs their incidences with all
inherited grade-one owners, including long rows. Every shadow, including a
zero-rank shadow, has a separately installed same-source ceiling leaf.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.RelativeLadderLayer
open Transform Value ExtOrd LadderScalarRendering
noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype X] [Fintype Q] {A : Finset ι}
variable (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
variable (field : Cell D → X) (fields : Q → X → ExtOrd)

def ranks (a : Q) (x : X) : ℕ := fieldRank (fields a) x
def rungs : ℕ := Fintype.card X + 1
abbrev Point := SupportLadderRows.Point (rungs (X := X)) X Q
abbrev carrier := SourceLayerCarrier.scheme D (Point (X := X) (Q := Q)) 1 Nat.one_pos hA
abbrev old (d : Cell D) : Cell (carrier D hA (X := X) (Q := Q)) :=
  SourceLayerCarrier.toCell D (Point (X := X) (Q := Q)) 1 Nat.one_pos hA (.inl d)
abbrev added (v : Point (X := X) (Q := Q)) : Cell (carrier D hA (X := X) (Q := Q)) :=
  SourceLayerCarrier.toCell D (Point (X := X) (Q := Q)) 1 Nat.one_pos hA (.inr v)
abbrev view := SourceLayerCarrier.toOcc D (Point (X := X) (Q := Q)) 1 Nat.one_pos hA

theorem old_index (d : Cell D) : (carrier D hA (X := X) (Q := Q)).cell (old D hA d) = D.cell d :=
  SourceLayerCarrier.cell_toCell D _ 1 Nat.one_pos hA (.inl d)
theorem added_index (v : Point (X := X) (Q := Q)) :
    (carrier D hA (X := X) (Q := Q)).cell (added D hA v) = (A, 1) :=
  SourceLayerCarrier.cell_toCell D _ 1 Nat.one_pos hA (.inr v)

theorem cell_cases (d : Cell (carrier D hA (X := X) (Q := Q))) :
    (∃ c, d = old D hA c) ∨ ∃ v, d = added D hA v := by
  cases he : view D hA d with
  | inl c =>
      refine Or.inl ⟨c, ?_⟩
      rw [← SourceLayerCarrier.toCell_toOcc D (Point (X := X) (Q := Q)) 1 Nat.one_pos hA d]
      exact congrArg (SourceLayerCarrier.toCell D _ 1 Nat.one_pos hA) he
  | inr v =>
      refine Or.inr ⟨v, ?_⟩
      rw [← SourceLayerCarrier.toCell_toOcc D (Point (X := X) (Q := Q)) 1 Nat.one_pos hA d]
      exact congrArg (SourceLayerCarrier.toCell D _ 1 Nat.one_pos hA) he

def rankIndex (a : Q) (d : Cell (carrier D hA (X := X) (Q := Q))) : ℕ :=
  match view D hA d with
  | .inl c => ranks fields a (field c)
  | .inr v => SupportLadderRows.index (ranks fields) a v

@[simp] theorem rankIndex_old (a : Q) (d : Cell D) :
    rankIndex D hA field fields a (old D hA d) = ranks fields a (field d) := by
  simp only [rankIndex, old, view, SourceLayerCarrier.toOcc_toCell]
@[simp] theorem rankIndex_added (a : Q) (v : Point (X := X) (Q := Q)) :
    rankIndex D hA field fields a (added D hA v) = SupportLadderRows.index (ranks fields) a v := by
  simp only [rankIndex, added, view, SourceLayerCarrier.toOcc_toCell]

omit [Fintype Q] in
theorem rank_bound (a : Q) (x : X) : ranks fields a x < rungs (X := X) :=
  Nat.lt_succ_of_le (fieldRank_le _ _)

omit [Fintype Q] in
theorem rank_zero (a : Q) (x : X) : ranks fields a x = 0 ↔ fields a x = ⊥ := by
  constructor
  · intro hz
    by_contra hn
    have hh := rank_pos (mem_values.mpr ⟨hn, x, rfl⟩)
    change 0 < ranks fields a x at hh
    omega
  · intro hz
    change rank (values (fields a)) (fields a x) = 0
    rw [hz]
    exact rank_bot (bot_not_values _)

theorem rankIndex_bound (a : Q) (d : Cell (carrier D hA (X := X) (Q := Q))) :
    rankIndex D hA field fields a d ≤ rungs (X := X) := by
  unfold rankIndex
  split
  · exact (rank_bound fields _ _).le
  · exact SupportLadderRows.index_le _ _

theorem rankIndex_agreement (a b : Q) (d : Cell (carrier D hA (X := X) (Q := Q))) :
    min (rankIndex D hA field fields a d)
        (FiniteProfileControllers.cut (rungs (X := X)) (ranks fields a) (ranks fields b)) =
      min (rankIndex D hA field fields b d)
        (FiniteProfileControllers.cut (rungs (X := X)) (ranks fields a) (ranks fields b)) := by
  unfold rankIndex
  split
  · exact FiniteProfileControllers.agree_cut _ _ _ _
  · exact SupportLadderRows.index_agreement _ _ _

def image (a : Q) (f : ℕ → ExtOrd) (d : Cell (carrier D hA (X := X) (Q := Q))) : ExtOrd :=
  f (rankIndex D hA field fields a d)

def ladderRow (v : Point (X := X) (Q := Q)) : Cell (carrier D hA (X := X) (Q := Q)) → ExtOrd :=
  image D hA field fields (SupportLadderRows.parent v)
    (SupportLadderRows.source (SupportLadderRows.ceiling (ranks fields) v))

variable (hp : ∀ d : Cell D, D.scope d ≠ A)

abbrev separated := SeparatedSourceLayerCarrier.separated_of_proper D 1 hp
abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv D
  (Point (X := X) (Q := Q)) 1 Nat.one_pos hA (separated D hp)
abbrev base := SeparatedSourceLayerCarrier.base D
  (Point (X := X) (Q := Q)) 1 Nat.one_pos hA (separated D hp) sem

theorem below_grade_one (v : Point (X := X) (Q := Q))
    (d : (carrier D hA (X := X) (Q := Q)).below
      ((carrier D hA (X := X) (Q := Q)).cell (added D hA v))) :
    (carrier D hA (X := X) (Q := Q)).grade d.1 = 1 :=
  le_antisymm (by simpa only [CellScheme.grade, added_index] using d.2.2)
    ((carrier D hA (X := X) (Q := Q)).grade_pos d.1)

def rows : Semantics (carrier D hA (X := X) (Q := Q)) where
  E c d := match view D hA c with
    | .inl _ => (base D sem hA hp).E c d
    | .inr v => ladderRow D hA field fields v d.1
  orderly c d := by
    dsimp only
    split
    · exact (base D sem hA hp).orderly c d
    · rename_i v h
      have hc : c = added D hA v := by
        rw [← SourceLayerCarrier.toCell_toOcc D (Point (X := X) (Q := Q)) 1 Nat.one_pos hA c]
        exact congrArg (SourceLayerCarrier.toCell D _ 1 Nat.one_pos hA) h
      have hg : (carrier D hA (X := X) (Q := Q)).grade d.1 = 1 :=
        below_grade_one D hA v ⟨d.1, hc ▸ d.2⟩
      change _ = extVisibilityReplace _
        ((carrier D hA (X := X) (Q := Q)).grade d.1) _
      rw [hg]
      exact (SupportLadderRows.source_visible _ _).symm

theorem row_added (v : Point (X := X) (Q := Q))
    (d : (carrier D hA (X := X) (Q := Q)).below
      ((carrier D hA (X := X) (Q := Q)).cell (added D hA v))) :
    (rows D sem hA field fields hp).E (added D hA v) d = ladderRow D hA field fields v d.1 := by
  simp only [rows, view, added, SourceLayerCarrier.toOcc_toCell]

theorem row_old (c : Cell D)
    (d : (carrier D hA (X := X) (Q := Q)).below
      ((carrier D hA (X := X) (Q := Q)).cell (old D hA c))) :
    (rows D sem hA field fields hp).E (old D hA c) d = (base D sem hA hp).E (old D hA c) d := by
  simp only [rows, view, old, SourceLayerCarrier.toOcc_toCell]

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows D sem hA field fields hp).E (old D hA c) (ownerEquiv D hA hp c d) = sem.E c d := by
  rw [row_old]
  exact SeparatedSourceLayerCarrier.base_old D _ 1 Nat.one_pos hA (separated D hp) sem c d

theorem old_respects_iff (c : Cell D)
    (p : (carrier D hA (X := X) (Q := Q)).below
      ((carrier D hA (X := X) (Q := Q)).cell (old D hA c)) → ExtOrd) :
    RespectsSemanticsBelow (rows D sem hA field fields hp) _ p ↔
      RespectsSemanticsBelow sem (D.cell c) (p ∘ ownerEquiv D hA hp c) := by
  have he (d : (carrier D hA (X := X) (Q := Q)).below
      ((carrier D hA (X := X) (Q := Q)).cell (old D hA c))) :
      (rows D sem hA field fields hp).E d.1 = (base D sem hA hp).E d.1 := by
    obtain ⟨d, rfl⟩ := (ownerEquiv D hA hp c).surjective d
    exact funext (row_old D sem hA field fields hp d.1)
  rw [← SeparatedSourceLayerCarrier.base_respects_iff D _ 1 Nat.one_pos hA
    (separated D hp) sem c p]
  constructor <;> intro h <;> refine ⟨h.orderly, ?_, h.availability⟩
  · intro d
    simpa only [he d] using h.locality d
  · intro d
    rw [he d]
    exact h.locality d

omit [Fintype Q] in
/-- The original-lawful input, not a completed physical source, supplies all
rank-coded old incidences. Long rows are handled by finite bottom reflection. -/
theorem rank_respects (a : Q)
    (ha : RespectsSemanticsBelow sem (A, 1) (fun d => fields a (field d.1))) (t : ℕ) :
    RespectsSemanticsBelow sem (A, 1)
      (fun d => SupportLadderRows.source t (ranks fields a (field d.1))) := by
  have hg (d : D.below (A, 1)) : D.grade d.1 = 1 := le_antisymm d.2.2 (D.grade_pos d.1)
  refine ⟨fun d => by
    change _ = extVisibilityReplace _ (D.grade d.1) (D.grade d.1)
    rw [hg]; exact (SupportLadderRows.source_visible _ _).symm, ?_, ?_⟩
  · intro c
    have hgc (d : D.below (D.cell c.1)) : D.grade d.1 = 1 :=
      le_antisymm (d.2.2.trans c.2.2) (D.grade_pos d.1)
    have hgrade : (fun d : D.below (D.cell c.1) => D.grade d.1) = (fun _ => 1) := funext hgc
    rw [hgrade]
    by_cases ht : t = 0
    · subst t
      have hz (i : ℕ) : SupportLadderRows.source 0 i = ⊥ :=
        (SupportLadderRows.source_bot_iff _ _).mpr (Nat.min_zero i)
      simp only [hz, min_self]
      exact TransformsTo.to_bot _
    let f : ExtOrd → ExtOrd := fun x => SupportLadderRows.source t (rank (values (fields a)) x)
    have hm : Monotone f := (SupportLadderRows.source_mono t).comp (rank_mono _)
    have h0 : f ⊥ = ⊥ := by
      simp only [f, rank_bot (bot_not_values _), SupportLadderRows.source_zero]
    have hz (x : X) : f (fields a x) = ⊥ ↔ fields a x = ⊥ := by
      change SupportLadderRows.source t (ranks fields a x) = ⊥ ↔ _
      rw [SupportLadderRows.source_bot_iff, Nat.min_eq_zero_iff, or_iff_left ht]
      exact rank_zero fields a x
    have hl := ha.locality c
    rw [hgrade] at hl
    have hout := ReceivingCatalogueIncidences.postprocess hl
      (fun d => by simpa only [hgc d] using (sem.orderly c.1 d).symm) hm h0
      (fun _ => SupportLadderRows.source_visible _ _)
      (fun d => by rw [hm.map_min, min_eq_bot, hz, hz, min_eq_bot])
    simpa only [hm.map_min, f, ranks, fieldRank] using hout
  · intro c v hs hgr
    obtain ⟨w, hw, hcw⟩ := ha.availability c v hs hgr
    exact ⟨w, hw, SupportLadderRows.source_mono t (rank_mono _ hcw)⟩

/-- Locality at every installed rung, on its complete actual domain. -/
theorem image_locality (a : Q) (f : ℕ → ExtOrd) (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, SelfVis 1 (f i)) (hpos : ∀ i, 0 < i → i ≤ rungs (X := X) → f i ≠ ⊥)
    (v : Point (X := X) (Q := Q)) :
    TransformsTo (fun d : (carrier D hA (X := X) (Q := Q)).below
      ((carrier D hA (X := X) (Q := Q)).cell (added D hA v)) =>
      (carrier D hA (X := X) (Q := Q)).grade d.1)
      ((rows D sem hA field fields hp).E (added D hA v))
      (fun d => min (image D hA field fields a f d.1)
        (image D hA field fields a f (added D hA v))) := by
  let e := SupportLadderRows.index (ranks fields) a v
  have hec : e ≤ SupportLadderRows.ceiling (ranks fields) v := min_le_right _ _
  have hel : e ≤ rungs (X := X) := SupportLadderRows.index_le a v
  have he (d : Cell (carrier D hA (X := X) (Q := Q))) :
      min (image D hA field fields a f d) (image D hA field fields a f (added D hA v)) =
        f (min (rankIndex D hA field fields (SupportLadderRows.parent v) d) e) := by
    simp only [image, rankIndex_added, ← hf.map_min]
    apply congrArg f
    have hag := rankIndex_agreement D hA field fields a (SupportLadderRows.parent v) d
    dsimp only [e, SupportLadderRows.index]
    grind
  rw [show (fun d : (carrier D hA (X := X) (Q := Q)).below
      ((carrier D hA (X := X) (Q := Q)).cell (added D hA v)) =>
    (carrier D hA (X := X) (Q := Q)).grade d.1) = (fun _ => 1) from funext (below_grade_one D hA v)]
  rw [funext (row_added D sem hA field fields hp v),
    show (fun d : (carrier D hA (X := X) (Q := Q)).below
        ((carrier D hA (X := X) (Q := Q)).cell (added D hA v)) =>
      min (image D hA field fields a f d.1)
        (image D hA field fields a f (added D hA v))) =
      (fun d => f (min (rankIndex D hA field fields (SupportLadderRows.parent v) d.1) e))
      from funext (fun d => he d.1)]
  simp only [ladderRow, image]
  by_cases hz : e = 0
  · simp only [hz, Nat.min_zero, h0]
    exact TransformsTo.to_bot _
  · have ht := SupportLadderRows.transforms_positive
      (fun d : (carrier D hA (X := X) (Q := Q)).below
        ((carrier D hA (X := X) (Q := Q)).cell (added D hA v)) =>
        rankIndex D hA field fields (SupportLadderRows.parent v) d.1)
      (SupportLadderRows.ceiling (ranks fields) v) (fun i => f (min i e))
      (fun _ _ h => hf (min_le_min_right _ h)) (by simpa using h0) (fun _ => hv _)
      (fun i hi _ => hpos _ (by omega) ((min_le_right _ _).trans hel))
    simpa only [min_assoc, min_eq_right hec] using ht

theorem image_respects {j : ℕ} (a : Q) (f : ℕ → ExtOrd) (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, SelfVis 1 (f i)) (hpos : ∀ i, 0 < i → i ≤ rungs (X := X) → f i ≠ ⊥)
    (hold : RespectsSemanticsBelow sem (A, j) (fun d => f (ranks fields a (field d.1)))) :
    RespectsSemanticsBelow (rows D sem hA field fields hp) (A, j)
      (fun d => image D hA field fields a f d.1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    rcases cell_cases D hA d.1 with ⟨x, hx⟩ | ⟨v, hv'⟩
    · have hxd : GradedLe (D.cell x) (A, j) := by
        simpa only [hx, old_index] using d.2
      simpa only [hx, CellScheme.grade, old_index, image, rankIndex_old] using
        hold.orderly ⟨x, hxd⟩
    · change _ = extVisibilityReplace _ ((carrier D hA).grade d.1) _
      simp only [hv', CellScheme.grade, added_index]
      exact (hv _).symm
  · intro c
    rcases cell_cases D hA c.1 with ⟨x, hx⟩ | ⟨v, hv'⟩
    · have hxc : GradedLe (D.cell x) (A, j) := by
        simpa only [hx, old_index] using c.2
      have hl := RespectsSemanticsBelow.mono hxc hold
      have hphysical : RespectsSemanticsBelow (rows D sem hA field fields hp)
          ((carrier D hA (X := X) (Q := Q)).cell (old D hA x))
          (fun d => image D hA field fields a f d.1) := by
        apply (old_respects_iff D sem hA field fields hp x _).mpr
        simpa only [Function.comp_def, ownerEquiv,
          SeparatedSourceLayerCarrier.ownerEquiv_val, image, rankIndex_old,
          CellScheme.below.mono] using hl
      have hh := hphysical.locality ⟨old D hA x, GradedLe.refl _⟩
      rcases c with ⟨c, hc⟩
      dsimp only at hx
      subst c
      exact hh
    · rcases c with ⟨c, hc⟩
      dsimp only at hv'
      subst c
      exact image_locality D sem hA field fields hp a f hf h0 hv hpos v
  · intro c t hs hgr
    rcases cell_cases D hA t.1 with ⟨x, hx⟩ | ⟨v, hv'⟩
    · have hct : GradedLe ((carrier D hA (X := X) (Q := Q)).cell c.1)
          ((carrier D hA (X := X) (Q := Q)).cell (old D hA x)) := hx ▸ ⟨hs, hgr.le⟩
      obtain ⟨y, hy⟩ := (ownerEquiv D hA hp x).surjective ⟨c.1, hct⟩
      have hy' : c.1 = old D hA y.1 := (congrArg Subtype.val hy).symm
      have hx' : GradedLe (D.cell x) (A, j) := by simpa only [hx, old_index] using t.2
      have hscope : D.scope y.1 ⊆ D.scope x := by
        simpa only [hy', hx, CellScheme.scope, old_index] using hs
      have hgrade : D.grade y.1 = D.grade x := by
        simpa only [hy', hx, CellScheme.grade, old_index] using hgr
      obtain ⟨w, hw, hle⟩ := hold.availability ⟨y.1, y.2.trans hx'⟩ ⟨x, hx'⟩ hscope hgrade
      refine ⟨⟨old D hA w.1, by rw [old_index]; exact w.2⟩, ?_, ?_⟩
      · rw [old_index, hx, old_index]; exact hw
      · simpa only [hy', image, rankIndex_old] using hle
    · let leaf : Point (X := X) (Q := Q) := SupportLadderRows.leaf (Nat.succ_pos _) a
      refine ⟨⟨added D hA leaf, by simpa only [hv', added_index] using t.2⟩, ?_, ?_⟩
      · rw [added_index, hv', added_index]
      · change f _ ≤ f _
        apply hf
        have hl : rankIndex D hA field fields a (added D hA leaf) = rungs (X := X) := by
          exact (rankIndex_added D hA field fields a leaf).trans
            ((SupportLadderRows.index_leaf (profile := ranks fields) (Nat.succ_pos _) a a).trans
              (FiniteProfileControllers.cut_refl _ _))
        exact (rankIndex_bound D hA field fields a c.1).trans_eq hl.symm

/-- All new long rows are lawful on the installed lower domain, rather than
only on the abstract ladder table. -/
theorem ladder_respects
    (hinput : ∀ a, RespectsSemanticsBelow sem (A, 1) (fun d => fields a (field d.1)))
    (v : Point (X := X) (Q := Q)) :
    RespectsSemanticsBelow (rows D sem hA field fields hp) (A, 1)
      (fun d => ladderRow D hA field fields v d.1) := by
  by_cases ht : SupportLadderRows.ceiling (ranks fields) v = 0
  · have hz (d : Cell (carrier D hA (X := X) (Q := Q))) :
        ladderRow D hA field fields v d = ⊥ := by
      exact (SupportLadderRows.source_bot_iff _ _).mpr (by simp [ht])
    simp only [hz]
    exact ⟨fun _ => (selfVis_bot _).symm, fun c => by
      simpa only [min_self] using TransformsTo.to_bot ((rows D sem hA field fields hp).E c.1),
      fun _ t _ _ => ⟨t, rfl, le_rfl⟩⟩
  · exact image_respects D sem hA field fields hp (SupportLadderRows.parent v) _
      (SupportLadderRows.source_mono _) (SupportLadderRows.source_zero _)
      (SupportLadderRows.source_visible _) (fun i hi _ hz => by
        have hh := (SupportLadderRows.source_bot_iff _ _).mp hz
        omega)
      (rank_respects D sem field fields _ (hinput _) _)

theorem consistent (hs : sem.IsConsistent)
    (hinput : ∀ a, RespectsSemanticsBelow sem (A, 1) (fun d => fields a (field d.1))) :
    (rows D sem hA field fields hp).IsConsistent := by
  intro c
  rcases cell_cases D hA c with ⟨c, rfl⟩ | ⟨v, rfl⟩
  · apply (old_respects_iff D sem hA field fields hp c _).mpr
    simpa only [Function.comp_def, inherited_row] using hs c
  · have hr := GradeCutLayerRows.cast_respects (carrier D hA (X := X) (Q := Q))
      (rows D sem hA field fields hp) (added_index D hA v).symm
      (ladder_respects D sem hA field fields hp hinput v)
    convert hr using 1
    exact funext (row_added D sem hA field fields hp v)

def selected (a : Q) (C : ExtOrd) : Cell (carrier D hA (X := X) (Q := Q)) → ExtOrd :=
  image D hA field fields a (LadderScalarRendering.level (values (fields a)) C)

theorem selected_old (a : Q) (C : ExtOrd) (d : Cell D) :
    selected D hA field fields a C (old D hA d) = fields a (field d) := by
  simp only [selected, image, rankIndex_old, ranks, field_readback]

theorem selected_bound (a : Q) {C : ExtOrd} (hC : ∀ x, fields a x ≤ C)
    (d : Cell (carrier D hA (X := X) (Q := Q))) : selected D hA field fields a C d ≤ C :=
  level_le (values_bound hC) _

/-- A scalar lawful source now produces an actual lawful predecessor vector,
including every rung and shadow; no physical lawfulness is an input. -/
theorem selected_respects {j : ℕ} (a : Q) {C : ExtOrd} (hC : ∀ x, fields a x ≤ C)
    (hv : ∀ x, SelfVis 1 (fields a x)) (hvis : SelfVis 1 C)
    (ha : RespectsSemanticsBelow sem (A, j) (fun d => fields a (field d.1))) :
    RespectsSemanticsBelow (rows D sem hA field fields hp) (A, j)
      (fun d => selected D hA field fields a C d.1) := by
  by_cases hz : C = ⊥
  · have he (d : Cell (carrier D hA (X := X) (Q := Q))) :
        selected D hA field fields a C d = ⊥ :=
      le_bot_iff.mp ((selected_bound D hA field fields a hC d).trans_eq hz)
    simp only [he]
    exact ⟨fun _ => (selfVis_bot _).symm, fun c => by
      simpa only [min_self] using TransformsTo.to_bot ((rows D sem hA field fields hp).E c.1),
      fun _ t _ _ => ⟨t, rfl, le_rfl⟩⟩
  · apply image_respects D sem hA field fields hp a _ (level_mono (values_bound hC))
      (level_zero _ _) (level_visible hv hvis)
      (fun _ hi _ => level_pos (bot_not_values _) (values_bound hC) hz hi)
    simpa only [ranks, field_readback] using ha

/-- Complete physical prefix agreement, including unused rungs. The ceiling
is fixed while comparing selected sections. -/
theorem selected_agreement {a b : Q} {C h : ExtOrd}
    (ha : ∀ x, fields a x ≤ C) (hb : ∀ x, fields b x ≤ C) (hC : h ≤ C)
    (hag : ∀ x, min (fields a x) h = min (fields b x) h)
    (d : Cell (carrier D hA (X := X) (Q := Q))) :
    min (selected D hA field fields a C d) h = min (selected D hA field fields b C d) h := by
  rcases cell_cases D hA d with ⟨d, rfl⟩ | ⟨v, rfl⟩
  · rw [selected_old, selected_old]; exact hag _
  · have hh := render_cap_agreement (L := rungs (X := X)) (ranks fields)
      (a := a) (b := b) (p := fields a) (q := fields b) le_rfl
      (fun _ => rfl) (fun _ => rfl) ha hb hC hag v
    change min (LadderScalarRendering.level (values (fields a)) C
      (rankIndex D hA field fields a (added D hA v))) h = _
    rw [rankIndex_added]
    change min (LadderScalarRendering.level (values (fields a)) C
      (SupportLadderRows.index (ranks fields) a v)) h =
      min (LadderScalarRendering.level (values (fields b)) C
        (rankIndex D hA field fields b (added D hA v))) h
    rw [rankIndex_added]
    exact hh

/-- The parent is physically present even for a zero-rank shadow. -/
theorem parent_present (v : Point (X := X) (Q := Q)) :
    ∃ c : Cell (carrier D hA (X := X) (Q := Q)),
      (carrier D hA (X := X) (Q := Q)).cell c = (A, 1) ∧
      ladderRow D hA field fields v c = ladderRow D hA field fields v (added D hA v) := by
  refine ⟨added D hA (SupportLadderRows.leaf (Nat.succ_pos _) (SupportLadderRows.parent v)),
    added_index D hA _, ?_⟩
  simp only [ladderRow, image, rankIndex_added]
  exact SupportLadderRows.row_parent (fun a x => (rank_bound fields a x).le)
    (Nat.succ_pos _) v

theorem coded (hs : sem.IsCoded) : (rows D sem hA field fields hp).IsCoded := by
  intro c d
  rcases cell_cases D hA c with ⟨c, rfl⟩ | ⟨v, rfl⟩
  · obtain ⟨d, rfl⟩ := (ownerEquiv D hA hp c).surjective d
    rw [inherited_row]
    simpa only [CellScheme.grade, old_index] using hs c d
  · rw [row_added]
    simpa only [CellScheme.grade, added_index, ladderRow, image] using
      SupportLadderRows.source_coded (SupportLadderRows.ceiling (ranks fields) v)
        (rankIndex D hA field fields (SupportLadderRows.parent v) d.1)

/-- The selected physical vector introduces no unhosted values, including
on spare rungs: only a field value, bottom, or the fixed ceiling can occur. -/
theorem selected_supported (a : Q) (C : ExtOrd)
    (d : Cell (carrier D hA (X := X) (Q := Q))) :
    selected D hA field fields a C d = ⊥ ∨
      (∃ x, selected D hA field fields a C d = fields a x) ∨
      selected D hA field fields a C d = C := by
  rcases level_supported (values (fields a)) C (rankIndex D hA field fields a d)
      with hz | hm | hc
  · exact Or.inl hz
  · obtain ⟨_, x, hx⟩ := mem_values.mp hm
    exact Or.inr (Or.inl ⟨x, hx.symm⟩)
  · exact Or.inr (Or.inr hc)

end
end VaughtConjecture.Knight.RelativeLadderLayer
