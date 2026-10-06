/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HighGradeLifting

/-! # Choosing a coded higher row for an arbitrary lawful retained labelling

The source is constructed from the retained labels and a separately chosen
self-visible high label. It respects the old rows by fixed-key recoding,
and a direct decoder witnesses the selected section. No general faithful
composition, domination, or equality among the prescribed labels is used.

Together with `Data.bountiful`, this supplies both a selected positive
section and unrestricted bountifulness on the resulting fixed rows. It
does not require arbitrary later capped lifts to keep that positive demand.
-/

@[expose] public section

namespace VaughtConjecture.Knight.HighGradeExtension

open AmalgamationPlan Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}
  (base : Semantics D) (h : Cell D) (hh : k < D.grade h) (hfull : D.scope h = A)
  (p : D.below (A, k) → ExtOrd) (hp : RespectsSemanticsBelow base (A, k) p)
  (N : ExtOrd) (hN : SelfVis (D.grade h) N)

noncomputable def sourceValues : Finset Ordinal := by
  let _ : Fintype (D.below (A, k)) := Fintype.ofFinite _
  exact primRange p ∪ primRange (fun _ : Unit => N)

theorem supported_old (d : D.below (A, k)) : SourceCode.Supported (sourceValues p N) (p d) := by
  let _ : Fintype (D.below (A, k)) := Fintype.ofFinite _
  intro v hv
  exact Finset.mem_union_left _ (mem_primRange_of_eq hv)

theorem supported_new : SourceCode.Supported (sourceValues p N) N := by
  intro v hv
  apply Finset.mem_union_right
  exact mem_primRange_of_eq (target := fun _ : Unit => N) (d := ()) hv

/-- The new high row is selected jointly with its selected labelling. -/
noncomputable def adapted : Data D k where
  base := base
  high := h
  above := hh
  full := hfull
  profile d := SourceCode.encode (D.grade h) (sourceValues p N) (p d)
  lawful := SourceCode.respectsBelow (D.grade h) (sourceValues p N) hh.le hp
    (supported_old p N)
  diagonal := SourceCode.encode (D.grade h) (sourceValues p N) N
  visible := SourceCode.encode_selfVis _ _ le_rfl hN

def selected (d : Cell D) : ExtOrd :=
  if hd : D.grade d ≤ k then p (Data.oldCell d hd) else if d = h then N else ⊥

theorem selected_old (d : Cell D) (hd : D.grade d ≤ k) :
    selected h p N d = p (Data.oldCell d hd) := by simp only [selected, hd, ↓reduceDIte]

include hh in
theorem selected_high : selected h p N h = N := by
  simp only [selected, not_le_of_gt hh, ↓reduceDIte, ↓reduceIte]

theorem selected_other (d : Cell D) (hd : ¬D.grade d ≤ k) (he : d ≠ h) :
    selected h p N d = ⊥ := by simp only [selected, hd, he, ↓reduceDIte, ↓reduceIte]

include hh in
theorem selected_supported (d : Cell D) :
    SourceCode.Supported (sourceValues p N) (selected h p N d) := by
  by_cases hd : D.grade d ≤ k
  · rw [selected_old h p N d hd]
    exact supported_old p N _
  · by_cases he : d = h
    · subst d
      rw [selected_high h hh p N]
      exact supported_new p N
    · rw [selected_other h p N d hd he]
      exact SourceCode.supported_bot _

include hh hp hN in
theorem selected_visible (d : Cell D) : SelfVis (D.grade d) (selected h p N d) := by
  by_cases hd : D.grade d ≤ k
  · rw [selected_old h p N d hd]
    exact (hp.orderly _).symm
  · by_cases he : d = h
    · subst d
      rw [selected_high h hh p N]
      exact hN
    · rw [selected_other h p N d hd he]
      exact selfVis_bot _

theorem source_read (d : D.below (D.cell h)) :
    (adapted base h hh hfull p hp N hN).rows.E h d =
      SourceCode.encode (D.grade h) (sourceValues p N) (selected h p N d.1) := by
  simp only [Data.rows, adapted, not_le_of_gt hh, ↓reduceIte]
  by_cases hd : D.grade d.1 ≤ k
  · simp only [Data.display, selected, hd, ↓reduceDIte]
  · by_cases he : d.1 = h
    · simp only [Data.display, selected, he, not_le_of_gt hh, ↓reduceDIte, ↓reduceIte]
    · simp only [Data.display, selected, hd, he, ↓reduceDIte, ↓reduceIte,
        SourceCode.encode]

/-- The new row has exactly the equalities of the selected labels on its
actual occurrences. In particular, retained positive highs are not muted. -/
theorem source_eq_iff (d e : D.below (D.cell h)) :
    (adapted base h hh hfull p hp N hN).rows.E h d =
        (adapted base h hh hfull p hp N hN).rows.E h e ↔
      selected h p N d.1 = selected h p N e.1 := by
  rw [source_read base h hh hfull p hp N hN d, source_read base h hh hfull p hp N hN e]
  exact SourceCode.encode_eq_iff _ _ (selected_supported h hh p N d.1)
    (selected_supported h hh p N e.1)

theorem source_bot_iff (d : D.below (D.cell h)) :
    (adapted base h hh hfull p hp N hN).rows.E h d = ⊥ ↔ selected h p N d.1 = ⊥ := by
  rw [source_read base h hh hfull p hp N hN d]
  change SourceCode.encode _ _ _ = SourceCode.encode (D.grade h) (sourceValues p N) ⊥ ↔ _
  exact SourceCode.encode_eq_iff _ _ (selected_supported h hh p N d.1)
    (SourceCode.supported_bot _)

/-- All retained labels, including previously active high controllers, are
literal. The new label is any self-visible value, including bottom or top. -/
theorem selected_respects :
    RespectsSemantics (adapted base h hh hfull p hp N hN).rows (selected h p N) where
  orderly d := (selected_visible base h hh p hp N hN d).symm
  locality c := by
    let F := adapted base h hh hfull p hp N hN
    change TransformsTo _ (F.rows.E c) (fun d => min (selected h p N d.1) (selected h p N c))
    by_cases hc : D.grade c ≤ k
    · rw [F.row_old hc]
      have ht := hp.locality (Data.oldCell c hc)
      dsimp only [Data.oldCell, CellScheme.below.incl] at ht
      dsimp only [F, adapted]
      convert ht using 1
      funext d
      rw [selected_old h p N c hc, selected_old h p N d.1 (d.2.2.trans hc)]
      rfl
    · by_cases he : c = h
      · subst c
        have ht := SourceCode.outgoing (fun d : D.below (D.cell h) => D.grade d.1)
          (fun d => selected h p N d.1) (D.grade h) (sourceValues p N)
          (fun d => d.2.2) (fun d => selected_supported h hh p N d.1) hN
        have hs : F.rows.E h = fun d =>
            SourceCode.encode (D.grade h) (sourceValues p N) (selected h p N d.1) :=
          funext (source_read base h hh hfull p hp N hN)
        rw [hs, selected_high h hh p N]
        exact ht
      · simpa only [selected_other h p N c hc he, min_bot_right] using
          (TransformsTo.to_bot (grade := fun d : D.below (D.cell c) => D.grade d.1) (F.rows.E c))
  availability d e hs hg := by
    by_cases hd : D.grade d ≤ k
    · have he : D.grade e ≤ k := hg ▸ hd
      obtain ⟨f, hf, hv⟩ := hp.availability (Data.oldCell d hd) (Data.oldCell e he) hs hg
      refine ⟨f.1, hf, ?_⟩
      simpa only [selected_old h p N d hd, selected_old h p N f.1 f.2.2,
        show Data.oldCell f.1 f.2.2 = f from Subtype.ext rfl] using hv
    · by_cases he : d = h
      · refine ⟨d, ?_, le_rfl⟩
        rw [he]
        exact (adapted base h hh hfull p hp N hN).high_index
          (by simpa only [adapted, he] using hs) (by simpa only [adapted, he] using hg)
      · exact ⟨e, rfl, by rw [selected_other h p N d hd he]; exact bot_le⟩

theorem coded (hb : base.IsCoded) : (adapted base h hh hfull p hp N hN).rows.IsCoded := by
  intro c d
  let F := adapted base h hh hfull p hp N hN
  change IsCodedLabel (D.grade c) (F.rows.E c d)
  by_cases hc : D.grade c ≤ k
  · rw [F.row_old hc]
    exact hb c d
  · by_cases he : c = h
    · subst c
      rw [source_read base h hh hfull p hp N hN]
      exact SourceCode.encode_coded _ _ _
    · exact Or.inl (F.row_mute hc he d)

include hh hfull hp hN in
/-- A genuine existence theorem: the codebook, source row, selected
section, consistency, and all unrestricted lifts are constructed. -/
theorem exists_extension (hk : 1 ≤ k) (hc : base.IsConsistent)
    (hb : base.IsBountiful) (hcode : base.IsCoded) :
    ∃ (rows : Semantics D) (q : Cell D → ExtOrd),
      rows.IsConsistent ∧ rows.IsBountiful ∧ rows.IsCoded ∧ RespectsSemantics rows q ∧
      (∀ c, D.grade c ≤ k → rows.E c = base.E c) ∧
      (∀ d : D.below (A, k), q d.1 = p d) ∧ q h = N := by
  let F := adapted base h hh hfull p hp N hN
  refine ⟨F.rows, selected h p N, F.consistent hc, F.bountiful hk hb,
    coded base h hh hfull p hp N hN hcode, selected_respects base h hh hfull p hp N hN,
    fun c hc => F.row_old hc, ?_, selected_high h hh p N⟩
  intro d
  rw [selected_old h p N d.1 d.2.2]
  exact congrArg p (Subtype.ext rfl)

variable {n : ℕ} {D : CellScheme (ι := Fin n) Finset.univ} {k : ℕ}

/-- Complete carrier packaging. Completeness belongs to the unchanged carrier. -/
noncomputable def domain (base : SemScheme n) (h : Cell base.scheme)
    (hh : k < base.scheme.grade h) (hfull : base.scheme.scope h = Finset.univ)
    (hk : 1 ≤ k) (p : base.scheme.below (Finset.univ, k) → ExtOrd)
    (hp : RespectsSemanticsBelow base.rows (Finset.univ, k) p)
    (N : ExtOrd) (hN : SelfVis (base.scheme.grade h) N) : SemScheme n where
  scheme := base.scheme
  rows := (adapted base.rows h hh hfull p hp N hN).rows
  consistent := (adapted base.rows h hh hfull p hp N hN).consistent base.consistent
  bountiful := (adapted base.rows h hh hfull p hp N hN).bountiful hk base.bountiful
  rows_coded := coded base.rows h hh hfull p hp N hN base.rows_coded
  complete := base.complete

end VaughtConjecture.Knight.HighGradeExtension
