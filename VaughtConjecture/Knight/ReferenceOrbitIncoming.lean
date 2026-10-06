/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReferenceOrbitRow
public import VaughtConjecture.Knight.FiniteOrbitEmbedding
public import VaughtConjecture.Knight.SourceBlockPadding

/-! # Incoming finite-face transport for model-derived orbit columns

The actual old witness determines the order of the source blocks. Padding the
new row by one block provides room for a bottom-reflecting interpolation from
requested proper labels to those columns. No inverse transformation is assumed.
The old semantic rows are unchanged; the new row's inherited source entries are
padded, rather than left literal as in `ReferenceOrbitRow`.
-/

@[expose] public section

namespace VaughtConjecture.Knight.ReferenceContext

open TypeTower StageType Transform Value ExtOrd VaughtConjecture.AmalgamationPlan

universe w
variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}
  {n : ℕ} {t : Fin n ↪ M} {reqs : List BlockRequest}
  {C : ReferenceContext R t reqs}

namespace FullController

variable (F : C.FullController)
variable (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block)

/-- The block is extracted from the actual reference source, not chosen from
the requested face's order type. -/
noncomputable def sourceBlock (i : Fin reqs.length) : ℕ :=
  (F.reference_source_code hblocks i).choose

theorem reference_sourceBlock (i : Fin reqs.length) :
    C.p₀.scheme.rows.E F.cell (F.reference hblocks i) =
      ofOrd (Ordinal.omega0 * F.sourceBlock hblocks i + C.repOff reqs[i.val].block) :=
  (F.reference_source_code hblocks i).choose_spec

theorem orbit_sourceBlock (i : Fin reqs.length) :
    F.orbitSource hblocks i =
      ofOrd (Ordinal.omega0 * F.sourceBlock hblocks i + reqs[i.val].offset) := by
  rw [orbitSource, F.reference_sourceBlock hblocks i,
    extVisibilityReplace_of_finitePart_lt
      (by simpa only [finitePart_mul_add] using C.rep_off_lt _ (List.getElem_mem i.isLt)),
    limitPart_mul_add]

/-- The existing witness reads the floor of every reference source as the
requested block floor. This is derived by its orbit clause at offset zero. -/
theorem sourceBlock_readback {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop C.N) τ)
    (hread : ∀ d : F.Old, τ (C.p₀.scheme.rows.E F.cell d) =
      min (C.p₀.label d.1) (C.p₀.label F.cell)) (i : Fin reqs.length) :
    τ (ofOrd (Ordinal.omega0 * F.sourceBlock hblocks i)) = ofOrd reqs[i.val].block := by
  have hr := List.getElem_mem i.isLt
  have hrep : τ (C.p₀.scheme.rows.E F.cell (F.reference hblocks i)) =
      ofOrd (reqs[i.val].block + C.repOff reqs[i.val].block) := by
    rw [hread]
    change min (C.p₀.label (C.repBase reqs[i.val].block)) (C.p₀.label F.cell) = _
    rw [min_eq_left ((C.rep_le_cap _ hr).trans F.dominates), C.rep_label _ hr]
  have hc := hτ.clause5 (C.p₀.scheme.rows.E F.cell (F.reference hblocks i)) C.N
    (by rw [gTop_of_le le_rfl]; exact le_top) 0 (Nat.zero_le _)
  rw [hrep, extVisibilityReplace_rep (hblocks _ hr) (C.rep_off_lt _ hr),
    Nat.cast_zero, add_zero] at hc
  rw [F.reference_sourceBlock hblocks i, extVisibilityReplace_of_finitePart_lt
    (by simpa only [finitePart_mul_add] using C.rep_off_lt _ hr),
    limitPart_mul_add, Nat.cast_zero, add_zero] at hc
  exact hc

theorem sourceBlock_strict (i j : Fin reqs.length)
    (h : reqs[i.val].block < reqs[j.val].block) :
    F.sourceBlock hblocks i < F.sourceBlock hblocks j := by
  obtain ⟨τ, hτ, _, hread⟩ := F.exists_exact_witness
  apply lt_of_not_ge
  intro hle
  have hs : ofOrd (Ordinal.omega0 * F.sourceBlock hblocks j) ≤
      ofOrd (Ordinal.omega0 * F.sourceBlock hblocks i) :=
    ofOrd_le_ofOrd.mpr (mul_le_mul_right (Nat.cast_le.mpr hle) _)
  have hh := hτ.mono hs
  rw [F.sourceBlock_readback hblocks hτ hread j,
    F.sourceBlock_readback hblocks hτ hread i, ofOrd_le_ofOrd] at hh
  exact (not_le_of_gt h) hh

theorem sourceBlock_equal (i j : Fin reqs.length)
    (h : reqs[i.val].block = reqs[j.val].block) :
    F.sourceBlock hblocks i = F.sourceBlock hblocks j := by
  have href : F.reference hblocks i = F.reference hblocks j :=
    Subtype.ext (congrArg C.repBase h)
  have hs := congrArg (C.p₀.scheme.rows.E F.cell) href
  rw [F.reference_sourceBlock hblocks i, F.reference_sourceBlock hblocks j] at hs
  exact_mod_cast (code_inj (ofOrd_inj.mp hs)).1

/-- The fixed source map uses the actual source blocks, each with one spare
initial block. It fixes bottom and preserves respect for the original face rows. -/
noncomputable def incomingMap : ExtOrd → ExtOrd :=
  FiniteOrbitEmbedding.interpolate C.N (fun i : Fin reqs.length => reqs[i.val].block)
    (fun i => Ordinal.omega0 * (F.sourceBlock hblocks i + 1 : ℕ))

theorem incomingMap_witness : Witness (gTop C.N) (F.incomingMap hblocks) :=
  FiniteOrbitEmbedding.interpolate_witness _ _ _ (fun _ => limitPart_omega0_mul _)

theorem incomingMap_reflects_bottom (x : ExtOrd) (hx : F.incomingMap hblocks x = ⊥) :
    x = ⊥ := FiniteOrbitEmbedding.interpolate_reflects_bottom _ _ _ x hx

/-- The map agrees with every padded orbit source at the requested offset. -/
theorem incomingMap_request (i : Fin reqs.length) :
    F.incomingMap hblocks (ofOrd reqs[i.val].value) =
      SourceBlockPadding.pad (F.orbitSource hblocks i) := by
  rw [F.orbit_sourceBlock hblocks i, SourceBlockPadding.pad_code]
  apply FiniteOrbitEmbedding.interpolate_at
  · intro j; exact hblocks _ (List.getElem_mem j.isLt)
  · intro j; exact limitPart_omega0_mul _
  · intro j k h
    exact (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono
      (Nat.cast_lt.mpr (Nat.add_lt_add_right (F.sourceBlock_strict hblocks j k h) 1))
  · intro j k h
    rw [F.sourceBlock_equal hblocks j k h]
  · intro j _
    have hn : (1 : Ordinal.{0}) ≤ (F.sourceBlock hblocks j + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (F.sourceBlock hblocks j))
    simpa only [mul_one] using mul_le_mul_right hn Ordinal.omega0
  · exact (C.offset_lt _ (List.getElem_mem i.isLt)).le

/-- New-row sources, including its inherited columns, are padded together. -/
noncomputable def paddedSource (d : F.Old ⊕ Fin reqs.length) : ExtOrd :=
  SourceBlockPadding.pad (F.source hblocks d)

theorem paddedSource_coded (d : F.Old ⊕ Fin reqs.length) :
    IsCodedLabel C.N (F.paddedSource hblocks d) :=
  SourceBlockPadding.pad_coded (F.source_coded hblocks d)

/-- Padding retains the exact old and requested target readback. -/
theorem paddedSource_transformsTo (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ C.N) :
    TransformsTo (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade)
      (F.paddedSource hblocks) F.target :=
  SourceBlockPadding.transforms_padded_source (F.transformsTo hblocks newGrade hgrade)

/-- The padded old prefix still respects the literal inherited semantics. -/
theorem paddedSource_old_respects :
    RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell F.cell)
      (fun d => F.paddedSource hblocks (Sum.inl d)) :=
  SourceBlockPadding.pad_respects (F.source_old_respects hblocks) F.grade_le

/-- The bottom-source condition is automatic at an inherited mute occurrence:
actual old-row consistency, not the intended target's bottom label, supplies it. -/
theorem source_bot_of_inherited_diagonal_bot (d : F.Old)
    (hd : C.p₀.scheme.rows.E d.1 ⟨d.1, GradedLe.refl _⟩ = ⊥) :
    F.source hblocks (Sum.inl d) = ⊥ := by
  obtain ⟨g, σ, _, _, hb, _, _, he⟩ := (F.source_old_respects hblocks).locality d
  have hh := he ⟨d.1, GradedLe.refl _⟩
  change min (F.source hblocks (Sum.inl d)) (F.source hblocks (Sum.inl d)) =
    min (σ (C.p₀.scheme.rows.E d.1 ⟨d.1, GradedLe.refl _⟩)) (g _) at hh
  simpa only [min_self, hd, hb, min_bot_left] using hh

/-- Incoming-face closure for any occurrence-indexed requested labelling,
including bottom occurrences. The indexing does not identify cells. -/
theorem incoming_face_respects
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ}
    (occ : D.below BJ → Option (Fin reqs.length))
    (hgrade : ∀ d : D.below BJ, D.grade d.1 ≤ C.N)
    (hr : RespectsSemanticsBelow sem BJ
      (fun d => (occ d).elim ⊥ (fun i => ofOrd reqs[i.val].value))) :
    RespectsSemanticsBelow sem BJ
      (fun d => (occ d).elim ⊥ (fun i => SourceBlockPadding.pad (F.orbitSource hblocks i))) := by
  have hm := FiniteOrbitEmbedding.map_respects hr hgrade
    (F.incomingMap_witness hblocks) (F.incomingMap_reflects_bottom hblocks)
  have he : (fun d => F.incomingMap hblocks
      ((occ d).elim ⊥ (fun i => ofOrd reqs[i.val].value))) =
      (fun d => (occ d).elim ⊥ (fun i => SourceBlockPadding.pad (F.orbitSource hblocks i))) := by
    funext d
    cases occ d with
    | none => exact (F.incomingMap_witness hblocks).bot
    | some i => exact F.incomingMap_request hblocks i
  rw [he] at hm
  exact hm

private theorem sources_equal_at_invisible_output
    {K : ℕ} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop K) τ)
    {a b t : Ordinal.{0}} (ha : τ (ofOrd a) = ofOrd t) (hb : τ (ofOrd b) = ofOrd t)
    (ht : finitePart t < K) : a = b := by
  have hcomm : ∀ x i, i ≤ K →
      τ (extVisibilityReplace x K i) = extVisibilityReplace (τ x) K i :=
    fun x i hi => hτ.clause5 x K (by rw [gTop_of_le le_rfl]; exact le_top) i hi
  have hnv : ¬ SelfVis K (ofOrd t) := by
    rw [selfVis_ofOrd_iff]; exact not_le_of_gt ht
  have hblock : limitPart a = limitPart b := by
    rcases lt_trichotomy (limitPart a) (limitPart b) with h | h | h
    · have hv := selfVis_of_equal_images_separated_blocks hτ.mono
        (fun x => hcomm x K le_rfl) h (ha.trans hb.symm)
      exact False.elim (hnv (ha ▸ hv))
    · exact h
    · have hv := selfVis_of_equal_images_separated_blocks hτ.mono
        (fun x => hcomm x K le_rfl) h (hb.trans ha.symm)
      exact False.elim (hnv (hb ▸ hv))
  have hfa := finitePart_eq_of_nonvisible_image hcomm ha ht
  have hfb := finitePart_eq_of_nonvisible_image hcomm hb ht
  rw [← decomposition a, ← decomposition b, hblock, hfa, hfb]

/-- At a proper requested value, overlap source agreement is forced by the
actual witness. It is not an extra source-equality assumption. -/
theorem source_eq_orbit_of_target (d : F.Old ⊕ Fin reqs.length) (i : Fin reqs.length)
    (hd : F.target d = ofOrd reqs[i.val].value) :
    F.source hblocks d = F.orbitSource hblocks i := by
  obtain ⟨τ, hτ, _, hread⟩ := F.exists_exact_witness
  have htarget : ∀ e, τ (F.source hblocks e) = F.target e := by
    intro e
    cases e with
    | inl e => exact hread e
    | inr j => exact F.orbit_readback hblocks hτ hread j
  have ha := (htarget d).trans hd
  have hb := F.orbit_readback hblocks hτ hread i
  obtain ⟨b, hsrc⟩ := F.orbitSource_code hblocks i
  rcases F.source_coded hblocks d with hbot | ⟨a, j, _, hsrc'⟩
  · rw [hbot, hτ.bot] at ha
    exact False.elim (ofOrd_ne_bot _ ha.symm)
  · have ht : finitePart reqs[i.val].value < C.N := by
      have hf := finitePart_limitPart_add_nat reqs[i.val].block reqs[i.val].offset
      rw [hblocks _ (List.getElem_mem i.isLt)] at hf
      exact hf ▸ C.offset_lt _ (List.getElem_mem i.isLt)
    rw [hsrc', hsrc, ofOrd_inj]
    exact sources_equal_at_invisible_output hτ (hsrc' ▸ ha) (hsrc ▸ hb) ht

/-- An actual incoming face can use both old and new occurrences. Proper labels
need target agreement only: the previous lemma supplies their source agreement.
Bottom occurrences must really be bottom in the source row; witness collapse
alone would not establish this. -/
theorem incoming_actual_respects
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ}
    (r : D.below BJ → ExtOrd) (occ : D.below BJ → F.Old ⊕ Fin reqs.length)
    (hgrade : ∀ d : D.below BJ, D.grade d.1 ≤ C.N)
    (hr : RespectsSemanticsBelow sem BJ r)
    (hcover : ∀ d, (r d = ⊥ ∧ F.source hblocks (occ d) = ⊥) ∨
      ∃ i : Fin reqs.length, r d = ofOrd reqs[i.val].value ∧ F.target (occ d) = r d) :
    RespectsSemanticsBelow sem BJ (fun d => F.paddedSource hblocks (occ d)) := by
  have hm := FiniteOrbitEmbedding.map_respects hr hgrade
    (F.incomingMap_witness hblocks) (F.incomingMap_reflects_bottom hblocks)
  have he : (fun d => F.incomingMap hblocks (r d)) =
      (fun d => F.paddedSource hblocks (occ d)) := by
    funext d
    rcases hcover d with ⟨hb, hs⟩ | ⟨i, hi, ht⟩
    · rw [hb, (F.incomingMap_witness hblocks).bot, paddedSource, hs,
        SourceBlockPadding.pad_bot]
    · rw [hi, F.incomingMap_request hblocks i, paddedSource,
        F.source_eq_orbit_of_target hblocks (occ d) i (ht.trans hi)]
  rw [he] at hm
  exact hm

/-- The same padded sources still serve every canonical row retuning. This is
not arbitrary-profile or whole-domain bountifulness. -/
theorem paddedSource_retuned (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ C.N) (p : F.Old → ExtOrd)
    (hvis : SelfVis C.N (p F.owner))
    (hloc : TransformsTo (fun d : F.Old => C.p₀.scheme.scheme.grade d.1)
      (C.p₀.scheme.rows.E F.cell) (fun d => min (p d) (p F.owner))) :
    TransformsTo (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade)
      (F.paddedSource hblocks) (F.retunedTarget hblocks p) :=
  SourceBlockPadding.transforms_padded_source
    (F.retunedTarget_transformsTo hblocks newGrade hgrade p hvis hloc)

/-- Padding includes the genuinely fresh owner's diagonal. -/
noncomputable def paddedOwnedSource (b : ℕ) (d : Option (F.Old ⊕ Fin reqs.length)) : ExtOrd :=
  SourceBlockPadding.pad
    (FreeDiagonal.append (F.source hblocks) (FreeDiagonal.source C.N b) d)

theorem paddedOwnedSource_none (b : ℕ) :
    F.paddedOwnedSource hblocks b none = FreeDiagonal.source C.N (b + 1) :=
  SourceBlockPadding.pad_code b C.N

theorem paddedOwnedSource_some (b : ℕ) (d : F.Old ⊕ Fin reqs.length) :
    F.paddedOwnedSource hblocks b (some d) = F.paddedSource hblocks d := rfl

/-- The already constructed fixed free diagonal remains available after padding,
before any later retuning or choice of the new owner's high label. -/
theorem exists_padded_owned_row (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ reqs[i.val].offset) :
    ∃ b : ℕ, 0 < b ∧
      (∀ d, IsCodedLabel C.N (F.paddedOwnedSource hblocks b d)) ∧
      (∀ d, SelfVis
        (FreeDiagonal.append
          (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade) C.N d)
        (F.paddedOwnedSource hblocks b d)) ∧
      ∀ (p : F.Old → ExtOrd), SelfVis C.N (p F.owner) →
        TransformsTo (fun d : F.Old => C.p₀.scheme.scheme.grade d.1)
          (C.p₀.scheme.rows.E F.cell) (fun d => min (p d) (p F.owner)) →
        ∀ U, SelfVis C.N U → p F.owner ≤ U →
          TransformsTo
            (FreeDiagonal.append
              (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade) C.N)
            (F.paddedOwnedSource hblocks b)
            (FreeDiagonal.append (F.retunedTarget hblocks p) U) := by
  obtain ⟨b, hb, _, hcode, ho, hserve⟩ := F.exists_fixed_owned_row hblocks newGrade hgrade
  refine ⟨b, hb, fun d => SourceBlockPadding.pad_coded (hcode d), ?_, ?_⟩
  · intro d
    change extVisibilityReplace (SourceBlockPadding.pad _) _ _ = SourceBlockPadding.pad _
    rw [← SourceBlockPadding.pad_comm, ho d]
  · intro p hp hloc U hU hle
    exact SourceBlockPadding.transforms_padded_source (hserve p hp hloc U hU hle)

/-- Universal response readback is retained, not merely the intended display:
every faithful response at the fresh owner still has the requested finite labels. -/
theorem padded_owned_forced_readback (b : ℕ) (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ C.N)
    (q : Option (F.Old ⊕ Fin reqs.length) → ExtOrd)
    (hvis : SelfVis C.N (q none))
    (hloc : TransformsTo
      (FreeDiagonal.append
        (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade) C.N)
      (F.paddedOwnedSource hblocks b) (fun d => min (q d) (q none)))
    (hcap : C.p₀.label C.capBase ≤ q none)
    (href : ∀ i, q (some (Sum.inl (F.reference hblocks i))) =
      C.p₀.label (C.repBase reqs[i.val].block)) (i : Fin reqs.length) :
    q (some (Sum.inr i)) = ofOrd reqs[i.val].value :=
  F.owned_forced_readback hblocks b newGrade hgrade q hvis
    (SourceBlockPadding.transforms_padded_source_iff.mp hloc) hcap href i

end FullController

end VaughtConjecture.Knight.ReferenceContext
