/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReferenceContext
public import VaughtConjecture.Knight.FreeDiagonal
public import VaughtConjecture.Knight.MixedGradeInterpolation

/-! # Completing finite reference orbits with the existing witness

An actual `ReferenceContext` supplies a coded old row whose cap dominates all finite requests.
The source for a new requested offset is the replacement of the old representative's source.
One normalized witness of the old row reads every such new source correctly. No inverse,
composition of faithful transformations, or independently chosen new source order is used.

Requests are indexed by their positions in the list, so repeated requests remain distinct
occurrences. Old row entries stay literal; their target values are capped at the controller,
not asserted to stay literal above that cap. The new sources have the requested finite parts,
are coded in existing source blocks, and lie strictly below the old diagonal source.

This is a source-row construction and faithful readback, not an enlarged cell scheme.
Candidate-side and mixed-scope localities, availability outside the row, bountifulness, and the
infinite-label branch are not supplied here. In particular it is not terminal comparison.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType Transform Value ExtOrd VaughtConjecture.AmalgamationPlan

universe w

namespace ReferenceContext

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}
  {n : ℕ} {t : Fin n ↪ M} {reqs : List BlockRequest}
  (C : ReferenceContext R t reqs)

/-- A full-scope controller of the reference grade, dominating the reference cap. -/
structure FullController where
  cell : Cell C.p₀.scheme.scheme
  index : C.p₀.scheme.scheme.cell cell = (Finset.univ, C.N)
  dominates : C.p₀.label C.capBase ≤ C.p₀.label cell

/-- Completeness and actual availability choose the controller; no new row is postulated. -/
theorem exists_fullController : Nonempty C.FullController := by
  have hmem : ((Finset.univ : Finset (Fin C.m)), C.N) ∈
      Plan.gradedPlan C.p₀.scheme.scheme.plan := by
    refine Plan.mem_gradedPlan.mpr
      ⟨C.p₀.scheme.scheme.isPlan.domain_mem, ?_, ?_⟩
    · rw [← C.cap_grade]
      exact C.p₀.scheme.scheme.grade_pos C.capBase
    · rw [← C.cap_grade]
      exact (C.p₀.scheme.scheme.grade_le_card_scope C.capBase).trans
        (Finset.card_le_card (Finset.subset_univ _))
  obtain ⟨d, hd⟩ := C.p₀.scheme.complete _ hmem
  obtain ⟨c, hc, hle⟩ := C.p₀.respects.availability C.capBase d
    (by rw [show C.p₀.scheme.scheme.scope d = Finset.univ from congrArg Prod.fst hd]
        exact Finset.subset_univ _)
    (C.cap_grade.trans (congrArg Prod.snd hd).symm)
  exact ⟨⟨c, hc.trans hd, hle⟩⟩

/-- The grade bound on a reference cell is derived from its literal ordinal label. -/
theorem rep_grade_le {r : BlockRequest} (hr : r ∈ reqs)
    (hblock : limitPart r.block = r.block) :
    C.p₀.scheme.scheme.grade (C.repBase r.block) ≤ C.repOff r.block := by
  have h := (C.p₀.respects.orderly (C.repBase r.block)).symm
  rw [C.rep_label r hr] at h
  have hgrade := selfVis_ofOrd_iff.mp h
  have hfp := finitePart_limitPart_add_nat r.block (C.repOff r.block)
  rw [hblock] at hfp
  rwa [hfp] at hgrade

namespace FullController

variable {C} (F : C.FullController)

/-- The actual old lower domain, with occurrences retained. -/
abbrev Old := C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell F.cell)

/-- The old owner as an occurrence in its own lower domain. -/
def owner : F.Old := ⟨F.cell, GradedLe.refl _⟩

theorem grade_eq : C.p₀.scheme.scheme.grade F.cell = C.N :=
  congrArg Prod.snd F.index

theorem grade_le (d : F.Old) : C.p₀.scheme.scheme.grade d.1 ≤ C.N :=
  d.2.2.trans_eq F.grade_eq

/-- One exact bounded shifter for the actual reference row. -/
theorem exists_exact_witness :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop C.N) τ ∧
      (∀ x, τ x ≤ C.p₀.label F.cell) ∧
      (∀ d : F.Old, τ (C.p₀.scheme.rows.E F.cell d) =
        min (C.p₀.label d.1) (C.p₀.label F.cell)) := by
  have h := exists_bounded_exact_capped_witness
    (c := F.owner) (p := fun d : F.Old => C.p₀.label d.1)
    (fun d => d.2.2) (C.p₀.respects.orderly F.cell).symm
    (C.p₀.respects.locality F.cell)
  change ∃ τ, Witness (gTop (C.p₀.scheme.scheme.grade F.cell)) τ ∧ _ at h
  rwa [F.grade_eq] at h

variable (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block)

/-- Position-indexed references: equal values do not identify occurrences. -/
def reference (i : Fin reqs.length) : F.Old :=
  ⟨C.repBase reqs[i.val].block, by
    rw [F.index]
    exact ⟨Finset.subset_univ _,
      (C.rep_grade_le (List.getElem_mem i.isLt) (hblocks _ (List.getElem_mem i.isLt))).trans
        (C.rep_off_lt _ (List.getElem_mem i.isLt)).le⟩⟩

/-- Fixed source columns, determined by the old row, the references, and requested offsets. -/
noncomputable def orbitSource (i : Fin reqs.length) : ExtOrd :=
  extVisibilityReplace (C.p₀.scheme.rows.E F.cell (F.reference hblocks i)) C.N reqs[i.val].offset

/-- The extended row leaves every old source literally unchanged. -/
noncomputable def source : F.Old ⊕ Fin reqs.length → ExtOrd :=
  Sum.elim (C.p₀.scheme.rows.E F.cell) (F.orbitSource hblocks)

/-- Old targets are capped; finite new requests are literal. -/
noncomputable def target : F.Old ⊕ Fin reqs.length → ExtOrd :=
  Sum.elim (fun d => min (C.p₀.label d.1) (C.p₀.label F.cell))
    (fun i => ofOrd reqs[i.val].value)

theorem source_old (d : F.Old) :
    F.source hblocks (Sum.inl d) = C.p₀.scheme.rows.E F.cell d := rfl

theorem target_new (i : Fin reqs.length) :
    F.target (Sum.inr i) = ofOrd reqs[i.val].value := rfl

/-- The same old shifter, not a composition, evaluates every new orbit column. -/
theorem orbit_readback {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop C.N) τ)
    (hread : ∀ d : F.Old, τ (C.p₀.scheme.rows.E F.cell d) =
      min (C.p₀.label d.1) (C.p₀.label F.cell)) (i : Fin reqs.length) :
    τ (F.orbitSource hblocks i) = ofOrd reqs[i.val].value := by
  have hr := List.getElem_mem i.isLt
  rw [orbitSource, hτ.clause5 _ C.N (by rw [gTop_of_le le_rfl]; exact le_top)
    _ (C.offset_lt _ hr).le, hread]
  change extVisibilityReplace
    (min (C.p₀.label (C.repBase reqs[i.val].block)) (C.p₀.label F.cell)) C.N reqs[i.val].offset = _
  rw [min_eq_left ((C.rep_le_cap _ hr).trans F.dominates), C.rep_label _ hr]
  exact extVisibilityReplace_rep (hblocks _ hr) (C.rep_off_lt _ hr)

/-- Simultaneous faithful readback on the old lower domain and all new occurrences. -/
theorem transformsTo (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ C.N) :
    TransformsTo (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade)
      (F.source hblocks) F.target := by
  obtain ⟨τ, hτ, _, hread⟩ := F.exists_exact_witness
  apply hτ.transformsTo
  intro d
  cases d with
  | inl d =>
    change min (C.p₀.label d.1) (C.p₀.label F.cell) =
      min (τ (C.p₀.scheme.rows.E F.cell d)) (gTop C.N (C.p₀.scheme.scheme.grade d.1))
    rw [gTop_of_le (F.grade_le d), min_top_right, hread]
  | inr i =>
    change ofOrd reqs[i.val].value = min (τ (F.orbitSource hblocks i)) (gTop C.N (newGrade i))
    rw [gTop_of_le (hgrade i), min_top_right, F.orbit_readback hblocks hτ hread]

/-- Strict domination of the requested outputs forces strict domination of their sources
by the unchanged diagonal. This is a row inequality, not scheme-wide availability. -/
theorem orbitSource_lt_diagonal (i : Fin reqs.length) :
    F.orbitSource hblocks i < C.p₀.scheme.rows.E F.cell F.owner := by
  obtain ⟨τ, hτ, _, hread⟩ := F.exists_exact_witness
  apply lt_of_not_ge
  intro hle
  have h := hτ.mono hle
  rw [F.orbit_readback hblocks hτ hread, hread] at h
  change min (C.p₀.label F.cell) (C.p₀.label F.cell) ≤ ofOrd reqs[i.val].value at h
  rw [min_self] at h
  exact (not_le_of_gt ((C.cap_dom _ (List.getElem_mem i.isLt)).trans_le F.dominates)) h

/-- The finite part of a reference source is forced by its invisible output. -/
theorem reference_source_code (i : Fin reqs.length) :
    ∃ b : ℕ, C.p₀.scheme.rows.E F.cell (F.reference hblocks i) =
      ofOrd (Ordinal.omega0 * b + C.repOff reqs[i.val].block) := by
  obtain ⟨τ, hτ, _, hread⟩ := F.exists_exact_witness
  have hr := List.getElem_mem i.isLt
  have hrep : τ (C.p₀.scheme.rows.E F.cell (F.reference hblocks i)) =
      ofOrd (reqs[i.val].block + C.repOff reqs[i.val].block) := by
    rw [hread]
    change min (C.p₀.label (C.repBase reqs[i.val].block)) (C.p₀.label F.cell) = _
    rw [min_eq_left ((C.rep_le_cap _ hr).trans F.dominates), C.rep_label _ hr]
  rcases C.p₀.scheme.rows_coded F.cell (F.reference hblocks i) with hb | ⟨b, j, _, hs⟩
  · rw [hb, hτ.bot] at hrep
    exact False.elim ((ofOrd_ne_bot _ ) hrep.symm)
  · have hout := finitePart_limitPart_add_nat reqs[i.val].block (C.repOff reqs[i.val].block)
    rw [hblocks _ hr] at hout
    have hfp := finitePart_eq_of_nonvisible_image
      (fun x k hk => hτ.clause5 x C.N (by rw [gTop_of_le le_rfl]; exact le_top) k hk)
      (hs ▸ hrep) (by simpa only [hout] using C.rep_off_lt _ hr)
    rw [finitePart_mul_add, hout] at hfp
    exact ⟨b, by simpa only [hfp] using hs⟩

/-- New finite columns use existing blocks and exactly the requested finite parts. -/
theorem orbitSource_code (i : Fin reqs.length) :
    ∃ b : ℕ, F.orbitSource hblocks i = ofOrd (Ordinal.omega0 * b + reqs[i.val].offset) := by
  obtain ⟨b, hb⟩ := F.reference_source_code hblocks i
  refine ⟨b, ?_⟩
  rw [orbitSource, hb, extVisibilityReplace_of_finitePart_lt
    (by simpa only [finitePart_mul_add] using C.rep_off_lt _ (List.getElem_mem i.isLt))]
  rw [limitPart_mul_add]

/-- The completed row retains the original owner's coding convention. -/
theorem source_coded (d : F.Old ⊕ Fin reqs.length) : IsCodedLabel C.N (F.source hblocks d) := by
  cases d with
  | inl d => simpa only [source, Sum.elim_inl, F.grade_eq] using C.p₀.scheme.rows_coded F.cell d
  | inr i =>
    obtain ⟨b, hb⟩ := F.orbitSource_code hblocks i
    exact Or.inr ⟨b, reqs[i.val].offset, (C.offset_lt _ (List.getElem_mem i.isLt)).le.trans
      (Nat.le_succ _), hb⟩

/-- Source orderliness is checked at each requested cell's own grade, not the controller grade. -/
theorem source_orderly (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ reqs[i.val].offset) :
    IsOrderly (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade)
      (F.source hblocks) := by
  intro d
  cases d with
  | inl d => exact C.p₀.scheme.rows.orderly F.cell d
  | inr i =>
    obtain ⟨b, hb⟩ := F.orbitSource_code hblocks i
    change F.orbitSource hblocks i = extVisibilityReplace (F.orbitSource hblocks i)
      (newGrade i) (newGrade i)
    rw [hb]
    exact (selfVis_ofOrd_iff.mpr (by simpa only [finitePart_mul_add] using hgrade i)).symm

/-- Re-evaluate the fixed orbit columns from an arbitrary old capped reading. -/
noncomputable def retunedTarget (p : F.Old → ExtOrd) : F.Old ⊕ Fin reqs.length → ExtOrd :=
  Sum.elim (fun d => min (p d) (p F.owner))
    (fun i => extVisibilityReplace (min (p (F.reference hblocks i)) (p F.owner))
      C.N reqs[i.val].offset)

theorem retunedTarget_owner (p : F.Old → ExtOrd) :
    F.retunedTarget hblocks p (Sum.inl F.owner) = p F.owner := min_self _

/-- Replacement does not exceed a controller-visible cap. -/
theorem retunedTarget_le (p : F.Old → ExtOrd) (hvis : SelfVis C.N (p F.owner))
    (d : F.Old ⊕ Fin reqs.length) : F.retunedTarget hblocks p d ≤ p F.owner := by
  cases d with
  | inl d => exact min_le_right _ _
  | inr i =>
    exact extVisibilityReplace_le_of_le_selfVis
      (C.offset_lt _ (List.getElem_mem i.isLt)).le hvis (min_le_right _ _)

/-- Every faithful old capped reading extends by this formula, including bottom and top.
This is relative retuning of one row, not a theorem about all controllers in a scheme. -/
theorem retunedTarget_transformsTo (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ C.N) (p : F.Old → ExtOrd)
    (hvis : SelfVis C.N (p F.owner))
    (hloc : TransformsTo (fun d : F.Old => C.p₀.scheme.scheme.grade d.1)
      (C.p₀.scheme.rows.E F.cell) (fun d => min (p d) (p F.owner))) :
    TransformsTo (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade)
      (F.source hblocks) (F.retunedTarget hblocks p) := by
  obtain ⟨τ, hτ, _, hread⟩ := exists_bounded_exact_capped_witness
    (c := F.owner) (fun d => d.2.2) (by
      change SelfVis (C.p₀.scheme.scheme.grade F.cell) (p F.owner)
      exact F.grade_eq.symm ▸ hvis) hloc
  change Witness (gTop (C.p₀.scheme.scheme.grade F.cell)) τ at hτ
  rw [F.grade_eq] at hτ
  apply hτ.transformsTo
  intro d
  cases d with
  | inl d =>
    change min (p d) (p F.owner) =
      min (τ (C.p₀.scheme.rows.E F.cell d)) (gTop C.N (C.p₀.scheme.scheme.grade d.1))
    rw [gTop_of_le (F.grade_le d), min_top_right, hread]
  | inr i =>
    change extVisibilityReplace (min (p (F.reference hblocks i)) (p F.owner))
      C.N reqs[i.val].offset = min
        (τ (extVisibilityReplace (C.p₀.scheme.rows.E F.cell (F.reference hblocks i))
          C.N reqs[i.val].offset)) (gTop C.N (newGrade i))
    rw [gTop_of_le (hgrade i), min_top_right,
      hτ.clause5 _ C.N (by rw [gTop_of_le le_rfl]; exact le_top)
        _ (C.offset_lt _ (List.getElem_mem i.isLt)).le, hread]

/-- The re-evaluation formula preserves every capped output at an `N`-visible cap,
provided all old capped values (the controller's included) are preserved. -/
theorem retunedTarget_agrees {p q : F.Old → ExtOrd} {γ : ExtOrd}
    (hγ : SelfVis C.N γ) (hpq : ∀ d, min (p d) γ = min (q d) γ)
    (d : F.Old ⊕ Fin reqs.length) :
    min (F.retunedTarget hblocks p d) γ = min (F.retunedTarget hblocks q d) γ := by
  have hcap (e : F.Old) : min (min (p e) (p F.owner)) γ =
      min (min (q e) (q F.owner)) γ := by
    calc
      min (min (p e) (p F.owner)) γ = min (min (p e) γ) (min (p F.owner) γ) := by
        rw [min_min_min_comm, min_self]
      _ = min (min (q e) γ) (min (q F.owner) γ) := by rw [hpq, hpq]
      _ = min (min (q e) (q F.owner)) γ := by rw [min_min_min_comm, min_self]
  cases d with
  | inl d => exact hcap d
  | inr i =>
    have hm : Monotone (fun x => extVisibilityReplace x C.N reqs[i.val].offset) :=
      fun _ _ h => evr_mono h (C.offset_lt _ (List.getElem_mem i.isLt)).le
    have hclip (x : ExtOrd) : min (extVisibilityReplace x C.N reqs[i.val].offset) γ =
        extVisibilityReplace (min x γ) C.N reqs[i.val].offset := by
      rw [hm.map_min, evr_eq_self_of_selfVis hγ]
    change min (extVisibilityReplace _ _ _) γ = min (extVisibilityReplace _ _ _) γ
    rw [hclip, hclip, hcap]

/-- On the model-produced reference labels, the retuning formula is the intended target. -/
theorem retunedTarget_original :
    F.retunedTarget hblocks (fun d => C.p₀.label d.1) = F.target := by
  funext d
  cases d with
  | inl d => rfl
  | inr i =>
    have hr := List.getElem_mem i.isLt
    change extVisibilityReplace
      (min (C.p₀.label (C.repBase reqs[i.val].block)) (C.p₀.label F.cell))
      C.N reqs[i.val].offset = ofOrd reqs[i.val].value
    rw [min_eq_left ((C.rep_le_cap _ hr).trans F.dominates), C.rep_label _ hr]
    exact extVisibilityReplace_rep (hblocks _ hr) (C.rep_off_lt _ hr)

/-- The old part of the constructed source row respects the old semantics, including
availability: it is literally a row of the consistent reference scheme. -/
theorem source_old_respects :
    RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell F.cell)
      (fun d => F.source hblocks (Sum.inl d)) := C.p₀.scheme.consistent F.cell

/-- Capping the actual old labelling preserves its old incidences and availability. -/
theorem target_old_respects :
    RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell F.cell)
      (fun d => F.target (Sum.inl d)) := by
  have hold : RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell F.cell)
      (fun d => C.p₀.label d.1) := by
    refine ⟨fun d => C.p₀.respects.orderly d.1, fun d => C.p₀.respects.locality d.1, ?_⟩
    intro d e hs hg
    obtain ⟨a, ha, hle⟩ := C.p₀.respects.availability d.1 e.1 hs hg
    exact ⟨⟨a, by rw [ha]; exact e.2⟩, ha, hle⟩
  exact hold.cap (C.p₀.respects.orderly F.cell).symm

include hblocks in
/-- The intended target is orderly at the actual individual grades when each requested
offset permits that grade. No grade-`N` visibility of a lower-grade request is assumed. -/
theorem target_orderly (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ reqs[i.val].offset) :
    IsOrderly (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade) F.target := by
  intro d
  cases d with
  | inl d => exact F.target_old_respects.orderly d
  | inr i =>
    change ofOrd reqs[i.val].value =
      extVisibilityReplace (ofOrd reqs[i.val].value) (newGrade i) (newGrade i)
    apply (selfVis_ofOrd_iff.mpr ?_).symm
    have hfp := finitePart_limitPart_add_nat reqs[i.val].block reqs[i.val].offset
    rw [hblocks _ (List.getElem_mem i.isLt)] at hfp
    exact (hgrade i).trans_eq hfp.symm

/-- Every later faithful capped response to the fixed row obeys the orbit equation.
The response and its shifter may change; the source row does not. -/
theorem capped_orbit (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ C.N) (q : F.Old ⊕ Fin reqs.length → ExtOrd)
    (hvis : SelfVis C.N (q (Sum.inl F.owner)))
    (hloc : TransformsTo
      (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade)
      (F.source hblocks) (fun d => min (q d) (q (Sum.inl F.owner))))
    (i : Fin reqs.length) :
    min (q (Sum.inr i)) (q (Sum.inl F.owner)) =
      extVisibilityReplace (min (q (Sum.inl (F.reference hblocks i)))
        (q (Sum.inl F.owner))) C.N reqs[i.val].offset := by
  let gr := Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade
  have hc : gr (Sum.inl F.owner) = C.N := F.grade_eq
  have hmax : ∀ d, gr d ≤ gr (Sum.inl F.owner) := by
    intro d
    rw [hc]
    cases d with
    | inl d => exact F.grade_le d
    | inr j => exact hgrade j
  obtain ⟨τ, hτ, _, hread⟩ := exists_bounded_exact_capped_witness
    hmax (by rwa [hc]) hloc
  rw [hc] at hτ
  have hnew := hread (Sum.inr i)
  have href := hread (Sum.inl (F.reference hblocks i))
  change τ (extVisibilityReplace (C.p₀.scheme.rows.E F.cell (F.reference hblocks i))
    C.N reqs[i.val].offset) = _ at hnew
  rw [hτ.clause5 _ C.N (by rw [gTop_of_le le_rfl]; exact le_top)
    _ (C.offset_lt _ (List.getElem_mem i.isLt)).le] at hnew
  change τ (C.p₀.scheme.rows.E F.cell (F.reference hblocks i)) = _ at href
  rw [href] at hnew
  exact hnew.symm

/-- Literal reference readback and domination of the old cap force every finite request.
This is a universal response statement, not just verification of the intended target. -/
theorem forced_readback (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ C.N) (q : F.Old ⊕ Fin reqs.length → ExtOrd)
    (hvis : SelfVis C.N (q (Sum.inl F.owner)))
    (hloc : TransformsTo
      (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade)
      (F.source hblocks) (fun d => min (q d) (q (Sum.inl F.owner))))
    (hcap : C.p₀.label C.capBase ≤ q (Sum.inl F.owner))
    (href : ∀ i, q (Sum.inl (F.reference hblocks i)) =
      C.p₀.label (C.repBase reqs[i.val].block)) (i : Fin reqs.length) :
    q (Sum.inr i) = ofOrd reqs[i.val].value := by
  have hr := List.getElem_mem i.isLt
  have heq := F.capped_orbit hblocks newGrade hgrade q hvis hloc i
  rw [href, min_eq_left ((C.rep_le_cap _ hr).trans hcap), C.rep_label _ hr,
    extVisibilityReplace_rep (hblocks _ hr) (C.rep_off_lt _ hr)] at heq
  have hlt := (C.cap_dom _ hr).trans_le hcap
  rcases le_total (q (Sum.inr i)) (q (Sum.inl F.owner)) with h | h
  · rwa [min_eq_left h] at heq
  · rw [min_eq_right h] at heq
    exact False.elim ((lt_irrefl _) (heq ▸ hlt))

/-- A wrong finite response is impossible for this fixed completed row under the actual
reference and cap conditions. No bounded search or chosen witness template is involved. -/
theorem wrong_response_not_faithful (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ C.N) (q : F.Old ⊕ Fin reqs.length → ExtOrd)
    (hvis : SelfVis C.N (q (Sum.inl F.owner)))
    (hcap : C.p₀.label C.capBase ≤ q (Sum.inl F.owner))
    (href : ∀ i, q (Sum.inl (F.reference hblocks i)) =
      C.p₀.label (C.repBase reqs[i.val].block))
    (i : Fin reqs.length) (hwrong : q (Sum.inr i) ≠ ofOrd reqs[i.val].value) :
    ¬ TransformsTo
      (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade)
      (F.source hblocks) (fun d => min (q d) (q (Sum.inl F.owner))) := by
  intro hloc
  exact hwrong (F.forced_readback hblocks newGrade hgrade q hvis hloc hcap href i)

/-- Add an actual fresh owner occurrence after fixing the entire source inventory.
The same source-only cutoff works for every faithful old capped reading and every larger
visible new-owner value. Its diagonal dominates every old and requested source. Scope and
the other owners' rows are deliberately not asserted. -/
theorem exists_fixed_owned_row (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ reqs[i.val].offset) :
    ∃ b : ℕ, 0 < b ∧
      (∀ d, F.source hblocks d < FreeDiagonal.source C.N b) ∧
      (∀ d, IsCodedLabel C.N (FreeDiagonal.append (F.source hblocks)
        (FreeDiagonal.source C.N b) d)) ∧
      (∀ d, SelfVis
        (FreeDiagonal.append
          (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade) C.N d)
        (FreeDiagonal.append (F.source hblocks) (FreeDiagonal.source C.N b) d)) ∧
      ∀ (p : F.Old → ExtOrd), SelfVis C.N (p F.owner) →
        TransformsTo (fun d : F.Old => C.p₀.scheme.scheme.grade d.1)
          (C.p₀.scheme.rows.E F.cell) (fun d => min (p d) (p F.owner)) →
        ∀ U, SelfVis C.N U → p F.owner ≤ U →
          TransformsTo
            (FreeDiagonal.append
              (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade) C.N)
            (FreeDiagonal.append (F.source hblocks) (FreeDiagonal.source C.N b))
            (FreeDiagonal.append (F.retunedTarget hblocks p) U) := by
  let gr := Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade
  have hc : gr (Sum.inl F.owner) = C.N := F.grade_eq
  have hn (i : Fin reqs.length) : newGrade i ≤ C.N :=
    (hgrade i).trans (C.offset_lt _ (List.getElem_mem i.isLt)).le
  have hmax : ∀ d, gr d ≤ gr (Sum.inl F.owner) := by
    intro d
    rw [hc]
    cases d with
    | inl d => exact F.grade_le d
    | inr i => exact hn i
  obtain ⟨b, hb, hcut, hcode, ho, hserve⟩ := FreeDiagonal.exists_fixed_extension
    gr (F.source hblocks) (Sum.inl F.owner) hmax
    (fun d => hc.symm ▸ F.source_coded hblocks d)
    (fun d => (F.source_orderly hblocks newGrade hgrade d).symm)
  rw [hc] at hcode ho hserve
  refine ⟨b, hb, fun d => (hcut d).trans_le (FreeDiagonal.limit_le_source _ _),
    hcode, ho, ?_⟩
  intro p hp hloc U hU hle
  have hq := F.retunedTarget_transformsTo hblocks newGrade hn p hp hloc
  have heq : (fun d => min (F.retunedTarget hblocks p d)
      (F.retunedTarget hblocks p (Sum.inl F.owner))) = F.retunedTarget hblocks p := by
    funext d
    rw [F.retunedTarget_owner, min_eq_left (F.retunedTarget_le hblocks p hp d)]
  have hq' : TransformsTo gr (F.source hblocks)
      (fun d => min (F.retunedTarget hblocks p d)
        (F.retunedTarget hblocks p (Sum.inl F.owner))) := heq.symm ▸ hq
  have result := hserve (F.retunedTarget hblocks p)
    (by rwa [F.retunedTarget_owner]) hq' U hU (by rwa [F.retunedTarget_owner])
  rwa [heq] at result

/-- Readback at the genuinely fresh owner, whose label need not equal the old controller's.
The only cap requirement is domination of the reference cap, as supplied by availability
in a future installation. This theorem does not assume that availability itself. -/
theorem owned_forced_readback (b : ℕ) (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ C.N)
    (q : Option (F.Old ⊕ Fin reqs.length) → ExtOrd)
    (hvis : SelfVis C.N (q none))
    (hloc : TransformsTo
      (FreeDiagonal.append
        (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade) C.N)
      (FreeDiagonal.append (F.source hblocks) (FreeDiagonal.source C.N b))
      (fun d => min (q d) (q none)))
    (hcap : C.p₀.label C.capBase ≤ q none)
    (href : ∀ i, q (some (Sum.inl (F.reference hblocks i))) =
      C.p₀.label (C.repBase reqs[i.val].block)) (i : Fin reqs.length) :
    q (some (Sum.inr i)) = ofOrd reqs[i.val].value := by
  let gr := FreeDiagonal.append
    (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade) C.N
  have hmax : ∀ d, gr d ≤ gr none := by
    rintro (_ | d)
    · exact le_rfl
    · cases d with
      | inl d => exact F.grade_le d
      | inr j => exact hgrade j
  obtain ⟨τ, hτ, _, hread⟩ := exists_bounded_exact_capped_witness hmax hvis hloc
  have hr := List.getElem_mem i.isLt
  have hrep := hread (some (Sum.inl (F.reference hblocks i)))
  change τ (C.p₀.scheme.rows.E F.cell (F.reference hblocks i)) = _ at hrep
  rw [href, min_eq_left ((C.rep_le_cap _ hr).trans hcap), C.rep_label _ hr] at hrep
  have hnew := hread (some (Sum.inr i))
  change Witness (gTop C.N) τ at hτ
  change τ (extVisibilityReplace (C.p₀.scheme.rows.E F.cell (F.reference hblocks i))
    C.N reqs[i.val].offset) = _ at hnew
  rw [hτ.clause5 _ C.N (by rw [gTop_of_le le_rfl]; exact le_top)
    _ (C.offset_lt _ hr).le, hrep,
    extVisibilityReplace_rep (hblocks _ hr) (C.rep_off_lt _ hr)] at hnew
  have hlt := (C.cap_dom _ hr).trans_le hcap
  rcases le_total (q (some (Sum.inr i))) (q none) with h | h
  · rw [min_eq_left h] at hnew
    exact hnew.symm
  · rw [min_eq_right h] at hnew
    exact False.elim ((lt_irrefl _) (hnew.symm ▸ hlt))

end FullController
end ReferenceContext

end VaughtConjecture.Knight
