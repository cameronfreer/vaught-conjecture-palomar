/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingCatalogueSources

/-! # Rank-row incidences with retained private owners

Rank compression preserves the source-block bottom condition at grade one.
Consequently the admitted private section supplies faithful locality for the
long lower ladder rows against original owners, not just upper-row locality.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingCatalogueIncidences
open Transform Value ExtOrd CappedDonor CappedDonor.Ref ReceivingLadderCarrier
open ReceivingCatalogueSources LadderScalarRendering
noncomputable section

/-- Visible postprocessing needs bottom reflection only on the actual target
table. This is a constructed faithful witness, not transformation transitivity. -/
theorem postprocess {Y : Type*} [Finite Y] {E t : Y → ExtOrd}
    (h : TransformsTo (fun _ : Y => 1) E t) (hE : ∀ d, SelfVis 1 (E d))
    {f : ExtOrd → ExtOrd} (hm : Monotone f) (h0 : f ⊥ = ⊥)
    (hv : ∀ d, SelfVis 1 (f (t d))) (hb : ∀ d, f (t d) = ⊥ ↔ t d = ⊥) :
    TransformsTo (fun _ : Y => 1) E (fun d => f (t d)) := by
  apply LongGuardRows.transforms_of_visible_table hE hv
  · intro d e he
    obtain ⟨g, σ, _, _, _, hσ, _, hr⟩ := h
    apply hm
    rw [hr d, hr e]
    exact min_le_min (hσ he) le_rfl
  · intro d hd
    obtain ⟨g, σ, _, _, hσ, _, _, hr⟩ := h
    rw [hr d, hd, hσ, min_bot_left, h0]
  · intro d e he hd
    exact (hb e).mpr (LongGuardRows.bottom_of_same_block h he ((hb d).mp hd))

variable {I : Type*} [Fintype I] {nP K : ℕ} {P : SemScheme (nP + 1)}
  {C : SemScheme 2} {R : Ref I nP 2 2 P C} (L : R.LowRef K)

theorem rank_zero_iff (a : Controller L) (f : TField P C) :
    ranks L a f = 0 ↔ fields L a f = ⊥ := by
  constructor
  · intro hz
    by_contra hn
    have hp := rank_pos (mem_values.mpr ⟨hn, f, rfl⟩)
    change 0 < ranks L a f at hp
    omega
  · intro hz
    change rank (values (fields L a)) (fields L a f) = 0
    rw [hz]
    exact rank_bot (bot_not_values (fields L a))

/-- All original grade-one rows, including long rows, admit the lower
rank-coded source restriction of every catalogue controller. -/
theorem private_rank_locality (a : Controller L) (t : ℕ) (c : Cell C.scheme)
    (hc : C.scheme.grade c = 1) :
    TransformsTo (fun d : C.scheme.below (C.scheme.cell c) => C.scheme.grade d.1)
      (C.rows.E c)
      (fun d => min (SupportLadderRows.source t (ranks L a (privateField d.1)))
        (SupportLadderRows.source t (ranks L a (privateField c)))) := by
  have hg (d : C.scheme.below (C.scheme.cell c)) : C.scheme.grade d.1 = 1 :=
    le_antisymm (d.2.2.trans_eq hc) (C.scheme.grade_pos d.1)
  have hgrade : (fun d : C.scheme.below (C.scheme.cell c) => C.scheme.grade d.1) =
      (fun _ => 1) := funext hg
  rw [hgrade]
  by_cases ht : t = 0
  · subst t
    have hz (i : ℕ) : SupportLadderRows.source 0 i = ⊥ :=
      (SupportLadderRows.source_bot_iff _ _).mpr (Nat.min_zero i)
    simp only [hz, min_self]
    exact TransformsTo.to_bot _
  let f : ExtOrd → ExtOrd := fun x => SupportLadderRows.source t (rank (values (fields L a)) x)
  have hm : Monotone f := (SupportLadderRows.source_mono t).comp (rank_mono _)
  have h0 : f ⊥ = ⊥ := by simp only [f, rank_bot (bot_not_values _), SupportLadderRows.source_zero]
  have hz (d : TField P C) : f (fields L a d) = ⊥ ↔ fields L a d = ⊥ := by
    change SupportLadderRows.source t (ranks L a d) = ⊥ ↔ _
    rw [SupportLadderRows.source_bot_iff, Nat.min_eq_zero_iff, or_iff_left ht]
    exact rank_zero_iff L a d
  have hp := (private_lawful L a).locality c
  rw [hgrade] at hp
  have he (d : C.scheme.below (C.scheme.cell c)) :
      f (min (fields L a (privateField d.1)) (fields L a (privateField c))) =
        min (SupportLadderRows.source t (ranks L a (privateField d.1)))
          (SupportLadderRows.source t (ranks L a (privateField c))) := hm.map_min
  have hout := postprocess hp
    (fun d => by simpa only [hg d] using (C.rows.orderly c d).symm) hm h0
    (fun _ => SupportLadderRows.source_visible _ _)
    (fun d => by rw [hm.map_min, min_eq_bot, hz, hz, min_eq_bot])
  simpa only [he] using hout

variable (hC : C.scheme.plan = privatePlan) (request : Cell P.scheme)

/-- The rank-coded locality transported to the literal physical lower domain
of an inherited owner. Both mixed copies use this same incidence. -/
theorem ladder_private_incidence
    (v : SupportLadderRows.Point (rungs (P := P) (C := C)) (TField P C) (Controller L))
    (c : Cell C.scheme) (hc : C.scheme.grade c = 1) :
    TransformsTo
      (fun d : (carrier L hC).below ((carrier L hC).cell (old C.scheme hC c)) =>
        (carrier L hC).grade d.1)
      ((semantics L hC request).E (old C.scheme hC c))
      (fun d => min
        (ladderRow (U := Controller L) C.scheme hC privateField (.field (.req request))
          (ranks L) v d.1)
        (ladderRow (U := Controller L) C.scheme hC privateField (.field (.req request))
          (ranks L) v (old C.scheme hC c))) := by
  have ht := (private_rank_locality L (SupportLadderRows.parent v)
    (SupportLadderRows.ceiling (ranks L) v) c hc).reindex
      (oldArg (L := rungs (P := P) (C := C)) (X := TField P C)
        (Q := Controller L) (U := Controller L) C.scheme hC c)
  have hg : (fun d : (carrier L hC).below ((carrier L hC).cell (old C.scheme hC c)) =>
      C.scheme.grade (oldArg C.scheme hC c d).1) = (fun d => (carrier L hC).grade d.1) :=
    funext (oldArg_grade C.scheme hC c)
  simp only [Function.comp_def] at ht
  rw [hg] at ht
  convert ht using 1
  · funext d
    exact ReceivingLadderSemantics.inherited C.scheme hC privateField (.field (.req request))
      (high (R := R)) (ranks L) (fields L) id (grid (P := P) (C := C))
      (ReceivingCatalogueSources.ceiling (P := P) (C := C)) C.rows grid_bot
      (fun _ => grid_visible) ceiling_visible (fields_visible L)
      (fun a e => private_visible L a e (gradeC_le e)) (high_visible L) c d
  · funext d
    obtain ⟨e, rfl⟩ := below_old C.scheme hC c d
    rw [ReceivingLadderCarrier.oldArg_oldBelow]
    simp only [ReceivingLadderCarrier.oldBelow, ladderRow_old]

/-- A positive monotone rank table gives faithful locality on the entire
physical grade-one lower domain, including original cells and both copies. -/
theorem lowerImage_locality (a : Controller L) (f : ℕ → ExtOrd)
    (hf : Monotone f) (h0 : f 0 = ⊥) (hv : ∀ i, SelfVis 1 (f i))
    (hp : ∀ i, 0 < i → i ≤ rungs (P := P) (C := C) → f i ≠ ⊥)
    (b : Bool)
    (v : SupportLadderRows.Point (rungs (P := P) (C := C)) (TField P C) (Controller L)) :
    TransformsTo
      (fun d : (carrier L hC).below ((carrier L hC).cell (added C.scheme hC (.ladder b v))) =>
        (carrier L hC).grade d.1)
      ((semantics L hC request).E (added C.scheme hC (.ladder b v)))
      (fun d => min
        (lowerImage C.scheme hC privateField (.field (.req request)) (ranks L) a f d.1)
        (f (SupportLadderRows.index (ranks L) a v))) := by
  let e := SupportLadderRows.index (ranks L) a v
  have hec : e ≤ SupportLadderRows.ceiling (ranks L) v := min_le_right _ _
  have hel : e ≤ rungs (P := P) (C := C) := SupportLadderRows.index_le a v
  have he (d : Cell (carrier L hC)) :
      min (lowerImage C.scheme hC privateField (.field (.req request)) (ranks L) a f d)
        (f e) = f (min (lowerIndex C.scheme hC privateField (.field (.req request))
          (ranks L) (SupportLadderRows.parent v) d) e) := by
    change min (f _) (f e) = _
    rw [← hf.map_min]
    apply congrArg f
    have hag := lowerIndex_agreement C.scheme hC privateField (.field (.req request))
      (ranks L) a (SupportLadderRows.parent v) d
    dsimp only [e, SupportLadderRows.index]
    grind
  have hgrade : (fun d : (carrier L hC).below
      ((carrier L hC).cell (added C.scheme hC (.ladder b v))) => (carrier L hC).grade d.1) =
      (fun _ => 1) := funext (below_ladder_grade C.scheme hC b v)
  rw [hgrade]
  have htarget : (fun d : (carrier L hC).below
      ((carrier L hC).cell (added C.scheme hC (.ladder b v))) =>
      min (lowerImage C.scheme hC privateField (.field (.req request)) (ranks L) a f d.1)
        (f (SupportLadderRows.index (ranks L) a v))) =
      (fun d => f (min (lowerIndex C.scheme hC privateField (.field (.req request))
        (ranks L) (SupportLadderRows.parent v) d.1) e)) := funext (fun d => he d.1)
  rw [htarget]
  simp only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
    view_added]
  by_cases hz : e = 0
  · simp only [hz, Nat.min_zero, h0]
    exact TransformsTo.to_bot _
  · have ht := SupportLadderRows.transforms_positive
      (fun d : (carrier L hC).below
        ((carrier L hC).cell (added C.scheme hC (.ladder b v))) =>
        lowerIndex C.scheme hC privateField (.field (.req request)) (ranks L)
          (SupportLadderRows.parent v) d.1)
      (SupportLadderRows.ceiling (ranks L) v) (fun i => f (min i e))
      (fun _ _ h => hf (min_le_min_right _ h)) (by simpa using h0) (fun _ => hv _)
      (fun i hi _ => hp _ (by omega) ((min_le_right _ _).trans hel))
    simpa only [ladderRow, min_assoc, min_eq_right hec] using ht

local notation "H" => ReceivingCatalogueSources.ceiling (P := P) (C := C)
local notation "G" => grid (P := P) (C := C)
local notation "D" => carrier L hC
local notation "T" => SupportLadderRows.Point (rungs (P := P) (C := C))
  (TField P C) (Controller L)

/-- The rendered upper source and rank table coincide on every actual
grade-one occurrence, not merely on the abstract ladder table. -/
theorem source_lower (a : Controller L) (d : Cell D) (hd : (D).grade d = 1) :
    source L hC request a d =
      lowerImage C.scheme hC privateField (.field (.req request)) (ranks L) a
        (LadderScalarRendering.level (values (fields L a)) H) d := by
  rcases ReceivingLadderCarrier.cell_cases C.scheme hC d with ⟨c, rfl⟩ | ⟨z, rfl⟩
  · simp only [source, ReceivingLadderSources.source_old, lowerImage, lowerIndex, view_old]
    exact (field_readback _ _ _).symm
  · cases z with
    | request =>
        simp only [source, ReceivingLadderSources.source_request, lowerImage, lowerIndex,
          view_added]
        exact (field_readback _ _ _).symm
    | ladder b v =>
        simp only [source, ReceivingLadderSources.source_ladder, lowerImage, lowerIndex,
          view_added, render, SupportLadderRows.image, id_eq]
    | upper b c node =>
        change (scheme C.scheme hC).grade (added C.scheme hC (.upper b c node)) = 1 at hd
        rw [ReceivingLadderCarrier.upper_grade] at hd
        exact (by decide : (2 : ℕ) ≠ 1) hd |>.elim
    | apex =>
        have hg : (D).grade (added C.scheme hC .apex) = 3 :=
          congrArg Prod.snd (added_index C.scheme hC .apex)
        omega

/-- Every weighted upper source has a faithful incidence with every lower
ladder owner on its complete actual lower domain. -/
theorem upper_ladder_incidence (a : Controller L) (node b : Bool) (v : T) :
    TransformsTo
      (fun d : (D).below ((D).cell (added C.scheme hC (.ladder b v))) => (D).grade d.1)
      ((semantics L hC request).E (added C.scheme hC (.ladder b v)))
      (fun d => min
        (ReceivingLadderUpperRows.row C.scheme hC privateField (.field (.req request))
          (high (R := R)) (ranks L) (fields L) id G H a node d.1)
        (ReceivingLadderUpperRows.row (L := rungs (P := P) (C := C))
          C.scheme hC privateField (.field (.req request))
          (high (R := R)) (ranks L) (fields L) id G H a node
            (added C.scheme hC (.ladder b v)))) := by
  have hb := values_bound (fields_bound L a)
  have ht := lowerImage_locality L hC request a
    (LadderScalarRendering.level (values (fields L a)) H)
    (level_mono hb) (level_zero _ _) (level_visible (fields_visible L a)
      (ceiling_visible.mono (by omega : 1 ≤ 2)))
    (fun _ hi _ => level_pos (bot_not_values _) hb (ofOrd_ne_bot _) hi) b v
  have hw := ReceivingLadderUpperRows.weight_visible (high (R := R)) (fields L) H
    (high_visible L) ceiling_visible a node
  have hcap := ht.cap (K := 2)
    (fun d => (below_ladder_grade C.scheme hC b v d).le.trans (by omega : 1 ≤ 2)) hw
  convert hcap using 1
  funext d
  have he := source_lower L hC request a d.1 (below_ladder_grade C.scheme hC b v d)
  have hv : source L hC request a (added C.scheme hC (.ladder b v)) =
      LadderScalarRendering.level (values (fields L a)) H
        (SupportLadderRows.index (ranks L) a v) := by
    simp only [source, ReceivingLadderSources.source_ladder, render, SupportLadderRows.image,
      id_eq]
  change min (min (source L hC request a d.1) _)
    (min (source L hC request a (added C.scheme hC (.ladder b v))) _) = _
  rw [he, hv]
  grind

/-- Incidences between lower ladder rows also hold on original occurrences,
not just between their auxiliary columns. -/
theorem ladder_ladder_incidence (w v : T) (b : Bool) :
    TransformsTo
      (fun d : (D).below ((D).cell (added C.scheme hC (.ladder b v))) => (D).grade d.1)
      ((semantics L hC request).E (added C.scheme hC (.ladder b v)))
      (fun d => min
        (ladderRow (U := Controller L) C.scheme hC privateField (.field (.req request))
          (ranks L) w d.1)
        (ladderRow (U := Controller L) C.scheme hC privateField (.field (.req request))
          (ranks L) w (added C.scheme hC (.ladder b v)))) := by
  by_cases hz : SupportLadderRows.ceiling (ranks L) w = 0
  · have he (d : Cell D) : ladderRow C.scheme hC privateField (.field (.req request))
        (ranks L) w d = ⊥ := by
      apply (SupportLadderRows.source_bot_iff _ _).mpr
      simp only [hz, Nat.min_zero]
    simp only [he, min_self]
    exact TransformsTo.to_bot _
  · have ht := lowerImage_locality L hC request (SupportLadderRows.parent w)
      (SupportLadderRows.source (SupportLadderRows.ceiling (ranks L) w))
      (SupportLadderRows.source_mono _) (SupportLadderRows.source_zero _)
      (SupportLadderRows.source_visible _)
      (fun i hi _ hb => by have := (SupportLadderRows.source_bot_iff _ _).mp hb; omega) b v
    simpa only [lowerImage, ladderRow, lowerIndex, view_added] using ht

/-- The catalogue-derived grid and rank hypotheses also discharge every
incidence between weighted upper owners on the actual physical domains. -/
theorem upper_upper_incidence (a c : Controller L) (node full other : Bool) :
    TransformsTo
      (fun d : (D).below ((D).cell (added C.scheme hC (.upper full c other))) =>
        (D).grade d.1)
      ((semantics L hC request).E (added C.scheme hC (.upper full c other)))
      (fun d => min
        (ReceivingLadderUpperRows.row C.scheme hC privateField (.field (.req request))
          (high (R := R)) (ranks L) (fields L) id G H a node d.1)
        (ReceivingLadderUpperRows.row (L := rungs (P := P) (C := C))
          C.scheme hC privateField (.field (.req request))
          (high (R := R)) (ranks L) (fields L) id G H a node
            (added C.scheme hC (.upper full c other)))) := by
  simpa only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
    view_added] using
    ReceivingLadderUpperRows.upper_locality (L := rungs (P := P) (C := C))
      C.scheme hC privateField (.field (.req request))
      (high (R := R)) (ranks L) (fields L) id G H grid_bot (fun _ => grid_visible)
      ceiling_visible (high_visible L) le_rfl (fun _ _ => rfl) (fields_bound L)
      (fun _ => grid_bound) a c node full other

end
end VaughtConjecture.Knight.ReceivingCatalogueIncidences
