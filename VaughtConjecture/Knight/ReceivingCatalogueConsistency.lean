/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingCatalogueAvailability

/-! # Consistency of the catalogue-derived fixed receiving carrier

The rows are unchanged. This closes the incidence and availability ledger;
bountifulness, and hence packaging a legal scheme, remain separate.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingCatalogueConsistency
open Transform Value ExtOrd CappedDonor CappedDonor.Ref ReceivingLadderCarrier
open ReceivingCatalogueSources ReceivingCatalogueIncidences ReceivingCatalogueAvailability
noncomputable section

variable {I : Type*} [Fintype I] {nP K : ℕ} {P : SemScheme (nP + 1)}
  {C : SemScheme 2} {R : Ref I nP 2 2 P C} (L : R.LowRef K)
  (hC : C.scheme.plan = privatePlan) (request : Cell P.scheme)

local notation "D" => carrier L hC
local notation "E" => semantics L hC request
local notation "T" => SupportLadderRows.Point (rungs (P := P) (C := C))
  (TField P C) (Controller L)

@[simp] theorem row_old (a : Cell C.scheme)
    (d : (D).below ((D).cell (old C.scheme hC a))) :
    (E).E (old C.scheme hC a) d = C.rows.E a (oldArg C.scheme hC a d) :=
  ReceivingLadderSemantics.inherited _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem row_request
    (d : (D).below ((D).cell (added C.scheme hC .request))) :
    (E).E (added C.scheme hC .request) d = SupportLadderRows.source 1 1 := by
  simp only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
    view_added]

@[simp] theorem row_ladder (b : Bool) (v : T)
    (d : (D).below ((D).cell (added C.scheme hC (.ladder b v)))) :
    (E).E (added C.scheme hC (.ladder b v)) d =
      ladderRow C.scheme hC privateField (.field (.req request)) (ranks L) v d.1 := by
  simp only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
    view_added]

@[simp] theorem row_upper (b : Bool) (a : Controller L) (node : Bool)
    (d : (D).below ((D).cell (added C.scheme hC (.upper b a node)))) :
    (E).E (added C.scheme hC (.upper b a node)) d =
      upperRow L hC request a node d.1 := by
  simp only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
    view_added, upperRow]

@[simp] theorem row_apex (d : (D).below ((D).cell (added C.scheme hC .apex))) :
    (E).E (added C.scheme hC .apex) d = ⊥ := by
  simp only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
    view_added]

/-- The fresh singleton has exactly one actual occurrence in its lower domain. -/
theorem below_request (d : (D).below ((D).cell (added C.scheme hC .request))) :
    d.1 = added C.scheme hC .request := by
  rcases ReceivingLadderCarrier.cell_cases C.scheme hC d.1 with ⟨a, ha⟩ | ⟨z, hz⟩
  · have hs := d.2.1
    rw [ha, old_index, added_index] at hs
    have hempty : C.scheme.scope a = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro i hi
      have hi' := hs (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      have he : (Fin.castSuccEmb i : Fin 3) = 2 := Finset.mem_singleton.mp hi'
      have hv := congrArg Fin.val he
      have hil := i.isLt
      change i.val = 2 at hv
      omega
    have hpos := C.scheme.grade_pos a
    have hcard := C.scheme.grade_le_card_scope a
    rw [hempty, Finset.card_empty] at hcard
    omega
  · cases z with
    | request => exact hz
    | ladder b v =>
        have hs := d.2.1
        rw [hz, added_index, added_index] at hs
        have hh := hs (show (0 : Fin 3) ∈ scope b by cases b <;> decide)
        simp [ReceivingLadderCarrier.newIndex] at hh
    | upper b a node =>
        have hs := d.2.1
        rw [hz, added_index, added_index] at hs
        have hh := hs (show (0 : Fin 3) ∈ scope b by cases b <;> decide)
        simp [ReceivingLadderCarrier.newIndex] at hh
    | apex =>
        have hh := d.2.2
        rw [hz, added_index, added_index] at hh
        change 3 ≤ 1 at hh
        omega

/-- Every orderly reading at the singleton admits its faithful local witness. -/
theorem request_incidence (x : ExtOrd) (hx : SelfVis 1 x) :
    TransformsTo
      (fun d : (D).below ((D).cell (added C.scheme hC .request)) => (D).grade d.1)
      ((E).E (added C.scheme hC .request)) (fun _ => x) := by
  rw [show (E).E (added C.scheme hC .request) =
    (fun _ => SupportLadderRows.source 1 1) from funext (row_request L hC request)]
  apply transformsTo_const_const
  · intro d
    simpa only [CellScheme.grade, added_index, ReceivingLadderCarrier.newIndex] using d.2.2
  · intro h
    have hh := (SupportLadderRows.source_bot_iff 1 1).mp h
    omega
  · exact hx

theorem request_consistent : RespectsSemanticsBelow E
    ((D).cell (added C.scheme hC .request)) ((E).E (added C.scheme hC .request)) := by
  refine ⟨(E).orderly _, ?_, ?_⟩
  · intro s
    have hs := below_request L hC s
    rcases s with ⟨s, hs'⟩
    dsimp only at hs
    subst s
    simpa only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
      view_added, min_self] using request_incidence L hC request
      (SupportLadderRows.source 1 1) (SupportLadderRows.source_visible 1 1)
  · intro s t _ _
    exact ⟨t, rfl, by simp only [row_request, le_refl]⟩

theorem apex_consistent : RespectsSemanticsBelow E
    ((D).cell (added C.scheme hC .apex)) ((E).E (added C.scheme hC .apex)) := by
  refine ⟨(E).orderly _, ?_, ?_⟩
  · intro s
    simpa only [row_apex, min_self] using TransformsTo.to_bot ((E).E s.1)
  · intro s t _ _
    exact ⟨t, rfl, by simp only [row_apex, le_refl]⟩

/-- Inherited consistency uses the actual lower-domain bijection, including
all original occurrences at repeated indices and long inherited rows. -/
theorem old_consistent (c : Cell C.scheme) : RespectsSemanticsBelow E
    ((D).cell (old C.scheme hC c)) ((E).E (old C.scheme hC c)) := by
  let e : (D).below ((D).cell (old C.scheme hC c)) ≃ C.scheme.below (C.scheme.cell c) :=
    ⟨oldArg C.scheme hC c, ReceivingLadderCarrier.oldBelow C.scheme hC c,
      oldArg_spec C.scheme hC c, ReceivingLadderCarrier.oldArg_oldBelow C.scheme hC c⟩
  have hg : ∀ a, (D).grade a.1 = C.scheme.grade (e a).1 :=
    fun a => (oldArg_grade C.scheme hC c a).symm
  have hs : ∀ a b, (D).scope a.1 ⊆ (D).scope b.1 ↔
      C.scheme.scope (e a).1 ⊆ C.scheme.scope (e b).1 := by
    intro a b
    obtain ⟨a, rfl⟩ := below_old C.scheme hC c a
    obtain ⟨b, rfl⟩ := below_old C.scheme hC c b
    change (D).scope (old C.scheme hC a.1) ⊆ (D).scope (old C.scheme hC b.1) ↔
      C.scheme.scope (oldArg C.scheme hC c (ReceivingLadderCarrier.oldBelow C.scheme hC c a)).1 ⊆
      C.scheme.scope (oldArg C.scheme hC c (ReceivingLadderCarrier.oldBelow C.scheme hC c b)).1
    rw [ReceivingLadderCarrier.oldArg_oldBelow, ReceivingLadderCarrier.oldArg_oldBelow]
    simpa only [CellScheme.scope, old_index] using
      (Finset.image_subset_image_iff Fin.castSuccEmb.injective
        (s := C.scheme.scope a.1) (t := C.scheme.scope b.1))
  have hr : ∀ (s : (D).below ((D).cell (old C.scheme hC c)))
      (d : (D).below ((D).cell s.1))
      (hd : GradedLe (C.scheme.cell (e ⟨d.1, d.2.trans s.2⟩).1)
        (C.scheme.cell (e s).1)),
      (E).E s.1 d = C.rows.E (e s).1 ⟨(e ⟨d.1, d.2.trans s.2⟩).1, hd⟩ := by
    intro s d hd
    obtain ⟨s, rfl⟩ := below_old C.scheme hC c s
    obtain ⟨d, rfl⟩ := below_old C.scheme hC s.1 d
    have hes : e (ReceivingLadderCarrier.oldBelow C.scheme hC c s) = s := e.apply_symm_apply s
    have hed : (e ⟨old C.scheme hC d.1, d.2.trans s.2 |> fun h =>
        by rw [old_index, old_index]; exact ⟨Finset.image_subset_image h.1, h.2⟩⟩).1 = d.1 := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨d.1, d.2.trans s.2⟩)
    change (E).E (old C.scheme hC s.1) (ReceivingLadderCarrier.oldBelow C.scheme hC s.1 d) = _
    rw [row_old, ReceivingLadderCarrier.oldArg_oldBelow]
    revert hd
    rw [hes]
    intro hd
    apply congrArg (C.rows.E s.1)
    exact Subtype.ext hed.symm
  have hh := RespectsSemanticsBelow.of_equiv e hg hs hr (C.consistent c)
  simpa only [e, Equiv.coe_fn_mk, ← row_old L hC request c] using hh

/-- Exhaustive availability reduction below a grade-at-most-two owner. The
request is a singleton, original targets use original availability, and each
mixed target uses its own actual-index witness. -/
theorem availability_cases (c : Cell D) (hc : (D).grade c ≤ 2) (r : Cell D → ExtOrd)
    (hold : ∀ (d e : Cell C.scheme), C.scheme.scope d ⊆ C.scheme.scope e →
      C.scheme.grade d = C.scheme.grade e →
      GradedLe ((D).cell (old C.scheme hC e)) ((D).cell c) →
      ∃ w : (D).below ((D).cell c), (D).cell w.1 = (D).cell (old C.scheme hC e) ∧
        r (old C.scheme hC d) ≤ r w.1)
    (hone : ∀ b, GradedLe (scope b, 1) ((D).cell c) →
      ∀ d : (D).below ((D).cell c), ∃ w : (D).below ((D).cell c),
        (D).cell w.1 = (scope b, 1) ∧ r d.1 ≤ r w.1)
    (htwo : ∀ b, GradedLe (scope b, 2) ((D).cell c) →
      ∀ d : (D).below ((D).cell c), ∃ w : (D).below ((D).cell c),
        (D).cell w.1 = (scope b, 2) ∧ r d.1 ≤ r w.1)
    (s t : (D).below ((D).cell c))
    (hs : (D).scope s.1 ⊆ (D).scope t.1) (hg : (D).grade s.1 = (D).grade t.1) :
    ∃ w : (D).below ((D).cell c), (D).cell w.1 = (D).cell t.1 ∧ r s.1 ≤ r w.1 := by
  rcases ReceivingLadderCarrier.cell_cases C.scheme hC t.1 with ⟨e, he⟩ | ⟨z, hz⟩
  · have hst : GradedLe ((D).cell s.1) ((D).cell (old C.scheme hC e)) :=
      he ▸ ⟨hs, hg.le⟩
    obtain ⟨d, hd⟩ := below_old C.scheme hC e ⟨s.1, hst⟩
    have hsd : s.1 = old C.scheme hC d.1 := (congrArg Subtype.val hd).symm
    have hge : C.scheme.grade d.1 = C.scheme.grade e := by
      simpa only [hsd, he, CellScheme.grade, old_index] using hg
    obtain ⟨w, hw, hle⟩ := hold d.1 e d.2.1 hge (he ▸ t.2)
    exact ⟨w, he ▸ hw, hsd ▸ hle⟩
  · cases z with
    | request =>
        have hst : GradedLe ((D).cell s.1) ((D).cell (added C.scheme hC .request)) :=
          hz ▸ ⟨hs, hg.le⟩
        have hsr := below_request L hC ⟨s.1, hst⟩
        exact ⟨t, rfl, le_of_eq (congrArg r (hsr.trans hz.symm))⟩
    | ladder b v =>
        have ht : GradedLe (scope b, 1) ((D).cell c) := by
          simpa only [hz, added_index, ReceivingLadderCarrier.newIndex] using t.2
        obtain ⟨w, hw, hle⟩ := hone b ht s
        exact ⟨w, by simpa only [hz, added_index, ReceivingLadderCarrier.newIndex] using hw, hle⟩
    | upper b a node =>
        have ht : GradedLe (scope b, 2) ((D).cell c) := by
          simpa only [hz, added_index, ReceivingLadderCarrier.newIndex] using t.2
        obtain ⟨w, hw, hle⟩ := htwo b ht s
        exact ⟨w, by simpa only [hz, added_index, ReceivingLadderCarrier.newIndex] using hw, hle⟩
    | apex =>
        have ht : 3 ≤ (D).grade c := by
          simpa only [hz, added_index, ReceivingLadderCarrier.newIndex, CellScheme.grade]
            using t.2.2
        omega

/-- Locality at the request inside any orderly row on an enclosing lower domain. -/
theorem request_locality (c : Cell D)
    (r : (D).below ((D).cell c) → ExtOrd) (hr : IsOrderly (fun d => (D).grade d.1) r)
    (hs : GradedLe ((D).cell (added C.scheme hC .request)) ((D).cell c)) :
    TransformsTo
      (fun d : (D).below ((D).cell (added C.scheme hC .request)) => (D).grade d.1)
      ((E).E (added C.scheme hC .request))
      (fun d => min (r ⟨d.1, d.2.trans hs⟩) (r ⟨added C.scheme hC .request, hs⟩)) := by
  have hv : SelfVis 1 (r ⟨added C.scheme hC .request, hs⟩) := by
    simpa only [CellScheme.grade, added_index, ReceivingLadderCarrier.newIndex] using
      (hr ⟨added C.scheme hC .request, hs⟩).symm
  have he : (fun d : (D).below ((D).cell (added C.scheme hC .request)) =>
      min (r ⟨d.1, d.2.trans hs⟩) (r ⟨added C.scheme hC .request, hs⟩)) =
      fun _ => r ⟨added C.scheme hC .request, hs⟩ := by
    funext d
    have hd := below_request L hC d
    have he : (⟨d.1, d.2.trans hs⟩ : (D).below ((D).cell c)) =
        ⟨added C.scheme hC .request, hs⟩ := Subtype.ext hd
    rw [he, min_self]
  rw [he]
  exact request_incidence L hC request _ hv

theorem ladder_consistent (full : Bool) (v : T) : RespectsSemanticsBelow E
    ((D).cell (added C.scheme hC (.ladder full v)))
    ((E).E (added C.scheme hC (.ladder full v))) := by
  refine ⟨(E).orderly _, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    rcases ReceivingLadderCarrier.cell_cases C.scheme hC s with ⟨c, rfl⟩ | ⟨z, rfl⟩
    · have hg : C.scheme.grade c = 1 := by
        simpa only [CellScheme.grade, old_index] using
          below_ladder_grade C.scheme hC full v ⟨old C.scheme hC c, hs⟩
      simpa only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
        view_added, CellScheme.below.incl] using
        ladder_private_incidence L hC request v c hg
    · cases z with
      | request => exact request_locality L hC request _ _ ((E).orderly _) hs
      | ladder b w =>
          simpa only [semantics, ReceivingLadderSemantics.semantics,
            ReceivingLadderSemantics.row, view_added, CellScheme.below.incl] using
            ladder_ladder_incidence L hC request v w b
      | upper b a node =>
          have hh := hs.2
          rw [added_index, added_index] at hh
          change 2 ≤ 1 at hh
          omega
      | apex =>
          have hh := hs.2
          rw [added_index, added_index] at hh
          change 3 ≤ 1 at hh
          omega
  · intro s t hs hg
    simp only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
      view_added]
    apply availability_cases L hC _ (by rw [ladder_grade]; omega)
      (ladderRow C.scheme hC privateField (.field (.req request)) (ranks L) v)
      (ladder_available_old L hC request v full) ?_ ?_ s t hs hg
    · intro b hb d
      exact ladder_available L hC request v full b
        (by simpa only [added_index, ReceivingLadderCarrier.newIndex] using hb.1) d
    · intro b hb
      have hh := hb.2
      rw [added_index] at hh
      change 2 ≤ 1 at hh
      omega

theorem upper_consistent (full : Bool) (a : Controller L) (node : Bool) : RespectsSemanticsBelow E
    ((D).cell (added C.scheme hC (.upper full a node)))
    ((E).E (added C.scheme hC (.upper full a node))) := by
  refine ⟨(E).orderly _, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    rcases ReceivingLadderCarrier.cell_cases C.scheme hC s with ⟨c, rfl⟩ | ⟨z, rfl⟩
    · simpa only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
        view_added, CellScheme.below.incl] using private_incidence L hC request a node c
    · cases z with
      | request => exact request_locality L hC request _ _ ((E).orderly _) hs
      | ladder b v =>
          simpa only [semantics, ReceivingLadderSemantics.semantics,
            ReceivingLadderSemantics.row, view_added, CellScheme.below.incl] using
            upper_ladder_incidence L hC request a node b v
      | upper b c other =>
          simpa only [semantics, ReceivingLadderSemantics.semantics,
            ReceivingLadderSemantics.row, view_added, CellScheme.below.incl] using
            upper_upper_incidence L hC request a c node b other
      | apex =>
          have hh := hs.2
          rw [added_index, added_index] at hh
          change 3 ≤ 2 at hh
          omega
  · intro s t hs hg
    simp only [semantics, ReceivingLadderSemantics.semantics, ReceivingLadderSemantics.row,
      view_added]
    apply availability_cases L hC _ (by rw [upper_grade]) (upperRow L hC request a node)
      (upper_available_old L hC request a node full) ?_ ?_ s t hs hg
    · intro b hb d
      exact upper_available_one L hC request a node full b
        (by simpa only [added_index, ReceivingLadderCarrier.newIndex] using hb.1) d
    · intro b hb d
      exact upper_available_two L hC request a node full b
        (by simpa only [added_index, ReceivingLadderCarrier.newIndex] using hb.1) d

/-- Exhaustive fixed-carrier consistency, with catalogue admission supplying
the original-private incidences and availability. No lifting is assumed. -/
theorem consistent : (E).IsConsistent := by
  intro c
  rcases ReceivingLadderCarrier.cell_cases C.scheme hC c with ⟨a, rfl⟩ | ⟨z, rfl⟩
  · exact old_consistent L hC request a
  · cases z with
    | request => exact request_consistent L hC request
    | ladder b v => exact ladder_consistent L hC request b v
    | upper b a node => exact upper_consistent L hC request b a node
    | apex => exact apex_consistent L hC request

/-- The checked endpoint deliberately stops short of a legal `SemScheme`:
bountifulness is not a consequence of these three fields. -/
theorem coded_complete_consistent :
    (E).IsCoded ∧ (D).IsComplete ∧ (E).IsConsistent :=
  ⟨coded L hC request, complete L hC, consistent L hC request⟩

end
end VaughtConjecture.Knight.ReceivingCatalogueConsistency
