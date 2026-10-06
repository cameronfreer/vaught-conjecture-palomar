/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneBottomCuts

/-! # A structural criterion for all grade-one face lifts

With common full-row orders on the face and target, unrestricted lifting
is equivalent to source-order trace and extension of admissible bottom cuts.
Both conditions concern the source rows only: no section, lawful completion,
ambient, or output-label search is hidden in the structural criterion.

Unique full controllers supply common order. All actual nested block laws,
bottom sources, and distinct occurrences are retained. This is grade one
only, and is not a native identification of KVC's semantics.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

namespace BottomCut

variable {Y S : Type*} [LinearOrder S]

/-- The binary seed of a source cut is source-monotone. -/
theorem seed_order (E : Y → S) (a : Option Y) (d e : Y) (hde : E d ≤ E e) :
    BottomPattern.seed (flag E a) d ≤ BottomPattern.seed (flag E a) e := by
  by_cases he : flag E a e = true
  · have hd : flag E a d = true := by
      cases a with
      | none => contradiction
      | some a =>
        simp only [flag, decide_eq_true_eq] at he ⊢
        exact hde.trans he
    simp [BottomPattern.seed, hd, he]
  · simp only [BottomPattern.seed, ite_eq_right he]
    split_ifs <;> simp

end BottomCut

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ CI : Finset ι × ℕ}

noncomputable local instance (J : Finset ι × ℕ) : Fintype (D.below J) := Fintype.ofFinite _

namespace BottomCut

/-- Admissible source cuts satisfy every nested block implication and kill
every bottom source. This definition has no semantic existence hypothesis. -/
def Admissible (c : Controller D BJ) (a : Option (D.below BJ)) : Prop :=
  BottomPattern.Compatible sem (flag (c.row sem) a) ∧
    ∀ d, c.row sem d = ⊥ → flag (c.row sem) a d = true

/-- Every admissible cut has a canonical lawful binary labelling. -/
theorem seed_respects (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    (c : Controller D BJ) (a : Option (D.below BJ))
    (ha : Admissible (sem := sem) c a) :
    RespectsSemanticsBelow sem BJ (BottomPattern.seed (flag (c.row sem) a)) := by
  apply respects_of_order_and_blocks hc hgrade c
  · intro d
    rw [hgrade]
    exact BottomPattern.seed_visible _ d
  · exact seed_order _ a
  · intro d hd
    exact (BottomPattern.seed_eq_bot _ d).mpr (ha.2 d hd)
  · exact (BottomPattern.compatible_iff _).mp ha.1

/-- A common row order identifies every lawful labelling's bottom pattern
with an admissible cut, including bottom sources and all block conditions. -/
theorem admissible_of_respects (hgrade : BJ.2 = 1) {c : Controller D BJ}
    (H : CommonOrder (sem := sem) c) {p : D.below BJ → ExtOrd}
    (hp : RespectsSemanticsBelow sem BJ p) :
    ∃ a, Admissible (sem := sem) c a ∧
      ∀ d, flag (c.row sem) a d = true ↔ p d = ⊥ := by
  obtain ⟨hord, hbot⟩ := H.of_respects hgrade hp
  obtain ⟨a, ha⟩ := exists_flag hord
  refine ⟨a, ⟨?_, fun d hd => (ha d).mpr (hbot d hd)⟩, ha⟩
  apply (BottomPattern.compatible_iff _).mpr
  apply rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects hp)
  intro d
  exact (BottomPattern.seed_eq_bot _ d).trans (ha d)

end BottomCut

/-- Every admissible source cut on the face extends to an admissible cut
of the target, with the same bottom flags at every actual face occurrence. -/
def CutTrace (h : GradedLe CI BJ) (b : Controller D CI) (c : Controller D BJ) : Prop :=
  ∀ a : Option (D.below CI), BottomCut.Admissible (sem := sem) b a →
    ∃ t : Option (D.below BJ), BottomCut.Admissible (sem := sem) c t ∧
      ∀ d, BottomCut.flag (c.row sem) t (CellScheme.below.mono h d) =
        BottomCut.flag (b.row sem) a d

/-- Source-order trace and finite cut extension construct a section of
every lawful prescribed face. No section or ambient is an input hypothesis. -/
theorem section_of_cutTrace (hc : sem.IsConsistent) (h : GradedLe CI BJ)
    (hface : CI.2 = 1) (htarget : BJ.2 = 1)
    {b : Controller D CI} {c : Controller D BJ}
    (Hb : CommonOrder (sem := sem) b) (Ht : RowTrace (sem := sem) h b c)
    (Hz : CutTrace (sem := sem) h b c)
    {p : D.below CI → ExtOrd} (hp : RespectsSemanticsBelow sem CI p) :
    ∃ s, RespectsSemanticsBelow sem BJ s ∧
      ∀ d, s (CellScheme.below.mono h d) = p d := by
  obtain ⟨a, ha, hpa⟩ := BottomCut.admissible_of_respects hface Hb hp
  obtain ⟨t, ht, hta⟩ := Hz a ha
  obtain ⟨hpo, hpb⟩ := Hb.of_respects hface hp
  have hv : ∀ d, SelfVis 1 (p d) := by
    intro d
    have hh : SelfVis (D.grade d.1) (p d) := (hp.orderly d).symm
    rwa [grade_eq_one hface d] at hh
  have hm : ∀ d, BottomCut.flag (c.row sem) t (CellScheme.below.mono h d) = true ↔
      p d = ⊥ := by
    intro d
    rw [hta d]
    exact hpa d
  have hcheck : BottomPattern.Check (sem := sem) c (BottomCut.flag (c.row sem) t)
      (CellScheme.below.mono h) p := by
    refine ⟨Propagation.check_of_compatible_order ?_ (BottomCut.seed_order _ t) ?_ ?_ ?_, ht.1⟩
    · exact fun d e hde => hpo d e (Ht.order d e hde)
    · exact fun d hd => hpb d (Ht.bottom d hd)
    · intro d hd
      exact (BottomPattern.seed_eq_bot _ d).mpr (ht.2 d hd)
    · intro d
      exact (BottomPattern.seed_cap hv hm d).symm
  obtain ⟨hr, _, he⟩ := least_bottom_lift_of_check hc htarget
    (by simpa only [htarget] using hv) c _ hcheck (fun _ => ⊥)
  exact ⟨_, hr, he⟩

/-- Any all-face section theorem forces the source trace: use the face's
own lawful row as the prescription and read its section in the target order. -/
theorem rowTrace_of_sections (hc : sem.IsConsistent) (h : GradedLe CI BJ)
    (htarget : BJ.2 = 1) (b : Controller D CI) {c : Controller D BJ}
    (Hc : CommonOrder (sem := sem) c)
    (hs : ∀ p : D.below CI → ExtOrd, RespectsSemanticsBelow sem CI p →
      ∃ s, RespectsSemanticsBelow sem BJ s ∧ ∀ d, s (CellScheme.below.mono h d) = p d) :
    RowTrace (sem := sem) h b c := by
  obtain ⟨s, hs, he⟩ := hs (b.row sem) (b.row_respects hc)
  obtain ⟨ho, hb⟩ := Hc.of_respects htarget hs
  refine ⟨?_, ?_⟩
  · intro d e hde
    rw [← he d, ← he e]
    exact ho _ _ hde
  · intro d hd
    rw [← he d]
    exact hb _ hd

/-- The binary seed of each admissible face cut makes cut extension
necessary for any all-face section theorem. -/
theorem cutTrace_of_sections (hc : sem.IsConsistent) (h : GradedLe CI BJ)
    (hface : CI.2 = 1) (htarget : BJ.2 = 1) (b : Controller D CI)
    {c : Controller D BJ} (Hc : CommonOrder (sem := sem) c)
    (hs : ∀ p : D.below CI → ExtOrd, RespectsSemanticsBelow sem CI p →
      ∃ s, RespectsSemanticsBelow sem BJ s ∧ ∀ d, s (CellScheme.below.mono h d) = p d) :
    CutTrace (sem := sem) h b c := by
  intro a ha
  obtain ⟨s, hs, he⟩ := hs _ (BottomCut.seed_respects hc hface b a ha)
  obtain ⟨t, ht, hst⟩ := BottomCut.admissible_of_respects htarget Hc hs
  refine ⟨t, ht, fun d => Bool.eq_iff_iff.mpr ?_⟩
  rw [hst, he d]
  exact BottomPattern.seed_eq_bot _ d

/-- Exact structural characterization of arbitrary sections under common
full-row orders. CutTrace quantifies only over finite source-cut indices. -/
theorem sections_iff_traces (hc : sem.IsConsistent) (h : GradedLe CI BJ)
    (hface : CI.2 = 1) (htarget : BJ.2 = 1)
    {b : Controller D CI} {c : Controller D BJ}
    (Hb : CommonOrder (sem := sem) b) (Hc : CommonOrder (sem := sem) c) :
    (∀ p : D.below CI → ExtOrd, RespectsSemanticsBelow sem CI p →
      ∃ s, RespectsSemanticsBelow sem BJ s ∧ ∀ d, s (CellScheme.below.mono h d) = p d) ↔
      RowTrace (sem := sem) h b c ∧ CutTrace (sem := sem) h b c := by
  constructor
  · intro hs
    exact ⟨rowTrace_of_sections hc h htarget b Hc hs,
      cutTrace_of_sections hc h hface htarget b Hc hs⟩
  · rintro ⟨Ht, Hz⟩ p hp
    exact section_of_cutTrace hc h hface htarget Hb Ht Hz hp

/-- Under unique full controllers, the entire all-ordinal lifting clause
is equivalent to source-order trace and finite admissible-cut extension. -/
theorem liftsAt_iff_traces_of_unique (hc : sem.IsConsistent) (h : GradedLe CI BJ)
    (hface : CI.2 = 1) (htarget : BJ.2 = 1)
    (b : Controller D CI) (c : Controller D BJ)
    (hb : ∀ b' : Controller D CI, b' = b) (hc' : ∀ c' : Controller D BJ, c' = c) :
    LiftsAt sem h ↔ RowTrace (sem := sem) h b c ∧ CutTrace (sem := sem) h b c := by
  rw [liftsAt_iff_sections_of_unique hc h htarget c hc']
  exact sections_iff_traces hc h hface htarget
    (commonOrder_of_unique b hb) (commonOrder_of_unique c hc')

/-- A missing admissible cut gives an explicit lawful binary prescribed
face with no section, not merely a rejected proposed witness. -/
theorem no_section_of_missing_cut (hc : sem.IsConsistent) (h : GradedLe CI BJ)
    (hface : CI.2 = 1) (htarget : BJ.2 = 1) (b : Controller D CI)
    {c : Controller D BJ} (Hc : CommonOrder (sem := sem) c)
    (a : Option (D.below CI)) (ha : BottomCut.Admissible (sem := sem) b a)
    (hmiss : ¬ ∃ t : Option (D.below BJ), BottomCut.Admissible (sem := sem) c t ∧
      ∀ d, BottomCut.flag (c.row sem) t (CellScheme.below.mono h d) =
        BottomCut.flag (b.row sem) a d) :
    RespectsSemanticsBelow sem CI (BottomPattern.seed (BottomCut.flag (b.row sem) a)) ∧
      ¬ ∃ s, RespectsSemanticsBelow sem BJ s ∧
        ∀ d, s (CellScheme.below.mono h d) =
          BottomPattern.seed (BottomCut.flag (b.row sem) a) d := by
  refine ⟨BottomCut.seed_respects hc hface b a ha, ?_⟩
  rintro ⟨s, hs, he⟩
  obtain ⟨t, ht, hst⟩ := BottomCut.admissible_of_respects htarget Hc hs
  apply hmiss
  refine ⟨t, ht, fun d => Bool.eq_iff_iff.mpr ?_⟩
  rw [hst, he d]
  exact BottomPattern.seed_eq_bot _ d

/-- Source traces compose along literal lower-domain inclusions. -/
theorem RowTrace.comp {AJ : Finset ι × ℕ} {h : GradedLe AJ CI} {h' : GradedLe CI BJ}
    {a : Controller D AJ} {b : Controller D CI} {c : Controller D BJ}
    (H : RowTrace (sem := sem) h a b) (H' : RowTrace (sem := sem) h' b c) :
    RowTrace (sem := sem) ⟨h.1.trans h'.1, h.2.trans h'.2⟩ a c where
  order d e hd := H.order d e (H'.order _ _ hd)
  bottom d hd := H.bottom d (H'.bottom _ hd)

/-- Cut-extension certificates compose; no faithful transformations are
composed, and every intermediate bottom flag is retained exactly. -/
theorem CutTrace.comp {AJ : Finset ι × ℕ} {h : GradedLe AJ CI} {h' : GradedLe CI BJ}
    {a : Controller D AJ} {b : Controller D CI} {c : Controller D BJ}
    (H : CutTrace (sem := sem) h a b) (H' : CutTrace (sem := sem) h' b c) :
    CutTrace (sem := sem) ⟨h.1.trans h'.1, h.2.trans h'.2⟩ a c := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := H x hx
  obtain ⟨z, hz, hyz⟩ := H' y hy
  exact ⟨z, hz, fun d => (hyz (CellScheme.below.mono h d)).trans (hxy d)⟩

end VaughtConjecture.Knight.FullRowLifting
