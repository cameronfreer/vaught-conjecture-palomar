/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneInputEncoding

/-! # A bounded universal test for a grade-one bountifulness clause

For a face with m occurrences and a target with n occurrences, all ordinal
inputs reduce to the alphabet {bottom, 1, ..., m+n+1}. Input lawfulness, cap
agreement, and the existence or nonexistence of a lift survive the reduction.

For consistent semantics and inhabited grade-one face and target indices,
lawfulness and lifting are then replaced by finite source-order and block-bottom
tests. Source rows and all occurrences remain literal. This proves a finite
universal characterization; it does not run an exhaustive solver on KVC's rows
or assert that any new construction passes. No mixed-grade claim is made.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

namespace InputEncoding

section Inventory

variable {X Y : Type*} [Fintype X] [Fintype Y]

open Classical in
/-- The joint input inventory, including the actual cap. -/
noncomputable def inventory (p : X → ExtOrd) (q : Y → ExtOrd) (γ : ExtOrd) : Finset ExtOrd :=
  insert γ ((Finset.univ.image p) ∪ (Finset.univ.image q))

theorem prescribed_mem (p : X → ExtOrd) (q : Y → ExtOrd) (γ : ExtOrd) (x : X) :
    p x ∈ inventory p q γ := by classical simp [inventory]

theorem ambient_mem (p : X → ExtOrd) (q : Y → ExtOrd) (γ : ExtOrd) (y : Y) :
    q y ∈ inventory p q γ := by classical simp [inventory]

theorem cap_mem (p : X → ExtOrd) (q : Y → ExtOrd) (γ : ExtOrd) :
    γ ∈ inventory p q γ := by classical simp [inventory]

theorem inventory_card (p : X → ExtOrd) (q : Y → ExtOrd) (γ : ExtOrd) :
    (inventory p q γ).card ≤ Fintype.card X + Fintype.card Y + 1 := by
  classical
  calc
    (inventory p q γ).card ≤ ((Finset.univ.image p) ∪ (Finset.univ.image q)).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (Finset.univ.image p).card + (Finset.univ.image q).card + 1 :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ Fintype.card X + Fintype.card Y + 1 := by
      have hp := Finset.card_image_le (s := Finset.univ) (f := p)
      have hq := Finset.card_image_le (s := Finset.univ) (f := q)
      simpa only [Finset.card_univ] using Nat.add_le_add_right (Nat.add_le_add hp hq) 1

theorem inventory_visible {p : X → ExtOrd} {q : Y → ExtOrd} {γ : ExtOrd}
    (hp : ∀ x, SelfVis 1 (p x)) (hq : ∀ y, SelfVis 1 (q y)) (hγ : SelfVis 1 γ) :
    ∀ v ∈ inventory p q γ, SelfVis 1 v := by
  classical
  intro v hv
  simp only [inventory, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hv
  rcases hv with rfl | ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact hγ
  · exact hp x
  · exact hq y

end Inventory

end InputEncoding

/-- Explicit finite enumeration of the bounded alphabet. -/
noncomputable def finiteValue {N : ℕ} (i : Fin (N + 1)) : ExtOrd :=
  if i.val = 0 then ⊥ else ofOrd i.val

theorem finiteValue_mem {N : ℕ} (i : Fin (N + 1)) : InAlphabet N (finiteValue i) := by
  by_cases hi : i.val = 0
  · exact Or.inl (ite_eq_left hi)
  · exact Or.inr ⟨i.val, Nat.one_le_iff_ne_zero.mpr hi, Nat.le_of_lt_succ i.isLt,
      ite_eq_right hi⟩

theorem InAlphabet.exists_finiteValue {N : ℕ} {x : ExtOrd} (hx : InAlphabet N x) :
    ∃ i : Fin (N + 1), finiteValue i = x := by
  rcases hx with rfl | ⟨n, hn, hN, rfl⟩
  · exact ⟨0, rfl⟩
  · refine ⟨⟨n, Nat.lt_succ_of_le hN⟩, ?_⟩
    exact ite_eq_right (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {CI BJ : Finset ι × ℕ}

noncomputable local instance (J : Finset ι × ℕ) : Fintype (D.below J) := Fintype.ofFinite _

/-- Exactly one literal lifting clause; plan membership and strictness can be
supplied by the caller quantifying over the pairs in IsBountiful. -/
def LiftsAt (sem : Semantics D) (h : GradedLe CI BJ) : Prop :=
  ∀ (p : D.below CI → ExtOrd) (q : D.below BJ → ExtOrd) (γ : ExtOrd),
    RespectsSemanticsBelow sem CI p → RespectsSemanticsBelow sem BJ q →
    SelfVis BJ.2 γ →
    (∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) →
    HasLift (sem := sem) (CellScheme.below.mono h) p q γ

/-- Number of input labels, counting occurrences rather than their distinct values. -/
noncomputable def inputBound (D : CellScheme A) (CI BJ : Finset ι × ℕ) : ℕ :=
  Fintype.card (D.below CI) + Fintype.card (D.below BJ) + 1

/-- The same literal clause, restricted to a bounded finite alphabet. -/
def FiniteLiftsAt (N : ℕ) (sem : Semantics D) (h : GradedLe CI BJ) : Prop :=
  ∀ (p : D.below CI → ExtOrd) (q : D.below BJ → ExtOrd) (γ : ExtOrd),
    (∀ d, InAlphabet N (p d)) → (∀ d, InAlphabet N (q d)) → InAlphabet N γ →
    RespectsSemanticsBelow sem CI p → RespectsSemanticsBelow sem BJ q →
    (∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) →
    HasLift (sem := sem) (CellScheme.below.mono h) p q γ

/-- Every ordinal input is represented, with no assumption of consistency or
completeness needed for the encoding argument itself. -/
theorem liftsAt_iff_finite (h : GradedLe CI BJ) (hgrade : BJ.2 = 1) :
    LiftsAt sem h ↔ FiniteLiftsAt (inputBound D CI BJ) sem h := by
  constructor
  · intro hl p q γ _ _ hγ hp hq hag
    apply hl p q γ hp hq
    · rw [hgrade]
      exact hγ.visible
    · exact hag
  · intro hl p q γ hp hq hγ hag
    have hpv : ∀ d, SelfVis 1 (p d) := by
      intro d
      have hd : D.grade d.1 = 1 := grade_eq_one hgrade (CellScheme.below.mono h d)
      have hh : SelfVis (D.grade d.1) (p d) := (hp.orderly d).symm
      rwa [hd] at hh
    have hqv : ∀ d, SelfVis 1 (q d) := by
      intro d
      have hh : SelfVis (D.grade d.1) (q d) := (hq.orderly d).symm
      rwa [grade_eq_one hgrade d] at hh
    have hγv : SelfVis 1 γ := by rwa [hgrade] at hγ
    let S := InputEncoding.inventory p q γ
    have hS : ∀ v ∈ S, SelfVis 1 v := InputEncoding.inventory_visible hpv hqv hγv
    have hsize : S.card ≤ inputBound D CI BJ := InputEncoding.inventory_card p q γ
    let f := InputEncoding.encode S
    have hf := InputEncoding.encode_bounded hS
    have hsmall : ∀ d : D.below CI, D.grade d.1 ≤ 1 := fun d => by
      exact (grade_eq_one hgrade (CellScheme.below.mono h d)).le
    have hlarge : ∀ d : D.below BJ, D.grade d.1 ≤ 1 := fun d => by
      rw [grade_eq_one hgrade d]
    have hpm := InputEncoding.prescribed_mem p q γ
    have hqm := InputEncoding.ambient_mem p q γ
    have hγm := InputEncoding.cap_mem p q γ
    have hp' := map_respects_of_bounded_reflecting hf (InputEncoding.encode_bot_iff S) hsmall hp
    have hq' := map_respects_of_bounded_reflecting hf (InputEncoding.encode_bot_iff S) hlarge hq
    have hg' : ∀ d, min (f (q (CellScheme.below.mono h d))) (f γ) =
        min (f (p d)) (f γ) := by
      intro d
      rw [← hf.mono.map_min, ← hf.mono.map_min, hag d]
    have henc := hl (fun d => f (p d)) (fun d => f (q d)) (f γ)
      (fun d => (InputEncoding.encode_alphabet (hpm d)).mono hsize)
      (fun d => (InputEncoding.encode_alphabet (hqm d)).mono hsize)
      ((InputEncoding.encode_alphabet hγm).mono hsize) hp' hq' hg'
    exact (lift_iff_encoded hS hgrade hpm hqm hγm).mpr henc

/-- The bounded quantifiers can be over genuinely finite types, not over
ordinal-valued variables with an implicit promise to enumerate them. -/
theorem finiteLiftsAt_iff_codes (N : ℕ) (h : GradedLe CI BJ) :
    FiniteLiftsAt N sem h ↔
      ∀ (p : D.below CI → Fin (N + 1)) (q : D.below BJ → Fin (N + 1)) (γ : Fin (N + 1)),
        RespectsSemanticsBelow sem CI (fun d => finiteValue (p d)) →
        RespectsSemanticsBelow sem BJ (fun d => finiteValue (q d)) →
        (∀ d, min (finiteValue (q (CellScheme.below.mono h d))) (finiteValue γ) =
          min (finiteValue (p d)) (finiteValue γ)) →
        HasLift (sem := sem) (CellScheme.below.mono h)
          (fun d => finiteValue (p d)) (fun d => finiteValue (q d)) (finiteValue γ) := by
  classical
  constructor
  · intro hl p q γ hp hq hag
    exact hl _ _ _ (fun d => finiteValue_mem (p d)) (fun d => finiteValue_mem (q d))
      (finiteValue_mem γ) hp hq hag
  · intro hl p q γ hpN hqN hγN hp hq hag
    choose pc hpc using fun d => (hpN d).exists_finiteValue
    choose qc hqc using fun d => (hqN d).exists_finiteValue
    obtain ⟨gc, hgc⟩ := hγN.exists_finiteValue
    have hpce : (fun d => finiteValue (pc d)) = p := funext hpc
    have hqce : (fun d => finiteValue (qc d)) = q := funext hqc
    have hh := hl pc qc gc
    rw [hpce, hqce, hgc] at hh
    exact hh hp hq (fun d => by rw [hqc, hpc]; exact hag d)

/-- Input respect at a grade-one domain reduces to finite order and source-block
conditions, once the input labels are known visible. -/
def FiniteRespect (sem : Semantics D) (J : Finset ι × ℕ) (r : D.below J → ExtOrd) : Prop :=
  RowBlockBottom sem J r ∧ ∃ c : Controller D J,
    (∀ d e, c.row sem d ≤ c.row sem e → r d ≤ r e) ∧
    (∀ d, c.row sem d = ⊥ → r d = ⊥)

theorem respects_iff_finiteRespect (hc : sem.IsConsistent) {J : Finset ι × ℕ}
    (hgrade : J.2 = 1) (c₀ : Controller D J) {r : D.below J → ExtOrd}
    (hv : ∀ d, SelfVis J.2 (r d)) :
    RespectsSemanticsBelow sem J r ↔ FiniteRespect sem J r := by
  constructor
  · intro hr
    obtain ⟨c, τ, hτ, _, he⟩ := exists_full_row_representation hgrade c₀ hr
    refine ⟨rowBlockBottom_of_respects hr, c, ?_, ?_⟩
    · intro d e hde
      rw [← he d, ← he e]
      exact hτ.mono hde
    · intro d hd
      rw [← he d, hd, hτ.bot]
  · rintro ⟨hb, c, hord, hbot⟩
    exact respects_of_order_and_blocks hc hgrade c hv hord hbot hb

/-- The previously proved exact output test, with no ordinal output variables. -/
def CapCheck {X : Type*} [Fintype X] (sem : Semantics D) (embed : X → D.below BJ)
    (p : X → ExtOrd) (q : D.below BJ → ExtOrd) (γ : ExtOrd) : Prop :=
  (γ = ⊥ ∧ ∃ c : Controller D BJ, ∃ z : D.below BJ → Bool,
    BottomPattern.Check (sem := sem) c z embed p) ∨
  (γ ≠ ⊥ ∧ ∃ c : Controller D BJ, Propagation.Check (c.row sem) embed p q γ)

/-- A genuinely finite universal test, after the fixed row comparisons are
identified: finite input arrays, finite controller choices, and Boolean flags.
There is no respect, locality-witness, or extension-existence assumption inside. -/
def FiniteTest (N : ℕ) (sem : Semantics D) (h : GradedLe CI BJ) : Prop :=
  ∀ (p : D.below CI → Fin (N + 1)) (q : D.below BJ → Fin (N + 1)) (γ : Fin (N + 1)),
    FiniteRespect sem CI (fun d => finiteValue (p d)) →
    FiniteRespect sem BJ (fun d => finiteValue (q d)) →
    (∀ d, min (finiteValue (q (CellScheme.below.mono h d))) (finiteValue γ) =
      min (finiteValue (p d)) (finiteValue γ)) →
    CapCheck sem (CellScheme.below.mono h)
      (fun d => finiteValue (p d)) (fun d => finiteValue (q d)) (finiteValue γ)

/-- Exact universal grade-one bountifulness test at the explicit bound m+n+1.
Failure of the universal test is equivalent to an actual failed lifting input,
not just to failure of one selected witness or branch. -/
theorem liftsAt_iff_finiteTest (hc : sem.IsConsistent) (h : GradedLe CI BJ)
    (hsmall : CI.2 = 1) (hlarge : BJ.2 = 1)
    (csmall : Controller D CI) (clarge : Controller D BJ) :
    LiftsAt sem h ↔ FiniteTest (inputBound D CI BJ) sem h := by
  rw [liftsAt_iff_finite h hlarge, finiteLiftsAt_iff_codes]
  have hs (p : D.below CI → Fin (inputBound D CI BJ + 1)) :
      RespectsSemanticsBelow sem CI (fun d => finiteValue (p d)) ↔
        FiniteRespect sem CI (fun d => finiteValue (p d)) :=
    respects_iff_finiteRespect hc hsmall csmall (fun d => by
      rw [hsmall]; exact (finiteValue_mem (p d)).visible)
  have ht (q : D.below BJ → Fin (inputBound D CI BJ + 1)) :
      RespectsSemanticsBelow sem BJ (fun d => finiteValue (q d)) ↔
        FiniteRespect sem BJ (fun d => finiteValue (q d)) :=
    respects_iff_finiteRespect hc hlarge clarge (fun d => by
      rw [hlarge]; exact (finiteValue_mem (q d)).visible)
  constructor
  · intro hl p q γ hp hq hag
    have hr := hl p q γ ((hs p).mpr hp) ((ht q).mpr hq) hag
    exact (lift_iff_all_cap_check hc hlarge clarge ((ht q).mpr hq)
      (fun d => by rw [hlarge]; exact (finiteValue_mem (p d)).visible)
      (by rw [hlarge]; exact (finiteValue_mem γ).visible)).mp hr
  · intro hl p q γ hp hq hag
    exact (lift_iff_all_cap_check hc hlarge clarge hq
      (fun d => by rw [hlarge]; exact (finiteValue_mem (p d)).visible)
      (by rw [hlarge]; exact (finiteValue_mem γ).visible)).mpr
      (hl p q γ ((hs p).mp hp) ((ht q).mp hq) hag)

/-- Small-counterexample property: every failed grade-one clause has a lawful
counterexample in the same bounded finite alphabet, with every branch rejected. -/
theorem not_liftsAt_iff_finite_counterexample (hc : sem.IsConsistent) (h : GradedLe CI BJ)
    (hsmall : CI.2 = 1) (hlarge : BJ.2 = 1)
    (csmall : Controller D CI) (clarge : Controller D BJ) :
    ¬ LiftsAt sem h ↔
      ∃ (p : D.below CI → Fin (inputBound D CI BJ + 1))
        (q : D.below BJ → Fin (inputBound D CI BJ + 1)) (γ : Fin (inputBound D CI BJ + 1)),
        FiniteRespect sem CI (fun d => finiteValue (p d)) ∧
        FiniteRespect sem BJ (fun d => finiteValue (q d)) ∧
        (∀ d, min (finiteValue (q (CellScheme.below.mono h d))) (finiteValue γ) =
          min (finiteValue (p d)) (finiteValue γ)) ∧
        ¬ CapCheck sem (CellScheme.below.mono h)
          (fun d => finiteValue (p d)) (fun d => finiteValue (q d)) (finiteValue γ) := by
  classical
  rw [liftsAt_iff_finiteTest hc h hsmall hlarge csmall clarge]
  simp only [FiniteTest, not_forall, exists_prop]

end VaughtConjecture.Knight.FullRowLifting
