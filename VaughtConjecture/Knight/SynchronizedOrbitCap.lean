/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTailCap
public import VaughtConjecture.Knight.ReferenceOrbitCompletion

/-! # Synchronized highest-grade clipping for a donor-orbit row

Lowering only a new unique controller can violate availability from its retained
old donor. Here the highest old grade moves with the new controller. The old
semantics remain respected, every lower grade stays literal, and exact tests say
when the prescribed labels and the original external capped values survive.

The donor's original faithful witness still serves the orbit row at the new cap.
This constructs old-side respect, the new row's locality, and all old same-grade
incoming bounds. It does not construct the remaining mixed rows, their localities,
or a completion of an arbitrary old face. The initial old labelling is lawful.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.OrbitCap

open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {BJ : Finset ι × ℕ}

/-- Clip only the highest grade of the actual lower domain. -/
noncomputable def synchronizedCap (U : ExtOrd) (p : D.below BJ → ExtOrd) :
    D.below BJ → ExtOrd := gradeTailCap (BJ.2 - 1) U p

theorem synchronizedCap_lower (p : D.below BJ → ExtOrd) (U : ExtOrd)
    (d : D.below BJ) (hd : D.grade d.1 < BJ.2) :
    synchronizedCap U p d = p d :=
  gradeTailCap_eq (by omega)

theorem synchronizedCap_highest (p : D.below BJ → ExtOrd) (U : ExtOrd)
    (d : D.below BJ) (hd : D.grade d.1 = BJ.2) :
    synchronizedCap U p d = min (p d) U := by
  have hp := D.grade_pos d.1
  simp only [synchronizedCap, gradeTailCap,
    ite_eq_right (show ¬ D.grade d.1 ≤ BJ.2 - 1 by omega)]

theorem synchronizedCap_respects {sem : Semantics D} {p : D.below BJ → ExtOrd}
    (hp : RespectsSemanticsBelow sem BJ p) {U : ExtOrd} (hU : SelfVis BJ.2 U) :
    RespectsSemanticsBelow sem BJ (synchronizedCap U p) := hp.gradeTailCap _ hU

/-- The unchanged capped target is the reason the old witness can be reused. -/
theorem synchronizedCap_capped (p : D.below BJ → ExtOrd) (U : ExtOrd)
    (d : D.below BJ) : min (synchronizedCap U p d) U = min (p d) U :=
  gradeTailCap_capped p _ U d

/-- All old highest-grade requesters are now bounded by the new owner's label. -/
theorem synchronizedCap_incoming (p : D.below BJ → ExtOrd) (U : ExtOrd)
    (d : D.below BJ) (hd : D.grade d.1 = BJ.2) : synchronizedCap U p d ≤ U := by
  rw [synchronizedCap_highest p U d hd]
  exact min_le_right _ _

/-- Exact preservation of arbitrary occurrence-wise external caps. Their visibility
is not strengthened, and no common ambient completion is assumed. -/
theorem synchronizedCap_receipts_iff (p γ : D.below BJ → ExtOrd) (U : ExtOrd) :
    (∀ d, min (synchronizedCap U p d) (γ d) = min (p d) (γ d)) ↔
    ∀ d, D.grade d.1 = BJ.2 → min (p d) (γ d) ≤ U := by
  constructor
  · intro h d hd
    have he := h d
    rw [synchronizedCap_highest p U d hd, min_right_comm] at he
    exact min_eq_left_iff.mp he
  · intro h d
    rcases lt_or_eq_of_le d.2.2 with hd | hd
    · rw [synchronizedCap_lower p U d hd]
    · rw [synchronizedCap_highest p U d hd, min_right_comm, min_eq_left (h d hd)]

/-- Exact preservation of the prescribed occurrences, including auxiliaries. -/
theorem synchronizedCap_protected_iff (p : D.below BJ → ExtOrd)
    (S : Set (D.below BJ)) (U : ExtOrd) :
    (∀ d ∈ S, synchronizedCap U p d = p d) ↔
    ∀ d ∈ S, D.grade d.1 = BJ.2 → p d ≤ U := by
  constructor
  · intro h d hd hg
    have he := h d hd
    rw [synchronizedCap_highest p U d hg] at he
    exact min_eq_left_iff.mp he
  · intro h d hd
    rcases lt_or_eq_of_le d.2.2 with hg | hg
    · exact synchronizedCap_lower p U d hg
    · rw [synchronizedCap_highest p U d hg, min_eq_left (h d hd hg)]

/-- Finite lower bound contributed by the original external capped values and
the protected highest-grade labels. Lower grades impose no clipping bound. -/
noncomputable def preservationBound (p γ : D.below BJ → ExtOrd)
    (S : Set (D.below BJ)) : ExtOrd := by
  classical
  letI := Fintype.ofFinite (D.below BJ)
  exact Finset.univ.sup fun d => if D.grade d.1 = BJ.2 then
    max (min (p d) (γ d)) (if d ∈ S then p d else ⊥) else ⊥

theorem preservationBound_le_iff (p γ : D.below BJ → ExtOrd)
    (S : Set (D.below BJ)) (U : ExtOrd) :
    preservationBound p γ S ≤ U ↔
    (∀ d, min (synchronizedCap U p d) (γ d) = min (p d) (γ d)) ∧
    (∀ d ∈ S, synchronizedCap U p d = p d) := by
  classical
  let _ := Fintype.ofFinite (D.below BJ)
  rw [synchronizedCap_receipts_iff, synchronizedCap_protected_iff]
  simp only [preservationBound, Finset.sup_le_iff, Finset.mem_univ, true_implies]
  constructor
  · intro h
    constructor
    · intro d hd
      have hh := h d
      rw [ite_eq_left hd] at hh
      exact (max_le_iff.mp hh).1
    · intro d hd hg
      have hh := h d
      rw [ite_eq_left hg, ite_eq_left hd] at hh
      exact (max_le_iff.mp hh).2
  · rintro ⟨hr, hs⟩ d
    split_ifs with hg hd
    · exact max_le (hr d hg) (hs d hd hg)
    · exact max_le (hr d hg) bot_le
    · exact bot_le

section Row

variable {I : Type*} {newGrade : I → ℕ} {E : D.below BJ → ExtOrd}
  {ref : I → D.below BJ} {offset : I → ℕ} {p : D.below BJ → ExtOrd}
  {y : I → ExtOrd} {c : D.below BJ}

theorem synchronizedCap_target (p : D.below BJ → ExtOrd) (y : I → ExtOrd)
    (U : ExtOrd) :
    (fun d => min (labels (synchronizedCap U p) y d) U) =
    (fun d => min (labels p y d) U) := by
  funext d
  cases d with
  | inl d => exact synchronizedCap_capped p U d
  | inr i => rfl

/-- Reuse the donor's one faithful witness with the synchronized old labels.
The equations use the original reference labels; lower-grade references remain
literal, and the capped orbit equations are unchanged even at the highest grade. -/
theorem synchronizedCap_transforms (hc : D.grade c.1 = BJ.2)
    (hnew : ∀ i, newGrade i ≤ BJ.2) (hoff : ∀ i, offset i ≤ BJ.2)
    (hH : SelfVis BJ.2 (p c))
    (hold : TransformsTo (fun d : D.below BJ => D.grade d.1) E
      (fun d => min (p d) (p c)))
    {U : ExtOrd} (hU : SelfVis BJ.2 U) (hUH : U ≤ p c)
    (he : ∀ i, min (y i) U =
      min (extVisibilityReplace (p (ref i)) BJ.2 (offset i)) U) :
    TransformsTo (Sum.elim (fun d : D.below BJ => D.grade d.1) newGrade)
      (row E ref offset BJ.2) (fun d => min (labels (synchronizedCap U p) y d) U) := by
  have ht := transforms_of_equations (grade := fun d : D.below BJ => D.grade d.1)
    hc (fun d => d.2.2) hnew hoff hH hold hU hUH he
  refine transformsTo_congr rfl rfl ?_ ht
  funext d
  cases d with
  | inl d => exact (synchronizedCap_capped p U d).symm
  | inr i => rfl

/-- Joint local construction: the old semantics are respected, the new orbit row
has locality, and every old highest-grade requester lies below its new label.
The theorem supplies these obligations; it does not assume them of the output. -/
theorem synchronizedCap_local_package {sem : Semantics D}
    (hp : RespectsSemanticsBelow sem BJ p) (hc : D.grade c.1 = BJ.2)
    (hnew : ∀ i, newGrade i ≤ BJ.2) (hoff : ∀ i, offset i ≤ BJ.2)
    (hold : TransformsTo (fun d : D.below BJ => D.grade d.1) E
      (fun d => min (p d) (p c)))
    {U : ExtOrd} (hU : SelfVis BJ.2 U) (hUH : U ≤ p c)
    (he : ∀ i, min (y i) U =
      min (extVisibilityReplace (p (ref i)) BJ.2 (offset i)) U) :
    RespectsSemanticsBelow sem BJ (synchronizedCap U p) ∧
    TransformsTo (Sum.elim (fun d : D.below BJ => D.grade d.1) newGrade)
      (row E ref offset BJ.2) (fun d => min (labels (synchronizedCap U p) y d) U) ∧
    ∀ d : D.below BJ, D.grade d.1 = BJ.2 → synchronizedCap U p d ≤ U := by
  refine ⟨synchronizedCap_respects hp hU, ?_, synchronizedCap_incoming p U⟩
  exact synchronizedCap_transforms hc hnew hoff (hc ▸ (hp.orderly c).symm) hold hU hUH he

/-- Exact feasibility of this synchronized construction. The effective lower bound
includes every protected old label and every old capped value, as well as an explicit
additional bound `b` (for example, fresh highest-grade incoming requests). The ambient
new-owner value `V` and its external cap `δ` remain independent of the old donor.

When the right side holds, its displayed `requiredCap` is a witnessing cap. Failure
rules out this synchronized donor-row construction, not all possible scheme lifts. -/
theorem synchronizedCap_feasible_iff (hc : D.grade c.1 = BJ.2)
    (hnew : ∀ i, newGrade i ≤ BJ.2) (hoff : ∀ i, offset i ≤ BJ.2)
    (hH : SelfVis BJ.2 (p c))
    (hold : TransformsTo (fun d : D.below BJ => D.grade d.1) E
      (fun d => min (p d) (p c)))
    (γ : D.below BJ → ExtOrd) (S : Set (D.below BJ)) {V δ b : ExtOrd}
    (hV : SelfVis BJ.2 V) :
    (∃ U, SelfVis BJ.2 U ∧ U ≤ p c ∧ b ≤ U ∧ min U δ = min V δ ∧
      (∀ d, min (synchronizedCap U p d) (γ d) = min (p d) (γ d)) ∧
      (∀ d ∈ S, synchronizedCap U p d = p d) ∧
      TransformsTo (Sum.elim (fun d : D.below BJ => D.grade d.1) newGrade)
        (row E ref offset BJ.2) (fun d => min (labels (synchronizedCap U p) y d) U)) ↔
    let B := max b (preservationBound p γ S)
    let C := requiredCap BJ.2 V δ B
    C ≤ p c ∧ min B δ ≤ min V δ ∧
      ∀ i, min (y i) C = min (extVisibilityReplace (p (ref i)) BJ.2 (offset i)) C := by
  have hex := exists_response_at_receipt_iff
    (grade := fun d : D.below BJ => D.grade d.1) (c := c)
    (newGrade := newGrade) (ref := ref) (offset := offset) (y := y)
    (γ := δ) (b := max b (preservationBound p γ S))
    hc (fun d => d.2.2) hnew hoff hH hold hV
  refine Iff.trans ?_ hex
  constructor
  · rintro ⟨U, hU, hUH, hb, hr, hcaps, hface, ht⟩
    refine ⟨U, hU, hUH, max_le hb ((preservationBound_le_iff p γ S U).mpr
      ⟨hcaps, hface⟩), hr, ?_⟩
    simpa only [synchronizedCap_target] using ht
  · rintro ⟨U, hU, hUH, hb, hr, ht⟩
    obtain ⟨hcaps, hface⟩ := (preservationBound_le_iff p γ S U).mp
      ((max_le_iff.mp hb).2)
    refine ⟨U, hU, hUH, (max_le_iff.mp hb).1, hr, hcaps, hface, ?_⟩
    simpa only [synchronizedCap_target] using ht

end Row

/-- For an actual donor, its locality is obtained from old-side respect rather
than added as a future-row obligation. -/
theorem synchronizedCap_actual_donor {sem : Semantics D} (c : Cell D)
    {p : D.below (D.cell c) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {I : Type*} (newGrade : I → ℕ) (ref : I → D.below (D.cell c)) (offset : I → ℕ)
    (hnew : ∀ i, newGrade i ≤ D.grade c) (hoff : ∀ i, offset i ≤ D.grade c)
    (y : I → ExtOrd) {U : ExtOrd} (hU : SelfVis (D.grade c) U)
    (hUH : U ≤ p ⟨c, GradedLe.refl _⟩)
    (he : ∀ i, min (y i) U =
      min (extVisibilityReplace (p (ref i)) (D.grade c) (offset i)) U) :
    RespectsSemanticsBelow sem (D.cell c) (synchronizedCap U p) ∧
    TransformsTo (Sum.elim (fun d : D.below (D.cell c) => D.grade d.1) newGrade)
      (row (sem.E c) ref offset (D.grade c))
      (fun d => min (labels (synchronizedCap U p) y d) U) ∧
    ∀ d : D.below (D.cell c), D.grade d.1 = D.grade c → synchronizedCap U p d ≤ U := by
  have hold : TransformsTo (fun d : D.below (D.cell c) => D.grade d.1)
      (sem.E c) (fun d => min (p d) (p ⟨c, GradedLe.refl _⟩)) := by
    refine transformsTo_congr rfl rfl ?_ (hp.locality ⟨c, GradedLe.refl _⟩)
    funext d
    exact congrArg (fun z => min (p z) (p ⟨c, GradedLe.refl _⟩)) (Subtype.ext rfl)
  exact synchronizedCap_local_package (c := ⟨c, GradedLe.refl _⟩) hp rfl
    hnew hoff hold hU hUH he

/-- Add the source-only coded diagonal to the actual donor construction. Its
locality uses the new owner's actual cap, not the old donor's original value. -/
theorem synchronizedCap_actual_owned {sem : Semantics D} (c : Cell D)
    {p : D.below (D.cell c) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {I : Type*} (newGrade : I → ℕ) (ref : I → D.below (D.cell c)) (offset : I → ℕ)
    (hnew : ∀ i, newGrade i ≤ D.grade c) (hoff : ∀ i, offset i ≤ D.grade c)
    (y : I → ExtOrd) {U : ExtOrd} (hU : SelfVis (D.grade c) U)
    (hUH : U ≤ p ⟨c, GradedLe.refl _⟩)
    (he : ∀ i, min (y i) U =
      min (extVisibilityReplace (p (ref i)) (D.grade c) (offset i)) U)
    {n : ℕ} (hcut : ∀ d, row (sem.E c) ref offset (D.grade c) d <
      ofOrd (Ordinal.omega0 * (n : ℕ))) :
    TransformsTo
      (FreeDiagonal.append
        (Sum.elim (fun d : D.below (D.cell c) => D.grade d.1) newGrade) (D.grade c))
      (FreeDiagonal.append (row (sem.E c) ref offset (D.grade c))
        (FreeDiagonal.source (D.grade c) n))
      (fun d => min (FreeDiagonal.append (labels (synchronizedCap U p) y) U d) U) := by
  have hu : U ≤ synchronizedCap U p ⟨c, GradedLe.refl _⟩ := by
    exact le_of_eq ((min_eq_right hUH).symm.trans
      (synchronizedCap_highest p U (⟨c, GradedLe.refl _⟩ : D.below (D.cell c)) rfl).symm)
  apply (owned_transforms_iff
    (grade := fun d : D.below (D.cell c) => D.grade d.1)
    (c := ⟨c, GradedLe.refl _⟩) (p := synchronizedCap U p)
    rfl (fun d => d.2.2) hnew hcut hU hu).mpr
  exact (synchronizedCap_actual_donor c hp newGrade ref offset hnew hoff y hU hUH he).2.1

/-- Fresh highest-grade requesters must also fit under the new owner. Lower-grade
fresh labels remain independent; they need not lie below this cap. -/
theorem synchronizedCap_all_incoming {I : Type*} (newGrade : I → ℕ)
    (p : D.below BJ → ExtOrd) (y : I → ExtOrd) (U : ExtOrd)
    (hfresh : ∀ i, newGrade i = BJ.2 → y i ≤ U) :
    ∀ d, Sum.elim (fun d : D.below BJ => D.grade d.1) newGrade d = BJ.2 →
      labels (synchronizedCap U p) y d ≤ U := by
  intro d hd
  cases d with
  | inl d => exact synchronizedCap_incoming p U d hd
  | inr i => exact hfresh i hd

/-- If the old top-grade owner itself is protected, synchronization cannot lower
its cap. This separates fresh-face lifting from preserving an entire context. -/
theorem synchronizedCap_pinned {p : D.below BJ → ExtOrd} {U : ExtOrd}
    (c : D.below BJ) (hc : D.grade c.1 = BJ.2) (hUH : U ≤ p c)
    (hkeep : synchronizedCap U p c = p c) : U = p c := by
  rw [synchronizedCap_highest p U c hc, min_eq_right hUH] at hkeep
  exact hkeep

end VaughtConjecture.Knight.OrbitCap
