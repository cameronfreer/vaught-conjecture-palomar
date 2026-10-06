/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.VisibleOrderInterpolation
public import VaughtConjecture.Knight.FullRowCoverage

/-! # A finite least-lift test at grade one

For a fixed full controller, propagate the prescribed values and the ambient's
capped values upward along source order. The maximum of these lower bounds is
the least order-compatible candidate. Check only its pinned inactive values,
protected values, and bottom-source reads. At a nonbottom visible cap, consistency
and the interpolation theorem make a passing candidate a genuine lawful lift.

Taking the finite disjunction over full controllers is exact. The result is not
a proof that every input passes. No mixed-grade claim or general transitivity
of faithful transformations is used.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

namespace Propagation

section Order

variable {Y X S L : Type*} [Fintype Y] [Fintype X]
  [LinearOrder S] [LinearOrder L] [OrderBot L]

/-- Least source-monotone candidate above the two sets of required lower bounds.
It is computed by finite maxima, not an iteration to an unspecified fixed point. -/
def close (E : Y → S) (embed : X → Y) (p : X → L) (q : Y → L) (γ : L) (d : Y) : L :=
  max (Finset.univ.sup (fun e => if E e ≤ E d then min (q e) γ else ⊥))
    (Finset.univ.sup (fun x => if E (embed x) ≤ E d then p x else ⊥))

theorem cap_le_close (E : Y → S) (embed : X → Y) (p : X → L) (q : Y → L)
    (γ : L) (d : Y) : min (q d) γ ≤ close E embed p q γ d := by
  apply le_trans _ (le_max_left _ _)
  apply Finset.le_sup_of_le (Finset.mem_univ d)
  rw [ite_eq_left (le_refl (E d))]

theorem prescribed_le_close (E : Y → S) (embed : X → Y) (p : X → L) (q : Y → L)
    (γ : L) (x : X) : p x ≤ close E embed p q γ (embed x) := by
  apply le_trans _ (le_max_right _ _)
  apply Finset.le_sup_of_le (Finset.mem_univ x)
  rw [ite_eq_left (le_refl (E (embed x)))]

theorem close_order (E : Y → S) (embed : X → Y) (p : X → L) (q : Y → L)
    (γ : L) {d e : Y} (hde : E d ≤ E e) : close E embed p q γ d ≤ close E embed p q γ e := by
  apply max_le_max
  · apply Finset.sup_le
    intro a _
    split_ifs with ha
    · apply Finset.le_sup_of_le (Finset.mem_univ a)
      rw [ite_eq_left (ha.trans hde)]
    · exact bot_le
  · apply Finset.sup_le
    intro x _
    split_ifs with hx
    · apply Finset.le_sup_of_le (Finset.mem_univ x)
      rw [ite_eq_left (hx.trans hde)]
    · exact bot_le

/-- Least among ALL source-order-compatible assignments meeting the required
lower bounds, not just among assignments made by this formula. -/
theorem close_le {E : Y → S} {embed : X → Y} {p : X → L} {q : Y → L} {γ : L}
    {r : Y → L} (hord : ∀ d e, E d ≤ E e → r d ≤ r e)
    (hcap : ∀ d, min (q d) γ ≤ r d) (hface : ∀ x, p x ≤ r (embed x)) (d : Y) :
    close E embed p q γ d ≤ r d := by
  apply max_le
  · apply Finset.sup_le
    intro e _
    split_ifs with he
    · exact (hcap e).trans (hord e d he)
    · exact bot_le
  · apply Finset.sup_le
    intro x _
    split_ifs with hx
    · exact (hface x).trans (hord _ d hx)
    · exact bot_le

/-- The output uses only bottom, an ambient capped value, or a prescribed value.
In particular, no new ordinal value or palette generator is introduced. -/
theorem close_value (E : Y → S) (embed : X → Y) (p : X → L) (q : Y → L)
    (γ : L) (d : Y) :
    close E embed p q γ d = ⊥ ∨
      (∃ e, close E embed p q γ d = min (q e) γ) ∨
      ∃ x, close E embed p q γ d = p x := by
  let P : L → Prop := fun v => v = ⊥ ∨ (∃ e, v = min (q e) γ) ∨ ∃ x, v = p x
  have hb : P ⊥ := Or.inl rfl
  have hm : ∀ a, P a → ∀ b, P b → P (max a b) := by
    intro a ha b hb
    rcases le_total a b with h | h
    · simpa only [max_eq_right h] using hb
    · simpa only [max_eq_left h] using ha
  apply hm
  · apply Finset.sup_induction (p := P) hb hm
    intro e _
    split_ifs
    · exact Or.inr (Or.inl ⟨e, rfl⟩)
    · exact hb
  · apply Finset.sup_induction (p := P) hb hm
    intro x _
    split_ifs
    · exact Or.inr (Or.inr ⟨x, rfl⟩)
    · exact hb

variable [OrderBot S]

/-- The remaining upper bounds after lower-bound propagation. -/
def Check (E : Y → S) (embed : X → Y) (p : X → L) (q : Y → L) (γ : L) : Prop :=
  (∀ d, q d < γ → close E embed p q γ d ≤ q d) ∧
  (∀ x, close E embed p q γ (embed x) ≤ p x) ∧
  (∀ d, E d = ⊥ → close E embed p q γ d = ⊥)

/-- An exact finite order test. The conclusion of the reverse direction uses
the displayed closure itself, so no search over output labels is needed. -/
theorem check_iff {E : Y → S} {embed : X → Y} {p : X → L} {q : Y → L} {γ : L} :
    Check E embed p q γ ↔
      ∃ r : Y → L, (∀ d e, E d ≤ E e → r d ≤ r e) ∧
        (∀ d, E d = ⊥ → r d = ⊥) ∧
        (∀ d, min (r d) γ = min (q d) γ) ∧ (∀ x, r (embed x) = p x) := by
  constructor
  · rintro ⟨hinactive, hprotected, hbot⟩
    refine ⟨close E embed p q γ, fun _ _ => close_order E embed p q γ, hbot, ?_, ?_⟩
    · intro d
      apply (cap_eq_iff_profile _ _ _).mpr
      constructor
      · intro hd
        apply le_antisymm (hinactive d hd)
        have h := cap_le_close E embed p q γ d
        rwa [min_eq_left hd.le] at h
      · intro hd
        have h := cap_le_close E embed p q γ d
        rwa [min_eq_right hd] at h
    · intro x
      exact le_antisymm (hprotected x) (prescribed_le_close E embed p q γ x)
  · rintro ⟨r, hord, hbot, hcap, hface⟩
    have hleast := close_le hord
      (fun d => (hcap d) ▸ min_le_left (r d) γ) (fun x => (hface x).ge)
    refine ⟨?_, fun x => (hleast (embed x)).trans_eq (hface x), ?_⟩
    · intro d hd
      exact (hleast d).trans_eq (((cap_eq_iff_profile _ _ _).mp (hcap d)).1 hd)
    · intro d hd
      exact le_bot_iff.mp ((hleast d).trans_eq (hbot d hd))

end Order

section Visibility

variable {Y X S : Type*} [Fintype Y] [Fintype X] [LinearOrder S]

private theorem visible_max {a b : ExtOrd} {K : ℕ}
    (ha : SelfVis K a) (hb : SelfVis K b) : SelfVis K (max a b) := by
  rcases le_total a b with h | h
  · simpa only [max_eq_right h] using hb
  · simpa only [max_eq_left h] using ha

/-- No visibility repairs or extra palette generators are required: finite
maxima of the input's visible lower bounds are visible at the same grade. -/
theorem close_visible (E : Y → S) (embed : X → Y)
    {p : X → ExtOrd} {q : Y → ExtOrd} {γ : ExtOrd} {K : ℕ}
    (hp : ∀ x, SelfVis K (p x)) (hq : ∀ d, SelfVis K (q d)) (hγ : SelfVis K γ) (d : Y) :
    SelfVis K (close E embed p q γ d) := by
  apply visible_max
  · apply Finset.sup_induction (p := SelfVis K) (extVisibilityReplace_bot _ _)
      (fun _ ha _ hb => visible_max ha hb)
    intro e _
    split_ifs
    · exact selfVis_min (hq e) hγ
    · exact extVisibilityReplace_bot _ _
  · apply Finset.sup_induction (p := SelfVis K) (extVisibilityReplace_bot _ _)
      (fun _ ha _ hb => visible_max ha hb)
    intro x _
    split_ifs
    · exact hp x
    · exact extVisibilityReplace_bot _ _

end Visibility

end Propagation

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

noncomputable local instance : Fintype (D.below BJ) := Fintype.ofFinite _

/-- A passing controller test constructs its least source-order-compatible
lawful lift. No other section, completion, or faithful witness is assumed. -/
theorem least_lift_of_check (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    {X : Type*} [Fintype X] {embed : X → D.below BJ} {p : X → ExtOrd}
    {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) (hp : ∀ x, SelfVis BJ.2 (p x))
    (hγvis : SelfVis BJ.2 γ) (hγ : γ ≠ ⊥) (c : Controller D BJ)
    (hcheck : Propagation.Check (c.row sem) embed p q γ) :
    RespectsSemanticsBelow sem BJ (Propagation.close (c.row sem) embed p q γ) ∧
      Boundary embed p q γ (Propagation.close (c.row sem) embed p q γ) := by
  have hvq : ∀ d, SelfVis BJ.2 (q d) := by
    intro d
    have hh : SelfVis (D.grade d.1) (q d) := (hq.orderly d).symm
    rwa [grade_eq_one hgrade d, ← hgrade] at hh
  have hboundary : Boundary embed p q γ (Propagation.close (c.row sem) embed p q γ) := by
    constructor
    · intro d
      apply (cap_eq_iff_profile _ _ _).mpr
      constructor
      · intro hd
        apply le_antisymm (hcheck.1 d hd)
        have hh := Propagation.cap_le_close (c.row sem) embed p q γ d
        rwa [min_eq_left hd.le] at hh
      · intro hd
        have hh := Propagation.cap_le_close (c.row sem) embed p q γ d
        rwa [min_eq_right hd] at hh
    · intro x
      exact le_antisymm (hcheck.2.1 x)
        (Propagation.prescribed_le_close (c.row sem) embed p q γ x)
  have hE : ∀ d, SelfVis BJ.2 (c.row sem d) := by
    intro d
    have hh : SelfVis (D.grade d.1) (c.row sem d) := ((c.row_respects hc).orderly d).symm
    rwa [grade_eq_one hgrade d, ← hgrade] at hh
  let r := Propagation.close (c.row sem) embed p q γ
  have hord : ∀ d e, c.row sem d ≤ c.row sem e → r d ≤ r e :=
    fun _ _ => Propagation.close_order _ _ _ _ _
  have hbot : ∀ d, c.row sem d = ⊥ → r d = ⊥ := hcheck.2.2
  have hread := funext (orderInterpolate_read hord hbot)
  have hmap := orderInterpolate_bounded hE
    (Propagation.close_visible (c.row sem) embed hp hvq hγvis)
  have hr := map_respects_of_positive_cap_agreement (c.row_respects hc) hq
    (fun d => d.2.2) hmap hγ
    (fun d => by rw [orderInterpolate_read hord hbot]; exact hboundary.1 d)
  have hfinal : RespectsSemanticsBelow sem BJ r := hread ▸ hr
  exact ⟨hfinal, hboundary⟩

/-- Exact grade-one lift test at a permitted positive cap: enumerate the full
controllers and check each finite closure. No output-label or shifter search
remains. A failed particular controller is not failure of the disjunction. -/
theorem lift_iff_exists_check (hc : sem.IsConsistent) (hgrade : BJ.2 = 1)
    (c₀ : Controller D BJ) {X : Type*} [Fintype X] {embed : X → D.below BJ}
    {p : X → ExtOrd} {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) (hp : ∀ x, SelfVis BJ.2 (p x))
    (hγvis : SelfVis BJ.2 γ) (hγ : γ ≠ ⊥) :
    HasLift (sem := sem) embed p q γ ↔
      ∃ c : Controller D BJ, Propagation.Check (c.row sem) embed p q γ := by
  constructor
  · intro h
    obtain ⟨c, r, _, hord, hbot, hcap, hface⟩ := orderQuery_of_lift hgrade c₀ h
    exact ⟨c, Propagation.check_iff.mpr ⟨r, hord, hbot, hcap, hface⟩⟩
  · rintro ⟨c, hcheck⟩
    exact ⟨_, least_lift_of_check hc hgrade hq hp hγvis hγ c hcheck⟩

end VaughtConjecture.Knight.FullRowLifting
