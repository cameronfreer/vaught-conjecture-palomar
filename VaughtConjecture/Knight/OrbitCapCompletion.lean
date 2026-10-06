/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReferenceOrbitRow

/-! # Exact controller-cap completion for fixed orbit rows

Old and fresh labels are fixed independently. Only the new controller cap may change.
At a visible controller cap, each orbit equation is equality of two capped values.
The least visible cap preserving the old controller's external receipt and a demanded
lower bound is explicit. Testing the equations at that cap decides existence at any
smaller-than-old cap. The external cap itself need not be visible at the row's grade.

The row theorem constructs a faithful witness, including clause 5, from the donor's
actual locality. It does not construct a scheme, availability, or simultaneous localities
at other controllers. In particular, changing a prescribed controller label is not licensed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.OrbitCap

open Transform Value ExtOrd

/-- Visibility replacement at the grade is the least visible value above its input. -/
theorem ceiling_visible (K : ℕ) (x : ExtOrd) :
    SelfVis K (extVisibilityReplace x K K) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact extVisibilityReplace_bot K K
  · exact extVisibilityReplace_top K K
  · rw [extVisibilityReplace_ofOrd, selfVis_ofOrd_iff, finitePart_visibilityReplace]
    split_ifs <;> omega

/-- Least controller cap meeting a lower bound and the old external capped value. -/
noncomputable def requiredCap (K : ℕ) (H γ b : ExtOrd) : ExtOrd :=
  extVisibilityReplace (max b (min H γ)) K K

theorem requiredCap_visible (K : ℕ) (H γ b : ExtOrd) :
    SelfVis K (requiredCap K H γ b) := ceiling_visible _ _

theorem bound_le_requiredCap (K : ℕ) (H γ b : ExtOrd) : b ≤ requiredCap K H γ b :=
  (le_max_left _ _).trans (le_extVisibilityReplace_self _ _)

theorem receipt_le_requiredCap (K : ℕ) (H γ b : ExtOrd) :
    min H γ ≤ requiredCap K H γ b :=
  (le_max_right _ _).trans (le_extVisibilityReplace_self _ _)

theorem requiredCap_le {K : ℕ} {H γ b U : ExtOrd} (hU : SelfVis K U)
    (hb : b ≤ U) (hr : min H γ ≤ U) : requiredCap K H γ b ≤ U :=
  extVisibilityReplace_le_of_le_selfVis le_rfl hU (max_le hb hr)

theorem requiredCap_le_old {K : ℕ} {H γ b : ExtOrd}
    (hH : SelfVis K H) (hb : b ≤ H) : requiredCap K H γ b ≤ H :=
  requiredCap_le hH hb (min_le_left _ _)

/-- The original external cap is retained, not raised to a visible replacement. -/
theorem requiredCap_receipt {K : ℕ} {H γ b : ExtOrd}
    (hH : SelfVis K H) (hb : b ≤ H) :
    min (requiredCap K H γ b) γ = min H γ := by
  apply le_antisymm (min_le_min_right γ (requiredCap_le_old hH hb))
  exact le_min (receipt_le_requiredCap _ _ _ _) (min_le_right _ _)

theorem requiredCap_minimal {K : ℕ} {H γ b U : ExtOrd}
    (hU : SelfVis K U) (hb : b ≤ U) (hr : min U γ = min H γ) :
    requiredCap K H γ b ≤ U :=
  requiredCap_le hU hb (by rw [← hr]; exact min_le_left _ _)

/-- A demanded lower bound can exceed the ambient controller when its old value
already reaches the external cap. This is the exact condition, not `b ≤ H`. -/
theorem requiredCap_receipt_iff {K : ℕ} {H γ b : ExtOrd} (hH : SelfVis K H) :
    min (requiredCap K H γ b) γ = min H γ ↔ min b γ ≤ min H γ := by
  constructor
  · intro h
    rw [← h]
    exact min_le_min_right γ (bound_le_requiredCap _ _ _ _)
  · intro h
    by_cases hγH : γ ≤ H
    · rw [min_eq_right hγH]
      exact min_eq_right (by
        simpa only [min_eq_right hγH] using receipt_le_requiredCap K H γ b)
    · have hb : b ≤ H := by
        rw [min_eq_left (le_of_not_ge hγH)] at h
        exact (min_le_iff.mp h).resolve_right hγH
      exact requiredCap_receipt hH hb

/-- A mismatched pair permits exactly the caps below both values. -/
theorem cap_eq_iff {x y U : ExtOrd} :
    min x U = min y U ↔ x = y ∨ U ≤ min x y := by
  constructor
  · intro h
    by_cases he : x = y
    · exact Or.inl he
    · right
      rcases lt_or_gt_of_ne he with hxy | hyx
      · have hU : U ≤ x := by
          by_contra hn
          have hxU := lt_of_not_ge hn
          rw [min_eq_left hxU.le] at h
          exact (not_lt_of_ge h.ge) (lt_min hxy hxU)
        exact le_min hU (hU.trans hxy.le)
      · have hU : U ≤ y := by
          by_contra hn
          have hyU := lt_of_not_ge hn
          rw [min_eq_left hyU.le] at h
          exact (not_lt_of_ge h.le) (lt_min hyx hyU)
        exact le_min (hU.trans hyx.le) hU
  · rintro (rfl | h)
    · rfl
    · rw [min_eq_right (h.trans (min_le_left _ _)),
        min_eq_right (h.trans (min_le_right _ _))]

theorem cap_eq_down {x y U V : ExtOrd} (hUV : U ≤ V)
    (h : min x V = min y V) : min x U = min y U := by
  have hh := congrArg (fun z => min z U) h
  simpa only [min_assoc, min_eq_right hUV] using hh

/-- Replacement commutes with capping at a controller-visible value. -/
theorem replace_min {K i : ℕ} {U : ExtOrd} (hi : i ≤ K) (hU : SelfVis K U)
    (x : ExtOrd) :
    extVisibilityReplace (min x U) K i = min (extVisibilityReplace x K i) U := by
  have hm : Monotone (fun z => extVisibilityReplace z K i) := fun _ _ h => evr_mono h hi
  rw [hm.map_min, evr_eq_self_of_selfVis hU]

/-- A simultaneous scalar feasibility test, with arbitrary many fixed requests.
No finiteness, visibility of the external cap, or equality of fresh labels is assumed. -/
theorem exists_cap_iff {I : Type*} (x y : I → ExtOrd) {K : ℕ} {H γ b : ExtOrd}
    (hH : SelfVis K H) (hb : b ≤ H) :
    (∃ U, SelfVis K U ∧ U ≤ H ∧ b ≤ U ∧ min U γ = min H γ ∧
      ∀ i, min (x i) U = min (y i) U) ↔
    ∀ i, min (x i) (requiredCap K H γ b) = min (y i) (requiredCap K H γ b) := by
  constructor
  · rintro ⟨U, hU, _, hbU, hr, he⟩ i
    exact cap_eq_down (requiredCap_minimal hU hbU hr) (he i)
  · intro he
    exact ⟨requiredCap K H γ b, requiredCap_visible _ _ _ _, requiredCap_le_old hH hb,
      bound_le_requiredCap _ _ _ _, requiredCap_receipt hH hb, he⟩

section Row

variable {D I : Type*} (grade : D → ℕ) (newGrade : I → ℕ) (E : D → ExtOrd)
  (ref : I → D) (offset : I → ℕ) (K : ℕ)

/-- Literal old sources with one visibility-orbit column per new occurrence. -/
noncomputable def row : D ⊕ I → ExtOrd :=
  Sum.elim E (fun i => extVisibilityReplace (E (ref i)) K (offset i))

/-- Fixed old labels and independently prescribed fresh labels. -/
def labels (p : D → ExtOrd) (y : I → ExtOrd) : D ⊕ I → ExtOrd := Sum.elim p y

variable {grade newGrade E ref offset K} {p : D → ExtOrd} {y : I → ExtOrd}
  {c : D} (hc : grade c = K) (hgrade : ∀ d, grade d ≤ K)
  (hnew : ∀ i, newGrade i ≤ K) (hoff : ∀ i, offset i ≤ K)

include hc hgrade hnew hoff

/-- The orbit equations are sufficient at a fixed cap. The old locality is used
at its own controller and clipped explicitly, never composed with another witness. -/
theorem transforms_of_equations (hH : SelfVis K (p c))
    (hold : TransformsTo grade E (fun d => min (p d) (p c)))
    {U : ExtOrd} (hU : SelfVis K U) (hUH : U ≤ p c)
    (he : ∀ i, min (y i) U = min (extVisibilityReplace (p (ref i)) K (offset i)) U) :
    TransformsTo (Sum.elim grade newGrade) (row E ref offset K)
      (fun d => min (labels p y d) U) := by
  obtain ⟨τ, hτ, _, hread⟩ := exists_bounded_exact_capped_witness
    (c := c) (fun d => by simpa only [hc] using hgrade d) (hc.symm ▸ hH) hold
  rw [hc] at hτ
  have hclip := FreeDiagonal.clip_witness hτ hU
  have hr (d : D) : min (τ (E d)) U = min (p d) U := by
    rw [hread, min_assoc, min_eq_right hUH]
  apply hclip.transformsTo
  intro d
  cases d with
  | inl d =>
    change min (p d) U = min (min (τ (E d)) U) (gTop K (grade d))
    rw [gTop_of_le (hgrade d), min_top_right, hr]
  | inr i =>
    change min (y i) U = min
      (min (τ (extVisibilityReplace (E (ref i)) K (offset i))) U)
      (gTop K (newGrade i))
    rw [gTop_of_le (hnew i), min_top_right]
    have hh := hclip.clause5 (E (ref i)) K
      (by rw [gTop_of_le le_rfl]; exact le_top) (offset i) (hoff i)
    rw [hh, hr, replace_min (hoff i) hU]
    exact he i

/-- Conversely every faithful response satisfies the same equations, regardless
of which shifter supplied it. The old owner is an actual maximal-grade occurrence. -/
theorem equations_of_transforms {U : ExtOrd} (hU : SelfVis K U) (hUH : U ≤ p c)
    (h : TransformsTo (Sum.elim grade newGrade) (row E ref offset K)
      (fun d => min (labels p y d) U)) :
    ∀ i, min (y i) U = min (extVisibilityReplace (p (ref i)) K (offset i)) U := by
  let q : D ⊕ I → ExtOrd := fun d => min (labels p y d) U
  have howner : q (Sum.inl c) = U := min_eq_right hUH
  have hmax : ∀ d, Sum.elim grade newGrade d ≤ Sum.elim grade newGrade (Sum.inl c) := by
    intro d
    cases d with
    | inl d => simpa only [Sum.elim_inl, hc] using hgrade d
    | inr i => simpa only [Sum.elim_inl, Sum.elim_inr, hc] using hnew i
  have hh : TransformsTo (Sum.elim grade newGrade) (row E ref offset K)
      (fun d => min (q d) (q (Sum.inl c))) := by
    simpa only [howner, q, min_assoc, min_self] using h
  obtain ⟨τ, hτ, _, hread⟩ := exists_bounded_exact_capped_witness
    hmax (by change SelfVis (grade c) (q (Sum.inl c)); rw [hc, howner]; exact hU) hh
  change Witness (gTop (grade c)) τ at hτ
  rw [hc] at hτ
  have hr (d : D ⊕ I) : τ (row E ref offset K d) = min (labels p y d) U := by
    simpa only [howner, q, min_assoc, min_self] using hread d
  intro i
  have hn := hr (Sum.inr i)
  have ho := hr (Sum.inl (ref i))
  change τ (extVisibilityReplace (E (ref i)) K (offset i)) = min (y i) U at hn
  change τ (E (ref i)) = min (p (ref i)) U at ho
  rw [hτ.clause5 _ K (by rw [gTop_of_le le_rfl]; exact le_top) _ (hoff i), ho,
    replace_min (hoff i) hU] at hn
  exact hn.symm

/-- Exact feasibility for a fixed row, preserving all face labels and the original
external capped controller value. When feasible, `requiredCap` constructs a witness. -/
theorem exists_response_iff (hH : SelfVis K (p c))
    (hold : TransformsTo grade E (fun d => min (p d) (p c)))
    {γ b : ExtOrd} (hb : b ≤ p c) :
    (∃ U, SelfVis K U ∧ U ≤ p c ∧ b ≤ U ∧ min U γ = min (p c) γ ∧
      TransformsTo (Sum.elim grade newGrade) (row E ref offset K)
        (fun d => min (labels p y d) U)) ↔
    ∀ i, min (y i) (requiredCap K (p c) γ b) =
      min (extVisibilityReplace (p (ref i)) K (offset i)) (requiredCap K (p c) γ b) := by
  constructor
  · rintro ⟨U, hU, hUH, hbU, hr, ht⟩ i
    exact cap_eq_down (requiredCap_minimal hU hbU hr)
      (equations_of_transforms hc hgrade hnew hoff hU hUH ht i)
  · intro he
    exact ⟨requiredCap K (p c) γ b, requiredCap_visible _ _ _ _,
      requiredCap_le_old hH hb, bound_le_requiredCap _ _ _ _, requiredCap_receipt hH hb,
      transforms_of_equations hc hgrade hnew hoff hH hold
        (requiredCap_visible _ _ _ _) (requiredCap_le_old hH hb) he⟩

/-- The ambient value of a newly added owner need not be the old donor's label.
This version keeps those values independent and characterizes every missing scalar bound. -/
theorem exists_response_at_receipt_iff (hH : SelfVis K (p c))
    (hold : TransformsTo grade E (fun d => min (p d) (p c)))
    {V γ b : ExtOrd} (hV : SelfVis K V) :
    (∃ U, SelfVis K U ∧ U ≤ p c ∧ b ≤ U ∧ min U γ = min V γ ∧
      TransformsTo (Sum.elim grade newGrade) (row E ref offset K)
        (fun d => min (labels p y d) U)) ↔
    requiredCap K V γ b ≤ p c ∧ min b γ ≤ min V γ ∧
      ∀ i, min (y i) (requiredCap K V γ b) =
        min (extVisibilityReplace (p (ref i)) K (offset i)) (requiredCap K V γ b) := by
  constructor
  · rintro ⟨U, hU, hUH, hbU, hr, ht⟩
    have hCU := requiredCap_minimal hU hbU hr
    refine ⟨hCU.trans hUH, ?_, ?_⟩
    · rw [← hr]
      exact min_le_min_right γ hbU
    · intro i
      exact cap_eq_down hCU (equations_of_transforms hc hgrade hnew hoff hU hUH ht i)
  · rintro ⟨hCH, hr, he⟩
    exact ⟨requiredCap K V γ b, requiredCap_visible _ _ _ _, hCH,
      bound_le_requiredCap _ _ _ _, (requiredCap_receipt_iff hV).mpr hr,
      transforms_of_equations hc hgrade hnew hoff hH hold
        (requiredCap_visible _ _ _ _) hCH he⟩

end Row

end VaughtConjecture.Knight.OrbitCap
