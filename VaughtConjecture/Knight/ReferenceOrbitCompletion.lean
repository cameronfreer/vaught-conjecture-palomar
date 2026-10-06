/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrbitCapCompletion

/-! # A fixed owned donor row with independently prescribed fresh labels

The source-only cutoff and the new diagonal are chosen before any new labels or caps.
All old and fresh labels are kept literally in the completed vector; only its new owner
value is chosen. Locality reads that vector at the actual owner's cap.

This is a row completion, not a respecting labelling of an enlarged scheme. In particular,
availability may demand a larger owner value than the least cap used here. Such a lower
bound must be supplied as `b`; it is not dropped by the construction.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

namespace OrbitCap

variable {D I : Type*} {grade : D → ℕ} {newGrade : I → ℕ} {E : D → ExtOrd}
  {ref : I → D} {offset : I → ℕ} {K : ℕ} {p : D → ExtOrd} {y : I → ExtOrd} {c : D}

/-- At a fixed new owner, the owned row and its prefix have equivalent locality
for the chosen capped vector. The reverse direction uses literal restriction. -/
theorem owned_transforms_iff (hc : grade c = K) (hgrade : ∀ d, grade d ≤ K)
    (hnew : ∀ i, newGrade i ≤ K) {n : ℕ}
    (hcut : ∀ d, row E ref offset K d < ofOrd (Ordinal.omega0 * (n : Ordinal)))
    {U : ExtOrd} (hU : SelfVis K U) (hUH : U ≤ p c) :
    TransformsTo (FreeDiagonal.append (Sum.elim grade newGrade) K)
        (FreeDiagonal.append (row E ref offset K) (FreeDiagonal.source K n))
        (fun d => min (FreeDiagonal.append (labels p y) U d) U) ↔
      TransformsTo (Sum.elim grade newGrade) (row E ref offset K)
        (fun d => min (labels p y d) U) := by
  constructor
  · intro h
    exact h.reindex some
  · intro h
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
    have hs := FreeDiagonal.transforms_append hmax
      (by change SelfVis (grade c) (q (Sum.inl c)); rw [hc, howner]; exact hU)
      hh hcut (hc.symm ▸ hU) (by rw [howner])
    change TransformsTo (FreeDiagonal.append (Sum.elim grade newGrade) (grade c))
      (FreeDiagonal.append (row E ref offset K) (FreeDiagonal.source (grade c) n))
      (FreeDiagonal.append (fun d => min (q d) (q (Sum.inl c))) U) at hs
    rw [hc] at hs
    convert hs using 1
    funext d
    cases d <;> simp only [FreeDiagonal.append, howner, q, min_assoc, min_self]

/-- Exact completion criterion at a genuine fresh diagonal, not a phantom cap.
The scalar test is necessary for all witnesses and sufficient by an explicit one. -/
theorem exists_owned_response_iff (hc : grade c = K) (hgrade : ∀ d, grade d ≤ K)
    (hnew : ∀ i, newGrade i ≤ K) (hoff : ∀ i, offset i ≤ K) {n : ℕ}
    (hcut : ∀ d, row E ref offset K d < ofOrd (Ordinal.omega0 * (n : Ordinal)))
    (hH : SelfVis K (p c))
    (hold : TransformsTo grade E (fun d => min (p d) (p c)))
    {V γ b : ExtOrd} (hV : SelfVis K V) :
    (∃ U, SelfVis K U ∧ U ≤ p c ∧ b ≤ U ∧ min U γ = min V γ ∧
      TransformsTo (FreeDiagonal.append (Sum.elim grade newGrade) K)
        (FreeDiagonal.append (row E ref offset K) (FreeDiagonal.source K n))
        (fun d => min (FreeDiagonal.append (labels p y) U d) U)) ↔
    requiredCap K V γ b ≤ p c ∧ min b γ ≤ min V γ ∧
      ∀ i, min (y i) (requiredCap K V γ b) =
        min (extVisibilityReplace (p (ref i)) K (offset i)) (requiredCap K V γ b) := by
  rw [← exists_response_at_receipt_iff hc hgrade hnew hoff hH hold hV]
  constructor <;> rintro ⟨U, hU, hUH, hbU, hr, ht⟩
  · exact ⟨U, hU, hUH, hbU, hr, (owned_transforms_iff hc hgrade hnew hcut hU hUH).mp ht⟩
  · exact ⟨U, hU, hUH, hbU, hr, (owned_transforms_iff hc hgrade hnew hcut hU hUH).mpr ht⟩

/-- If availability requires the old donor's full label, the minimal feasible
cap is that label. Lowering a controller cannot evade this requirement. -/
theorem requiredCap_of_domination {K : ℕ} {H γ : ExtOrd} (hH : SelfVis K H) :
    requiredCap K H γ H = H := by
  apply le_antisymm (requiredCap_le_old hH le_rfl)
  exact bound_le_requiredCap _ _ _ _

end OrbitCap

namespace ReferenceContext.FullController

variable {M : Type*} {α : LimitStage} {R : KnightRealization α M}
  {n : ℕ} {t : Fin n ↪ M} {reqs : List BlockRequest}
  {C : ReferenceContext R t reqs} (F : C.FullController)
  (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block)

/-- A source-only choice for the actual reference row. Every later old input and
independent fresh prescription uses this same row and this same diagonal. -/
theorem exists_owned_completion_test (newGrade : Fin reqs.length → ℕ)
    (hgrade : ∀ i, newGrade i ≤ reqs[i.val].offset) :
    ∃ m : ℕ, 0 < m ∧
      (∀ d, IsCodedLabel C.N
        (FreeDiagonal.append (F.source hblocks) (FreeDiagonal.source C.N m) d)) ∧
      ∀ (p : F.Old → ExtOrd) (y : Fin reqs.length → ExtOrd),
        SelfVis C.N (p F.owner) →
        TransformsTo (fun d : F.Old => C.p₀.scheme.scheme.grade d.1)
          (C.p₀.scheme.rows.E F.cell) (fun d => min (p d) (p F.owner)) →
        ∀ V γ b, SelfVis C.N V →
          ((∃ U, SelfVis C.N U ∧ U ≤ p F.owner ∧ b ≤ U ∧ min U γ = min V γ ∧
            TransformsTo (FreeDiagonal.append
              (Sum.elim (fun d : F.Old => C.p₀.scheme.scheme.grade d.1) newGrade) C.N)
              (FreeDiagonal.append (F.source hblocks) (FreeDiagonal.source C.N m))
              (fun d => min (FreeDiagonal.append (Sum.elim p y) U d) U)) ↔
          OrbitCap.requiredCap C.N V γ b ≤ p F.owner ∧ min b γ ≤ min V γ ∧
            ∀ i, min (y i) (OrbitCap.requiredCap C.N V γ b) =
              min (extVisibilityReplace (p (F.reference hblocks i)) C.N reqs[i.val].offset)
                (OrbitCap.requiredCap C.N V γ b)) := by
  obtain ⟨m, hm, hcut⟩ := FreeDiagonal.exists_limit_above (F.source hblocks)
    (F.source_coded hblocks)
  refine ⟨m, hm, ?_, ?_⟩
  · rintro (_ | d)
    · exact FreeDiagonal.source_coded _ _
    · exact F.source_coded hblocks d
  · intro p y hp hloc V γ b hV
    exact OrbitCap.exists_owned_response_iff
      (grade := fun d : F.Old => C.p₀.scheme.scheme.grade d.1) (c := F.owner)
      (ref := F.reference hblocks) (offset := fun i => reqs[i.val].offset)
      F.grade_eq F.grade_le
      (fun i => (hgrade i).trans (C.offset_lt _ (List.getElem_mem i.isLt)).le)
      (fun i => (C.offset_lt _ (List.getElem_mem i.isLt)).le) hcut hp hloc hV

end ReferenceContext.FullController

end VaughtConjecture.Knight
