/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProvisionalLift
public import VaughtConjecture.Knight.FiniteBandReadback

/-! # The provisional vector is the least lawful lift

Finite band readback identifies every competing value below the reduct's top-grade
threshold. Above that threshold the provisional bound gives leastness. The minimum
is attained simultaneously by the lawful provisional lift on the unchanged scheme.

These are finite-type statements, with no model or receiving hypothesis. The finite
supplier excludes the `ExpansionUniqueness` and `ProvisionalRatchet` import
cones. Model definitions remain upstream through `Terminal`. No closure under
pointwise minima is asserted.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.StageType

open TypeTower Value ExtOrd
open CellScheme.restrictFace (toCell)

variable {α β : Ordinal.{0}} {n : ℕ}

/-- Every label of a higher type equals its reduct's provisional value, or is at
least the reduct's top-grade threshold. The higher stage need only be above `α`. -/
theorem label_eq_provisional_or_threshold_le (hα : Order.IsSuccLimit α) (hαβ : α ≤ β)
    (q : S β n) (d : Cell q.scheme.scheme) :
    q.label d = (reduceType hα hαβ q).someProvisionalValue d ∨
      ofOrd (α + (reduceType hα hαβ q).topGrade) ≤ q.label d := by
  let p := reduceType hα hαβ q
  by_cases htop : p.label d = ⊤
  · by_cases hlarge : ofOrd (α + p.topGrade) ≤ q.label d
    · exact Or.inr hlarge
    · have hge : ofOrd α ≤ q.label d := truncExt_eq_top_iff.mp htop
      have hlt : q.label d < ofOrd (α + Ordinal.omega0) :=
        (lt_of_not_ge hlarge).trans (ofOrd_lt_ofOrd.mpr
          ((add_lt_add_iff_left α).mpr (Ordinal.natCast_lt_omega0 p.topGrade)))
      obtain ⟨i, hi⟩ := exists_nat_of_mem_band hge hlt
      have hiK : i < p.topGrade := by
        have h := lt_of_not_ge hlarge
        rw [hi, ofOrd_lt_ofOrd, add_lt_add_iff_left] at h
        exact_mod_cast h
      left
      exact hi.trans (isProvisionalValue_iff.mp
        (isProvisionalValue_band_of_expansion hα hαβ d hi hiK))
  · have hlt : q.label d < ofOrd α := lt_of_not_ge
      (fun h => htop (truncExt_eq_top_of_ge h))
    left
    rw [someProvisionalValue_of_ne_top htop]
    exact (truncExt_id_of_lt hlt).symm

/-- The provisional value is a lower bound for every lawful higher lift of its
literal reduct, coordinate by coordinate in the common scalar value space. -/
theorem provisional_reduct_le_label (hα : Order.IsSuccLimit α) (hαβ : α ≤ β)
    (q : S β n) (d : Cell q.scheme.scheme) :
    (reduceType hα hαβ q).someProvisionalValue d ≤ q.label d := by
  rcases label_eq_provisional_or_threshold_le hα hαβ q d with h | h
  · exact h.ge
  · exact (someProvisionalValue_le _ _).trans h

/-- Fixed-scheme form: every lawful bounded vector reducing to `p` dominates its
provisional vector. Rows and cells are literally those of `p`. -/
theorem provisional_le_of_lawful_lift (p : S α n) (hα : Order.IsSuccLimit α)
    (hαβ : α ≤ β) (v : Cell p.scheme.scheme → ExtOrd)
    (hbound : ∀ d, v d < ofOrd β ∨ v d = ⊤)
    (hlawful : RespectsSemantics p.scheme.rows v)
    (hreduce : ∀ d, truncExt α (v d) = p.label d) :
    ∀ d, p.someProvisionalValue d ≤ v d := by
  let q : S β n := ⟨p.scheme, v, hbound, hlawful⟩
  have hred : reduceType hα hαβ q = p :=
    StageType.ext rfl (heq_of_eq (funext hreduce))
  have he : (reduceType hα hαβ q).someProvisionalValue = p.someProvisionalValue :=
    eq_of_heq (congr_arg_heq (fun t : S α n => t.someProvisionalValue) hred)
  intro d
  simpa only [he] using provisional_reduct_le_label hα hαβ q d

/-- Fixed-scheme fibre gap: a competing label can change only by reaching the
old top-grade threshold. This makes no assertion about arbitrary pointwise minima. -/
theorem eq_provisional_or_threshold_le_of_lawful_lift (p : S α n)
    (hα : Order.IsSuccLimit α) (hαβ : α ≤ β) (v : Cell p.scheme.scheme → ExtOrd)
    (hbound : ∀ d, v d < ofOrd β ∨ v d = ⊤)
    (hlawful : RespectsSemantics p.scheme.rows v)
    (hreduce : ∀ d, truncExt α (v d) = p.label d) (d : Cell p.scheme.scheme) :
    v d = p.someProvisionalValue d ∨ ofOrd (α + p.topGrade) ≤ v d := by
  let q : S β n := ⟨p.scheme, v, hbound, hlawful⟩
  have hred : reduceType hα hαβ q = p :=
    StageType.ext rfl (heq_of_eq (funext hreduce))
  have he : (reduceType hα hαβ q).someProvisionalValue = p.someProvisionalValue :=
    eq_of_heq (congr_arg_heq (fun t : S α n => t.someProvisionalValue) hred)
  simpa only [he, hred] using label_eq_provisional_or_threshold_le hα hαβ q d

/-- The minimum in the next-band reduction fibre is attained by one lawful
vector simultaneously at all coordinates, including for empty schemes. -/
theorem isLeast_provisional_lift (p : S α n) (hα : Order.IsSuccLimit α) :
    IsLeast {v : Cell p.scheme.scheme → ExtOrd |
      (∀ d, v d < ofOrd (α + Ordinal.omega0) ∨ v d = ⊤) ∧
      RespectsSemantics p.scheme.rows v ∧
      ∀ d, truncExt α (v d) = p.label d} p.someProvisionalValue := by
  refine ⟨⟨fun d => Or.inl (p.someProvisionalValue_lt_add_omega d),
    p.provisionalLift_respects hα, p.truncExt_someProvisionalValue⟩, ?_⟩
  rintro v ⟨hb, hl, hr⟩
  exact provisional_le_of_lawful_lift p hα (le_add_of_nonneg_right zero_le) v hb hl hr

/-- The same least vector lies in every higher-stage fibre containing the whole
next band. Increasing the ambient stage does not change this finite minimum. -/
theorem isLeast_provisional_lift_at (p : S α n) (hα : Order.IsSuccLimit α)
    (hstage : α + Ordinal.omega0 ≤ β) :
    IsLeast {v : Cell p.scheme.scheme → ExtOrd |
      (∀ d, v d < ofOrd β ∨ v d = ⊤) ∧
      RespectsSemantics p.scheme.rows v ∧
      ∀ d, truncExt α (v d) = p.label d} p.someProvisionalValue := by
  refine ⟨⟨fun d => Or.inl ((p.someProvisionalValue_lt_add_omega d).trans_le
    (ofOrd_le_ofOrd.mpr hstage)), p.provisionalLift_respects hα,
    p.truncExt_someProvisionalValue⟩, ?_⟩
  rintro v ⟨hb, hl, hr⟩
  exact provisional_le_of_lawful_lift p hα
    ((le_add_of_nonneg_right zero_le).trans hstage) v hb hl hr

/-- A universal lower bound over next-band lawful lifts is exactly a lower bound
on the single provisional vector. The reverse test uses that same vector at all
coordinates, not separately selected minimizing lifts. -/
theorem forall_lawful_lifts_le_iff (p : S α n) (hα : Order.IsSuccLimit α)
    (d : Cell p.scheme.scheme) (x : ExtOrd) :
    (∀ v : Cell p.scheme.scheme → ExtOrd,
      (∀ e, v e < ofOrd (α + Ordinal.omega0) ∨ v e = ⊤) →
      RespectsSemantics p.scheme.rows v →
      (∀ e, truncExt α (v e) = p.label e) → x ≤ v d) ↔
      x ≤ p.someProvisionalValue d := by
  constructor
  · intro h
    exact h p.someProvisionalValue
      (fun e => Or.inl (p.someProvisionalValue_lt_add_omega e))
      (p.provisionalLift_respects hα) p.truncExt_someProvisionalValue
  · intro h v hb hl hr
    exact h.trans (provisional_le_of_lawful_lift p hα
      (le_add_of_nonneg_right zero_le) v hb hl hr d)

/-- Universal thresholds at any ambient stage containing the next band are
tested on the same attained finite minimum. -/
theorem forall_lawful_lifts_le_iff_at (p : S α n) (hα : Order.IsSuccLimit α)
    (hstage : α + Ordinal.omega0 ≤ β) (d : Cell p.scheme.scheme) (x : ExtOrd) :
    (∀ v : Cell p.scheme.scheme → ExtOrd,
      (∀ e, v e < ofOrd β ∨ v e = ⊤) →
      RespectsSemantics p.scheme.rows v →
      (∀ e, truncExt α (v e) = p.label e) → x ≤ v d) ↔
      x ≤ p.someProvisionalValue d := by
  have hleast := isLeast_provisional_lift_at p hα hstage
  exact ⟨fun h => h _ hleast.1.1 hleast.1.2.1 hleast.1.2.2,
    fun h v hb hl hr => h.trans (hleast.2 ⟨hb, hl, hr⟩ d)⟩

/-- Restricting a larger provisional lift gives a lawful lift of the face.
Leastness therefore proves provisional monotonicity without invoking the
existing ratchet theorem. Equality of the two provisional vectors is not asserted. -/
theorem provisional_le_restrict_of_least {m : ℕ} (q : S α n)
    (hα : Order.IsSuccLimit α) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ q.scheme.scheme.plan) :
    ∀ d : Cell (q.scheme.scheme.restrictFace f hr),
      (q.restrictFace f hr).someProvisionalValue d ≤
        q.someProvisionalValue (toCell q.scheme.scheme f hr d) := by
  apply provisional_le_of_lawful_lift (q.restrictFace f hr) hα
    (β := α + Ordinal.omega0) (le_add_of_nonneg_right zero_le)
  · intro d
    exact Or.inl (q.someProvisionalValue_lt_add_omega _)
  · exact ((q.provisionalLift hα).restrictFace f hr).respects
  · intro d
    exact q.truncExt_someProvisionalValue _

/-- The strong restriction ratchet follows by applying the fibre gap to the
restriction of the larger lawful provisional lift. -/
theorem provisional_restrict_gap_of_least {m : ℕ} (q : S α n)
    (hα : Order.IsSuccLimit α) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ q.scheme.scheme.plan)
    (d : Cell (q.scheme.scheme.restrictFace f hr)) :
    (q.restrictFace f hr).someProvisionalValue d =
        q.someProvisionalValue (toCell q.scheme.scheme f hr d) ∨
      ofOrd (α + (q.restrictFace f hr).topGrade) ≤
        q.someProvisionalValue (toCell q.scheme.scheme f hr d) := by
  have h := eq_provisional_or_threshold_le_of_lawful_lift (q.restrictFace f hr) hα
    (β := α + Ordinal.omega0) (le_add_of_nonneg_right zero_le)
    (fun e => q.someProvisionalValue (toCell q.scheme.scheme f hr e))
    (fun e => Or.inl (q.someProvisionalValue_lt_add_omega _))
    ((q.provisionalLift hα).restrictFace f hr).respects
    (fun e => q.truncExt_someProvisionalValue _) d
  exact h.imp Eq.symm id

/-- Exact-face adapter for least-lift monotonicity, retaining the specified face
embedding and its transported cell. -/
theorem provisional_le_mapCell_of_least {m : ℕ} {p : S α m} {q : S α n}
    {f : Fin m ↪ Fin n} (hα : Order.IsSuccLimit α) (hf : typeMap f q = some p)
    (d : Cell p.scheme.scheme) :
    p.someProvisionalValue d ≤ q.someProvisionalValue (mapCell hf d) := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some hf, restrictFace_eq_of_typeMap_eq_some hf⟩
  exact provisional_le_restrict_of_least q hα f hr d

end VaughtConjecture.Knight.StageType
