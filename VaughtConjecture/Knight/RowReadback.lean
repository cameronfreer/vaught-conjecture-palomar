/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.EntailmentDomainCashout

/-!
# Lemma 10.1.1, finite fragment: readback from the pattern trigger, the cap, and one controller row

On the real objects: a domain `D` extending the base `p`, a prescribed labelling `q'`, and finite
reference data `R` over the cells of `D` (`Knight/RowCorrectness.lean`: cap at grade `N`, trigger,
block representatives, finite requests).  For every coface `q` of `p` with domain `D` and the
`⊥`-pattern of `q'`:

1. the pattern makes the trigger non-`⊥`;
2. availability from the cap — an old cell, so its label is pinned by `IsCoface.label_cellOf` —
   yields a controller `Ξ` at graded index `(univ, N)` with `q □ ≤ q Ξ`;
3. locality at `Ξ` gives a Def. 2.3.9 witness carrying the row of `Ξ` (correct by hypothesis) to
   `d ↦ min (q d) (q Ξ)`; the transported correctness
   (`FiniteReferenceData.Correct.transport_witness`) then reads back every requested finite
   label exactly: `q Θ = μ + i` (`ReadbackInputs.readback`).

No availability is applied at a requested cell and no same-grade "guard" is involved: full-grade
request cells are read through the controller's row.  No general transitivity of `⇒` is used; the
printed proof's chain of two transformations is replaced by one transported correctness and one
locality.  `ReadbackInputs` lists what the producer owes: the reference cells with their base
labels (Lemma 8.1.1's context enlargement), the existence of a controller at `(univ, N)`
(completeness of `D`), and correctness of every such controller's row (Def. 8.3.2's thinning).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType CellScheme Transform Value ExtOrd

variable {α : Ordinal.{0}} {m : ℕ}

/-! ## Label transport (local copies) -/

theorem StageType.label_castCell {t₁ t₂ : S α m} (h : t₁ = t₂) (d : Cell t₁.scheme.scheme) :
    t₂.label (SemScheme.castCell (congrArg StageType.scheme h) d) = t₁.label d := by
  subst h
  rw [SemScheme.castCell_self]

theorem IsCoface.label_cellOf {p : S α m} {q : S α (m + 1)} (h : IsCoface p q)
    (d : Cell p.scheme.scheme) : q.label (h.extendsDomain.cellOf d) = p.label d := by
  have hvis := h.extendsDomain.visible
  have hp : q.restrictFace Fin.castSuccEmb hvis = p :=
    Option.some.inj ((typeMap_eq_some _ q hvis).symm.trans h)
  rw [← StageType.label_castCell hp.symm d]
  rfl

/-! ## Rows as total functions on the cells -/

open Classical in
/-- The row of `Ξ`, extended by `⊥` off the lower set of `Ξ`. -/
noncomputable def SemScheme.rowOf (D : SemScheme (m + 1)) (Ξ : Cell D.scheme) :
    Cell D.scheme → ExtOrd :=
  fun d => if h : GradedLe (D.scheme.cell d) (D.scheme.cell Ξ) then D.rows.E Ξ ⟨d, h⟩ else ⊥

theorem SemScheme.rowOf_of_le (D : SemScheme (m + 1)) (Ξ : Cell D.scheme) {d : Cell D.scheme}
    (h : GradedLe (D.scheme.cell d) (D.scheme.cell Ξ)) : D.rowOf Ξ d = D.rows.E Ξ ⟨d, h⟩ := by
  unfold SemScheme.rowOf
  rw [dif_pos h]

/-- Every cell of grade `≤ N` lies below a cell at graded index `(univ, N)`. -/
theorem gradedLe_of_cell_eq_univ {D : SemScheme (m + 1)} {Ξ d : Cell D.scheme} {N : ℕ}
    (hΞ : D.scheme.cell Ξ = (Finset.univ, N)) (hd : D.scheme.grade d ≤ N) :
    GradedLe (D.scheme.cell d) (D.scheme.cell Ξ) := by
  rw [hΞ]
  exact ⟨Finset.subset_univ _, hd⟩

/-! ## The producer's inputs and the readback theorem -/

/-- **Readback inputs** for a domain `D` extending `p`, prescribed labelling `q'`, and reference
data `R`: the trigger is pattern-visible and non-`⊥` in `q'`; the cap is an old cell whose base
label dominates every requested value; each representative is an old cell whose base label is
`μ + j` with `j < N`, under the cap; requested blocks are limit parts; a controller at `(univ, N)`
exists; and every controller's row is correct. -/
structure ReadbackInputs {p : S α m} {D : SemScheme (m + 1)} (h : ExtendsDomain p D)
    (q' : Cell D.scheme → ExtOrd) (R : FiniteReferenceData (Cell D.scheme) D.scheme.grade) where
  trigger_grade_le_m : D.scheme.grade R.trigger ≤ m
  trigger_grade_le_N : D.scheme.grade R.trigger ≤ R.N
  trigger_pattern : q' R.trigger ≠ ⊥
  capBase : Cell p.scheme.scheme
  cap_eq : R.cap = h.cellOf capBase
  cap_dom : ∀ r ∈ R.requests, ofOrd (r.block + r.offset) < p.label capBase
  repBase : Ordinal.{0} → Cell p.scheme.scheme
  repOff : Ordinal.{0} → ℕ
  rep_eq : ∀ r ∈ R.requests, R.rep r.block = h.cellOf (repBase r.block)
  rep_label : ∀ r ∈ R.requests, p.label (repBase r.block) = ofOrd (r.block + repOff r.block)
  rep_off_lt : ∀ r ∈ R.requests, repOff r.block < R.N
  rep_le_cap : ∀ r ∈ R.requests, p.label (repBase r.block) ≤ p.label capBase
  block_limit : ∀ r ∈ R.requests, limitPart r.block = r.block
  controller_exists : ∃ Ξ : Cell D.scheme, D.scheme.cell Ξ = (Finset.univ, R.N)
  rows_correct : ∀ Ξ : Cell D.scheme, D.scheme.cell Ξ = (Finset.univ, R.N) →
    R.Correct (D.rowOf Ξ)

theorem min_ne_bot {a b : ExtOrd} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : min a b ≠ ⊥ := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]; exact ha
  · rw [min_eq_right h]; exact hb

/-- The block representative's replaced value is the requested value. -/
theorem extVisibilityReplace_rep {μ : Ordinal.{0}} {j i N : ℕ} (hμ : limitPart μ = μ)
    (hj : j < N) : extVisibilityReplace (ofOrd (μ + j)) N i = ofOrd (μ + i) := by
  rw [extVisibilityReplace_ofOrd]
  unfold visibilityReplace
  have hfp : finitePart (μ + j) = j := by
    conv_lhs => rw [← hμ]
    exact finitePart_limitPart_add_nat μ j
  rw [hfp, if_pos hj]
  unfold ordinalReplace
  have hlp : limitPart (μ + j) = μ := by
    conv_lhs => rw [← hμ]
    rw [limitPart_limitPart_add_nat, hμ]
  rw [hlp]

/-- **Lemma 10.1.1, finite fragment.**  Every coface of `p` with domain `D` and the `⊥`-pattern
of `q'` reads back each requested finite label exactly. -/
theorem ReadbackInputs.readback {p : S α m} {D : SemScheme (m + 1)} {h : ExtendsDomain p D}
    {q' : Cell D.scheme → ExtOrd} {R : FiniteReferenceData (Cell D.scheme) D.scheme.grade}
    (I : ReadbackInputs h q' R) (q : S α (m + 1)) (hqD : q.scheme = D)
    (hpat : ∀ Θ : D.scheme.below (Finset.univ, m),
      q.label (SemScheme.castCell hqD.symm Θ.1) = ⊥ ↔ q' Θ.1 = ⊥)
    (hq : IsCoface p q) :
    ∀ r ∈ R.requests,
      q.label (SemScheme.castCell hqD.symm r.cell) = ofOrd (r.block + r.offset) := by
  obtain ⟨sch, lab, hb, hr⟩ := q
  dsimp only at hqD
  subst hqD
  intro r hrq
  rw [SemScheme.castCell_self]
  -- 1. the trigger fires
  have htrig : lab R.trigger ≠ ⊥ := by
    intro h0
    apply I.trigger_pattern
    have := (hpat ⟨R.trigger, ⟨Finset.subset_univ _, I.trigger_grade_le_m⟩⟩).mp
    rw [SemScheme.castCell_self] at this
    exact this h0
  -- known labels of the old reference cells
  have hcap : lab R.cap = p.label I.capBase := by
    rw [I.cap_eq]; exact hq.label_cellOf I.capBase
  have hrep : lab (R.rep r.block) = ofOrd (r.block + I.repOff r.block) := by
    rw [I.rep_eq r hrq]
    exact (hq.label_cellOf _).trans (I.rep_label r hrq)
  -- 2. availability from the cap: a controller `Ξ` with `lab cap ≤ lab Ξ`
  obtain ⟨Ξ₀, hΞ₀⟩ := I.controller_exists
  obtain ⟨Ξ, hΞ, hle⟩ := hr.availability R.cap Ξ₀
    (by rw [show sch.scheme.scope Ξ₀ = Finset.univ from congrArg Prod.fst hΞ₀]
        exact Finset.subset_univ _)
    (by rw [show sch.scheme.grade Ξ₀ = R.N from congrArg Prod.snd hΞ₀]; exact R.cap_grade)
  have hΞ' : sch.scheme.cell Ξ = (Finset.univ, R.N) := hΞ.trans hΞ₀
  -- 3. locality at `Ξ` transports the correct row of `Ξ`
  obtain ⟨g, σ, hanti, hsv, hbot, hmono, h5, hloc⟩ := hr.locality Ξ
  have hc0 : R.Correct (sch.rowOf Ξ) := I.rows_correct Ξ hΞ'
  have hc1 := hc0.transport_witness ⟨g, σ, hanti, hsv, hbot, hmono, h5⟩
  -- on every cell of grade `≤ N` the transported row is `min (lab d) (lab Ξ)`
  have hval : ∀ d : Cell sch.scheme, sch.scheme.grade d ≤ R.N →
      (TransformWitness.apply ⟨g, σ, hanti, hsv, hbot, hmono, h5⟩ sch.scheme.grade
        (sch.rowOf Ξ)) d = min (lab d) (lab Ξ) := by
    intro d hd
    have hdΞ := gradedLe_of_cell_eq_univ hΞ' hd
    show min (σ (sch.rowOf Ξ d)) (g (sch.scheme.grade d)) = min (lab d) (lab Ξ)
    rw [sch.rowOf_of_le Ξ hdΞ]
    exact (hloc ⟨d, hdΞ⟩).symm
  have hc2 : R.Correct (fun d => min (lab d) (lab Ξ)) :=
    hc1.congr (hval _ I.trigger_grade_le_N) (hval _ (by rw [R.cap_grade]))
      fun r' hr' => ⟨hval _ (R.req_grade_le r' hr'), hval _ (R.rep_grade_le r' hr')⟩
  -- the trigger of the transported row
  have hcapne : lab R.cap ≠ ⊥ := by
    rw [hcap]; exact ne_bot_of_gt (I.cap_dom r hrq)
  have hΞne : lab Ξ ≠ ⊥ := fun h0 => hcapne (le_bot_iff.mp (h0 ▸ hle))
  have heq := hc2 (min_ne_bot htrig hΞne) r hrq
  -- 4. evaluate the equation
  have hcapΞ : min (lab R.cap) (lab Ξ) = lab R.cap := min_eq_left hle
  have hrepΞ : min (lab (R.rep r.block)) (lab Ξ) = lab (R.rep r.block) :=
    min_eq_left (by
      rw [hrep, ← I.rep_label r hrq]
      exact (I.rep_le_cap r hrq).trans (hcap ▸ hle))
  dsimp only at heq
  rw [hcapΞ, hrepΞ, hrep,
    extVisibilityReplace_rep (I.block_limit r hrq) (I.rep_off_lt r hrq), hcap] at heq
  have hdom := I.cap_dom r hrq
  have hcΞ : p.label I.capBase ≤ lab Ξ := hcap ▸ hle
  rw [min_eq_left hdom.le, min_assoc, min_eq_right hcΞ] at heq
  rcases le_total (lab r.cell) (p.label I.capBase) with hΘ | hΘ
  · rwa [min_eq_left hΘ] at heq
  · rw [min_eq_right hΘ] at heq
    exact absurd (heq ▸ hdom) (lt_irrefl _)

end VaughtConjecture.Knight
