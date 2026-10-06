/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Transform
public import VaughtConjecture.Knight.VisibilityAlgebra

/-!
# Row correctness (Def. 8.3.1, finite-value fragment) and its transport along `⇒` (Lemma 8.3.3)

Knight's Def. 8.3.1 states correctness of a *row* `f` relative to reference cells of an enlarged
context: a cap `□` of grade `N`, one representative `□_μ` per limit block `μ` occurring among the
requested finite labels, and a trigger `Σ♦`.  Its finite-value clause (clause 2), guarded by the
trigger `f Σ♦ ≥ 0`, reads

    min (f Θ) (f □) = min (f (□_μ) ⊔⁺_N i) (f □)      whenever the requested label of Θ is μ + i.

Lemma 8.3.3 asserts that correctness is preserved by `⇒`, "as a consequence of the logical form
in which correctness is defined".  This file proves the finite-value fragment of that claim on the
faithful relation (`Transform.TransformsTo`, Def. 2.3.9 verbatim, unguarded clause 5), with no
transitivity of `⇒`, and records the four facts the one-line proof leaves implicit:

1. the common cap at grade `N` absorbs the grade-dependent suppression of the lower-grade cells
   (`g N ≤ g (grade d)`), so the target equation reduces to the source equation under `σ`;
2. visibility replacement at threshold `N` commutes with the shifter (clause 5) when the
   representative's image lies under the cap, and a self-visible cap survives replacement from
   below (`le_extVisibilityReplace_of_selfVis_le`);
3. the trigger survives in the needed direction (`f' Σ♦ ≠ ⊥ → f Σ♦ ≠ ⊥`, from `σ ⊥ = ⊥`);
4. the remaining case — representative above the cap but its replacement below — is impossible:
   clause 5 applied to the *replaced* representative, re-replacement of the finite part
   (`extVisibilityReplace_extVisibilityReplace_finitePart`, which needs the offset `< N`), and
   self-visibility of `g N` contradict it.

The `∞` clauses of Def. 8.3.1 (clauses 3–5, branch-specific) are not treated here.

The transport is stated for a Def. 2.3.9 witness (`TransformWitness`) as well as for the relation
(`FiniteReferenceData.Correct.transport`), and correctness only inspects the reference and
requested cells (`FiniteReferenceData.Correct.congr`), so a row restricted to a lower set can be
transported after extension by `⊥`.  Consumed by the Lemma 10.1.1 readback (in preparation).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Reference data and the finite-value correctness predicate -/

/-- A finite-label request over cells `D`: cell `Θ`, limit block `μ`, finite offset `i`, meaning
the requested label of `Θ` is `μ + i`. -/
structure FiniteRequest (D : Type*) where
  cell : D
  block : Ordinal.{0}
  offset : ℕ

/-- Reference data of the finite fragment: threshold `N`, cap cell (grade `N`), trigger cell, one
representative cell per block, and the requests, with the grade side conditions of Lemma 8.1.1
clause 4 (`N` exceeds the grades of requested and representative cells and every offset). -/
structure FiniteReferenceData (D : Type*) (grade : D → ℕ) where
  N : ℕ
  cap : D
  cap_grade : grade cap = N
  trigger : D
  rep : Ordinal.{0} → D
  requests : List (FiniteRequest D)
  req_grade_le : ∀ r ∈ requests, grade r.cell ≤ N
  rep_grade_le : ∀ r ∈ requests, grade (rep r.block) ≤ N
  offset_lt : ∀ r ∈ requests, r.offset < N

variable {D : Type*} {grade : D → ℕ}

/-- **Finite-value correctness** of a row `f` (Def. 8.3.1, clause 2), guarded by the trigger. -/
def FiniteReferenceData.Correct (R : FiniteReferenceData D grade) (f : D → ExtOrd) : Prop :=
  f R.trigger ≠ ⊥ →
    ∀ r ∈ R.requests,
      min (f r.cell) (f R.cap) =
        min (extVisibilityReplace (f (R.rep r.block)) R.N r.offset) (f R.cap)

/-! ## Value lemmas -/

/-- `min` distributes over a monotone shifter. -/
theorem monotone_min_apply {σ : ExtOrd → ExtOrd} (hσ : Monotone σ) (a b : ExtOrd) :
    σ (min a b) = min (σ a) (σ b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (hσ h)]
  · rw [min_eq_right h, min_eq_right (hσ h)]


/-- A label moved by visibility replacement at threshold `N` is an ordinal with finite part
below `N`. -/
theorem exists_of_extVisibilityReplace_ne {x : ExtOrd} {N i : ℕ}
    (h : extVisibilityReplace x N i ≠ x) : ∃ β : Ordinal.{0}, x = ofOrd β ∧ finitePart β < N := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact absurd rfl h
  · exact absurd rfl h
  · refine ⟨β, rfl, ?_⟩
    by_contra hge
    push Not at hge
    apply h
    rw [extVisibilityReplace_ofOrd]
    unfold visibilityReplace
    rw [if_neg (not_lt.mpr hge)]

/-- Re-replacing the finite part recovers the label (offset `< N`). -/
theorem extVisibilityReplace_extVisibilityReplace_finitePart {β : Ordinal.{0}} {N i : ℕ}
    (hβ : finitePart β < N) (hi : i < N) :
    extVisibilityReplace (extVisibilityReplace (ofOrd β) N i) N (finitePart β) = ofOrd β := by
  rw [extVisibilityReplace_ofOrd]
  unfold visibilityReplace
  rw [if_pos hβ]
  unfold ordinalReplace
  rw [extVisibilityReplace_ofOrd]
  unfold visibilityReplace
  rw [finitePart_limitPart_add_nat, if_pos hi]
  unfold ordinalReplace
  rw [limitPart_limitPart_add_nat, decomposition]

/-! ## Lemma 8.3.3, finite fragment: correctness is preserved by `⇒` -/

/-- The witness data of Def. 2.3.9 without the target equation: a suppressor and a shifter with
clauses 1–5. -/
structure TransformWitness where
  g : ℕ → ExtOrd
  σ : ExtOrd → ExtOrd
  anti : ∀ n m : ℕ, n < m → g m ≤ g n
  selfVis : ∀ n : ℕ, g n = extVisibilityReplace (g n) n n
  bot : σ ⊥ = ⊥
  mono : Monotone σ
  comm : ∀ (α : ExtOrd) (k : ℕ), σ α ≤ g k → ∀ i : ℕ, i ≤ k →
    σ (extVisibilityReplace α k i) = extVisibilityReplace (σ α) k i

/-- The target of a witness applied to a source row. -/
noncomputable def TransformWitness.apply (W : TransformWitness) (grade : D → ℕ) (f : D → ExtOrd) :
    D → ExtOrd :=
  fun d => min (W.σ (f d)) (W.g (grade d))

/-- Correctness mentions only the trigger, the cap, the representatives and the requested cells. -/
theorem FiniteReferenceData.Correct.congr {R : FiniteReferenceData D grade} {f f' : D → ExtOrd}
    (hc : R.Correct f) (htrig : f R.trigger = f' R.trigger) (hcap : f R.cap = f' R.cap)
    (hreq : ∀ r ∈ R.requests, f r.cell = f' r.cell ∧ f (R.rep r.block) = f' (R.rep r.block)) :
    R.Correct f' := by
  intro ht' r hr
  have := hc (htrig ▸ ht') r hr
  rw [(hreq r hr).1, (hreq r hr).2, hcap] at this
  exact this

/-- **Transport of finite-value correctness along a Def. 2.3.9 witness** (Lemma 8.3.3, finite
fragment).  The cap at grade `N` absorbs the suppression of the lower-grade cells; clause 5 at
threshold `N` moves the shifter through the replacement when the representative's image lies under
the cap; when it does not, both sides collapse to the (self-visible) cap, the impossible middle
case being excluded by clause 5 applied to the replaced representative. -/
theorem FiniteReferenceData.Correct.transport_witness {R : FiniteReferenceData D grade}
    {f : D → ExtOrd} (W : TransformWitness) (hc : R.Correct f) :
    R.Correct (W.apply grade f) := by
  obtain ⟨g, σ, hanti, hsv, hbot, hmono, h5⟩ := W
  have hq : ∀ d, (TransformWitness.apply ⟨g, σ, hanti, hsv, hbot, hmono, h5⟩ grade f) d =
      min (σ (f d)) (g (grade d)) := fun _ => rfl
  intro ht' r hr
  have ht : f R.trigger ≠ ⊥ := by
    intro h0
    apply ht'
    rw [hq, h0, hbot]
    exact min_eq_left bot_le
  have hc' := hc ht r hr
  have hgΘ : g R.N ≤ g (grade r.cell) := suppressor_le_of_grade_le hanti (R.req_grade_le r hr)
  have hgρ : g R.N ≤ g (grade (R.rep r.block)) :=
    suppressor_le_of_grade_le hanti (R.rep_grade_le r hr)
  have hgcap : g (grade R.cap) = g R.N := by rw [R.cap_grade]
  have hsvN : extVisibilityReplace (g R.N) R.N R.N = g R.N := (hsv R.N).symm
  rw [hq r.cell, hq R.cap, hq (R.rep r.block), hgcap]
  -- the left-hand side: the cap absorbs `g (grade Θ)`, then the source equation applies
  have hL : min (min (σ (f r.cell)) (g (grade r.cell))) (min (σ (f R.cap)) (g R.N)) =
      min (σ (extVisibilityReplace (f (R.rep r.block)) R.N r.offset))
        (min (σ (f R.cap)) (g R.N)) := by
    have e1 : min (min (σ (f r.cell)) (g (grade r.cell))) (min (σ (f R.cap)) (g R.N)) =
        min (σ (min (f r.cell) (f R.cap))) (g R.N) := by
      rw [monotone_min_apply hmono, min_min_min_comm, min_eq_right hgΘ]
    have e2 : min (σ (min (extVisibilityReplace (f (R.rep r.block)) R.N r.offset) (f R.cap)))
        (g R.N) =
        min (σ (extVisibilityReplace (f (R.rep r.block)) R.N r.offset))
          (min (σ (f R.cap)) (g R.N)) := by
      rw [monotone_min_apply hmono, min_assoc]
    rw [e1, hc', e2]
  rw [hL]
  by_cases hA : σ (f (R.rep r.block)) ≤ g R.N
  · rw [min_eq_left (hA.trans hgρ), ← h5 _ R.N hA _ (R.offset_lt r hr).le]
  · push Not at hA
    have hρ' : g R.N ≤ min (σ (f (R.rep r.block))) (g (grade (R.rep r.block))) :=
      le_min hA.le hgρ
    have hR : g R.N ≤ extVisibilityReplace
        (min (σ (f (R.rep r.block))) (g (grade (R.rep r.block)))) R.N r.offset :=
      le_extVisibilityReplace_of_selfVis_le hsvN hρ'
    rw [min_eq_right ((min_le_right _ _).trans hR)]
    by_cases hB : g R.N ≤ σ (extVisibilityReplace (f (R.rep r.block)) R.N r.offset)
    · exact min_eq_right ((min_le_right _ _).trans hB)
    · exfalso
      push Not at hB
      have hne : extVisibilityReplace (f (R.rep r.block)) R.N r.offset ≠ f (R.rep r.block) :=
        fun he => absurd (he ▸ hB) (not_lt.mpr hA.le)
      obtain ⟨β, hβ, hfp⟩ := exists_of_extVisibilityReplace_ne hne
      have h5' := h5 _ R.N hB.le (finitePart β) hfp.le
      have hle := extVisibilityReplace_le_of_le_selfVis hfp.le hsvN hB.le
      rw [hβ] at h5' hle hA
      rw [extVisibilityReplace_extVisibilityReplace_finitePart hfp (R.offset_lt r hr)] at h5'
      rw [← h5'] at hle
      exact absurd hle (not_le.mpr hA)

/-- The relation form: correctness is preserved by `⇒`. -/
theorem FiniteReferenceData.Correct.transport {R : FiniteReferenceData D grade}
    {f f' : D → ExtOrd} (h : TransformsTo grade f f') (hc : R.Correct f) : R.Correct f' := by
  obtain ⟨g, σ, hanti, hsv, hbot, hmono, h5, hq⟩ := h
  have := hc.transport_witness ⟨g, σ, hanti, hsv, hbot, hmono, h5⟩
  exact this.congr (hq _).symm (hq _).symm fun r _ => ⟨(hq _).symm, (hq _).symm⟩

end VaughtConjecture.Knight
