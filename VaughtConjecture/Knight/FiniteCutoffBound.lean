/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RowCorrectness

/-! # The one-block finite-cut transfer: a lower bound in place of an exact `⊤`

**The observation** (`docs/notes`, 2026-09-05): reduction to a limit stage `α` sends every value at
or above `α` to `⊤` (`truncExt_ofOrd_of_le`).  So to copy a requested `α`-chart inside a model one
block higher, a requested `⊤` needs only a value **at least `α`** — a lower bound, not an actual
`⊤`.  The reference for it is a *proper* value `α + j` (`j` below the comparison grade `N`), whose
visibility replacement at offset `0` is `α`; the requested cell must then satisfy the **capped
inequality**

    min (ν_{N,0}(f (rep)), f cap) ≤ min (f Θ, f cap).

**Compiled here.**

1. `FiniteReferenceData.CutoffBound` — the inequality form of the finite-value correctness
   predicate `FiniteReferenceData.Correct` (`Knight/RowCorrectness.lean`), guarded by the trigger.
2. `CutoffBound.transport_witness` / `CutoffBound.transport` — **the inequality transports along
   every Def. 2.3.9 witness**, by the same case analysis as the equality (the cap at grade `N`
   absorbs lower suppressions; clause 5 moves the shifter through the replacement when the
   representative's image is under the cap; otherwise both sides collapse to the cap, the middle
   case being impossible).  Monotonicity of the shifter carries the inequality where the equality
   proof used it as an equation.
3. `CutoffBound.readback_top` — **readback as `⊤` after reduction**: at a request with offset `0`
   whose representative carries the proper reference `α + j` (`j < N`, `α` a limit) and whose cap
   is at least `α`, the requested cell's value reduces to `⊤` at `α`.

A legal finite domain enforcing the inequality on an actual respecting labelling is
`Knight/AssembledReferenceContext.lean`.  Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

variable {D : Type*} {grade : D → ℕ}

/-- **The cutoff lower bound** (finite-cut correctness): at every request, the capped normalized
reference is at most the capped requested value. -/
def FiniteReferenceData.CutoffBound (R : FiniteReferenceData D grade) (f : D → ExtOrd) : Prop :=
  f R.trigger ≠ ⊥ →
    ∀ r ∈ R.requests,
      min (extVisibilityReplace (f (R.rep r.block)) R.N r.offset) (f R.cap) ≤
        min (f r.cell) (f R.cap)

theorem FiniteReferenceData.CutoffBound.congr {R : FiniteReferenceData D grade} {f f' : D → ExtOrd}
    (hc : R.CutoffBound f) (htrig : f R.trigger = f' R.trigger) (hcap : f R.cap = f' R.cap)
    (hreq : ∀ r ∈ R.requests, f r.cell = f' r.cell ∧ f (R.rep r.block) = f' (R.rep r.block)) :
    R.CutoffBound f' := by
  intro ht' r hr
  have := hc (htrig ▸ ht') r hr
  rw [(hreq r hr).1, (hreq r hr).2, hcap] at this
  exact this

/-- **Transport of the cutoff lower bound along a witness.** -/
theorem FiniteReferenceData.CutoffBound.transport_witness {R : FiniteReferenceData D grade}
    {f : D → ExtOrd} (W : TransformWitness) (hc : R.CutoffBound f) :
    R.CutoffBound (W.apply grade f) := by
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
  -- the right-hand side: the cap absorbs `g (grade Θ)`
  have eR : min (min (σ (f r.cell)) (g (grade r.cell))) (min (σ (f R.cap)) (g R.N)) =
      min (σ (min (f r.cell) (f R.cap))) (g R.N) := by
    rw [monotone_min_apply hmono, min_min_min_comm, min_eq_right hgΘ]
  -- the source inequality, pushed through the monotone shifter
  have hσ : min (σ (extVisibilityReplace (f (R.rep r.block)) R.N r.offset))
      (min (σ (f R.cap)) (g R.N))
      ≤ min (σ (min (f r.cell) (f R.cap))) (g R.N) := by
    have := hmono hc'
    rw [monotone_min_apply hmono] at this
    calc min (σ (extVisibilityReplace (f (R.rep r.block)) R.N r.offset)) (min (σ (f R.cap)) (g R.N))
        = min (min (σ (extVisibilityReplace (f (R.rep r.block)) R.N r.offset)) (σ (f R.cap)))
          (g R.N) := by
          rw [min_assoc]
      _ ≤ _ := min_le_min this le_rfl
  rw [eR]
  refine le_trans ?_ hσ
  -- the shifter moves through the replacement, or both collapse to the cap
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
    · exact le_min ((min_le_right _ _).trans hB) le_rfl
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

/-- The relation form: the cutoff lower bound is preserved by `⇒`. -/
theorem FiniteReferenceData.CutoffBound.transport {R : FiniteReferenceData D grade}
    {f f' : D → ExtOrd} (h : TransformsTo grade f f') (hc : R.CutoffBound f) :
    R.CutoffBound f' := by
  obtain ⟨g, σ, hanti, hsv, hbot, hmono, h5, hq⟩ := h
  have := hc.transport_witness ⟨g, σ, hanti, hsv, hbot, hmono, h5⟩
  exact this.congr (hq _).symm (hq _).symm fun r _ => ⟨(hq _).symm, (hq _).symm⟩

/-- The equality form implies the inequality form. -/
theorem FiniteReferenceData.Correct.cutoffBound {R : FiniteReferenceData D grade} {f : D → ExtOrd}
    (hc : R.Correct f) : R.CutoffBound f := fun ht r hr => (hc ht r hr).ge

/-! ## Readback as `⊤` after reduction -/

/-- **Readback**: at a request with offset `0` whose representative carries the proper reference
`α + j` (`j < N`, `α` a limit) and whose cap is at least `α`, the requested value reduces to `⊤`
at `α`. -/
theorem FiniteReferenceData.CutoffBound.readback_top {R : FiniteReferenceData D grade}
    {f : D → ExtOrd} (hc : R.CutoffBound f) (ht : f R.trigger ≠ ⊥) {r : FiniteRequest D}
    (hr : r ∈ R.requests) (h0 : r.offset = 0) {α : Ordinal.{0}} (hα : limitPart α = α) {j : ℕ}
    (hj : j < R.N) (href : f (R.rep r.block) = ofOrd (α + j)) (hcap : ofOrd α ≤ f R.cap) :
    truncExt α (f r.cell) = ⊤ := by
  have h := hc ht r hr
  rw [h0, href] at h
  -- the normalized reference is `α`
  have hν : extVisibilityReplace (ofOrd (α + j)) R.N 0 = ofOrd α := by
    rw [extVisibilityReplace_ofOrd, visibilityReplace,
      ite_eq_left (by rw [← hα, finitePart_limitPart_add_nat]; exact hj)]
    unfold ordinalReplace
    rw [← hα, limitPart_limitPart_add_nat, Nat.cast_zero, add_zero, hα]
  rw [hν, min_eq_left hcap] at h
  have hΘ : ofOrd α ≤ f r.cell := h.trans (min_le_left _ _)
  rcases ExtOrd.cases (f r.cell) with hb | htop | ⟨β, hβ⟩
  · rw [hb] at hΘ; exact absurd hΘ (not_ofOrd_le_bot α)
  · rw [htop, truncExt_top]
  · rw [hβ] at hΘ ⊢
    exact truncExt_ofOrd_of_le (ofOrd_le_ofOrd.mp hΘ)

end VaughtConjecture.Knight

