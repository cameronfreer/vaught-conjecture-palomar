/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RowReadback
public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.Semantics

/-! # The capped-offset guard: reflection, safe predicates, and two-labelling readback

After the reviewer's notes `vc-notes/newapproach2.md` and `vc-notes/README.md`
(offset-guarded comparison, 2026-09-12; ported with attribution, checked here in Lean).

**The guard.**  For a marker `a` and a cap `C` of grade `N`, `Guard N j a C f` says the capped
marker `min (f a) (f C)` is a proper ordinal of finite part `j` (`j < N`).

* **Guard reflection** (`Guard.reflect`): if `f ⇒ f'` faithfully, `Guard f'` implies `Guard f`.
  The capped coordinates of the target are one monotone scalar map of the capped coordinates of
  the source (`capped_transform`); the suppressor value is `N`-visible while the target minimum
  is not, so the shifter sends the source minimum to it under the clause-5 guard, and clause 5 at
  the source's own finite offset pins that offset to `j`.  No transitivity of transformations is
  used.
* **Safe predicates** (`Safe`, `Safe.transport`): for a predicate `Φ` preserved by faithful
  transformation, `Guard f → Φ f` is preserved too.  A row outside the guard may remain incorrect;
  no faithful retuning of it becomes guarded and incorrect.
* **Top requests** (`TopRequests`, `TopRequests.Correct`, `.transport`): the capped marker is at
  most every requested capped coordinate; preserved because the same monotone map acts on both
  sides.  Proper requests are the finite correctness predicate of `Knight/RowCorrectness.lean`.
* **Strata** (`guard_min`, `not_guard_min`): the guard and its negation are both closed under
  pointwise minimum, since the capped marker of a meet is one of the two capped markers.
* **Two-labelling readback at a selected controller** (`guarded_readback_at`): with two
  labellings respecting the same rows — `q` ordinary, `s` "stable" — a controller `Θ` labelled
  `⊤` by `q` whose row is safe, and the guard active on the stable capped target at `Θ`, the
  ordinary labelling satisfies both correctness predicates: the guard reflects along the stable
  locality to the row, safety gives the row's correctness, and ordinary locality transports it to
  `q` capped at `q Θ = ⊤`.  `select_top_controller` supplies `Θ` from ordinary availability at a
  top-labelled cap; `read_proper`/`read_top` read the exact labels.  Nothing assumes `q ⇒ s` or
  that the stable labelling satisfies model axioms.

What this does not do: construct a legal request domain whose full-scope rows are safe, nor
supply the stable labelling and its guard activation (those come from the actual model's
stable values in the reviewer's lane).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

section Guard

variable {D : Type*} {grade : D → ℕ}

/-- **The capped-offset guard**: the capped marker is a proper ordinal of finite part `j`. -/
def Guard (j : ℕ) (a C : D) (f : D → ExtOrd) : Prop :=
  ∃ δ : Ordinal.{0}, min (f a) (f C) = ofOrd δ ∧ finitePart δ = j

/-- **The capped-coordinate identity**: under a faithful witness, the target's capped coordinate
at a cell of grade at most the cap's is the shifted source capped coordinate, suppressed at the
cap's grade. -/
theorem capped_transform {f f' : D → ExtOrd} {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd}
    (hanti : ∀ n m : ℕ, n < m → g m ≤ g n) (hmono : Monotone σ)
    (hq : ∀ d, f' d = min (σ (f d)) (g (grade d))) {N : ℕ} {C d : D} (hC : grade C = N)
    (hd : grade d ≤ N) : min (f' d) (f' C) = min (σ (min (f d) (f C))) (g N) := by
  rw [hq d, hq C, hC, min_min_min_comm, ← monotone_min_apply hmono,
    min_eq_right (suppressor_le_of_grade_le hanti hd)]

/-- A label `ofOrd β` with `finitePart β < N` is not self-visible at `N`. -/
theorem not_selfVis_of_finitePart_lt {β : Ordinal.{0}} {N : ℕ} (h : finitePart β < N) :
    ¬ SelfVis N (ofOrd β) := by
  rw [selfVis_ofOrd_iff]
  omega

/-- Replacing the finite part of a label by its own finite part (below the threshold) fixes it. -/
theorem extVisibilityReplace_finitePart_self {v : Ordinal.{0}} {N : ℕ} (h : finitePart v < N) :
    extVisibilityReplace (ofOrd v) N (finitePart v) = ofOrd v := by
  have e := extVisibilityReplace_rep (limitPart_idem v) h (i := finitePart v)
  rw [limitPart_add_finitePart] at e
  exact e

/-- **Guard reflection**: a guard on the target of a faithful transformation reflects to the
source. -/
theorem Guard.reflect {f f' : D → ExtOrd} (h : TransformsTo grade f f') {N j : ℕ} {a C : D}
    (hC : grade C = N) (ha : grade a ≤ N) (hj : j < N) (hg : Guard j a C f') : Guard j a C f := by
  obtain ⟨g, σ, hanti, hsv, hbot, hmono, h5, hq⟩ := h
  obtain ⟨β, hβ, hfp⟩ := hg
  rw [capped_transform hanti hmono hq hC ha] at hβ
  set u := min (f a) (f C) with hu
  have hβvis : ¬ SelfVis N (ofOrd β) := not_selfVis_of_finitePart_lt (by omega)
  have hσu : σ u = ofOrd β := by
    rcases min_cases (σ u) (g N) with ⟨hm, -⟩ | ⟨hm, -⟩
    · rw [hm] at hβ; exact hβ
    · exfalso
      rw [hm] at hβ
      apply hβvis
      rw [← hβ]
      exact (hsv N).symm
  have hguard : σ u ≤ g N := by
    rw [hσu, ← hβ]
    exact min_le_right _ _
  have hβe : ofOrd β = ofOrd (limitPart β + (j : Ordinal)) := by
    rw [← hfp, limitPart_add_finitePart]
  rcases ExtOrd.cases u with hbot' | htop | ⟨v, hv⟩
  · exfalso
    rw [hbot', hbot] at hσu
    exact ofOrd_ne_bot β hσu.symm
  · exfalso
    have h5' := h5 u N hguard N le_rfl
    rw [htop, extVisibilityReplace_top] at h5'
    rw [htop] at hσu
    rw [hσu] at h5'
    exact hβvis h5'.symm
  · rcases lt_or_ge (finitePart v) N with hlt | hge
    · have h5' := h5 u N hguard (finitePart v) hlt.le
      rw [hv] at hσu h5'
      rw [extVisibilityReplace_finitePart_self hlt, hσu, hβe,
        extVisibilityReplace_rep (limitPart_idem β) hj] at h5'
      have h2 : j = finitePart v := by
        have := congrArg finitePart (ofOrd_inj.mp h5')
        rw [finitePart_limitPart_add_nat, finitePart_limitPart_add_nat] at this
        exact this
      exact ⟨v, by rw [← hu]; exact hv, h2.symm⟩
    · exfalso
      have hvis : SelfVis N u := by rw [hv, selfVis_ofOrd_iff]; exact hge
      have h5' := h5 u N hguard N le_rfl
      rw [evr_eq_self_of_selfVis hvis, hσu] at h5'
      exact hβvis h5'.symm

/-- **A safe predicate**: correctness whenever the guard is active. -/
def Safe (Φ : (D → ExtOrd) → Prop) (j : ℕ) (a C : D) (f : D → ExtOrd) : Prop :=
  Guard j a C f → Φ f

/-- **Safe predicates are preserved by faithful transformation** whenever the underlying
predicate is: a target guard reflects, source safety gives source correctness, and correctness
transports. -/
theorem Safe.transport {Φ : (D → ExtOrd) → Prop}
    (hΦ : ∀ f f' : D → ExtOrd, TransformsTo grade f f' → Φ f → Φ f') {f f' : D → ExtOrd}
    (h : TransformsTo grade f f') {N j : ℕ} {a C : D} (hC : grade C = N) (ha : grade a ≤ N)
    (hj : j < N) (hs : Safe Φ j a C f) : Safe Φ j a C f' :=
  fun hg => hΦ f f' h (hs (hg.reflect h hC ha hj))

/-- **Top requests**: a marker and a list of requested cells, all of grade at most the cap's. -/
structure TopRequests (D : Type*) (grade : D → ℕ) where
  /-- The threshold. -/
  N : ℕ
  /-- The cap cell, of grade `N`. -/
  cap : D
  cap_grade : grade cap = N
  /-- The trigger cell. -/
  trigger : D
  /-- The marker cell. -/
  marker : D
  marker_grade_le : grade marker ≤ N
  /-- The requested top cells. -/
  tops : List D
  top_grade_le : ∀ y ∈ tops, grade y ≤ N

/-- **Top correctness**: under a nonbottom trigger, the capped marker is at most every requested
capped coordinate. -/
def TopRequests.Correct (T : TopRequests D grade) (f : D → ExtOrd) : Prop :=
  f T.trigger ≠ ⊥ → ∀ y ∈ T.tops, min (f T.marker) (f T.cap) ≤ min (f y) (f T.cap)

/-- Top correctness is preserved by faithful transformation. -/
theorem TopRequests.Correct.transport {T : TopRequests D grade} {f f' : D → ExtOrd}
    (h : TransformsTo grade f f') (hc : T.Correct f) : T.Correct f' := by
  obtain ⟨g, σ, hanti, hsv, hbot, hmono, h5, hq⟩ := h
  intro ht' y hy
  have ht : f T.trigger ≠ ⊥ := by
    intro h0
    apply ht'
    rw [hq, h0, hbot]
    exact min_eq_left bot_le
  rw [capped_transform hanti hmono hq T.cap_grade T.marker_grade_le,
    capped_transform hanti hmono hq T.cap_grade (T.top_grade_le y hy)]
  exact min_le_min (hmono (hc ht y hy)) le_rfl

/-- The guard is closed under pointwise minimum. -/
theorem guard_min {j : ℕ} {a C : D} {f g : D → ExtOrd} (hf : Guard j a C f) (hg : Guard j a C g) :
    Guard j a C (fun d => min (f d) (g d)) := by
  obtain ⟨δ, hδ, hδj⟩ := hf
  obtain ⟨ε, hε, hεj⟩ := hg
  have e : min (min (f a) (g a)) (min (f C) (g C)) = min (min (f a) (f C)) (min (g a) (g C)) :=
    min_min_min_comm _ _ _ _
  rcases le_total (min (f a) (f C)) (min (g a) (g C)) with hle | hle
  · exact ⟨δ, by rw [e, min_eq_left hle, hδ], hδj⟩
  · exact ⟨ε, by rw [e, min_eq_right hle, hε], hεj⟩

/-- The complement of the guard is closed under pointwise minimum. -/
theorem not_guard_min {j : ℕ} {a C : D} {f g : D → ExtOrd} (hf : ¬ Guard j a C f)
    (hg : ¬ Guard j a C g) : ¬ Guard j a C (fun d => min (f d) (g d)) := by
  rintro ⟨δ, hδ, hδj⟩
  have e : min (min (f a) (g a)) (min (f C) (g C)) = min (min (f a) (f C)) (min (g a) (g C)) :=
    min_min_min_comm _ _ _ _
  rw [e] at hδ
  rcases le_total (min (f a) (f C)) (min (g a) (g C)) with hle | hle
  · rw [min_eq_left hle] at hδ
    exact hf ⟨δ, hδ, hδj⟩
  · rw [min_eq_right hle] at hδ
    exact hg ⟨δ, hδ, hδj⟩

end Guard

/-! ## Two-labelling readback at a selected controller -/

section Readback

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- **Selecting a top controller**: ordinary availability at a top-labelled cap toward an index
where the cap's grade occurs supplies a controller labelled `⊤`. -/
theorem select_top_controller {q : Cell D → ExtOrd} (hq : RespectsSemantics sem q) (C Xi₀ : Cell D)
    (hs : D.scope C ⊆ D.scope Xi₀) (hg : D.grade C = D.grade Xi₀) (hC : q C = ⊤) :
    ∃ Θ : Cell D, D.cell Θ = D.cell Xi₀ ∧ q Θ = ⊤ := by
  obtain ⟨Θ, hΘ, hle⟩ := hq.availability C Xi₀ hs hg
  exact ⟨Θ, hΘ, top_le_iff.mp (hC ▸ hle)⟩

/-- **The two-labelling readback at a selected controller.**  Two labellings respect the same
rows: `q` (ordinary) and `s` (stable).  At a controller `Θ` labelled `⊤` by `q`, whose row is safe
for the combined proper/top correctness, and at which the stable capped target is guarded, the
ordinary labelling satisfies both correctness predicates. -/
theorem guarded_readback_at {q s : Cell D → ExtOrd} (hq : RespectsSemantics sem q)
    (hs : RespectsSemantics sem s) (Θ : Cell D) (hΘ : q Θ = ⊤)
    (R : FiniteReferenceData (D.below (D.cell Θ)) fun d => D.grade d.1)
    (T : TopRequests (D.below (D.cell Θ)) fun d => D.grade d.1) {j : ℕ} (hj : j < T.N)
    (hsafe : Safe (fun f => R.Correct f ∧ T.Correct f) j T.marker T.cap (sem.E Θ))
    (hguard : Guard j T.marker T.cap (fun d => min (s d.1) (s Θ))) :
    R.Correct (fun d => q d.1) ∧ T.Correct (fun d => q d.1) := by
  have hrow : Guard j T.marker T.cap (sem.E Θ) :=
    hguard.reflect (hs.locality Θ) T.cap_grade T.marker_grade_le hj
  obtain ⟨hR, hT⟩ := hsafe hrow
  have e : (fun d : D.below (D.cell Θ) => min (q d.1) (q Θ)) = fun d => q d.1 := by
    funext d
    rw [hΘ, min_eq_left le_top]
  have hR' := hR.transport (hq.locality Θ)
  have hT' := hT.transport (hq.locality Θ)
  rw [e] at hR' hT'
  exact ⟨hR', hT'⟩

/-- Reading a proper request from correctness at a top-labelled cap: the requested label is the
visibility replacement of the representative's label. -/
theorem read_proper {D' : Type*} {grade : D' → ℕ} {R : FiniteReferenceData D' grade}
    {f : D' → ExtOrd} (hc : R.Correct f) (ht : f R.trigger ≠ ⊥) (hcap : f R.cap = ⊤)
    {r : FiniteRequest D'} (hr : r ∈ R.requests) :
    f r.cell = extVisibilityReplace (f (R.rep r.block)) R.N r.offset := by
  have h := hc ht r hr
  rw [hcap, min_eq_left le_top, min_eq_left le_top] at h
  exact h

/-- Reading a top request from top correctness at a top-labelled cap and marker. -/
theorem read_top {D' : Type*} {grade : D' → ℕ} {T : TopRequests D' grade} {f : D' → ExtOrd}
    (hc : T.Correct f) (ht : f T.trigger ≠ ⊥) (hcap : f T.cap = ⊤) (hmark : f T.marker = ⊤)
    {y : D'} (hy : y ∈ T.tops) : f y = ⊤ := by
  have h := hc ht y hy
  rw [hcap, hmark, min_self, min_eq_left le_top] at h
  exact top_le_iff.mp h

end Readback

end VaughtConjecture.Knight
