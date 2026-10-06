/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReferenceContext
public import VaughtConjecture.Knight.ReductModel

/-! # The realized reference context in the reduct: a top reference from the model clauses

**The question.**  The finite-cut readback (`FiniteReferenceData.CutoffBound.readback_top`)
needs, after reduction to a lower limit stage `β`, a *top* reference: a cap whose label becomes
`⊤` and a block-`β` representative.  Is that reference obtainable inside an actual model, over
an actually realized root tuple, from the model clauses alone?  This module answers yes, on the
context and arity that the model produces — **not** on the fixed three-point protected type of
the coupled construction, with which nothing here is identified.

**The construction.**  Start from a model `R` at stage `α`, a realized root `t` with type `p`,
and a limit stage `β < α`.  The single block request `blockRequest β` (block `β`, offset `0`) is
admissible (`β` is a limit below `α`), so `exists_referenceContext` produces an enlarged realized
context `C` whose cap dominates `β` (`exists_referenceContext_block`).  In the reduct
`R.reduct hβ` (a model, `IsModel.reduct`):

* the context stays realized, with the reduced type `C.reducedType hβ` (`reduct_eval_ctx`);
* the root stays realized at the same coordinates (`reduct_eval_root`), and it is literally the
  `C.proj`-face of the reduced context (`reduct_root_face`, by exact consistency of the reduct);
* **the cap becomes `⊤`** (`reduct_cap_top`), with its grade and its cell retained — reduction
  fixes schemes (`reducedType_scheme`, `reduct_cap_grade`);
* labels below `β` are exact (`reduct_label_exact`);
* **the requested block-`β` representative also becomes `⊤`** (`reduct_rep_top`), whereas a
  representative of a genuinely lower block stays exact at `μ + j` (`reduct_rep_exact`, since a
  limit absorbs finite offsets).  The two are kept apart: after reduction the block-`β`
  reference carries no finite information, only the lower bound `≥ β` that `readback_top` reads.

**Realized extensions after reduction are reductions of realized extensions**
(`reduct_coface_lift`): a coface of the reduced context that the reduct *realizes* over the
context tuple is the reduction of a coface of `C.p₀` that `R` realizes over the same tuple, with
the same domain (realized cofaces only: the lift goes through the model's evaluation).  The
target this serves is **reduced projected correctness**: for every such coface `q` and the
requested reduced type `P_β`, `typeMap f (reduceType β q) = some P_β`.  Full upstairs
correctness — Lemma 10.1.1 at stage `α` — is *sufficient* for it through the lift, but stronger
than necessary: distinct upstairs extensions can have identical whole reductions
(`MixedReferenceTypeReadback.distinct_cofaces_same_reduction`, #339), and equality of the
projected types is needed after reduction, not before.

## The gap to an entailment domain over this context (audit)

An `EntailmentCertificate` over `C.ctx` needs an extension domain `D*` of `C.p₀.scheme` on
`C.m + 1` points with a respecting labelling `q'` extending `C.p₀`'s labels, and Lemma 10.1.1
correctness: every coface of `C.p₀` with domain `D*` and the `⊥`-pattern of `q'` projects to the
requested type.  For the finite fragment that correctness is `ReadbackInputs.readback`, whose
inputs split into two halves:

* the **context half** — cap and representatives with their labels, offsets below the threshold,
  representatives under the cap, non-successor blocks — is exactly what `ReferenceContext`
  supplies and what this module shows survives reduction as a top reference;
* the **domain half** — the reference cells *inside* `D*` read through the face map
  `ExtendsDomain.cellOf`, a trigger of grade `≤ C.m` with the pattern active, a controller at
  `(univ, N)` (completeness of `D*`), and **correctness of every `(univ, N)` controller row**
  for that reference data (`rows_correct`, Def. 8.3.2's thinning; in the inequality form
  `CutoffBound` for the `⊤`-cells after reduction).

Controller-row correctness with `D*`'s legality (complete, coded, consistent, and bountiful
*for every permitted labelling*, so that `IsModel.bottomPattern` applies) is a **sufficient
construction route**, not a proved necessary interface: `ReadbackInputs.readback` supplies
cell-label equations, and equality of the whole projected type additionally needs the
identification of the projection's domain and coverage of all its labels; the parameter-based
uniqueness proof of `MixedReferenceTypeReadback` (#339) is another route, on the fixed domain.
The model supplies a legal context scheme `C.p₀.scheme` (arity `C.m`), its respecting
labelling `C.p₀`, and the reference data, but no fixed-inventory presentation.  The **missing
producer** constructs a legal extension of that context **enforcing the requested reduced
projection**; the existing generic coface theorems already extend labellings once such a legal
extension domain is supplied.  The compiled legal domains with a readback (the assembled scheme,
its four-point duplication, the repaired coupled domain `semSchemeR`, and the readback tests on
it) are fixed-inventory presentations.  That is the domain mismatch, and it is not closed here:
no supply field is added for it and no further numerical example is begun.  **The next target** is
reduced projected correctness over the actual context — not full upstairs correctness, and not
identification with the fixed three-point protected type.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd

universe w

/-! ## Truncation at a limit: exact below, `⊤` at and above -/

section Trunc

variable {β : Ordinal.{0}}

theorem truncExt_eq_top_of_lt {x : ExtOrd} (h : ofOrd β < x) : truncExt β x = ⊤ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨δ, rfl⟩
  · exact absurd h not_lt_bot
  · exact truncExt_top β
  · exact truncExt_ofOrd_of_le (ofOrd_lt_ofOrd.mp h).le

theorem truncExt_eq_top_of_le {x : ExtOrd} (h : ofOrd β ≤ x) : truncExt β x = ⊤ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨δ, rfl⟩
  · exact absurd h (not_ofOrd_le_bot β)
  · exact truncExt_top β
  · exact truncExt_ofOrd_of_le (ofOrd_le_ofOrd.mp h)

theorem truncExt_eq_self_of_lt {x : ExtOrd} (h : x < ofOrd β) : truncExt β x = x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨δ, rfl⟩
  · exact truncExt_bot β
  · exact absurd h not_top_lt
  · exact truncExt_ofOrd_of_lt (ofOrd_lt_ofOrd.mp h)

end Trunc

/-! ## The block request at a lower limit stage -/

variable {M : Type w} {α β : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}

/-- The single block request at the limit stage `β`: block `β`, offset `0`. -/
def blockRequest (β : LimitStage) : BlockRequest := ⟨β.1, 0⟩

theorem blockRequest_block (β : LimitStage) : (blockRequest β).block = β.1 := rfl

theorem blockRequest_value (β : LimitStage) : (blockRequest β).value = β.1 := by
  change β.1 + ((0 : ℕ) : Ordinal.{0}) = β.1
  rw [Nat.cast_zero, add_zero]

/-- A lower limit stage is an admissible block: a non-successor below the stage. -/
theorem blockRequest_admissible (hβ : β < α) :
    ∀ r ∈ [blockRequest β], Value.IsNonSuccessor r.block ∧ r.block < α.1 := by
  intro r hr
  rw [List.mem_singleton] at hr
  subst hr
  exact ⟨Or.inr β.2, hβ⟩

/-- **A reference context for the block request at `β` exists** in every model, over every
realized root tuple. -/
theorem exists_referenceContext_block (hM : R.IsModel) {p : S α.1 n} (hp : R.eval t = some p)
    (hβ : β < α) : Nonempty (ReferenceContext R t [blockRequest β]) :=
  exists_referenceContext hM p hp _ (blockRequest_admissible hβ)

/-! ## The context in the reduct -/

namespace ReferenceContext

variable {reqs : List BlockRequest} (C : ReferenceContext R t reqs) (hβ : β ≤ α)

/-- The context's type in the reduct to `β`. -/
noncomputable def reducedType : S β.1 C.m := reduceType β.2 hβ C.p₀

theorem reducedType_scheme : (C.reducedType hβ).scheme = C.p₀.scheme := rfl

theorem reducedType_label (d : Cell C.p₀.scheme.scheme) :
    (C.reducedType hβ).label d = truncExt β.1 (C.p₀.label d) := rfl

/-- **The enlarged context remains realized** in the reduct, with the reduced type. -/
theorem reduct_eval_ctx : (R.reduct hβ).eval C.ctx = some (C.reducedType hβ) := by
  rw [Realization.reduct_eval, C.eval_ctx]; rfl

/-- **The root remains realized** in the reduct, at the same coordinates. -/
theorem reduct_eval_root {p : S α.1 n} (hp : R.eval t = some p) :
    (R.reduct hβ).eval t = some (reduceType β.2 hβ p) := by
  rw [Realization.reduct_eval, hp]; rfl

/-- **The root is literally the `proj`-face of the reduced context**: by exact consistency of
the reduct, the reduced root type is the partial restriction of the reduced context type along
`C.proj`, whose tuple is `t` itself (`C.proj_ctx`). -/
theorem reduct_root_face (hM : R.IsModel) {p : S α.1 n} (hp : R.eval t = some p) :
    typeMap C.proj (C.reducedType hβ) = some (reduceType β.2 hβ p) := by
  have h := hM.consistent_reduct hβ C.ctx (C.reducedType hβ) C.proj (C.reduct_eval_ctx hβ)
  rw [C.proj_ctx, reduct_eval_root hβ hp] at h
  exact h.symm

/-- **The cap becomes `⊤`** once the block request at `β` is among the requests. -/
theorem reduct_cap_top (h : blockRequest β ∈ reqs) : (C.reducedType hβ).label C.capBase = ⊤ := by
  have := C.cap_dom _ h
  rw [blockRequest_value] at this
  exact truncExt_eq_top_of_lt this

/-- The cap keeps its grade (reduction fixes schemes). -/
theorem reduct_cap_grade : (C.reducedType hβ).scheme.scheme.grade C.capBase = C.N := C.cap_grade

/-- **Labels below the cut are exact.** -/
theorem reduct_label_exact {d : Cell C.p₀.scheme.scheme} (hd : C.p₀.label d < ofOrd β.1) :
    (C.reducedType hβ).label d = C.p₀.label d :=
  truncExt_eq_self_of_lt hd

/-- **The block-`β` representative also becomes `⊤`**: its label `β + j` is at least `β`. -/
theorem reduct_rep_top (h : blockRequest β ∈ reqs) :
    (C.reducedType hβ).label (C.repBase β.1) = ⊤ := by
  have := C.rep_label _ h
  rw [blockRequest_block] at this
  rw [reducedType_label, this]
  exact truncExt_ofOrd_of_le (le_add_of_nonneg_right zero_le)

/-- **A genuinely lower representative stays exact**: for a requested block below `β`, the
representative's label `μ + j` is still below `β` (a limit absorbs finite offsets), so it is
read exactly in the reduct. -/
theorem reduct_rep_exact {r : BlockRequest} (hr : r ∈ reqs) (hlow : r.block < β.1) :
    (C.reducedType hβ).label (C.repBase r.block) = ofOrd (r.block + C.repOff r.block) := by
  rw [reducedType_label, C.rep_label r hr]
  exact truncExt_ofOrd_of_lt (add_nat_lt_stage (α := β) hlow _)

/-! ## Extensions after reduction are reductions of extensions -/

/-- **Every coface of the reduced context *realized* by the reduct over the context tuple is the
reduction of a coface of `C.p₀` realized by `R`, with the same domain** (realized cofaces only).
Hence reduced projected correctness — `typeMap f (reduceType β q) = some P_β` for the realized
cofaces — follows from Lemma 10.1.1 correctness at stage `α`; that upstairs correctness is
sufficient, not necessary (#339: distinct upstairs extensions with identical whole reductions). -/
theorem reduct_coface_lift (hM : R.IsModel) {y : M} (hy : y ∉ Set.range C.ctx)
    {q' : S β.1 (C.m + 1)} (hq' : (R.reduct hβ).eval (snoc C.ctx y hy) = some q') :
    ∃ q : S α.1 (C.m + 1), R.eval (snoc C.ctx y hy) = some q ∧ IsCoface C.p₀ q ∧
      reduceType β.2 hβ q = q' ∧ q.scheme = q'.scheme := by
  obtain ⟨q, hq, rfl⟩ := eval_reduct_eq_some hβ hq'
  refine ⟨q, hq, ?_, rfl, rfl⟩
  have h := hM.consistent (snoc C.ctx y hy) q Fin.castSuccEmb hq
  have e : Fin.castSuccEmb.trans (snoc C.ctx y hy) = C.ctx := by
    ext i
    exact snoc_apply_castSucc C.ctx y hy i
  rw [e, C.eval_ctx] at h
  exact h.symm

end ReferenceContext

end VaughtConjecture.Knight
