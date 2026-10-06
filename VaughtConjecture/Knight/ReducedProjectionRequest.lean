/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReductReferenceContext
public import VaughtConjecture.Knight.EntailmentDomainCashout

/-! # One requested reduced projection over the actual context: what the request forces

Working backwards from **one** requested reduced projection `P` (a stage-`β` one-point type over
the root `t`), over the model-produced reference context `C` (arbitrary arity `C.m` and scheme
`C.p₀.scheme`), reduced at a limit `β` (`Knight/ReductReferenceContext.lean`).  The request is
served by an extension domain `D` on `C.m + 1` points together with reduced projected
correctness: every relevant coface `q` of the reduced context with domain `D` satisfies
`typeMap (onePointProj C.proj) q = some P`.  This module identifies what that target forces,
before any rows are chosen.

**1. The required domain and visible face** (`face_of_typeMap_eq_some`,
`typeMap_eq_some_iff_labels`): a projection to `P` along `f` exists only if the face
`univ.image f` is visible in the domain and the domain restricts *as a domain with semantics* to
`P.scheme` there — the request pins `D`'s plan on the request face and the rows of every cell on
it, not just labels.  Given that, projected correctness is exactly the cellwise statement: every
cell of the face reads `P`'s label at the corresponding cell (`toCell`).  **Geometry**
(`exists_pivot_outside_root`): if the request face is proper, the domain's plan has pivots
`last` and an old point `b` outside the root, and `univ.erase b` is a visible face of the
**context's own plan** — a necessary condition on the context, read off `IsPlan.pivot_pair`.

**2. Exact below `β`, at least `β` above** (`truncExt_eq_iff_of_bound`, `reduced_label_iff`):
a stage-`β` request label is either `< β` or `⊤`; an upstairs coface meets it after reduction
exactly when its label is literally the requested value (the `< β` case) or is **at least `β`**
(the `⊤` case).  So the request splits its cells into exact requirements and lower-bound
requirements, and the block-`β` representative (which reduces to `⊤`) certifies only the latter;
exact low readback must go through genuinely lower representatives (`reduct_rep_exact`).

**3. What follows from the realized context** (`projection_root_face`,
`request_root_compatible`): for every coface of the reduced context, the root part of its
projection is the realized reduced root — the labels of the request's cells on the root face are
forced by the context alone, whatever `D` is, and a request whose root face is not the reduced
root is unservable.  The cells containing the fresh point are the only ones that need the
mechanism, and none of them follows from the reference data without rows: the reference data
constrain labellings only through the controller rows that transform onto them.

## The audit: the smallest legal extension, and where it stops

The smallest candidate is a one-point extension of `C.p₀.scheme` whose plan is the step with
pivots `last` and `castSucc b` (`IsPlan.step`): the pushed context plan on the old face, a plan
`R` on `univ.erase (castSucc b)` containing the request face with the request's plan and
agreeing with the context's plan on `(univ.erase last).erase (castSucc b)`, and the full domain.
Its cells are the old cells (old rows, by the face equation), the request-face cells (the
request's rows, by the face equation), and one cell per remaining graded pair of the plan —
in particular the full-scope controllers `(univ, k)`.

**Geometry first.**  `R` is an amalgam of two support plans along the common face
`univ.image C.proj`.  The library's one-point extension (`isPlan_extend_one`,
`Plan.extendOnePlan`) adds a point along a fixed branch; the amalgam of a whole plan with a
prescribed one-point plan over one of its visible faces is `IsPlan.attach_one_over_face`
(`AmalgamationPlan/PlanAttachment.lean`), from the two plans and their agreement on the shared
face — so the geometry is supplied from its stated premises, and the pivot lemma above is a
necessary-condition check on the result, not a further hypothesis.  Instantiating it on the
actual context and request is the next step; it is verified before rows.

**Then the rows.**  With the plan in hand, every old and request-face row is fixed by the two
face equations, and the **first genuinely new obligation** is the rows of the new cells — the
full-scope controllers and any new mixed proper scopes, possibly several cells at one graded
index (one cell per remaining index is index completeness, not semantic adequacy): they must be
consistent with both the context's rows and the request's rows (mixed locality across the two
faces), correct for the reference data (equality form on the exact requests, inequality form on
the lower-bound requests) so that `ReadbackInputs.readback` and `CutoffBound.readback_top` read
every fresh cell back, and bountiful for **every** permitted labelling of the old and request
faces — the quantifier that fixed-inventory constructions discharged by hand (the coupled
semantics' no-go and single-row repair) and that no theorem in the repository discharges for a
domain given only as a scheme with rows.  Nothing here replaces
the context by the fixed coupled example, demands upstairs uniqueness, or adds a supply record.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization AmalgamationPlan Value ExtOrd
open CellScheme.restrictFace (toCell)

universe w

/-! ## Exact below `β`, at least `β` above -/

section LabelSplit

variable {β : Ordinal.{0}}

/-- A stage-`β` label `y` is met by the reduction of `x` exactly when `y = ⊤` and `x ≥ β`, or
`y < β` and `x = y`. -/
theorem truncExt_eq_iff_of_bound {x y : ExtOrd} (hy : y < ofOrd β ∨ y = ⊤) :
    truncExt β x = y ↔ (y = ⊤ ∧ ofOrd β ≤ x) ∨ (y < ofOrd β ∧ x = y) := by
  rcases hy with hy | rfl
  · have hne : y ≠ ⊤ := ne_top_of_lt hy
    constructor
    · intro h
      right
      refine ⟨hy, ?_⟩
      rcases ExtOrd.cases x with rfl | rfl | ⟨δ, rfl⟩
      · rw [truncExt_bot] at h; exact h
      · rw [truncExt_top] at h; exact absurd h.symm hne
      · rcases lt_or_ge δ β with hδ | hδ
        · rwa [truncExt_ofOrd_of_lt hδ] at h
        · rw [truncExt_ofOrd_of_le hδ] at h; exact absurd h.symm hne
    · rintro (⟨h, -⟩ | ⟨-, rfl⟩)
      · exact absurd h hne
      · exact truncExt_eq_self_of_lt hy
  · constructor
    · intro h
      left
      refine ⟨rfl, ?_⟩
      rcases ExtOrd.cases x with rfl | rfl | ⟨δ, rfl⟩
      · rw [truncExt_bot] at h; exact absurd h bot_ne_top
      · exact le_top
      · rcases lt_or_ge δ β with hδ | hδ
        · rw [truncExt_ofOrd_of_lt hδ] at h; exact absurd h (ofOrd_ne_top δ)
        · exact ofOrd_le_ofOrd.mpr hδ
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact truncExt_eq_top_of_le h
      · exact absurd h not_top_lt

/-- **The label split on a coface**: the reduced label of an upstairs type meets a stage-`β`
request label exactly when it is the requested value (below `β`) or at least `β` (requested
`⊤`). -/
theorem reduced_label_iff {α : Ordinal.{0}} (hβ : Order.IsSuccLimit β) (hβα : β ≤ α) {m : ℕ}
    (q : S α m) (d : Cell q.scheme.scheme) {y : ExtOrd} (hy : y < ofOrd β ∨ y = ⊤) :
    (reduceType hβ hβα q).label d = y ↔
      (y = ⊤ ∧ ofOrd β ≤ q.label d) ∨ (y < ofOrd β ∧ q.label d = y) := by
  rw [reduceType_label]
  exact truncExt_eq_iff_of_bound hy

end LabelSplit

/-! ## The required domain and visible face -/

section RequiredFace

variable {γ : Ordinal.{0}} {k m : ℕ}

/-- **The requested projection forces the domain**: a projection along `f` to `P` exists only if
the face `univ.image f` is visible in the domain and the domain (with its rows) restricts to
`P`'s domain there. -/
theorem face_of_typeMap_eq_some (f : Fin k ↪ Fin m) {q : S γ m} {P : S γ k}
    (h : typeMap f q = some P) :
    ∃ hv : Finset.univ.image f ∈ q.scheme.scheme.plan, q.scheme.restrictFace f hv = P.scheme := by
  have hv : Finset.univ.image f ∈ q.scheme.scheme.plan :=
    (typeMap_isSome_iff f q).mp (by rw [h]; rfl)
  refine ⟨hv, ?_⟩
  rw [typeMap_eq_some f q hv] at h
  exact congrArg StageType.scheme (Option.some_injective _ h)

/-- **Projected correctness, cellwise**: once the face is visible and the domains match,
`typeMap f q = some P` says exactly that every cell of the face reads `P`'s label at the
corresponding cell. -/
theorem typeMap_eq_some_iff_labels (f : Fin k ↪ Fin m) (q : S γ m) (P : S γ k)
    (hv : Finset.univ.image f ∈ q.scheme.scheme.plan)
    (hs : q.scheme.restrictFace f hv = P.scheme) :
    typeMap f q = some P ↔
      ∀ i : Cell (q.scheme.restrictFace f hv).scheme,
        q.label (toCell q.scheme.scheme f hv i) = P.label (SemScheme.castCell hs i) := by
  rw [typeMap_eq_some f q hv, Option.some_inj]
  constructor
  · rintro rfl i
    rfl
  · intro h
    obtain ⟨Ps, Pl, Pb, Pr⟩ := P
    dsimp only at hs h
    subst hs
    exact StageType.ext rfl (heq_of_eq (funext fun i => h i))

end RequiredFace

/-! ## The root part of every projection is the realized reduced root -/

section RootPart

variable {M : Type w} {α β : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} (C : ReferenceContext R t reqs) (hβ : β ≤ α)

theorem castSucc_trans_onePointProj {k m : ℕ} (e : Fin k ↪ Fin m) :
    Fin.castSuccEmb.trans (onePointProj e) = e.trans Fin.castSuccEmb :=
  Function.Embedding.ext fun i => onePointProj_castSucc e i

/-- **Realized cofaces of the reduced context are cofaces** (exact consistency of the reduct). -/
theorem ReferenceContext.reduct_isCoface_of_eval (hM : R.IsModel) {y : M}
    (hy : y ∉ Set.range C.ctx) {q' : S β.1 (C.m + 1)}
    (hq' : (R.reduct hβ).eval (snoc C.ctx y hy) = some q') : IsCoface (C.reducedType hβ) q' :=
  isCoface_of_consistent (hM.consistent_reduct hβ) (C.reduct_eval_ctx hβ) hq'

/-- **The root part of any projection is the realized reduced root**: for every coface `q'` of
the reduced context and every projection `P'` of it along `onePointProj C.proj`, the initial
face of `P'` is the reduction of the root's type.  The labels of a request on the root face are
thus forced by the context alone, whatever the extension domain. -/
theorem ReferenceContext.projection_root_face (hM : R.IsModel) {p : S α.1 n}
    (hp : R.eval t = some p) {q' : S β.1 (C.m + 1)} (hc : IsCoface (C.reducedType hβ) q')
    {P' : S β.1 (n + 1)} (hP' : typeMap (onePointProj C.proj) q' = some P') :
    typeMap Fin.castSuccEmb P' = some (reduceType β.2 hβ p) := by
  rw [typeMap_trans _ _ q' P' hP', castSucc_trans_onePointProj,
    ← typeMap_trans _ _ q' _ hc]
  exact C.reduct_root_face hβ hM hp

/-- **A servable request has the reduced root as its initial face**: if some coface of the
reduced context projects to `P`, then `P`'s root face is the reduction of the root's type.  A
request violating this is unservable by any extension domain. -/
theorem ReferenceContext.request_root_compatible (hM : R.IsModel) {p : S α.1 n}
    (hp : R.eval t = some p) {P : S β.1 (n + 1)}
    (h : ∃ q' : S β.1 (C.m + 1), IsCoface (C.reducedType hβ) q' ∧
      typeMap (onePointProj C.proj) q' = some P) :
    typeMap Fin.castSuccEmb P = some (reduceType β.2 hβ p) := by
  obtain ⟨q', hc, hP⟩ := h
  exact C.projection_root_face hβ hM hp hc hP

end RootPart

/-! ## Geometry: the request face forces a pivot of the context's plan outside the root -/

section Geometry

variable {m : ℕ}

theorem image_castSuccEmb_univ :
    (Finset.univ : Finset (Fin m)).image Fin.castSuccEmb =
      (Finset.univ : Finset (Fin (m + 1))).erase (Fin.last m) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true,
    Fin.castSuccEmb_apply]
  exact Fin.exists_castSucc_eq

theorem erase_erase_eq_image_erase (b : Fin m) :
    ((Finset.univ : Finset (Fin (m + 1))).erase (Fin.last m)).erase (Fin.castSucc b) =
      ((Finset.univ : Finset (Fin m)).erase b).image Fin.castSuccEmb := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_image,
    Fin.castSuccEmb_apply]
  constructor
  · rintro ⟨hxb, hxl⟩
    obtain ⟨y, rfl⟩ := Fin.exists_castSucc_eq.mpr hxl
    exact ⟨y, fun e => hxb (e ▸ rfl), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨fun e => hy (Fin.castSucc_injective _ e), (Fin.castSucc_lt_last y).ne⟩

/-- **The request face forces a pivot of the context's plan outside the root**: if a domain on
`m + 1` points extends `p₀`'s domain and the request face `univ.image (onePointProj e)` is a
proper visible face, then the plan's pivots are `last` and an old point `b` outside the range of
`e`, and `univ.erase b` is a visible face of the context's own plan. -/
theorem exists_pivot_outside_root {k : ℕ} (e : Fin k ↪ Fin m) {γ : Ordinal.{0}} {p₀ : S γ m}
    {D : SemScheme (m + 1)} (hD : ExtendsDomain p₀ D) (hm : 1 ≤ m)
    (hF : Finset.univ.image (onePointProj e) ∈ D.scheme.plan)
    (hne : Finset.univ.image (onePointProj e) ≠ Finset.univ) :
    ∃ b : Fin m, b ∉ Set.range e ∧ Finset.univ.erase b ∈ p₀.scheme.scheme.plan := by
  classical
  have hcard : 2 ≤ (Finset.univ : Finset (Fin (m + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨a, b, -, -, hab, hmax, hboth, hfull⟩ := D.scheme.isPlan.pivot_pair hcard
  have hO : (Finset.univ : Finset (Fin (m + 1))).erase (Fin.last m) ∈ D.scheme.plan := by
    rw [← image_castSuccEmb_univ]; exact hD.visible
  have hlast : Fin.last m = a ∨ Fin.last m = b :=
    (hmax (Fin.last m) (Finset.mem_univ _)).mp hO
  have hlastF : Fin.last m ∈ Finset.univ.image (onePointProj e) :=
    Finset.mem_image.mpr ⟨Fin.last k, Finset.mem_univ _, onePointProj_last e⟩
  -- the other pivot `c`
  obtain ⟨c, hcl, hcmem, hcF⟩ : ∃ c : Fin (m + 1), c ≠ Fin.last m ∧
      ((Finset.univ : Finset (Fin (m + 1))).erase (Fin.last m)).erase c ∈ D.scheme.plan ∧
      c ∉ Finset.univ.image (onePointProj e) := by
    rcases hlast with rfl | rfl
    · refine ⟨b, hab.symm, hboth, fun hbF => hne (hfull _ hF hlastF hbF)⟩
    · refine ⟨a, hab, ?_, fun haF => hne (hfull _ hF haF hlastF)⟩
      rwa [Finset.erase_right_comm]
  obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.mpr hcl
  refine ⟨b', ?_, ?_⟩
  · rintro ⟨j, hj⟩
    apply hcF
    exact Finset.mem_image.mpr ⟨Fin.castSucc j, Finset.mem_univ _,
      by rw [onePointProj_castSucc, hj]⟩
  · rw [erase_erase_eq_image_erase] at hcmem
    have := (CellScheme.mem_restrictFace_plan D.scheme Fin.castSuccEmb hD.visible).mpr hcmem
    have hplan : (D.scheme.restrictFace Fin.castSuccEmb hD.visible).plan =
        p₀.scheme.scheme.plan :=
      congrArg (fun X : SemScheme m => X.scheme.plan) hD.restrict
    rw [hplan] at this
    exact this

end Geometry

end VaughtConjecture.Knight
