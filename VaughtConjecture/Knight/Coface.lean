/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Domain

/-! # Cofaces over a given extension domain: (a)(i)/(a)(ii) nonemptiness from bountifulness

PR 2 of #41 (the *fixed-domain coface experiment*, `docs/EXPERIMENTS.md` B4).  Def. 3.2.1(4)(a)
asks, for a realized `p : S α n` and a domain `D` on `n+1` with `D⟨n,n⟩ = dom p`
(`ExtendsDomain p D`), that some coface of `p` **with domain `D`** be realized.  The paper
obtains cofaces through Prop. 4.3.23 (Cor. 4.3.22 / Lemma 4.3.21 / Lemma 4.3.19, the §4.3
completion — `docs/CONCORDANCE.md` §4, proof-gap), which also *produces* the extension domain.
This module shows that **over a given extension domain no §4.3 machinery is needed**: the
bountifulness of `D` itself (Def. 2.5.14, a field of `SemScheme`) at the cutoff `γ = −∞` already
yields a coface of `p` on `D`.

## The argument

Write `f = ι_{n,n+1} = Fin.castSuccEmb`, `C = f[n] ⊆ n+1` for the old face, and `n = m+1 ≥ 1`.

* The cells of `dom p = D⟨n,n⟩` are the lower set `D⟨C, m+1⟩ = D.below (C, m+1)` of `D`
  (`CellScheme.restrictFace.belowEquiv`: the restricted scheme *is* that lower set, and every
  restricted cell has grade `≤ m+1`), and the whole of `D` is the lower set `D⟨n+1, m+2⟩`
  (`StageType.gradedLe_univ_succ`).  Both pairs lie in `P̂` (`hvis`, `univ_succ_mem_gradedPlan`)
  and `⟨C, m+1⟩ ≺ ⟨n+1, m+2⟩` strictly.
* `p.label`, transported to `D⟨C, m+1⟩`, respects `E⟨C, m+1⟩` (`RespectsSemantics.toBelow`,
  `RespectsSemanticsBelow.of_restrictFace`); any respecting labelling `q₀` of `D` — the row of a
  full-grade cell, Prop. 4.3.24 (`SemScheme.exists_respectsSemantics`) — respects `E⟨n+1, m+2⟩`.
* Apply `D.bountiful` at a cutoff `γ` self-visible at `n+1` (clause 7, `γ = γ ⊔⁺_{n+1} (n+1)`)
  with `(q₀ ∧ γ) ↾ D⟨C,m+1⟩ = p ∧ γ` (clause 8): the conclusion gives `q'` respecting
  `E⟨n+1, m+2⟩`, i.e. `E` (`RespectsSemanticsBelow.toRespects`), with `q' ∧ γ = q₀ ∧ γ` on
  every cell and `q' ↾ D⟨C,m+1⟩ = p.label` **literally**.  This single application is
  `StageType.exists_respects_extends_capped`, the engine of the module.  At `γ = ⊥`
  (`StageType.exists_respects_extends`) clause 7 is `extVisibilityReplace_bot`, clause 8 is
  **automatic** (both sides are `⊥`), and the clause `q' ∧ γ = q₀ ∧ γ` is vacuous and is
  discarded; at the positive cutoff `γ = n+1` (`Knight/ReductModel.lean`, #101) the same
  engine transfers the `−∞`-pattern across truncation of the face.
* Truncate to stage `α` (`StageType.ofRespects`: labels `truncExt α ∘ q'`, respect by
  `RespectsSemantics.truncate`, Lemma 3.1.3).  Truncation does not interfere with the face:
  `p`'s labels are already strictly bounded at `α` (`label_bound`), so `truncExt α` fixes them
  (`truncExt_id_of_bound`), and the restriction of the truncated type to the face is `p`
  (`StageType.isCoface_ofRespects`, via `StageType.ext`).  On the new cells, values `≥ α`
  become `⊤`, as Def. 3.1.2 prescribes.

**Role of truncation, precisely.**  Bountifulness is stated for labellings respecting `E`
with values in `{−∞} ∪ Ord ∪ {∞}` (the paper's `{−∞} ∪ ω₁ ∪ {∞}`; here `ExtOrd`, no stage
bound).  `p.label` is such a labelling — its values `< α` or `⊤` are legitimate labels, and
`StageType.respects` is the same predicate `RespectsSemantics` that bountifulness quantifies
over — so the premise is met by `p` as it stands, **without untruncating**.  Nothing in the
argument requires a preimage of `p` under reduction; the `⊤` labels of `p` are simply extended
by `⊤`-respecting values, and the final truncation fixes them.

**Arity `0`.**  `⟨∅, 0⟩ ∉ P̂` (grades are positive), so bountifulness cannot be applied from the
empty face; but `S α 0` is a singleton (`StageType.subsingleton_zero`), so *any* respecting
labelling of `D` (Prop. 4.3.24) gives a coface of the unique `p : S α 0`.  This is the base
case of Prop. 4.3.23 in the paper, by the same argument.

## Consequences

* `StageType.exists_coface_of_extendsDomain`: `ExtendsDomain p D → ∃ q, q.scheme = D ∧
  IsCoface p q` at every limit stage — the fibre `(S^α ι_{n,n+1})⁻¹(p) ∩ {dom q = D}` is
  nonempty for every extension domain `D` of `dom p`; Prop. 4.3.23 **for a given extension
  domain**, with Cor. 4.3.22 / Lemma 4.3.21 / Lemma 4.3.19 not involved.
* Def. 3.2.1(4)(a)(i): `GenSatFamily D ∩ Coface p ≠ ∅` (`genSatFamily_nonempty`).
* Def. 3.2.1(4)(a)(ii): for every faithful `q'` respecting `D.rows` and extending `p`,
  `BottomPatternFamily D q' ∩ Coface p ≠ ∅` (`bottomPatternFamily_nonempty`): the truncation of
  `q'` itself is the witness, since `truncExt α` preserves and reflects `⊥`
  (`truncExt_eq_bot_iff`) and fixes `p` on the face.  Moreover (a)(i) is the special case of
  (a)(ii) in which the faithful `q'` is produced by bountifulness
  (`StageType.exists_respects_extends`).

What remains of §4.3 for the existence of models (#106) is therefore the **production of
extension domains** for a given `p` on a non-mute domain (exact face recovery) and the
witnesses for clauses (b)/(c) over them — not the (a)-families. -/

@[expose] public section

namespace VaughtConjecture.Knight

open VaughtConjecture.AmalgamationPlan

open Value ExtOrd
open CellScheme.restrictFace (toCell belowEquiv belowEquiv_symm_mk toCell_belowEquiv_symm_val
  pushGraded gradedLe_cell_pushGraded_iff)

/-! ### Respect on the whole scheme versus respect on a lower set -/

section Below

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- A cell scheme over `Fin 0` has no cells (grades are positive and bounded by the size of
the scope). -/
theorem CellScheme.isEmpty_cell_fin0 (C : CellScheme (ι := Fin 0) Finset.univ) :
    IsEmpty (Cell C) :=
  ⟨fun d => by
    have h1 := C.grade_pos d
    have h2 := C.grade_le_card_scope d
    rw [Finset.card_eq_zero.mpr (Finset.eq_empty_of_isEmpty _)] at h2
    omega⟩

end Below

/-! ### Every domain has a respecting labelling (Prop. 4.3.24, before truncation) -/

/-- Every domain on `Fin (n+1)` has a labelling respecting its rows (no stage bound): the row
of a full-grade cell `Σ ∈ D^{A,|A|}`, which respects `E⟨A,|A|⟩ = E` by consistency
(the untruncated half of Prop. 4.3.24, `StageType.ofScheme`). -/
theorem SemScheme.exists_respectsSemantics {n : ℕ} (D : SemScheme (n + 1)) :
    ∃ q : Cell D.scheme → ExtOrd, RespectsSemantics D.rows q :=
  -- Existence alone needs neither a full-grade owner nor consistency.
  ⟨_, RespectsSemantics.bot _⟩

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-! ### The stage type of a respecting labelling -/

/-- The stage type at a limit stage `α` on the domain `D` obtained by reducing a labelling `q'`
respecting the rows of `D` (no stage bound on `q'`): labels `truncExt α ∘ q'` (Def. 3.1.2),
respect by `RespectsSemantics.truncate` (Lemma 3.1.3, reduction half).  `StageType.ofScheme`
is the instance at the row of a full-grade cell. -/
noncomputable def ofRespects (hα : Order.IsSuccLimit α) (D : SemScheme n)
    (q' : Cell D.scheme → ExtOrd) (hq' : RespectsSemantics D.rows q') : S α n where
  scheme := D
  label d := truncExt α (q' d)
  label_bound _ := truncExt_bound α _
  respects := hq'.truncate hα

@[simp] theorem ofRespects_scheme (hα : Order.IsSuccLimit α) (D : SemScheme n)
    (q' : Cell D.scheme → ExtOrd) (hq' : RespectsSemantics D.rows q') :
    (ofRespects hα D q' hq').scheme = D := rfl

@[simp] theorem ofRespects_label (hα : Order.IsSuccLimit α) (D : SemScheme n)
    (q' : Cell D.scheme → ExtOrd) (hq' : RespectsSemantics D.rows q') (d : Cell D.scheme) :
    (ofRespects hα D q' hq').label d = truncExt α (q' d) := rfl

/-- **Truncation does not disturb the face.**  If `q'` respects the rows of an extension domain
`D` of `dom p` and extends `p.label` along the cell map of the initial face (`hD.cellOf`),
then the reduction of `q'` to stage `α` is a coface of `p`: its restriction to the initial
face has the scheme `D⟨n,n⟩ = dom p` (`hD.restrict`) and the labels `truncExt α ∘ p.label =
p.label`, since the labels of `p` are already strictly bounded at `α` (`truncExt_id_of_bound`).
-/
theorem isCoface_ofRespects (hα : Order.IsSuccLimit α) {p : S α n} {D : SemScheme (n + 1)}
    (hD : ExtendsDomain p D) {q' : Cell D.scheme → ExtOrd} (hq' : RespectsSemantics D.rows q')
    (hext : ∀ d, q' (hD.cellOf d) = p.label d) : IsCoface p (ofRespects hα D q' hq') := by
  obtain ⟨Ps, pl, pb, pr⟩ := p
  obtain ⟨hvis, hres⟩ := hD
  dsimp only at hres ⊢
  subst hres
  unfold IsCoface
  rw [typeMap_eq_some _ _ hvis]
  congr 1
  refine StageType.ext rfl (heq_of_eq (funext fun c => ?_))
  have h := hext c
  change truncExt α (q' (toCell D.scheme Fin.castSuccEmb hvis c)) = pl c
  change q' (toCell D.scheme Fin.castSuccEmb hvis c) = pl c at h
  rw [h]
  exact truncExt_id_of_bound (pb c)

/-! ### The core: bountifulness across the initial face at a self-visible cutoff `γ` -/

/-- **Capped bountifulness across the initial face** — the engine of this module (Def. 2.5.14,
lifted to the `S`/`ExtendsDomain` API).  For `p : S α n`, `D` an extension domain of `dom p`,
`q'` a labelling of `D` respecting its rows (no stage bound), and a cutoff `γ` self-visible at
`n + 1` (`γ = γ ⊔⁺_{n+1} (n+1)`, clause 7 of Def. 2.5.14) with `(q' ∧ γ) ↾ dom p = p ∧ γ`
(clause 8), there is a respecting `q''` on `D` with `q'' ∧ γ = q' ∧ γ` on every cell and
`q'' ↾ dom p = p` literally.  For `n = m+1`: `D.bountiful` applied to `⟨C, m+1⟩ ≺ ⟨n+1, m+2⟩`
(`C` the old face; the lower set `D⟨C,m+1⟩` is `dom p` by `belowEquiv`, `D⟨n+1,m+2⟩` is all of
`D`), with `p.label` on the small lower set and `q'` itself on the large one.  For `n = 0` the
face has no cells and `q'' = q'`.

`exists_respects_extends` (B4) is the case `γ = ⊥`, where both premises are automatic;
`exists_respects_extends_of_truncated` (`Knight/ReductModel.lean`, #101) is the case
`γ = n + 1`, where the conclusion is `⊥`-pattern agreement. -/
theorem exists_respects_extends_capped {p : S α n} {D : SemScheme (n + 1)}
    (hD : ExtendsDomain p D) {q' : Cell D.scheme → ExtOrd} (hq' : RespectsSemantics D.rows q')
    {γ : ExtOrd} (hγ : extVisibilityReplace γ (n + 1) (n + 1) = γ)
    (hcap : ∀ d, min (q' (hD.cellOf d)) γ = min (p.label d) γ) :
    ∃ q'' : Cell D.scheme → ExtOrd, RespectsSemantics D.rows q'' ∧
      (∀ d, min (q'' d) γ = min (q' d) γ) ∧ ∀ d, q'' (hD.cellOf d) = p.label d := by
  obtain ⟨Ps, pl, pb, pr⟩ := p
  obtain ⟨hvis, hres⟩ := hD
  dsimp only at hres hcap ⊢
  subst hres
  cases n with
  | zero =>
    exact ⟨q', hq', fun _ => rfl, fun d => ((CellScheme.isEmpty_cell_fin0 _).false d).elim⟩
  | succ m =>
    -- the old face `C = ι[m+1]` and the two graded pairs `⟨C, m+1⟩ ≺ ⟨m+2, m+2⟩` of `P̂`
    set CI : Finset (Fin (m + 2)) × ℕ := (Finset.univ.image Fin.castSuccEmb, m + 1) with hCIdef
    set BJ : Finset (Fin (m + 2)) × ℕ := (Finset.univ, m + 2) with hBJdef
    have hCI : CI ∈ Plan.gradedPlan D.scheme.plan :=
      Plan.mem_gradedPlan.mpr ⟨hvis, Nat.succ_pos _, by
        change m + 1 ≤ (Finset.univ.image Fin.castSuccEmb).card
        rw [Finset.card_image_of_injective _ Fin.castSuccEmb.injective, Finset.card_univ,
          Fintype.card_fin]⟩
    have hBJ : BJ ∈ Plan.gradedPlan D.scheme.plan := univ_succ_mem_gradedPlan D.scheme
    have hle : GradedLe CI BJ := ⟨Finset.subset_univ _, Nat.le_succ _⟩
    have hne : CI ≠ BJ := fun h => by
      have := congrArg Prod.snd h
      simp [hCIdef, hBJdef] at this
    -- the lower set `D⟨C, m+1⟩` is the domain of `p`
    have hpush : pushGraded Fin.castSuccEmb ((Finset.univ : Finset (Fin (m + 1))), m + 1) = CI :=
      rfl
    -- `p.label` on `D⟨C, m+1⟩`, respecting `E⟨C, m+1⟩`
    let pC : D.scheme.below CI → ExtOrd :=
      (fun d => pl d.1) ∘ (belowEquiv D.scheme Fin.castSuccEmb hvis hpush).symm
    have hpC : RespectsSemanticsBelow D.rows CI pC :=
      (pr.toBelow (Finset.univ, m + 1)).of_restrictFace hpush
    -- the capped-agreement premise, transported to `D⟨C, m+1⟩`
    have hcapC : ∀ d : D.scheme.below CI,
        min (q' (CellScheme.below.mono hle d).1) γ = min (pC d) γ := by
      intro d
      have h := hcap ((belowEquiv D.scheme Fin.castSuccEmb hvis hpush).symm d).1
      change min (q' (toCell D.scheme Fin.castSuccEmb hvis
        ((belowEquiv D.scheme Fin.castSuccEmb hvis hpush).symm d).1)) γ =
        min (pl ((belowEquiv D.scheme Fin.castSuccEmb hvis hpush).symm d).1) γ at h
      rw [toCell_belowEquiv_symm_val] at h
      exact h
    -- bountifulness at `γ`
    obtain ⟨q'', hq'', hq''γ, hq''p⟩ := D.bountiful CI BJ hCI hBJ hle hne pC (fun d => q' d.1) γ
      hpC (hq'.toBelow BJ) hγ hcapC
    have hall : ∀ d : Cell D.scheme, GradedLe (D.scheme.cell d) BJ :=
      gradedLe_univ_succ D.scheme
    refine ⟨fun d => q'' ⟨d, hall d⟩, hq''.toRespects hall, fun d => hq''γ ⟨d, hall d⟩,
      fun c => ?_⟩
    change Cell (D.scheme.restrictFace Fin.castSuccEmb hvis) at c
    -- the old cell `c`, as a cell of `D⟨C, m+1⟩`
    have hc : GradedLe (D.scheme.cell (toCell D.scheme Fin.castSuccEmb hvis c)) CI :=
      (gradedLe_cell_pushGraded_iff D.scheme Fin.castSuccEmb hvis c).mp
        (gradedLe_univ_succ (D.scheme.restrictFace Fin.castSuccEmb hvis) c)
    change q'' ⟨toCell D.scheme Fin.castSuccEmb hvis c, hall _⟩ = pl c
    calc q'' ⟨toCell D.scheme Fin.castSuccEmb hvis c, hall _⟩
        = q'' (CellScheme.below.mono hle ⟨toCell D.scheme Fin.castSuccEmb hvis c, hc⟩) := rfl
      _ = pC ⟨toCell D.scheme Fin.castSuccEmb hvis c, hc⟩ := hq''p _
      _ = pl c := by
        change pl ((belowEquiv D.scheme Fin.castSuccEmb hvis hpush).symm
          ⟨toCell D.scheme Fin.castSuccEmb hvis c, hc⟩).1 = pl c
        rw [belowEquiv_symm_mk]

/-! ### Bountifulness at `γ = ⊥`: a respecting labelling of `D` extending `p` -/

/-- **Bountifulness at the cutoff `γ = −∞` extends `p` to any extension domain** — the case
`γ = ⊥` of `exists_respects_extends_capped`.  For `p : S α n` and `D` a domain on `n+1` with
`D⟨n,n⟩ = dom p`, there is a labelling of `D` respecting its rows (no stage bound) and agreeing
with `p.label` on the cells of the old face: take any respecting labelling `q₀` of `D`
(`SemScheme.exists_respectsSemantics`) as the large labelling; at `γ = ⊥` the self-visibility
premise is `extVisibilityReplace_bot` and the capped-agreement premise
`(q₀ ∧ ⊥) ↾ D⟨C,m+1⟩ = p ∧ ⊥` is automatic (both sides are `⊥`); the conclusion
`q' ∧ ⊥ = q₀ ∧ ⊥` is vacuous and is discarded, and `q' ↾ dom p = p` is literal agreement. -/
theorem exists_respects_extends {p : S α n} {D : SemScheme (n + 1)} (hD : ExtendsDomain p D) :
    ∃ q' : Cell D.scheme → ExtOrd,
      RespectsSemantics D.rows q' ∧ ∀ d, q' (hD.cellOf d) = p.label d := by
  obtain ⟨q₀, hq₀⟩ := D.exists_respectsSemantics
  obtain ⟨q', hq', -, hext⟩ := exists_respects_extends_capped hD hq₀
    (extVisibilityReplace_bot _ _) (fun d => by rw [min_eq_right bot_le, min_eq_right bot_le])
  exact ⟨q', hq', hext⟩

/-! ### Cofaces over a given extension domain, and the (a)-families -/

/-- **Cofaces over a given extension domain** (Prop. 4.3.23 for a given `D`, from
bountifulness alone): at a limit stage `α`, every extension domain `D` of `dom p`
(`ExtendsDomain p D`) carries a coface of `p`.  Built from `exists_respects_extends`
(bountifulness at `γ = ⊥`) and `isCoface_ofRespects` (truncation to `α`). -/
theorem exists_coface_of_extendsDomain (hα : Order.IsSuccLimit α) (p : S α n)
    (D : SemScheme (n + 1)) (hD : ExtendsDomain p D) :
    ∃ q : S α (n + 1), q.scheme = D ∧ IsCoface p q := by
  obtain ⟨q', hq', hext⟩ := exists_respects_extends hD
  exact ⟨ofRespects hα D q' hq', rfl, isCoface_ofRespects hα hD hq' hext⟩

/-- The coface fibre over any extension domain is nonempty. -/
theorem nonempty_coface_of_extendsDomain (hα : Order.IsSuccLimit α) (p : S α n)
    (D : SemScheme (n + 1)) (hD : ExtendsDomain p D) : Nonempty (Coface p) :=
  let ⟨q, _, hq⟩ := exists_coface_of_extendsDomain hα p D hD
  ⟨⟨q, hq⟩⟩

/-- **Def. 3.2.1(4)(a)(i) is never vacuous**: for every extension domain `D` of `dom p`, the
generalised-saturation family `GenSatFamily D` contains a coface of `p`. -/
theorem genSatFamily_nonempty (hα : Order.IsSuccLimit α) (p : S α n) (D : SemScheme (n + 1))
    (hD : ExtendsDomain p D) : ∃ q ∈ GenSatFamily (α := α) D, IsCoface p q :=
  let ⟨q, hq, hc⟩ := exists_coface_of_extendsDomain hα p D hD
  ⟨q, hq, hc⟩

/-- **Def. 3.2.1(4)(a)(ii) is never vacuous**: for `D` an extension domain of `dom p` and `q'`
a labelling of `D` respecting its rows (no stage bound) and extending `p` along the cell map
of the initial face, the prescribed-`−∞`-pattern family `BottomPatternFamily D q'` contains a
coface of `p` — the reduction of `q'` itself: `truncExt α` preserves and reflects `⊥`
(`truncExt_eq_bot_iff`), so the `−∞`-pattern on `D^{≤ n}` is that of `q'`, and it fixes `p`
on the face (`isCoface_ofRespects`). -/
theorem bottomPatternFamily_nonempty (hα : Order.IsSuccLimit α) {p : S α n}
    {D : SemScheme (n + 1)} (hD : ExtendsDomain p D) (q' : Cell D.scheme → ExtOrd)
    (hq' : RespectsSemantics D.rows q') (hext : ∀ d, q' (hD.cellOf d) = p.label d) :
    ∃ q ∈ BottomPatternFamily (α := α) D q', IsCoface p q :=
  ⟨ofRespects hα D q' hq', ⟨rfl, fun _ => truncExt_eq_bot_iff⟩, isCoface_ofRespects hα hD hq' hext⟩

end StageType

end VaughtConjecture.Knight
