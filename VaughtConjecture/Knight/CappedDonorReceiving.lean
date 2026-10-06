/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorSelector
public import VaughtConjecture.Knight.GradeTwoCodedBountiful

/-! # The gated receiving-input family and both original-state fibres (notes32 §§4–6)

The reviewer's notes32 §§4–6 (audit5 §§3–5) on the coherent capped-donor selector of
`Knight/CappedDonorSelector.lean`: a **constructed family of receiving inputs** — states of the
request scheme `P` and the private scheme `C` at every numerical cutoff `j`, with a free
grade-one gate and numerical persistent shadow fields — and **both original-state fibres**,
proved from the unchanged old bountifulness of `P` and `C` alone.  This is the receiving-input
side only; the physical (legal-probe) realization of notes32 §7 is not here.

**Effective grades.**  At cutoff `j` the present fields of `P` are its lower set
`effP nP j = (univ, min j (nP + 1))` and those of `C` (arity `J ≥ N`) are
`effC J j = (univ, min j J)`; the cap (grade `N`) is present exactly when `N ≤ j`, and then the
cap's lower domain `Low` — the acquisition face's cells of grade at most `N` — is present
(`capLe`); the private cells above grade `N` are present only from their own grade on.  A
section at such a cutoff restricts to the cap's lower domain (`lowC`), which is all the selector
reads.  Caps are
permissible at a scheme's *own* effective grade: an `N`-visible cut is permissible for `P`
because every grade of `P` is below `N` (`selfVis_effP_of_N`); the external cap `γ` is
`j`-visible, hence visible at every present grade, including those above `N`.

**States** (`State j`): lawful current numerical sections `u` of `effP nP j` and `v` of
`effC J j`, the grade-one gate, and **numerical persistent shadows** `shadowP`, `shadowC` —
`1`-visible values for *every* field, present or future (**future-field visibility**).

**The filtered literal face** (newapproach2 §3.1).  The common face `(A, KA)` is the literal
root, of any arity `KA ≥ 0`; at cutoff `j` its **present portion** is the grade-`≤ j` part, and
admissibility demands the two numerical sections to agree on it **at every cutoff**
(`Admissible.face`, through `reqFace`/`privFace`) — not only once the whole face is present.
For `KA > K` this is what lets the low-reference repairs (`CappedDonorRetarget`,
`CappedDonorRelease`) control the already-present high-grade root values.  Installing a face
prescription (`exists_installP`, `exists_installC`) is old bountifulness on the present lower set
`(A, min KA j)` (`faceSec`, `faceCSec`), through the equal-index form
`Semantics.IsBountiful.extend`; an empty present portion (empty root, or `j = 0`) needs no
extension call.
**Admissibility** (`Admissible`): both sections lawful; the whole common face literal whenever
it is present; gate and shadows `1`-visible; each present field's shadow has the field's
numerical support; the finite support guard (11) — a positive gate and cap shadow force positive
reference shadows and the donor's support on the request fields; and the numerical relation
(10), **only when the cap is present**, the gate is positive and the cap is positive:

    u ∧ cut v = sel v        on every request cell.

A positive future cap shadow never forces a positive numerical cap before grade `N`.

**The fibres.**  Both retain the entire common face, every original cap coordinate, and the
**cap receipts** of the gate and of every shadow (`CapReceipts`: agreement below the comparison
cap); at a positive cap the gate and every shadow are retained literally:

* `exists_private_lift` (§5): for an independently lawful private prescription `v₁` agreeing
  with `v` below a permissible `γ`, there is an admissible state with `v₁` literally and `u`
  retained below `γ`.  Two cases when active: `cut v₁ ≤ γ` uses old `P`-bountifulness at `γ`
  from the old ambient `u`; `γ < cut v₁` uses old `P`-bountifulness at `cut v₁` from the lawful
  ambient `sel v₁` with the exact face prescription, whose compatibility hypothesis is the
  capped-donor boundary (7).
* `exists_request_lift` (§6): for a lawful request prescription `u₁` agreeing with `u` below
  `γ`, old `C`-bountifulness installs the face and **clipping every private coordinate of grade
  at least `N` at `γ`** (`clip`, lawful by grade-sensitive capping) restores the relation
  through the clip identities of the selector.
* **Bottom cap** (`offState`): at `γ = ⊥` the gate is switched off and the shadows of the
  present fields recomputed as the `1`-visible roundings of the new values (the future shadows
  are retained); the relation and the guard are then vacuous.  At a positive cap an already
  positive gate is never switched off (the persistence lemma `admissible_persist`).

The **empty block list** needs no representative: the selector is then identically bottom and
the relation is vacuous (`Ref.sel_of_isEmpty`).  The actual pair with the gate on is admissible
at every cutoff (`actual_admissible`), by `sel vact = p ∧ cut vact`.  All old extension calls
are inside the unchanged `P` and `C`; no new-domain bountifulness is an input. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd SharpWitnessComposition AmalgamationPlan

/-! ## Bountifulness with equal indices -/

/-- Bountifulness with the source index allowed to equal the target index. -/
theorem Semantics.IsBountiful.extend {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {D : CellScheme A} {sem : Semantics D} (hb : sem.IsBountiful) {CI BJ : Finset ι × ℕ}
    (hCI : CI ∈ Plan.gradedPlan D.plan) (hBJ : BJ ∈ Plan.gradedPlan D.plan) (h : GradedLe CI BJ)
    {p : D.below CI → ExtOrd} {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hp : RespectsSemanticsBelow sem CI p) (hq : RespectsSemanticsBelow sem BJ q)
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ)
    (hcompat : ∀ d : D.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ q' ∧
      (∀ d : D.below BJ, min (q' d) γ = min (q d) γ) ∧
      ∀ d : D.below CI, q' (CellScheme.below.mono h d) = p d := by
  by_cases heq : CI = BJ
  · subst heq
    exact ⟨p, hp, fun d => (hcompat d).symm, fun _ => rfl⟩
  · exact hb CI BJ hCI hBJ h heq p q γ hp hq hγ hcompat

namespace CappedDonor

/-! ## Effective cutoffs -/

/-- The present request fields at cutoff `j`. -/
def effP (nP j : ℕ) : Finset (Fin (nP + 1)) × ℕ := (Finset.univ, min j (nP + 1))

/-- The present private fields at cutoff `j`. -/
def effC (J j : ℕ) : Finset (Fin J) × ℕ := (Finset.univ, min j J)

theorem effP_snd (nP j : ℕ) : (effP nP j).2 = min j (nP + 1) := rfl

theorem effC_snd (J j : ℕ) : (effC J j).2 = min j J := rfl

section Cutoffs

variable {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}

theorem effP_mem {j : ℕ} (hj : 0 < j) : effP nP j ∈ Plan.gradedPlan P.scheme.plan :=
  Plan.mem_gradedPlan.mpr ⟨P.scheme.isPlan.domain_mem, lt_min hj (Nat.succ_pos _), by
    change min j (nP + 1) ≤ (Finset.univ : Finset (Fin (nP + 1))).card
    rw [Finset.card_univ, Fintype.card_fin]
    exact min_le_right _ _⟩

theorem gradeC_le (d : Cell C.scheme) : C.scheme.grade d ≤ J :=
  (C.scheme.grade_le_card_scope d).trans (by simpa using Finset.card_le_univ (C.scheme.scope d))

theorem effC_mem {j : ℕ} (hj : 0 < j) (hJ : 0 < J) : effC J j ∈ Plan.gradedPlan C.scheme.plan :=
  Plan.mem_gradedPlan.mpr ⟨C.scheme.isPlan.domain_mem, lt_min hj hJ, by
    change min j J ≤ (Finset.univ : Finset (Fin J)).card
    rw [Finset.card_univ, Fintype.card_fin]
    exact min_le_right _ _⟩

/-- The clipping caps: `⊤` below grade `N`, `γ` from grade `N` on. -/
noncomputable def clipCap (N : ℕ) (γ : ExtOrd) (k : ℕ) : ExtOrd := if k < N then ⊤ else γ

theorem clipCap_of_lt {γ : ExtOrd} {k : ℕ} (h : k < N) : clipCap N γ k = ⊤ := by
  unfold clipCap; rw [ite_eq_left h]

theorem clipCap_of_le {γ : ExtOrd} {k : ℕ} (h : N ≤ k) : clipCap N γ k = γ := by
  unfold clipCap; rw [ite_eq_right (not_lt.mpr h)]

theorem clipCap_anti (γ : ExtOrd) (k k' : ℕ) (h : k ≤ k') : clipCap N γ k' ≤ clipCap N γ k := by
  unfold clipCap
  split_ifs <;> first | exact le_rfl | exact le_top | omega

/-- Clipping every private coordinate of grade at least `N` at `γ`. -/
noncomputable def clip {j : ℕ} (γ : ExtOrd) (v : C.scheme.below (effC J j) → ExtOrd)
    (d : C.scheme.below (effC J j)) : ExtOrd :=
  min (v d) (clipCap N γ (C.scheme.grade d.1))

/-- Clipping is lawful: the external cap is visible at every present grade. -/
theorem clip_respects {j : ℕ} {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ)
    {v : C.scheme.below (effC J j) → ExtOrd} (hv : RespectsSemanticsBelow C.rows (effC J j) v) :
    RespectsSemanticsBelow C.rows (effC J j) (clip (N := N) γ v) := by
  refine hv.gradeCap _ (clipCap_anti γ) ?_
  intro k hk
  unfold clipCap
  split_ifs
  · exact TopSupport.selfVis_top_ext k
  · exact hγ.mono hk

theorem clip_of_lt {j : ℕ} (γ : ExtOrd) (v : C.scheme.below (effC J j) → ExtOrd)
    {d : C.scheme.below (effC J j)} (h : C.scheme.grade d.1 < N) : clip (N := N) γ v d = v d := by
  unfold clip; rw [clipCap_of_lt h, min_top_right]

theorem clip_agree {j : ℕ} (γ : ExtOrd) (v : C.scheme.below (effC J j) → ExtOrd)
    (d : C.scheme.below (effC J j)) : min (clip (N := N) γ v d) γ = min (v d) γ := by
  unfold clip clipCap
  split_ifs
  · rw [min_top_right]
  · rw [min_assoc, min_self]

end Cutoffs

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  (R : Ref I nP N J P C)

/-! ## Effective grades relative to the reference data -/

include R in
theorem effP_snd_le_N (j : ℕ) : (effP nP j).2 ≤ N := (min_le_right _ _).trans R.arity_lt.le

include R in
theorem effP_snd_le_effC (j : ℕ) : (effP nP j).2 ≤ (effC J j).2 :=
  min_le_min_left j (R.arity_lt.le.trans R.N_le)

include R in
theorem effC_mem' {j : ℕ} (hj : 0 < j) : effC J j ∈ Plan.gradedPlan C.scheme.plan :=
  effC_mem hj ((Nat.succ_pos _).trans_le (R.arity_lt.le.trans R.N_le))

include R in
/-- Once the cap is present, every request cell is present. -/
theorem effP_all {j : ℕ} (hj : N ≤ j) (d : Cell P.scheme) :
    GradedLe (P.scheme.cell d) (effP nP j) :=
  ⟨Finset.subset_univ _, le_min ((gradeP_le d).trans (R.arity_lt.le.trans hj)) (gradeP_le d)⟩

/-- Once the cap is present, its whole lower domain is present. -/
theorem capLe {j : ℕ} (hj : N ≤ j) : GradedLe (C.scheme.cell R.cap) (effC J j) := by
  rw [R.cap_cell]
  exact ⟨Finset.subset_univ _, le_min hj R.N_le⟩

/-- The cap as a present field. -/
def capC {j : ℕ} (hj : N ≤ j) : C.scheme.below (effC J j) :=
  CellScheme.below.mono (R.capLe hj) R.capL

/-- The restriction of a present private section to the cap's lower domain. -/
def lowC {j : ℕ} (hj : N ≤ j) (v : C.scheme.below (effC J j) → ExtOrd) (d : R.Low) : ExtOrd :=
  v (CellScheme.below.mono (R.capLe hj) d)

theorem lowC_respects {j : ℕ} (hj : N ≤ j) {v : C.scheme.below (effC J j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC J j) v) :
    RespectsSemanticsBelow C.rows (C.scheme.cell R.cap) (R.lowC hj v) :=
  hv.mono (R.capLe hj)

theorem lowC_cap {j : ℕ} (hj : N ≤ j) (v : C.scheme.below (effC J j) → ExtOrd) :
    R.lowC hj v R.capL = v (R.capC hj) := rfl

include R in
theorem selfVis_N_of_effC {j : ℕ} (hj : N ≤ j) {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) :
    SelfVis N γ := hγ.mono (le_min hj R.N_le)

include R in
theorem selfVis_effP_of_effC {j : ℕ} {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) :
    SelfVis (effP nP j).2 γ := hγ.mono (R.effP_snd_le_effC j)

include R in
/-- An `N`-visible cut is permissible at the request scheme's own effective grade. -/
theorem selfVis_effP_of_N (j : ℕ) {β : ExtOrd} (hβ : SelfVis N β) : SelfVis (effP nP j).2 β :=
  hβ.mono (R.effP_snd_le_N j)

/-! ## The present portion of the face -/

/-- A face cell present at cutoff `j` as a present request field. -/
def reqFace {j : ℕ} (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j) :
    P.scheme.below (effP nP j) :=
  ⟨a.1, ⟨Finset.subset_univ _, le_min h (gradeP_le a.1)⟩⟩

/-- The private copy of a face cell present at cutoff `j` as a present private field. -/
def privFace {j : ℕ} (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j) :
    C.scheme.below (effC J j) :=
  ⟨(R.face a).1, ⟨Finset.subset_univ _, le_min ((R.face_grade a).trans_le h) (gradeC_le _)⟩⟩

theorem reqFace_val {j : ℕ} (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j) :
    (R.reqFace a h).1 = a.1 := rfl

theorem privFace_val {j : ℕ} (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j) :
    (R.privFace a h).1 = (R.face a).1 := rfl

theorem reqFace_congr {j : ℕ} {a a' : P.scheme.below (R.A, R.KA)} (e : a = a')
    (h : P.scheme.grade a.1 ≤ j) (h' : P.scheme.grade a'.1 ≤ j) :
    R.reqFace a h = R.reqFace a' h' := by
  subst e; rfl

theorem privFace_congr {j : ℕ} {a a' : P.scheme.below (R.A, R.KA)} (e : a = a')
    (h : P.scheme.grade a.1 ≤ j) (h' : P.scheme.grade a'.1 ≤ j) :
    R.privFace a h = R.privFace a' h' := by
  subst e; rfl

/-- Every face cell is present once the cap is. -/
theorem face_grade_le_of_N {j : ℕ} (hj : N ≤ j) (a : P.scheme.below (R.A, R.KA)) :
    P.scheme.grade a.1 ≤ j := a.2.2.trans (R.KA_lt_N.le.trans hj)

/-- The present portion `(A, min KA j)` of the face at cutoff `j`. -/
theorem face_le_effP {j : ℕ} : GradedLe (R.A, min R.KA j) (effP nP j) :=
  ⟨Finset.subset_univ _, le_min (min_le_right _ _) ((min_le_left _ _).trans R.KA_le)⟩

theorem face_le_effC {j : ℕ} : GradedLe (R.A', min R.KA j) (effC J j) :=
  ⟨Finset.subset_univ _, le_min (min_le_right _ _)
    ((min_le_left _ _).trans (R.KA_lt_N.le.trans R.N_le))⟩

/-- No face cell is present when the present portion has grade zero. -/
theorem face_absent {j : ℕ} (hk : ¬ 0 < min R.KA j) (a : P.scheme.below (R.A, R.KA))
    (h : P.scheme.grade a.1 ≤ j) : False :=
  hk (lt_min ((P.scheme.grade_pos a.1).trans_le a.2.2) ((P.scheme.grade_pos a.1).trans_le h))

/-- A private section read on the present portion of the request copy of the face. -/
def faceSec {j : ℕ} (v : C.scheme.below (effC J j) → ExtOrd)
    (a : P.scheme.below (R.A, min R.KA j)) : ExtOrd :=
  v (R.privFace (R.faceLift (min_le_left _ _) a) (a.2.2.trans (min_le_right _ _)))

/-- A request section read on the present portion of the private copy of the face. -/
def faceCSec {j : ℕ} (u : P.scheme.below (effP nP j) → ExtOrd)
    (b : C.scheme.below (R.A', min R.KA j)) : ExtOrd :=
  u (R.reqFace (R.face.symm (R.faceLift' (min_le_left _ _) b))
    (by rw [R.face_symm_grade]; exact b.2.2.trans (min_le_right _ _)))

theorem faceSec_respects {j : ℕ} {v : C.scheme.below (effC J j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC J j) v) :
    RespectsSemanticsBelow P.rows (R.A, min R.KA j) (R.faceSec v) :=
  (R.faceAt_respects (min_le_left _ _) _).mp (hv.mono R.face_le_effC)

theorem faceCSec_respects {j : ℕ} {u : P.scheme.below (effP nP j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effP nP j) u) :
    RespectsSemanticsBelow C.rows (R.A', min R.KA j) (R.faceCSec u) := by
  refine (R.faceAt_respects (min_le_left _ _) (R.faceCSec u)).mpr ?_
  have heq : (fun a : P.scheme.below (R.A, min R.KA j) =>
      R.faceCSec u (R.faceAt (min_le_left _ _) a)) =
      fun a => u (CellScheme.below.mono R.face_le_effP a) := by
    funext a
    unfold faceCSec
    congr 1
    apply Subtype.ext
    change (R.face.symm (R.faceLift' _ (R.faceAt _ a))).1 = a.1
    have h : R.faceLift' (min_le_left R.KA j) (R.faceAt (min_le_left _ _) a) =
        R.face (R.faceLift (min_le_left _ _) a) := rfl
    rw [h, Equiv.symm_apply_apply]
    rfl
  rw [heq]
  exact hu.mono R.face_le_effP

theorem lowC_face {j : ℕ} (hj : N ≤ j) (v : C.scheme.below (effC J j) → ExtOrd)
    (a : P.scheme.below (R.A, R.KA)) :
    R.lowC hj v (R.lowFace a) = v (R.privFace a (R.face_grade_le_of_N hj a)) := rfl

/-! ## States and admissibility -/

/-- A state at cutoff `j`: the present numerical sections, the gate, and the numerical
persistent shadows of every field (present or future). -/
structure State (R : Ref I nP N J P C) (j : ℕ) where
  /-- The current request section. -/
  u : P.scheme.below (effP nP j) → ExtOrd
  /-- The current private section. -/
  v : C.scheme.below (effC J j) → ExtOrd
  /-- The free grade-one gate. -/
  gate : ExtOrd
  /-- The persistent grade-one shadow of every request field. -/
  shadowP : Cell P.scheme → ExtOrd
  /-- The persistent grade-one shadow of every private field. -/
  shadowC : Cell C.scheme → ExtOrd

/-- **Admissibility** (notes32 §4): lawful sections, the literal common face on its present
portion (at every cutoff), `1`-visible gate and shadows, shadows carrying the present numerical
supports, the support guard (11), and the numerical relation (10) whenever the cap is present,
the gate is positive and the cap is positive. -/
structure Admissible {j : ℕ} (st : R.State j) : Prop where
  u_respects : RespectsSemanticsBelow P.rows (effP nP j) st.u
  v_respects : RespectsSemanticsBelow C.rows (effC J j) st.v
  face : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
    st.u (R.reqFace a h) = st.v (R.privFace a h)
  gate_vis : SelfVis 1 st.gate
  shadowP_vis : ∀ d, SelfVis 1 (st.shadowP d)
  shadowC_vis : ∀ d, SelfVis 1 (st.shadowC d)
  shadowP_iff : ∀ d : P.scheme.below (effP nP j), st.shadowP d.1 ≠ ⊥ ↔ st.u d ≠ ⊥
  shadowC_iff : ∀ d : C.scheme.below (effC J j), st.shadowC d.1 ≠ ⊥ ↔ st.v d ≠ ⊥
  support : st.gate ≠ ⊥ → st.shadowC R.cap ≠ ⊥ →
    (∀ i, st.shadowC (R.ref i) ≠ ⊥) ∧ ∀ d, st.shadowP d ≠ ⊥ ↔ R.p d ≠ ⊥
  relation : ∀ (hj : N ≤ j), st.gate ≠ ⊥ → st.v (R.capC hj) ≠ ⊥ →
    ∀ d : P.scheme.below (effP nP j),
      min (st.u d) (R.cut (R.lowC hj st.v)) = R.sel (R.lowC hj st.v) d.1

/-- In an active admissible state the restricted private section is active for the selector. -/
theorem Admissible.active {j : ℕ} {st : R.State j} (hst : R.Admissible st) (hj : N ≤ j)
    (hg : st.gate ≠ ⊥) (hc : st.v (R.capC hj) ≠ ⊥) : R.Active (R.lowC hj st.v) := by
  obtain ⟨href, hsupp⟩ := hst.support hg ((hst.shadowC_iff (R.capC hj)).mpr hc)
  refine ⟨R.lowC_respects hj hst.v_respects, hc, fun i => ?_, ?_⟩
  · exact (hst.shadowC_iff (CellScheme.below.mono (R.capLe hj) (R.lowRef i))).mp (href i)
  · intro a ha
    have hu : st.u (R.reqFace a (R.face_grade_le_of_N hj a)) = ⊥ := by
      by_contra hne
      exact (hsupp a.1).mp ((hst.shadowP_iff _).mpr hne) ha
    rw [R.lowC_face, ← hst.face a (R.face_grade_le_of_N hj a), hu]

/-! ## Cap receipts, persistence at a positive cap, and the bottom-cap state -/

/-- **Cap receipts**: the gate and every shadow of the new state agree with the old ones below
the comparison cap `γ`. -/
def CapReceipts {j : ℕ} (γ : ExtOrd) (st st₁ : R.State j) : Prop :=
  min st₁.gate γ = min st.gate γ ∧ (∀ d, min (st₁.shadowP d) γ = min (st.shadowP d) γ) ∧
    ∀ d, min (st₁.shadowC d) γ = min (st.shadowC d) γ

theorem capReceipts_bot {j : ℕ} (st st₁ : R.State j) : R.CapReceipts ⊥ st st₁ :=
  ⟨by rw [min_bot_right, min_bot_right], fun _ => by rw [min_bot_right, min_bot_right],
    fun _ => by rw [min_bot_right, min_bot_right]⟩

theorem capReceipts_of_eq {j : ℕ} (γ : ExtOrd) {st st₁ : R.State j} (hg : st₁.gate = st.gate)
    (hP : st₁.shadowP = st.shadowP) (hC : st₁.shadowC = st.shadowC) : R.CapReceipts γ st st₁ :=
  ⟨by rw [hg], fun _ => by rw [hP], fun _ => by rw [hC]⟩

/-- **Persistence**: at a positive cap the gate and every shadow are retained; new lawful
sections agreeing with the old ones below the cap, with the literal face and the relation, form
an admissible state. -/
theorem admissible_persist {j : ℕ} {st : R.State j} (hst : R.Admissible st) {γ : ExtOrd}
    (hγ : γ ≠ ⊥) {u₁ : P.scheme.below (effP nP j) → ExtOrd}
    {v₁ : C.scheme.below (effC J j) → ExtOrd}
    (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁)
    (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁)
    (hu : ∀ d, min (u₁ d) γ = min (st.u d) γ) (hv : ∀ d, min (v₁ d) γ = min (st.v d) γ)
    (hface : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      u₁ (R.reqFace a h) = v₁ (R.privFace a h))
    (hrel : ∀ (hj : N ≤ j), st.gate ≠ ⊥ → v₁ (R.capC hj) ≠ ⊥ →
      ∀ d : P.scheme.below (effP nP j),
        min (u₁ d) (R.cut (R.lowC hj v₁)) = R.sel (R.lowC hj v₁) d.1) :
    R.Admissible ⟨u₁, v₁, st.gate, st.shadowP, st.shadowC⟩ where
  u_respects := hu₁
  v_respects := hv₁
  face := hface
  gate_vis := hst.gate_vis
  shadowP_vis := hst.shadowP_vis
  shadowC_vis := hst.shadowC_vis
  shadowP_iff d := by
    rw [hst.shadowP_iff d]
    exact not_congr (bottom_pattern_of_cap_agreement hγ hu d).symm
  shadowC_iff d := by
    rw [hst.shadowC_iff d]
    exact not_congr (bottom_pattern_of_cap_agreement hγ hv d).symm
  support := hst.support
  relation := hrel

open Classical in
/-- **The bottom-cap state**: the gate switched off, the shadows of the present fields
recomputed as the `1`-visible roundings of the new sections, the shadows of the future fields
retained. -/
noncomputable def offState {j : ℕ} (st : R.State j) (u₁ : P.scheme.below (effP nP j) → ExtOrd)
    (v₁ : C.scheme.below (effC J j) → ExtOrd) : R.State j where
  u := u₁
  v := v₁
  gate := ⊥
  shadowP d := if h : GradedLe (P.scheme.cell d) (effP nP j) then
    extVisibilityReplace (u₁ ⟨d, h⟩) 1 1 else st.shadowP d
  shadowC d := if h : GradedLe (C.scheme.cell d) (effC J j) then
    extVisibilityReplace (v₁ ⟨d, h⟩) 1 1 else st.shadowC d

open Classical in
theorem admissible_off {j : ℕ} {st : R.State j} (hst : R.Admissible st)
    {u₁ : P.scheme.below (effP nP j) → ExtOrd} {v₁ : C.scheme.below (effC J j) → ExtOrd}
    (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁)
    (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁)
    (hface : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      u₁ (R.reqFace a h) = v₁ (R.privFace a h)) :
    R.Admissible (R.offState st u₁ v₁) where
  u_respects := hu₁
  v_respects := hv₁
  face := hface
  gate_vis := selfVis_bot 1
  shadowP_vis d := by
    change SelfVis 1 (if h : GradedLe (P.scheme.cell d) (effP nP j) then
      extVisibilityReplace (u₁ ⟨d, h⟩) 1 1 else st.shadowP d)
    split_ifs
    · exact TopSupport.selfVis_evr_self 1 _
    · exact hst.shadowP_vis d
  shadowC_vis d := by
    change SelfVis 1 (if h : GradedLe (C.scheme.cell d) (effC J j) then
      extVisibilityReplace (v₁ ⟨d, h⟩) 1 1 else st.shadowC d)
    split_ifs
    · exact TopSupport.selfVis_evr_self 1 _
    · exact hst.shadowC_vis d
  shadowP_iff d := by
    change (if h : GradedLe (P.scheme.cell d.1) (effP nP j) then
      extVisibilityReplace (u₁ ⟨d.1, h⟩) 1 1 else st.shadowP d.1) ≠ ⊥ ↔ u₁ d ≠ ⊥
    rw [dite_eq_left d.2]
    exact not_congr (evr_eq_bot_iff 1 1)
  shadowC_iff d := by
    change (if h : GradedLe (C.scheme.cell d.1) (effC J j) then
      extVisibilityReplace (v₁ ⟨d.1, h⟩) 1 1 else st.shadowC d.1) ≠ ⊥ ↔ v₁ d ≠ ⊥
    rw [dite_eq_left d.2]
    exact not_congr (evr_eq_bot_iff 1 1)
  support h := (h rfl).elim
  relation _ h := (h rfl).elim

/-! ## Installing a face prescription by old bountifulness -/

/-- Old `P`-bountifulness installs a lawful private face prescription into a request section at
a permissible cap, on the present portion of the face; nothing is done when that portion is
empty. -/
theorem exists_installP {j : ℕ} {u : P.scheme.below (effP nP j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effP nP j) u)
    {v₁ : C.scheme.below (effC J j) → ExtOrd} (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁)
    {γ : ExtOrd} (hγ : SelfVis (effP nP j).2 γ)
    (hcompat : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      min (u (R.reqFace a h)) γ = min (v₁ (R.privFace a h)) γ) :
    ∃ u₁ : P.scheme.below (effP nP j) → ExtOrd, RespectsSemanticsBelow P.rows (effP nP j) u₁ ∧
      (∀ d, min (u₁ d) γ = min (u d) γ) ∧
      ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
        u₁ (R.reqFace a h) = v₁ (R.privFace a h) := by
  by_cases hk : 0 < min R.KA j
  · obtain ⟨u₁, hu₁, hcap, hface⟩ := P.bountiful.extend (R.face_mem hk (min_le_left _ _))
      (effP_mem (hk.trans_le (min_le_right _ _))) R.face_le_effP (R.faceSec_respects hv₁) hu hγ
      (fun a => hcompat (R.faceLift (min_le_left _ _) a) (a.2.2.trans (min_le_right _ _)))
    exact ⟨u₁, hu₁, hcap, fun a h => hface ⟨a.1, ⟨a.2.1, le_min a.2.2 h⟩⟩⟩
  · exact ⟨u, hu, fun _ => rfl, fun a h => (R.face_absent hk a h).elim⟩

/-- Old `C`-bountifulness installs a lawful request face prescription into a private section at
a permissible cap, on the present portion of the face; nothing is done when that portion is
empty. -/
theorem exists_installC {j : ℕ} {v : C.scheme.below (effC J j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC J j) v)
    {u₁ : P.scheme.below (effP nP j) → ExtOrd} (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁)
    {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ)
    (hcompat : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      min (v (R.privFace a h)) γ = min (u₁ (R.reqFace a h)) γ) :
    ∃ v₁ : C.scheme.below (effC J j) → ExtOrd, RespectsSemanticsBelow C.rows (effC J j) v₁ ∧
      (∀ d, min (v₁ d) γ = min (v d) γ) ∧
      ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
        u₁ (R.reqFace a h) = v₁ (R.privFace a h) := by
  by_cases hk : 0 < min R.KA j
  · obtain ⟨v₁, hv₁, hcap, hface⟩ := C.bountiful.extend (R.face_mem' hk (min_le_left _ _))
      (R.effC_mem' (hk.trans_le (min_le_right _ _))) R.face_le_effC (R.faceCSec_respects hu₁) hv
      hγ (by
        intro b
        have hb : P.scheme.grade (R.face.symm (R.faceLift' (min_le_left _ _) b)).1 ≤ j := by
          rw [R.face_symm_grade]; exact b.2.2.trans (min_le_right _ _)
        have h := hcompat (R.face.symm (R.faceLift' (min_le_left _ _) b)) hb
        have e : R.privFace (R.face.symm (R.faceLift' (min_le_left _ _) b)) hb =
            CellScheme.below.mono R.face_le_effC b := by
          apply Subtype.ext
          change (R.face (R.face.symm (R.faceLift' _ b))).1 = b.1
          rw [Equiv.apply_symm_apply]
          rfl
        rw [e] at h
        exact h)
    refine ⟨v₁, hv₁, hcap, fun a h => ?_⟩
    have hb : GradedLe (C.scheme.cell (R.face a).1) (R.A', min R.KA j) :=
      ⟨(R.face a).2.1, le_min ((R.face_grade a).trans_le a.2.2) ((R.face_grade a).trans_le h)⟩
    have h1 := hface ⟨(R.face a).1, hb⟩
    have e : R.face.symm (R.faceLift' (min_le_left _ _) ⟨(R.face a).1, hb⟩) = a := by
      change R.face.symm (R.face a) = a
      exact Equiv.symm_apply_apply _ _
    unfold faceCSec at h1
    rw [R.reqFace_congr e _ h] at h1
    exact h1.symm
  · exact ⟨v, hv, fun _ => rfl, fun a h => (R.face_absent hk a h).elim⟩

/-! ## Clipping the coordinates of grade at least `N` -/

theorem clip_cap {j : ℕ} (hj : N ≤ j) (γ : ExtOrd) (v : C.scheme.below (effC J j) → ExtOrd) :
    R.lowC hj (clip (N := N) γ v) R.capL = min (R.lowC hj v R.capL) γ := by
  change min (v (R.capC hj)) (clipCap N γ (C.scheme.grade R.cap)) = _
  rw [R.grade_cap, clipCap_of_le le_rfl]
  rfl

theorem clip_ref {j : ℕ} (hj : N ≤ j) (γ : ExtOrd) (v : C.scheme.below (effC J j) → ExtOrd)
    (i : I) : R.lowC hj (clip (N := N) γ v) (R.lowRef i) = R.lowC hj v (R.lowRef i) :=
  clip_of_lt γ v (R.ref_grade_lt i)

theorem clip_face {j : ℕ} (γ : ExtOrd) (v : C.scheme.below (effC J j) → ExtOrd)
    (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j) :
    clip (N := N) γ v (R.privFace a h) = v (R.privFace a h) :=
  clip_of_lt γ v (by rw [R.privFace_val, R.face_grade]; exact a.2.2.trans_lt R.KA_lt_N)

/-! ## The private-context-prescribed fibre (notes32 §5) -/

/-- **The private fibre**: an independently lawful private prescription `v₁` agreeing with the
current private section below a permissible cap `γ` lifts to an admissible state retaining `v₁`
literally, the whole request cap vector `u ∧ γ`, the entire common face, the cap receipts of the
gate and of every shadow — and, at a positive cap, the gate and every shadow literally.  The only
extension operation is old `P`-bountifulness. -/
theorem exists_private_lift {j : ℕ} {st : R.State j} (hst : R.Admissible st)
    {v₁ : C.scheme.below (effC J j) → ExtOrd} (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁)
    {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (v₁ d) γ = min (st.v d) γ) :
    ∃ st₁ : R.State j, R.Admissible st₁ ∧ st₁.v = v₁ ∧ (∀ d, min (st₁.u d) γ = min (st.u d) γ) ∧
      R.CapReceipts γ st st₁ ∧
      (γ ≠ ⊥ → st₁.gate = st.gate ∧ st₁.shadowP = st.shadowP ∧ st₁.shadowC = st.shadowC) := by
  have hcompat : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      min (st.u (R.reqFace a h)) γ = min (v₁ (R.privFace a h)) γ := by
    intro a h
    rw [hst.face a h]
    exact (hagree _).symm
  by_cases hbot : γ = ⊥
  · -- bottom cap: switch the gate off
    subst hbot
    obtain ⟨u₁, hu₁, hcap, hface⟩ := R.exists_installP hst.u_respects hv₁ (selfVis_bot _) hcompat
    exact ⟨R.offState st u₁ v₁, R.admissible_off hst hu₁ hv₁ hface, rfl, hcap,
      R.capReceipts_bot _ _, fun h => absurd rfl h⟩
  have hγP : SelfVis (effP nP j).2 γ := R.selfVis_effP_of_effC hγ
  have hpat := bottom_pattern_of_cap_agreement hbot hagree
  by_cases hact : ∃ hj : N ≤ j, st.gate ≠ ⊥ ∧ st.v (R.capC hj) ≠ ⊥
  · obtain ⟨hj, hg, hc⟩ := hact
    have hγN : SelfVis N γ := R.selfVis_N_of_effC hj hγ
    have hA₀ := Admissible.active R hst hj hg hc
    have hrel₀ := hst.relation hj hg hc
    have hA₁ : R.Active (R.lowC hj v₁) :=
      ⟨R.lowC_respects hj hv₁, fun h => hc ((hpat _).mp h),
        fun i h => hA₀.ref_pos i ((hpat _).mp h), fun a ha => (hpat _).mpr (hA₀.face_bot a ha)⟩
    have hVγ : (fun d => min (R.lowC hj v₁ d) γ) = fun d => min (R.lowC hj st.v d) γ :=
      funext fun d => hagree _
    have hcutγ : min (R.cut (R.lowC hj v₁)) γ = min (R.cut (R.lowC hj st.v)) γ := by
      rw [← R.cut_min hγN, ← R.cut_min hγN, hVγ]
    have hselγ : ∀ e, min (R.sel (R.lowC hj v₁) e) γ = min (R.sel (R.lowC hj st.v) e) γ := by
      intro e
      rw [← R.sel_min hγN, ← R.sel_min hγN, hVγ]
    have hcutvis : SelfVis N (R.cut (R.lowC hj v₁)) :=
      R.selfVis_cut (Active.selfVis_cap R hA₁)
    by_cases hβ : R.cut (R.lowC hj v₁) ≤ γ
    · -- the cut is at most the cap: extend from the old ambient at `γ`
      obtain ⟨u₁, hu₁, hcap, hface⟩ := R.exists_installP hst.u_respects hv₁ hγP hcompat
      refine ⟨⟨u₁, v₁, st.gate, st.shadowP, st.shadowC⟩,
        R.admissible_persist hst hbot hu₁ hv₁ hcap hagree hface ?_, rfl, hcap,
        R.capReceipts_of_eq γ rfl rfl rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩
      intro hj' _ _ d
      change min (u₁ d) (R.cut (R.lowC hj v₁)) = R.sel (R.lowC hj v₁) d.1
      have hβ' : R.cut (R.lowC hj v₁) = min (R.cut (R.lowC hj st.v)) γ := by
        rw [← hcutγ, min_eq_left hβ]
      calc min (u₁ d) (R.cut (R.lowC hj v₁))
          = min (min (u₁ d) γ) (R.cut (R.lowC hj v₁)) := by rw [min_assoc, min_eq_right hβ]
        _ = min (min (st.u d) γ) (R.cut (R.lowC hj v₁)) := by rw [hcap d]
        _ = min (st.u d) (R.cut (R.lowC hj v₁)) := by rw [min_assoc, min_eq_right hβ]
        _ = min (min (st.u d) (R.cut (R.lowC hj st.v))) γ := by rw [hβ', min_assoc]
        _ = min (R.sel (R.lowC hj st.v) d.1) γ := by rw [hrel₀ d]
        _ = min (R.sel (R.lowC hj v₁) d.1) γ := (hselγ d.1).symm
        _ = R.sel (R.lowC hj v₁) d.1 := min_eq_left ((R.sel_le_cut _ d.1).trans hβ)
    · -- the cap is below the cut: extend from the lawful selector at the cut
      have hγβ : γ ≤ R.cut (R.lowC hj v₁) := (not_le.mp hβ).le
      obtain ⟨u₁, hu₁, hcap₁, hface₁⟩ := R.exists_installP
        (u := fun d => R.sel (R.lowC hj v₁) d.1) ((Active.sel_respects R hA₁).toBelow _) hv₁
        (R.selfVis_effP_of_N j hcutvis) (by
          intro a h
          change min (R.sel (R.lowC hj v₁) a.1) (R.cut (R.lowC hj v₁)) =
            min (v₁ (R.privFace a h)) (R.cut (R.lowC hj v₁))
          rw [Active.sel_face R hA₁ a, R.lowC_face, min_assoc, min_self])
      have hrel₁ : ∀ d, min (u₁ d) (R.cut (R.lowC hj v₁)) = R.sel (R.lowC hj v₁) d.1 := by
        intro d
        rw [hcap₁ d]
        exact min_eq_left (R.sel_le_cut _ d.1)
      have hcap : ∀ d, min (u₁ d) γ = min (st.u d) γ := by
        intro d
        calc min (u₁ d) γ
            = min (min (u₁ d) (R.cut (R.lowC hj v₁))) γ := by
              rw [min_assoc, min_eq_right hγβ]
          _ = min (R.sel (R.lowC hj v₁) d.1) γ := by rw [hrel₁ d]
          _ = min (R.sel (R.lowC hj st.v) d.1) γ := hselγ d.1
          _ = min (min (st.u d) (R.cut (R.lowC hj st.v))) γ := by rw [hrel₀ d]
          _ = min (st.u d) (min (R.cut (R.lowC hj v₁)) γ) := by rw [min_assoc, hcutγ]
          _ = min (st.u d) γ := by rw [min_eq_right hγβ]
      refine ⟨⟨u₁, v₁, st.gate, st.shadowP, st.shadowC⟩,
        R.admissible_persist hst hbot hu₁ hv₁ hcap hagree hface₁ ?_, rfl, hcap,
        R.capReceipts_of_eq γ rfl rfl rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩
      intro _ _ _ d
      exact hrel₁ d
  · -- inactive: plain matching-face bountifulness; the relation stays vacuous
    obtain ⟨u₁, hu₁, hcap, hface⟩ := R.exists_installP hst.u_respects hv₁ hγP hcompat
    refine ⟨⟨u₁, v₁, st.gate, st.shadowP, st.shadowC⟩,
      R.admissible_persist hst hbot hu₁ hv₁ hcap hagree hface ?_, rfl, hcap,
      R.capReceipts_of_eq γ rfl rfl rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩
    intro hj hg hc
    exact absurd ⟨hj, hg, fun h => hc ((hpat _).mpr h)⟩ hact

/-! ## The request-prescribed fibre (notes32 §6) -/

/-- **The clipped request state**: a lawful request prescription agreeing with the current one
below a positive permissible cap, together with a lawful private section carrying the prescribed
face and agreeing with the current one below the cap, give an admissible state after clipping the
private coordinates of grade at least `N` at the cap; the clipped section retains the private cap
vector. -/
theorem admissible_clip {j : ℕ} {st : R.State j} (hst : R.Admissible st)
    {u₁ : P.scheme.below (effP nP j) → ExtOrd} (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁)
    {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (u₁ d) γ = min (st.u d) γ)
    (hbot : γ ≠ ⊥) {v₀ : C.scheme.below (effC J j) → ExtOrd}
    (hv₀ : RespectsSemanticsBelow C.rows (effC J j) v₀) (hcap₀ : ∀ d, min (v₀ d) γ = min (st.v d) γ)
    (hface₀ : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      u₁ (R.reqFace a h) = v₀ (R.privFace a h)) :
    R.Admissible ⟨u₁, clip (N := N) γ v₀, st.gate, st.shadowP, st.shadowC⟩ ∧
      ∀ d, min (clip (N := N) γ v₀ d) γ = min (st.v d) γ := by
  have hclip : ∀ d, min (clip (N := N) γ v₀ d) γ = min (st.v d) γ := fun d => by
    rw [clip_agree, hcap₀ d]
  refine ⟨R.admissible_persist hst hbot hu₁ (clip_respects hγ hv₀) hagree hclip
    (fun a h => by rw [hface₀ a h, R.clip_face]) ?_, hclip⟩
  intro hj hg hc d
  have hγN : SelfVis N γ := R.selfVis_N_of_effC hj hγ
  have hcap' : R.lowC hj (clip (N := N) γ v₀) R.capL = min (R.lowC hj v₀ R.capL) γ :=
    R.clip_cap hj γ v₀
  have href' : ∀ i, R.lowC hj (clip (N := N) γ v₀) (R.lowRef i) = R.lowC hj v₀ (R.lowRef i) :=
    R.clip_ref hj γ v₀
  have hcut₁ : R.cut (R.lowC hj (clip (N := N) γ v₀)) = min (R.cut (R.lowC hj v₀)) γ :=
    R.cut_clip hcap' href'
  have hsel₁ : R.sel (R.lowC hj (clip (N := N) γ v₀)) d.1 =
      min (R.sel (R.lowC hj v₀) d.1) γ :=
    R.sel_clip hcap' href' d.1
  have hV₀γ : (fun e => min (R.lowC hj v₀ e) γ) = fun e => min (R.lowC hj st.v e) γ :=
    funext fun e => hcap₀ _
  have hcutγ : min (R.cut (R.lowC hj v₀)) γ = min (R.cut (R.lowC hj st.v)) γ := by
    rw [← R.cut_min hγN, ← R.cut_min hγN, hV₀γ]
  have hselγ : min (R.sel (R.lowC hj v₀) d.1) γ = min (R.sel (R.lowC hj st.v) d.1) γ := by
    rw [← R.sel_min hγN, ← R.sel_min hγN, hV₀γ]
  have hc₀ : st.v (R.capC hj) ≠ ⊥ := by
    intro h
    apply hc
    change R.lowC hj (clip (N := N) γ v₀) R.capL = ⊥
    rw [hcap']
    change min (v₀ (R.capC hj)) γ = ⊥
    rw [hcap₀, h, min_bot_left]
  have hrel₀ := hst.relation hj hg hc₀ d
  calc min (u₁ d) (R.cut (R.lowC hj (clip (N := N) γ v₀)))
      = min (min (u₁ d) γ) (R.cut (R.lowC hj v₀)) := by
        rw [hcut₁, min_comm (R.cut _) γ, ← min_assoc]
    _ = min (min (st.u d) γ) (R.cut (R.lowC hj v₀)) := by rw [hagree d]
    _ = min (st.u d) (min (R.cut (R.lowC hj st.v)) γ) := by
        rw [min_assoc, min_comm γ, hcutγ]
    _ = min (R.sel (R.lowC hj st.v) d.1) γ := by rw [← min_assoc, hrel₀]
    _ = R.sel (R.lowC hj (clip (N := N) γ v₀)) d.1 := by rw [hsel₁, hselγ]

/-- **The request fibre**: a lawful request prescription `u₁` agreeing with the current request
section below a permissible cap `γ` lifts to an admissible state retaining `u₁` literally, the
whole private cap vector `v ∧ γ`, the entire common face, the cap receipts — and, at a positive
cap, the gate and every shadow literally.  Old `C`-bountifulness installs the face; clipping the
coordinates of grade at least `N` at `γ` restores the relation. -/
theorem exists_request_lift {j : ℕ} {st : R.State j} (hst : R.Admissible st)
    {u₁ : P.scheme.below (effP nP j) → ExtOrd} (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁)
    {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (u₁ d) γ = min (st.u d) γ) :
    ∃ st₁ : R.State j, R.Admissible st₁ ∧ st₁.u = u₁ ∧ (∀ d, min (st₁.v d) γ = min (st.v d) γ) ∧
      R.CapReceipts γ st st₁ ∧
      (γ ≠ ⊥ → st₁.gate = st.gate ∧ st₁.shadowP = st.shadowP ∧ st₁.shadowC = st.shadowC) := by
  have hcompat : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      min (st.v (R.privFace a h)) γ = min (u₁ (R.reqFace a h)) γ := by
    intro a h
    rw [← hst.face a h]
    exact (hagree _).symm
  obtain ⟨v₀, hv₀, hcap₀, hface₀⟩ := R.exists_installC hst.v_respects hu₁ hγ hcompat
  by_cases hbot : γ = ⊥
  · subst hbot
    exact ⟨R.offState st u₁ v₀, R.admissible_off hst hu₁ hv₀ hface₀, rfl, hcap₀,
      R.capReceipts_bot _ _, fun h => absurd rfl h⟩
  obtain ⟨hadm, hclip⟩ := R.admissible_clip hst hu₁ hγ hagree hbot hv₀ hcap₀ hface₀
  exact ⟨⟨u₁, clip (N := N) γ v₀, st.gate, st.shadowP, st.shadowC⟩, hadm, rfl, hclip,
    R.capReceipts_of_eq γ rfl rfl rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩

/-! ## The actual state -/

/-- The actual pair — the donor on the request scheme and the actual private labelling — with
the gate on and the shadows the `1`-visible roundings of the actual values, at any cutoff. -/
noncomputable def actualState (j : ℕ) : R.State j where
  u d := R.p d.1
  v d := R.vact d.1
  gate := ⊤
  shadowP d := extVisibilityReplace (R.p d) 1 1
  shadowC d := extVisibilityReplace (R.vact d) 1 1

/-- The actual pair is admissible with a positive gate (notes32 §8, first step): it matches on
the face and satisfies the relation by `sel_actual`. -/
theorem actual_admissible (j : ℕ) : R.Admissible (R.actualState j) where
  u_respects := R.p_respects.toBelow _
  v_respects := R.vact_respects.toBelow _
  face a _ := (R.face_actual a).symm
  gate_vis := TopSupport.selfVis_top_ext 1
  shadowP_vis _ := TopSupport.selfVis_evr_self 1 _
  shadowC_vis _ := TopSupport.selfVis_evr_self 1 _
  shadowP_iff _ := not_congr (evr_eq_bot_iff 1 1)
  shadowC_iff _ := not_congr (evr_eq_bot_iff 1 1)
  support _ _ := ⟨fun i => by
    change extVisibilityReplace (R.vact (R.ref i)) 1 1 ≠ ⊥
    rw [R.vact_ref, ne_eq, evr_eq_bot_iff]
    exact ofOrd_ne_bot _, fun _ => not_congr (evr_eq_bot_iff 1 1)⟩
  relation _ _ _ d := by
    change min (R.p d.1) (R.cut R.vactL) = R.sel R.vactL d.1
    exact (R.sel_actual d.1).symm

end Ref

end CappedDonor

end VaughtConjecture.Knight
