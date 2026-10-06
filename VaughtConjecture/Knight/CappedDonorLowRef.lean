/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorSource

/-! # The two-threshold (LOW/HIGH) receiving family: low reference, states, policy (audit16 §1)

The reviewer's audit16 / `same_grade_LOW_HIGH.md` (audit-notes4) strengthen the receiving family
of `Knight/CappedDonorReceiving.lean` by a **stored cutoff** `b` of numerical grade `K` and a
second numerical condition **LOW**, present from grade `K`, next to the selector relation
**HIGH** of grade `N`.  This module sets up the data; the row operations, the fibres and the
normalization are in the following modules.

**The low reference** (`LowRef`): an original grade-`K` owner `c` of the private scheme whose
scope contains the private copy of the common face, a source cell `r ≤ c`, and the **strict
source gap** (GAP) on the *original* row of `c`, stated as explicit inputs:

    h = R_K(E_c r) < E_c c,      h < E_c a   for every donor-top face cell a.

Every donor-top occurrence has grade at most `K` (`top_grade`) and `K < N`.  **No bound on the
root arity** is imposed (newapproach2 §3.2): only the grade-`≤ K` part of the face lies in the
owner's lower domain (`faceLow`), and that is all the low reference reads — every donor-top face
cell has grade at most `K`, so its source gap is stated.  Nothing here is derived from the
receiving construction; these are the reference-row facts the note lists as inputs.

**The frontier** `e v = v c ∧ R_K (v r)` of a lawful section is `K`-visible (`e_selfVis`), at
most every donor-top face value (`e_le_top`, from GAP through the exact normalized witness of
the section at `c`), and commutes with every `K`-visible cap (`e_min`).

**Two-threshold states** (`TState`): a receiving state together with the stored cutoff.
**Admissibility** (`TAdmissible`): the receiving admissibility, `1`-visibility of `b` (its
persistent observation) and `K`-visibility once `b` is numerically present (`K ≤ j`), and, for a
positive gate,

    LOW  (K ≤ j) :  m(u) < b < H  ⟹  max b (e v) ≤ u t   for every donor-top field t,
    HIGH (N ≤ j) :  b ∧ H = cut v,

where `m(u)` is the maximum of the request fields with a non-top donor label (present or
future, read from the source vector, empty maximum bottom: `nonTopMax`) and `H` is the cap field
(numerical once present, persistent before: `capField`).  The selector half of HIGH is the
receiving relation.

**The cutoff policy** (`policy`, audit16 (2)): below `N` a positive-cap repair keeps `b` when
`H ≤ b` and clips it at the comparison cap otherwise; it is `K`-visible, carries `b`'s cap
receipt (`policy_min`), and can only activate LOW when it is the clipped value below the cap
(`policy_barrier`).  The **actual pair** with `b` the actual cut is admissible: HIGH is
`cut_actual ≤ vact cap` and LOW is discharged because every donor-top field is literally top
(`actual_tadmissible`), without imposing any physical history. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

/-! ## Order facts about visibility replacement -/

/-- A `k`-visible value strictly below `x` stays strictly below every `k`-replacement of `x`. -/
theorem lt_evr_of_selfVis_lt {k i : ℕ} {a x : ExtOrd} (ha : SelfVis k a) (hax : a < x) :
    a < extVisibilityReplace x k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact absurd hax not_lt_bot
  · rw [extVisibilityReplace_top]; exact hax
  · rw [extVisibilityReplace_ofOrd]
    unfold visibilityReplace
    split_ifs with hβ
    · unfold ordinalReplace
      rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
      · exact bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)
      · exact absurd hax not_top_lt
      · rw [selfVis_ofOrd_iff] at ha
        rw [ofOrd_lt_ofOrd] at hax ⊢
        apply lt_of_limitPart_lt
        rw [limitPart_limitPart_add_nat]
        by_contra hle
        have hle' : limitPart β ≤ limitPart α := not_lt.mp hle
        have h1 : limitPart β + (k : Ordinal) ≤ α :=
          calc limitPart β + (k : Ordinal) ≤ limitPart α + k := add_le_add_left hle' _
            _ ≤ limitPart α + (finitePart α : Ordinal) :=
              (add_le_add_iff_left _).mpr (Nat.cast_le.mpr ha)
            _ = α := decomposition α
        have h2 : β < limitPart β + (k : Ordinal) := by
          conv_lhs => rw [← decomposition β]
          exact (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hβ)
        exact absurd (h2.trans_le h1) (not_lt.mpr hax.le)
    · exact hax

/-- A replacement through `k ≤ K` of a value at most a `K`-visible `b` stays at most `b`. -/
theorem evr_le_of_le_selfVis {K k i : ℕ} {b x : ExtOrd} (hb : SelfVis K b) (hk : k ≤ K)
    (hi : i ≤ k) (hx : x ≤ b) : extVisibilityReplace x k i ≤ b :=
  extVisibilityReplace_le_of_le_selfVis hi (hb.mono hk) hx

/-- Cap agreement below a cap pins every value strictly below the cap. -/
theorem eq_of_capAgree_of_lt {x y γ : ExtOrd} (h : min x γ = min y γ) (hx : x < γ) : y = x := by
  rw [min_eq_left hx.le] at h
  rcases le_total y γ with hy | hy
  · rw [min_eq_left hy] at h
    exact h.symm
  · rw [min_eq_right hy] at h
    exact absurd h hx.ne

/-- Cap agreement below a cap and a value at least the cap force the other value at least the
cap. -/
theorem le_of_capAgree_of_le {x y γ : ExtOrd} (h : min x γ = min y γ) (hx : γ ≤ x) : γ ≤ y := by
  rw [min_eq_right hx] at h
  exact h.symm ▸ min_le_left _ _

namespace CappedDonor

/-! ## The cutoff policy -/

/-- The cutoff policy (audit16 (2)): keep `b` when `H ≤ b`, clip it at `γ` otherwise. -/
noncomputable def policy (b H γ : ExtOrd) : ExtOrd := if H ≤ b then b else min b γ

theorem policy_of_le {b H γ : ExtOrd} (h : H ≤ b) : policy b H γ = b := by
  unfold policy; rw [ite_eq_left h]

theorem policy_of_lt {b H γ : ExtOrd} (h : b < H) : policy b H γ = min b γ := by
  unfold policy; rw [ite_eq_right (not_le.mpr h)]

theorem policy_le (b H γ : ExtOrd) : policy b H γ ≤ b := by
  unfold policy; split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- The policy carries the cap receipt of `b`. -/
theorem policy_min (b H γ : ExtOrd) : min (policy b H γ) γ = min b γ := by
  unfold policy; split_ifs
  · rfl
  · rw [min_assoc, min_self]

theorem policy_selfVis {K : ℕ} {b H γ : ExtOrd} (hb : SelfVis K b) (hγ : SelfVis K γ) :
    SelfVis K (policy b H γ) := by
  unfold policy; split_ifs
  · exact hb
  · exact selfVis_min hb hγ

/-- **The activation barrier** (audit16 (3)): the policy value is below `H` only in the clipped
branch, where it is at most `γ` and the old cutoff was below `H`. -/
theorem policy_barrier {b H γ : ExtOrd} (h : policy b H γ < H) :
    policy b H γ = min b γ ∧ policy b H γ ≤ γ ∧ b < H := by
  have hlt : b < H := by
    by_contra hle
    rw [policy_of_le (not_lt.mp hle)] at h
    exact absurd h (not_lt.mpr (not_lt.mp hle))
  exact ⟨policy_of_lt hlt, by rw [policy_of_lt hlt]; exact min_le_right _ _, hlt⟩

/-- **The floor cap** (audit16 (4)): floors built from cap-equivalent data are cap-equivalent. -/
theorem floor_min {b b' e e' γ : ExtOrd} (hb : min b' γ = min b γ) (he : min e' γ = min e γ) :
    min (max b' e') γ = min (max b e) γ := by
  rw [min_max_distrib_right, min_max_distrib_right, hb, he]

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  (R : Ref I nP N J P C)

/-! ## The low reference -/

/-- **The low reference** (same_grade_LOW_HIGH §2, explicit inputs): an original grade-`K` owner
`c` of the private scheme whose scope contains the private copy of the face, a source cell
`r ≤ c`, the strict source gap on the original row of `c`, and the grade bounds: donor-top
occurrences have grade at most `K`, and `K < N`.  The root arity is unrestricted. -/
structure LowRef (K : ℕ) where
  K_pos : 1 ≤ K
  K_lt_N : K < N
  /-- The low reference owner. -/
  c : Cell C.scheme
  c_grade : C.scheme.grade c = K
  /-- The low reference source, below its owner. -/
  r : C.scheme.below (C.scheme.cell c)
  /-- The private copy of the face lies in the owner's scope. -/
  A'_sub : R.A' ⊆ C.scheme.scope c
  /-- Every donor-top occurrence has grade at most `K`. -/
  top_grade : ∀ d, R.p d = ⊤ → P.scheme.grade d ≤ K
  /-- The strict source gap at the owner (GAP). -/
  gap_c : extVisibilityReplace (C.rows.E c r) K K < C.rows.E c ⟨c, GradedLe.refl _⟩
  /-- The strict source gap at every donor-top face cell (GAP). -/
  gap_top : ∀ (a : P.scheme.below (R.A, R.KA))
    (h : GradedLe (C.scheme.cell (R.face a).1) (C.scheme.cell c)),
    R.p a.1 = ⊤ → extVisibilityReplace (C.rows.E c r) K K < C.rows.E c ⟨(R.face a).1, h⟩

namespace LowRef

variable {R} {K : ℕ} (L : R.LowRef K)

/-- The lower domain of the low reference owner. -/
abbrev Dom : Type := C.scheme.below (C.scheme.cell L.c)

/-- The owner in its own lower domain. -/
def cL : L.Dom := ⟨L.c, GradedLe.refl _⟩

theorem grade_dom (d : L.Dom) : C.scheme.grade d.1 ≤ K := d.2.2.trans_eq L.c_grade

/-- A face cell of grade at most `K` lies in the owner's lower domain. -/
theorem face_le_dom (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ K) :
    GradedLe (C.scheme.cell (R.face a).1) (C.scheme.cell L.c) :=
  ⟨(R.face a).2.1.trans L.A'_sub, (R.face_grade a).trans_le (h.trans_eq L.c_grade.symm)⟩

/-- A face cell of grade at most `K` in the owner's lower domain. -/
def faceLow (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ K) : L.Dom :=
  ⟨(R.face a).1, L.face_le_dom a h⟩

theorem faceLow_val (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ K) :
    (L.faceLow a h).1 = (R.face a).1 := rfl

/-- The rounded source of the low reference. -/
noncomputable def h : ExtOrd := extVisibilityReplace (C.rows.E L.c L.r) K K

theorem h_selfVis : SelfVis K L.h := TopSupport.selfVis_evr_self K _

theorem h_lt_c : L.h < C.rows.E L.c L.cL := L.gap_c

theorem h_lt_top (a : P.scheme.below (R.A, R.KA)) (ht : R.p a.1 = ⊤) :
    L.h < C.rows.E L.c (L.faceLow a (L.top_grade a.1 ht)) :=
  L.gap_top a (L.face_le_dom a (L.top_grade a.1 ht)) ht

theorem srcE_r_le_h : C.rows.E L.c L.r ≤ L.h := TopSupport.le_evr_self _ K

/-! ## The frontier -/

/-- The frontier `e v = v c ∧ R_K (v r)`. -/
noncomputable def e (v : L.Dom → ExtOrd) : ExtOrd :=
  min (v L.cL) (extVisibilityReplace (v L.r) K K)

theorem e_le_c (v : L.Dom → ExtOrd) : L.e v ≤ v L.cL := min_le_left _ _

theorem e_congr {v₁ v₂ : L.Dom → ExtOrd} (hc : v₁ L.cL = v₂ L.cL) (hr : v₁ L.r = v₂ L.r) :
    L.e v₁ = L.e v₂ := by
  unfold e; rw [hc, hr]

/-- The frontier commutes with every `K`-visible cap. -/
theorem e_min {γ : ExtOrd} (hγ : SelfVis K γ) (v : L.Dom → ExtOrd) :
    L.e (fun d => min (v d) γ) = min (L.e v) γ := by
  unfold e
  rw [evr_min_of_selfVis hγ le_rfl le_rfl, min_min_min_comm, min_self]

section Lawful

variable {v : L.Dom → ExtOrd} (hv : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) v)
include hv

theorem c_selfVis : SelfVis K (v L.cL) := by
  have h : SelfVis (C.scheme.grade L.c) (v L.cL) := (hv.orderly L.cL).symm
  rwa [L.c_grade] at h

theorem e_selfVis : SelfVis K (L.e v) :=
  selfVis_min (L.c_selfVis hv) (TopSupport.selfVis_evr_self K _)

/-- One exact bounded witness for any lawful labelling of the owner's lower domain. -/
theorem exists_witness : ∃ τ : ExtOrd → ExtOrd, Witness (gTop K) τ ∧ (∀ x, τ x ≤ v L.cL) ∧
    ∀ d : L.Dom, τ (C.rows.E L.c d) = min (v d) (v L.cL) := by
  have h := exists_bounded_exact_capped_witness (grade := fun d : L.Dom => C.scheme.grade d.1)
    (c := L.cL) (p := v) (fun d => d.2.2) (hv.orderly L.cL).symm (hv.locality L.cL)
  have hg : C.scheme.grade L.cL.1 = K := L.c_grade
  rwa [hg] at h

omit hv in
/-- The frontier is the witness's reading of the rounded source. -/
theorem e_eq_read {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop K) τ)
    (hread : ∀ d : L.Dom, τ (C.rows.E L.c d) = min (v d) (v L.cL)) (hvis : SelfVis K (v L.cL)) :
    L.e v = τ L.h := by
  unfold e h
  rw [hτ.comm_gTop _ le_rfl, hread, evr_min_of_selfVis hvis le_rfl le_rfl, min_comm]

/-- The frontier is at most every donor-top face value (GAP through the witness). -/
theorem e_le_top (a : P.scheme.below (R.A, R.KA)) (ht : R.p a.1 = ⊤) :
    L.e v ≤ v (L.faceLow a (L.top_grade a.1 ht)) := by
  obtain ⟨τ, hτ, -, hread⟩ := L.exists_witness hv
  rw [L.e_eq_read hτ hread (L.c_selfVis hv)]
  exact (hτ.mono (L.h_lt_top a ht).le).trans ((hread _).le.trans (min_le_left _ _))

end Lawful

/-! ## The frontier at a cutoff -/

theorem domLe {j : ℕ} (hj : K ≤ j) : GradedLe (C.scheme.cell L.c) (effC J j) :=
  ⟨Finset.subset_univ _, by
    change C.scheme.grade L.c ≤ min j J
    rw [L.c_grade]; exact le_min hj (L.K_lt_N.le.trans R.N_le)⟩

/-- The restriction of a present private section to the owner's lower domain. -/
def lowD {j : ℕ} (hj : K ≤ j) (v : C.scheme.below (effC J j) → ExtOrd) (d : L.Dom) : ExtOrd :=
  v (CellScheme.below.mono (L.domLe hj) d)

theorem lowD_respects {j : ℕ} (hj : K ≤ j) {v : C.scheme.below (effC J j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC J j) v) :
    RespectsSemanticsBelow C.rows (C.scheme.cell L.c) (L.lowD hj v) :=
  hv.mono (L.domLe hj)

theorem lowD_face {j : ℕ} (hj : K ≤ j) (v : C.scheme.below (effC J j) → ExtOrd)
    (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ K) :
    L.lowD hj v (L.faceLow a h) = v (R.privFace a (h.trans hj)) := rfl

/-- The frontier of a present private section. -/
noncomputable def eC {j : ℕ} (hj : K ≤ j) (v : C.scheme.below (effC J j) → ExtOrd) : ExtOrd :=
  L.e (L.lowD hj v)

theorem eC_selfVis {j : ℕ} (hj : K ≤ j) {v : C.scheme.below (effC J j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC J j) v) : SelfVis K (L.eC hj v) :=
  L.e_selfVis (L.lowD_respects hj hv)

theorem eC_min {j : ℕ} (hj : K ≤ j) {γ : ExtOrd} (hγ : SelfVis K γ)
    (v : C.scheme.below (effC J j) → ExtOrd) :
    L.eC hj (fun d => min (v d) γ) = min (L.eC hj v) γ :=
  L.e_min hγ (L.lowD hj v)

/-- Cap agreement of two present sections gives cap agreement of their frontiers. -/
theorem eC_agree {j : ℕ} (hj : K ≤ j) {γ : ExtOrd} (hγ : SelfVis K γ)
    {v v₁ : C.scheme.below (effC J j) → ExtOrd} (hagree : ∀ d, min (v₁ d) γ = min (v d) γ) :
    min (L.eC hj v₁) γ = min (L.eC hj v) γ := by
  rw [← L.eC_min hj hγ, ← L.eC_min hj hγ]
  congr 1
  funext d
  exact hagree _

theorem eC_le_top {j : ℕ} (hj : K ≤ j) {v : C.scheme.below (effC J j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC J j) v) (a : P.scheme.below (R.A, R.KA))
    (ht : R.p a.1 = ⊤) : L.eC hj v ≤ v (R.privFace a ((L.top_grade a.1 ht).trans hj)) :=
  L.e_le_top (L.lowD_respects hj hv) a ht

include L in
/-- A cap permissible at the cutoff is `K`-visible once the low reference is present. -/
theorem selfVis_K_of_effC {j : ℕ} (hj : K ≤ j) {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) :
    SelfVis K γ := hγ.mono (le_min hj ((L.K_lt_N).le.trans R.N_le))

end LowRef

/-! ## Two-threshold states -/

/-- A two-threshold state: a receiving state and the stored cutoff. -/
structure TState (R : Ref I nP N J P C) (j : ℕ) where
  /-- The receiving state. -/
  st : R.State j
  /-- The stored cutoff. -/
  b : ExtOrd

variable {R}

open Classical in
/-- The maximum of the request fields with a non-top donor label, present or future (empty
maximum bottom). -/
noncomputable def State.nonTopMax {j : ℕ} (st : R.State j) : ExtOrd :=
  (Finset.univ.filter fun d : Cell P.scheme => R.p d ≠ ⊤).sup fun d => st.sourceProfile (.req d)

/-- The cap field: numerical once present, persistent before. -/
noncomputable def State.capField {j : ℕ} (st : R.State j) : ExtOrd := st.sourceProfile (.priv R.cap)

theorem State.le_nonTopMax {j : ℕ} (st : R.State j) {d : Cell P.scheme} (hd : R.p d ≠ ⊤) :
    st.sourceProfile (.req d) ≤ st.nonTopMax := by
  classical
  exact Finset.le_sup (f := fun d => st.sourceProfile (.req d)) (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hd⟩)

theorem State.nonTopMax_lt_iff {j : ℕ} (st : R.State j) {b : ExtOrd} (hb : ⊥ < b) :
    st.nonTopMax < b ↔ ∀ d, R.p d ≠ ⊤ → st.sourceProfile (.req d) < b := by
  classical
  unfold State.nonTopMax
  rw [Finset.sup_lt_iff hb]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem State.nonTopMax_congr {j : ℕ} {st st₁ : R.State j}
    (h : ∀ d, R.p d ≠ ⊤ → st₁.sourceProfile (.req d) = st.sourceProfile (.req d)) :
    st₁.nonTopMax = st.nonTopMax := by
  classical
  unfold State.nonTopMax
  apply Finset.sup_congr rfl
  intro d hd
  exact h d (Finset.mem_filter.mp hd).2

theorem State.capField_of_present {j : ℕ} (st : R.State j) (hj : N ≤ j) :
    st.capField = st.v (R.capC hj) := by
  unfold State.capField
  rw [st.sourceProfile_of_present (f := .priv R.cap) (by
    change C.scheme.grade R.cap ≤ j; rw [R.grade_cap]; exact hj)]
  rfl

theorem State.capField_of_future {j : ℕ} (st : R.State j) (hj : ¬ N ≤ j) :
    st.capField = st.shadowC R.cap := by
  unfold State.capField
  rw [st.sourceProfile_of_future (f := .priv R.cap) (by
    change ¬ C.scheme.grade R.cap ≤ j; rw [R.grade_cap]; exact hj)]
  rfl

theorem State.sourceProfile_req_of_present {j : ℕ} (st : R.State j) (d : Cell P.scheme)
    (h : P.scheme.grade d ≤ j) : st.sourceProfile (.req d) = st.u (reqCell d h) :=
  st.sourceProfile_of_present (f := .req d) h

theorem State.sourceProfile_req_of_future {j : ℕ} (st : R.State j) (d : Cell P.scheme)
    (h : ¬ P.scheme.grade d ≤ j) : st.sourceProfile (.req d) = st.shadowP d :=
  st.sourceProfile_of_future (f := .req d) h

/-- **Two-threshold admissibility**: receiving admissibility, `K`-visibility of the stored
cutoff, LOW from grade `K` and HIGH from grade `N` (its selector half is the receiving
relation). -/
structure LowRef.TAdmissible {K : ℕ} (L : R.LowRef K) {j : ℕ} (S : R.TState j) : Prop where
  adm : R.Admissible S.st
  /-- The stored cutoff's persistent grade-one observation. -/
  b_vis : SelfVis 1 S.b
  /-- The stored cutoff is `K`-visible once numerically present. -/
  b_visK : K ≤ j → SelfVis K S.b
  low : ∀ hj : K ≤ j, S.st.gate ≠ ⊥ → S.st.nonTopMax < S.b → S.b < S.st.capField →
    ∀ t (ht : R.p t = ⊤),
      max S.b (L.eC hj S.st.v) ≤ S.st.u (reqCell t ((L.top_grade t ht).trans hj))
  high : ∀ hj : N ≤ j, S.st.gate ≠ ⊥ → min S.b (S.st.v (R.capC hj)) = R.cut (R.lowC hj S.st.v)

/-! ## The actual state -/

variable (R) in
/-- The actual two-threshold state: the actual pair with the stored cutoff the actual cut. -/
noncomputable def actualTState (j : ℕ) : R.TState j := ⟨R.actualState j, R.cut R.vactL⟩

/-- The actual state is admissible: HIGH because the actual cut is below the actual cap, LOW
because every donor-top field is literally top — no physical history is imposed. -/
theorem LowRef.actual_tadmissible {K : ℕ} (L : R.LowRef K) (j : ℕ) :
    L.TAdmissible (R.actualTState j) where
  adm := R.actual_admissible j
  b_vis := (R.selfVis_cut (Active.selfVis_cap R R.actual_active)).mono (L.K_pos.trans L.K_lt_N.le)
  b_visK _ := (R.selfVis_cut (Active.selfVis_cap R R.actual_active)).mono L.K_lt_N.le
  low _ _ _ _ t ht := by
    change _ ≤ R.p t
    rw [ht]; exact le_top
  high _ _ := by
    change min (R.cut R.vactL) (R.vact R.cap) = R.cut R.vactL
    exact min_eq_left (R.cut_le_cap _)

end Ref

end CappedDonor

end VaughtConjecture.Knight
