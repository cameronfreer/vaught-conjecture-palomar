/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowRef
public import VaughtConjecture.Knight.SourceBlockLocalityTransport

/-! # Exact release of the private frontier (audit16 §2, note §3.2)

The second original-row operation of the two-threshold family, on the **unchanged private scheme
`C`**, from the strict source gap (GAP) and numerical shielding.

Every extension call below goes through the equal-index form of bountifulness
(`Semantics.IsBountiful.extend`, in `CappedDonorReceiving`), so no separate case is needed when
the owner's lower domain is the whole cutoff or the low face is the owner's whole lower domain.

**Exact frontier release, arbitrary root** (`LowRef.exists_release`; newapproach2 §5): let `v`
be lawful at a cutoff `j ≥ K`, let `γ > ⊥` be permissible there, and suppose the frontier
exceeds `γ` while every present donor non-top face value is strictly below `γ` (SHIELD, on the
whole present root, high grades included).  Then there is a lawful `v'` with the whole present
face literal, every value retained below `γ`, the low source exactly `γ`, the owner's value not
lowered, and frontier exactly `γ`:

* with `L = v c > γ` and `τ` the exact normalized witness of `v` at `c`, retune
  `ν x = τ x ∧ γ` for `x ≤ h` and `ν x = τ x` above `h` (`releaseShifter`) — bounded, monotone
  and replacement-compatible through `K` because `h` is `K`-visible (`releaseShifter_witness`);
* `w = ν ∘ E_c` is lawful on the owner's whole lower domain by source-block transport: it has the
  bottom pattern of the lawful capped old target `v ∧ L = τ ∘ E_c` because `γ` is positive;
  GAP keeps the donor-top face values at `τ ∘ E_c`, SHIELD keeps the non-top ones, so
  `w = v ∧ L` on the face, `w c = L` and `w r = γ`;
* restore the exact **grade-`≤ K` part of the face** at cap `L` inside the owner's lower domain
  (`L` is a valid grade-`K` cap there; an empty low part needs no call) and prescribe the result
  into the cutoff at cap `γ` by old `C`-bountifulness — two extension calls inside the unchanged
  `C`;
* a face cell of grade above `K` is donor non-top, so SHIELD and the `γ`-cap agreement fix its
  value exactly: the two caps `L` (through `K` only) and `γ` (at the cutoff) are kept apart.

This may alter private values above `γ`; it does not retain them literally.  Still-future
coordinates are outside the current numerical domain and are untouched when the lemma is applied
to a source-state fibre. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd SharpWitnessComposition AmalgamationPlan

namespace CappedDonor

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C} {K : ℕ} (L : R.LowRef K)

namespace LowRef

/-! ## The release shifter -/

/-- The release shifter: the old witness capped at `γ` up to `h`, the old witness above. -/
noncomputable def releaseShifter (τ : ExtOrd → ExtOrd) (h γ : ExtOrd) (x : ExtOrd) : ExtOrd :=
  if x ≤ h then min (τ x) γ else τ x

omit L in
theorem releaseShifter_of_le {τ : ExtOrd → ExtOrd} {h γ x : ExtOrd} (hx : x ≤ h) :
    releaseShifter τ h γ x = min (τ x) γ := by
  unfold releaseShifter; rw [ite_eq_left hx]

omit L in
theorem releaseShifter_of_lt {τ : ExtOrd → ExtOrd} {h γ x : ExtOrd} (hx : h < x) :
    releaseShifter τ h γ x = τ x := by
  unfold releaseShifter; rw [ite_eq_right (not_le.mpr hx)]

omit L in
theorem releaseShifter_eq_bot_iff {τ : ExtOrd → ExtOrd} {h γ : ExtOrd} (hγ : γ ≠ ⊥) (x : ExtOrd) :
    releaseShifter τ h γ x = ⊥ ↔ τ x = ⊥ := by
  unfold releaseShifter
  split_ifs
  · simp only [min_eq_bot, hγ, or_false]
  · exact Iff.rfl

omit L in
theorem releaseShifter_le {τ : ExtOrd → ExtOrd} (h γ x : ExtOrd) :
    releaseShifter τ h γ x ≤ τ x := by
  unfold releaseShifter
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

omit L in
/-- The release shifter is a normalized witness through `K` whenever the old witness is, the
split point `h` and the cap `γ` are `K`-visible and `γ` is positive. -/
theorem releaseShifter_witness {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop K) τ) {h γ : ExtOrd}
    (hh : SelfVis K h) (hγ : SelfVis K γ) (hγpos : γ ≠ ⊥) :
    Witness (gTop K) (releaseShifter τ h γ) where
  anti := hτ.anti
  vis := hτ.vis
  bot := by rw [releaseShifter_of_le bot_le, hτ.bot, min_bot_left]
  mono := by
    intro x y hxy
    by_cases hy : y ≤ h
    · rw [releaseShifter_of_le (hxy.trans hy), releaseShifter_of_le hy]
      exact min_le_min_right _ (hτ.mono hxy)
    · rw [releaseShifter_of_lt (not_le.mp hy)]
      exact (releaseShifter_le h γ x).trans (hτ.mono hxy)
  clause5 := by
    intro x kk hle i hi
    by_cases hkk : kk ≤ K
    · have h1 : τ (extVisibilityReplace x kk i) = extVisibilityReplace (τ x) kk i :=
        hτ.clause5 x kk (by rw [gTop_of_le hkk]; exact le_top) i hi
      by_cases hx : x ≤ h
      · rw [releaseShifter_of_le hx, releaseShifter_of_le (evr_le_of_le_selfVis hh hkk hi hx), h1,
          evr_min_of_selfVis hγ hkk hi]
      · rw [releaseShifter_of_lt (not_le.mp hx),
          releaseShifter_of_lt (lt_evr_of_selfVis_lt (hh.mono hkk) (not_le.mp hx)), h1]
    · rw [gTop_of_gt (not_le.mp hkk), le_bot_iff] at hle
      have hx : τ x = ⊥ := (releaseShifter_eq_bot_iff hγpos x).mp hle
      have h1 : τ (extVisibilityReplace x kk i) = ⊥ := by
        rw [hτ.clause5 x kk (by rw [gTop_of_gt (not_le.mp hkk), hx]) i hi, hx,
          extVisibilityReplace_bot]
      rw [hle, extVisibilityReplace_bot]
      exact (releaseShifter_eq_bot_iff hγpos _).mpr h1

/-! ## Geometry of the owner's lower domain at a cutoff -/

/-- The low part of the face lies in the owner's lower domain. -/
theorem faceLe : GradedLe (R.A', min R.KA K) (C.scheme.cell L.c) :=
  ⟨L.A'_sub, (min_le_right _ _).trans_eq L.c_grade.symm⟩

theorem grade_cell_c : (C.scheme.cell L.c).2 = K := L.c_grade

/-- The owner as a present private cell. -/
def cC {j : ℕ} (hj : K ≤ j) : C.scheme.below (effC J j) := CellScheme.below.mono (L.domLe hj) L.cL

/-- The low source as a present private cell. -/
def rC {j : ℕ} (hj : K ≤ j) : C.scheme.below (effC J j) := CellScheme.below.mono (L.domLe hj) L.r

theorem lowD_cL {j : ℕ} (hj : K ≤ j) (v : C.scheme.below (effC J j) → ExtOrd) :
    L.lowD hj v L.cL = v (L.cC hj) := rfl

theorem lowD_r {j : ℕ} (hj : K ≤ j) (v : C.scheme.below (effC J j) → ExtOrd) :
    L.lowD hj v L.r = v (L.rC hj) := rfl

/-- The frontier bounds the low source from below at a positive cap. -/
theorem le_r_of_lt_e {v : L.Dom → ExtOrd} {γ : ExtOrd} (hγ : SelfVis K γ) (he : γ < L.e v) :
    γ ≤ v L.r := by
  by_contra hlt
  have h1 : extVisibilityReplace (v L.r) K K ≤ γ :=
    evr_le_of_le_selfVis hγ le_rfl le_rfl (not_le.mp hlt).le
  exact absurd ((he.trans_le (min_le_right _ _)).trans_le h1) (lt_irrefl _)

/-! ## Exact frontier release -/

/-- **Exact frontier release, arbitrary root** (audit16 §2 (1), note §3.2; newapproach2 §5):
with the frontier above a positive permissible cap `γ` and every present donor non-top face
value strictly below `γ` (SHIELD), there is a lawful private section with the whole present face
literal, every value retained below `γ`, the low source exactly `γ`, the owner's value not
lowered, and frontier exactly `γ`. -/
theorem exists_release {j : ℕ} (hj : K ≤ j) {v : C.scheme.below (effC J j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC J j) v) {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ)
    (hγpos : γ ≠ ⊥) (he : γ < L.eC hj v)
    (hshield : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j), R.p a.1 ≠ ⊤ →
      v (R.privFace a h) < γ) :
    ∃ v' : C.scheme.below (effC J j) → ExtOrd, RespectsSemanticsBelow C.rows (effC J j) v' ∧
      (∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
        v' (R.privFace a h) = v (R.privFace a h)) ∧
      (∀ d, min (v' d) γ = min (v d) γ) ∧ v' (L.rC hj) = γ ∧ v (L.cC hj) ≤ v' (L.cC hj) ∧
      L.eC hj v' = γ := by
  have hγK : SelfVis K γ := L.selfVis_K_of_effC hj hγ
  -- the old section on the owner's lower domain and its exact witness
  set w₀ := L.lowD hj v with hw₀def
  have hw₀ : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) w₀ := L.lowD_respects hj hv
  have hLvis : SelfVis K (w₀ L.cL) := L.c_selfVis hw₀
  have hγL : γ < w₀ L.cL := he.trans_le (L.e_le_c _)
  have hγr : γ ≤ w₀ L.r := L.le_r_of_lt_e hγK he
  obtain ⟨τ, hτ, -, hread⟩ := L.exists_witness hw₀
  -- the retuned shifter and the released section on the owner's lower domain
  have hν : Witness (gTop K) (releaseShifter τ L.h γ) :=
    releaseShifter_witness hτ L.h_selfVis hγK hγpos
  set w : L.Dom → ExtOrd := fun d => releaseShifter τ L.h γ (C.rows.E L.c d) with hwdef
  have hE : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) (C.rows.E L.c) := C.consistent L.c
  have hgrade : ∀ d : L.Dom, C.scheme.grade d.1 ≤ K := L.grade_dom
  -- the capped old target is lawful with the same bottom pattern
  have hcapL : extVisibilityReplace (w₀ L.cL) (C.scheme.cell L.c).2 (C.scheme.cell L.c).2 =
      w₀ L.cL := by
    rw [L.grade_cell_c]; exact hLvis
  have ht : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) (fun d => τ (C.rows.E L.c d)) := by
    have := hw₀.cap hcapL
    have heq : (fun d : L.Dom => τ (C.rows.E L.c d)) = fun d => min (w₀ d) (w₀ L.cL) :=
      funext hread
    rw [heq]; exact this
  have hw : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) w := by
    refine (map_respects_iff_rowBlockBottom hE hgrade (boundedMap_of_witness hν)).mpr ?_
    refine rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects ht) fun d => ?_
    exact releaseShifter_eq_bot_iff hγpos _
  -- values of the released section
  have hwc : w L.cL = w₀ L.cL := by
    change releaseShifter τ L.h γ (C.rows.E L.c L.cL) = _
    rw [releaseShifter_of_lt L.h_lt_c, hread, min_self]
  have hwr : w L.r = γ := by
    change releaseShifter τ L.h γ (C.rows.E L.c L.r) = _
    rw [releaseShifter_of_le L.srcE_r_le_h, hread]
    exact min_eq_right (le_min hγr hγL.le)
  have hwcap : ∀ d, min (w d) γ = min (w₀ d) γ := by
    intro d
    change min (releaseShifter τ L.h γ (C.rows.E L.c d)) γ = _
    unfold releaseShifter
    split_ifs
    · rw [hread, min_assoc, min_self, min_assoc, min_eq_right hγL.le]
    · rw [hread, min_assoc, min_eq_right hγL.le]
  have hwface : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ K),
      w (L.faceLow a h) = min (w₀ (L.faceLow a h)) (w₀ L.cL) := by
    intro a h
    change releaseShifter τ L.h γ (C.rows.E L.c (L.faceLow a h)) = _
    by_cases hat : R.p a.1 = ⊤
    · have hlt : L.h < C.rows.E L.c (L.faceLow a h) := L.h_lt_top a hat
      rw [releaseShifter_of_lt hlt, hread]
    · have hlt : w₀ (L.faceLow a h) < γ := hshield a (h.trans hj) hat
      unfold releaseShifter
      split_ifs
      · rw [hread, min_eq_left ((min_le_left _ _).trans hlt.le)]
      · rw [hread]
  -- restore the exact low part of the face at cap `L` inside the owner's lower domain
  have hrest : ∃ w' : L.Dom → ExtOrd, RespectsSemanticsBelow C.rows (C.scheme.cell L.c) w' ∧
      (∀ d, min (w' d) (w₀ L.cL) = min (w d) (w₀ L.cL)) ∧
      ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ K),
        w' (L.faceLow a h) = w₀ (L.faceLow a h) := by
    by_cases hk : 0 < min R.KA K
    · obtain ⟨w', hw', hcap', hface'⟩ := C.bountiful.extend (R.face_mem' hk (min_le_left _ _))
        (C.scheme.cell_mem L.c) L.faceLe (hw₀.mono L.faceLe) hw hcapL (by
          intro x
          have hx : P.scheme.grade (R.face.symm (R.faceLift' (min_le_left _ _) x)).1 ≤ K := by
            rw [R.face_symm_grade]; exact x.2.2.trans (min_le_right _ _)
          have e : CellScheme.below.mono L.faceLe x =
              L.faceLow (R.face.symm (R.faceLift' (min_le_left _ _) x)) hx := by
            apply Subtype.ext
            change x.1 = (R.face (R.face.symm (R.faceLift' _ x))).1
            rw [Equiv.apply_symm_apply]
            rfl
          rw [e, hwface _ hx, min_assoc, min_self])
      refine ⟨w', hw', hcap', fun a h => ?_⟩
      have hb : GradedLe (C.scheme.cell (R.face a).1) (R.A', min R.KA K) :=
        ⟨(R.face a).2.1, le_min ((R.face_grade a).trans_le a.2.2) ((R.face_grade a).trans_le h)⟩
      exact hface' ⟨(R.face a).1, hb⟩
    · exact ⟨w, hw, fun _ => rfl, fun a h => (R.face_absent hk a h).elim⟩
  obtain ⟨w', hw', hcap', hface'⟩ := hrest
  have hw'r : w' L.r = γ := by
    have h := hcap' L.r
    rw [hwr, min_eq_left hγL.le] at h
    exact eq_of_capAgree_of_lt (x := γ) (by rw [min_eq_left hγL.le]; exact h.symm) hγL
  have hw'c : w₀ L.cL ≤ w' L.cL := by
    have h := hcap' L.cL
    rw [hwc, min_self] at h
    exact le_of_capAgree_of_le (x := w₀ L.cL) (by rw [min_self]; exact h.symm) le_rfl
  have hw'cap : ∀ d, min (w' d) γ = min (w₀ d) γ := by
    intro d
    calc min (w' d) γ = min (min (w' d) (w₀ L.cL)) γ := by rw [min_assoc, min_eq_right hγL.le]
      _ = min (min (w d) (w₀ L.cL)) γ := by rw [hcap' d]
      _ = min (w d) γ := by rw [min_assoc, min_eq_right hγL.le]
      _ = min (w₀ d) γ := hwcap d
  -- prescribe the released lower section into the cutoff at cap `γ`
  obtain ⟨v', hv', hcap, hlow⟩ := C.bountiful.extend (C.scheme.cell_mem L.c)
    (R.effC_mem' (L.K_pos.trans hj)) (L.domLe hj) hw' hv hγ (fun d => (hw'cap d).symm)
  have hlowD : L.lowD hj v' = w' := funext fun d => hlow d
  refine ⟨v', hv', fun a h => ?_, hcap, ?_, ?_, ?_⟩
  · by_cases hK : P.scheme.grade a.1 ≤ K
    · change L.lowD hj v' (L.faceLow a hK) = L.lowD hj v (L.faceLow a hK)
      rw [hlowD]
      exact hface' a hK
    · exact eq_of_capAgree_of_lt (hcap _).symm (hshield a h fun ht => hK (L.top_grade a.1 ht))
  · change L.lowD hj v' L.r = γ
    rw [hlowD, hw'r]
  · change L.lowD hj v L.cL ≤ L.lowD hj v' L.cL
    rw [hlowD]; exact hw'c
  · unfold eC
    rw [hlowD]
    unfold e
    rw [hw'r, evr_eq_self_of_selfVis hγK, min_eq_right (hγL.le.trans hw'c)]

end LowRef

end Ref

end CappedDonor

end VaughtConjecture.Knight
