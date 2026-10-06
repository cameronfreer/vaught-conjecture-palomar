/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowHighFibres

/-! # The HIGH/LOW readback consumer from explicit chart receipts (newapproach2 §7 of new4)

The **semantic half** of the probe readback of the reviewer's new4 §7: what an admissible
two-threshold state reads back once the physical charts have supplied their receipts.  Nothing
here constructs a state or a physical probe; the receipts are explicit hypotheses.

* **The high chart** (`LowRef.high_readback`, new4 §7.1): at a cutoff where the cap is present,
  with a positive gate and the **actual cap and reference values** (the receipts of a bounded
  grade-`N` chart), HIGH pins the stored cutoff to the actual cut (`cut_actual_lt_cap`: the actual
  cut lies strictly below the actual cap by the endpoint margin, so `b ∧ H = B` cancels), the
  receiving relation reads every donor non-top request field back literally (`nonTop_readback`),
  hence the non-top maximum is strictly below the stored cutoff as soon as the actual cut is
  positive (the block-zero comparison reference of audit18 §5 supplies that), and the stored
  cutoff is strictly below the cap field.  That is exactly LOW's antecedent, obtained from
  numerical receipts — not from the donor's non-top tags.
* **The low chart makes LOW exact** (`LowRef.readback`, new4 §7.2): with, in addition, the low
  frontier **top** (`LowRef.eC_top`: the owner and the low source read top, the receipt of a
  grade-`K` controller with value top), LOW forces every donor-top request field to be top.
  Together, the current request section **is** the donor labelling (`readback_eq`).

**The probe contract** (`LowRef.readback_of_actualFace`): every receipt except the rendered
state's admissibility and the gate is the value of the **actual private labelling at an actual
occurrence**, so a probe section that retains the actual private face literally supplies them
all at once.  Receipt by receipt:

* `hcap` (the cap value): supplied by the full-scope grade-`N` controller `F.cell` of the
  reference context (`Ref.cap`, `cap_cell`); its chart is the cap's own row `E_cap` on `Low`
  through the exact bounded witness `Ref.exists_witness` — the grade-`N` chart, clipped at `H`.
* `href i` (the reference values): supplied by the block representatives `C.repBase i`
  (`Ref.ref`, `vact_ref`), block `0` included; read through the same grade-`N` chart
  (`read_ref_rep`).
* `hcut` (the positive actual cut): supplied by the block-zero comparison representative
  (audit18 §5, `exists_ref_zero`); no chart, an order fact (`cut_actual`).
* `hc`, `hr` (the owner and the low source top): supplied by the surviving full-scope grade-`K`
  owner `c` and the lost top `r` of the protected-flexibility alternative — both **actual tops**
  (`LowRef.exists_of_protectedFlex_top`); their chart is the owner's own row `E_c` through the
  exact bounded witness `LowRef.exists_witness` — the grade-`K` chart, uncapped since
  `vact c = ⊤`.
* `hg` (the positive gate): a grade-one node of the probe kept non-bottom by bottom-pattern
  realization (new4 §8); no chart.
* `hS` (`TAdmissible` at `j ≥ N`): the rendered two-threshold state of the probe section; built
  from the guarded source rows of the probe (new4 §§3–6), HIGH through the cap's row and LOW
  through `c`'s row.
The last two items are the physical obligations proper: rendering an arbitrary lawful probe
section as an admissible two-threshold state (with its charts the witnesses of the two installed
rows above), and bottom-pattern realization keeping the gate node positive.  Nothing here asserts
either; `readback_of_actualFace` states exactly what they must deliver. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

namespace CappedDonor

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-- The actual cut lies strictly below the actual cap (the endpoint margin). -/
theorem cut_actual_lt_cap : R.cut R.vactL < R.vact R.cap := by
  rw [R.cut_actual]
  exact (Finset.sup_lt_iff R.cap_pos).mpr fun i _ => R.margin i

variable {K : ℕ} (L : R.LowRef K)

/-- The low frontier is top when the owner and the low source read top. -/
theorem LowRef.eC_top {j : ℕ} (hj : K ≤ j) {v : C.scheme.below (effC J j) → ExtOrd}
    (hc : v (L.cC hj) = ⊤) (hr : v (L.rC hj) = ⊤) : L.eC hj v = ⊤ := by
  unfold LowRef.eC LowRef.e
  rw [L.lowD_cL, L.lowD_r, hc, hr, extVisibilityReplace_top, min_self]

/-- **The high chart** (new4 §7.1): with the cap present, a positive gate and the actual cap and
reference values, the stored cutoff is the actual cut, every donor non-top request field reads
the donor label literally, the non-top maximum lies strictly below the stored cutoff whenever the
actual cut is positive, and the stored cutoff lies strictly below the cap field. -/
theorem LowRef.high_readback {j : ℕ} (hj : N ≤ j) {S : R.TState j} (hS : L.TAdmissible S)
    (hg : S.st.gate ≠ ⊥) (hcap : S.st.v (R.capC hj) = R.vact R.cap)
    (href : ∀ i, S.st.v (CellScheme.below.mono (R.capLe hj) (R.lowRef i)) = R.vact (R.ref i)) :
    S.b = R.cut R.vactL ∧
      (∀ d : P.scheme.below (effP nP j), R.p d.1 ≠ ⊤ → S.st.u d = R.p d.1) ∧
      (⊥ < R.cut R.vactL → S.st.nonTopMax < S.b) ∧ S.b < S.st.capField := by
  have hcut : R.cut (R.lowC hj S.st.v) = R.cut R.vactL := cut_congr hcap href
  have hhigh := hS.high hj hg
  rw [hcut, hcap] at hhigh
  have hlt := cut_actual_lt_cap (R := R)
  have hb : S.b = R.cut R.vactL := by
    have h1 : min (R.cut R.vactL) (R.vact R.cap) = min S.b (R.vact R.cap) := by
      rw [min_eq_left hlt.le, hhigh]
    exact eq_of_capAgree_of_lt h1 hlt
  obtain ⟨hnon, -⟩ := R.nonTop_readback hj hS.adm hg hcap href
  refine ⟨hb, hnon, fun hpos => ?_, ?_⟩
  · rw [hb, S.st.nonTopMax_lt_iff hpos]
    intro d hd
    have h2 : S.st.u (reqCell d ((R.gradeP_lt_N d).le.trans hj)) = R.p d :=
      hnon (reqCell d ((R.gradeP_lt_N d).le.trans hj)) hd
    rw [S.st.sourceProfile_req_of_present d ((R.gradeP_lt_N d).le.trans hj), h2]
    by_cases hbot : R.p d = ⊥
    · rw [hbot]; exact hpos
    · exact R.p_lt_cut_actual ⟨hbot, hd⟩
  · rw [S.st.capField_of_present hj, hcap, hb]
    exact hlt

/-- **The low chart makes LOW exact** (new4 §7.2): with the receipts of the high chart, a
positive actual cut and the low frontier top, every request field reads the donor label
literally — the donor tops as top. -/
theorem LowRef.readback {j : ℕ} (hj : N ≤ j) (hcut : ⊥ < R.cut R.vactL) {S : R.TState j}
    (hS : L.TAdmissible S) (hg : S.st.gate ≠ ⊥) (hcap : S.st.v (R.capC hj) = R.vact R.cap)
    (href : ∀ i, S.st.v (CellScheme.below.mono (R.capLe hj) (R.lowRef i)) = R.vact (R.ref i))
    (he : L.eC (L.K_lt_N.le.trans hj) S.st.v = ⊤) :
    S.b = R.cut R.vactL ∧ ∀ d : P.scheme.below (effP nP j), S.st.u d = R.p d.1 := by
  obtain ⟨hb, hnon, hm, hH⟩ := L.high_readback hj hS hg hcap href
  refine ⟨hb, fun d => ?_⟩
  by_cases hd : R.p d.1 = ⊤
  · have hlow := hS.low (L.K_lt_N.le.trans hj) hg (hm hcut) hH d.1 hd
    rw [he, max_eq_right le_top] at hlow
    rw [hd]
    exact top_le_iff.mp hlow
  · exact hnon d hd

/-- The readback in section form, with the low receipt as the owner and the low source reading
top. -/
theorem LowRef.readback_eq {j : ℕ} (hj : N ≤ j) (hcut : ⊥ < R.cut R.vactL) {S : R.TState j}
    (hS : L.TAdmissible S) (hg : S.st.gate ≠ ⊥) (hcap : S.st.v (R.capC hj) = R.vact R.cap)
    (href : ∀ i, S.st.v (CellScheme.below.mono (R.capLe hj) (R.lowRef i)) = R.vact (R.ref i))
    (hc : S.st.v (L.cC (L.K_lt_N.le.trans hj)) = ⊤)
    (hr : S.st.v (L.rC (L.K_lt_N.le.trans hj)) = ⊤) :
    S.b = R.cut R.vactL ∧ S.st.u = fun d => R.p d.1 := by
  obtain ⟨hb, hu⟩ := L.readback hj hcut hS hg hcap href (L.eC_top _ hc hr)
  exact ⟨hb, funext hu⟩

/-- **The probe contract**: a rendered admissible two-threshold state at a cutoff with the cap
present, whose private section is the **actual private labelling** (the probe retains the actual
private face literally), with a positive gate, a positive actual cut, and a low reference whose
owner and low source are actual tops, reads the donor labelling back literally.  Every chart
receipt of `readback_eq` is discharged by the retained actual face. -/
theorem LowRef.readback_of_actualFace {j : ℕ} (hj : N ≤ j) (hcut : ⊥ < R.cut R.vactL)
    {S : R.TState j} (hS : L.TAdmissible S) (hg : S.st.gate ≠ ⊥)
    (hv : ∀ d, S.st.v d = R.vact d.1) (hc : R.vact L.c = ⊤) (hr : R.vact L.r.1 = ⊤) :
    S.b = R.cut R.vactL ∧ S.st.u = fun d => R.p d.1 :=
  L.readback_eq hj hcut hS hg (hv _) (fun _ => hv _) ((hv _).trans hc) ((hv _).trans hr)

end Ref

end CappedDonor

end VaughtConjecture.Knight
