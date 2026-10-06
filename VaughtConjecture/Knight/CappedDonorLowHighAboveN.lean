/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowHighBelowN

/-! # The two-threshold fibres at and above the high grade (audit16 §4, note §5)

Both same-grade fibres of the two-threshold family at cutoffs `j ≥ N`, where every request field,
the references, the cap `H` and the stored cutoff are current and HIGH dictates the allowable
repair of the stored cutoff.  Still-future private fields enter only the support clauses and are
retained literally.

* **Gate off, or cap bottom**: the receiving fibre with the stored cutoff unchanged; with `H = ⊥`
  positive-cap agreement keeps it bottom, `B = ⊥`, HIGH is automatic and LOW cannot activate
  (`tadmissible_of_cap_bot`).
* **Private context prescribed** (`exists_private_lift_aboveN`): with `B₁ = cut v₁`, `H₁ = v₁ H`,
  the repaired cutoff is `highCutoff b B₁ H₁ γ` — `B₁` when `B₁ < H₁`, `max H₁ (b ∧ γ)` when
  `B₁ = H₁` — so that `b₁ ∧ H₁ = B₁` (`highCutoff_min_H`) and `b₁ ∧ γ = b ∧ γ`
  (`highCutoff_min_cap`, from the old HIGH equation and cap agreement).  **Separation**
  (`Sep`: `B₁ < H₁` and the empty-max-safe `selMax v₁ < B₁`) is, under HIGH, LOW's antecedent
  (`sep_of_low`).  If it fails, the receiving fibre suffices and LOW cannot activate.  If it
  holds, the **high barrier** (`old_active_of_sep`, audit16 (7)): `B₁ < γ` forces the old LOW
  antecedent — the caps pin the old cutoff to `B₁`, every old non-top request value to the
  selector value below `B₁`, and the old cap above `B₁`.  With `η₁ = max B₁ (e v₁)`: if
  `η₁ ≤ γ` the receiving fibre's request section already satisfies LOW (floor cap, or, when the
  old condition was inactive, `B₁ = η₁ = γ` and HIGH supplies the floor); if `γ < η₁` the tops
  of the lawful selector section `sel v₁` are retargeted to `η₁` with the exact old face restored
  through `min K (arity P)` and the higher selector values attached unchanged — old top caps
  survive because either the old floor reaches `γ` or `γ ≤ B₁` and old HIGH puts every old top
  above `γ`.
* **Request prescribed** (`exists_request_lift_aboveN`): install the face in old `C` at `γ`, clip
  every current private grade at least `N` at `γ`, and put `b₁ = b ∧ γ`; HIGH holds by selector
  naturality (`high_clip`).  If LOW activates then `b₁ < γ`, the old cutoff is `b₁`, every non-top
  request value is pinned below it and the old condition was active; if the frontier exceeds `γ`,
  SHIELD holds and the exact frontier release, followed by reclipping (which changes neither the
  owner nor the low source, `eC_clip`), makes the frontier exactly `γ`. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd SharpWitnessComposition AmalgamationPlan

namespace CappedDonor

/-! ## The high cutoff repair -/

/-- The repaired cutoff at and above `N` (audit16 (5)). -/
noncomputable def highCutoff (b B₁ H₁ γ : ExtOrd) : ExtOrd :=
  if B₁ < H₁ then B₁ else max H₁ (min b γ)

theorem highCutoff_of_lt {b B₁ H₁ γ : ExtOrd} (h : B₁ < H₁) : highCutoff b B₁ H₁ γ = B₁ := by
  unfold highCutoff; rw [ite_eq_left h]

theorem highCutoff_of_not_lt {b B₁ H₁ γ : ExtOrd} (h : ¬ B₁ < H₁) :
    highCutoff b B₁ H₁ γ = max H₁ (min b γ) := by
  unfold highCutoff; rw [ite_eq_right h]

/-- `b₁ ∧ H₁ = B₁`. -/
theorem highCutoff_min_H {b B₁ H₁ γ : ExtOrd} (hle : B₁ ≤ H₁) :
    min (highCutoff b B₁ H₁ γ) H₁ = B₁ := by
  by_cases h : B₁ < H₁
  · rw [highCutoff_of_lt h, min_eq_left hle]
  · rw [highCutoff_of_not_lt h, min_eq_right (le_max_left _ _), le_antisymm hle (not_lt.mp h)]

theorem highCutoff_selfVis {K : ℕ} {b B₁ H₁ γ : ExtOrd} (hb : SelfVis K b) (hB : SelfVis K B₁)
    (hH : SelfVis K H₁) (hγ : SelfVis K γ) : SelfVis K (highCutoff b B₁ H₁ γ) := by
  unfold highCutoff; split_ifs
  · exact hB
  · exact TopSupport.selfVis_max_of hH (selfVis_min hb hγ)

/-- The repaired cutoff is below `H₁` only in the separated branch, where it is `B₁`. -/
theorem highCutoff_lt {b B₁ H₁ γ : ExtOrd} (h : highCutoff b B₁ H₁ γ < H₁) :
    B₁ < H₁ ∧ highCutoff b B₁ H₁ γ = B₁ := by
  by_cases hlt : B₁ < H₁
  · exact ⟨hlt, highCutoff_of_lt hlt⟩
  · rw [highCutoff_of_not_lt hlt] at h
    exact absurd h (not_lt.mpr (le_max_left _ _))

/-- **The cap receipt of the repaired cutoff** (pure order form): from the old HIGH equation
`b ∧ H = B₀` and the cap agreements of `B₁` with `B₀` and of `H₁` with `H`. -/
theorem highCutoff_min_cap {b B₀ B₁ H H₁ γ : ExtOrd} (hhigh : min b H = B₀) (hle : B₁ ≤ H₁)
    (hB : min B₁ γ = min B₀ γ) (hH : min H₁ γ = min H γ) :
    min (highCutoff b B₁ H₁ γ) γ = min b γ := by
  have hBγ : min B₁ γ = min (min b γ) (min H₁ γ) := by
    rw [hB, ← hhigh, hH, min_min_min_comm, min_self]
  by_cases hlt : B₁ < H₁
  · rw [highCutoff_of_lt hlt, hBγ]
    apply min_eq_left
    refine le_min ?_ (min_le_right _ _)
    by_contra hgt
    have hgt' : H₁ < min b γ := not_le.mp hgt
    have hH₁γ : H₁ < γ := hgt'.trans_le (min_le_right _ _)
    have hHeq : H = H₁ := eq_of_capAgree_of_lt hH hH₁γ
    have hB₀ : B₀ = H₁ := by
      rw [← hhigh, hHeq, min_eq_right (hgt'.trans_le (min_le_left _ _)).le]
    have hB₁ : B₁ = H₁ := by
      have h1 : min B₁ γ = min H₁ γ := by rw [hB, hB₀]
      exact (eq_of_capAgree_of_lt (x := H₁) (y := B₁) (γ := γ) h1.symm hH₁γ)
    exact absurd hlt (hB₁ ▸ lt_irrefl _)
  · rw [highCutoff_of_not_lt hlt, min_max_distrib_right, min_assoc, min_self]
    apply max_eq_right
    have hBH : B₁ = H₁ := le_antisymm hle (not_lt.mp hlt)
    rw [← hBH, hBγ]
    exact min_le_left _ _

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-! ## The selector maximum over the non-top donor cells -/

open Classical in
/-- The maximum of the selector over the donor cells with a non-top label (empty maximum
bottom). -/
noncomputable def selMax (v : R.Low → ExtOrd) : ExtOrd :=
  (Finset.univ.filter fun d : Cell P.scheme => R.p d ≠ ⊤).sup fun d => R.sel v d

theorem sel_le_selMax (v : R.Low → ExtOrd) {d : Cell P.scheme} (hd : R.p d ≠ ⊤) :
    R.sel v d ≤ selMax (R := R) v := by
  classical
  exact Finset.le_sup (f := fun d => R.sel v d) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)

theorem selMax_lt_iff (v : R.Low → ExtOrd) {b : ExtOrd} (hb : ⊥ < b) :
    selMax (R := R) v < b ↔ ∀ d, R.p d ≠ ⊤ → R.sel v d < b := by
  classical
  unfold selMax
  rw [Finset.sup_lt_iff hb]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

variable {K : ℕ} (L : R.LowRef K)

/-! ## Vacuous cases at and above `N` -/

/-- With a bottom cap value neither condition is imposed beyond the receiving relation. -/
theorem LowRef.tadmissible_of_cap_bot {j : ℕ} (hj : N ≤ j) {st : R.State j} (hst : R.Admissible st)
    (hc : st.v (R.capC hj) = ⊥) {b : ExtOrd} (hb : SelfVis 1 b) (hbK : K ≤ j → SelfVis K b) :
    L.TAdmissible ⟨st, b⟩ where
  adm := hst
  b_vis := hb
  b_visK := hbK
  low _ _ _ hlt := by
    rw [st.capField_of_present hj, hc] at hlt
    exact absurd hlt not_lt_bot
  high _ _ := by
    have h1 : st.v (R.capC hj) = ⊥ := hc
    rw [h1, min_bot_right]
    symm
    apply le_bot_iff.mp
    exact (R.cut_le_cap _).trans (by rw [R.lowC_cap]; exact h1.le)

/-! ## The high barrier -/

/-- **Separation** (audit16 (6)): `B₁ < H₁` and the selector maximum over the non-top donor cells
is strictly below `B₁`. -/
def Sep {j : ℕ} (hj : N ≤ j) (v₁ : C.scheme.below (effC J j) → ExtOrd) : Prop :=
  R.cut (R.lowC hj v₁) < v₁ (R.capC hj) ∧ selMax (R := R) (R.lowC hj v₁) < R.cut (R.lowC hj v₁)

/-- Under HIGH, LOW's antecedent for a state with private section `v₁` gives separation. -/
theorem sep_of_low {j : ℕ} (hj : N ≤ j) {st : R.State j} {b₁ : ExtOrd}
    (hrel : ∀ d : P.scheme.below (effP nP j),
      min (st.u d) (R.cut (R.lowC hj st.v)) = R.sel (R.lowC hj st.v) d.1)
    (hm : st.nonTopMax < b₁) (hH : b₁ < st.capField)
    (hb₁ : b₁ < st.v (R.capC hj) → b₁ = R.cut (R.lowC hj st.v)) : Sep (R := R) hj st.v := by
  rw [st.capField_of_present hj] at hH
  have hb := hb₁ hH
  rw [hb] at hH hm
  refine ⟨hH, ?_⟩
  rw [selMax_lt_iff _ (bot_le.trans_lt hm)]
  intro d hd
  have h : min (st.u (reqCell d ((R.gradeP_lt_N d).le.trans hj))) (R.cut (R.lowC hj st.v)) =
      R.sel (R.lowC hj st.v) d := hrel (reqCell d ((R.gradeP_lt_N d).le.trans hj))
  rw [← h]
  exact (min_le_left _ _).trans_lt ((st.u_le_nonTopMax _ hd).trans_lt hm)

/-- **The high barrier** (audit16 (7)): with a positive gate and cap, separation of a cap-equivalent
private section and `B₁ < γ` force the old LOW antecedent, with the old cutoff `B₁`. -/
theorem LowRef.old_active_of_sep {j : ℕ} (hj : N ≤ j) {S : R.TState j} (hS : L.TAdmissible S)
    (hg : S.st.gate ≠ ⊥) (hc : S.st.v (R.capC hj) ≠ ⊥) {γ : ExtOrd} (hγN : SelfVis N γ)
    {v₁ : C.scheme.below (effC J j) → ExtOrd} (hagree : ∀ d, min (v₁ d) γ = min (S.st.v d) γ)
    (hsep : Sep (R := R) hj v₁) (hBγ : R.cut (R.lowC hj v₁) < γ) :
    S.b = R.cut (R.lowC hj v₁) ∧ S.st.nonTopMax < S.b ∧ S.b < S.st.capField := by
  have hVγ : (fun d => min (R.lowC hj v₁ d) γ) = fun d => min (R.lowC hj S.st.v d) γ :=
    funext fun d => hagree _
  have hcutγ : min (R.cut (R.lowC hj v₁)) γ = min (R.cut (R.lowC hj S.st.v)) γ := by
    rw [← R.cut_min hγN, ← R.cut_min hγN, hVγ]
  have hselγ : ∀ e, min (R.sel (R.lowC hj v₁) e) γ = min (R.sel (R.lowC hj S.st.v) e) γ := by
    intro e
    rw [← R.sel_min hγN, ← R.sel_min hγN, hVγ]
  have hHγ : min (v₁ (R.capC hj)) γ = min (S.st.v (R.capC hj)) γ := hagree _
  have hhigh := hS.high hj hg
  have hrel := hS.adm.relation hj hg hc
  -- the old cut is `B₁`
  have hB₀ : R.cut (R.lowC hj S.st.v) = R.cut (R.lowC hj v₁) := eq_of_capAgree_of_lt hcutγ hBγ
  -- the old cap is above `B₁`
  have hHB : R.cut (R.lowC hj v₁) < S.st.v (R.capC hj) := by
    by_contra hle
    have hHγ' : S.st.v (R.capC hj) < γ := (not_lt.mp hle).trans_lt hBγ
    have hHeq : v₁ (R.capC hj) = S.st.v (R.capC hj) := eq_of_capAgree_of_lt hHγ.symm hHγ'
    exact absurd (hsep.1.trans_le (hHeq ▸ not_lt.mp hle)) (lt_irrefl _)
  -- the old cutoff is `B₁`
  have hb : S.b = R.cut (R.lowC hj v₁) := by
    have h1 : min (R.cut (R.lowC hj v₁)) (S.st.v (R.capC hj)) = min S.b (S.st.v (R.capC hj)) := by
      rw [min_eq_left hHB.le, hhigh, hB₀]
    exact eq_of_capAgree_of_lt h1 hHB
  refine ⟨hb, ?_, by rw [S.st.capField_of_present hj, hb]; exact hHB⟩
  rw [hb, S.st.nonTopMax_lt_iff (bot_le.trans_lt hsep.2)]
  intro d hd
  rw [S.st.sourceProfile_req_of_present d ((R.gradeP_lt_N d).le.trans hj)]
  have hF₁ : R.sel (R.lowC hj v₁) d < R.cut (R.lowC hj v₁) :=
    (sel_le_selMax _ hd).trans_lt hsep.2
  have hF₀ : R.sel (R.lowC hj S.st.v) d = R.sel (R.lowC hj v₁) d :=
    eq_of_capAgree_of_lt (hselγ d) (hF₁.trans hBγ)
  have h : min (S.st.u (reqCell d ((R.gradeP_lt_N d).le.trans hj))) (R.cut (R.lowC hj S.st.v)) =
      R.sel (R.lowC hj S.st.v) d := hrel (reqCell d ((R.gradeP_lt_N d).le.trans hj))
  rw [hB₀, hF₀] at h
  have hu : S.st.u (reqCell d ((R.gradeP_lt_N d).le.trans hj)) = R.sel (R.lowC hj v₁) d :=
    eq_of_capAgree_of_lt (x := R.sel (R.lowC hj v₁) d) (by rw [min_eq_left hF₁.le]; exact h.symm)
      hF₁
  rw [hu]; exact hF₁

/-! ## HIGH after clipping -/

/-- **HIGH after clipping** (audit16 §4, request prescribed): with the stored cutoff `b ∧ γ` and a
private section agreeing with the old one below `γ`, clipping the coordinates of grade at least
`N` at `γ` satisfies HIGH. -/
theorem LowRef.high_clip {j : ℕ} (hj : N ≤ j) {S : R.TState j} (hS : L.TAdmissible S)
    (hg : S.st.gate ≠ ⊥) {γ : ExtOrd} (hγN : SelfVis N γ)
    {v₀ : C.scheme.below (effC J j) → ExtOrd} (hcap₀ : ∀ d, min (v₀ d) γ = min (S.st.v d) γ) :
    min (min S.b γ) (clip (N := N) γ v₀ (R.capC hj)) = R.cut (R.lowC hj (clip (N := N) γ v₀)) := by
  have hcap' : R.lowC hj (clip (N := N) γ v₀) R.capL = min (R.lowC hj v₀ R.capL) γ :=
    R.clip_cap hj γ v₀
  have href' := R.clip_ref hj γ v₀
  rw [R.cut_clip hcap' href']
  have hV₀γ : (fun e => min (R.lowC hj v₀ e) γ) = fun e => min (R.lowC hj S.st.v e) γ :=
    funext fun e => hcap₀ _
  have hcutγ : min (R.cut (R.lowC hj v₀)) γ = min (R.cut (R.lowC hj S.st.v)) γ := by
    rw [← R.cut_min hγN, ← R.cut_min hγN, hV₀γ]
  have hc : clip (N := N) γ v₀ (R.capC hj) = min (v₀ (R.capC hj)) γ := hcap'
  rw [hcutγ, ← hS.high hj hg, hc, hcap₀ (R.capC hj), min_min_min_comm, min_self]

/-- Clipping at `γ` leaves the frontier unchanged (the owner and the low source have grade below
`N`). -/
theorem LowRef.eC_clip {j : ℕ} (hjK : K ≤ j) (γ : ExtOrd) (v : C.scheme.below (effC J j) → ExtOrd) :
    L.eC hjK (clip (N := N) γ v) = L.eC hjK v :=
  L.e_congr (clip_of_lt γ v (d := L.cC hjK) (by
      change C.scheme.grade L.c < N; rw [L.c_grade]; exact L.K_lt_N))
    (clip_of_lt γ v (d := L.rC hjK) ((L.grade_dom L.r).trans_lt L.K_lt_N))

/-! ## The private fibre at and above `N` -/

/-- **The private fibre at and above `N`** (audit16 §4, note §5.1): every still-future field, the
gate and every shadow retained literally; the stored cutoff repaired to `highCutoff`; the request
tops raised by exact old-face restoration from the lawful selector section when the new floor
exceeds the cap. -/
theorem LowRef.exists_private_lift_aboveN {j : ℕ} (hj : N ≤ j) {S : R.TState j}
    (hS : L.TAdmissible S) {v₁ : C.scheme.below (effC J j) → ExtOrd}
    (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁) {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ)
    (hbot : γ ≠ ⊥) (hagree : ∀ d, min (v₁ d) γ = min (S.st.v d) γ) :
    ∃ S₁ : R.TState j, L.TAdmissible S₁ ∧ S₁.st.v = v₁ ∧
      (∀ d, min (S₁.st.u d) γ = min (S.st.u d) γ) ∧ min S₁.b γ = min S.b γ ∧
      S₁.st.gate = S.st.gate ∧ S₁.st.shadowP = S.st.shadowP ∧ S₁.st.shadowC = S.st.shadowC := by
  have hjK : K ≤ j := L.K_lt_N.le.trans hj
  have hγN : SelfVis N γ := R.selfVis_N_of_effC hj hγ
  have hγK : SelfVis K γ := hγN.mono L.K_lt_N.le
  have hpat := bottom_pattern_of_cap_agreement hbot hagree
  obtain ⟨st₁, hst₁, hv, hu, -, hlit⟩ := R.exists_private_lift hS.adm hv₁ hγ hagree
  obtain ⟨hg₁, hP, hC⟩ := hlit hbot
  by_cases hg : S.st.gate = ⊥
  · exact ⟨⟨st₁, S.b⟩, L.tadmissible_of_gate_bot hst₁ (hg₁.trans hg) hS.b_vis hS.b_visK, hv, hu,
      rfl, hg₁, hP, hC⟩
  by_cases hc : S.st.v (R.capC hj) = ⊥
  · have hc₁ : st₁.v (R.capC hj) = ⊥ := by rw [hv]; exact (hpat _).mpr hc
    exact ⟨⟨st₁, S.b⟩, L.tadmissible_of_cap_bot hj hst₁ hc₁ hS.b_vis hS.b_visK, hv, hu, rfl, hg₁,
      hP, hC⟩
  -- the active case
  have hhigh := hS.high hj hg
  have hrel₀ := hS.adm.relation hj hg hc
  have hA₀ := Admissible.active R hS.adm hj hg hc
  have hA₁ : R.Active (R.lowC hj v₁) :=
    ⟨R.lowC_respects hj hv₁, fun h => hc ((hpat _).mp h),
      fun i h => hA₀.ref_pos i ((hpat _).mp h), fun a ha => (hpat _).mpr (hA₀.face_bot a ha)⟩
  have hVγ : (fun d => min (R.lowC hj v₁ d) γ) = fun d => min (R.lowC hj S.st.v d) γ :=
    funext fun d => hagree _
  have hcutγ : min (R.cut (R.lowC hj v₁)) γ = min (R.cut (R.lowC hj S.st.v)) γ := by
    rw [← R.cut_min hγN, ← R.cut_min hγN, hVγ]
  have hselγ : ∀ e, min (R.sel (R.lowC hj v₁) e) γ = min (R.sel (R.lowC hj S.st.v) e) γ := by
    intro e
    rw [← R.sel_min hγN, ← R.sel_min hγN, hVγ]
  have hHγ : min (v₁ (R.capC hj)) γ = min (S.st.v (R.capC hj)) γ := hagree _
  have hB₁H₁ : R.cut (R.lowC hj v₁) ≤ v₁ (R.capC hj) := R.cut_le_cap _
  have hB₁vis : SelfVis K (R.cut (R.lowC hj v₁)) :=
    (R.selfVis_cut (Active.selfVis_cap R hA₁)).mono L.K_lt_N.le
  have hH₁vis : SelfVis K (v₁ (R.capC hj)) := (Active.selfVis_cap R hA₁).mono L.K_lt_N.le
  set b₁ := highCutoff S.b (R.cut (R.lowC hj v₁)) (v₁ (R.capC hj)) γ with hb₁def
  have hb₁vis : SelfVis K b₁ := highCutoff_selfVis (hS.b_visK hjK) hB₁vis hH₁vis hγK
  have hb₁min : min b₁ γ = min S.b γ := highCutoff_min_cap hhigh hB₁H₁ hcutγ hHγ
  have hb₁H : min b₁ (v₁ (R.capC hj)) = R.cut (R.lowC hj v₁) := highCutoff_min_H hB₁H₁
  have hhigh₁ : ∀ (st : R.State j), st.v = v₁ → ∀ (hj₀ : N ≤ j), st.gate ≠ ⊥ →
      min b₁ (st.v (R.capC hj₀)) = R.cut (R.lowC hj₀ st.v) := by
    intro st hst _ _
    rw [hst]; exact hb₁H
  have hcap₁ : st₁.v (R.capC hj) ≠ ⊥ := by rw [hv]; exact hA₁.cap_pos
  by_cases hsep : Sep (R := R) hj v₁
  · obtain ⟨hlt, hsmax⟩ := hsep
    have hb₁B : b₁ = R.cut (R.lowC hj v₁) := highCutoff_of_lt hlt
    have hfloor : min (max (R.cut (R.lowC hj v₁)) (L.eC hjK v₁)) γ =
        min (max S.b (L.eC hjK S.st.v)) γ :=
      floor_min (by rw [← hb₁min, hb₁B]) (L.eC_agree hjK hγK hagree)
    have hB₁pos : ⊥ < R.cut (R.lowC hj v₁) := bot_le.trans_lt hsmax
    have hold : R.cut (R.lowC hj v₁) < γ → S.st.nonTopMax < S.b ∧ S.b < S.st.capField :=
      fun h => (L.old_active_of_sep hj hS hg hc hγN hagree ⟨hlt, hsmax⟩ h).2
    -- when the floor exceeds the cap, every old top reaches the cap
    have htopγ : γ < max (R.cut (R.lowC hj v₁)) (L.eC hjK v₁) →
        ∀ d : P.scheme.below (effP nP j), R.p d.1 = ⊤ → γ ≤ S.st.u d := by
      intro hη d hd
      by_cases hBγ : R.cut (R.lowC hj v₁) < γ
      · obtain ⟨hm₀, hbH₀⟩ := hold hBγ
        have hlow₀ := hS.low hjK hg hm₀ hbH₀ d.1 hd
        have hγfloor : γ ≤ max S.b (L.eC hjK S.st.v) := by
          rw [min_eq_right hη.le] at hfloor
          exact min_eq_right_iff.mp hfloor.symm
        exact hγfloor.trans hlow₀
      · have h := hrel₀ d
        rw [R.sel_of_top hd] at h
        have hB₀ : R.cut (R.lowC hj S.st.v) ≤ S.st.u d := min_eq_right_iff.mp h
        have hγB₀ : γ ≤ R.cut (R.lowC hj S.st.v) := by
          have h2 : min (R.cut (R.lowC hj S.st.v)) γ = γ := by
            rw [← hcutγ, min_eq_right (not_lt.mp hBγ)]
          exact min_eq_right_iff.mp h2
        exact hγB₀.trans hB₀
    by_cases hη : γ < max (R.cut (R.lowC hj v₁)) (L.eC hjK v₁)
    · -- the floor exceeds the cap: retarget the tops of the selector section
      have hF₁ : RespectsSemanticsBelow P.rows (effP nP j)
          (fun d : P.scheme.below (effP nP j) => R.sel (R.lowC hj v₁) d.1) :=
        (Active.sel_respects R hA₁).toBelow _
      have hRD : RetargetData (R := R) (K := K)
          (fun d : P.scheme.below (effP nP j) => R.sel (R.lowC hj v₁) d.1)
          (R.cut (R.lowC hj v₁)) (max (R.cut (R.lowC hj v₁)) (L.eC hjK v₁)) :=
        ⟨hF₁, hB₁vis, hB₁pos, fun d hd => (sel_le_selMax _ hd).trans_lt hsmax,
          fun d hd => (R.sel_of_top hd).symm.le,
          TopSupport.selfVis_max_of hB₁vis (L.eC_selfVis hjK hv₁), le_max_left _ _⟩
      have hface₁ : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
          R.sel (R.lowC hj v₁) a.1 = min (v₁ (R.privFace a h)) (R.cut (R.lowC hj v₁)) :=
        fun a _ => Active.sel_face R hA₁ a
      obtain ⟨u', hu', hnon', htop', hface'⟩ := exists_retarget_restore L hjK hRD hv₁
        (fun a h ha => by
          have hlt' : R.sel (R.lowC hj v₁) a.1 < R.cut (R.lowC hj v₁) :=
            (sel_le_selMax _ ha).trans_lt hsmax
          have h1 : min (R.sel (R.lowC hj v₁) a.1) (R.cut (R.lowC hj v₁)) =
              min (v₁ (R.privFace a h)) (R.cut (R.lowC hj v₁)) := by
            rw [min_eq_left (R.sel_le_cut _ _), hface₁ a h]
          exact eq_of_capAgree_of_lt h1 hlt')
        (fun a h ha => by
          have h1 := hface₁ a h
          rw [R.sel_of_top ha] at h1
          exact max_le (min_eq_right_iff.mp h1.symm) (L.eC_le_top hjK hv₁ a ha))
      have hcap₂ : ∀ d, min (u' d) γ = min (S.st.u d) γ := by
        intro d
        by_cases hd : R.p d.1 = ⊤
        · rw [min_eq_right ((htop' d hd).trans' hη.le), min_eq_right (htopγ hη d hd)]
        · rw [hnon' d hd]
          by_cases hF : R.sel (R.lowC hj v₁) d.1 < γ
          · have hF₀ : R.sel (R.lowC hj S.st.v) d.1 = R.sel (R.lowC hj v₁) d.1 :=
              eq_of_capAgree_of_lt (hselγ d.1) hF
            have h := hrel₀ d
            rw [hF₀] at h
            by_cases hB₀γ : γ ≤ R.cut (R.lowC hj S.st.v)
            · rw [← h, min_assoc, min_eq_right hB₀γ]
            · have hB₀γ' : R.cut (R.lowC hj S.st.v) < γ := not_le.mp hB₀γ
              have hB₁B₀ : R.cut (R.lowC hj v₁) = R.cut (R.lowC hj S.st.v) :=
                eq_of_capAgree_of_lt hcutγ.symm hB₀γ'
              have hlt' : R.sel (R.lowC hj v₁) d.1 < R.cut (R.lowC hj S.st.v) :=
                hB₁B₀ ▸ ((sel_le_selMax _ hd).trans_lt hsmax)
              have hu : S.st.u d = R.sel (R.lowC hj v₁) d.1 :=
                eq_of_capAgree_of_lt (x := R.sel (R.lowC hj v₁) d.1)
                  (by rw [min_eq_left hlt'.le]; exact h.symm) hlt'
              rw [hu]
          · have hγF : γ ≤ R.sel (R.lowC hj v₁) d.1 := not_lt.mp hF
            have h2 : min (R.sel (R.lowC hj S.st.v) d.1) γ = γ := by
              rw [← hselγ d.1, min_eq_right hγF]
            have hγF₀ : γ ≤ R.sel (R.lowC hj S.st.v) d.1 := min_eq_right_iff.mp h2
            have h := hrel₀ d
            have hγu : γ ≤ S.st.u d := hγF₀.trans (h ▸ min_le_left _ _)
            rw [min_eq_right hγF, min_eq_right hγu]
      have hrel₂ : ∀ (hj₀ : N ≤ j), S.st.gate ≠ ⊥ → v₁ (R.capC hj₀) ≠ ⊥ →
          ∀ d : P.scheme.below (effP nP j),
            min (u' d) (R.cut (R.lowC hj₀ v₁)) = R.sel (R.lowC hj₀ v₁) d.1 := by
        intro _ _ _ d
        by_cases hd : R.p d.1 = ⊤
        · rw [R.sel_of_top hd]; exact min_eq_right ((le_max_left _ _).trans (htop' d hd))
        · rw [hnon' d hd]; exact min_eq_left (R.sel_le_cut _ _)
      have hadm₂ : R.Admissible ⟨u', v₁, S.st.gate, S.st.shadowP, S.st.shadowC⟩ :=
        R.admissible_persist hS.adm hbot hu' hv₁ hcap₂ hagree hface' hrel₂
      refine ⟨⟨⟨u', v₁, S.st.gate, S.st.shadowP, S.st.shadowC⟩, b₁⟩,
        ⟨hadm₂, hb₁vis.mono L.K_pos, fun _ => hb₁vis, ?_, hhigh₁ _ rfl⟩, rfl, hcap₂, hb₁min, rfl,
        rfl, rfl⟩
      intro _ _ _ _ t ht
      change max b₁ (L.eC _ v₁) ≤ u' (reqCell t _)
      rw [hb₁B]; exact htop' _ ht
    · -- the floor is at most the cap: the receiving lift with the repaired cutoff
      refine ⟨⟨st₁, b₁⟩, ⟨hst₁, hb₁vis.mono L.K_pos, fun _ => hb₁vis, ?_, hhigh₁ st₁ hv⟩, hv, hu,
        hb₁min, hg₁, hP, hC⟩
      intro hjK' hg₂ _ _ t ht
      have hrel₁ := hst₁.relation hj hg₂ hcap₁
      change max b₁ (L.eC hjK' st₁.v) ≤ st₁.u (reqCell t _)
      rw [hv, hb₁B]
      have hηγ : max (R.cut (R.lowC hj v₁)) (L.eC hjK v₁) ≤ γ := not_lt.mp hη
      by_cases hBγ : R.cut (R.lowC hj v₁) < γ
      · obtain ⟨hm₀, hbH₀⟩ := hold hBγ
        have hlow₀ := hS.low hjK hg hm₀ hbH₀ t ht
        calc max (R.cut (R.lowC hj v₁)) (L.eC hjK' v₁)
            = min (max (R.cut (R.lowC hj v₁)) (L.eC hjK v₁)) γ := (min_eq_left hηγ).symm
          _ = min (max S.b (L.eC hjK S.st.v)) γ := hfloor
          _ ≤ min (S.st.u (reqCell t ((L.top_grade t ht).trans hjK))) γ :=
              min_le_min_right _ hlow₀
          _ = min (st₁.u (reqCell t ((L.top_grade t ht).trans hjK))) γ := (hu _).symm
          _ ≤ st₁.u (reqCell t _) := min_le_left _ _
      · have hηB : max (R.cut (R.lowC hj v₁)) (L.eC hjK' v₁) = R.cut (R.lowC hj v₁) :=
          le_antisymm (hηγ.trans (not_lt.mp hBγ)) (le_max_left _ _)
        rw [hηB]
        have h : min (st₁.u (reqCell t ((L.top_grade t ht).trans hjK))) (R.cut (R.lowC hj st₁.v)) =
            R.sel (R.lowC hj st₁.v) t := hrel₁ (reqCell t ((L.top_grade t ht).trans hjK))
        rw [hv, R.sel_of_top ht] at h
        exact min_eq_right_iff.mp h
  · -- no separation: the receiving lift with the repaired cutoff; LOW cannot activate
    refine ⟨⟨st₁, b₁⟩, ⟨hst₁, hb₁vis.mono L.K_pos, fun _ => hb₁vis, ?_, hhigh₁ st₁ hv⟩, hv, hu,
      hb₁min, hg₁, hP, hC⟩
    intro _ hg₂ hm hH t ht
    exfalso
    have hrel₁ := hst₁.relation hj hg₂ hcap₁
    apply hsep
    have hsep' := sep_of_low (R := R) hj (st := st₁) (b₁ := b₁) hrel₁ hm hH (fun hlt => by
      rw [hv] at hlt ⊢; exact (highCutoff_lt hlt).2)
    rw [hv] at hsep'; exact hsep'

/-! ## The request fibre at and above `N` -/

/-- **The request fibre at and above `N`** (audit16 §4, note §5.2): the face installed in old `C`
at `γ`, every current private grade at least `N` clipped at `γ`, the stored cutoff `b ∧ γ`; HIGH
by selector naturality; the frontier released exactly to the cap, then reclipped, when it exceeds
the cap under an active LOW condition. -/
theorem LowRef.exists_request_lift_aboveN {j : ℕ} (hj : N ≤ j) {S : R.TState j}
    (hS : L.TAdmissible S) {u₁ : P.scheme.below (effP nP j) → ExtOrd}
    (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁) {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ)
    (hbot : γ ≠ ⊥) (hagree : ∀ d, min (u₁ d) γ = min (S.st.u d) γ) :
    ∃ S₁ : R.TState j, L.TAdmissible S₁ ∧ S₁.st.u = u₁ ∧
      (∀ d, min (S₁.st.v d) γ = min (S.st.v d) γ) ∧ min S₁.b γ = min S.b γ ∧
      S₁.st.gate = S.st.gate ∧ S₁.st.shadowP = S.st.shadowP ∧ S₁.st.shadowC = S.st.shadowC := by
  have hjK : K ≤ j := L.K_lt_N.le.trans hj
  have hγN : SelfVis N γ := R.selfVis_N_of_effC hj hγ
  have hγK : SelfVis K γ := hγN.mono L.K_lt_N.le
  have hcompat : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      min (S.st.v (R.privFace a h)) γ = min (u₁ (R.reqFace a h)) γ := by
    intro a h
    rw [← hS.adm.face a h]
    exact (hagree _).symm
  obtain ⟨v₀, hv₀, hcap₀, hface₀⟩ := R.exists_installC hS.adm.v_respects hu₁ hγ hcompat
  obtain ⟨hadm₁, hclip⟩ := R.admissible_clip hS.adm hu₁ hγ hagree hbot hv₀ hcap₀ hface₀
  by_cases hg : S.st.gate = ⊥
  · exact ⟨⟨⟨u₁, clip (N := N) γ v₀, S.st.gate, S.st.shadowP, S.st.shadowC⟩, S.b⟩,
      L.tadmissible_of_gate_bot hadm₁ hg hS.b_vis hS.b_visK, rfl, hclip, rfl, rfl, rfl, rfl⟩
  by_cases hc : S.st.v (R.capC hj) = ⊥
  · have hc₁ : clip (N := N) γ v₀ (R.capC hj) = ⊥ := by
      have h := hclip (R.capC hj)
      rw [hc, min_bot_left] at h
      exact (min_eq_bot.mp h).resolve_right hbot
    exact ⟨⟨⟨u₁, clip (N := N) γ v₀, S.st.gate, S.st.shadowP, S.st.shadowC⟩, S.b⟩,
      L.tadmissible_of_cap_bot hj hadm₁ hc₁ hS.b_vis hS.b_visK, rfl, hclip, rfl, rfl, rfl, rfl⟩
  -- the active case
  have hb₁vis : SelfVis K (min S.b γ) := selfVis_min (hS.b_visK hjK) hγK
  have hb₁min : min (min S.b γ) γ = min S.b γ := by rw [min_assoc, min_self]
  -- the activation analysis for any clipped state
  have hlowcore : ∀ (v : C.scheme.below (effC J j) → ExtOrd),
      (∀ d, min (v d) γ = min (S.st.v d) γ) → ∀ st : R.State j, st.u = u₁ →
      st.v = clip (N := N) γ v → st.shadowP = S.st.shadowP →
      st.nonTopMax < min S.b γ → min S.b γ < st.capField →
      S.b < γ ∧ S.st.nonTopMax < S.b ∧ S.b < S.st.capField := by
    intro v hcapv st hstu hstv hstP hm hH
    rw [st.capField_of_present hj, hstv] at hH
    have h1 : clip (N := N) γ v (R.capC hj) = min (v (R.capC hj)) γ := R.clip_cap hj γ v
    rw [h1] at hH
    have hbγ : S.b < γ := by
      by_contra hle
      rw [min_eq_right (not_lt.mp hle)] at hH
      exact absurd (hH.trans_le (min_le_right _ _)) (lt_irrefl _)
    have hb₁ : min S.b γ = S.b := min_eq_left hbγ.le
    rw [hb₁] at hm hH
    refine ⟨hbγ, ?_, ?_⟩
    · have hpin : ∀ d, R.p d.1 ≠ ⊤ → st.u d = S.st.u d :=
        State.pin_of_nonTopMax_lt (st := S.st) (st₁ := st) (by rw [hstu]; exact hagree) hm hbγ.le
      rw [← State.nonTopMax_eq_of_pinned hstP hpin]; exact hm
    · rw [S.st.capField_of_present hj]
      rw [hcapv] at hH
      exact hH.trans_le (min_le_left _ _)
  set st₂ : R.State j := ⟨u₁, clip (N := N) γ v₀, S.st.gate, S.st.shadowP, S.st.shadowC⟩
    with hst₂
  by_cases hact : γ < L.eC hjK (clip (N := N) γ v₀) ∧ st₂.nonTopMax < min S.b γ ∧
      min S.b γ < st₂.capField
  · -- release the frontier exactly to the cap, then reclip
    obtain ⟨he, hm, hH⟩ := hact
    obtain ⟨hbγ, -, -⟩ := hlowcore v₀ hcap₀ st₂ rfl rfl rfl hm hH
    have hshield : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
        R.p a.1 ≠ ⊤ → clip (N := N) γ v₀ (R.privFace a h) < γ := by
      intro a h ha
      have h1 : u₁ (R.reqFace a h) = clip (N := N) γ v₀ (R.privFace a h) := hadm₁.face a h
      rw [← h1]
      exact ((st₂.u_le_nonTopMax _ ha).trans_lt hm).trans_le (min_le_right _ _)
    obtain ⟨v', hv', hface', hcap', -, -, he'⟩ :=
      L.exists_release hjK (clip_respects hγ hv₀) hγ hbot he hshield
    have hcap'' : ∀ d, min (v' d) γ = min (S.st.v d) γ := fun d => (hcap' d).trans (hclip d)
    have hface'' : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
        u₁ (R.reqFace a h) = v' (R.privFace a h) :=
      fun a h => (hadm₁.face a h).trans (hface' a h).symm
    obtain ⟨hadm₃, hclip₃⟩ := R.admissible_clip hS.adm hu₁ hγ hagree hbot hv' hcap'' hface''
    refine ⟨⟨⟨u₁, clip (N := N) γ v', S.st.gate, S.st.shadowP, S.st.shadowC⟩, min S.b γ⟩,
      ⟨hadm₃, hb₁vis.mono L.K_pos, fun _ => hb₁vis, ?_,
        fun _ _ => L.high_clip hj hS hg hγN hcap''⟩, rfl, hclip₃, hb₁min, rfl,
      rfl, rfl⟩
    intro hjK' _ hm₃ hH₃ t ht
    obtain ⟨hbγ', hm₀, hbH₀⟩ := hlowcore v' hcap''
      (⟨u₁, clip (N := N) γ v', S.st.gate, S.st.shadowP, S.st.shadowC⟩ : R.State j) rfl rfl rfl
      hm₃ hH₃
    have hlow₀ := hS.low hjK hg hm₀ hbH₀ t ht
    change max (min S.b γ) (L.eC hjK' (clip (N := N) γ v')) ≤ u₁ (reqCell t _)
    rw [L.eC_clip, he', min_eq_left hbγ'.le, max_eq_right hbγ'.le]
    have hfloor : min (max (min S.b γ) (L.eC hjK (clip (N := N) γ v₀))) γ =
        min (max S.b (L.eC hjK S.st.v)) γ :=
      floor_min hb₁min (L.eC_agree hjK hγK hclip)
    have hγfloor : γ ≤ max S.b (L.eC hjK S.st.v) := by
      rw [min_eq_right (he.le.trans (le_max_right _ _))] at hfloor
      exact min_eq_right_iff.mp hfloor.symm
    exact le_of_capAgree_of_le (hagree _).symm (hγfloor.trans hlow₀)
  · -- the clipped state with the cutoff `b ∧ γ`
    refine ⟨⟨st₂, min S.b γ⟩, ⟨hadm₁, hb₁vis.mono L.K_pos, fun _ => hb₁vis, ?_,
      fun _ _ => L.high_clip hj hS hg hγN hcap₀⟩, rfl,
      hclip, hb₁min, rfl, rfl, rfl⟩
    intro hjK' _ hm hH t ht
    obtain ⟨hbγ, hm₀, hbH₀⟩ := hlowcore v₀ hcap₀ st₂ rfl rfl rfl hm hH
    have hlow₀ := hS.low hjK hg hm₀ hbH₀ t ht
    have he : ¬ γ < L.eC hjK (clip (N := N) γ v₀) := fun h => hact ⟨h, hm, hH⟩
    have hfloor : min (max (min S.b γ) (L.eC hjK (clip (N := N) γ v₀))) γ =
        min (max S.b (L.eC hjK S.st.v)) γ :=
      floor_min hb₁min (L.eC_agree hjK hγK hclip)
    change max (min S.b γ) (L.eC hjK' (clip (N := N) γ v₀)) ≤ u₁ (reqCell t _)
    calc max (min S.b γ) (L.eC hjK' (clip (N := N) γ v₀))
        = min (max (min S.b γ) (L.eC hjK (clip (N := N) γ v₀))) γ :=
          (min_eq_left (max_le (min_le_right _ _) (not_lt.mp he))).symm
      _ = min (max S.b (L.eC hjK S.st.v)) γ := hfloor
      _ ≤ min (S.st.u (reqCell t ((L.top_grade t ht).trans hjK))) γ :=
          min_le_min_right _ hlow₀
      _ = min (u₁ (reqCell t ((L.top_grade t ht).trans hjK))) γ := (hagree _).symm
      _ ≤ u₁ (reqCell t _) := min_le_left _ _

end Ref

end CappedDonor

end VaughtConjecture.Knight
