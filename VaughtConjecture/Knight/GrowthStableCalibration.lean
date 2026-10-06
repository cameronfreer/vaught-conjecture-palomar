/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthStableSelectedInput
public import VaughtConjecture.Knight.GrowthHighCover
public import VaughtConjecture.Knight.CappedDonorContext
public import VaughtConjecture.Knight.RawReferenceContext

/-! # Actual reference acquisition for a proper stable marker

Old-block references are acquired in the original model. The new stable block
uses the attained marker itself. A subsequent growth cover contains both and
places them below an actual top cap of sufficiently high grade. No occurrence
of the chosen stable donor is assumed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthStableCalibration
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan
noncomputable section
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}

/-- The stable cap bound, with the proof from integration's
`SameStageCalibration.stable_ge_of_top`, without its guard dependencies. -/
theorem stable_cap_bound (hM : W.IsModel) {m : ℕ} {u : Fin m ↪ M} {Q : S α.1 m}
    (hQ : W.eval u = some Q) {c : Cell Q.scheme.scheme} (hc : Q.label c = ⊤) :
    ofOrd (α.1 + Q.scheme.scheme.grade c) ≤ W.stableValue u Q c := by
  have hα := le_stableValue_of_top (R := W) hQ hc
  have hvis : SelfVis (Q.scheme.scheme.grade c) (W.stableValue u Q c) :=
    ((stableLiftRespects hM hQ).orderly c).symm
  rcases ExtOrd.cases (W.stableValue u Q c) with hb | ht | ⟨γ, hγ⟩
  · rw [hb] at hα; exact absurd hα (not_ofOrd_le_bot _)
  · rw [ht]; exact le_top
  · rw [hγ] at hα hvis ⊢
    rw [selfVis_ofOrd_iff] at hvis
    have hlim := limitPart_mono (ofOrd_le_ofOrd.mp hα)
    rw [limitPart_eq_self_of_isNonSuccessor (Or.inr α.2)] at hlim
    apply ofOrd_le_ofOrd.mpr
    calc α.1 + (Q.scheme.scheme.grade c : Ordinal.{0})
        ≤ limitPart γ + (Q.scheme.scheme.grade c : Ordinal.{0}) := add_le_add_left hlim _
      _ ≤ limitPart γ + finitePart γ := add_le_add_right (Nat.cast_le.mpr hvis) _
      _ = γ := limitPart_add_finitePart γ

/-- Construct all block references under one actual cap, while retaining both
the requested root and the independently supplied attained marker. The floor
`L` is chosen before this construction; the physical grade is strictly larger.
The root may be empty. -/
theorem exists_calibration (hM : W.IsModel) (hg : W.HasTopGradeGrowth)
    {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} (hp : W.eval t = some p)
    (a : Cell p.scheme.scheme) (hatop : p.label a = ⊤) {i : ℕ}
    (ha : W.stableValue t p a = ofOrd (α.1 + i))
    {k : ℕ} (s : Fin k ↪ M) (p₀ : S α.1 k) (hs : W.eval s = some p₀)
    (S : Finset Ordinal.{0}) (hS : ∀ μ ∈ S, limitPart μ = μ)
    (hle : ∀ μ ∈ S, μ ≤ α.1) (L : ℕ) :
    ∃ (m : ℕ) (u : Fin m ↪ M) (Q : Knight.S α.1 m), W.eval u = some Q ∧
      ∃ (g : Fin k ↪ Fin m) (f : Fin n ↪ Fin m), g.trans u = s ∧ f.trans u = t ∧
        typeMap g Q = some p₀ ∧ ∃ hf : typeMap f Q = some p,
          ∃ (c : Cell Q.scheme.scheme), Q.scheme.scheme.scope c = Finset.univ ∧
            Q.label c = ⊤ ∧ L < Q.scheme.scheme.grade c ∧ i < Q.scheme.scheme.grade c ∧
            ∃ hab : GradedLe (Q.scheme.scheme.cell (mapCell hf a)) (Q.scheme.scheme.cell c),
              W.stableValue u Q (mapCell hf a) = ofOrd (α.1 + i) ∧
              ofOrd (α.1 + L) < W.stableValue u Q c ∧
              ofOrd (α.1 + i) < W.stableValue u Q c ∧
              ∃ (ref : Ordinal.{0} → Q.scheme.scheme.below (Q.scheme.scheme.cell c))
                (off : Ordinal.{0} → ℕ),
                (∀ μ ∈ S, off μ < Q.scheme.scheme.grade c ∧
                  W.stableValue u Q (ref μ).1 = ofOrd (μ + off μ) ∧
                  ofOrd (μ + off μ) < W.stableValue u Q c) ∧
                ref α.1 = ⟨mapCell hf a, hab⟩ ∧ off α.1 = i := by
  classical
  let old := S.filter (fun μ => μ < α.1)
  have hold : ∀ μ ∈ old, IsNonSuccessor μ ∧ μ < α.1 := by
    intro μ hμ
    have hm := Finset.mem_filter.mp hμ
    exact ⟨hS μ hm.1 ▸ CappedDonor.isNonSuccessor_limitPart μ, hm.2⟩
  obtain ⟨C⟩ := exists_rawReferenceContext hM p₀ hs old hold
  obtain ⟨z, hxz, ⟨g, hgu⟩, hhigh, c, hsc, hgr, hc⟩ :=
    exists_high_common_cover hM.consistent hM.covering hg ⟨n, t, p, hp⟩ C.ctx
      (max (max L C.m) (max C.offsetBound i))
  obtain ⟨f, hfu, hf⟩ := hxz
  let m := z.arity
  let u := z.tuple
  let Q := z.type
  have hQ : W.eval u = some Q := z.eval_eq
  have hfloor : max (max L C.m) (max C.offsetBound i) < Q.topGrade := hhigh
  have hi : i < Q.topGrade := by omega
  have hab : GradedLe (Q.scheme.scheme.cell (mapCell hf a)) (Q.scheme.scheme.cell c) := by
    constructor
    · change Q.scheme.scheme.scope (mapCell hf a) ⊆ Q.scheme.scheme.scope c
      rw [hsc]; exact Finset.subset_univ _
    · change Q.scheme.scheme.grade (mapCell hf a) ≤ Q.scheme.scheme.grade c
      rw [grade_mapCell, hgr]
      exact (le_csSup p.topGrades_bddAbove (grade_mem_topGrades hatop)).trans
        (topGrade_le_of_typeMap_eq_some hf)
  have hgQ : typeMap g Q = some C.p₀ := by
    have h := hM.consistent u Q g hQ
    rw [hgu, C.eval_ctx, knightTower_pull] at h
    exact h.symm
  have hroot : (C.proj.trans g).trans u = s := by
    rw [Function.Embedding.trans_assoc, hgu, C.proj_ctx]
  have hrootQ : typeMap (C.proj.trans g) Q = some p₀ := by
    have h := hM.consistent u Q (C.proj.trans g) hQ
    rw [hroot, hs, knightTower_pull] at h
    exact h.symm
  have hL : L < Q.scheme.scheme.grade c := by rw [hgr]; omega
  have hi' : i < Q.scheme.scheme.grade c := by rwa [hgr]
  have hm : C.m < Q.scheme.scheme.grade c := by rw [hgr]; omega
  have hoff : C.offsetBound < Q.scheme.scheme.grade c := by rw [hgr]; omega
  have hbound := stable_cap_bound hM hQ hc
  have hcut : ofOrd (α.1 + L) < W.stableValue u Q c :=
    (ofOrd_lt_ofOrd.mpr (add_lt_add_right (Nat.cast_lt.mpr hL) _)).trans_le hbound
  have hai : ofOrd (α.1 + i) < W.stableValue u Q c :=
    (ofOrd_lt_ofOrd.mpr (add_lt_add_right (Nat.cast_lt.mpr hi') _)).trans_le hbound
  have hmarker : W.stableValue u Q (mapCell hf a) = ofOrd (α.1 + i) := by
    rw [stableValue_mapCell' hM.consistent hQ hfu hf, ha]
  have hbelow (d : Cell C.p₀.scheme.scheme) :
      GradedLe (Q.scheme.scheme.cell (mapCell hgQ d)) (Q.scheme.scheme.cell c) := by
    constructor
    · change Q.scheme.scheme.scope (mapCell hgQ d) ⊆ Q.scheme.scheme.scope c
      rw [hsc]; exact Finset.subset_univ _
    · change Q.scheme.scheme.grade (mapCell hgQ d) ≤ Q.scheme.scheme.grade c
      rw [grade_mapCell]
      exact (C.p₀.scheme.scheme.grade_le_card_scope d).trans
        ((Finset.card_le_univ _).trans (by simpa using hm.le))
  let ref : Ordinal.{0} → Q.scheme.scheme.below (Q.scheme.scheme.cell c) := fun μ =>
    if μ = α.1 then ⟨mapCell hf a, hab⟩ else
      if hμ : μ ∈ old then ⟨mapCell hgQ (C.repBase ⟨μ, hμ⟩), hbelow _⟩ else
        ⟨c, GradedLe.refl _⟩
  let off : Ordinal.{0} → ℕ := fun μ => if μ = α.1 then i else
    if hμ : μ ∈ old then C.repOff ⟨μ, hμ⟩ else 0
  refine ⟨m, u, Q, hQ, C.proj.trans g, f, hroot, hfu, hrootQ, hf, c, hsc, hc,
    hL, hi', hab, hmarker, hcut, hai, ref, off, ?_, ?_, by simp [off]⟩
  swap
  · apply Subtype.ext
    simp [ref]
  intro μ hμ
  by_cases heq : μ = α.1
  · subst μ; simpa [ref, off] using And.intro hi' (And.intro hmarker hai)
  · have hmα := lt_of_le_of_ne (hle μ hμ) heq
    have hmem : μ ∈ old := Finset.mem_filter.mpr ⟨hμ, hmα⟩
    let b : old := ⟨μ, hmem⟩
    have hlab := C.rep_label b
    have hnt : C.p₀.label (C.repBase b) ≠ ⊤ := hlab ▸ ofOrd_ne_top _
    have hstable : W.stableValue u Q (mapCell hgQ (C.repBase b)) =
        ofOrd (μ + C.repOff b) := by
      rw [stableValue_mapCell' hM.consistent hQ hgu hgQ,
        stableValue_of_ne_top hM.consistent hM.covering C.eval_ctx hnt, hlab]
    have hlt : ofOrd (μ + C.repOff b) < W.stableValue u Q c := by
      have hb := (C.p₀.label_bound (C.repBase b)).resolve_right hnt
      rw [hlab] at hb
      exact hb.trans_le ((ofOrd_le_ofOrd.mpr le_self_add).trans hbound)
    simpa [ref, off, heq, hmem, b] using
      And.intro ((C.rep_off_le b).trans_lt hoff) (And.intro hstable hlt)

end
end VaughtConjecture.Knight.GrowthStableCalibration
