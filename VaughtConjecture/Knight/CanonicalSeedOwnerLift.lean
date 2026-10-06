/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSeedCutPrefix
public import VaughtConjecture.Knight.CanonicalOwnerBoundary
public import VaughtConjecture.Knight.RetunedCutDecoding

/-! # Constructed active-owner capped lifting on the recursive seed

Owner alignment and old-face completion run on the current boundary cut.
The complete persistent field inventory is retained before recursive prefix
completion. Arbitrary target-local ambient caps survive at every coordinate.
Literal lower restoration is the next composition step.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalSeedOwnerLift
open Transform Value ExtOrd SharpWitnessComposition CoatomBoundaryExtension
open CanonicalRecursiveSeedRows CanonicalSeedCutPrefix
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)

theorem exists_owner_capped_lift
    (c : Cell (cut (D := D))) (hc : (cut (D := D)).grade c = 3)
    {p : (cut (D := D)).below ((cut (D := D)).cell c) → ExtOrd}
    (hp : RespectsSemanticsBelow (cutRows sem) ((cut (D := D)).cell c) p)
    {q : CanonicalSeedAmbient.target sem hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem hA hproper) (A, 3) q)
    {γ : ExtOrd} (hγ : SelfVis 3 γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e, min (p e) γ = min (q (oldTarget sem hA e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell (cut (D := D)),
      GradedLe ((cut (D := D)).cell d) U ∨ GradedLe ((cut (D := D)).cell d) V)
    (hcU : GradedLe ((cut (D := D)).cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell (cut (D := D)), GradedLe ((cut (D := D)).cell d) U →
      GradedLe ((cut (D := D)).cell d) V → GradedLe ((cut (D := D)).cell d) O)
    (hleft : CappedLift (cutRows sem) hcU) (hright : CappedLift (cutRows sem) hOV)
    (hU : U.2 ≤ 3) (hV : V.2 ≤ 3) :
    ∃ r : CanonicalSeedAmbient.target sem hA → ExtOrd,
      RespectsSemanticsBelow (rows sem hA hproper) (A, 3) r ∧
      (∀ e, r (oldTarget sem hA e.1) = min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  classical
  let _ := Fintype.ofFinite ((cut (D := D)).below ((cut (D := D)).cell c))
  let F := data sem hA hproper
  let M := p ⟨c, GradedLe.refl _⟩
  let pp := fun e => min (p e) M
  have hactive : γ ≤ q (oldTarget sem hA c) :=
    (AmbientGradeCharts.cap_reaches_iff (hag ⟨c, GradedLe.refl _⟩)).mp hpc.le
  obtain ⟨a, τ, _, hτ, hbound, _, _, _, _, _, _, _, hambient, _⟩ :=
    CanonicalSeedAmbient.exists_capped_source sem hA hproper hq
      (oldTarget sem hA c) ((congrArg Prod.snd (oldTarget_cell sem hA c)).trans hc)
      hγ hγb hactive
  have hface (e : (cut (D := D)).below ((cut (D := D)).cell c)) :
      τ (a.val (occurrence (D := D) e.1)) = min (p e) γ := by
    have he := hambient (oldTarget sem hA e.1)
    change τ (source sem hA hproper a
      (boundary sem hA (occurrence (D := D) e.1))) = _ at he
    rw [source_boundary] at he
    exact he.trans (hag e).symm
  have H := CanonicalOwnerBoundary.exists_completion (sem := cutRows sem) (a := a.val) c
    (by simpa only [hc] using a.property.2) (occurrence (D := D)) a.property.1 hp
    hcover hcU hOU hOV hinter hleft hright
    (by simpa only [hc] using hU) (by simpa only [hc] using hV)
    (by simpa only [hc] using hτ) (by simpa only [hc] using hγ)
    (bot_lt_iff_ne_bot.mpr hγb) hbound hface hpc
  simp only [hc] at H
  obtain ⟨h, ρ, δ, u, _, _, ⟨B, hB, hBeq⟩, hρ, hγδ, hδM, hδvis,
      hρh, hu, hucap, huface, _, hread, hretune⟩ := H
  let tail := 2 * Fintype.card (Cell D) + 1
  have hroom : h < ofOrd (Ordinal.omega0 * tail) := by
    rw [hBeq]
    exact ofOrd_lt_ofOrd.mpr (code_add_lt_mul
      (Nat.cast_lt.mpr (by dsimp [tail]; omega)) _)
  let S := RelativePrefixEncoding.inventory pp δ
  let T := S.card + tail
  let C := CanonicalPairedInverse.grid 3 (T + 1)
  have hC : SelfVis 3 C := CanonicalPairedInverse.grid_visible 3 (T + 1)
  have hhC : h ≤ C := hroom.le.trans (ofOrd_le_ofOrd.mpr (le_trans
    (by gcongr; dsimp [T]; omega) le_self_add))
  have hfC (e : (cut (D := D)).below ((cut (D := D)).cell c)) : u e.1 ≤ C := by
    rw [huface]
    change AlignedCutEncoding.encode (fun e => a.val (occurrence (D := D) e.1))
      pp 3 tail h δ e ≤ C
    by_cases he : pp e ≤ δ
    · rw [AlignedCutEncoding.encode_of_le _ _ _ _ _ _ e he]
      exact (min_le_right _ _).trans hhC
    · rw [AlignedCutEncoding.encode_of_gt _ _ hroom e (not_le.mp he)]
      rcases mem_codedAlphabet_iff.mp (PaddedSourceDecoder.encode_mem S (3) tail
          (pp e)) with hb | ⟨b, n, hb, _, he⟩
      · rw [hb]; exact bot_le
      · rw [he]
        exact ofOrd_le_ofOrd.mpr ((code_add_lt_mul
          (Nat.cast_lt.mpr (by dsimp [T]; omega)) n).le.trans le_self_add)
  let v : Cell (cut (D := D)) → ExtOrd := fun d => min (u d) C
  have hv : RespectsSemantics (cutRows sem) v :=
    ((hu.toBelow (A, 3)).cap hC).toRespects
      (fun d => ⟨D.isPlan.subset_of_mem (D.scope_mem_plan _),
        GradeCutBoundary.grade_bound D 3 d⟩)
  have hvt : ∀ d, v d ≠ ⊤ := by
    intro d hd
    change min (u d) C = ⊤ at hd
    exact ofOrd_ne_top _ (top_le_iff.mp (hd ▸ min_le_right (u d) C))
  have hvcap (d : Cell (cut (D := D))) :
      min (v d) h = min (a.val (occurrence (D := D) d)) h := by
    dsimp only [v]
    rw [min_assoc, min_eq_right hhC]
    exact hucap d
  obtain ⟨w, hw, hwold, hwcap⟩ := CanonicalSeedCutPrefix.exists_section
    sem hA hproper a hv hvt (hB.trans (Nat.le_succ _))
    (fun d => by rw [← hBeq]; exact (hvcap d).symm)
  have hwcap' (d) : min (w d) h = min (source sem hA hproper a d) h := by
    rw [hBeq]
    exact hwcap d
  apply RetunedCutDecoding.decode_lift
    (fun d => source sem hA hproper a d.1)
    pp (fun e => oldTarget sem hA e.1)
    (F.profile_respects (controller sem hA a))
    hw hq (fun d => d.2.2) hρ hδvis hγb hγδ hroom hρh.ge
    (fun d => hwcap' d.1)
  · intro d
    exact (hretune _ (source_short sem hA hproper a d.1)).trans
      ((min_eq_left (hbound _)).trans (hambient d))
  · intro e
    change min (pp e) δ = min (ρ (source sem hA hproper a
      (boundary sem hA (occurrence (D := D) e.1)))) δ
    rw [source_boundary]
    dsimp only [pp]
    rw [min_assoc, min_eq_right hδM]
    exact hread e
  · intro e
    have hs : ((fun d => source sem hA hproper a d.1) ∘
        fun e : (cut (D := D)).below ((cut (D := D)).cell c) => oldTarget sem hA e.1) =
        fun e => a.val (occurrence (D := D) e.1) := by
      funext e
      exact source_boundary sem hA hproper a (occurrence (D := D) e.1)
    rw [hs]
    change w (oldTarget sem hA e.1).1 = _
    rw [hwold, show v e.1 = u e.1 from min_eq_left (hfC e), huface]

end
end VaughtConjecture.Knight.CanonicalSeedOwnerLift
