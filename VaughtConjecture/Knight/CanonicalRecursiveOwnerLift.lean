/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveCutPrefix
public import VaughtConjecture.Knight.CanonicalOwnerBoundary
public import VaughtConjecture.Knight.RetunedCutDecoding

/-! # Constructed active-owner capped lifting on the recursive successor

Owner alignment and old-face completion run on the current boundary cut.
The complete persistent field inventory is retained before recursive prefix
completion. Arbitrary target-local ambient caps survive at every coordinate.
Literal lower restoration is the next composition step.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveOwnerLift
open Transform Value ExtOrd SharpWitnessComposition CoatomBoundaryExtension
open CanonicalRecursiveSuccessorRows CanonicalRecursiveCutPrefix
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))

theorem exists_owner_capped_lift
    (c : Cell (cut (D := D) n)) (hc : (cut (D := D) n).grade c = n + 4)
    {p : (cut (D := D) n).below ((cut (D := D) n).cell c) → ExtOrd}
    (hp : RespectsSemanticsBelow (cutRows sem n) ((cut (D := D) n).cell c) p)
    {q : CanonicalRecursiveAmbient.target sem n hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem n hA hproper P) (A, n + 4) q)
    {γ : ExtOrd} (hγ : SelfVis (n + 4) γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e, min (p e) γ = min (q (oldTarget sem n hA e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell (cut (D := D) n),
      GradedLe ((cut (D := D) n).cell d) U ∨ GradedLe ((cut (D := D) n).cell d) V)
    (hcU : GradedLe ((cut (D := D) n).cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell (cut (D := D) n), GradedLe ((cut (D := D) n).cell d) U →
      GradedLe ((cut (D := D) n).cell d) V → GradedLe ((cut (D := D) n).cell d) O)
    (hleft : CappedLift (cutRows sem n) hcU) (hright : CappedLift (cutRows sem n) hOV)
    (hU : U.2 ≤ n + 4) (hV : V.2 ≤ n + 4) :
    ∃ r : CanonicalRecursiveAmbient.target sem n hA → ExtOrd,
      RespectsSemanticsBelow (rows sem n hA hproper P) (A, n + 4) r ∧
      (∀ e, r (oldTarget sem n hA e.1) = min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  classical
  let _ := Fintype.ofFinite ((cut (D := D) n).below ((cut (D := D) n).cell c))
  let F := data sem n hA hproper P
  let M := p ⟨c, GradedLe.refl _⟩
  let pp := fun e => min (p e) M
  have hactive : γ ≤ q (oldTarget sem n hA c) :=
    (AmbientGradeCharts.cap_reaches_iff (hag ⟨c, GradedLe.refl _⟩)).mp hpc.le
  obtain ⟨a, τ, _, hτ, hbound, _, _, _, _, _, _, _, hambient, _⟩ :=
    CanonicalRecursiveAmbient.exists_capped_source sem n hA hproper P hq
      (oldTarget sem n hA c) ((congrArg Prod.snd (oldTarget_cell sem n hA c)).trans hc)
      hγ hγb hactive
  have hface (e : (cut (D := D) n).below ((cut (D := D) n).cell c)) :
      τ (a.val (occurrence (D := D) n e.1)) = min (p e) γ := by
    have he := hambient (oldTarget sem n hA e.1)
    change τ (source sem n hA hproper P a
      (boundary sem n hA (occurrence (D := D) n e.1))) = _ at he
    rw [source_boundary] at he
    exact he.trans (hag e).symm
  have H := CanonicalOwnerBoundary.exists_completion (sem := cutRows sem n) (a := a.val) c
    (by simpa only [hc] using a.property.2) (occurrence (D := D) n) a.property.1 hp
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
  let C := CanonicalPairedInverse.grid (n + 4) (T + 1)
  have hC : SelfVis (n + 4) C := CanonicalPairedInverse.grid_visible (n + 4) (T + 1)
  have hhC : h ≤ C := hroom.le.trans (ofOrd_le_ofOrd.mpr (le_trans
    (by gcongr; dsimp [T]; omega) le_self_add))
  have hfC (e : (cut (D := D) n).below ((cut (D := D) n).cell c)) : u e.1 ≤ C := by
    rw [huface]
    change AlignedCutEncoding.encode (fun e => a.val (occurrence (D := D) n e.1))
      pp (n + 4) tail h δ e ≤ C
    by_cases he : pp e ≤ δ
    · rw [AlignedCutEncoding.encode_of_le _ _ _ _ _ _ e he]
      exact (min_le_right _ _).trans hhC
    · rw [AlignedCutEncoding.encode_of_gt _ _ hroom e (not_le.mp he)]
      rcases mem_codedAlphabet_iff.mp (PaddedSourceDecoder.encode_mem S ((n + 4)) tail
          (pp e)) with hb | ⟨b, n, hb, _, he⟩
      · rw [hb]; exact bot_le
      · rw [he]
        exact ofOrd_le_ofOrd.mpr ((code_add_lt_mul
          (Nat.cast_lt.mpr (by dsimp [T]; omega)) n).le.trans le_self_add)
  let v : Cell (cut (D := D) n) → ExtOrd := fun d => min (u d) C
  have hv : RespectsSemantics (cutRows sem n) v :=
    ((hu.toBelow (A, (n + 4))).cap hC).toRespects
      (fun d => ⟨D.isPlan.subset_of_mem (D.scope_mem_plan _),
        GradeCutBoundary.grade_bound D (n + 4) d⟩)
  have hvt : ∀ d, v d ≠ ⊤ := by
    intro d hd
    change min (u d) C = ⊤ at hd
    exact ofOrd_ne_top _ (top_le_iff.mp (hd ▸ min_le_right (u d) C))
  have hvcap (d : Cell (cut (D := D) n)) :
      min (v d) h = min (a.val (occurrence (D := D) n d)) h := by
    dsimp only [v]
    rw [min_assoc, min_eq_right hhC]
    exact hucap d
  obtain ⟨w, hw, hwold, hwcap⟩ := CanonicalRecursiveCutPrefix.exists_section
    sem n hA hproper P a hv hvt (hB.trans (Nat.le_succ _))
    (fun d => by rw [← hBeq]; exact (hvcap d).symm)
  have hwcap' (d) : min (w d) h = min (source sem n hA hproper P a d) h := by
    rw [hBeq]
    exact hwcap d
  apply RetunedCutDecoding.decode_lift
    (fun d => source sem n hA hproper P a d.1)
    pp (fun e => oldTarget sem n hA e.1)
    (F.profile_respects (controller sem n hA a))
    hw hq (fun d => d.2.2) hρ hδvis hγb hγδ hroom hρh.ge
    (fun d => hwcap' d.1)
  · intro d
    exact (hretune _ (source_short sem n hA hproper P a d.1)).trans
      ((min_eq_left (hbound _)).trans (hambient d))
  · intro e
    change min (pp e) δ = min (ρ (source sem n hA hproper P a
      (boundary sem n hA (occurrence (D := D) n e.1)))) δ
    rw [source_boundary]
    dsimp only [pp]
    rw [min_assoc, min_eq_right hδM]
    exact hread e
  · intro e
    have hs : ((fun d => source sem n hA hproper P a d.1) ∘
        fun e : (cut (D := D) n).below ((cut (D := D) n).cell c) => oldTarget sem n hA e.1) =
        fun e => a.val (occurrence (D := D) n e.1) := by
      funext e
      exact source_boundary sem n hA hproper P a (occurrence (D := D) n e.1)
    rw [hs]
    change w (oldTarget sem n hA e.1).1 = _
    rw [hwold, show v e.1 = u e.1 from min_eq_left (hfC e), huface]

end
end VaughtConjecture.Knight.CanonicalRecursiveOwnerLift
