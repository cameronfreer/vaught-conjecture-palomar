/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedAmbient
public import VaughtConjecture.Knight.CanonicalMixedPrefix
public import VaughtConjecture.Knight.CanonicalOwnerBoundary
public import VaughtConjecture.Knight.RetunedCutDecoding

/-! # An arbitrary-ambient active-owner lift on the canonical carrier

Availability constructs the ambient source; owner locality constructs alignment;
the two old faces construct a boundary completion. A finite clipping ceiling
makes that coded boundary proper without changing its prescription or source
caps. The canonical supported-prefix operator extends it over BOTH controller
layers, then retuned decoding preserves every original ambient cap.

The conclusion reads the prescribed face capped at its owner. Literal readback
therefore follows when that owner dominates the face. Larger prescribed lower-
grade values remain a separate restoration obligation.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalMixedOwnerLift
open Transform Value ExtOrd SharpWitnessComposition CanonicalMixedGradeLayers
open CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)
variable (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
variable (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

abbrev oldTarget (d : Cell D) : CanonicalMixedAmbient.target sem j hj hjA k hk hkA :=
  SourcePrefixAmbient.occurrence (data sem j hj hjA hproper k hg hk hkA hjk)
    (oldCell sem j hj hjA k hk hkA (lowerOld sem j hj hjA d))

theorem oldTarget_grade (d : Cell D) :
    (scheme sem j hj hjA k hk hkA).grade
      (oldTarget sem j hj hjA hproper k hg hk hkA hjk d).1 = D.grade d := by
  change (SourceLayerCarrier.scheme _ _ _ _ _).grade
    (SourceLayerCarrier.toCell _ _ _ _ _ (.inl
      (SourceLayerCarrier.toCell _ _ _ _ _ (.inl d)))) = _
  simp only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]

theorem exists_owner_capped_lift (c : Cell D) (hc : D.grade c = k)
    {p : D.below (D.cell c) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {q : CanonicalMixedAmbient.target sem j hj hjA k hk hkA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k) q)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e : D.below (D.cell c), min (p e) γ =
      min (q (oldTarget sem j hj hjA hproper k hg hk hkA hjk e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hcU : GradedLe (D.cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hcU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ k) (hV : V.2 ≤ k) :
    ∃ r : CanonicalMixedAmbient.target sem j hj hjA k hk hkA → ExtOrd,
      RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k) r ∧
      (∀ e : D.below (D.cell c),
        r (oldTarget sem j hj hjA hproper k hg hk hkA hjk e.1) =
          min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  classical
  let _ := Fintype.ofFinite (D.below (D.cell c))
  subst k
  let F := data sem j hj hjA hproper (D.grade c) hg hk hkA hjk
  let M := p ⟨c, GradedLe.refl _⟩
  let pp : D.below (D.cell c) → ExtOrd := fun e => min (p e) M
  have hactive : γ ≤ q (oldTarget sem j hj hjA hproper (D.grade c) hg hk hkA hjk c) :=
    (AmbientGradeCharts.cap_reaches_iff (hag ⟨c, GradedLe.refl _⟩)).mp hpc.le
  obtain ⟨a, τ, _, hτ, hbound, _, _, _, _, _, _, _, hambient, _⟩ :=
    CanonicalMixedAmbient.exists_capped_source sem j hj hjA hproper (D.grade c) hg hk hkA
      hjk hq (oldTarget sem j hj hjA hproper (D.grade c) hg hk hkA hjk c)
      (oldTarget_grade sem j hj hjA hproper (D.grade c) hg hk hkA hjk c) hγ hγb hactive
  have hface (e : D.below (D.cell c)) : τ (a.val e.1) = min (p e) γ := by
    have he := hambient (oldTarget sem j hj hjA hproper (D.grade c) hg hk hkA hjk e.1)
    change τ (source sem j hj hjA hproper (D.grade c) hg hk hkA hjk a
      (oldCell sem j hj hjA (D.grade c) hk hkA (lowerOld sem j hj hjA e.1))) = _ at he
    rw [source_boundary] at he
    exact he.trans (hag e).symm
  obtain ⟨h, ρ, δ, u, hhpos, hvis, ⟨B, hB, hBeq⟩, hρ, hγδ, hδM, hδvis,
      hρh, hu, hucap, huface, _, hread, hretune⟩ :=
    CanonicalOwnerBoundary.exists_completion c a.property.2 id a.property.1 hp
      hcover hcU hOU hOV hinter hleft hright hU hV hτ hγ
      (bot_lt_iff_ne_bot.mpr hγb) hbound hface hpc
  let tail := 2 * Fintype.card (Cell D) + 1
  have hroom : h < ofOrd (Ordinal.omega0 * tail) := by
    rw [hBeq]
    exact ofOrd_lt_ofOrd.mpr (code_add_lt_mul
      (Nat.cast_lt.mpr (by dsimp [tail]; omega)) _)
  let S := RelativePrefixEncoding.inventory pp δ
  let T := S.card + tail
  let C := ofOrd (Ordinal.omega0 * (T + 1 : ℕ) + D.grade c)
  have hC : SelfVis (D.grade c) C := CanonicalPairedInverse.grid_visible _ _
  have hhC : h ≤ C := hroom.le.trans (ofOrd_le_ofOrd.mpr (le_trans
    (by gcongr; dsimp [T]; omega) le_self_add))
  have hfC (e : D.below (D.cell c)) : u e.1 ≤ C := by
    rw [huface]
    change AlignedCutEncoding.encode (fun e => a.val e.1) pp (D.grade c) tail h δ e ≤ C
    by_cases he : pp e ≤ δ
    · rw [AlignedCutEncoding.encode_of_le _ _ _ _ _ _ e he]
      exact (min_le_right _ _).trans hhC
    · rw [AlignedCutEncoding.encode_of_gt _ _ hroom e (not_le.mp he)]
      rcases mem_codedAlphabet_iff.mp (PaddedSourceDecoder.encode_mem S (D.grade c) tail
          (pp e)) with hb | ⟨b, n, hb, _, he⟩
      · rw [hb]; exact bot_le
      · rw [he]
        exact ofOrd_le_ofOrd.mpr ((code_add_lt_mul
          (Nat.cast_lt.mpr (by dsimp [T]; omega)) n).le.trans le_self_add)
  let v : Cell D → ExtOrd := fun d => min (u d) C
  have hv : RespectsSemantics sem v :=
    ((hu.toBelow (A, D.grade c)).cap hC).toRespects
      (fun d => ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), hg d⟩)
  have hvt : ∀ d, v d ≠ ⊤ := by
    intro d hd
    change min (u d) C = ⊤ at hd
    exact ofOrd_ne_top _ (top_le_iff.mp (hd ▸ min_le_right (u d) C))
  have hvcap (d : Cell D) : min (v d) h = min (a.val d) h := by
    dsimp only [v]
    rw [min_assoc, min_eq_right hhC]
    exact hucap d
  obtain ⟨w, hw, hwold, hwcap⟩ := CanonicalMixedPrefix.exists_section sem j hj hjA hproper
    (D.grade c) hg hk hkA hjk a hv hvt (hB.trans (Nat.le_succ _))
    (fun d => by rw [← hBeq]; exact (hvcap d).symm)
  have hwcap' (d) : min (w d) h = min (source sem j hj hjA hproper
      (D.grade c) hg hk hkA hjk a d) h := by rw [hBeq]; exact hwcap d
  apply RetunedCutDecoding.decode_lift
    (fun d => source sem j hj hjA hproper (D.grade c) hg hk hkA hjk a d.1)
    pp (fun e => oldTarget sem j hj hjA hproper (D.grade c) hg hk hkA hjk e.1)
    ((F.profile_respects (controller sem j hj hjA (D.grade c) hk hkA a)).toBelow _)
    (hw.toBelow _) hq (fun d => F.max_grade d.1) hρ hδvis hγb hγδ hroom hρh.ge
    (fun d => hwcap' d.1)
  · intro d
    exact (hretune _ (source_short sem j hj hjA hproper (D.grade c) hg hk hkA hjk a d.1)).trans
      ((min_eq_left (hbound _)).trans (hambient d))
  · intro e
    change min (pp e) δ = min (ρ (source sem j hj hjA hproper (D.grade c) hg hk hkA hjk a
      (oldCell sem j hj hjA (D.grade c) hk hkA (lowerOld sem j hj hjA e.1)))) δ
    rw [source_boundary]
    dsimp only [pp]
    rw [min_assoc, min_eq_right hδM]
    exact hread e
  · intro e
    have hs : ((fun d => source sem j hj hjA hproper (D.grade c) hg hk hkA hjk a d.1) ∘
        fun e : D.below (D.cell c) => oldTarget sem j hj hjA hproper
          (D.grade c) hg hk hkA hjk e.1) = fun e => a.val e.1 := by
      funext e
      exact source_boundary sem j hj hjA hproper (D.grade c) hg hk hkA hjk a e.1
    rw [hs]
    change w (oldCell sem j hj hjA (D.grade c) hk hkA (lowerOld sem j hj hjA e.1)) = _
    rw [hwold, show v e.1 = u e.1 from min_eq_left (hfC e), huface]
    rfl

/-- A genuine original-cap lift for arbitrary lawful ambients, when the
prescribed owner dominates its face. The domination is explicit, not claimed
to follow from arbitrary lower-grade legality. No alignment or completion is
an input. Literal top on the prescribed face is allowed. -/
theorem exists_lift (c : Cell D) (hc : D.grade c = k)
    {p : D.below (D.cell c) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    (hdom : ∀ e, p e ≤ p ⟨c, GradedLe.refl _⟩)
    {q : CanonicalMixedAmbient.target sem j hj hjA k hk hkA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k) q)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e : D.below (D.cell c), min (p e) γ =
      min (q (oldTarget sem j hj hjA hproper k hg hk hkA hjk e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hcU : GradedLe (D.cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hcU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ k) (hV : V.2 ≤ k) :
    ∃ r : CanonicalMixedAmbient.target sem j hj hjA k hk hkA → ExtOrd,
      RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k) r ∧
      (∀ e : D.below (D.cell c),
        r (oldTarget sem j hj hjA hproper k hg hk hkA hjk e.1) = p e) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨r, hr, hread, hcap⟩ := exists_owner_capped_lift sem j hj hjA hproper k hg hk hkA
    hjk c hc hp hq hγ hγb hag hpc hcover hcU hOU hOV hinter hleft hright hU hV
  exact ⟨r, hr, fun e => (hread e).trans (min_eq_left (hdom e)), hcap⟩

end
end VaughtConjecture.Knight.CanonicalMixedOwnerLift
