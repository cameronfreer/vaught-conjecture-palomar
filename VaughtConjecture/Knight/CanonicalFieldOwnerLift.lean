/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalFieldPrefix
public import VaughtConjecture.Knight.CanonicalOwnerBoundary
public import VaughtConjecture.Knight.SourcePrefixAmbient
public import VaughtConjecture.Knight.RetunedCutDecoding

/-! # Arbitrary-ambient owner lifting on the complete-field lower catalogue

Only the two old faces supply lifting. Unrepresented fields are retained by
`CanonicalFieldPrefix`, so every lower controller's cap survives. The result
initially reads the prescription capped at its owner; grade one will choose
a maximal prescribed owner to obtain literal readback.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalFieldOwnerLift
open Transform Value ExtOrd SharpWitnessComposition CanonicalFieldLayer
open CoatomBoundaryExtension SourcePrefixRows
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (X : Type*) [Fintype X] (occ : Cell D → X)
variable (hj : 0 < j) (hA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ j)

abbrev target := (scheme sem j X occ hj hA).below (A, j)

abbrev oldTarget (d : Cell D) : target sem j X occ hj hA :=
  SourcePrefixAmbient.occurrence (data sem j X occ hj hA hproper hg)
    (old sem j X occ hj hA d)

theorem oldTarget_grade (d : Cell D) :
    (scheme sem j X occ hj hA).grade (oldTarget sem j X occ hj hA hproper hg d).1 =
      D.grade d := by
  simp only [oldTarget, SourcePrefixAmbient.occurrence, old, CellScheme.grade,
    SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]

theorem source_short (a : Profile sem j X occ)
    (d : Cell (scheme sem j X occ hj hA)) :
    Short j (source sem j X occ hj hA hproper hg a d) := by
  let F := data sem j X occ hj hA hproper hg
  by_cases he : (scheme sem j X occ hj hA).cell d = (A, j)
  · have hh : source sem j X occ hj hA hproper hg a d ∈ F.grid := by
      change F.profile (controller sem j X occ hj hA a) d ∈ F.grid
      rw [show d = (⟨d, he⟩ : SourcePrefixLayer.Controller _ j).1 from rfl, F.profile_new]
      exact cut_mem F.bot_mem _ _
    exact grid_short j X hh
  · obtain ⟨e, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j X occ)
      j hj hA d he
    rw [source_old]
    exact profile_short sem j X occ a (occ e)

private def seed : Profile sem j X occ := encode sem j X occ hg
  (p := fun _ => ⊥) (RespectsSemantics.bot sem) (fun _ => bot_ne_top)

theorem exists_capped_source {q : target sem j X occ hj hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem j X occ hj hA hproper hg) (A, j) q)
    (d : target sem j X occ hj hA) (hd : (scheme sem j X occ hj hA).grade d.1 = j)
    {γ : ExtOrd} (hγ : SelfVis j γ) (hactive : γ ≤ q d) :
    ∃ (a : Profile sem j X occ) (τ : ExtOrd → ExtOrd),
      Witness (gTop j) τ ∧ (∀ x, τ x ≤ γ) ∧
      ∀ x : target sem j X occ hj hA,
        τ (source sem j X occ hj hA hproper hg a x.1) = min (q x) γ := by
  let F := data sem j X occ hj hA hproper hg
  obtain ⟨c, τ, _, hτ, hb, _, hr⟩ := SourcePrefixAmbient.exists_active_source F
    (controller sem j X occ hj hA (seed sem j X occ hg)) hq d hd hγ hactive
  let a := member sem j X occ hj hA hproper c
  have ha : controller sem j X occ hj hA a = c :=
    (SeparatedSourceLayerCarrier.controllerEquiv D (Profile sem j X occ) j hj hA
      (SeparatedSourceLayerCarrier.separated_of_proper D j hproper)).apply_symm_apply c
  refine ⟨a, τ, hτ, hb, ?_⟩
  intro x
  change τ (F.profile (controller sem j X occ hj hA a) x.1) = _
  rw [ha]
  exact hr x

theorem exists_owner_capped_lift (hinj : Function.Injective occ)
    (c : Cell D) (hc : D.grade c = j)
    {p : D.below (D.cell c) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {q : target sem j X occ hj hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem j X occ hj hA hproper hg) (A, j) q)
    {γ : ExtOrd} (hγ : SelfVis j γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e : D.below (D.cell c), min (p e) γ =
      min (q (oldTarget sem j X occ hj hA hproper hg e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hcU : GradedLe (D.cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hcU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ j) (hV : V.2 ≤ j) :
    ∃ r : target sem j X occ hj hA → ExtOrd,
      RespectsSemanticsBelow (rows sem j X occ hj hA hproper hg) (A, j) r ∧
      (∀ e : D.below (D.cell c), r (oldTarget sem j X occ hj hA hproper hg e.1) =
        min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  classical
  let _ := Fintype.ofFinite (D.below (D.cell c))
  subst j
  let F := data sem (D.grade c) X occ hj hA hproper hg
  let M := p ⟨c, GradedLe.refl _⟩
  let pp : D.below (D.cell c) → ExtOrd := fun e => min (p e) M
  have hactive : γ ≤ q (oldTarget sem (D.grade c) X occ hj hA hproper hg c) :=
    (AmbientGradeCharts.cap_reaches_iff (hag ⟨c, GradedLe.refl _⟩)).mp hpc.le
  obtain ⟨a, τ, hτ, hb, ha⟩ := exists_capped_source sem (D.grade c) X occ hj hA hproper hg
    hq (oldTarget sem (D.grade c) X occ hj hA hproper hg c)
    (oldTarget_grade sem (D.grade c) X occ hj hA hproper hg c) hγ hactive
  have hface (e : D.below (D.cell c)) : τ (a.val (occ e.1)) = min (p e) γ := by
    have he := ha (oldTarget sem (D.grade c) X occ hj hA hproper hg e.1)
    change τ (source sem (D.grade c) X occ hj hA hproper hg a
      (old sem (D.grade c) X occ hj hA e.1)) = _ at he
    rw [source_old] at he
    exact he.trans (hag e).symm
  obtain ⟨h, ρ, δ, u, _, _, ⟨B, hB, hBeq⟩, hρ, hγδ, hδM, hδvis,
      hρh, hu, hucap, huface, _, hread, hretune⟩ :=
    CanonicalOwnerBoundary.exists_completion c a.property.2 occ a.property.1 hp
      hcover hcU hOU hOV hinter hleft hright hU hV hτ hγ
      (bot_lt_iff_ne_bot.mpr hγb) hb hface hpc
  let tail := 2 * Fintype.card X + 1
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
    change AlignedCutEncoding.encode (fun e => a.val (occ e.1)) pp
      (D.grade c) tail h δ e ≤ C
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
  have hvcap (d : Cell D) : min (v d) h = min (a.val (occ d)) h := by
    dsimp only [v]
    rw [min_assoc, min_eq_right hhC]
    exact hucap d
  obtain ⟨w, hw, hwold, hwcap⟩ := CanonicalFieldPrefix.exists_boundary_section
    sem (D.grade c) X occ hj hA hproper hg hinj a hv hvt (hB.trans (Nat.le_succ _))
    (fun d => by rw [← hBeq]; exact (hvcap d).symm)
  have hwcap' (d) : min (w d) h =
      min (source sem (D.grade c) X occ hj hA hproper hg a d) h := by
    rw [hBeq]; exact hwcap d
  apply RetunedCutDecoding.decode_lift
    (fun d => source sem (D.grade c) X occ hj hA hproper hg a d.1)
    pp (fun e => oldTarget sem (D.grade c) X occ hj hA hproper hg e.1)
    ((F.profile_respects (controller sem (D.grade c) X occ hj hA a)).toBelow _)
    (hw.toBelow _) hq (fun d => F.max_grade d.1) hρ hδvis hγb hγδ hroom hρh.ge
    (fun d => hwcap' d.1)
  · intro d
    exact (hretune _ (source_short sem (D.grade c) X occ hj hA hproper hg a d.1)).trans
      ((min_eq_left (hb _)).trans (ha d))
  · intro e
    change min (pp e) δ = min (ρ (source sem (D.grade c) X occ hj hA hproper hg a
      (old sem (D.grade c) X occ hj hA e.1))) δ
    rw [source_old]
    dsimp only [pp]
    rw [min_assoc, min_eq_right hδM]
    exact hread e
  · intro e
    have hs : ((fun d => source sem (D.grade c) X occ hj hA hproper hg a d.1) ∘
        fun e : D.below (D.cell c) => oldTarget sem (D.grade c) X occ hj hA hproper hg e.1) =
        fun e => a.val (occ e.1) := by
      funext e
      exact source_old sem (D.grade c) X occ hj hA hproper hg a e.1
    rw [hs]
    change w (old sem (D.grade c) X occ hj hA e.1) = _
    rw [hwold, show v e.1 = u e.1 from min_eq_left (hfC e), huface]

end
end VaughtConjecture.Knight.CanonicalFieldOwnerLift
