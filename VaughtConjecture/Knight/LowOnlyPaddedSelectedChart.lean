/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedRenderChart
public import VaughtConjecture.Knight.LowOnlyPaddedStage

/-! # A whole LOW display with a simultaneous native chart

Supported terminal decoding constructs the whole display. Descent through
the actual later rendering steps retains a single numerical native chart,
including all future fields and its ceiling. No exact cross-grade identity
of selected renderings and no lifting hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedSelectedChart
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedInstallation
open LowOnlyPaddedEndpoints
open LowOnlyPaddedRestriction LowOnlyPaddedRenderChart SharpWitnessComposition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem native_source_original (t : ℕ) (ht : t + 2 ≤ A.card)
    (a : F.Anchor (t + 2)) (d : Cell I.boundary) :
    nativeSource I F hroot hA hB hC t ht a (original I F hroot hA hB hC t ht d) =
      a.val (field I d) := by
  cases t with
  | zero => exact LowOnlyPaddedSuccessor.original_readback I F hroot hA hB hC a d
  | succ t => exact LowOnlyPaddedStepDecode.source_original _ _ _ a d

theorem native_decoded_lawful (t : ℕ) (ht : t + 2 ≤ A.card)
    (a : F.Anchor (t + 2)) {δ : ExtOrd → ExtOrd} (hδ : Witness (gTop (t + 2)) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow I.rows (A, t + 2)
      (fun d => δ (a.val (field I d.1)))) :
    RespectsSemanticsBelow (build I F hroot hA hB hC t ht).rows (A, t + 2)
      (fun d => δ (nativeSource I F hroot hA hB hC t ht a d.1)) := by
  cases t with
  | zero => exact LowOnlyPaddedSupply.decoded_lawful I F hroot hA hB hC a hδ hreflect horiginal
  | succ t => exact LowOnlyPaddedStepSupply.decoded_lawful _ _ _ a hδ hreflect horiginal

/-- Every native source has the same complete padded-base rank table,
with a constructed admitted rank anchor. -/
theorem native_source_base (t : ℕ) (ht : t + 2 ≤ A.card) (a : F.Anchor (t + 2)) :
    ∃ b : F.Anchor 1,
      RelativeLadderLayer.ranks (F.fields 1) b = LadderScalarRendering.fieldRank a.val ∧
      ∀ d : Cell (base I F hroot hA hB hC),
        nativeSource I F hroot hA hB hC t ht a
          ((build I F hroot hA hB hC t ht).baseMap d) =
        RelativeLadderLayer.renderWith I.boundary (by omega) (field I) (F.fields 1)
          b a.val (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right)) d := by
  cases t with
  | zero =>
    refine ⟨LowOnlyPaddedSuccessor.baseAnchor F a,
      funext (LowOnlyPaddedSuccessor.baseAnchor_ranks F a), ?_⟩
    intro d
    exact (LowOnlyPaddedSuccessor.input I F hroot hA hB hC).source_old a d
  | succ t =>
    let P := build I F hroot hA hB hC t (by omega)
    exact ⟨LowOnlyPaddedStepSupply.birth P a,
      funext (LowOnlyPaddedStepSupply.birth_ranks P a),
      LowOnlyPaddedStepSupply.source_base P (by omega) ht a⟩

/-- The native chart and the whole supported display are produced together.
One top complete field makes the chart's reserved ceiling top. -/
theorem exists_whole_chart (t : ℕ) (ht : t + 2 ≤ A.card) (r : ℕ)
    (hr : t + r + 2 ≤ A.card) (hfull : t + r + 2 = A.card)
    {S : State I.left I.right} (hS : F.Admissible (t + r + 2) S)
    (htop : ∃ f, S.profile f = ⊤) :
    ∃ w : Cell (build I F hroot hA hB hC (t + r) hr).carrier → ExtOrd,
      RespectsSemantics (build I F hroot hA hB hC (t + r) hr).rows w ∧
      (∀ d, w (original I F hroot hA hB hC (t + r) hr d) = S.profile (field I d)) ∧
      (∀ d, OrbitPrefixSupport.Supported (t + r + 2) ({⊤} : Set ExtOrd) S.profile (w d)) ∧
      ∃ a : F.Anchor (t + 2), ∃ σ : ExtOrd → ExtOrd,
        BoundedMap (t + 2) σ ∧
        (∀ f, σ (a.val f) = S.profile f) ∧
        σ (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right)) = ⊤ ∧
        ∀ d : (build I F hroot hA hB hC t ht).carrier.below (A, t + 2),
          w (belowEquiv I F hroot hA hB hC t ht (A, t + 2) le_rfl r hr d).1 =
            σ (nativeSource I F hroot hA hB hC t ht a d.1) := by
  obtain ⟨Q, hQ, hcanon, δ, hδ, hread, hreflect, hsupp⟩ :=
    F.exists_supported_decoder (by omega) hS
  let b : F.Anchor (t + r + 2) := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  have horiginal : RespectsSemanticsBelow I.rows (A, t + r + 2)
      (fun d => δ (b.val (field I d.1))) := by
    simpa only [b, hread] using
      LowOnlyOrderedSources.boundary_lawful_at I F hroot (t + r + 2) S hS
  have hw := native_decoded_lawful I F hroot hA hB hC (t + r) hr b hδ hreflect horiginal
  have hall (d : Cell (build I F hroot hA hB hC (t + r) hr).carrier) :
      GradedLe ((build I F hroot hA hB hC (t + r) hr).carrier.cell d) (A, t + r + 2) := by
    let D := (build I F hroot hA hB hC (t + r) hr).carrier
    have hs := D.isPlan.subset_of_mem (D.scope_mem_plan d)
    exact ⟨hs, ((D.grade_le_card_scope d).trans (Finset.card_le_card hs)).trans_eq hfull.symm⟩
  obtain ⟨a, τ, hτ, hf, hc, hd⟩ := source_chart I F hroot hA hB hC t ht r hr b
  have hcomp : BoundedMap (t + 2) (δ ∘ τ) :=
    ⟨by simp only [Function.comp_apply, hτ.bot, hδ.bot], hδ.mono.comp hτ.mono,
      fun x k i hk hi => by
        simp only [Function.comp_apply]
        rw [hτ.comm x k i hk hi,
          (boundedMap_of_witness hδ).comm _ k i (by omega) hi]⟩
  have hceiling : δ (CanonicalFieldLayer.ceiling (t + r + 2) (Field I.left I.right)) = ⊤ := by
    obtain ⟨f, hf⟩ := htop
    apply top_le_iff.mp
    exact (hf.symm.trans (hread f).symm).le.trans
      (hδ.mono (LowOnlyRecursiveCharts.anchor_bound F b f))
  refine ⟨fun d => δ (nativeSource I F hroot hA hB hC (t + r) hr b d),
    hw.toRespects hall, ?_, fun d => hsupp _, a, δ ∘ τ, hcomp, ?_,
    (congrArg δ hc).trans hceiling, ?_⟩
  · intro d
    exact (congrArg δ (native_source_original I F hroot hA hB hC (t + r) hr b d)).trans
      (hread _)
  · intro f
    exact (congrArg δ (hf f)).trans (hread f)
  · intro d
    exact congrArg δ (hd d)

end
end VaughtConjecture.Knight.LowOnlyPaddedSelectedChart
