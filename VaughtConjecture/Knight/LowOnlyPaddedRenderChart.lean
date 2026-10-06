/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedRestriction

/-! # Native source charts through later selected LOW renderings

Later selected renderings need not restrict to independently selected earlier
renderings. They do restrict to a numerical image of one native source. The
composite map is proved bounded through that native grade; it is not asserted
to be a faithful witness on long rows. All complete fields and the reserved
ceiling are read through the same map.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedRenderChart
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedRestriction
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

/-- The actual native source on the seed or a constructed successor. -/
def nativeSource : (t : ℕ) → (ht : t + 2 ≤ A.card) → F.Anchor (t + 2) →
    Cell (build I F hroot hA hB hC t ht).carrier → ExtOrd
  | 0, _, a => LowOnlyPaddedSuccessor.source I F hroot hA hB hC a
  | t + 1, ht, a => LowOnlyPaddedStepRows.source
      (build I F hroot hA hB hC t (by omega)) (by omega) ht a

/-- At its own height, the renderer is the decoder of one admitted source. -/
theorem native_chart (t : ℕ) (ht : t + 2 ≤ A.card) {j : ℕ} (hj : t + 2 ≤ j)
    (S : State I.left I.right) (hS : F.Admissible j S) (hp : ∀ f, S.profile f ≠ ⊤)
    {G : Finset ExtOrd} {H : ExtOrd} (hG : ∀ z ∈ G, SelfVis (t + 2) z)
    (hH : SelfVis (t + 2) H) (hb : ∀ f, S.profile f ≤ H) :
    ∃ a : F.Anchor (t + 2), ∃ σ : ExtOrd → ExtOrd,
      BoundedMap (t + 2) σ ∧
      (∀ f, σ (a.val f) = S.profile f) ∧
      σ (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right)) = H ∧
      ∀ d, (build I F hroot hA hB hC t ht).render hj S hS hp G H d =
        σ (nativeSource I F hroot hA hB hC t ht a d) := by
  let a := LowOnlyRecursiveCoverage.normalizedAnchor F (by omega) hj hS hp
  let σ := PairedSlotDecoder.decode (t + 2) (PairedSlotEncoding.values S.profile) G H
  refine ⟨a, σ, boundedMap_of_witness (PairedSlotDecoder.decode_witness hG hH), ?_,
    decode_reserved_ceiling hH hb, ?_⟩
  · intro f
    have ha := LowOnlyRecursiveCoverage.normalizedAnchor_fields F (by omega) hj hS hp
    change σ (F.fields (t + 2) a f) = _
    rw [show F.fields (t + 2) a = PairedSlotEncoding.normalize (t + 2) S.profile from ha]
    exact PairedSlotDecoder.decode_normalize hG hH hp f
  · intro d
    cases t <;> rfl

/-- One native source chart survives any number of later rendering steps.
The field receipts include future fields, not only current physical reads. -/
theorem later_chart (t : ℕ) (ht : t + 2 ≤ A.card) (r : ℕ)
    (hr : t + r + 2 ≤ A.card) {j : ℕ} (hj : t + r + 2 ≤ j)
    (S : State I.left I.right) (hS : F.Admissible j S) (hp : ∀ f, S.profile f ≠ ⊤)
    {G : Finset ExtOrd} {H : ExtOrd} (hG : ∀ z ∈ G, SelfVis (t + r + 2) z)
    (hH : SelfVis (t + r + 2) H) (hb : ∀ f, S.profile f ≤ H) :
    ∃ a : F.Anchor (t + 2), ∃ σ : ExtOrd → ExtOrd,
      BoundedMap (t + 2) σ ∧
      (∀ f, σ (a.val f) = S.profile f) ∧
      σ (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right)) = H ∧
      ∀ d : (build I F hroot hA hB hC t ht).carrier.below (A, t + 2),
        (build I F hroot hA hB hC (t + r) hr).render hj S hS hp G H
          (belowEquiv I F hroot hA hB hC t ht (A, t + 2) le_rfl r hr d).1 =
            σ (nativeSource I F hroot hA hB hC t ht a d.1) := by
  induction r generalizing j S G H with
  | zero =>
    obtain ⟨a, σ, hσ, hf, hc, hd⟩ := native_chart I F hroot hA hB hC t ht hj S hS hp hG hH hb
    exact ⟨a, σ, hσ, hf, hc, fun d => hd d.1⟩
  | succ r ih =>
    let P := build I F hroot hA hB hC (t + r) (by omega)
    let a₁ := LowOnlyPaddedStepRendering.normalized hj S hS hp
    let T := state F a₁
    have hT := state_admissible F a₁
    have hpT := state_proper F a₁
    have hG₁ : ∀ z ∈ LowOnlyPaddedStepRows.grid P, SelfVis (t + r + 2) z :=
      fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ _)
    have hH₁ : SelfVis (t + r + 2) (LowOnlyPaddedStepRows.ceiling P) :=
      (sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ _)
    have hb₁ : ∀ f, T.profile f ≤ LowOnlyPaddedStepRows.ceiling P := by
      intro f
      rw [show T.profile = F.fields (t + r + 2 + 1) a₁ from state_profile F a₁]
      exact LowOnlyRecursiveCharts.anchor_bound F a₁ f
    obtain ⟨a, τ, hτ, hf, hc, hd⟩ := ih (by omega) (Nat.le_succ _) T hT hpT hG₁ hH₁ hb₁
    let δ := PairedSlotDecoder.decode (t + r + 2 + 1)
      (PairedSlotEncoding.values S.profile) G H
    have hδ := PairedSlotDecoder.decode_witness
      (S := PairedSlotEncoding.values S.profile) hG hH
    have hδb : BoundedMap (t + r + 2 + 1) δ := boundedMap_of_witness hδ
    have hcomp : BoundedMap (t + 2) (δ ∘ τ) :=
      ⟨by simp only [Function.comp_apply, hτ.bot, hδb.bot], hδb.mono.comp hτ.mono,
        fun x k i hk hi => by
          simp only [Function.comp_apply]
          rw [hτ.comm x k i hk hi, hδb.comm _ k i (by omega) hi]⟩
    have hfields (f : Field I.left I.right) : δ (T.profile f) = S.profile f := by
      change δ ((state F a₁).profile f) = _
      rw [state_profile, LowOnlyPaddedStepRendering.normalized_fields]
      exact PairedSlotDecoder.decode_normalize hG hH hp f
    refine ⟨a, δ ∘ τ, hcomp, fun f => (congrArg δ (hf f)).trans (hfields f),
      (congrArg δ hc).trans (decode_reserved_ceiling hH hb), ?_⟩
    intro d
    change δ (LowOnlyPaddedStepRows.source P (by omega) (by omega) a₁
      (LowOnlyPaddedStepRows.old P (by omega)
        (belowEquiv I F hroot hA hB hC t ht (A, t + 2) le_rfl r (by omega) d).1)) = _
    rw [LowOnlyPaddedStepRows.source_old]
    exact congrArg δ (hd d)

/-- The same chart for a later raw source, before its final decoder. -/
theorem source_chart (t : ℕ) (ht : t + 2 ≤ A.card) (r : ℕ)
    (hr : t + r + 2 ≤ A.card) (b : F.Anchor (t + r + 2)) :
    ∃ a : F.Anchor (t + 2), ∃ σ : ExtOrd → ExtOrd,
      BoundedMap (t + 2) σ ∧
      (∀ f, σ (a.val f) = b.val f) ∧
      σ (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right)) =
        CanonicalFieldLayer.ceiling (t + r + 2) (Field I.left I.right) ∧
      ∀ d : (build I F hroot hA hB hC t ht).carrier.below (A, t + 2),
        nativeSource I F hroot hA hB hC (t + r) hr b
          (belowEquiv I F hroot hA hB hC t ht (A, t + 2) le_rfl r hr d).1 =
            σ (nativeSource I F hroot hA hB hC t ht a d.1) := by
  cases r with
  | zero => exact ⟨b, id, ⟨rfl, monotone_id, fun _ _ _ _ _ => rfl⟩,
      fun _ => rfl, rfl, fun _ => rfl⟩
  | succ r =>
    let P := build I F hroot hA hB hC (t + r) (by omega)
    have hG : ∀ z ∈ LowOnlyPaddedStepRows.grid P, SelfVis (t + r + 2) z :=
      fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ _)
    have hH : SelfVis (t + r + 2) (LowOnlyPaddedStepRows.ceiling P) :=
      (sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ _)
    have hb : ∀ f, (state F b).profile f ≤ LowOnlyPaddedStepRows.ceiling P := by
      intro f
      rw [state_profile]
      exact LowOnlyRecursiveCharts.anchor_bound F b f
    obtain ⟨a, σ, hσ, hf, hc, hd⟩ := later_chart I F hroot hA hB hC t ht r
      (by omega) (Nat.le_succ _) (state F b) (state_admissible F b)
      (state_proper F b) hG hH hb
    refine ⟨a, σ, hσ, ?_, hc, ?_⟩
    · intro f
      exact (hf f).trans (congrFun (state_profile F b) f)
    · intro d
      change LowOnlyPaddedStepRows.source P (by omega) (by omega) b
        (LowOnlyPaddedStepRows.old P (by omega)
          (belowEquiv I F hroot hA hB hC t ht (A, t + 2) le_rfl r (by omega) d).1) = _
      rw [LowOnlyPaddedStepRows.source_old]
      exact hd d

end
end VaughtConjecture.Knight.LowOnlyPaddedRenderChart
