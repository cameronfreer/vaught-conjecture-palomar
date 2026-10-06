/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepDecode
public import VaughtConjecture.Knight.LowOnlyPaddedStepCharts

/-! # Constructed higher private owner-capped repair

The actual chart supplies lawful source-cut factorization. The private fibre
and supported decoder construct the replacement and every external-cap receipt.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedStepPrivateRepair
open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse
open LowOnlyPaddedContract LowOnlyPaddedStepRows LowOnlyOrderedLadder
open LowOnlyPaddedStepDecode LowOnlyPaddedStepCharts SharpWitnessComposition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

theorem private_grade (d : I.right.scheme.below (effC n (k + 1))) :
    (carrier P hnext).grade (privateAt P hnext d).1 =
      I.right.scheme.grade d.1 := by
  exact (congrArg Prod.snd (original_index P hnext
    (I.rightFace.map d.1))).trans (congrArg Prod.snd (I.rightFace.index d.1))

/-- A supplied original owner identifies the actual private lower domain.
The final lifting theorem chooses a maximal such owner from the prescription. -/
theorem owner_capped
    (c : I.right.scheme.below (effC n (k + 1)))
    (hc : I.right.scheme.cell c.1 = effC n (k + 1)) (hg : I.right.scheme.grade c.1 = (k + 1))
    {p : I.right.scheme.below (effC n (k + 1)) → ExtOrd}
    {q : (carrier P hnext).below (A, (k + 1)) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (effC n (k + 1)) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ) (hpos : ⊥ < γ) (hactive : γ < p c)
    (hag : ∀ d, min (q (privateAt P hnext d)) γ = min (p d) γ) :
    ∃ u, RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) u ∧
      (∀ d, u (privateAt P hnext d) = min (p d) (p c)) ∧
      (∀ d, min (u d) γ = min (q d) γ) ∧ (∀ d, u d ≤ p c) := by
  classical
  obtain ⟨a, σ, H, hσ, hmax, hread⟩ := LowOnlyPaddedStepCharts.exists_chart P hk hnext hq
  have hreach : γ ≤ H := by
    have he := hag c
    rw [min_eq_right hactive.le] at he
    exact (he.ge.trans (min_le_left _ _)).trans
      (hmax _ ((private_grade P hnext c).trans hg))
  have hchart (d) : min (σ (source P hk hnext a d.1)) γ = min (q d) γ := by
    rw [hread, min_assoc, min_eq_right hreach]
  obtain ⟨S, hS, he⟩ := a.property.2
  have hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) (k + 1) :=
    he.symm ▸ a.property.1
  have ha : (⟨S.profile, hcanon, S, hS, rfl⟩ : F.Anchor (k + 1)) = a := Subtype.ext he
  have hprivate (d : I.right.scheme.below (effC n (k + 1))) :
      source P hk hnext a (privateAt P hnext d).1 = S.lowerC (k + 1) d := by
    change source P hk hnext a
      (original P hnext (I.rightFace.map d.1)) = _
    rw [source_original]
    change a.val (LowOnlyOrderedLadder.field I (I.rightFace.map d.1)) = S.v d.1
    rw [← he]
    exact LowOnlyOrderedLadder.field_private I F hroot
      (LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega) hS) d.1
  let toEff := CellScheme.below.mono (D := I.right.scheme)
    (show GradedLe (I.right.scheme.cell c.1) (effC n (k + 1)) from by
      rw [hc]; exact GradedLe.refl _)
  let fromEff := CellScheme.below.mono (D := I.right.scheme)
    (show GradedLe (effC n (k + 1)) (I.right.scheme.cell c.1) from by
      rw [hc]; exact GradedLe.refl _)
  let s := S.lowerC (k + 1) ∘ toEff
  let p' := p ∘ toEff
  have hs' : RespectsSemanticsBelow I.right.rows (I.right.scheme.cell c.1) s := hS.lawfulC.mono _
  have hp' : RespectsSemanticsBelow I.right.rows (I.right.scheme.cell c.1) p' := hp.mono _
  obtain ⟨δ, hδ, hδpos, _, _, ⟨fac⟩⟩ := PrivateRowFactorization.exists_factorization c.1
    (Fintype.card (Field I.left I.right)) hs' hp'
    (fun d => by
      rw [hg]
      exact CanonicalPairedProfiles.inventory_coded _ _ hcanon (.inr (.inl d.1)))
    (fun d => by
      rw [hg]
      exact CanonicalPairedProfiles.inventory_short _ _ hcanon (.inr (.inl d.1)))
    (by simpa only [hg] using hσ) (by simpa only [hg] using hγ) hpos hactive (fun d => by
      change min (σ (S.lowerC (k + 1) (toEff d))) γ = min (p (toEff d)) γ
      rw [← hprivate]
      exact (hchart _).trans (hag _))
  rw [hg] at hδ
  rcases Finset.mem_insert.mp hδ with hz | hd
  · exact False.elim (not_lt_of_ge (le_of_eq hz) hδpos)
  obtain ⟨b, hb, hbδ⟩ := Finset.mem_image.mp hd
  change CanonicalPairedInverse.grid (k + 1) b = δ at hbδ
  subst δ
  have hb' : b ≤ 2 * Fintype.card (Field I.left I.right) + 1 := by
    have := Finset.mem_range.mp hb
    omega
  let v := fac.source ∘ fromEff
  have hv : RespectsSemanticsBelow I.right.rows (effC n (k + 1)) v := fac.lawful.mono _
  obtain ⟨w, hw, hwread, hwcap⟩ := private_source_repair P hk hnext hS hcanon hb' hv
    (fun d => fac.prefix_eq (fromEff d))
  have hcap (d) : min (fac.outgoing (w d)) γ = min (q d) γ := by
    have hpre := hwcap d
    rw [ha] at hpre
    have hs : Short (I.right.scheme.grade c.1) (source P hk hnext a d.1) := by
      simpa only [hg] using source_short P hk hnext a d.1
    exact (AmbientGradeCharts.map_cap_agreement fac.witness.mono hpre fac.reaches).trans
      ((fac.caps _ hs).trans (hchart d))
  have hν : Witness (gTop (k + 1)) fac.outgoing := by simpa only [hg] using fac.witness
  refine ⟨fun d => fac.outgoing (w d),
    map_respects_of_positive_cap_agreement hw hq (fun d => d.2.2)
      (boundedMap_of_witness hν) (ne_of_gt hpos) hcap, ?_, hcap, fun _ => fac.bounded _⟩
  intro d
  exact (congrArg fac.outgoing (hwread d)).trans (fac.readback (fromEff d))


end
end VaughtConjecture.Knight.LowOnlyPaddedStepPrivateRepair
