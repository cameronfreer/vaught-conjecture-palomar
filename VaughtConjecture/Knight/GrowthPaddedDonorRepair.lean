/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedCharts

/-! # Constructed owner-capped donor repair on the installed growth successor

The three cuts remain distinct: the original external cap, the constructed
native grid cut, and the prescribed owner value. No alignment or replacement
source is supplied by the caller. The argument reuses
`LowOnlyPaddedDonorRepair` with the pre-activation growth donor repair producer.
No symmetry of the admission predicate is used.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedDonorRepair
open Transform Value ExtOrd CappedDonor Growth CanonicalPairedInverse
open GrowthPaddedSuccessor GrowthPaddedDecode GrowthPaddedCharts
open SharpWitnessComposition
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem donor_grade (d : I.left.scheme.below (Finset.univ, 2)) :
    (carrier I X T hA hB hC).grade (donorAt I X T hA hB hC d).1 =
      I.left.scheme.grade d.1 := by
  exact (congrArg Prod.snd (original_index I X T hA hB hC
    (I.leftFace.map d.1))).trans (congrArg Prod.snd (I.leftFace.index d.1))

/-- A supplied original owner identifies the actual donor lower domain.
The final lifting theorem chooses a maximal such owner from the prescription. -/
theorem owner_capped (hN : 2 < X.req.N)
    (c : I.left.scheme.below (Finset.univ, 2))
    (hc : I.left.scheme.cell c.1 = (Finset.univ, 2)) (hg : I.left.scheme.grade c.1 = 2)
    {p : I.left.scheme.below (Finset.univ, 2) → ExtOrd}
    {q : (carrier I X T hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) p)
    (hq : RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ) (hpos : ⊥ < γ) (hactive : γ < p c)
    (hag : ∀ d, min (q (donorAt I X T hA hB hC d)) γ = min (p d) γ) :
    ∃ u, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) u ∧
      (∀ d, u (donorAt I X T hA hB hC d) = min (p d) (p c)) ∧
      (∀ d, min (u d) γ = min (q d) γ) ∧ (∀ d, u d ≤ p c) := by
  classical
  obtain ⟨a, σ, H, hσ, hmax, hread⟩ := GrowthPaddedCharts.exists_chart I X T hA hB hC hq
  have hreach : γ ≤ H := by
    have he := hag c
    rw [min_eq_right hactive.le] at he
    exact (he.ge.trans (min_le_left _ _)).trans
      (hmax _ ((donor_grade I X T hA hB hC c).trans hg))
  have hchart (d) : min (σ (source I X T hA hB hC a d.1)) γ = min (q d) γ := by
    rw [hread, min_assoc, min_eq_right hreach]
  obtain ⟨S, hS, he⟩ := a.property.2
  have hcanon : S.profile ∈
      CanonicalPairedProfiles.inventory (Field I.right.scheme I.left.scheme) 2 :=
    he.symm ▸ a.property.1
  have ha : (⟨S.profile, hcanon, S, hS, rfl⟩ : Catalogue X 2) = a := Subtype.ext he
  have hdonor (d : I.left.scheme.below (Finset.univ, 2)) :
      source I X T hA hB hC a (donorAt I X T hA hB hC d).1 = S.donorValues d.1 := by
    change source I X T hA hB hC a
      (original I X T hA hB hC (I.leftFace.map d.1)) = _
    rw [original_readback]
    change a.val (GrowthOrderedBase.field I (I.leftFace.map d.1)) = S.donorValues d.1
    rw [← he]
    exact GrowthOrderedBase.field_donor I S d.1
  let toEff := CellScheme.below.mono (D := I.left.scheme)
    (show GradedLe (I.left.scheme.cell c.1) (Finset.univ, 2) from by
      rw [hc]; exact GradedLe.refl _)
  let fromEff := CellScheme.below.mono (D := I.left.scheme)
    (show GradedLe (Finset.univ, 2) (I.left.scheme.cell c.1) from by
      rw [hc]; exact GradedLe.refl _)
  let s := (fun d : I.left.scheme.below (Finset.univ, 2) => S.donorValues d.1) ∘ toEff
  let p' := p ∘ toEff
  have hs' : RespectsSemanticsBelow I.left.rows (I.left.scheme.cell c.1) s :=
    hS.donor_lawful.mono _
  have hp' : RespectsSemanticsBelow I.left.rows (I.left.scheme.cell c.1) p' := hp.mono _
  obtain ⟨δ, hδ, hδpos, _, _, ⟨fac⟩⟩ := PrivateRowFactorization.exists_factorization c.1
    (Fintype.card (Field I.right.scheme I.left.scheme)) hs' hp'
    (fun d => by
      rw [hg]
      exact CanonicalPairedProfiles.inventory_coded _ _ hcanon (.inr d.1))
    (fun d => by
      rw [hg]
      exact CanonicalPairedProfiles.inventory_short _ _ hcanon (.inr d.1))
    (by simpa only [hg] using hσ) (by simpa only [hg] using hγ) hpos hactive (fun d => by
      change min (σ (S.donorValues (toEff d).1)) γ = min (p (toEff d)) γ
      rw [← hdonor (toEff d)]
      exact (hchart _).trans (hag _))
  rw [hg] at hδ
  rcases Finset.mem_insert.mp hδ with hz | hd
  · exact False.elim (not_lt_of_ge (le_of_eq hz) hδpos)
  obtain ⟨b, hb, hbδ⟩ := Finset.mem_image.mp hd
  change grid 2 b = δ at hbδ
  subst δ
  have hb' : b ≤ 2 * Fintype.card (Field I.right.scheme I.left.scheme) + 1 := by
    have := Finset.mem_range.mp hb
    omega
  let v := fac.source ∘ fromEff
  have hv : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) v := fac.lawful.mono _
  obtain ⟨w, hw, hwread, hwcap⟩ := donor_source_repair I X T hA hB hC hN hS hcanon hb' hv
    (fun d => fac.prefix_eq (fromEff d))
  have hcap (d) : min (fac.outgoing (w d)) γ = min (q d) γ := by
    have hpre := hwcap d
    rw [ha] at hpre
    have hs : Short (I.left.scheme.grade c.1) (source I X T hA hB hC a d.1) := by
      simpa only [hg] using source_short I X T hA hB hC a d.1
    exact (AmbientGradeCharts.map_cap_agreement fac.witness.mono hpre fac.reaches).trans
      ((fac.caps _ hs).trans (hchart d))
  have hν : Witness (gTop 2) fac.outgoing := by simpa only [hg] using fac.witness
  refine ⟨fun d => fac.outgoing (w d),
    map_respects_of_positive_cap_agreement hw hq (fun d => d.2.2)
      (boundedMap_of_witness hν) (ne_of_gt hpos) hcap, ?_, hcap, fun _ => fac.bounded _⟩
  intro d
  exact (congrArg fac.outgoing (hwread d)).trans (fac.readback (fromEff d))

end
end VaughtConjecture.Knight.GrowthPaddedDonorRepair
