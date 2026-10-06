/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepDecode
public import VaughtConjecture.Knight.LowOnlyPaddedStepCharts
public import VaughtConjecture.Knight.LowOnlyDonorOrderedLift

/-! # Constructed higher donor owner-capped repair

The actual chart supplies lawful source-cut factorization. The donor fibre
is used explicitly; LOW is not exchanged between faces. Supported decoding
retains every physical coordinate's external cap.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedStepDonorRepair
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

theorem donor_grade (d : I.left.scheme.below (effC n (k + 1))) :
    (carrier P hnext).grade (donorAt P hnext d).1 =
      I.left.scheme.grade d.1 := by
  exact (congrArg Prod.snd (original_index P hnext
    (I.leftFace.map d.1))).trans (congrArg Prod.snd (I.leftFace.index d.1))

/-- A supplied original owner identifies the actual donor lower domain.
The final lifting theorem chooses a maximal such owner from the prescription. -/
theorem owner_capped
    (c : I.left.scheme.below (effC n (k + 1)))
    (hc : I.left.scheme.cell c.1 = effC n (k + 1)) (hg : I.left.scheme.grade c.1 = (k + 1))
    {p : I.left.scheme.below (effC n (k + 1)) → ExtOrd}
    {q : (carrier P hnext).below (A, (k + 1)) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n (k + 1)) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ) (hpos : ⊥ < γ) (hactive : γ < p c)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ u, RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) u ∧
      (∀ d, u (donorAt P hnext d) = min (p d) (p c)) ∧
      (∀ d, min (u d) γ = min (q d) γ) ∧ (∀ d, u d ≤ p c) := by
  classical
  obtain ⟨a, σ, H, hσ, hmax, hread⟩ := LowOnlyPaddedStepCharts.exists_chart P hk hnext hq
  have hreach : γ ≤ H := by
    have he := hag c
    rw [min_eq_right hactive.le] at he
    exact (he.ge.trans (min_le_left _ _)).trans
      (hmax _ ((donor_grade P hnext c).trans hg))
  have hchart (d) : min (σ (source P hk hnext a d.1)) γ = min (q d) γ := by
    rw [hread, min_assoc, min_eq_right hreach]
  obtain ⟨S, hS, he⟩ := a.property.2
  have hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) (k + 1) :=
    he.symm ▸ a.property.1
  have ha : (⟨S.profile, hcanon, S, hS, rfl⟩ : F.Anchor (k + 1)) = a := Subtype.ext he
  have hdonor (d : I.left.scheme.below (effC n (k + 1))) :
      source P hk hnext a (donorAt P hnext d).1 = S.lowerP (k + 1) d := by
    change source P hk hnext a
      (original P hnext (I.leftFace.map d.1)) = _
    rw [source_original]
    change a.val (LowOnlyOrderedLadder.field I (I.leftFace.map d.1)) = S.u d.1
    rw [← he]
    exact LowOnlyOrderedLadder.field_donor I S d.1
  let toEff := CellScheme.below.mono (D := I.left.scheme)
    (show GradedLe (I.left.scheme.cell c.1) (effC n (k + 1)) from by
      rw [hc]; exact GradedLe.refl _)
  let fromEff := CellScheme.below.mono (D := I.left.scheme)
    (show GradedLe (effC n (k + 1)) (I.left.scheme.cell c.1) from by
      rw [hc]; exact GradedLe.refl _)
  let s := S.lowerP (k + 1) ∘ toEff
  let p' := p ∘ toEff
  have hs' : RespectsSemanticsBelow I.left.rows (I.left.scheme.cell c.1) s := hS.lawfulP.mono _
  have hp' : RespectsSemanticsBelow I.left.rows (I.left.scheme.cell c.1) p' := hp.mono _
  obtain ⟨δ, hδ, hδpos, _, _, ⟨fac⟩⟩ := PrivateRowFactorization.exists_factorization c.1
    (Fintype.card (Field I.left I.right)) hs' hp'
    (fun d => by
      rw [hg]
      exact CanonicalPairedProfiles.inventory_coded _ _ hcanon (.inl d.1))
    (fun d => by
      rw [hg]
      exact CanonicalPairedProfiles.inventory_short _ _ hcanon (.inl d.1))
    (by simpa only [hg] using hσ) (by simpa only [hg] using hγ) hpos hactive (fun d => by
      change min (σ (S.lowerP (k + 1) (toEff d))) γ = min (p (toEff d)) γ
      rw [← hdonor]
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
  have hv : RespectsSemanticsBelow I.left.rows (effC n (k + 1)) v := fac.lawful.mono _
  obtain ⟨w, hw, hwread, hwcap⟩ := donor_source_repair P hk hnext hS hcanon hb' hv
    (fun d => fac.prefix_eq (fromEff d))
  have hcap (d) : min (fac.outgoing (w d)) γ = min (q d) γ := by
    have hpre := hwcap d
    rw [ha] at hpre
    have hs : Short (I.left.scheme.grade c.1) (source P hk hnext a d.1) := by
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
end VaughtConjecture.Knight.LowOnlyPaddedStepDonorRepair
