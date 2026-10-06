/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalProperOwnerLift
public import VaughtConjecture.Knight.CanonicalProperOwnerLower

/-! # Independent section supply through the three canonical layers

Full-controller rows are short at their own grades; proper long rows are
retained literally. Decoding can therefore reconstruct an arbitrary lawful
old boundary, including top, without any positive-cap lifting assumption.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalProperOwnerSections
open Transform Value ExtOrd CanonicalProperOwnerLayer CanonicalProperOwnerLift
open SharpWitnessComposition CoatomBoundaryExtension PairedSlotEncoding
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (k : ℕ) (h2k : 2 < k) (hkA : k ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ k)

theorem lower_full_short (c : Cell (lowerScheme sem k h2k hkA))
    (hc : (lowerScheme sem k h2k hkA).scope c = A)
    (d : (lowerScheme sem k h2k hkA).below ((lowerScheme sem k h2k hkA).cell c)) :
    Short ((lowerScheme sem k h2k hkA).grade c) ((lowerSem sem k h2k hkA hp).E c d) := by
  have hc2 : (lowerScheme sem k h2k hkA).grade c ≤ 2 := by
    obtain ⟨x, rfl⟩ := (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
      (one_le k h2k hkA) (by decide) (two_le k h2k hkA)).surjective c
    change (lowerScheme sem k h2k hkA).grade (GradeCutPairCarrier.cell _ _ _ _ _ _ _ _ _ x) ≤ 2
    change ((lowerScheme sem k h2k hkA).cell
      (GradeCutPairCarrier.cell _ _ _ _ _ _ _ _ _ x)).1 = A at hc
    rw [GradeCutPairCarrier.cell_idx] at hc
    rw [CellScheme.grade, GradeCutPairCarrier.cell_idx]
    rcases x with (c | q) | q
    · exact (hp c hc).elim
    · exact (by decide : 1 ≤ 2)
    · exact le_rfl
  obtain ⟨a, rfl⟩ := GradeCutPairCarrier.exhaustive D _ _ 1 2 (by decide)
    (one_le k h2k hkA) (by decide) (two_le k h2k hkA) c hc2
  obtain ⟨e, rfl⟩ := (GradeCutPairCarrier.belowEquiv D _ _ 1 2 (by decide)
    (one_le k h2k hkA) (by decide) (two_le k h2k hkA) _ hc2).surjective d
  have he := CanonicalPairBoundary.lower_row sem 1 2 (by decide) (one_le k h2k hkA)
    (by decide) (two_le k h2k hkA) hp (by decide) a
    ⟨e.1, by simpa only [GradeCutPairCarrier.embed_index] using e.2⟩
  have hv := CanonicalMixedGradeLayers.full_source_short
    (CanonicalPairBoundary.boundaryRows sem 2) 1 (by decide) (one_le k h2k hkA)
    (GradeCutBoundary.proper D 2 hp) 2 (GradeCutBoundary.grade_bound D 2)
    (by decide) (two_le k h2k hkA) (by decide) a
    (by simpa only [CellScheme.scope, GradeCutPairCarrier.embed_index] using hc)
    ⟨e.1, by simpa only [GradeCutPairCarrier.embed_index] using e.2⟩
  rw [← he] at hv
  exact (congrArg (fun i => Short i _) (congrArg Prod.snd
    (GradeCutPairCarrier.embed_index D _ _ 1 2 (by decide) (one_le k h2k hkA)
      (by decide) (two_le k h2k hkA) a))).mpr hv

theorem full_source_short (c : Cell (scheme sem k h2k hkA))
    (hc : (scheme sem k h2k hkA).scope c = A)
    (d : (scheme sem k h2k hkA).below ((scheme sem k h2k hkA).cell c)) :
    Short ((scheme sem k h2k hkA).grade c) ((rows sem k h2k hkA hp hg).E c d) := by
  apply (data sem k h2k hkA hp hg).full_source_short
    (fun _ hh => PairedBoundarySections.grid_short k hh) _ _ c hc d
  · intro q x hx
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem k h2k hkA)
      (Profile sem k) k (positive k h2k) hkA x hx
    change Short k (lower sem k h2k hkA hp _ (old sem k h2k hkA y))
    rw [lower_old]
    exact PairedCoupledSections.supported_short
      (fun _ hh => PairedBoundarySections.grid_short k hh)
      (CanonicalFieldLayer.profile_short sem k (Cell D) id _)
      (lower_supported sem k h2k hkA hp _ y)
  · intro x hs hx e
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme sem k h2k hkA)
      (Profile sem k) k (positive k h2k) hkA x hx
    obtain ⟨z, rfl⟩ := (ownerEquiv sem k h2k hkA hp y).surjective e
    have he := SeparatedSourceLayerCarrier.base_old (lowerScheme sem k h2k hkA)
      (Profile sem k) k (positive k h2k) hkA (separated sem k h2k hkA hp)
      (lowerSem sem k h2k hkA hp) y z
    change (data sem k h2k hkA hp hg).base.E _ _ = _ at he
    rw [he]
    have hi := SourceLayerCarrier.cell_toCell (lowerScheme sem k h2k hkA)
      (Profile sem k) k (positive k h2k) hkA (.inl y)
    change Short ((scheme sem k h2k hkA).grade (old sem k h2k hkA y)) _
    rw [show (scheme sem k h2k hkA).grade (old sem k h2k hkA y) =
      (lowerScheme sem k h2k hkA).grade y from congrArg Prod.snd hi]
    exact lower_full_short sem k h2k hkA hp y ((congrArg Prod.fst hi).symm.trans hs) z

theorem proper_lawful {p : Cell D → ExtOrd} (hpr : RespectsSemantics sem p)
    {r : Cell (scheme sem k h2k hkA) → ExtOrd}
    (hread : ∀ d, r (boundary sem k h2k hkA d) = p d)
    (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) :
    RespectsSemanticsBelow (rows sem k h2k hkA hp hg) J (fun d => r d.1) := by
  let e := CanonicalProperOwnerLower.properEquiv sem k h2k hkA J hJ
  have he : (fun d : (scheme sem k h2k hkA).below J => r d.1) =
      (fun d : D.below J => p d.1) ∘ e.symm := by
    funext d
    obtain ⟨a, rfl⟩ := e.surjective d
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact hread a.1
  rw [he]
  exact (CanonicalProperOwnerLower.proper_respects_iff sem k h2k hkA hp hg J hJ _).mp
    (hpr.toBelow J)

theorem exists_proper_whole {p : Cell D → ExtOrd} (hpr : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) :
    ∃ r : CanonicalProperOwnerAmbient.target sem k h2k hkA → ExtOrd,
      RespectsSemanticsBelow (rows sem k h2k hkA hp hg) (A, k) r ∧
      ∀ d, r (oldTarget sem k h2k hkA hp hg d) = p d := by
  let F := data sem k h2k hkA hp hg
  let a := CanonicalFieldLayer.encode sem k (Cell D) id hg hpr ht
  let ν := PairedSlotDecoder.decode k (values p) ∅ ⊤
  have hν : Witness (gTop k) ν :=
    PairedSlotDecoder.decode_witness (by simp) (extVisibilityReplace_top k k)
  have hread (d : Cell D) : ν (F.profile (controller sem k h2k hkA a)
      (boundary sem k h2k hkA d)) = p d := by
    rw [show F.profile (controller sem k h2k hkA a) _ = a.val d from
      source_boundary sem k h2k hkA hp hg a d]
    exact PairedSlotDecoder.decode_normalize (by simp) (extVisibilityReplace_top k k) ht d
  have hr := F.decoded_respects (controller sem k h2k hkA a) le_rfl hν
    (fun c hc => ?_) (full_source_short sem k h2k hkA hp hg)
  · exact ⟨_, hr.toBelow _, hread⟩
  have hc' : (scheme sem k h2k hkA).cell c ≠ (A, k) := fun he => hc (congrArg Prod.fst he)
  have hnot : ¬ A ⊆ (scheme sem k h2k hkA).scope c := fun ha => hc (Finset.Subset.antisymm
    ((scheme sem k h2k hkA).isPlan.subset_of_mem ((scheme sem k h2k hkA).scope_mem_plan c)) ha)
  have hv := (F.old_respects_iff hc').mp
    (proper_lawful sem k h2k hkA hp hg hpr
      (r := fun d => ν (F.profile (controller sem k h2k hkA a) d)) hread _ hnot)
  simpa only [F.profile_old _ (SourcePrefixLayer.below_old F.max_grade hc' _)] using hv

/-- Finite outer coding handles top independently of positive-cap transport. -/
theorem exists_whole {p : Cell D → ExtOrd} (hpr : RespectsSemantics sem p) :
    ∃ r : CanonicalProperOwnerAmbient.target sem k h2k hkA → ExtOrd,
      RespectsSemanticsBelow (rows sem k h2k hkA hp hg) (A, k) r ∧
      ∀ d, r (oldTarget sem k h2k hkA hp hg d) = p d := by
  classical
  let all (d : Cell D) : D.below (A, k) :=
    ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hg d⟩
  obtain ⟨S, u, hu, _, hcode, hdecode⟩ :=
    (hpr.toBelow (A, k)).exists_coded_representative (fun d => hg d.1)
      (le_refl (Nat.card (D.below (A, k))))
  have ht (d : Cell D) : u (all d) ≠ ⊤ := by
    rcases mem_codedAlphabet_iff.mp (hcode (all d)) with hb | ⟨b, i, _, _, he⟩
    · exact hb.trans_ne bot_ne_top
    · exact he.trans_ne (ofOrd_ne_top _)
  obtain ⟨r, hr, hread⟩ := exists_proper_whole sem k h2k hkA hp hg
    (hu.toRespects (fun d => (all d).2)) ht
  exact ⟨fun d => canonicalDecoder S k (r d), hr.decoded S (fun d => d.2.2),
    fun d => (congrArg (canonicalDecoder S k) (hread d)).trans (hdecode (all d))⟩

theorem exists_section {I U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hIU : GradedLe I U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hIU) (hright : CappedLift sem hOV)
    {p : D.below I → ExtOrd} (hpr : RespectsSemanticsBelow sem I p) :
    ∃ r : CanonicalProperOwnerAmbient.target sem k h2k hkA → ExtOrd,
      RespectsSemanticsBelow (rows sem k h2k hkA hp hg) (A, k) r ∧
      ∀ d : D.below I, r (oldTarget sem k h2k hkA hp hg d.1) = p d := by
  obtain ⟨b, hread⟩ := section_left hIU hOU hOV hinter hleft hright p hpr
  obtain ⟨r, hr, hold⟩ := exists_whole sem k h2k hkA hp hg (b.whole_respects hcover)
  exact ⟨r, hr, fun d => (hold d.1).trans (hread d)⟩

end
end VaughtConjecture.Knight.CanonicalProperOwnerSections
