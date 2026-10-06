/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthBaseSupply
public import VaughtConjecture.Knight.RecursiveRungRendering

/-! # Lawful growth boundary sources at every present cutoff

Extend the grade-one boundary argument to the whole currently present original
boundary. Only the proof's temporary zero tails are discarded: all future
fields remain in the actual catalogue vector. Normalization is used downward,
never to admit a source at a higher cutoff.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthHigherSources
open Transform Value ExtOrd Growth GrowthOrderedBase
noncomputable section

section Catalogue
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

instance (j : ℕ) : Fintype (Catalogue X j) := Fintype.ofFinite _

abbrev fields (j : ℕ) (a : Catalogue X j) : Field DA DQ → ExtOrd := a.val

theorem anchor_proper {j : ℕ} (a : Catalogue X j) (f : Field DA DQ) :
    fields X j a f ≠ ⊤ := a.property.1.2 f

theorem anchor_bound {j : ℕ} (a : Catalogue X j) (f : Field DA DQ) :
    fields X j a f ≤ CanonicalFieldLayer.ceiling j (Field DA DQ) := by
  apply (CanonicalPairedProfiles.inventory_bound _ _ a.property.1 f).trans
  exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr; omega) le_rfl)

theorem anchor_short {j : ℕ} (a : Catalogue X j) (f : Field DA DQ) :
    SharpWitnessComposition.Short j (fields X j a f) :=
  CanonicalPairedProfiles.inventory_short _ _ a.property.1 f

theorem anchor_visible_one {j : ℕ} (a : Catalogue X j) (f : Field DA DQ) :
    SelfVis 1 (fields X j a f) := by
  obtain ⟨S, hs, he⟩ := a.property.2
  change SelfVis 1 (a.val f)
  rw [← he]
  exact hs.visible f

/-- The state is admitted at its own cutoff. No upward admission is used. -/
def state {j : ℕ} (a : Catalogue X j) : State DA DQ := State.ofProfile a.val

theorem state_eq_chosen {j : ℕ} (a : Catalogue X j) :
    state X a = a.property.2.choose := by
  apply State.profile_injective
  exact (State.profile_ofProfile a.val).trans a.property.2.choose_spec.2.symm

theorem state_admitted {j : ℕ} (a : Catalogue X j) :
    Admitted X j (state X a) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  have hs : state X a = S := State.profile_injective
    ((State.profile_ofProfile a.val).trans he.symm)
  exact hs.symm ▸ hS

theorem state_profile {j : ℕ} (a : Catalogue X j) :
    (state X a).profile = fields X j a := State.profile_ofProfile a.val

theorem state_proper {j : ℕ} (a : Catalogue X j) (f : Field DA DQ) :
    (state X a).profile f ≠ ⊤ := by
  rw [state_profile]
  exact anchor_proper X a f

def normalized {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    (S : State DA DQ) (hs : Admitted X j S) (hp : ∀ f, S.profile f ≠ ⊤) :
    Catalogue X i := normalizedMember X hi (hs.down X hij) hp

theorem normalized_fields {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    (S : State DA DQ) (hs : Admitted X j S) (hp : ∀ f, S.profile f ≠ ⊤) :
    fields X i (normalized X hi hij S hs hp) = PairedSlotEncoding.normalize i S.profile :=
  funext (State.profile_normalize i S)

end Catalogue

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)

include T in
theorem boundary_lawful_at {j : ℕ} {S : State I.right.scheme I.left.scheme} (hs : Admitted X j S) :
    RespectsSemanticsBelow I.rows (A, j) (fun d => S.profile (field I d.1)) := by
  let u := CellScheme.zeroAbove (fun d : I.left.scheme.below (Finset.univ, j) => S.donorValues d.1)
  let v := CellScheme.zeroAbove
    (fun d : I.right.scheme.below (Finset.univ, j) => S.privateValues d.1)
  have hshared (i : Cell I.common.scheme) : u (I.shared.f i) = v (I.shared.g i) := by
    have hg : I.left.scheme.grade (I.shared.f i) = I.right.scheme.grade (I.shared.g i) :=
      congrArg (fun x : Finset ι × ℕ => x.2) (I.shared.shared i)
    by_cases hd : I.left.scheme.grade (I.shared.f i) ≤ j
    · have he : I.right.scheme.grade (I.shared.g i) ≤ j := hg ▸ hd
      rw [show u (I.shared.f i) = S.donorValues (I.shared.f i) from
        CellScheme.zeroAbove_low _ ⟨_, Finset.subset_univ _, hd⟩,
        show v (I.shared.g i) = S.privateValues (I.shared.g i) from
        CellScheme.zeroAbove_low _ ⟨_, Finset.subset_univ _, he⟩]
      exact shared I X T hs i
    · exact (CellScheme.zeroAbove_high _ hd).trans
        (CellScheme.zeroAbove_high _ (hg ▸ hd)).symm
  have hl := (I.paste_respects hs.donor_lawful.zeroAbove
    hs.private_lawful.zeroAbove hshared).toBelow (A, j)
  have he : (fun d : I.boundary.below (A, j) => S.profile (field I d.1)) =
      (fun d => I.paste u v d.1) := by
    funext d
    rw [field_read]
    rcases OrderedFaceBoundaryRows.covered I.leftScheme I.rightScheme I.shared R I.isPlan
        I.leftPlan_le I.rightPlan_le d.1 with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hg : I.left.scheme.grade c ≤ j := by
        have hi := d.2.2
        rw [← hc] at hi
        exact (congrArg Prod.snd (I.leftFace.index c)).ge.trans hi
      rw [← hc]
      exact (I.paste_left _ _ c).trans
        ((CellScheme.zeroAbove_low
          (fun d : I.left.scheme.below (Finset.univ, j) => S.donorValues d.1)
          ⟨c, Finset.subset_univ _, hg⟩).symm.trans
          (I.paste_left u v c).symm)
    · have hg : I.right.scheme.grade c ≤ j := by
        have hi := d.2.2
        rw [← hc] at hi
        exact (congrArg Prod.snd (I.rightFace.index c)).ge.trans hi
      rw [← hc]
      exact (I.paste_right _ _ (shared I X T hs) c).trans
        ((CellScheme.zeroAbove_low
          (fun d : I.right.scheme.below (Finset.univ, j) => S.privateValues d.1)
          ⟨c, Finset.subset_univ _, hg⟩).symm.trans
          (I.paste_right u v hshared c).symm)
  exact he ▸ hl


include T in
theorem anchor_lawful_at {j : ℕ} (a : Catalogue X j) :
    RespectsSemanticsBelow I.rows (A, j)
      (fun d => fields X j a (field I d.1)) := by
  obtain ⟨S, hs, he⟩ := a.property.2
  change RespectsSemanticsBelow I.rows (A, j) (fun d => a.val (field I d.1))
  rw [← he]
  exact boundary_lawful_at I X T hs

end
end VaughtConjecture.Knight.GrowthHigherSources
