/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedOwnerLift

/-! # Independent section supply on the canonical two-layer carrier

First glue the two old faces at bottom cap. Normalize the resulting lawful
boundary with a bottom-reflecting finite encoder, construct its proper-profile
section, and decode. Literal top is restored by the outer decoder; it is not
inserted into the fixed proper-profile catalogue. No output lift is used.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalSections
open Transform Value ExtOrd CanonicalMixedGradeLayers CanonicalMixedOwnerLift
open CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)
variable (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
variable (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

/-- Every lawful whole OLD boundary extends, with arbitrary proper values
and literal top. This supplies sections, not agreement with an ambient. -/
theorem exists_whole {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    ∃ r : CanonicalMixedAmbient.target sem j hj hjA k hk hkA → ExtOrd,
      RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k) r ∧
      ∀ d, r (oldTarget sem j hj hjA hproper k hg hk hkA hjk d) = p d := by
  classical
  let all (d : Cell D) : D.below (A, k) :=
    ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hg d⟩
  obtain ⟨S, u, hu, _, hcode, hdecode⟩ :=
    (hp.toBelow (A, k)).exists_coded_representative (fun d => hg d.1)
      (le_refl (Nat.card (D.below (A, k))))
  let v : Cell D → ExtOrd := fun d => u (all d)
  have hv : RespectsSemantics sem v := hu.toRespects (fun d => (all d).2)
  have ht (d : Cell D) : v d ≠ ⊤ := by
    rcases mem_codedAlphabet_iff.mp (hcode (all d)) with hb | ⟨b, i, _, _, he⟩
    · exact hb.trans_ne bot_ne_top
    · exact he.trans_ne (ofOrd_ne_top _)
  let s := sectionOf sem j hj hjA hproper k hg hk hkA hjk hv ht ∅ ⊤
  have hs : RespectsSemantics (rows sem j hj hjA hproper k hg hk hkA hjk) s :=
    section_lawful sem j hj hjA hproper k hg hk hkA hjk hv ht
      (by simp) (extVisibilityReplace_top k k)
  have hsread := section_boundary sem j hj hjA hproper k hg hk hkA hjk hv ht
    (G := ∅) (by simp) (extVisibilityReplace_top k k)
  refine ⟨fun d => canonicalDecoder S k (s d.1),
    (hs.toBelow (A, k)).decoded S (fun d => d.2.2), ?_⟩
  intro d
  exact (congrArg (canonicalDecoder S k) (hsread d)).trans (hdecode (all d))

/-- Bottom-cap supply from a proper prescribed face uses only the two old
face clauses. Empty prescribed domains require no owner or positive label. -/
theorem exists_section {I U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hIU : GradedLe I U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hIU) (hright : CappedLift sem hOV)
    {p : D.below I → ExtOrd} (hp : RespectsSemanticsBelow sem I p) :
    ∃ r : CanonicalMixedAmbient.target sem j hj hjA k hk hkA → ExtOrd,
      RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k) r ∧
      ∀ d : D.below I, r (oldTarget sem j hj hjA hproper k hg hk hkA hjk d.1) = p d := by
  obtain ⟨b, hread⟩ := section_left hIU hOU hOV hinter hleft hright p hp
  obtain ⟨r, hr, hold⟩ := exists_whole sem j hj hjA hproper k hg hk hkA hjk
    (b.whole_respects hcover)
  exact ⟨r, hr, fun d => (hold d.1).trans (hread d)⟩

end
end VaughtConjecture.Knight.CanonicalSections
