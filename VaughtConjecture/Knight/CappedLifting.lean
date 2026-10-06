/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SemScheme
public import VaughtConjecture.Knight.VisibilityAlgebra

/-! # The foundational original-cap lifting calculus

One literal lifting property, its identity and composition laws, old-face transport,
and generation by finite cover relations. These results do not depend on any concrete
carrier, code table, receiver or model. Historical public names remain in the
`CoatomBoundaryExtension` namespace for compatibility.

General lifting asserts existence for each ambient and cap. It does not assert a unique
extension or simultaneous cap preservation; those require injective restriction and are
supplied separately by `CappedLiftOfExtension`.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.CoatomBoundaryExtension

open Transform Value ExtOrd
open VaughtConjecture.AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable {sem : Semantics D} {I U J K : Finset ι × ℕ}

/-- A single literal old graded-pair lifting clause, also allowing equal
indices and empty source domains. No new whole-target lift is included. -/
def CappedLift (sem : Semantics D) (h : GradedLe I U) : Prop :=
  ∀ (p : D.below I → ExtOrd) (q : D.below U → ExtOrd) (γ : ExtOrd),
    RespectsSemanticsBelow sem I p → RespectsSemanticsBelow sem U q →
    SelfVis U.2 γ →
    (∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) →
    ∃ r : D.below U → ExtOrd, RespectsSemanticsBelow sem U r ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ d, r (CellScheme.below.mono h d) = p d

/-- Equal indices require no appeal to strict-pair bountifulness. -/
theorem lift_refl : CappedLift sem (GradedLe.refl I) := by
  intro p q γ hp _ _ hag
  exact ⟨p, hp, fun d => (hag d).symm, fun _ => rfl⟩

/-- Empty overlap needs neither a positive grade nor a fictitious owner. -/
theorem lift_empty (h : GradedLe I U) [IsEmpty (D.below I)] : CappedLift sem h := by
  intro _ q _ _ hq _ _
  exact ⟨q, hq, fun _ => rfl, fun d => isEmptyElim d⟩

/-- The clause is supplied by the old scheme's actual bountifulness. -/
theorem lift_of_bountiful (hb : sem.IsBountiful)
    (hI : I ∈ Plan.gradedPlan D.plan) (hU : U ∈ Plan.gradedPlan D.plan)
    (h : GradedLe I U) : CappedLift sem h := by
  by_cases he : I = U
  · subst U
    exact lift_refl
  · intro p q γ hp hq hγ hag
    exact hb I U hI hU h he p q γ hp hq hγ hag

/-- Transport a lift along literal lower-domain equivalences. The restriction square must
commute, lawful sections must transport, and the old target grade must permit the new cap.
No global carrier equivalence or output bountifulness is assumed. -/
theorem CappedLift.of_equiv
    {ι' : Type*} [DecidableEq ι'] {A' : Finset ι'} {D' : CellScheme A'}
    {sem' : Semantics D'} {I' U' : Finset ι' × ℕ}
    {h : GradedLe I U} {h' : GradedLe I' U'}
    (eI : D'.below I' ≃ D.below I) (eU : D'.below U' ≃ D.below U)
    (hsquare : ∀ d, eU (CellScheme.below.mono h' d) = CellScheme.below.mono h (eI d))
    (hgrade : U'.2 ≤ U.2)
    (hsource : ∀ p, RespectsSemanticsBelow sem I p →
      RespectsSemanticsBelow sem' I' (p ∘ eI))
    (htarget : ∀ q, RespectsSemanticsBelow sem U q ↔
      RespectsSemanticsBelow sem' U' (q ∘ eU))
    (hl : CappedLift sem' h') : CappedLift sem h := by
  intro p q γ hp hq hγ hag
  obtain ⟨r, hr, hc, hf⟩ := hl (p ∘ eI) (q ∘ eU) γ (hsource p hp)
    ((htarget q).mp hq) (hγ.mono hgrade) (fun d => by
      simpa only [Function.comp_apply, hsquare] using hag (eI d))
  refine ⟨r ∘ eU.symm, (htarget _).mpr ?_, ?_, ?_⟩
  · simpa only [Function.comp_def, Equiv.symm_apply_apply] using hr
  · intro d
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hc (eU.symm d)
  · intro d
    have he : eU.symm (CellScheme.below.mono h d) = CellScheme.below.mono h' (eI.symm d) := by
      apply eU.injective
      rw [Equiv.apply_symm_apply, hsquare, Equiv.apply_symm_apply]
    rw [Function.comp_apply, he, hf, Function.comp_apply, Equiv.apply_symm_apply]

section FaceTransport

open CellScheme.restrictFace

variable {m n : ℕ} {D₀ : CellScheme (ι := Fin n) Finset.univ}
variable {s : Semantics D₀} {f : Fin m ↪ Fin n}
variable {hf : Finset.univ.image f ∈ D₀.plan}
variable {I' U' : Finset (Fin m) × ℕ}

/-- Only the old face is assumed bountiful. The surrounding semantics may
have arbitrary unfinished rows outside that face. -/
theorem lift_of_restrictFace
    (hb : (s.restrictFace f hf).IsBountiful)
    (hI : I' ∈ Plan.gradedPlan (D₀.restrictFace f hf).plan)
    (hU : U' ∈ Plan.gradedPlan (D₀.restrictFace f hf).plan)
    (h : GradedLe I' U') :
    CappedLift s ((gradedLe_pushGraded_iff f).mpr h) := by
  apply CappedLift.of_equiv (belowEquiv D₀ f hf rfl) (belowEquiv D₀ f hf rfl)
    (fun d => belowEquiv_mono D₀ f hf h d) le_rfl
    (fun _ hp => hp.restrictFace rfl) _ (lift_of_bountiful hb hI hU h)
  intro q
  exact ⟨fun hq => hq.restrictFace rfl, fun hq => by
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using hq.of_restrictFace rfl⟩

end FaceTransport

theorem CappedLift.comp {hIJ : GradedLe I J} {hJK : GradedLe J K}
    (hleft : CappedLift sem hIJ) (hright : CappedLift sem hJK) :
    CappedLift sem (hIJ.trans hJK) := by
  intro p q γ hp hq hγ hag
  obtain ⟨u, hu, hucap, huread⟩ := hleft p (q ∘ CellScheme.below.mono hJK) γ hp
    (hq.mono hJK) (hγ.mono hJK.2) hag
  obtain ⟨r, hr, hcap, hread⟩ := hright u q γ hu hq hγ (fun d => (hucap d).symm)
  exact ⟨r, hr, hcap, fun d => (hread (CellScheme.below.mono hIJ d)).trans (huread d)⟩

/-- Restrict a target after lawfully extending its actual ambient. The common target
grade keeps the permitted cap unchanged. Bottom supply comes from the second lift. -/
theorem CappedLift.restrict_target (hIJ : GradedLe I J) (hJU : GradedLe J U)
    (hgrade : J.2 = U.2) (hIU : CappedLift sem (hIJ.trans hJU))
    (hJU_lift : CappedLift sem hJU) : CappedLift sem hIJ := by
  intro p q γ hp hq hγ hag
  obtain ⟨qU, hqU, _, hqread⟩ := hJU_lift q (fun _ => ⊥) ⊥ hq
    (RespectsSemanticsBelow.bot sem U)
    (extVisibilityReplace_bot _ _) (fun _ => by simp only [min_bot_right])
  have hagU (d : D.below I) :
      min (qU (CellScheme.below.mono (hIJ.trans hJU) d)) γ = min (p d) γ := by
    change min (qU (CellScheme.below.mono hJU (CellScheme.below.mono hIJ d))) γ = _
    rw [hqread]
    exact hag d
  obtain ⟨r, hr, hcap, hread⟩ := hIU p qU γ hp hqU (hgrade ▸ hγ) hagU
  refine ⟨fun d => r (CellScheme.below.mono hJU d), hr.mono hJU, ?_, hread⟩
  intro d
  exact (hcap (CellScheme.below.mono hJU d)).trans
    (congrArg (fun x => min x γ) (hqread d))

/-- **Bountifulness from a decided cover table.**  The graded plan is enumerated by `gidx`,
its order decided by `gle`, a strictly ascending measure `gsize` given, and `covers` lists
pairs such that every strict pair `i < j` has a cover `(i, k)` with `k ≤ j`; a lift at every
listed pair gives bountifulness. -/
theorem CappedLift.isBountiful_of_covers {G : ℕ} (gidx : Fin G → Finset ι × ℕ)
    (gle : Fin G → Fin G → Bool) (gsize : Fin G → ℕ) (covers : List (Fin G × Fin G))
    (gradedLe_iff : ∀ i j, GradedLe (gidx i) (gidx j) ↔ gle i j = true)
    (gle_of_cov : ∀ i k, (i, k) ∈ covers → gle i k = true)
    (gsize_lt_of_cov : ∀ i k, (i, k) ∈ covers → gsize i < gsize k)
    (gsize_le_of_gle : ∀ i j, gle i j = true → gsize i ≤ gsize j)
    (exists_cov : ∀ i j, i ≠ j → gle i j = true → ∃ k, (i, k) ∈ covers ∧ gle k j = true)
    (exists_gidx : ∀ BJ ∈ Plan.gradedPlan D.plan, ∃ i, gidx i = BJ)
    (build : ∀ i k (h : (i, k) ∈ covers),
      CappedLift sem ((gradedLe_iff i k).mpr (gle_of_cov i k h))) :
    sem.IsBountiful := by
  have main : ∀ (m : ℕ) (i j : Fin G), gsize j - gsize i = m → i ≠ j →
      (h : GradedLe (gidx i) (gidx j)) → CappedLift sem h := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i j hm hij h
      obtain ⟨k, hik, hkj⟩ := exists_cov i j hij ((gradedLe_iff i j).mp h)
      by_cases hk : k = j
      · subst hk
        exact build i k hik
      · have h2 : GradedLe (gidx k) (gidx j) := (gradedLe_iff k j).mpr hkj
        have hlt : gsize j - gsize k < m := by
          have := gsize_lt_of_cov i k hik
          have := gsize_le_of_gle k j hkj
          omega
        exact (build i k hik).comp (ih _ hlt k j rfl hk h2)
  intro CI BJ hCI hBJ h hne
  obtain ⟨i, rfl⟩ := exists_gidx CI hCI
  obtain ⟨j, rfl⟩ := exists_gidx BJ hBJ
  exact main _ i j rfl (fun e => hne (e ▸ rfl)) h


end VaughtConjecture.Knight.CoatomBoundaryExtension
