/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryFinalOwnerLift
public import VaughtConjecture.Knight.OrdinaryFinalBottom
public import VaughtConjecture.Knight.FinalGateTransport
public import VaughtConjecture.Knight.NativePrivateFace

/-! # Literal private-face lifting on the ordinary final physical layer

The private original face is identified occurrence by occurrence. An active
maximal prescribed owner supplies the capped physical repair; the predecessor's
lower-grade lift restores every remaining private value literally, including
distinct invisible values and top. Inactive owners and bottom caps are handled
separately. Every auxiliary retains the original external cap.

This proves the one private-face lifting clause under explicit predecessor
source, face, and lower-lifting hypotheses. It does not construct the global
scope predecessor or assert bountifulness for the whole request plan.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryFinalPrivateLift
open Transform Value ExtOrd CappedDonor CappedDonor.Ref CoatomBoundaryExtension
open OrdinaryFinalCatalogue OrdinaryFinalReadback OrdinaryOwnerFactorization
open SharpWitnessComposition
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)
variable {ι : Type*} [DecidableEq ι] {A S : Finset ι} {D : CellScheme A}
variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))
variable (place : Fin N ↪ ι) (hS : Finset.univ.image place = S)
variable (hSA : S ⊆ A) (hne : S ≠ A)
variable (E : ExactSemanticFace (PointImageSemantics.rows C.scheme place hS C.rows) F.sem)

abbrev privateGrade (d : Cell C.scheme) : D.grade (E.map d) = C.scheme.grade d :=
  congrArg Prod.snd (E.index d)

abbrev privateEquiv : C.scheme.below (effC N N) ≃ F.carrier.below (S, N) :=
  NativePrivateFace.fullEquiv C place hS (F.inheritedFace hSA hne E)

theorem privateEquiv_mono (d : C.scheme.below (effC N N)) :
    CellScheme.below.mono (show GradedLe (S, N) (A, N) from ⟨hSA, le_rfl⟩)
      (privateEquiv R F place hS hSA hne E d) =
      privAt R F E.map (privateGrade R F place hS E) d.1 := rfl

include hne

/-- Positive-cap lifting on the actual private lower set. The maximal owner
and the lower literal restoration are constructed, not extra assumptions. -/
theorem exists_positive_lift
    (hfields : ∀ a f, F.fields a f = a.val f)
    (hgrid : F.grid = PairedSlotComparison.sourceGrid N (Fintype.card (Field P C)))
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (hpriv : ∀ a d, F.lower a (E.map d) = a.val (.priv d))
    (hlift : CappedLift F.sem
      (show GradedLe (S, N - 1) (A, N - 1) from ⟨hSA, le_rfl⟩))
    {p : F.carrier.below (S, N) → ExtOrd}
    (hp : RespectsSemanticsBelow F.rows (S, N) p)
    {q : F.carrier.below (A, N) → ExtOrd}
    (hq : RespectsSemanticsBelow F.rows (A, N) q)
    {γ : ExtOrd} (hγ : SelfVis N γ) (hpos : ⊥ < γ)
    (hag : ∀ e, min (q (CellScheme.below.mono
      (show GradedLe (S, N) (A, N) from ⟨hSA, le_rfl⟩) e)) γ = min (p e) γ) :
    ∃ r : F.carrier.below (A, N) → ExtOrd,
      RespectsSemanticsBelow F.rows (A, N) r ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ e, r (CellScheme.below.mono
        (show GradedLe (S, N) (A, N) from ⟨hSA, le_rfl⟩) e) = p e := by
  classical
  by_cases hhigh : ∀ e : F.carrier.below (S, N), F.carrier.grade e.1 = N → p e ≤ γ
  · exact F.lift_inactive hSA hlift hp hq hγ hag hhigh
  push Not at hhigh
  obtain ⟨e₀, he₀, hpe₀⟩ := hhigh
  let e := privateEquiv R F place hS hSA hne E
  let pn := p ∘ e
  have hpn : RespectsSemanticsBelow C.rows (effC N N) pn :=
    (NativePrivateFace.respects_iff C place hS (F.inheritedFace hSA hne E) p).mp hp
  have hg (d : C.scheme.below (effC N N)) :
      F.carrier.grade (e d).1 = C.scheme.grade d.1 :=
    NativePrivateFace.fullEquiv_grade C place hS (F.inheritedFace hSA hne E) d
  let : Fintype (Cell C.scheme) := Fintype.ofFinite _
  let s := Finset.univ.filter (fun c : Cell C.scheme => C.scheme.grade c = N)
  have hs : (e.symm e₀).1 ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    rw [← hg, e.apply_symm_apply, he₀]⟩
  obtain ⟨c, hc, hm⟩ := Finset.exists_max_image s (fun c => pn (privateCell c))
    ⟨(e.symm e₀).1, hs⟩
  have hpc : γ < pn (privateCell c) := by
    have he : pn (privateCell (e.symm e₀).1) = p e₀ := by
      change p (e (e.symm e₀)) = p e₀
      rw [e.apply_symm_apply]
    exact hpe₀.trans_le (he ▸ hm (e.symm e₀).1 hs)
  have hcn : C.scheme.grade c = N := (Finset.mem_filter.mp hc).2
  have hmax (d : C.scheme.below (effC N N)) (hd : C.scheme.grade d.1 = N) :
      pn d ≤ pn (privateCell c) :=
    hm d.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)
  obtain ⟨u, hu, hread, hcaps, -⟩ := OrdinaryFinalOwnerLift.exists_owner_capped_lift
    R F E.map (privateGrade R F place hS E) hfields hgrid hsupport hpriv c hcn
    hpn hq hγ hpos hpc (fun d => hag (e d))
  have hread' (d : F.carrier.below (S, N)) :
      u (CellScheme.below.mono (show GradedLe (S, N) (A, N) from ⟨hSA, le_rfl⟩) d) =
        min (p d) (pn (privateCell c)) := by
    obtain ⟨b, rfl⟩ := e.surjective d
    exact hread b
  have hhigh' (d : F.carrier.below (S, N)) (hd : F.carrier.grade d.1 = N) :
      p d ≤ pn (privateCell c) := by
    obtain ⟨b, rfl⟩ := e.surjective d
    exact hmax b ((hg b).symm.trans hd)
  have hM : SelfVis N (pn (privateCell c)) := by
    have hh : SelfVis (C.scheme.grade c) (pn (privateCell c)) :=
      (hpn.orderly (privateCell c)).symm
    rwa [hcn] at hh
  obtain ⟨r, hr, hprivate, hcap, -⟩ := F.restore hSA hlift hp hu hM hread' hhigh'
  exact ⟨r, hr, fun d => (GradeTailRestoration.cap_below (hcap d) hpc.le).trans
    (hcaps d), hprivate⟩

/-- All-cap private-face lifting, including independent bottom supply and
literal top. The only lifting premise belongs to the predecessor below N. -/
theorem private_lift
    (hfields : ∀ a f, F.fields a f = a.val f) (hgate : F.gate = .gate)
    (hgrid : F.grid = PairedSlotComparison.sourceGrid N (Fintype.card (Field P C)))
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (howners : ∀ a (c : D.below (A, N)),
      (∀ d : D.below (D.cell c.1), Short (D.grade c.1) (F.sem.E c.1 d)) ∨
      (∀ d : D.below (D.cell c.1), ∃ f : Field P C, F.lower a d.1 = a.val f))
    (hpriv : ∀ a d, F.lower a (E.map d) = a.val (.priv d))
    (hlift : CappedLift F.sem
      (show GradedLe (S, N - 1) (A, N - 1) from ⟨hSA, le_rfl⟩)) :
    CappedLift F.rows (show GradedLe (S, N) (A, N) from ⟨hSA, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  by_cases hbot : γ = ⊥
  · let e := privateEquiv R F place hS hSA hne E
    have hpn := (NativePrivateFace.respects_iff C place hS
      (F.inheritedFace hSA hne E) p).mp hp
    have hgridShort : ∀ z ∈ F.grid, Short N z := by
      rw [hgrid]
      exact fun _ hz => CanonicalFieldLayer.grid_short N (Field P C) hz
    obtain ⟨b, δ, -, hv, hread, -⟩ := OrdinaryFinalBottom.exists_private_display R F
      hfields hgate hgridShort hsupport howners E.map hpriv hpn
    refine ⟨fun d => δ (F.source b d.1), hv, ?_, ?_⟩
    · intro d
      simp only [hbot, min_eq_right bot_le]
    · intro d
      obtain ⟨x, rfl⟩ := e.surjective d
      exact hread x
  · exact exists_positive_lift R F place hS hSA hne E hfields hgrid hsupport hpriv
      hlift hp hq hγ (bot_lt_iff_ne_bot.mpr hbot) hag

end
end VaughtConjecture.Knight.OrdinaryFinalPrivateLift
