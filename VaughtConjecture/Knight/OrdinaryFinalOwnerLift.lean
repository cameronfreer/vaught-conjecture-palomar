/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryFinalRepair
public import VaughtConjecture.Knight.OrdinaryOwnerFactorization
public import VaughtConjecture.Knight.OrdinaryFinalReadback

/-! # Original-cap owner lifting on the ordinary final physical layer

From arbitrary lawful private prescriptions and target-local ambients, actual
availability/locality select the serving chart. Private-owner factorization,
ordinary catalogue repair, and supported inversion construct a new physical
section. Every installed coordinate retains the original external cap, and the
private prescription is read back capped at its active owner.

The cap identity is proved before lawfulness of the composite image. Only
bounded commutation is used for the composite; unrestricted faithful witness
composition is not asserted. Literal restoration above a proper owner remains
a separate predecessor-lifting step.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryFinalOwnerLift
open Transform Value ExtOrd CappedDonor CappedDonor.Ref SharpWitnessComposition
open OrdinaryFinalCatalogue OrdinaryFinalReadback OrdinaryOwnerFactorization
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))
variable (priv : Cell C.scheme ↪ Cell D)
variable (hprivGrade : ∀ d, D.grade (priv d) = C.scheme.grade d)

private theorem cap_of_prefix {ν : ExtOrd → ExtOrd} (hν : Monotone ν)
    {δ γ x y : ExtOrd} (hr : γ ≤ ν δ) (he : min y δ = min x δ) :
    min (ν y) γ = min (ν x) γ := by
  have h (z) : min (ν (min z δ)) γ = min (ν z) γ := by
    rw [hν.map_min, min_assoc, min_eq_right hr]
  exact (h y).symm.trans ((congrArg (fun z => min (ν z) γ) he).trans (h x))

/-- All original auxiliary caps are retained against an arbitrary lawful
ambient. The output reads the prescription capped at the chosen active owner. -/
theorem exists_owner_capped_lift
    (hfields : ∀ a f, F.fields a f = a.val f)
    (hgrid : F.grid = PairedSlotComparison.sourceGrid N (Fintype.card (Field P C)))
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (hpriv : ∀ a d, F.lower a (priv d) = a.val (.priv d))
    (c : Cell C.scheme) (hc : C.scheme.grade c = N)
    {p : C.scheme.below (effC N N) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC N N) p)
    {q : F.carrier.below (A, N) → ExtOrd}
    (hq : RespectsSemanticsBelow F.rows (A, N) q)
    {γ : ExtOrd} (hγ : SelfVis N γ) (hpos : ⊥ < γ)
    (hpc : γ < p (privateCell c))
    (hag : ∀ d, min (q (privAt R F priv hprivGrade d.1)) γ = min (p d) γ) :
    ∃ w : F.carrier.below (A, N) → ExtOrd,
      RespectsSemanticsBelow F.rows (A, N) w ∧
      (∀ d : C.scheme.below (effC N N),
        w (privAt R F priv hprivGrade d.1) = min (p d) (p (privateCell c))) ∧
      (∀ d, min (w d) γ = min (q d) γ) ∧
      ∀ d, w d ≤ p (privateCell c) := by
  let c' := privAt R F priv hprivGrade c
  have hc' : F.carrier.grade c'.1 = N :=
    (congrArg Prod.snd (F.old_index (priv c))).trans ((hprivGrade c).trans hc)
  have hreach : γ ≤ q c' := min_eq_right_iff.mp
    ((hag (privateCell c)).trans (min_eq_right hpc.le))
  let seed : OrdinaryFinalCatalogue.Member R := ⟨PairedSlotEncoding.normalize N (fun _ => ⊥),
    (CappedDonor.Ref.Admitted.zero R).normalize_mem_catalogue (fun _ => bot_ne_top)⟩
  obtain ⟨a, σ, hσ, hb, hchart⟩ := F.exists_cap_chart hq c' hc' seed hγ hreach
  have hread (d : C.scheme.below (effC N N)) :
      σ (a.val (.priv d.1)) = min (q (privAt R F priv hprivGrade d.1)) γ := by
    simpa only [privAt, oldAt, F.source_old, hpriv] using
      hchart (privAt R F priv hprivGrade d.1)
  obtain ⟨B, hB, f, ν, hf, hproper, hprefix, hν, hbound, hprivate, hνreach, hνcaps⟩ :=
    OrdinaryOwnerFactorization.exists_factorization R c hc a hp hσ hγ hpos hpc
      (fun d => by rw [min_eq_left (hb _), hread d]; exact hag d)
  have hBF : CanonicalPairedInverse.grid N B ∈ F.grid := hgrid ▸ hB
  obtain ⟨b, κ, hκ, -, hsource, hfread⟩ :=
    OrdinaryFinalRepair.exists_source_repair R F hfields hgrid hsupport priv hpriv
      a hf hproper hBF hprefix
  have hfieldShort : ∀ b f, Short N (F.fields b f) := by
    intro b f
    rw [hfields]
    exact member_short R b f
  have hgridShort : ∀ z ∈ F.grid, Short N z := by
    rw [hgrid]
    exact fun _ hz => CanonicalFieldLayer.grid_short N (Field P C) hz
  let w := fun d : F.carrier.below (A, N) => ν (κ (F.source b d.1))
  have hcaps (d : F.carrier.below (A, N)) : min (w d) γ = min (q d) γ := by
    exact (cap_of_prefix hν.mono hνreach (hsource d)).trans
      ((hνcaps _ (F.source_short hsupport hfieldShort hgridShort a d.1 d.2.2)).trans
        (by rw [hchart d, min_assoc, min_self]))
  refine ⟨w, ?_, ?_, hcaps, fun _ => hbound _⟩
  · exact map_respects_of_positive_cap_agreement (F.source_lawful b) hq
      (fun d => d.2.2) (bounded_comp hκ hν le_rfl) hpos.ne' hcaps
  · intro d
    change ν (κ (F.source b (F.old (priv d.1)))) = _
    rw [hfread]
    exact hprivate d

end
end VaughtConjecture.Knight.OrdinaryFinalOwnerLift
