/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthCarrierEvaluation
public import VaughtConjecture.Knight.StableActualLabelling
public import VaughtConjecture.Knight.GrowthStableSelectedInput
public import VaughtConjecture.Knight.TopSupportReceiving
public import VaughtConjecture.Knight.ActualOccurrence

/-! # Actual growth receiving evaluated by lawful stable labels

Generalized saturation realizes the legal scheme over the actual private
context. The stable labels of that actual coface are independently lawful,
agree with the private context's stable labels, and retain its bottom class.
Positive-cap physical correctness therefore applies even when the stable cap
is proper. No stable modelhood or realization of a selected display is used.

The calibrated `RelativeData` and literal root attachment remain inputs.
In particular this does not construct the shorter encoding or donor template.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthStableCarrierReceiving
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor
open Growth CellScheme.restrictFace
noncomputable section
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}
  {n J : ℕ} (C : S α.1 J) (P : SemScheme (n + 1)) (Q : SemScheme n)
  (e : Fin n ↪ Fin J)
  (hvC : Finset.univ.image e ∈ C.scheme.scheme.plan)
  (hvP : Finset.univ.image Fin.castSuccEmb ∈ P.scheme.plan)
  (hC : C.scheme.restrictFace e hvC = Q)
  (hP : P.restrictFace Fin.castSuccEmb hvP = Q)
  (X : RelativeData C.scheme.scheme C.scheme.rows P.scheme P.rows)
  (T : RootAttachment Q Fin.castSuccEmb hvP hP e hvC hC X)
  (hsmall : n + 1 < X.req.N)

local notation "E" => GrowthAttachedCarrier.semScheme C.scheme P Q e hvC hvP hC hP X T hsmall
local notation "F" => GrowthAttachedCarrier.privateFace C.scheme P Q e hvC hvP hC hP X T hsmall
local notation "G" => GrowthAttachedCarrier.donorFace C.scheme P Q e hvC hvP hC hP X T hsmall

theorem extendsDomain : ExtendsDomain C E :=
  GrowthCarrierEvaluation.extendsDomain C P Q e hvC hvP hC hP X T hsmall

theorem private_cellOf (d : Cell C.scheme.scheme) :
    (extendsDomain C P Q e hvC hvP hC hP X T hsmall).cellOf d = (F).map d :=
  GrowthCarrierEvaluation.private_cellOf C P Q e hvC hvP hC hP X T hsmall d

variable (hM : W.IsModel) {u : Fin J ↪ M} (hu : W.eval u = some C)

include hM hu in
set_option linter.unusedSectionVars false in
/-- Stable private values are retained along the actual coface, even when
they differ from its actual private labels. -/
theorem stable_private {y : M} {hy : y ∉ Set.range u} {r : S α.1 (J + 1)}
    (hr : r.scheme = E) (hco : IsCoface C r) (heval : W.eval (snoc u y hy) = some r)
    (d : Cell C.scheme.scheme) :
    W.stableValue (snoc u y hy) r (SemScheme.castCell hr.symm ((F).map d)) =
      W.stableValue u C d :=
  GrowthCarrierEvaluation.private_label C P Q e hvC hvP hC hP X T hsmall
    (stableActualLabelling hM.consistent hM.covering) hr hco heval d

include hM hu in
/-- The stable labelling of every actual coface satisfies the request relation
on the actual donor occurrences. Admission is derived physically. -/
theorem correct_of_coface (hclass : InClass X.ZA C.label)
    {y : M} {hy : y ∉ Set.range u} {r : S α.1 (J + 1)}
    (hr : r.scheme = E) (hco : IsCoface C r) (heval : W.eval (snoc u y hy) = some r) :
    X.req.Correct (X.req.sec (W.stableValue u C))
      (fun d => W.stableValue (snoc u y hy) r (SemScheme.castCell hr.symm ((G).map d))) := by
  have hin : InClass X.ZA (W.stableValue u C) := fun d =>
    (GrowthStableSelectedInput.private_bottom hM hu d.1).trans (hclass d)
  exact GrowthCarrierEvaluation.correct_of_coface C P Q e hvC hvP hC hP X T hsmall
    (stableActualLabelling hM.consistent hM.covering) hin hr hco heval

include hM hu in
/-- Actual realization over the private context; no selected labelling is
presented to generalized saturation. -/
theorem exists_correct_coface (hclass : InClass X.ZA C.label) :
    ∃ (y : M) (hy : y ∉ Set.range u) (r : S α.1 (J + 1)) (hr : r.scheme = E),
      IsCoface C r ∧ W.eval (snoc u y hy) = some r ∧
      X.req.Correct (X.req.sec (W.stableValue u C))
        (fun d => W.stableValue (snoc u y hy) r (SemScheme.castCell hr.symm ((G).map d))) := by
  exact GrowthCarrierEvaluation.exists_correct_coface C P Q e hvC hvP hC hP X T hsmall
    (stableActualLabelling hM.consistent hM.covering) hM hu
    (fun d => (GrowthStableSelectedInput.private_bottom hM hu d.1).trans (hclass d))

/-- The literal donor restriction and its actual occurrence map. -/
theorem donor_restriction {r : S α.1 (J + 1)} (hr : r.scheme = E) :
    ∃ s : S α.1 (n + 1), ∃ hs : typeMap (onePointProj e) r = some s,
      ∃ he : s.scheme = P, ∀ d,
        mapCell hs (SemScheme.castCell he.symm d) = SemScheme.castCell hr.symm ((G).map d) := by
  exact GrowthCarrierEvaluation.donor_restriction C P Q e hvC hvP hC hP X T hsmall hr

include Q hvC hvP hC hP T hsmall hM hu in
/-- A fresh actual donor occurrence whose stable labels satisfy the calibrated
request relation. The donor scheme is literal, with no displayed-stage premise. -/
theorem exists_correct_donor (hclass : InClass X.ZA C.label) :
    ∃ (y : M) (_hy : y ∉ Set.range u) (hyRoot : y ∉ Set.range (e.trans u))
      (s : S α.1 (n + 1)), W.eval (snoc (e.trans u) y hyRoot) = some s ∧
      ∃ hs : s.scheme = P,
        X.req.Correct (X.req.sec (W.stableValue u C))
          (fun d => W.stableValue (snoc (e.trans u) y hyRoot) s
            (SemScheme.castCell hs.symm d)) := by
  exact GrowthCarrierEvaluation.exists_correct_donor C P Q e hvC hvP hC hP X T hsmall
    (stableActualLabelling hM.consistent hM.covering) hM hu
    (fun d => (GrowthStableSelectedInput.private_bottom hM hu d.1).trans (hclass d))

include Q hvC hvP hC hP T hsmall hM hu in
/-- The two distinct selected-receiving receipts from concrete calibration:
exact cells use zero or proper reference requests; high cells use either a
high marker or an exact cell already above the requested bound. Constructing
the calibrated datum remains separate from this actual-occurrence theorem. -/
theorem exists_calibrated_donor (hclass : InClass X.ZA C.label)
    (target : Cell P.scheme → ExtOrd) (exactCells highCells : Set (Cell P.scheme))
    (γ : ExtOrd)
    (hexact : ∀ d ∈ exactCells,
      (d ∈ X.req.Z ∧ target d = ⊥) ∨
        (d ∈ X.req.F ∧ X.req.tOf (X.req.sec (W.stableValue u C)) d = target d ∧
          target d < W.stableValue u C X.req.C))
    (hhigh : ∀ d ∈ highCells,
      (d ∈ X.req.T ∧ γ < X.req.dOf (X.req.sec (W.stableValue u C))) ∨
        (d ∈ exactCells ∧ γ < target d)) :
    ∃ (y : M) (_hy : y ∉ Set.range u) (hyRoot : y ∉ Set.range (e.trans u))
      (s : S α.1 (n + 1)), W.eval (snoc (e.trans u) y hyRoot) = some s ∧
      ∃ hs : s.scheme = P,
        (∀ d ∈ exactCells, W.stableValue (snoc (e.trans u) y hyRoot) s
          (SemScheme.castCell hs.symm d) = target d) ∧
        (∀ d ∈ highCells, γ < W.stableValue (snoc (e.trans u) y hyRoot) s
          (SemScheme.castCell hs.symm d)) := by
  obtain ⟨y, hy, hyRoot, s, hev, hs, hc⟩ :=
    exists_correct_donor C P Q e hvC hvP hC hP X T hsmall hM hu hclass
  have hin : InClass X.ZA (W.stableValue u C) := fun d =>
    (GrowthStableSelectedInput.private_bottom hM hu d.1).trans (hclass d)
  have he (d) (hd : d ∈ exactCells) :=
    Requests.Correct.read_exact X.req hc (X.cap_ne_bot hin) (hexact d hd)
  refine ⟨y, hy, hyRoot, s, hev, hs, he, ?_⟩
  intro d hd
  rcases hhigh d hd with ⟨ht, hm⟩ | ⟨hd', hl⟩
  · exact Requests.Correct.read_high X.req hc ht hm
  · rwa [he d hd']

end
end VaughtConjecture.Knight.GrowthStableCarrierReceiving
