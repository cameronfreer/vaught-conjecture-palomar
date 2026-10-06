/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FinalGateApex
public import VaughtConjecture.Knight.OrdinaryFinalStage
public import VaughtConjecture.Knight.OrdinaryFinalReadback
public import VaughtConjecture.Knight.OrderedFaceRestriction
public import VaughtConjecture.Knight.CoatomRecursiveOrdered

/-! # Ordered ordinary receiving installation from the predecessor receipts

The final weighted layer is coded and completed by a mute apex. A stage-correct
physical selected display keeps both original types literally and its selected
marked gate top. Occurrence-exact ordered faces give literal `typeMap` equations,
not an isomorphism of restrictions.

The global scope predecessor is still an input. Its consistency, coding,
completeness-through-N ledger and selected-source contract are explicit; the
final-layer bountifulness theorem is consumed separately. No model receiving
or unconditional producer is asserted by this packaging.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryFinalInstallation
open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref SharpWitnessComposition
open OrdinaryFinalCatalogue OrdinaryFinalReadback
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)
variable {D : CellScheme (ι := Fin (N + 1)) Finset.univ}
variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))

abbrev card_eq : (Finset.univ : Finset (Fin (N + 1))).card = N + 1 := Finset.card_fin _
abbrev carrier := FinalGateApex.scheme F card_eq
abbrev original (d : Cell D) : Cell (carrier R F) := FinalGateApex.old F card_eq (F.old d)
abbrev marked (a : OrdinaryFinalCatalogue.Member R) : Cell (carrier R F) :=
  FinalGateApex.old F card_eq (F.added a true)

variable (hD : ∀ d : Cell D, D.grade d ≤ N)

/-- The concrete semantic package. The remaining final-layer pair theorem
is a visible input, not a renamed predecessor-completion assumption. -/
def semScheme (hcons : F.sem.IsConsistent) (hcode : F.sem.IsCoded)
    (hb : F.rows.IsBountiful)
    (hcomplete : ∀ J ∈ Plan.gradedPlan D.plan, J.2 ≤ N →
      J ≠ (Finset.univ, N) → ∃ d, D.cell d = J)
    (hfields : ∀ a f, F.fields a f = a.val f)
    (hgrid : F.grid = PairedSlotComparison.sourceGrid N (Fintype.card (Field P C)))
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d)) :
    SemScheme (N + 1) := by
  let seed := Classical.choose (exists_actual_member R)
  refine ⟨carrier R F, FinalGateApex.rows F hD card_eq, ?_,
    FinalGateApex.consistent F hD card_eq hcons, FinalGateApex.bountiful F hD card_eq hb,
    FinalGateApex.complete F card_eq seed hcomplete⟩
  apply FinalGateApex.coded F hD card_eq
  apply F.coded hcode (fun a f => hfields a f ▸ member_coded R a f) ?_ hsupport
  intro z hz
  exact CanonicalCodingSupport.grid N _ (hgrid ▸ hz)

/-- A lawful display on the complete inventory, without a stage-bound claim.
The bottom-pattern model clause consumes precisely this raw labelling. -/
theorem exists_installed_raw_display
    (hfields : ∀ a f, F.fields a f = a.val f) (hgate : F.gate = .gate)
    (hgrid : ∀ z ∈ F.grid, Short N z)
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (howners : ∀ a (c : D.below (Finset.univ, N)),
      (∀ d : D.below (D.cell c.1), Short (D.grade c.1) (F.sem.E c.1 d)) ∨
      (∀ d : D.below (D.cell c.1), ∃ f : Field P C, F.lower a d.1 = a.val f))
    (req : Cell P.scheme ↪ Cell D) (priv : Cell C.scheme ↪ Cell D)
    (hreq : ∀ a d, F.lower a (req d) = a.val (.req d))
    (hpriv : ∀ a d, F.lower a (priv d) = a.val (.priv d)) :
    ∃ (a : OrdinaryFinalCatalogue.Member R) (r : Cell (carrier R F) → ExtOrd),
      RespectsSemantics (FinalGateApex.rows F hD card_eq) r ∧
      (∀ d, r (original R F (req d)) = R.p d) ∧
      (∀ d, r (original R F (priv d)) = R.vact d) ∧
      r (marked R F a) = ⊤ ∧ r (FinalGateApex.apex F card_eq) = ⊥ := by
  obtain ⟨a, δ, -, hlaw, hp, hc, hg, -⟩ :=
    OrdinaryFinalDisplay.exists_actual_display R F hfields hgate hgrid hsupport howners
      req priv hreq hpriv
  let p := fun d : F.carrier.below (Finset.univ, N) => δ (F.source a d.1)
  refine ⟨a, FinalGateApex.display F card_eq p,
    FinalGateApex.display_lawful F hD card_eq hlaw, ?_, ?_, ?_,
    FinalGateApex.display_apex F card_eq p⟩
  · intro d
    exact (FinalGateApex.display_old F card_eq p (oldAt R F (req d) (hD _))).trans (hp d)
  · intro d
    exact (FinalGateApex.display_old F card_eq p (oldAt R F (priv d) (hD _))).trans (hc d)
  · exact (FinalGateApex.display_old F card_eq p (F.addedAt a true)).trans hg

/-- The selected physical display, now on the complete occurrence inventory
including the mute apex. Its original values and chosen gate remain literal. -/
theorem exists_installed_display (α : LimitStage)
    (hP : ∀ d, R.p d ≠ ⊤ → R.p d < ofOrd α.1)
    (hC : ∀ d, R.vact d ≠ ⊤ → R.vact d < ofOrd α.1)
    (hfields : ∀ a f, F.fields a f = a.val f) (hgate : F.gate = .gate)
    (hgrid : ∀ z ∈ F.grid, Short N z)
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (howners : ∀ a (c : D.below (Finset.univ, N)),
      (∀ d : D.below (D.cell c.1), Short (D.grade c.1) (F.sem.E c.1 d)) ∨
      (∀ d : D.below (D.cell c.1), ∃ f : Field P C, F.lower a d.1 = a.val f))
    (req : Cell P.scheme ↪ Cell D) (priv : Cell C.scheme ↪ Cell D)
    (hreq : ∀ a d, F.lower a (req d) = a.val (.req d))
    (hpriv : ∀ a d, F.lower a (priv d) = a.val (.priv d)) :
    ∃ (a : OrdinaryFinalCatalogue.Member R) (r : Cell (carrier R F) → ExtOrd),
      RespectsSemantics (FinalGateApex.rows F hD card_eq) r ∧
      (∀ d, r d < ofOrd α.1 ∨ r d = ⊤) ∧
      (∀ d, r (original R F (req d)) = R.p d) ∧
      (∀ d, r (original R F (priv d)) = R.vact d) ∧
      r (marked R F a) = ⊤ ∧ r (FinalGateApex.apex F card_eq) = ⊥ := by
  obtain ⟨a, δ, -, hlaw, hp, hc, hg, -, hbound⟩ :=
    OrdinaryFinalStage.exists_actual_display_at_stage R F α hP hC hfields hgate hgrid
      hsupport howners req priv hreq hpriv
  let p := fun d : F.carrier.below (Finset.univ, N) => δ (F.source a d.1)
  refine ⟨a, FinalGateApex.display F card_eq p,
    FinalGateApex.display_lawful F hD card_eq hlaw,
    FinalGateApex.display_bound F card_eq (fun d => hbound d.1), ?_, ?_, ?_,
    FinalGateApex.display_apex F card_eq p⟩
  · intro d
    exact (FinalGateApex.display_old F card_eq p (oldAt R F (req d) (hD _))).trans (hp d)
  · intro d
    exact (FinalGateApex.display_old F card_eq p (oldAt R F (priv d) (hD _))).trans (hc d)
  · exact (FinalGateApex.display_old F card_eq p (F.addedAt a true)).trans hg

/-- The original exact face survives both installations, in the same order. -/
def originalFace {m : ℕ} (T : SemScheme m) (f : Fin m ↪ Fin (N + 1))
    {B : Finset (Fin (N + 1))} (hB : Finset.univ.image f = B) (hne : B ≠ Finset.univ)
    (E : ExactSemanticFace (PointImageSemantics.rows T.scheme f hB T.rows) F.sem) :
    ExactSemanticFace (PointImageSemantics.rows T.scheme f hB T.rows)
      (FinalGateApex.rows F hD card_eq) :=
  FinalGateApex.properFace F hD card_eq
    (fun h => hne (Finset.Subset.antisymm (Finset.subset_univ _) h))
    (F.inheritedFace (Finset.subset_univ _) hne E)

theorem originalFace_order {m : ℕ} (T : SemScheme m) (f : Fin m ↪ Fin (N + 1))
    {B : Finset (Fin (N + 1))} (hB : Finset.univ.image f = B) (hne : B ≠ Finset.univ)
    (E : ExactSemanticFace (PointImageSemantics.rows T.scheme f hB T.rows) F.sem)
    (hE : StrictMono E.map) : StrictMono (originalFace R F hD T f hB hne E).map :=
  (FinalGateApex.old_order F card_eq).comp (F.old_strictMono.comp hE)

/-- Arbitrary lawful sections of the completed occurrence inventory retain
the capped readback theorem. The apex creates no additional chart hypothesis. -/
theorem capped_readback
    (hfields : ∀ a f, F.fields a f = a.val f) (hgate : F.gate = .gate)
    (req : Cell P.scheme ↪ Cell D) (priv : Cell C.scheme ↪ Cell D)
    (hreqGrade : ∀ d, D.grade (req d) = P.scheme.grade d)
    (hprivGrade : ∀ d, D.grade (priv d) = C.scheme.grade d)
    (hreq : ∀ a d, F.lower a (req d) = a.val (.req d))
    (hpriv : ∀ a d, F.lower a (priv d) = a.val (.priv d))
    {q : Cell (carrier R F) → ExtOrd}
    (hq : RespectsSemantics (FinalGateApex.rows F hD card_eq) q)
    (hretain : ∀ d, q (original R F (priv d)) = R.vact d)
    (b : OrdinaryFinalCatalogue.Member R) (hpositive : q (marked R F b) ≠ ⊥)
    (d : Cell P.scheme) :
    min (q (original R F (req d))) (R.cut R.vactL) = min (R.p d) (R.cut R.vactL) :=
  OrdinaryFinalReadback.capped_readback R F req priv hreqGrade hprivGrade hfields hgate hreq hpriv
    (FinalGateApex.restrict_lawful F hD card_eq hq) hretain b hpositive d

section Packaging

variable (hcons : F.sem.IsConsistent) (hcode : F.sem.IsCoded) (hb : F.rows.IsBountiful)
variable (hcomplete : ∀ J ∈ Plan.gradedPlan D.plan, J.2 ≤ N →
  J ≠ (Finset.univ, N) → ∃ d, D.cell d = J)
variable (hfields : ∀ a f, F.fields a f = a.val f)
variable (hgrid : F.grid = PairedSlotComparison.sourceGrid N (Fintype.card (Field P C)))
variable (hsupport : ∀ a d, D.grade d ≤ N →
  OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))

def stageType (α : Ordinal.{0}) (r : Cell (carrier R F) → ExtOrd)
    (hr : RespectsSemantics (FinalGateApex.rows F hD card_eq) r)
    (hbound : ∀ d, r d < ofOrd α ∨ r d = ⊤) : S α (N + 1) where
  scheme := semScheme R F hD hcons hcode hb hcomplete hfields hgrid hsupport
  label := r
  label_bound := hbound
  respects := hr

/-- The complete installed type restricts literally along an arbitrary
ordered original face, not just an initial-segment embedding. -/
theorem typeMap_original {α : Ordinal.{0}} {r : Cell (carrier R F) → ExtOrd}
    (hr : RespectsSemantics (FinalGateApex.rows F hD card_eq) r)
    (hbound : ∀ d, r d < ofOrd α ∨ r d = ⊤)
    {m : ℕ} (t : S α m) (f : Fin m ↪ Fin (N + 1))
    {B : Finset (Fin (N + 1))} (hB : Finset.univ.image f = B) (hne : B ≠ Finset.univ)
    (E : ExactSemanticFace (PointImageSemantics.rows t.scheme.scheme f hB t.scheme.rows) F.sem)
    (hE : StrictMono E.map)
    (hplan : Plan.restrictPlan D.plan B = t.scheme.scheme.plan.image (Finset.image f))
    (hlabel : ∀ d, r (original R F (E.map d)) = t.label d) :
    typeMap f (stageType R F hD hcons hcode hb hcomplete hfields hgrid hsupport α r hr hbound) =
      some t := by
  apply typeMap_of_pointImage_face _ t f hB
    (originalFace R F hD t.scheme f hB hne E)
    (originalFace_order R F hD t.scheme f hB hne E hE)
  · exact hplan
  · exact hlabel

/-- Conditional assembly of the complete selected type. Both ordered input
types are literal restrictions and a designated grade-N gate remains top.
The global predecessor and the final pair theorem have not been inferred. -/
theorem exists_selected_type (α : LimitStage)
    (hP : ∀ d, R.p d < ofOrd α.1 ∨ R.p d = ⊤)
    (hC : ∀ d, R.vact d < ofOrd α.1 ∨ R.vact d = ⊤)
    (hgate : F.gate = .gate)
    (howners : ∀ a (c : D.below (Finset.univ, N)),
      (∀ d : D.below (D.cell c.1), Short (D.grade c.1) (F.sem.E c.1 d)) ∨
      (∀ d : D.below (D.cell c.1), ∃ f : Field P C, F.lower a d.1 = a.val f))
    (fP : Fin (nP + 1) ↪ Fin (N + 1)) (fC : Fin N ↪ Fin (N + 1))
    {BP BC : Finset (Fin (N + 1))}
    (hBP : Finset.univ.image fP = BP) (hBC : Finset.univ.image fC = BC)
    (hneP : BP ≠ Finset.univ) (hneC : BC ≠ Finset.univ)
    (EP : ExactSemanticFace (PointImageSemantics.rows P.scheme fP hBP P.rows) F.sem)
    (EC : ExactSemanticFace (PointImageSemantics.rows C.scheme fC hBC C.rows) F.sem)
    (hEP : StrictMono EP.map) (hEC : StrictMono EC.map)
    (hplanP : Plan.restrictPlan D.plan BP = P.scheme.plan.image (Finset.image fP))
    (hplanC : Plan.restrictPlan D.plan BC = C.scheme.plan.image (Finset.image fC))
    (hreq : ∀ a d, F.lower a (EP.map d) = a.val (.req d))
    (hpriv : ∀ a d, F.lower a (EC.map d) = a.val (.priv d)) :
    ∃ t : S α.1 (N + 1),
      t.scheme = semScheme R F hD hcons hcode hb hcomplete hfields hgrid hsupport ∧
      typeMap fP t = some (⟨P, R.p, hP, R.p_respects⟩ : S α.1 (nP + 1)) ∧
      typeMap fC t = some (⟨C, R.vact, hC, R.vact_respects⟩ : S α.1 N) ∧
      ∃ g : Cell t.scheme.scheme, t.scheme.scheme.grade g = N ∧ t.label g = ⊤ := by
  have hshort : ∀ z ∈ F.grid, Short N z := by
    rw [hgrid]
    exact fun _ hz => CanonicalFieldLayer.grid_short N (Field P C) hz
  obtain ⟨a, r, hr, hbound, hPr, hCr, hgr, -⟩ := exists_installed_display R F hD α
    (fun d hd => (hP d).resolve_right hd) (fun d hd => (hC d).resolve_right hd)
    hfields hgate hshort hsupport howners EP.map EC.map hreq hpriv
  let t := stageType R F hD hcons hcode hb hcomplete hfields hgrid hsupport α.1 r hr hbound
  refine ⟨t, rfl, ?_, ?_, marked R F a, ?_, hgr⟩
  · exact typeMap_original R F hD hcons hcode hb hcomplete hfields hgrid hsupport hr hbound
      ⟨P, R.p, hP, R.p_respects⟩ fP hBP hneP EP hEP hplanP hPr
  · exact typeMap_original R F hD hcons hcode hb hcomplete hfields hgrid hsupport hr hbound
      ⟨C, R.vact, hC, R.vact_respects⟩ fC hBC hneC EC hEC hplanC hCr
  · change ((carrier R F).cell (marked R F a)).2 = N
    rw [marked, FinalGateApex.old_index, F.added_index]

end Packaging

end
end VaughtConjecture.Knight.OrdinaryFinalInstallation
