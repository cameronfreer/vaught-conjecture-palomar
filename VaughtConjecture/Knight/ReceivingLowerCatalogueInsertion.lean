/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingGradeOnePhysicalChart
public import VaughtConjecture.Knight.SameScopeBountiful

/-! # Lower private prescriptions inserted into the installed catalogue

At a grade-two-visible source-grid cut, a lawful private grade-one prescription
has a constructed grade-two old extension. The grade-two fibre and supported
insertion then produce an actual installed controller, exact lower field
readback, and the entire physical rank prefix. This is not upward admission of
an arbitrary grade-one state: every other field may be repaired above the cut.

The source-grid cap concerns the underlying grade-two field profile, not the
physical rank-coded row or its external agreement cap. Deriving this input from
an arbitrary active physical lifting query remains a separate obligation.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingLowerCatalogueInsertion
open Transform Value ExtOrd CappedDonor CappedDonor.Ref ReceivingLadderCarrier
open ReceivingCatalogueSources CanonicalPairedInverse ReceivingSupportedRepair
noncomputable section

variable {I : Type*} [Fintype I] {nP K : ℕ} {P : SemScheme (nP + 1)}
  {C : SemScheme 2} {R : Ref I nP 2 2 P C} (L : R.LowRef K)

/-- The same literal private occurrence at the two effective cutoffs. -/
def privateUp (d : C.scheme.below (effC 2 1)) : C.scheme.below (effC 2 2) :=
  ⟨d.1, d.2.1, d.2.2.trans (by decide : min 1 2 ≤ min 2 2)⟩

/-- Construct the higher old section before calling the higher fibre. No
whole completion, higher admission, or new-carrier lifting is an input. -/
theorem exists_repair (a : Controller L) (B : ℕ)
    {p : C.scheme.below (effC 2 1) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC 2 1) p)
    (hag : ∀ d, min (p d) (CanonicalPairedInverse.grid 2 B) =
      min (fields L a (privateField d.1)) (CanonicalPairedInverse.grid 2 B)) :
    ∃ T : R.TState 2, L.TAdmissible T ∧ Synchronized T.st ∧
      (∀ d, T.st.v (privateUp d) = p d) ∧
      (∀ f, min (T.profile f) (CanonicalPairedInverse.grid 2 B) =
        min (fields L a f) (CanonicalPairedInverse.grid 2 B)) ∧
      Nonempty (Repair L (fields L a) T B) := by
  let h : GradedLe (effC 2 1) (effC 2 2) := ⟨Finset.Subset.refl _, by decide⟩
  have hread (d : C.scheme.below (effC 2 1)) :
      (state L a).st.v (CellScheme.below.mono h d) = fields L a (privateField d.1) := by
    rw [← state_profile]
    exact (PrivateCatalogueRepair.profile_private (state L a) (privateUp d)).symm
  obtain ⟨v, hv, hv_cap, hv_low⟩ := bountiful_same_scope C.rows h p (state L a).st.v
    (CanonicalPairedInverse.grid 2 B) hp (state_admitted L a).adm.v_respects
    (CanonicalPairedInverse.grid_visible 2 B) (fun d =>
      (congrArg (fun x => min x (CanonicalPairedInverse.grid 2 B)) (hread d)).trans (hag d).symm)
  obtain ⟨T, hT, hsT, hTv, hcap, hr⟩ := ReceivingCatalogueFibres.exists_private_repair
    (L := L) (by decide : 1 ≤ 2) (state_admitted L a) (state_synchronized L a)
    (by rw [state_profile]; exact a.property.1) hv hv_cap
  refine ⟨T, hT, hsT, ?_, ?_, ?_⟩
  · intro d
    rw [hTv]
    exact hv_low d
  · intro f
    exact (hcap f).trans (congrArg (fun x => min x (CanonicalPairedInverse.grid 2 B))
      (congrFun (state_profile L a) f))
  · simpa only [state_profile] using hr

variable (hC : C.scheme.plan = privatePlan) (request : Cell P.scheme)
local notation "D" => carrier L hC
local notation "ℓ" => rungs (P := P) (C := C)

/-- An actual leaf index and its outgoing field decoder are constructed in
the frozen grade-two catalogue. All unused rungs and both scope copies retain
their rank-coded source prefix. Field readback is not identified with decoding
the rank-coded row by the same map. -/
theorem exists_anchor (a : Controller L) (B : ℕ)
    {p : C.scheme.below (effC 2 1) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC 2 1) p)
    (hag : ∀ d, min (p d) (CanonicalPairedInverse.grid 2 B) =
      min (fields L a (privateField d.1)) (CanonicalPairedInverse.grid 2 B)) :
    ∃ b : Controller L, ∃ κ k, Witness (gTop 2) κ ∧
      (∀ d, κ (fields L b (privateField d.1)) = p d) ∧
      (∀ f, min (fields L b f) (CanonicalPairedInverse.grid 2 B) =
        min (fields L a f) (CanonicalPairedInverse.grid 2 B)) ∧
      (∀ f, min (κ (fields L b f)) (CanonicalPairedInverse.grid 2 B) =
        min (fields L a f) (CanonicalPairedInverse.grid 2 B)) ∧
      0 < k ∧ k ≤ ℓ ∧ FiniteProfileControllers.Agree (ranks L a) (ranks L b) k ∧
      ∀ d : Cell D,
        min (ReceivingGradeOnePhysicalChart.lowerSource L hC request b d)
            (SupportLadderRows.source ℓ k) =
          min (ReceivingGradeOnePhysicalChart.lowerSource L hC request a d)
            (SupportLadderRows.source ℓ k) := by
  obtain ⟨T, _, _, hlow, hcap, ⟨r⟩⟩ := exists_repair L a B hp hag
  let b : Controller L := ⟨r.encoded.profile, r.catalogue⟩
  let k := LadderScalarRendering.next (LadderScalarRendering.values (fields L a))
    (CanonicalPairedInverse.grid 2 B)
  have hkpos : 0 < k := Nat.succ_pos _
  have hkbound : k ≤ ℓ := (LadderScalarRendering.next_le _ _).trans
    (Nat.add_le_add_right (LadderScalarRendering.values_card_le _) 1)
  have hfields (f) : min (fields L a f) (CanonicalPairedInverse.grid 2 B) =
      min (fields L b f) (CanonicalPairedInverse.grid 2 B) := (r.prefix_eq f).symm
  have hδ : ⊥ < CanonicalPairedInverse.grid 2 B :=
    bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)
  have hranks : FiniteProfileControllers.Agree (ranks L a) (ranks L b) k :=
    LadderScalarRendering.fieldRank_agreement hδ hfields
  have hcut := FiniteProfileControllers.le_cut hkbound hranks
  refine ⟨b, r.decoder, k, r.witness, ?_, fun f => (hfields f).symm,
    ?_, hkpos, hkbound, hranks, ?_⟩
  · intro d
    exact (r.readback (privateField d.1)).trans
      ((PrivateCatalogueRepair.profile_private T (privateUp d)).trans (hlow d))
  · intro f
    exact (congrArg (fun x => min x (CanonicalPairedInverse.grid 2 B))
      (r.readback f)).trans (hcap f)
  · intro d
    have he := congrArg (fun n => min n k)
      (lowerIndex_agreement C.scheme hC privateField (.field (.req request)) (ranks L) a b d)
    simp only [min_assoc, min_eq_right hcut] at he
    change min (SupportLadderRows.source ℓ _) (SupportLadderRows.source ℓ k) =
      min (SupportLadderRows.source ℓ _) (SupportLadderRows.source ℓ k)
    rw [← (SupportLadderRows.source_mono ℓ).map_min,
      ← (SupportLadderRows.source_mono ℓ).map_min, he]

end
end VaughtConjecture.Knight.ReceivingLowerCatalogueInsertion
