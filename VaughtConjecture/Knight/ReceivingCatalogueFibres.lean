/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingSupportedRepair

/-! # Constructed LOW/HIGH fibre repairs with supported inverse receipts

Consume the existing normalized same-grade fibres. Their numerical and
persistent receipts imply agreement on the complete canonical field inventory,
including future fields, gate and stored cutoff. The terminal repair producer
then constructs a proper catalogue member and a protected-grid inverse reading
the repaired prescription literally, even when it contains top.

These are the field-level repairs at a source-grid cut. They do not identify
an arbitrary physical ambient with a synchronized source state, or construct
the physical node and guard rows.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingCatalogueFibres
open Transform Value ExtOrd CappedDonor CappedDonor.Ref CanonicalPairedInverse
open ReceivingSupportedRepair
noncomputable section
variable {I : Type*} [Fintype I] {nP N J K j B : ℕ}
  {P : SemScheme (nP + 1)} {C : SemScheme J} {R : Ref I nP N J P C}
  {L : R.LowRef K}

/-- Present numerical fields and future persistent fields use different
receipts. Neither support flags nor capped maxima substitute for this vector. -/
theorem profile_cap {S T : R.TState j} {γ : ExtOrd}
    (hu : ∀ d, min (T.st.u d) γ = min (S.st.u d) γ)
    (hv : ∀ d, min (T.st.v d) γ = min (S.st.v d) γ)
    (hrec : R.CapReceipts γ S.st T.st) (hb : min T.b γ = min S.b γ) :
    ∀ f, min (T.profile f) γ = min (S.profile f) γ := by
  intro f
  cases f with
  | cutoff => exact hb
  | field f =>
    change min (T.st.sourceProfile f) γ = min (S.st.sourceProfile f) γ
    by_cases hf : f.grade ≤ j
    · rw [State.sourceProfile_of_present _ hf, State.sourceProfile_of_present _ hf]
      cases f with
      | req d => exact hu _
      | priv d => exact hv _
      | gate => exact hrec.1
    · rw [State.sourceProfile_of_future _ hf, State.sourceProfile_of_future _ hf]
      exact (capReceipts_iff γ S.st T.st).mp hrec f

/-- The private fibre's repair, canonical insertion and prefix-fixing decoder
are all constructed from the actual lawful private prescription. -/
theorem exists_private_repair (hj : 1 ≤ j) {S : R.TState j}
    (hS : L.TAdmissible S) (hs : Synchronized S.st)
    (hcanonical : S.profile ∈ CanonicalPairedProfiles.inventory (TField P C) j)
    {v : C.scheme.below (effC J j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC J j) v)
    (hag : ∀ d, min (v d) (grid j B) = min (S.st.v d) (grid j B)) :
    ∃ T : R.TState j, L.TAdmissible T ∧ Synchronized T.st ∧ T.st.v = v ∧
      (∀ f, min (T.profile f) (grid j B) = min (S.profile f) (grid j B)) ∧
      Nonempty (Repair L S.profile T B) := by
  have hγ : SelfVis (effC J j).2 (grid j B) :=
    selfVis_mono (grid_visible j B) (min_le_left j J)
  obtain ⟨T, hT, hsT, hvT, huT, hrec, hb, _⟩ :=
    L.exists_private_lift_normalized hj hS hs hv hγ hag
  have hcap := profile_cap huT (fun d => by rw [hvT]; exact hag d) hrec hb
  exact ⟨T, hT, hsT, hvT, hcap,
    exists_repair hj hcanonical hT hsT (fun d => (hcap d).symm)⟩

/-- The request fibre has the same complete-inventory and supported-prefix
receipt, without imposing owner domination or excluding literal top. -/
theorem exists_request_repair (hj : 1 ≤ j) {S : R.TState j}
    (hS : L.TAdmissible S) (hs : Synchronized S.st)
    (hcanonical : S.profile ∈ CanonicalPairedProfiles.inventory (TField P C) j)
    {u : P.scheme.below (effP nP j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effP nP j) u)
    (hag : ∀ d, min (u d) (grid j B) = min (S.st.u d) (grid j B)) :
    ∃ T : R.TState j, L.TAdmissible T ∧ Synchronized T.st ∧ T.st.u = u ∧
      (∀ f, min (T.profile f) (grid j B) = min (S.profile f) (grid j B)) ∧
      Nonempty (Repair L S.profile T B) := by
  have hγ : SelfVis (effC J j).2 (grid j B) :=
    selfVis_mono (grid_visible j B) (min_le_left j J)
  obtain ⟨T, hT, hsT, huT, hvT, hrec, hb, _⟩ :=
    L.exists_request_lift_normalized hj hS hs hu hγ hag
  have hcap := profile_cap (fun d => by rw [huT]; exact hag d) hvT hrec hb
  exact ⟨T, hT, hsT, huT, hcap,
    exists_repair hj hcanonical hT hsT (fun d => (hcap d).symm)⟩

end
end VaughtConjecture.Knight.ReceivingCatalogueFibres
