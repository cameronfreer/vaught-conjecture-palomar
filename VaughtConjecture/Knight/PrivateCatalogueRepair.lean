/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PrivateRowFactorization
public import VaughtConjecture.Knight.ReceivingCatalogueFibres

/-! # Owner factorization followed by LOW/HIGH catalogue repair

The old source is a catalogue state, not the arbitrary physical ambient. Its
actual chart and a lawful private prescription construct the repaired source,
the same-grade fibre, canonical insertion, and outgoing bounded decoder.
No new source rows are added to the catalogue.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.PrivateCatalogueRepair
open Transform Value ExtOrd CappedDonor CappedDonor.Ref CanonicalPairedInverse
open SharpWitnessComposition ReceivingSupportedRepair
noncomputable section

variable {I : Type*} [Fintype I] {nP N J K j : ℕ}
  {P : SemScheme (nP + 1)} {C : SemScheme J} {R : Ref I nP N J P C}
  {L : R.LowRef K}

/-- A full-scope actual owner has exactly the effective private lower domain.
The arity bound follows from the old scheme, not an extra geometry premise. -/
theorem owner_index (c : Cell C.scheme) (hc : C.scheme.scope c = Finset.univ) :
    C.scheme.cell c = effC J (C.scheme.grade c) := by
  apply Prod.ext
  · exact hc
  · exact (min_eq_left (gradeC_le c)).symm

/-- Numerical readback at every actual present private occurrence. -/
theorem profile_private (S : R.TState j) (d : C.scheme.below (effC J j)) :
    S.profile (.field (.priv d.1)) = S.st.v d := by
  change S.st.sourceProfile (.priv d.1) = _
  rw [State.sourceProfile_of_present _ ((present_priv_iff j d.1).mp d.2)]
  rfl

/-- Push an equal source prefix through the outgoing map, retaining the
external cap. In particular the source cut need not equal the output cap. -/
theorem cap_of_prefix {ν : ExtOrd → ExtOrd} (hν : Monotone ν)
    {δ γ x y : ExtOrd} (hr : γ ≤ ν δ) (he : min y δ = min x δ) :
    min (ν y) γ = min (ν x) γ := by
  have h (z) : min (ν (min z δ)) γ = min (ν z) γ := by
    rw [hν.map_min, min_assoc, min_eq_right hr]
  exact (h y).symm.trans ((congrArg (fun z => min (ν z) γ) he).trans (h x))

/-- Constructed source-level output. Physical rendering and literal lower
restoration are separate: this decoder reads the prescription capped at `M`. -/
structure Result (S : R.TState j) (p : C.scheme.below (effC J j) → ExtOrd)
    (σ : ExtOrd → ExtOrd) (γ M : ExtOrd) where
  original_canonical : S.profile ∈ CanonicalPairedProfiles.inventory (TField P C) j
  cap_pos : ⊥ < γ
  cap_lt_owner : γ < M
  owner_visible : SelfVis j M
  block : ℕ
  cut_mem : grid j block ∈ PairedSlotComparison.sourceGrid j (Fintype.card (TField P C))
  first_reach : γ ≤ σ (grid j block)
  first_minimal : ∀ z ∈ PairedSlotComparison.sourceGrid j (Fintype.card (TField P C)),
    z < grid j block → σ z < γ
  repaired : R.TState j
  admitted : L.TAdmissible repaired
  synchronized : Synchronized repaired.st
  field_caps : ∀ f, min (repaired.profile f) (grid j block) =
    min (S.profile f) (grid j block)
  insertion : Repair L S.profile repaired block
  outer : ExtOrd → ExtOrd
  outer_witness : Witness (gTop j) outer
  outer_bound : ∀ x, outer x ≤ M
  private_readback : ∀ d, outer (repaired.st.v d) = min (p d) M
  outer_reaches : γ ≤ outer (grid j block)
  outer_caps : ∀ x, Short j x → min (outer x) γ = min (σ x) γ

namespace Result
variable {S : R.TState j} {p : C.scheme.below (effC J j) → ExtOrd}
  {σ : ExtOrd → ExtOrd} {γ M : ExtOrd}
  (r : Result (L := L) S p σ γ M)

def decoder : ExtOrd → ExtOrd := r.outer ∘ r.insertion.decoder

theorem decoder_bounded : BoundedMap j r.decoder :=
  bounded_comp r.insertion.witness r.outer_witness le_rfl

theorem decoder_bound (x : ExtOrd) : r.decoder x ≤ M := r.outer_bound _

theorem catalogue : r.insertion.encoded.profile ∈ Catalogue (j := j) L :=
  r.insertion.catalogue

theorem readback (d : C.scheme.below (effC J j)) :
    r.decoder (r.insertion.encoded.st.v d) = min (p d) M := by
  rw [← profile_private r.insertion.encoded d]
  change r.outer (r.insertion.decoder _) = _
  rw [r.insertion.readback, profile_private]
  exact r.private_readback d

theorem readback_of_le (d : C.scheme.below (effC J j)) (hd : p d ≤ M) :
    r.decoder (r.insertion.encoded.st.v d) = p d := by
  rw [r.readback, min_eq_left hd]

/-- Whole-vector scalar consequence for the physical renderer. Both hypotheses
concern actual source coordinates; neither is an assumed cap equation for the
outgoing decoder. Unsupported invisible values are deliberately excluded. -/
theorem auxiliary_caps {Y : Type*} {u v : Y → ExtOrd}
    (hs : ∀ y, OrbitPrefixSupport.Supported j
      (PairedSlotComparison.sourceGrid j (Fintype.card (TField P C)) : Set ExtOrd)
      S.profile (u y))
    (hshort : ∀ y, Short j (u y))
    (he : ∀ y, min (v y) (grid j r.block) = min (u y) (grid j r.block)) :
    ∀ y, min (r.decoder (v y)) γ = min (σ (u y)) γ := by
  intro y
  exact (cap_of_prefix r.outer_witness.mono r.outer_reaches
    (r.insertion.auxiliary_caps hs he y)).trans (r.outer_caps _ (hshort y))

/-- Every complete-field cap survives insertion and outgoing decoding. This
includes future fields, gate and cutoff, not merely the private prescription. -/
theorem complete_field_caps (f : TField P C) :
    min (r.decoder (r.insertion.encoded.profile f)) γ = min (σ (S.profile f)) γ := by
  change min (r.outer (r.insertion.decoder _)) γ = _
  rw [r.insertion.readback]
  exact (cap_of_prefix r.outer_witness.mono r.outer_reaches (r.field_caps f)).trans
    (r.outer_caps _ (CanonicalPairedProfiles.inventory_short _ _ r.original_canonical f))

/-- All designated grid points, including unused ones, retain their original
external-cap readings through the composite decoder. -/
theorem grid_caps {x : ExtOrd}
    (hx : x ∈ PairedSlotComparison.sourceGrid j (Fintype.card (TField P C))) :
    min (r.decoder x) γ = min (σ x) γ := by
  have hs : Short j x := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inl rfl
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
      exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)
  exact r.auxiliary_caps (u := fun _ : Unit => x) (v := fun _ => x)
    (fun _ => Or.inr (Or.inl hx)) (fun _ => hs) (fun _ => rfl) ()

/-- Hosted finite-part orbit points need not themselves be used as fields.
Only capped readings, not uncapped invisible plateau readings, are retained. -/
theorem orbit_caps (f : TField P C) {i : ℕ} (hi : i ≤ j) :
    min (r.decoder (extVisibilityReplace (S.profile f) j i)) γ =
      min (σ (extVisibilityReplace (S.profile f) j i)) γ := by
  have hs := PrivateRowFactorization.short_replace
    (CanonicalPairedProfiles.inventory_short _ _ r.original_canonical f) le_rfl hi
  exact r.auxiliary_caps
    (u := fun _ : Unit => extVisibilityReplace (S.profile f) j i) (v := fun _ => _)
    (fun _ => Or.inr (Or.inr ⟨f, i, hi, rfl⟩)) (fun _ => hs) (fun _ => rfl) ()

/-- The composite need not be globally faithful. A faithful witness with the
same readings on all short sources is nevertheless constructed. -/
theorem exists_short_witness : ∃ τ, Witness (gTop j) τ ∧
    ∀ x, Short j x → τ x = r.decoder x := by
  exact comp_read (σ := r.insertion.decoder) (ν := r.outer)
    r.insertion.witness r.outer_witness le_rfl

end Result

/-- Owner-local factorization, the private LOW/HIGH fibre, normalization and
protected inversion, starting from the actual old source and lawful input.
The owner need only be full-scope; it need not be the distinguished receiving
owner. Literal top and long original semantic rows are permitted. -/
theorem exists_repair (c : Cell C.scheme) (hc : C.scheme.scope c = Finset.univ)
    {S : R.TState (C.scheme.grade c)} (hS : L.TAdmissible S)
    (hs : Synchronized S.st)
    (ha : S.profile ∈ CanonicalPairedProfiles.inventory (TField P C) (C.scheme.grade c))
    {p : C.scheme.below (effC J (C.scheme.grade c)) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC J (C.scheme.grade c)) p)
    {σ : ExtOrd → ExtOrd} {γ : ExtOrd}
    (hσ : Witness (gTop (C.scheme.grade c)) σ) (hγ : SelfVis (C.scheme.grade c) γ)
    (hpos : ⊥ < γ) (hpc : γ < p (privCell c le_rfl))
    (hag : ∀ d, min (σ (S.st.v d)) γ = min (p d) γ) :
    Nonempty (Result (L := L) S p σ γ (p (privCell c le_rfl))) := by
  classical
  have hi := owner_index c hc
  let toEff := CellScheme.below.mono (D := C.scheme) (show GradedLe (C.scheme.cell c)
    (effC J (C.scheme.grade c)) from hi ▸ GradedLe.refl _)
  let fromEff := CellScheme.below.mono (D := C.scheme) (show GradedLe (effC J (C.scheme.grade c))
    (C.scheme.cell c) from hi ▸ GradedLe.refl _)
  let s := S.st.v ∘ toEff
  let p' := p ∘ toEff
  have hs' : RespectsSemanticsBelow C.rows (C.scheme.cell c) s :=
    hS.adm.v_respects.mono _
  have hp' : RespectsSemanticsBelow C.rows (C.scheme.cell c) p' := hp.mono _
  have hsread (e : C.scheme.below (C.scheme.cell c)) :
      s e = S.profile (.field (.priv e.1)) := (profile_private S (toEff e)).symm
  obtain ⟨δ, hδ, hδpos, hreach, hfirst, ⟨F⟩⟩ :=
    PrivateRowFactorization.exists_factorization c (Fintype.card (TField P C)) hs' hp'
      (fun e => by rw [hsread]; exact CanonicalPairedProfiles.inventory_coded _ _ ha _)
      (fun e => by rw [hsread]; exact CanonicalPairedProfiles.inventory_short _ _ ha _)
      hσ hγ hpos hpc (fun e => hag (toEff e))
  rcases Finset.mem_insert.mp hδ with hδbot | hδgrid
  · exact (not_lt_of_ge (le_of_eq hδbot) hδpos).elim
  obtain ⟨B, hBmem, hB⟩ := Finset.mem_image.mp hδgrid
  change grid (C.scheme.grade c) B = δ at hB
  subst δ
  let v := F.source ∘ fromEff
  have hv : RespectsSemanticsBelow C.rows (effC J (C.scheme.grade c)) v := F.lawful.mono _
  have hvprefix (d) : min (v d) (grid (C.scheme.grade c) B) =
      min (S.st.v d) (grid (C.scheme.grade c) B) := F.prefix_eq (fromEff d)
  obtain ⟨T, hT, hsT, hvT, hTcap, ⟨ins⟩⟩ :=
    ReceivingCatalogueFibres.exists_private_repair (C.scheme.grade_pos c) hS hs ha hv hvprefix
  refine ⟨{
    original_canonical := ha
    cap_pos := hpos
    cap_lt_owner := hpc
    owner_visible := (hp.orderly (privCell c le_rfl)).symm
    block := B
    cut_mem := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨B, hBmem, rfl⟩)
    first_reach := hreach
    first_minimal := hfirst
    repaired := T
    admitted := hT
    synchronized := hsT
    field_caps := hTcap
    insertion := ins
    outer := F.outgoing
    outer_witness := F.witness
    outer_bound := F.bounded
    private_readback := ?_
    outer_reaches := F.reaches
    outer_caps := F.caps }⟩
  intro d
  rw [hvT]
  exact F.readback (fromEff d)

end
end VaughtConjecture.Knight.PrivateCatalogueRepair
