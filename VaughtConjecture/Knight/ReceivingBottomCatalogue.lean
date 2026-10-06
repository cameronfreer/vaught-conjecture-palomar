/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RequestCatalogueRepair

/-! # Independent bottom-cap catalogue supply on both original faces

At bottom cap no source prefix is protected. Use the proved bottom fibres,
resynchronize the source state, and construct terminal-block decoding into the
same canonical catalogue. This does not use positive-cap transport and does
not assert lawfulness of decoding a still-unconstructed physical renderer.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingBottomCatalogue
open Transform Value ExtOrd CappedDonor CappedDonor.Ref ReceivingSupportedRepair
noncomputable section
variable {I : Type*} [Fintype I] {nP N J K j : ℕ}
  {P : SemScheme (nP + 1)} {C : SemScheme J} {R : Ref I nP N J P C}
  {L : R.LowRef K}

/-- Constructed exact decoding of an entire source state. Unlike active repair,
there is no preserved grid cut or owner clipping in this bottom-cap output. -/
structure Insertion (T : R.TState j) where
  encoded : R.TState j
  admitted : L.TAdmissible encoded
  synchronized : Synchronized encoded.st
  canonical : encoded.profile ∈ CanonicalPairedProfiles.inventory (TField P C) j
  decoder : ExtOrd → ExtOrd
  witness : Witness (gTop j) decoder
  readback : ∀ f, decoder (encoded.profile f) = T.profile f

/-- Literal-top handling moves tops into a fresh terminal block before
normalization and collapses the whole block afterward. No protected extra grid
is needed here: the external cap is bottom. -/
theorem exists_insertion (hj : 1 ≤ j) {T : R.TState j}
    (hT : L.TAdmissible T) (hs : Synchronized T.st) : Nonempty (Insertion (L := L) T) := by
  obtain ⟨l, β, _, hβdef, hβ, hcap, hproper, _, δ, hδ, hread⟩ :=
    L.exists_terminal_decoding hj hT 0
  let V := mapT (fun x => min x β) T
  have hbot : β ≠ ⊥ := by rw [hβdef]; exact ofOrd_ne_bot _
  have hsV : Synchronized V.st := hs.map (capWitness hβ hbot) hj
  refine ⟨{
    encoded := normalizeT V
    admitted := L.normalizeT_tadmissible hj hcap
    synchronized := normalizeT_synchronized hj hsV
    canonical := ?_
    decoder := δ
    witness := hδ
    readback := hread }⟩
  have he : (normalizeT V).profile = PairedSlotEncoding.normalize j V.profile :=
    funext (profile_normalizeT V)
  rw [he]
  exact CanonicalPairedProfiles.normalize_mem_inventory _ _ hproper

namespace Insertion
variable {T : R.TState j} (r : Insertion (L := L) T)

theorem catalogue : r.encoded.profile ∈ Catalogue (j := j) L :=
  ⟨r.canonical, r.encoded, r.admitted, r.synchronized, rfl⟩

theorem private_readback (d : C.scheme.below (effC J j)) :
    r.decoder (r.encoded.st.v d) = T.st.v d := by
  rw [← PrivateCatalogueRepair.profile_private r.encoded d, r.readback,
    PrivateCatalogueRepair.profile_private]

theorem request_readback (d : P.scheme.below (effP nP j)) :
    r.decoder (r.encoded.st.u d) = T.st.u d := by
  rw [← RequestCatalogueRepair.profile_request r.encoded d, r.readback,
    RequestCatalogueRepair.profile_request]

/-- Persistent observations are recovered on source states, not identified
with the numerical labels of arbitrary physical sections. -/
theorem persistent_readback (hj : 1 ≤ j) (hs : Synchronized T.st) (f : Field P C) :
    r.decoder (r.encoded.st.persistent f) = T.st.persistent f := by
  rw [r.synchronized f, hs f,
    r.witness.clause5 _ 1 (by rw [gTop_of_le hj]; exact le_top) 1 le_rfl]
  exact congrArg (fun x => extVisibilityReplace x 1 1) (r.readback (.field f))

end Insertion

/-- Independent private-face section supply, including active owner values and
literal top. No canonical old source or source-placement premise is needed. -/
theorem exists_private_section (hj : 1 ≤ j) {S : R.TState j}
    (hS : L.TAdmissible S) {p : C.scheme.below (effC J j) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC J j) p) :
    ∃ T : R.TState j, T.st.v = p ∧ L.TAdmissible T ∧ Synchronized T.st ∧
      Nonempty (Insertion (L := L) T) := by
  obtain ⟨T, hT, hread, _⟩ := L.exists_private_lift_bot hS hp
  let U : R.TState j := ⟨resync T.st, T.b⟩
  have hU : L.TAdmissible U := hT.resync
  have hsU : Synchronized U.st := resync_synchronized hT.adm
  exact ⟨U, hread, hU, hsU, exists_insertion hj hU hsU⟩

/-- The request direction consumes its own proved bottom fibre, not a face
exchange. The complete encoded inventory remains `TField P C`. -/
theorem exists_request_section (hj : 1 ≤ j) {S : R.TState j}
    (hS : L.TAdmissible S) {p : P.scheme.below (effP nP j) → ExtOrd}
    (hp : RespectsSemanticsBelow P.rows (effP nP j) p) :
    ∃ T : R.TState j, T.st.u = p ∧ L.TAdmissible T ∧ Synchronized T.st ∧
      Nonempty (Insertion (L := L) T) := by
  obtain ⟨T, hT, hread, _⟩ := L.exists_request_lift_bot hS hp
  let U : R.TState j := ⟨resync T.st, T.b⟩
  have hU : L.TAdmissible U := hT.resync
  have hsU : Synchronized U.st := resync_synchronized hT.adm
  exact ⟨U, hread, hU, hsU, exists_insertion hj hU hsU⟩

end
end VaughtConjecture.Knight.ReceivingBottomCatalogue
