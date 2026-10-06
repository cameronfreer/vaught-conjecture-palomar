/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowHighNormalization
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.PairedSlotComparison
public import VaughtConjecture.Knight.OrbitPrefixSupport

/-! # LOW/HIGH catalogue insertion with a protected-grid terminal inverse

The repaired receiving state may contain literal top. Retarget its terminal
block above the protected source cut, normalize the complete field inventory,
then compose the supported inverse with whole-block collapse. The resulting
catalogue member is admissible, and the decoder fixes retained grid endpoints
and supported low orbits. No identity on unhosted invisible points is asserted.
This is a source-family producer, not a physical guarded-carrier construction.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingSupportedRepair
open Transform Value ExtOrd CappedDonor CappedDonor.Ref
open CanonicalPairedInverse
noncomputable section

variable {I : Type*} [Fintype I] {nP N J K j B : ℕ}
  {P : SemScheme (nP + 1)} {C : SemScheme J} {R : Ref I nP N J P C}
  (L : R.LowRef K)

/-- The receiving catalogue uses the entire field vector, cutoff included. -/
def Catalogue : Set (TField P C → ExtOrd) :=
  {a | a ∈ CanonicalPairedProfiles.inventory (TField P C) j ∧
    ∃ S : R.TState j, L.TAdmissible S ∧ Synchronized S.st ∧ S.profile = a}

theorem catalogue_finite : (Catalogue (j := j) L).Finite :=
  (CanonicalPairedProfiles.inventory_finite (TField P C) j).subset (fun _ h => h.1)

/-- Future fields are counted even before their numerical owners appear. -/
theorem field_count : Fintype.card (TField P C) =
    Fintype.card (Cell P.scheme) + Fintype.card (Cell C.scheme) + 2 := by
  rw [Fintype.card_congr TField.equivSum, Fintype.card_sum,
    Fintype.card_congr Field.equivSum, Fintype.card_sum, Fintype.card_sum]
  simp only [Fintype.card_unit]
  omega

/-- Constructed insertion data; this record is an output, not a completion premise. -/
structure Repair (a : TField P C → ExtOrd) (S : R.TState j) (B : ℕ) where
  encoded : R.TState j
  admissible : L.TAdmissible encoded
  synchronized : Synchronized encoded.st
  canonical : encoded.profile ∈ CanonicalPairedProfiles.inventory (TField P C) j
  prefix_eq : ∀ d, min (encoded.profile d) (grid j B) = min (a d) (grid j B)
  decoder : ExtOrd → ExtOrd
  witness : Witness (gTop j) decoder
  readback : ∀ d, decoder (encoded.profile d) = S.profile d
  grid_fixed : ∀ b < B, decoder (grid j b) = grid j b
  reaches : grid j B ≤ decoder (grid j B)
  boundary_fixed : ∀ d, a d < grid j B → decoder (a d) = a d

variable {L}

/-- Construct the missing terminal inverse at the original source-grid cut.
The protected points include unused endpoints, not just represented fields. -/
theorem exists_repair (hj : 1 ≤ j) {a : TField P C → ExtOrd}
    (ha : a ∈ CanonicalPairedProfiles.inventory (TField P C) j)
    {S : R.TState j} (hS : L.TAdmissible S) (hs : Synchronized S.st)
    (hag : ∀ d, min (a d) (grid j B) = min (S.profile d) (grid j B)) :
    Nonempty (Repair L a S B) := by
  let h : Ordinal.{0} := Ordinal.omega0 * B + j
  let l := S.freshFloor h
  let β : ExtOrd := ofOrd (l + j)
  have hlim : limitPart l = l := S.freshFloor_limit h
  have hh : grid j B < ofOrd l := ofOrd_lt_ofOrd.mpr (S.h_lt_freshFloor h)
  have hβ : SelfVis j β := by
    apply selfVis_ofOrd_iff.mpr
    have he := finitePart_limitPart_add_nat l j
    rw [hlim] at he
    exact he.ge
  have hlβ : ofOrd l ≤ β := ofOrd_le_ofOrd.mpr le_self_add
  have hcutβ : grid j B ≤ β := hh.le.trans hlβ
  let V := mapT (fun x => min x β) S
  have hV : L.TAdmissible V :=
    hS.map (capWitness hβ (ofOrd_ne_bot _)) L (min_le_left j J) hj
      (capWitness_reflects_bottom (ofOrd_ne_bot _))
  have hsV : Synchronized V.st := hs.map (capWitness hβ (ofOrd_ne_bot _)) hj
  have hproper : ∀ d, V.profile d ≠ ⊤ := by
    intro d
    rw [profile_mapT]
    exact fun ht => ofOrd_ne_top _ (min_eq_top.mp ht).2
  have hagV : ∀ d, min (a d) (grid j B) = min (V.profile d) (grid j B) := by
    intro d
    rw [profile_mapT, min_assoc, min_eq_right hcutβ]
    exact hag d
  obtain ⟨κ, hw, hread, hfix, hreach, _⟩ :=
    exists_supported_inverse ha hproper hagV
  let Q := normalizeT V
  have hQ : Q.profile ∈ CanonicalPairedProfiles.inventory (TField P C) j := by
    have he : Q.profile = PairedSlotEncoding.normalize j V.profile :=
      funext (profile_normalizeT V)
    rw [he]
    exact CanonicalPairedProfiles.normalize_mem_inventory (TField P C) j hproper
  have hprefix : ∀ d, min (Q.profile d) (grid j B) = min (a d) (grid j B) := by
    intro d
    rw [profile_normalizeT]
    exact CanonicalPairedProfiles.normalize_cap (TField P C) j ha hagV d
  let δ := collapseBlock l ∘ κ
  have hδ : Witness (gTop j) δ :=
    Witness.comp_of_bottom_reflecting hw (collapseBlock_witness j hlim) le_rfl
      (collapseBlock_reflects_bottom l)
  have hδread (d) : δ (Q.profile d) = S.profile d := by
    dsimp only [δ, Function.comp_apply]
    rw [profile_normalizeT, hread, profile_mapT]
    exact collapseBlock_min hlβ (S.profile_lt_freshFloor h d)
  have hδfix (b : ℕ) (hb : b < B) : δ (grid j b) = grid j b := by
    dsimp only [δ, Function.comp_apply]
    rw [hfix b hb]
    apply collapseBlock_of_lt
    apply lt_of_le_of_lt _ hh
    exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl)
  have hδreach : grid j B ≤ δ (grid j B) := by
    calc
      grid j B = collapseBlock l (grid j B) := (collapseBlock_of_lt hh).symm
      _ ≤ collapseBlock l (κ (grid j B)) := (collapseBlock_witness j hlim).mono hreach
  refine ⟨{
    encoded := Q
    admissible := L.normalizeT_tadmissible hj hV
    synchronized := normalizeT_synchronized hj hsV
    canonical := hQ
    prefix_eq := hprefix
    decoder := δ
    witness := hδ
    readback := hδread
    grid_fixed := hδfix
    reaches := hδreach
    boundary_fixed := ?_
  }⟩
  intro d hd
  have hqa : a d = Q.profile d := PairedSlotEncoding.eq_of_cap_eq_lt (hprefix d).symm hd
  have hpa : a d = S.profile d := PairedSlotEncoding.eq_of_cap_eq_lt (hag d) hd
  calc
    δ (a d) = δ (Q.profile d) := congrArg δ hqa
    _ = S.profile d := hδread d
    _ = a d := hpa.symm

namespace Repair
variable {a : TField P C → ExtOrd} {S : R.TState j} (r : Repair L a S B)

theorem catalogue : r.encoded.profile ∈ Catalogue (j := j) L :=
  ⟨r.canonical, r.encoded, r.admissible, r.synchronized, rfl⟩

/-- Numerical decoding also recovers the persistent shadows literally, via
clause 5 and the source-state synchronization, not by identifying shadows with
arbitrary physical numerical labels. -/
theorem persistent_readback (hj : 1 ≤ j) (hs : Synchronized S.st) (f : Field P C) :
    r.decoder (r.encoded.st.persistent f) = S.st.persistent f := by
  rw [r.synchronized f, hs f]
  rw [r.witness.clause5 _ 1 (by rw [gTop_of_le hj]; exact le_top) 1 le_rfl]
  exact congrArg (fun x => extVisibilityReplace x 1 1) (r.readback (.field f))

/-- Every supported invisible orbit below the cut is fixed, at each lower
grade. Unhosted invisible values are deliberately absent from this statement. -/
theorem orbit_fixed (d : TField P C) (hd : a d < grid j B)
    {k i : ℕ} (hk : k ≤ j) (hi : i ≤ k) :
    r.decoder (extVisibilityReplace (a d) k i) = extVisibilityReplace (a d) k i := by
  rw [r.witness.clause5 _ k (by rw [gTop_of_le hk]; exact le_top) i hi,
    r.boundary_fixed d hd]

/-- Whole-coordinate prefix transport, on any coordinate type. The physical
constructor still has to produce the source agreement and orbit support. -/
theorem auxiliary_caps {Y : Type*} {u v : Y → ExtOrd}
    (hs : ∀ y, OrbitPrefixSupport.Supported j
      (PairedSlotComparison.sourceGrid j (Fintype.card (TField P C)) : Set ExtOrd) a (u y))
    (hag : ∀ y, min (v y) (grid j B) = min (u y) (grid j B)) :
    ∀ y, min (r.decoder (v y)) (grid j B) = min (u y) (grid j B) := by
  apply OrbitPrefixSupport.decode_agree r.witness (grid_visible j B)
    (by rw [gTop_of_le le_rfl]; exact le_top) r.reaches _ r.boundary_fixed hs hag
  intro z hz hzh
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact r.witness.bot
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hz
    apply r.grid_fixed
    by_contra hn
    have hb : B ≤ b := Nat.le_of_not_gt hn
    exact (not_le_of_gt hzh) (ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl))

end Repair
end
end VaughtConjecture.Knight.ReceivingSupportedRepair
