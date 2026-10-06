/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorCatalogue
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.PairedSlotComparison

/-! # The scalar repair package of the ordinary final catalogue

The two scalar producers consumed by the physical final-grade layer's decoding
(`FinalGateDecoding.decode_source_prefix` on the integration branch, and its selected-display
decoder), composed from the existing private fibre, normalization, terminal insertion and the
supported inverse — none of whose machinery is re-proved here.

* **`positive_cap_repair`**: from a canonical admitted source `a` (a member of the fixed
  `Catalogue`) and a lawful **proper** private prescription agreeing with `a`'s private part at a
  source-grid endpoint `grid N B`: an admitted proper complete vector `b₀` retaining the
  prescription literally, with complete-field prefix agreement at the endpoint; its canonical
  normalization, a member of the **same** catalogue, with the same capped prefix agreement; and
  the actual supported inverse `κ` — a witness through `N` decoding `b₀` exactly from its
  normalization, fixing every unused grid endpoint below the cut (`fix_sourceGrid` gives the
  `sourceGrid` form) and every supported orbit of `a` below the cut, and reaching the cut.
* **`bottom_supply`**: independent bottom-cap private supply — from the zero admitted state,
  install an arbitrary lawful private prescription, **literal top included**, with the gate off;
  terminal insertion then gives a member of the catalogue with an exact decoder reading the
  installed prescription back.

Nothing here asserts a physical section, a display, admission of an arbitrary section or any
upward admission. -/

@[expose] public section

namespace VaughtConjecture.Knight.CappedDonor.Ref

open Transform Value ExtOrd
noncomputable section

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-- A witness fixing every grid endpoint below `B` fixes every source-grid value below the cut
`grid N B` (bottom included). -/
theorem fix_sourceGrid {κ : ExtOrd → ExtOrd} (hbot : κ ⊥ = ⊥) {B : ℕ}
    (hfix : ∀ b < B, κ (CanonicalPairedInverse.grid N b) = CanonicalPairedInverse.grid N b)
    (n : ℕ) : ∀ z ∈ PairedSlotComparison.sourceGrid N n, z < CanonicalPairedInverse.grid N B →
      κ z = z := by
  classical
  intro z hz hlt
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact hbot
  · obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hz
    refine hfix b ?_
    by_contra hle
    apply not_le.mpr hlt
    change ofOrd (Ordinal.omega0 * B + N) ≤ ofOrd (Ordinal.omega0 * b + N)
    exact ofOrd_le_ofOrd.mpr (add_le_add_left (omul_le_omul (not_lt.mp hle)) _)

/-- **Positive-cap repair through normalization and the supported inverse.** -/
theorem positive_cap_repair {a : Field P C → ExtOrd} (ha : a ∈ R.Catalogue)
    {v₁ : C.scheme.below (effC J N) → ExtOrd} (hv₁ : RespectsSemanticsBelow C.rows (effC J N) v₁)
    (hv₁p : ∀ d, v₁ d ≠ ⊤) {B : ℕ}
    (hagree : ∀ d, min (v₁ d) (CanonicalPairedInverse.grid N B) =
      min (a (.priv d.1)) (CanonicalPairedInverse.grid N B)) :
    ∃ b₀ : Field P C → ExtOrd, R.Admitted b₀ ∧ (∀ f, b₀ f ≠ ⊤) ∧
      (∀ d : C.scheme.below (effC J N), b₀ (.priv d.1) = v₁ d) ∧
      (∀ f, min (b₀ f) (CanonicalPairedInverse.grid N B) =
        min (a f) (CanonicalPairedInverse.grid N B)) ∧
      PairedSlotEncoding.normalize N b₀ ∈ R.Catalogue ∧
      (∀ f, min (PairedSlotEncoding.normalize N b₀ f) (CanonicalPairedInverse.grid N B) =
        min (a f) (CanonicalPairedInverse.grid N B)) ∧
      ∃ κ : ExtOrd → ExtOrd, Witness (gTop N) κ ∧
        (∀ f, κ (PairedSlotEncoding.normalize N b₀ f) = b₀ f) ∧
        (∀ b < B, κ (CanonicalPairedInverse.grid N b) = CanonicalPairedInverse.grid N b) ∧
        CanonicalPairedInverse.grid N B ≤ κ (CanonicalPairedInverse.grid N B) ∧
        ∀ f, a f < CanonicalPairedInverse.grid N B → ∀ k ≤ N, ∀ i ≤ k,
          κ (extVisibilityReplace (a f) k i) = extVisibilityReplace (a f) k i := by
  obtain ⟨hinv, hadm⟩ := ha
  have hgrid : SelfVis N (CanonicalPairedInverse.grid N B) :=
    CanonicalPairedInverse.grid_visible N B
  have hne : CanonicalPairedInverse.grid N B ≠ ⊥ := ofOrd_ne_bot _
  obtain ⟨b₁, hb₁, hpriv₁, hrec₁⟩ := hadm.private_repair hv₁ hgrid hne hagree
  obtain ⟨b₀, hb₀, hprop, hpre, hlit, -, -, -⟩ :=
    hb₁.exists_terminal (Ordinal.omega0 * B + N)
  have hpre' : ∀ f, min (b₀ f) (CanonicalPairedInverse.grid N B) =
      min (a f) (CanonicalPairedInverse.grid N B) := fun f => (hpre f).trans (hrec₁ f)
  have hag : ∀ f, min (a f) (CanonicalPairedInverse.grid N B) =
      min (b₀ f) (CanonicalPairedInverse.grid N B) := fun f => (hpre' f).symm
  refine ⟨b₀, hb₀, hprop, fun d => ?_, hpre', hb₀.normalize_mem_catalogue hprop, fun f => ?_, ?_⟩
  · rw [hlit _ (by rw [hpriv₁ d]; exact hv₁p d), hpriv₁ d]
  · exact CanonicalPairedProfiles.normalize_cap (Field P C) N hinv hag f
  · exact CanonicalPairedInverse.exists_supported_inverse hinv hprop hag

/-- **Independent bottom-cap private supply, with a supported decoder.**  From the zero
admitted state, an arbitrary lawful private prescription — literal top included — is installed
with the gate off; terminal insertion gives a member of the catalogue with an exact decoder
reading it back, every output of which is supported by the installed vector (bottom and top
allowed). -/
theorem bottom_supply' {v₁ : C.scheme.below (effC J N) → ExtOrd}
    (hv₁ : RespectsSemanticsBelow C.rows (effC J N) v₁) :
    ∃ a : Field P C → ExtOrd, R.Admitted a ∧
      (∀ d : C.scheme.below (effC J N), a (.priv d.1) = v₁ d) ∧ a .gate = ⊥ ∧
      ∃ b₀ : Field P C → ExtOrd, R.Admitted b₀ ∧ (∀ f, b₀ f ≠ ⊤) ∧
        PairedSlotEncoding.normalize N b₀ ∈ R.Catalogue ∧
        ∃ δ : ExtOrd → ExtOrd, Witness (gTop N) δ ∧
          (∀ f, δ (PairedSlotEncoding.normalize N b₀ f) = a f) ∧
          ∀ x, OrbitPrefixSupport.Supported N ({⊤} : Set ExtOrd) a (δ x) := by
  obtain ⟨st₁, hst₁, hv, -, -, -⟩ := R.exists_private_lift (zeroState_admissible N) hv₁
    (selfVis_bot _) (fun d => by simp only [min_bot_right])
  let st₂ : R.State N := Ref.gateOff (resync st₁)
  have hadm : R.Admitted st₂.sourceProfile :=
    ⟨st₂, hst₁.resync.gateOff, (resync_synchronized hst₁).gateOff R.one_le_N,
      extVisibilityReplace_bot _ _, rfl⟩
  obtain ⟨b₀, hb₀, hprop, -, -, hnorm, hmem, δ, hδ, hread, hsupp⟩ := hadm.exists_terminal' 0
  refine ⟨st₂.sourceProfile, hadm, fun d => ?_, ?_, b₀, hb₀, hprop, ⟨hmem, hnorm⟩, δ, hδ, hread,
    hsupp⟩
  · rw [State.sourceProfile_of_present _ ((present_priv_iff N d.1).mp d.2)]
    change st₁.v ⟨d.1, _⟩ = v₁ d
    rw [hv]
    exact congrArg v₁ (Subtype.ext rfl)
  · rw [State.sourceProfile_of_present _ (show (Field.gate : Field P C).grade ≤ N from R.one_le_N)]
    rfl

/-- **Independent bottom-cap private supply** (the decoder's support conjunct dropped). -/
theorem bottom_supply {v₁ : C.scheme.below (effC J N) → ExtOrd}
    (hv₁ : RespectsSemanticsBelow C.rows (effC J N) v₁) :
    ∃ a : Field P C → ExtOrd, R.Admitted a ∧
      (∀ d : C.scheme.below (effC J N), a (.priv d.1) = v₁ d) ∧ a .gate = ⊥ ∧
      ∃ b₀ : Field P C → ExtOrd, R.Admitted b₀ ∧ (∀ f, b₀ f ≠ ⊤) ∧
        PairedSlotEncoding.normalize N b₀ ∈ R.Catalogue ∧
        ∃ δ : ExtOrd → ExtOrd, Witness (gTop N) δ ∧
          ∀ f, δ (PairedSlotEncoding.normalize N b₀ f) = a f := by
  obtain ⟨a, h1, h2, h3, b₀, h4, h5, h6, δ, hδ, hread, -⟩ := bottom_supply' (R := R) hv₁
  exact ⟨a, h1, h2, h3, b₀, h4, h5, h6, δ, hδ, hread⟩

end
end VaughtConjecture.Knight.CappedDonor.Ref
