/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WitnessSplice
public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.SourceBlockLocalityTransport

/-! # Orbit-supported values survive prefix-fixing decoding

The source-prefix argument in `vc-notes/simplification/note4.md`, Section 4,
needs more than agreement on visible grid cuts: invisible auxiliary values must
come from replacement orbits represented on the proper boundary.

This module proves the scalar consequence of that support condition. A faithful
shifter which fixes the boundary and the grid below a self-visible cut fixes every
supported value below the cut. If its image of the cut reaches the cut, it retains
all supported capped readings. The suppressor bound used by clause 5 is explicit;
neither bottom reflection nor composition of transformations is assumed.

The construction of supported sections, paired normalization, and the right-filled
decoder comparison are not proved here. In particular, `Supported` is an input to
the preservation theorem, not a hidden finite-extension supply assumption.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.OrbitPrefixSupport

open Transform Value ExtOrd

variable {D : Type*} {K : ℕ} {grid : Set ExtOrd} {p : D → ExtOrd}

/-- Bottom, a designated grid value, or a replacement of a proper-boundary value.
The offset may equal the threshold; the supporting boundary value need not itself
be invisible. The finite constructor may establish a stronger support invariant. -/
def Supported (K : ℕ) (grid : Set ExtOrd) (p : D → ExtOrd) (x : ExtOrd) : Prop :=
  x = ⊥ ∨ x ∈ grid ∨ ∃ d i, i ≤ K ∧ x = extVisibilityReplace (p d) K i

/-- A replacement below a self-visible cut has its supporting value below that
cut too. This supplies the strict inequality needed to use boundary fixation. -/
theorem boundary_lt_of_orbit_lt {h : ExtOrd} (hh : SelfVis K h)
    {d : D} {i : ℕ} (hx : extVisibilityReplace (p d) K i < h) : p d < h := by
  by_contra hn
  exact (not_le_of_gt hx) (le_extVisibilityReplace_of_selfVis_le hh (le_of_not_gt hn))

/-- Clause 5 propagates fixation from the protected boundary to every supported
hidden value below the cut, including replacement endpoints. -/
theorem fixed_below {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hw : Witness g σ)
    {h x : ExtOrd} (hh : SelfVis K h) (hguard : h ≤ g K)
    (hgrid : ∀ z ∈ grid, z < h → σ z = z)
    (hboundary : ∀ d, p d < h → σ (p d) = p d)
    (hs : Supported K grid p x) (hx : x < h) : σ x = x := by
  rcases hs with rfl | hs | ⟨d, i, hi, rfl⟩
  · exact hw.bot
  · exact hgrid _ hs hx
  · have hd := boundary_lt_of_orbit_lt hh hx
    have hfix := hboundary d hd
    rw [hw.clause5 (p d) K (by rw [hfix]; exact hd.le.trans hguard) i hi, hfix]

/-- Below the cut there is exact fixation; at and above it monotonicity and the
cut's image preserve the capped reading. Literal top and bottom are included. -/
theorem cap_fixed {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hw : Witness g σ)
    {h x : ExtOrd} (hh : SelfVis K h) (hguard : h ≤ g K) (hreach : h ≤ σ h)
    (hgrid : ∀ z ∈ grid, z < h → σ z = z)
    (hboundary : ∀ d, p d < h → σ (p d) = p d)
    (hs : Supported K grid p x) : min (σ x) h = min x h := by
  by_cases hx : x < h
  · rw [fixed_below hw hh hguard hgrid hboundary hs hx]
  · have hle := le_of_not_gt hx
    rw [min_eq_right hle, min_eq_right (hreach.trans (hw.mono hle))]

/-- A second row with the same source prefix keeps that prefix after decoding.
Support is needed only for the protected row, not for the replacement row. -/
theorem decode_agree {X : Type*} {a b : X → ExtOrd}
    {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hw : Witness g σ)
    {h : ExtOrd} (hh : SelfVis K h) (hguard : h ≤ g K) (hreach : h ≤ σ h)
    (hgrid : ∀ z ∈ grid, z < h → σ z = z)
    (hboundary : ∀ d, p d < h → σ (p d) = p d)
    (hs : ∀ x, Supported K grid p (a x))
    (hag : ∀ x, min (b x) h = min (a x) h) :
    ∀ x, min (σ (b x)) h = min (a x) h := by
  intro x
  have hmin (z : ExtOrd) : min (σ (min z h)) h = min (σ z) h := by
    rw [monotone_min_apply hw.mono, min_assoc, min_eq_right hreach]
  calc
    min (σ (b x)) h = min (σ (min (b x) h)) h := (hmin _).symm
    _ = min (σ (min (a x) h)) h := by rw [hag x]
    _ = min (σ (a x)) h := hmin _
    _ = min (a x) h := cap_fixed hw hh hguard hreach hgrid hboundary (hs x)

/-- At a positive source cut the protected lawful row repairs decoder locality
on arbitrary inherited rows. No short-source hypothesis or composition of
faithful transformations is used. Existence of the lawful coded row remains an
input; this theorem only decodes it and proves its legality and full cap agreement. -/
theorem decode_respects_of_positive_cut
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {S : CellScheme A}
    {sem : Semantics S} {BJ : Finset ι × ℕ} {a b : S.below BJ → ExtOrd}
    {σ : ExtOrd → ExtOrd} (hw : Witness (gTop K) σ)
    (ha : RespectsSemanticsBelow sem BJ a) (hb : RespectsSemanticsBelow sem BJ b)
    (hK : ∀ d : S.below BJ, S.grade d.1 ≤ K)
    {h : ExtOrd} (hh : SelfVis K h) (hpos : h ≠ ⊥) (hreach : h ≤ σ h)
    (hgrid : ∀ z ∈ grid, z < h → σ z = z)
    (hboundary : ∀ d, p d < h → σ (p d) = p d)
    (hs : ∀ d, Supported K grid p (a d))
    (hag : ∀ d, min (b d) h = min (a d) h) :
    RespectsSemanticsBelow sem BJ (fun d => σ (b d)) ∧
      ∀ d, min (σ (b d)) h = min (a d) h := by
  have hguard : h ≤ gTop K K := by rw [gTop_of_le le_rfl]; exact le_top
  have hag' := decode_agree hw hh hguard hreach hgrid hboundary hs hag
  exact ⟨SharpWitnessComposition.map_respects_of_positive_cap_agreement hb ha hK
    (SharpWitnessComposition.boundedMap_of_witness hw) hpos hag', hag'⟩

end VaughtConjecture.Knight.OrbitPrefixSupport
