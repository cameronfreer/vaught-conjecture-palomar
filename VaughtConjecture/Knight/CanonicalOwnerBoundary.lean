/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OwnerLocalAlignment
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.CoatomBoundaryExtension

/-! # Canonical owner alignment and ordinary old-boundary completion

The complete field inventory supplies shortness, properness and the tail budget.
V-C's endpoint is a grid endpoint in that inventory, proved from the actual
owner observations. Two old lifting clauses construct the lawful old-boundary
completion. No prospective new controller or new-domain lifting is assumed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalOwnerBoundary
open Transform Value ExtOrd SharpWitnessComposition OwnerLocalEndpoint
open CanonicalPairedProfiles CoatomBoundaryExtension
noncomputable section

theorem endpoint_grid {X : Type*} [Fintype X] {j : ℕ} {a : X → ExtOrd}
    (ha : a ∈ CanonicalPairedProfiles.inventory X j) (d : X) (hd : a d ≠ ⊥) :
    ∃ b : ℕ, b ≤ 2 * Fintype.card X ∧
      endpoint j (a d) = CanonicalPairedInverse.grid j b := by
  rcases mem_codedAlphabet_iff.mp (inventory_coded X j ha d) with hb | ⟨b, n, hb, _, he⟩
  · exact (hd hb).elim
  have hn : n ≤ j := by
    rcases inventory_short X j ha d with hz | ht | ⟨v, hv, hshort⟩
    · exact (hd hz).elim
    · exact (ha.2 d ht).elim
    · have heq := ofOrd_inj.mp (he.symm.trans hv)
      simpa only [← heq, finitePart_mul_add] using hshort
  refine ⟨b, hb, ?_⟩
  rcases lt_or_eq_of_le hn with hn | hn
  · rw [endpoint, he, extVisibilityReplace_ofOrd, visibilityReplace,
      ite_eq_left (by rwa [finitePart_mul_add]), ordinalReplace, limitPart_mul_add]
    rfl
  · rw [endpoint, he, hn, extVisibilityReplace_of_le_finitePart
      (by simp only [finitePart_mul_add, le_refl])]
    rfl

theorem local_endpoint_grid {X Y : Type*} [Fintype X] {j : ℕ} {a : X → ExtOrd}
    (ha : a ∈ CanonicalPairedProfiles.inventory X j) (occ : Y → X)
    {τ : ExtOrd → ExtOrd} {γ h : ExtOrd}
    (H : IsEndpoint j (a ∘ occ) τ γ h) (hpos : ⊥ < h) :
    ∃ b : ℕ, b ≤ 2 * Fintype.card X ∧ h = CanonicalPairedInverse.grid j b := by
  obtain ⟨d, _, hd⟩ := H.exists_witness
  have hbot : a (occ d) ≠ ⊥ := by
    intro hb
    have he : h = ⊥ := hd.symm.trans (by rw [Function.comp_apply, hb]; rfl)
    exact hpos.ne he.symm
  obtain ⟨b, hb, he⟩ := endpoint_grid ha (occ d) hbot
  exact ⟨b, hb, hd.symm.trans he⟩

/-- An ordinary matching-face completion with all old coordinate caps retained.
The only lifting inputs are two actual old graded-pair clauses. They can be
obtained from the respective old faces by `lift_of_restrictFace`; no new
full-scope bountifulness is an input. -/
theorem exists_completion
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {X : Type*} [Fintype X]
    (c : Cell D) [Fintype (D.below (D.cell c))]
    {a : X → ExtOrd} (ha : a ∈ CanonicalPairedProfiles.inventory X (D.grade c))
    (occ : Cell D → X) (hs : RespectsSemantics sem (a ∘ occ))
    {p : D.below (D.cell c) → ExtOrd} (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hcU : GradedLe (D.cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hcU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ D.grade c) (hV : V.2 ≤ D.grade c)
    {τ : ExtOrd → ExtOrd} {γ : ExtOrd}
    (hτ : Witness (gTop (D.grade c)) τ)
    (hγ : SelfVis (D.grade c) γ) (hpos : ⊥ < γ) (hτbound : ∀ z, τ z ≤ γ)
    (hface : ∀ e : D.below (D.cell c), τ (a (occ e.1)) = min (p e) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩) :
    ∃ (h : ExtOrd) (ρ : ExtOrd → ExtOrd) (δ : ExtOrd) (r : Cell D → ExtOrd),
      ⊥ < h ∧ SelfVis (D.grade c) h ∧
      (∃ b : ℕ, b ≤ 2 * Fintype.card X ∧ h = CanonicalPairedInverse.grid (D.grade c) b) ∧
      Witness (gTop (D.grade c)) ρ ∧ γ ≤ δ ∧ δ ≤ p ⟨c, GradedLe.refl _⟩ ∧
      SelfVis (D.grade c) δ ∧ ρ h = δ ∧ RespectsSemantics sem r ∧
      (∀ d, min (r d) h = min (a (occ d)) h) ∧
      (∀ e : D.below (D.cell c), r e.1 = AlignedCutEncoding.encode
        (fun e => a (occ e.1)) (fun e => min (p e) (p ⟨c, GradedLe.refl _⟩))
        (D.grade c) (2 * Fintype.card X + 1) h δ e) ∧
      (∀ e : D.below (D.cell c), PaddedSourceDecoder.extend
        (RelativePrefixEncoding.inventory (fun e => min (p e) (p ⟨c, GradedLe.refl _⟩)) δ)
        (D.grade c) (2 * Fintype.card X + 1) ρ δ (r e.1) =
          min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      (∀ e, min (p e) δ = min (ρ (a (occ e.1))) δ) ∧
      ∀ z, Short (D.grade c) z → min (ρ z) γ = min (τ z) γ := by
  obtain ⟨h, ρ, δ, f, H, hhpos, hvis, _, _, hρ, hγδ, hδM, hδvis,
      hρh, hf, hfcap, hfeq, hfread, hread, hcap⟩ :=
    OwnerLocalAlignment.exists_coded_face c (hs.toBelow (D.cell c)) hp
      (fun e => ha.2 (occ e.1)) (fun e => inventory_short X (D.grade c) ha (occ e.1))
      (Fintype.card X) (inventory_bound X (D.grade c) ha (occ c))
      hτ hγ hpos hτbound hface hpc
  have hgrid := local_endpoint_grid ha (fun e : D.below (D.cell c) => occ e.1) H hhpos
  let old : Section sem U V := {
    onLeft := fun d => a (occ d.1)
    onRight := fun d => a (occ d.1)
    left_lawful := hs.toBelow U
    right_lawful := hs.toBelow V
    overlap := fun _ _ _ => rfl }
  obtain ⟨r, hr, hrcap, hrread⟩ := extend_boundary hcover hcU hOU hOV hinter hleft hright
    old f h hf (selfVis_mono hvis hU) (selfVis_mono hvis hV) (fun d => (hfcap d).symm)
  refine ⟨h, ρ, δ, r, hhpos, hvis, hgrid, hρ, hγδ, hδM, hδvis, hρh, hr,
    ?_, ?_, ?_, hread, hcap⟩
  · intro d
    have hold : old.whole hcover d = a (occ d) := by
      rcases hcover d with hu | hv
      · exact old.whole_left hcover ⟨d, hu⟩
      · exact old.whole_right hcover ⟨d, hv⟩
    exact (hrcap d).trans (congrArg (fun z => min z h) hold)
  · intro e
    rw [hrread, hfeq]
    rfl
  · intro e
    rw [hrread]
    exact hfread e

end
end VaughtConjecture.Knight.CanonicalOwnerBoundary
