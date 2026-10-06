/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OwnerStripRetuning
public import VaughtConjecture.Knight.AlignedCutEncoding

/-! # Complete owner-face alignment at a constructed retuned cap

First-cut minimality is used only at actual grid endpoints. Saturated unused
offsets are handled by the owner's affine strip, not excluded. The result
aligns the prescription capped at its owner; restoring larger lower-grade
labels and constructing a whole coded extension remain separate operations.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.OwnerFaceAlignment

open Transform Value ExtOrd SharpWitnessComposition OwnerStripRetuning

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable {sem : Semantics D} {K : ℕ}

theorem profile_code (a : PairedBoundarySections.Profile sem K) (d : Cell D) :
    a.val d = ⊥ ∨ ∃ b n : ℕ, b ≤ 2 * Fintype.card (Cell D) ∧ n ≤ K ∧
      a.val d = ofOrd (Ordinal.omega0 * b + n) := by
  rcases mem_codedAlphabet_iff.mp (a.property.2.1 d) with hb | ⟨b, n, hb, _, he⟩
  · exact Or.inl hb
  · refine Or.inr ⟨b, n, hb, ?_, he⟩
    rcases a.property.2.2 d with hz | hz | ⟨w, hw, hshort⟩
    · exact (ofOrd_ne_bot _ (he.symm.trans hz)).elim
    · exact (ofOrd_ne_top _ (he.symm.trans hz)).elim
    · have heq := ofOrd_inj.mp (he.symm.trans hw)
      simpa only [← heq, finitePart_mul_add] using hshort

/-- Every saturated subcut occurrence lies in the strip ending at the first
reaching grid point. This includes sources at unused offsets of that strip. -/
theorem saturated_subcut (a : PairedBoundarySections.Profile sem K)
    {τ : ExtOrd → ExtOrd} (hτ : Monotone τ) {h γ : ExtOrd}
    (hvis : SelfVis K h)
    (hfirst : ∀ z ∈ PairedSlotComparison.sourceGrid K (Fintype.card (Cell D)),
      z < h → τ z < γ)
    (d : Cell D) (hd : a.val d < h) (hsat : γ ≤ τ (a.val d)) :
    ∃ (u : Ordinal.{0}) (n : ℕ), n < K ∧
      a.val d = ofOrd (limitPart u + n) ∧ h = ofOrd (limitPart u + K) := by
  rcases profile_code a d with hb | ⟨b, n, hb, hn, he⟩
  · rw [hb] at hd hsat
    exact (not_lt_of_ge hsat
      (hfirst ⊥ (PairedSlotComparison.sourceGrid_bot _ _) hd)).elim
  have hgrid := PairedSlotComparison.sourceGrid_endpoint (j := K)
    (hb.trans (Nat.le_succ _))
  have hnlt : n < K := by
    by_contra hnot
    have hnK : n = K := le_antisymm hn (not_lt.mp hnot)
    rw [he, hnK] at hd hsat
    exact not_lt_of_ge hsat (hfirst _ hgrid hd)
  have hround : extVisibilityReplace (a.val d) K K =
      ofOrd (Ordinal.omega0 * b + K) := by
    rw [he, extVisibilityReplace_ofOrd, visibilityReplace,
      ite_eq_left (by rw [finitePart_mul_add]; exact hnlt), ordinalReplace,
      limitPart_mul_add]
  have hle : ofOrd (Ordinal.omega0 * b + K) ≤ h := by
    rw [← hround, ← hvis]
    exact evr_mono hd.le le_rfl
  have hge : h ≤ ofOrd (Ordinal.omega0 * b + K) := by
    by_contra hnot
    have hs : a.val d ≤ ofOrd (Ordinal.omega0 * b + K) := by
      rw [← hround]
      exact le_extVisibilityReplace_self _ _
    exact not_lt_of_ge (hsat.trans (hτ hs)) (hfirst _ hgrid (not_le.mp hnot))
  refine ⟨Ordinal.omega0 * b, n, hnlt, ?_, ?_⟩
  · simpa only [limitPart_mul] using he
  · simpa only [limitPart_mul] using le_antisymm hge hle

/-- Construct both branches of complete face alignment from actual owner
localities. No alignment or retuning is an input. The raised-output alignment
is for the owner-capped prescription, not for arbitrary larger lower labels. -/
theorem exists_face_alignment (c : Cell D)
    (a : PairedBoundarySections.Profile sem (D.grade c))
    {p : D.below (D.cell c) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {τ : ExtOrd → ExtOrd} {h γ : ExtOrd}
    (hτ : Witness (gTop (D.grade c)) τ)
    (hγ : SelfVis (D.grade c) γ) (hτbound : ∀ z, τ z ≤ γ)
    (hvis : SelfVis (D.grade c) h) (hreach : τ h = γ)
    (hfirst : ∀ z ∈ PairedSlotComparison.sourceGrid (D.grade c) (Fintype.card (Cell D)),
      z < h → τ z < γ)
    (hface : ∀ e : D.below (D.cell c), τ (a.val e.1) = min (p e) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩) :
    ∃ (ρ : ExtOrd → ExtOrd) (δ : ExtOrd),
      Witness (gTop (D.grade c)) ρ ∧ γ ≤ δ ∧ δ ≤ p ⟨c, GradedLe.refl _⟩ ∧
      SelfVis (D.grade c) δ ∧ ρ h = δ ∧
      (∀ e : D.below (D.cell c), min (p e) δ = min (ρ (a.val e.1)) δ) ∧
      (∀ e : D.below (D.cell c),
        δ < min (p e) (p ⟨c, GradedLe.refl _⟩) → h ≤ a.val e.1) ∧
      (∀ z, Short (D.grade c) z → min (ρ z) γ = min (τ z) γ) ∧
      ∀ z, ρ z ≤ p ⟨c, GradedLe.refl _⟩ := by
  classical
  let self : D.below (D.cell c) := ⟨c, GradedLe.refl _⟩
  let s : D.below (D.cell c) → ExtOrd := fun e => a.val e.1
  let M := p self
  by_cases halign : ∀ e : D.below (D.cell c), γ < min (p e) M → h ≤ s e
  · refine ⟨τ, γ, hτ, le_rfl, hpc.le, hγ, hreach, ?_, halign,
      fun _ _ => rfl, fun z => (hτbound z).trans hpc.le⟩
    intro e
    rw [min_eq_left (hτbound _), hface]
  push Not at halign
  obtain ⟨d, hpd, hsub⟩ := halign
  have hsd : s d < h := hsub
  have hsat : γ ≤ τ (a.val d.1) := by
    rw [hface d, min_eq_right (lt_of_lt_of_le hpd (min_le_left _ _)).le]
  obtain ⟨u, i, hi, hdi, hendpoint⟩ := saturated_subcut a hτ.mono hvis hfirst d.1 hsd hsat
  have howner : h ≤ a.val c := by
    by_contra hn
    have hb := hfirst _ (profile_owner_grid a c rfl) (not_le.mp hn)
    rw [hface self, min_eq_right hpc.le] at hb
    exact lt_irrefl _ hb
  have hs : RespectsSemanticsBelow sem (D.cell c) s := a.property.1.toBelow (D.cell c)
  obtain ⟨α, hα, _, hαread⟩ := exists_bounded_exact_capped_witness
    (grade := fun x : D.below (D.cell c) => D.grade x.1) (p := s) (c := self)
    (fun x : D.below (D.cell c) => x.2.2) (hs.orderly self).symm (hs.locality self)
  obtain ⟨β, hβ, hβbound, hβread⟩ := exists_bounded_exact_capped_witness
    (grade := fun x : D.below (D.cell c) => D.grade x.1) (p := p) (c := self)
    (fun x : D.below (D.cell c) => x.2.2) (hp.orderly self).symm (hp.locality self)
  have ha (e : D.below (D.cell c)) (he : s e < h) : α (sem.E c e) = s e :=
    (hαread e).trans (min_eq_left (he.le.trans howner))
  obtain ⟨ρ, δ, hρ, hγδ, hδM, hδvis, hend, hstrip, habove, hcap, hbound⟩ :=
    exists_retuning_with_transfer hα hβ hτ hi ((ha d hsd).trans hdi) hγ hτbound
      (by rw [ha d hsd]; exact le_antisymm (hτbound _) hsat)
      (by rw [hβread d]; exact hpd.le) hβbound
  have hρh : ρ h = δ := hendpoint ▸ hend
  have subread (e : D.below (D.cell c)) (he : s e < h) :
      min (p e) M = ρ (s e) := by
    by_cases hlo : τ (s e) < γ
    · have hpread : p e = τ (s e) := AmbientGradeCharts.eq_of_cap_below
        (by rw [min_eq_left (hτbound _)]; exact (hface e).symm) hlo
      have hρread : ρ (s e) = τ (s e) :=
        AmbientGradeCharts.eq_of_cap_below (hcap _ (a.property.2.2 e.1)) hlo
      rw [hpread, hρread, min_eq_left (hlo.le.trans hpc.le)]
    · obtain ⟨w, n, hn, heq, hwe⟩ :=
        saturated_subcut a hτ.mono hvis hfirst e.1 he (not_lt.mp hlo)
      have hfloor : limitPart w = limitPart u := by
        have heq := congrArg limitPart (ofOrd_inj.mp (hwe.symm.trans hendpoint))
        simpa only [limitPart_limitPart_add_nat] using heq
      rw [hfloor] at heq
      exact (hβread e).symm.trans
        ((hstrip (sem.E c e) n hn ((ha e he).trans heq)).symm.trans
          (congrArg ρ (ha e he)))
  refine ⟨ρ, δ, hρ, hγδ, hδM, hδvis, hρh, ?_, ?_, hcap, hbound⟩
  · intro e
    by_cases he : s e < h
    · have hc : min (min (p e) M) δ = min (p e) δ := by
        rw [min_assoc, min_eq_right hδM]
      rw [← hc, subread e he]
    · have has : ofOrd (limitPart u + D.grade c) ≤ α (sem.E c e) := by
        rw [hαread e, ← hendpoint]
        exact le_min (not_lt.mp he) howner
      have hpe : δ ≤ p e := (habove _ has).trans
        ((hβread e).le.trans (min_le_left _ _))
      rw [min_eq_right hpe, min_eq_right (hρh ▸ hρ.mono (not_lt.mp he))]
  · intro e hhigh
    by_contra hn
    have he := not_le.mp hn
    have hle : min (p e) M ≤ δ := by
      rw [subread e he, ← hρh]
      exact hρ.mono he.le
    exact not_lt_of_ge hle hhigh

/-- A finite tail strictly beyond the actual source grid is constructed;
this does not claim that appending that tail fits the frozen profile alphabet. -/
theorem grid_tail_room {h : ExtOrd}
    (hh : h ∈ PairedSlotComparison.sourceGrid K (Fintype.card (Cell D))) :
    h < ofOrd (Ordinal.omega0 * (2 * Fintype.card (Cell D) + 2 : ℕ)) := by
  apply (PairedBoundarySections.grid_bound K hh).trans_lt
  change ofOrd (Ordinal.omega0 * (2 * Fintype.card (Cell D) + 1 : ℕ) + K) < _
  apply ofOrd_lt_ofOrd.mpr
  have he : (2 * Fintype.card (Cell D) + 2 : ℕ) =
      (2 * Fintype.card (Cell D) + 1) + 1 := by omega
  conv_rhs => rw [he, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
  exact add_lt_add_right (Ordinal.natCast_lt_omega0 K) _

/-- Construct a lawful aligned coded face and its literal owner-capped
readback. Its complete source prefix is preserved at the original grid cut.
Neither the retuning nor the aligned prescription is supplied. -/
theorem exists_coded_face (c : Cell D)
    [Fintype (D.below (D.cell c))]
    (a : PairedBoundarySections.Profile sem (D.grade c))
    {p : D.below (D.cell c) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {τ : ExtOrd → ExtOrd} {h γ : ExtOrd}
    (hτ : Witness (gTop (D.grade c)) τ)
    (hγ : SelfVis (D.grade c) γ) (hτbound : ∀ z, τ z ≤ γ)
    (hh : h ∈ PairedSlotComparison.sourceGrid (D.grade c) (Fintype.card (Cell D)))
    (hpos : h ≠ ⊥) (hreach : τ h = γ)
    (hfirst : ∀ z ∈ PairedSlotComparison.sourceGrid (D.grade c) (Fintype.card (Cell D)),
      z < h → τ z < γ)
    (hface : ∀ e : D.below (D.cell c), τ (a.val e.1) = min (p e) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩) :
    ∃ (ρ : ExtOrd → ExtOrd) (δ : ExtOrd) (f : D.below (D.cell c) → ExtOrd),
      Witness (gTop (D.grade c)) ρ ∧ γ ≤ δ ∧ δ ≤ p ⟨c, GradedLe.refl _⟩ ∧
      SelfVis (D.grade c) δ ∧ ρ h = δ ∧
      RespectsSemanticsBelow sem (D.cell c) f ∧
      (∀ e, min (f e) h = min (a.val e.1) h) ∧
      f = AlignedCutEncoding.encode (fun e => a.val e.1)
        (fun e => min (p e) (p ⟨c, GradedLe.refl _⟩))
        (D.grade c) (2 * Fintype.card (Cell D) + 2) h δ ∧
      (∀ e, PaddedSourceDecoder.extend
        (RelativePrefixEncoding.inventory (fun e => min (p e) (p ⟨c, GradedLe.refl _⟩)) δ)
        (D.grade c) (2 * Fintype.card (Cell D) + 2) ρ δ (f e) =
          min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      (∀ e, min (p e) δ = min (ρ (a.val e.1)) δ) ∧
      ∀ z, Short (D.grade c) z → min (ρ z) γ = min (τ z) γ := by
  have hvis := PairedSlotComparison.sourceGrid_visible hh
  obtain ⟨ρ, δ, hρ, hγδ, hδM, hδvis, hρh, hread, halign, hcap, _⟩ :=
    exists_face_alignment c a hp hτ hγ hτbound hvis hreach hfirst hface hpc
  let p₀ := fun e => min (p e) (p ⟨c, GradedLe.refl _⟩)
  let s := fun e : D.below (D.cell c) => a.val e.1
  let b := 2 * Fintype.card (Cell D) + 2
  let f := AlignedCutEncoding.encode s p₀ (D.grade c) b h δ
  have hroom := grid_tail_room hh
  have hp₀ : RespectsSemanticsBelow sem (D.cell c) p₀ :=
    hp.cap (hp.orderly ⟨c, GradedLe.refl _⟩).symm
  refine ⟨ρ, δ, f, hρ, hγδ, hδM, hδvis, hρh, ?_, ?_, rfl, ?_, hread, hcap⟩
  · exact AlignedCutEncoding.encode_respects (a.property.1.toBelow (D.cell c)) hp₀
      (fun e => e.2.2) hvis hpos hδvis hroom halign
  · exact AlignedCutEncoding.encode_cap s p₀ hroom halign
  · intro e
    apply AlignedCutEncoding.decode_encode s p₀ hρ.mono hroom hρh.ge
    intro d
    change min (ρ (a.val d.1)) δ = min (min (p d) (p ⟨c, GradedLe.refl _⟩)) δ
    rw [min_assoc, min_eq_right hδM]
    exact (hread d).symm

end VaughtConjecture.Knight.OwnerFaceAlignment
