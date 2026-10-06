/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PullbackSemantics

/-! # Pullbacks along retractions with partial sections; transport along bijections

`Semantics.pullback_isConsistent` and `RespectsSemanticsBelow.pullback_of_sect` demand a section
over **every** graded index.  Two different faces glued along a shared pair have no total section
(a face carries only its own level-three cells).  Availability is trivial when the request already
has the index of the larger cell (`Xi := Sig`), so sections are needed only for pairs of
**distinct** graded indices — `PartialSections` — and both theorems go through
(`Semantics.pullback_isConsistent'`, `RespectsSemanticsBelow.pullback_of_sect'`).  A labelling of
the extension that is constant on the fibres of the retraction (rigidity) descends along a
section to a respecting labelling of the base (`RespectsSemanticsBelow.descend`).

Respect and bountifulness transport along a bijection of lower sets preserving scopes and grades
with agreeing rows (`RespectsSemanticsBelow.of_equiv`, `respects_iff_of_equiv`,
`bountiful_of_equiv`).  Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

section RefinedPullback
variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {A : Finset ι} {A' : Finset ι'}
  {D : CellScheme A} {D' : CellScheme A'} {sem : Semantics D} {ret : Cell D' → Cell D}
  {mute : Cell D' → Prop} [DecidablePred mute]
  {hgrade : ∀ x, ¬ mute x → D'.grade x = D.grade (ret x)}
  {hscope : ∀ x y, ¬ mute x → ¬ mute y → D'.scope x ⊆ D'.scope y →
    D.scope (ret x) ⊆ D.scope (ret y)}
  {hmute_below : ∀ x d, ¬ mute x → GradedLe (D'.cell d) (D'.cell x) → ¬ mute d}

/-- **Partial sections**: a lift of every old cell at the index of the larger cell, for pairs of
distinct graded indices only. -/
def PartialSections (ret : Cell D' → Cell D) (mute : Cell D' → Prop) : Prop :=
  ∀ (Sig Xi₀ : Cell D') (Xi' : Cell D), ¬ mute Sig → ¬ mute Xi₀ →
    D'.scope Sig ⊆ D'.scope Xi₀ → D'.grade Sig = D'.grade Xi₀ → D'.cell Sig ≠ D'.cell Xi₀ →
    D.cell Xi' = D.cell (ret Xi₀) → ∃ Xi : Cell D', D'.cell Xi = D'.cell Xi₀ ∧ ret Xi = Xi'

omit [DecidablePred mute] in
include hgrade hscope in
/-- The retraction respects graded indices of non-mute cells. -/
theorem cell_ret_eq {x y : Cell D'} (hx : ¬ mute x) (hy : ¬ mute y) (h : D'.cell x = D'.cell y) :
    D.cell (ret x) = D.cell (ret y) := by
  refine Prod.ext (Finset.Subset.antisymm ?_ ?_) ?_
  · exact hscope x y hx hy (subset_of_eq (congrArg Prod.fst h))
  · exact hscope y x hy hx (subset_of_eq (congrArg Prod.fst h.symm))
  · change D.grade (ret x) = D.grade (ret y)
    rw [← hgrade x hx, ← hgrade y hy]; exact congrArg Prod.snd h

/-- **Consistency pulls back along a retraction with partial sections.** -/
theorem Semantics.pullback_isConsistent' (hcons : sem.IsConsistent)
    (hsect : PartialSections ret mute) :
    (sem.pullback ret mute hgrade hscope hmute_below).IsConsistent := by
  intro x
  by_cases hx : mute x
  · refine ⟨(sem.pullback ret mute hgrade hscope hmute_below).orderly x, ?_, ?_⟩
    · intro Sig
      refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
      funext d
      rw [Semantics.pullback_E_of_mute hx (CellScheme.below.incl Sig d),
        Semantics.pullback_E_of_mute hx Sig, min_self]
    · intro Sig Xi₀ _ _
      exact ⟨Xi₀, rfl, by rw [Semantics.pullback_E_of_mute hx, Semantics.pullback_E_of_mute hx]⟩
  · have hold := hcons (ret x)
    refine ⟨(sem.pullback ret mute hgrade hscope hmute_below).orderly x, ?_, ?_⟩
    · intro Sig
      have hSig : ¬ mute Sig.1 := hmute_below x Sig.1 hx Sig.2
      have key := (hold.locality (retBelow ret mute hgrade hscope hmute_below hx Sig)).reindex
        (retBelow ret mute hgrade hscope hmute_below hSig)
      refine transformsTo_congr ?_ ?_ ?_ key
      · funext d; exact (hgrade d.1 (hmute_below Sig.1 d.1 hSig d.2)).symm
      · funext d; exact (Semantics.pullback_E_of_not_mute hSig d).symm
      · funext d
        rw [Semantics.pullback_E_of_not_mute hx, Semantics.pullback_E_of_not_mute hx]
        rfl
    · intro Sig Xi₀ hs hg
      have hSig : ¬ mute Sig.1 := hmute_below x Sig.1 hx Sig.2
      have hXi₀ : ¬ mute Xi₀.1 := hmute_below x Xi₀.1 hx Xi₀.2
      by_cases hc : D'.cell Sig.1 = D'.cell Xi₀.1
      · exact ⟨Sig, hc, le_rfl⟩
      obtain ⟨Xi', hcell, hle⟩ := hold.availability
        (retBelow ret mute hgrade hscope hmute_below hx Sig)
        (retBelow ret mute hgrade hscope hmute_below hx Xi₀) (hscope _ _ hSig hXi₀ hs)
        (by
          change D.grade (ret Sig.1) = D.grade (ret Xi₀.1)
          rw [← hgrade _ hSig, ← hgrade _ hXi₀]; exact hg)
      obtain ⟨Xi, hXi, hret⟩ := hsect Sig.1 Xi₀.1 Xi'.1 hSig hXi₀ hs hg hc hcell
      set XiB : D'.below (D'.cell x) := ⟨Xi, by rw [hXi]; exact Xi₀.2⟩ with hXiB
      refine ⟨XiB, hXi, ?_⟩
      rw [Semantics.pullback_E_of_not_mute hx Sig, Semantics.pullback_E_of_not_mute hx XiB]
      have e : retBelow ret mute hgrade hscope hmute_below hx XiB = Xi' := Subtype.ext hret
      rw [e]
      exact hle

/-- **Respect pulls back along a retraction with partial sections.** -/
theorem RespectsSemanticsBelow.pullback_of_sect' {BJ : Finset ι' × ℕ} {BJ' : Finset ι × ℕ}
    (hnm : ∀ a : D'.below BJ, ¬ mute a.1)
    (hretB : ∀ a : D'.below BJ, GradedLe (D.cell (ret a.1)) BJ')
    (hsect : PartialSections ret mute)
    {r' : D.below BJ' → ExtOrd} (h : RespectsSemanticsBelow sem BJ' r') :
    RespectsSemanticsBelow (sem.pullback ret mute hgrade hscope hmute_below) BJ
      (fun a => r' ⟨ret a.1, hretB a⟩) where
  orderly a := by
    have := h.orderly ⟨ret a.1, hretB a⟩
    dsimp only at this ⊢
    rw [← hgrade _ (hnm a)] at this
    exact this
  locality Sig := by
    have hSig : ¬ mute Sig.1 := hnm Sig
    have key := (h.locality ⟨ret Sig.1, hretB Sig⟩).reindex
      (retBelow ret mute hgrade hscope hmute_below hSig)
    refine transformsTo_congr ?_ ?_ ?_ key
    · funext d
      exact (hgrade _ (hmute_below Sig.1 d.1 hSig d.2)).symm
    · funext d
      exact (Semantics.pullback_E_of_not_mute hSig d).symm
    · funext d
      rfl
  availability Sig Xi₀ hs hg := by
    have hSig : ¬ mute Sig.1 := hnm Sig
    have hXi₀ : ¬ mute Xi₀.1 := hnm Xi₀
    by_cases hc : D'.cell Sig.1 = D'.cell Xi₀.1
    · exact ⟨Sig, hc, le_rfl⟩
    obtain ⟨Xi', hcell, hle⟩ := h.availability ⟨ret Sig.1, hretB Sig⟩ ⟨ret Xi₀.1, hretB Xi₀⟩
      (hscope _ _ hSig hXi₀ hs)
      (by change D.grade (ret Sig.1) = D.grade (ret Xi₀.1)
          rw [← hgrade _ hSig, ← hgrade _ hXi₀]; exact hg)
    obtain ⟨Xi, hXi, hret⟩ := hsect Sig.1 Xi₀.1 Xi'.1 hSig hXi₀ hs hg hc hcell
    refine ⟨⟨Xi, by rw [hXi]; exact Xi₀.2⟩, hXi, ?_⟩
    have e : (⟨ret Xi, hretB ⟨Xi, by rw [hXi]; exact Xi₀.2⟩⟩ : D.below BJ') = Xi' :=
      Subtype.ext hret
    dsimp only
    rw [e]
    exact hle

/-- **Descent**: a labelling of the extension that is constant on the fibres of the retraction
(rigidity) descends along a section to a respecting labelling of the base. -/
theorem RespectsSemanticsBelow.descend {BJ : Finset ι' × ℕ} {BJ' : Finset ι × ℕ}
    {q : D'.below BJ → ExtOrd}
    (hq : RespectsSemanticsBelow (sem.pullback ret mute hgrade hscope hmute_below) BJ q)
    (hnm : ∀ a : D'.below BJ, ¬ mute a.1)
    (hretB : ∀ a : D'.below BJ, GradedLe (D.cell (ret a.1)) BJ')
    (hrig : ∀ x y : D'.below BJ, ret x.1 = ret y.1 → q x = q y)
    (sec : D.below BJ' → D'.below BJ) (hsec_ret : ∀ d, ret (sec d).1 = d.1)
    (hsec_le : ∀ d Sig : D.below BJ', GradedLe (D.cell d.1) (D.cell Sig.1) →
      GradedLe (D'.cell (sec d).1) (D'.cell (sec Sig).1))
    (hsec_scope : ∀ d Sig : D.below BJ', D.scope d.1 ⊆ D.scope Sig.1 →
      D'.scope (sec d).1 ⊆ D'.scope (sec Sig).1) :
    RespectsSemanticsBelow sem BJ' (fun d => q (sec d)) where
  orderly d := by
    have := hq.orderly (sec d)
    dsimp only at this ⊢
    rw [hgrade _ (hnm _), hsec_ret] at this
    exact this
  locality Sig := by
    let φ : D.below (D.cell Sig.1) → D'.below (D'.cell (sec Sig).1) := fun d =>
      ⟨(sec ⟨d.1, d.2.trans Sig.2⟩).1, hsec_le ⟨d.1, d.2.trans Sig.2⟩ Sig d.2⟩
    have key := (hq.locality (sec Sig)).reindex φ
    refine transformsTo_congr ?_ ?_ ?_ key
    · funext d
      change D'.grade (sec ⟨d.1, d.2.trans Sig.2⟩).1 = D.grade d.1
      rw [hgrade _ (hnm _)]
      exact congrArg D.grade (hsec_ret _)
    · funext d
      change (sem.pullback ret mute hgrade hscope hmute_below).E (sec Sig).1 (φ d) = sem.E Sig.1 d
      rw [Semantics.pullback_E_of_not_mute (hnm _)]
      exact sem.E_congr (hsec_ret Sig) (hsec_ret ⟨d.1, d.2.trans Sig.2⟩)
    · funext d
      rfl
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hcell, hle⟩ := hq.availability (sec Sig) (sec Xi₀) (hsec_scope Sig Xi₀ hs)
      (by
        rw [hgrade _ (hnm _), hgrade _ (hnm _), hsec_ret, hsec_ret]; exact hg)
    refine ⟨⟨ret Xi.1, hretB Xi⟩, ?_, ?_⟩
    · change D.cell (ret Xi.1) = D.cell Xi₀.1
      rw [cell_ret_eq (hgrade := hgrade) (hscope := hscope) (hnm Xi) (hnm (sec Xi₀)) hcell]
      exact congrArg D.cell (hsec_ret Xi₀)
    · rw [hrig (sec ⟨ret Xi.1, hretB Xi⟩) Xi (hsec_ret _)]
      exact hle

end RefinedPullback

section Transport
variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {A : Finset ι} {A' : Finset ι'}
  {D : CellScheme A} {D' : CellScheme A'} {sem : Semantics D} {sem' : Semantics D'}

/-- The graded order is reflected and preserved by a bijection preserving scopes and grades. -/
theorem gradedLe_iff_of_equiv {BJ : Finset ι' × ℕ} {BJ' : Finset ι × ℕ}
    (e : D'.below BJ ≃ D.below BJ') (hgrade : ∀ a, D'.grade a.1 = D.grade (e a).1)
    (hscope : ∀ a b, D'.scope a.1 ⊆ D'.scope b.1 ↔ D.scope (e a).1 ⊆ D.scope (e b).1)
    (a b : D'.below BJ) :
    GradedLe (D'.cell a.1) (D'.cell b.1) ↔ GradedLe (D.cell (e a).1) (D.cell (e b).1) := by
  constructor
  · rintro ⟨hs, hg⟩
    refine ⟨(hscope a b).mp hs, ?_⟩
    change D.grade (e a).1 ≤ D.grade (e b).1
    rw [← hgrade, ← hgrade]; exact hg
  · rintro ⟨hs, hg⟩
    refine ⟨(hscope a b).mpr hs, ?_⟩
    change D'.grade a.1 ≤ D'.grade b.1
    rw [hgrade, hgrade]; exact hg

/-- **Respect transports along a bijection of lower sets with agreeing rows.** -/
theorem RespectsSemanticsBelow.of_equiv {BJ : Finset ι' × ℕ} {BJ' : Finset ι × ℕ}
    (e : D'.below BJ ≃ D.below BJ') (hgrade : ∀ a, D'.grade a.1 = D.grade (e a).1)
    (hscope : ∀ a b, D'.scope a.1 ⊆ D'.scope b.1 ↔ D.scope (e a).1 ⊆ D.scope (e b).1)
    (hrows : ∀ (Sig : D'.below BJ) (d : D'.below (D'.cell Sig.1))
      (hd : GradedLe (D.cell (e ⟨d.1, d.2.trans Sig.2⟩).1) (D.cell (e Sig).1)),
      sem'.E Sig.1 d = sem.E (e Sig).1 ⟨(e ⟨d.1, d.2.trans Sig.2⟩).1, hd⟩)
    {q : D.below BJ' → ExtOrd} (hq : RespectsSemanticsBelow sem BJ' q) :
    RespectsSemanticsBelow sem' BJ (fun a => q (e a)) where
  orderly a := by
    have := hq.orderly (e a)
    dsimp only at this ⊢
    rw [hgrade]; exact this
  locality Sig := by
    let φ : D'.below (D'.cell Sig.1) → D.below (D.cell (e Sig).1) := fun d =>
      ⟨(e ⟨d.1, d.2.trans Sig.2⟩).1, (gradedLe_iff_of_equiv e hgrade hscope _ _).mp d.2⟩
    have key := (hq.locality (e Sig)).reindex φ
    refine transformsTo_congr ?_ ?_ ?_ key
    · funext d
      exact (hgrade ⟨d.1, d.2.trans Sig.2⟩).symm
    · funext d
      exact (hrows Sig d _).symm
    · funext d
      rfl
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hcell, hle⟩ := hq.availability (e Sig) (e Xi₀) ((hscope _ _).mp hs)
      (by rw [← hgrade, ← hgrade]; exact hg)
    refine ⟨e.symm Xi, ?_, ?_⟩
    · apply GradedLe.antisymm'
      · rw [gradedLe_iff_of_equiv e hgrade hscope, e.apply_symm_apply, hcell]
        exact ⟨Finset.Subset.refl _, le_rfl⟩
      · rw [gradedLe_iff_of_equiv e hgrade hscope, e.apply_symm_apply, hcell]
        exact ⟨Finset.Subset.refl _, le_rfl⟩
    · rw [e.apply_symm_apply]; exact hle

/-- **Bountifulness transports along compatible bijections of the two lower sets.** -/
theorem bountiful_of_equiv {CI BJ : Finset ι' × ℕ} {CI' BJ' : Finset ι × ℕ}
    (h : GradedLe CI BJ) (h' : GradedLe CI' BJ')
    (eB : D'.below BJ ≃ D.below BJ') (eC : D'.below CI ≃ D.below CI')
    (hmonoE : ∀ d : D'.below CI, eB (CellScheme.below.mono h d) = CellScheme.below.mono h' (eC d))
    (hRB : ∀ q : D'.below BJ → ExtOrd,
      RespectsSemanticsBelow sem' BJ q ↔ RespectsSemanticsBelow sem BJ' (q ∘ eB.symm))
    (hRC : ∀ p : D'.below CI → ExtOrd,
      RespectsSemanticsBelow sem' CI p ↔ RespectsSemanticsBelow sem CI' (p ∘ eC.symm))
    (hb : ∀ (p : D.below CI' → ExtOrd) (q : D.below BJ' → ExtOrd) (γ : ExtOrd),
      RespectsSemanticsBelow sem CI' p → RespectsSemanticsBelow sem BJ' q →
      extVisibilityReplace γ BJ'.2 BJ'.2 = γ →
      (∀ d : D.below CI', min (q (CellScheme.below.mono h' d)) γ = min (p d) γ) →
      ∃ q' : D.below BJ' → ExtOrd, RespectsSemanticsBelow sem BJ' q' ∧
        (∀ d : D.below BJ', min (q' d) γ = min (q d) γ) ∧
        (∀ d : D.below CI', q' (CellScheme.below.mono h' d) = p d))
    (hgradeBJ : BJ.2 = BJ'.2)
    (p : D'.below CI → ExtOrd) (q : D'.below BJ → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow sem' CI p) (hq : RespectsSemanticsBelow sem' BJ q)
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ)
    (hagree : ∀ d : D'.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D'.below BJ → ExtOrd, RespectsSemanticsBelow sem' BJ q' ∧
      (∀ d : D'.below BJ, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D'.below CI, q' (CellScheme.below.mono h d) = p d) := by
  obtain ⟨q₀, hq₀, hq₀γ, hq₀p⟩ := hb (p ∘ eC.symm) (q ∘ eB.symm) γ ((hRC p).mp hp) ((hRB q).mp hq)
    (by rw [← hgradeBJ]; exact hγ)
    (by
      intro d'
      have e1 : CellScheme.below.mono h' d' = eB (CellScheme.below.mono h (eC.symm d')) := by
        rw [hmonoE, eC.apply_symm_apply]
      change min (q (eB.symm (CellScheme.below.mono h' d'))) γ = min (p (eC.symm d')) γ
      rw [e1, eB.symm_apply_apply]
      exact hagree (eC.symm d'))
  refine ⟨q₀ ∘ eB, ?_, ?_, ?_⟩
  · rw [hRB]
    have : (q₀ ∘ eB) ∘ eB.symm = q₀ := by funext d; simp
    rw [this]; exact hq₀
  · intro d
    have := hq₀γ (eB d)
    change min (q₀ (eB d)) γ = min (q (eB.symm (eB d))) γ at this
    rw [eB.symm_apply_apply] at this
    exact this
  · intro d
    have := hq₀p (eC d)
    change q₀ (CellScheme.below.mono h' (eC d)) = p (eC.symm (eC d)) at this
    rw [eC.symm_apply_apply] at this
    change q₀ (eB (CellScheme.below.mono h d)) = p d
    rw [hmonoE]; exact this

end Transport

theorem Semantics.E_congr' {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    (sem : Semantics D) {x y : Cell D} (h : x = y) {d : D.below (D.cell x)}
    {d' : D.below (D.cell y)} (hd : d.1 = d'.1) : sem.E x d = sem.E y d' := by
  subst h
  rw [Subtype.ext hd]

section Transport2
variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {A : Finset ι} {A' : Finset ι'}
  {D : CellScheme A} {D' : CellScheme A'} {sem : Semantics D} {sem' : Semantics D'}

/-- **Respect transports both ways** along a bijection with agreeing rows. -/
theorem respects_iff_of_equiv {BJ : Finset ι' × ℕ} {BJ' : Finset ι × ℕ}
    (e : D'.below BJ ≃ D.below BJ') (hgrade : ∀ a, D'.grade a.1 = D.grade (e a).1)
    (hscope : ∀ a b, D'.scope a.1 ⊆ D'.scope b.1 ↔ D.scope (e a).1 ⊆ D.scope (e b).1)
    (hrows : ∀ (Sig : D'.below BJ) (d : D'.below (D'.cell Sig.1))
      (hd : GradedLe (D.cell (e ⟨d.1, d.2.trans Sig.2⟩).1) (D.cell (e Sig).1)),
      sem'.E Sig.1 d = sem.E (e Sig).1 ⟨(e ⟨d.1, d.2.trans Sig.2⟩).1, hd⟩)
    (q : D'.below BJ → ExtOrd) :
    RespectsSemanticsBelow sem' BJ q ↔ RespectsSemanticsBelow sem BJ' (q ∘ e.symm) := by
  constructor
  · intro hq
    refine RespectsSemanticsBelow.of_equiv (sem := sem') (sem' := sem) e.symm
      (fun b => by rw [hgrade (e.symm b), e.apply_symm_apply])
      (fun a b => by rw [hscope (e.symm a) (e.symm b), e.apply_symm_apply, e.apply_symm_apply])
      ?_ hq
    intro Sig d hd
    have hv1 : (e (e.symm ⟨d.1, d.2.trans Sig.2⟩)).1 = d.1 :=
      congrArg Subtype.val (e.apply_symm_apply ⟨d.1, d.2.trans Sig.2⟩)
    have hv2 : (e (e.symm Sig)).1 = Sig.1 := congrArg Subtype.val (e.apply_symm_apply Sig)
    have hd0 : GradedLe (D.cell (e (e.symm ⟨d.1, d.2.trans Sig.2⟩)).1)
        (D.cell (e (e.symm Sig)).1) := by
      rw [hv1, hv2]; exact d.2
    have h1 := hrows (e.symm Sig) ⟨(e.symm ⟨d.1, d.2.trans Sig.2⟩).1, hd⟩ hd0
    have h2 : sem.E Sig.1 d =
        sem.E (e (e.symm Sig)).1 ⟨(e (e.symm ⟨d.1, d.2.trans Sig.2⟩)).1, hd0⟩ :=
      sem.E_congr' hv2.symm hv1.symm
    exact h2.trans h1.symm
  · intro hq
    have := RespectsSemanticsBelow.of_equiv e hgrade hscope hrows hq
    convert this using 1
    funext a
    change q a = q (e.symm (e a))
    rw [e.symm_apply_apply]

end Transport2

end VaughtConjecture.Knight
