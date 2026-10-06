/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.Domain

/-! # Pullback semantics along a graded retraction, with mute cells

A scheme `D'` whose cells retract onto the cells of a scheme `D` carrying a semantics `sem`:
`ret : Cell D' → Cell D` preserves grades and scope inclusions on the non-mute cells.  The
**pullback semantics** (`Semantics.pullback`) gives a non-mute cell `x` the row of `ret x` read
through `ret`, and a mute cell the row `⊥`.

* It is **coded** when `sem` is, and **consistent** when `sem` is, provided mute cells never lie
  below non-mute cells and `ret` has **sections over graded indices**: for every non-mute cell `Xi₀`
  and old cell `Xi'` of the graded index of `ret Xi₀`, some cell of the graded index of `Xi₀`
  retracts to `Xi'` (availability witnesses lift; `Semantics.pullback_isConsistent`).
* **Respect transports** both ways along a bijective retraction of lower sets
  (`RespectsSemanticsBelow.of_pullback`, `RespectsSemanticsBelow.pullback`), and the pullback of a
  respecting labelling along a retraction with sections respects (`pullback_of_sect`).
* **Bountifulness transports** along bijective retractions of both lower sets
  (`bountiful_pullback_of_bij`).
* **Controller probes** (`RespectsSemanticsBelow.eq_of_controller_probes`): two cells of the same
  grade at which every full-scope controller of that grade reads the same value carry the same
  label under every respecting labelling.  For a pullback along a retraction this gives
  **uniqueness of extension over a fixed old labelling**: respecting labellings factor through the
  retraction (`Knight/FourPointDuplication.lean`).

Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

section Pullback

variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {A : Finset ι} {A' : Finset ι'}
  {D : CellScheme A} {D' : CellScheme A'} (sem : Semantics D) (ret : Cell D' → Cell D)
  (mute : Cell D' → Prop) [DecidablePred mute]
  (hgrade : ∀ x, ¬ mute x → D'.grade x = D.grade (ret x))
  (hscope : ∀ x y, ¬ mute x → ¬ mute y → D'.scope x ⊆ D'.scope y →
    D.scope (ret x) ⊆ D.scope (ret y))
  (hmute_below : ∀ x d, ¬ mute x → GradedLe (D'.cell d) (D'.cell x) → ¬ mute d)

omit [DecidablePred mute] in
include hgrade hscope hmute_below in
/-- The graded preorder is preserved by the retraction below a non-mute cell. -/
theorem gradedLe_ret {a b : Cell D'} (hb : ¬ mute b) (h : GradedLe (D'.cell a) (D'.cell b)) :
    GradedLe (D.cell (ret a)) (D.cell (ret b)) :=
  have ha : ¬ mute a := hmute_below b a hb h
  ⟨hscope a b ha hb h.1, by
    change D.grade (ret a) ≤ D.grade (ret b)
    rw [← hgrade a ha, ← hgrade b hb]; exact h.2⟩

/-- The lower set of a non-mute cell maps into the lower set of its retraction. -/
def retBelow {x : Cell D'} (hx : ¬ mute x) (d : D'.below (D'.cell x)) : D.below (D.cell (ret x)) :=
  ⟨ret d.1, gradedLe_ret ret mute hgrade hscope hmute_below hx d.2⟩

/-- **The pullback semantics.** -/
noncomputable def Semantics.pullback : Semantics D' where
  E x d := if hx : mute x then ⊥ else
    sem.E (ret x) (retBelow ret mute hgrade hscope hmute_below hx d)
  orderly x d := by
    change (if hx : mute x then ⊥ else
      sem.E (ret x) (retBelow ret mute hgrade hscope hmute_below hx d)) =
      extVisibilityReplace _ (D'.grade d.1) (D'.grade d.1)
    split_ifs with hx
    · exact (extVisibilityReplace_bot _ _).symm
    · rw [hgrade d.1 (hmute_below x d.1 hx d.2)]
      exact sem.orderly (ret x) (retBelow ret mute hgrade hscope hmute_below hx d)

variable {sem ret mute hgrade hscope hmute_below}

theorem Semantics.pullback_E_of_mute {x : Cell D'} (hx : mute x) (d : D'.below (D'.cell x)) :
    (sem.pullback ret mute hgrade hscope hmute_below).E x d = ⊥ := by
  change (if hx : mute x then ⊥ else _) = ⊥
  rw [dite_of_pos hx]

theorem Semantics.pullback_E_of_not_mute {x : Cell D'} (hx : ¬ mute x) (d : D'.below (D'.cell x)) :
    (sem.pullback ret mute hgrade hscope hmute_below).E x d =
      sem.E (ret x) (retBelow ret mute hgrade hscope hmute_below hx d) := by
  change (if hx : mute x then ⊥ else _) = _
  rw [dite_of_neg hx]

/-- Coding pulls back (the grade of the owner is preserved). -/
theorem Semantics.pullback_isCoded (h : sem.IsCoded) :
    (sem.pullback ret mute hgrade hscope hmute_below).IsCoded := by
  intro x d
  by_cases hx : mute x
  · rw [Semantics.pullback_E_of_mute hx]; exact Or.inl rfl
  · rw [Semantics.pullback_E_of_not_mute hx, hgrade x hx]; exact h (ret x) _

/-- **Consistency pulls back**: locality at a non-mute cell is the old locality reindexed along
the retraction of lower sets; availability lifts the old witness through a section. -/
theorem Semantics.pullback_isConsistent (hcons : sem.IsConsistent)
    (hsect : ∀ (Xi₀ : Cell D') (Xi' : Cell D), ¬ mute Xi₀ → D.cell Xi' = D.cell (ret Xi₀) →
      ∃ Xi : Cell D', D'.cell Xi = D'.cell Xi₀ ∧ ret Xi = Xi') :
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
      obtain ⟨Xi', hcell, hle⟩ := hold.availability
        (retBelow ret mute hgrade hscope hmute_below hx Sig)
        (retBelow ret mute hgrade hscope hmute_below hx Xi₀) (hscope _ _ hSig hXi₀ hs)
        (by
          change D.grade (ret Sig.1) = D.grade (ret Xi₀.1)
          rw [← hgrade _ hSig, ← hgrade _ hXi₀]; exact hg)
      obtain ⟨Xi, hXi, hret⟩ := hsect Xi₀.1 Xi'.1 hXi₀ hcell
      set XiB : D'.below (D'.cell x) := ⟨Xi, by rw [hXi]; exact Xi₀.2⟩ with hXiB
      refine ⟨XiB, hXi, ?_⟩
      rw [Semantics.pullback_E_of_not_mute hx Sig, Semantics.pullback_E_of_not_mute hx XiB]
      have e : retBelow ret mute hgrade hscope hmute_below hx XiB = Xi' := Subtype.ext hret
      rw [e]
      exact hle

/-! ### Transport of respect and bountifulness along a bijective retraction of lower sets -/

theorem GradedLe.antisymm' {κ : Type*} {X Y : Finset κ × ℕ} (h₁ : GradedLe X Y)
    (h₂ : GradedLe Y X) :
    X = Y :=
  Prod.ext (Finset.Subset.antisymm h₁.1 h₂.1) (le_antisymm h₁.2 h₂.2)

section Transport

variable {BJ : Finset ι' × ℕ} {BJ' : Finset ι × ℕ}

theorem ret_symm_val (e : D'.below BJ ≃ D.below BJ') (he : ∀ a, (e a).1 = ret a.1)
    (d' : D.below BJ') : ret (e.symm d').1 = d'.1 := by
  rw [← he, Equiv.apply_symm_apply]

omit [DecidablePred mute] in
theorem grade_symm (hg : ∀ x, ¬ mute x → D'.grade x = D.grade (ret x))
    (hnm : ∀ a : D'.below BJ, ¬ mute a.1) (e : D'.below BJ ≃ D.below BJ')
    (he : ∀ a, (e a).1 = ret a.1) (d' : D.below BJ') : D'.grade (e.symm d').1 = D.grade d'.1 := by
  rw [hg _ (hnm _), ret_symm_val e he]

theorem gradedLe_symm_iff (e : D'.below BJ ≃ D.below BJ') (he : ∀ a, (e a).1 = ret a.1)
    (hle : ∀ a b : D'.below BJ, GradedLe (D'.cell a.1) (D'.cell b.1) ↔
      GradedLe (D.cell (ret a.1)) (D.cell (ret b.1))) (a' b' : D.below BJ') :
    GradedLe (D'.cell (e.symm a').1) (D'.cell (e.symm b').1) ↔
      GradedLe (D.cell a'.1) (D.cell b'.1) := by
  rw [hle, ret_symm_val e he, ret_symm_val e he]

/-- The inverse bijection on the lower set of a cell. -/
def belowInv (e : D'.below BJ ≃ D.below BJ') (he : ∀ a, (e a).1 = ret a.1)
    (hle : ∀ a b : D'.below BJ, GradedLe (D'.cell a.1) (D'.cell b.1) ↔
      GradedLe (D.cell (ret a.1)) (D.cell (ret b.1)))
    (Sig' : D.below BJ') (d' : D.below (D.cell Sig'.1)) : D'.below (D'.cell (e.symm Sig').1) :=
  ⟨(e.symm ⟨d'.1, d'.2.trans Sig'.2⟩).1, (gradedLe_symm_iff e he hle _ _).mpr d'.2⟩

/-- **Respect transports from the pullback to the old semantics** along a bijective retraction of
lower sets. -/
theorem RespectsSemanticsBelow.of_pullback (hnm : ∀ a : D'.below BJ, ¬ mute a.1)
    (e : D'.below BJ ≃ D.below BJ') (he : ∀ a, (e a).1 = ret a.1)
    (hle : ∀ a b : D'.below BJ, GradedLe (D'.cell a.1) (D'.cell b.1) ↔
      GradedLe (D.cell (ret a.1)) (D.cell (ret b.1)))
    {r : D'.below BJ → ExtOrd}
    (h : RespectsSemanticsBelow (sem.pullback ret mute hgrade hscope hmute_below) BJ r) :
    RespectsSemanticsBelow sem BJ' (r ∘ e.symm) where
  orderly d' := by
    have := h.orderly (e.symm d')
    dsimp only at this ⊢
    rw [grade_symm hgrade hnm e he] at this
    exact this
  locality Sig' := by
    have hSig : ¬ mute (e.symm Sig').1 := hnm _
    have key := (h.locality (e.symm Sig')).reindex (belowInv e he hle Sig')
    refine transformsTo_congr ?_ ?_ ?_ key
    · funext d'
      exact grade_symm hgrade hnm e he _
    · funext d'
      change (sem.pullback ret mute hgrade hscope hmute_below).E (e.symm Sig').1
        (belowInv e he hle Sig' d') = sem.E Sig'.1 d'
      rw [Semantics.pullback_E_of_not_mute hSig]
      exact sem.E_congr (ret_symm_val e he Sig') (ret_symm_val e he _)
    · funext d'
      rfl
  availability Sig' Xi₀' hs hg := by
    have hs' : D'.scope (e.symm Sig').1 ⊆ D'.scope (e.symm Xi₀').1 :=
      ((gradedLe_symm_iff e he hle _ _).mpr ⟨hs, hg.le⟩).1
    have hg' : D'.grade (e.symm Sig').1 = D'.grade (e.symm Xi₀').1 := by
      rw [grade_symm hgrade hnm e he, grade_symm hgrade hnm e he]; exact hg
    obtain ⟨Xi, hcell, hle'⟩ := h.availability (e.symm Sig') (e.symm Xi₀') hs' hg'
    refine ⟨e Xi, ?_, ?_⟩
    · have h1 : GradedLe (D'.cell Xi.1) (D'.cell (e.symm Xi₀').1) := hcell ▸ GradedLe.refl _
      have h2 : GradedLe (D'.cell (e.symm Xi₀').1) (D'.cell Xi.1) := hcell ▸ GradedLe.refl _
      have h1' := (hle _ _).mp h1
      have h2' := (hle _ _).mp h2
      rw [ret_symm_val e he] at h1' h2'
      rw [he]
      exact GradedLe.antisymm' h1' h2'
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hle'

/-- **Respect transports from the old semantics to the pullback** along a bijective retraction of
lower sets. -/
theorem RespectsSemanticsBelow.pullback (hnm : ∀ a : D'.below BJ, ¬ mute a.1)
    (e : D'.below BJ ≃ D.below BJ') (he : ∀ a, (e a).1 = ret a.1)
    (hle : ∀ a b : D'.below BJ, GradedLe (D'.cell a.1) (D'.cell b.1) ↔
      GradedLe (D.cell (ret a.1)) (D.cell (ret b.1)))
    {r' : D.below BJ' → ExtOrd} (h : RespectsSemanticsBelow sem BJ' r') :
    RespectsSemanticsBelow (sem.pullback ret mute hgrade hscope hmute_below) BJ (r' ∘ e) where
  orderly d := by
    have := h.orderly (e d)
    dsimp only at this ⊢
    rw [he, ← hgrade _ (hnm d)] at this
    exact this
  locality Sig := by
    have hSig : ¬ mute Sig.1 := hnm Sig
    let φ : D'.below (D'.cell Sig.1) → D.below (D.cell (e Sig).1) := fun d =>
      ⟨ret d.1, by rw [he Sig]; exact gradedLe_ret ret mute hgrade hscope hmute_below hSig d.2⟩
    have key := (h.locality (e Sig)).reindex φ
    refine transformsTo_congr ?_ ?_ ?_ key
    · funext d
      exact (hgrade _ (hmute_below Sig.1 d.1 hSig d.2)).symm
    · funext d
      change sem.E (e Sig).1 (φ d) = (sem.pullback ret mute hgrade hscope hmute_below).E Sig.1 d
      rw [Semantics.pullback_E_of_not_mute hSig]
      exact sem.E_congr (he Sig) rfl
    · funext d
      change min (r' (CellScheme.below.incl (e Sig) (φ d))) (r' (e Sig)) =
        min (r' (e (CellScheme.below.incl Sig d))) (r' (e Sig))
      congr 2
      apply Subtype.ext
      rw [he]
      rfl
  availability Sig Xi₀ hs hg := by
    have hs' : D.scope (e Sig).1 ⊆ D.scope (e Xi₀).1 := by
      rw [he, he]; exact hscope _ _ (hnm Sig) (hnm Xi₀) hs
    have hg' : D.grade (e Sig).1 = D.grade (e Xi₀).1 := by
      rw [he, he, ← hgrade _ (hnm Sig), ← hgrade _ (hnm Xi₀)]; exact hg
    obtain ⟨Xi', hcell, hle'⟩ := h.availability (e Sig) (e Xi₀) hs' hg'
    refine ⟨e.symm Xi', ?_, ?_⟩
    · have h1 : GradedLe (D.cell Xi'.1) (D.cell (e Xi₀).1) := hcell ▸ GradedLe.refl _
      have h2 : GradedLe (D.cell (e Xi₀).1) (D.cell Xi'.1) := hcell ▸ GradedLe.refl _
      rw [he] at h1 h2
      have h1' : GradedLe (D.cell (ret (e.symm Xi').1)) (D.cell (ret Xi₀.1)) := by
        rwa [ret_symm_val e he]
      have h2' : GradedLe (D.cell (ret Xi₀.1)) (D.cell (ret (e.symm Xi').1)) := by
        rwa [ret_symm_val e he]
      exact GradedLe.antisymm' ((hle _ _).mpr h1') ((hle _ _).mpr h2')
    · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hle'

end Transport

/-- **Bountifulness transports along bijective retractions of lower sets**: an instance of
Def. 2.5.14 for the pullback at `CI ≤ BJ` follows from the instance for the old semantics at
`CI' ≤ BJ'` when the retraction is a bijection of both lower sets. -/
theorem bountiful_pullback_of_bij {CI BJ : Finset ι' × ℕ} {CI' BJ' : Finset ι × ℕ}
    (h : GradedLe CI BJ) (h' : GradedLe CI' BJ')
    (hnmB : ∀ a : D'.below BJ, ¬ mute a.1) (hnmC : ∀ a : D'.below CI, ¬ mute a.1)
    (eB : D'.below BJ ≃ D.below BJ') (heB : ∀ a, (eB a).1 = ret a.1)
    (hleB : ∀ a b : D'.below BJ, GradedLe (D'.cell a.1) (D'.cell b.1) ↔
      GradedLe (D.cell (ret a.1)) (D.cell (ret b.1)))
    (eC : D'.below CI ≃ D.below CI') (heC : ∀ a, (eC a).1 = ret a.1)
    (hleC : ∀ a b : D'.below CI, GradedLe (D'.cell a.1) (D'.cell b.1) ↔
      GradedLe (D.cell (ret a.1)) (D.cell (ret b.1)))
    (hb : ∀ (p : D.below CI' → ExtOrd) (q : D.below BJ' → ExtOrd) (γ : ExtOrd),
      RespectsSemanticsBelow sem CI' p → RespectsSemanticsBelow sem BJ' q →
      extVisibilityReplace γ BJ'.2 BJ'.2 = γ →
      (∀ d : D.below CI', min (q (CellScheme.below.mono h' d)) γ = min (p d) γ) →
      ∃ q' : D.below BJ' → ExtOrd, RespectsSemanticsBelow sem BJ' q' ∧
        (∀ d : D.below BJ', min (q' d) γ = min (q d) γ) ∧
        (∀ d : D.below CI', q' (CellScheme.below.mono h' d) = p d))
    (hgradeBJ : BJ.2 = BJ'.2)
    (p : D'.below CI → ExtOrd) (q : D'.below BJ → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow (sem.pullback ret mute hgrade hscope hmute_below) CI p)
    (hq : RespectsSemanticsBelow (sem.pullback ret mute hgrade hscope hmute_below) BJ q)
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ)
    (hagree : ∀ d : D'.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D'.below BJ → ExtOrd,
      RespectsSemanticsBelow (sem.pullback ret mute hgrade hscope hmute_below) BJ q' ∧
      (∀ d : D'.below BJ, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D'.below CI, q' (CellScheme.below.mono h d) = p d) := by
  -- the bijections commute with the inclusions of lower sets
  have hmonoE : ∀ d : D'.below CI, eB (CellScheme.below.mono h d) =
      CellScheme.below.mono h' (eC d) := fun d => by
    apply Subtype.ext; rw [heB]; change ret d.1 = (eC d).1; rw [heC]
  obtain ⟨q₀, hq₀, hq₀γ, hq₀p⟩ := hb (p ∘ eC.symm) (q ∘ eB.symm) γ
    (RespectsSemanticsBelow.of_pullback hnmC eC heC hleC hp)
    (RespectsSemanticsBelow.of_pullback hnmB eB heB hleB hq)
    (by rwa [← hgradeBJ])
    (fun d' => by
      have e1 : CellScheme.below.mono h' d' = eB (CellScheme.below.mono h (eC.symm d')) := by
        rw [hmonoE, Equiv.apply_symm_apply]
      simp only [Function.comp_apply]
      rw [e1, Equiv.symm_apply_apply]
      exact hagree _)
  refine ⟨q₀ ∘ eB, RespectsSemanticsBelow.pullback hnmB eB heB hleB hq₀, fun d => ?_, fun d => ?_⟩
  · simp only [Function.comp_apply]
    rw [hq₀γ, Function.comp_apply, Equiv.symm_apply_apply]
  · simp only [Function.comp_apply]
    rw [hmonoE, hq₀p, Function.comp_apply, Equiv.symm_apply_apply]

/-- **Pullback of a respecting labelling** along the retraction (not necessarily bijective): when
every cell of the lower set is non-mute, the retraction maps it into the old lower set, and
sections exist, the pullback of a labelling respecting the old semantics respects the pullback. -/
theorem RespectsSemanticsBelow.pullback_of_sect {BJ : Finset ι' × ℕ} {BJ' : Finset ι × ℕ}
    (hnm : ∀ a : D'.below BJ, ¬ mute a.1)
    (hretB : ∀ a : D'.below BJ, GradedLe (D.cell (ret a.1)) BJ')
    (hsect : ∀ (Xi₀ : Cell D') (Xi' : Cell D), ¬ mute Xi₀ → D.cell Xi' = D.cell (ret Xi₀) →
      ∃ Xi : Cell D', D'.cell Xi = D'.cell Xi₀ ∧ ret Xi = Xi')
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
    obtain ⟨Xi', hcell, hle⟩ := h.availability ⟨ret Sig.1, hretB Sig⟩ ⟨ret Xi₀.1, hretB Xi₀⟩
      (hscope _ _ hSig hXi₀ hs)
      (by change D.grade (ret Sig.1) = D.grade (ret Xi₀.1)
          rw [← hgrade _ hSig, ← hgrade _ hXi₀]; exact hg)
    obtain ⟨Xi, hXi, hret⟩ := hsect Xi₀.1 Xi'.1 hXi₀ hcell
    refine ⟨⟨Xi, by rw [hXi]; exact Xi₀.2⟩, hXi, ?_⟩
    have e : (⟨ret Xi, hretB ⟨Xi, by rw [hXi]; exact Xi₀.2⟩⟩ : D.below BJ') = Xi' :=
      Subtype.ext hret
    dsimp only
    rw [e]
    exact hle

end Pullback

section ControllerProbes

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ} {q : D.below BJ → ExtOrd}

/-- **Equal readings at every full-scope controller force equal labels** (review lemma,
2026-09-05): for two cells of the same grade in a lower set, if every controller at the full-scope
index of that grade reads the same value at both, then every respecting labelling agrees at them —
locality at each controller equalizes the probes `min (q x) (q Ξ) = min (q y) (q Ξ)`, and
availability supplies a controller dominating `q x` (respectively `q y`), giving each inequality.
Respecting labellings therefore factor through any retraction whose rows are pulled back. -/
theorem RespectsSemanticsBelow.eq_of_controller_probes
    (hq : RespectsSemanticsBelow sem BJ q) (x y : D.below BJ)
    (hgrade : D.grade x.1 = D.grade y.1)
    (hc : ∃ c : D.below BJ, D.cell c.1 = (BJ.1, D.grade x.1))
    (hrows : ∀ (c : D.below BJ) (hx : GradedLe (D.cell x.1) (D.cell c.1))
      (hy : GradedLe (D.cell y.1) (D.cell c.1)),
      D.cell c.1 = (BJ.1, D.grade x.1) →
      sem.E c.1 ⟨x.1, hx⟩ = sem.E c.1 ⟨y.1, hy⟩) : q x = q y := by
  obtain ⟨c0, hc0⟩ := hc
  have hc0scope : D.scope c0.1 = BJ.1 := by
    change (D.cell c0.1).1 = BJ.1
    rw [hc0]
  have hc0grade : D.grade c0.1 = D.grade x.1 := by
    change (D.cell c0.1).2 = D.grade x.1
    rw [hc0]
  have probes : ∀ c : D.below BJ, D.cell c.1 = (BJ.1, D.grade x.1) →
      min (q x) (q c) = min (q y) (q c) := by
    intro c hc
    have hx : GradedLe (D.cell x.1) (D.cell c.1) := by
      rw [hc]; exact ⟨x.2.1, le_rfl⟩
    have hy : GradedLe (D.cell y.1) (D.cell c.1) := by
      rw [hc]; exact ⟨y.2.1, hgrade.symm.le⟩
    obtain ⟨g, σ, _, _, _, _, _, heq⟩ := hq.locality c
    have ex := heq ⟨x.1, hx⟩
    have ey := heq ⟨y.1, hy⟩
    change min (q x) (q c) = min (σ (sem.E c.1 ⟨x.1, hx⟩)) (g (D.grade x.1)) at ex
    change min (q y) (q c) = min (σ (sem.E c.1 ⟨y.1, hy⟩)) (g (D.grade y.1)) at ey
    rw [ex, ey, hrows c hx hy hc, hgrade]
  obtain ⟨cx, hcx, hxle⟩ := hq.availability x c0
    (hc0scope.symm ▸ x.2.1) hc0grade.symm
  obtain ⟨cy, hcy, hyle⟩ := hq.availability y c0
    (hc0scope.symm ▸ y.2.1) (hgrade.symm.trans hc0grade.symm)
  apply le_antisymm
  · calc q x = min (q x) (q cx) := (min_eq_left hxle).symm
         _ = min (q y) (q cx) := probes cx (hcx.trans hc0)
         _ ≤ q y := min_le_left _ _
  · calc q y = min (q y) (q cy) := (min_eq_left hyle).symm
         _ = min (q x) (q cy) := (probes cy (hcy.trans hc0)).symm
         _ ≤ q x := min_le_left _ _
end ControllerProbes

end VaughtConjecture.Knight
