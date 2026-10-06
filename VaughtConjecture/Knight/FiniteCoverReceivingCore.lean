/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteCutReceiving
public import VaughtConjecture.Knight.StageCappedRepair
public import VaughtConjecture.Knight.GradeSplice
public import VaughtConjecture.Knight.VisibleFaceOneStep
public import VaughtConjecture.Knight.CapObservation

/-! # Finite-cover receiving at one stage

**Transfer of an arbitrary finite legal donor over an exact realized root**, retaining the donor's
literal scheme and agreeing with it below a requested cutoff, without spending stage blocks
(newapproach17 new33 §3): finite-cut receiving (supplied independently of modelhood) is
applied one point at a time along a saturated chain of visible faces of the donor's plan
(`IsPlan.exists_visible_card_succ_superface`), at one auxiliary cap `γ` self-visible at the
donor's point count and above the requested cutoff.  Before each application the donor is
**repaired to the actual current receiving root**: bountifulness of the donor's own scheme
(`exists_respects_extends_capped_emb`, the arbitrary-embedding form of
`exists_respects_extends_capped`) installs the received face literally while retaining every
`γ`-cap, and the stage bound is restored by strict truncation (`truncExt`), which does not
disturb the `γ`-caps since `γ` lies below the stage.  Agreement below the cap is never treated
as equality of the intermediate roots: the next candidate restricts to the actual received type
exactly.  `finiteCoverReceiving` then chooses the cap `ofOrd (ν + m)` for the requested cutoff
`ofOrd ν` and caps down. -/

@[expose] public section

namespace VaughtConjecture.Knight.FiniteCoverReceiving

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CellScheme.restrictFace

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}


/-- **Finite-cover receiving at an auxiliary cap.**  For a donor `Q` on `m` points whose face `f`
is the realized root `t ↦ p`, and a cap `γ` self-visible at `m`, proper and below the stage,
`r = m - n` applications of finite-cut receiving along a saturated visible chain of `Q`'s plan,
each preceded by a repair of the donor to the actual current root, produce an actual tuple `u`
over `t` on `Q`'s exact scheme agreeing with `Q` below `γ`. -/
theorem receive_cover_at_cap_of_receiving (hcons : R.IsExactParentConsistent)
    (hFC : FiniteCutReceiving R) {γ : ExtOrd} (hγbot : ⊥ < γ)
    (hγα : γ < ofOrd α.1) (r : ℕ) :
    ∀ {n m : ℕ} (Q : S α.1 m), SelfVis m γ → ∀ (f : Fin n ↪ Fin m), n + r = m →
      ∀ (t : Fin n ↪ M) (p : S α.1 n), typeMap f Q = some p → R.eval t = some p →
        ∃ (u : Fin m ↪ M) (Q' : S α.1 m), f.trans u = t ∧ R.eval u = some Q' ∧
          ∃ h : Q'.scheme = Q.scheme,
            ∀ d, min (Q'.label d) γ = min (Q.label (SemScheme.castCell h d)) γ := by
  induction r with
  | zero =>
    intro n m Q _ f hcard t p hp ht
    subst hcard
    have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp f.injective
    let e : Fin n ≃ Fin (n + 0) := Equiv.ofBijective f hbij
    let g : Fin (n + 0) ↪ Fin n := e.symm.toEmbedding
    have hfg : f.trans g = Function.Embedding.refl _ :=
      Function.Embedding.ext fun i => e.symm_apply_apply i
    have hgf : g.trans f = Function.Embedding.refl _ :=
      Function.Embedding.ext fun i => e.apply_symm_apply i
    refine ⟨g.trans t, Q, ?_, ?_, rfl, fun _ => rfl⟩
    · rw [← Function.Embedding.trans_assoc, hfg, Function.Embedding.refl_trans]
    · have h1 := hcons t p g ht
      rw [h1]
      change typeMap g p = some Q
      rw [typeMap_trans g f Q p hp, hgf, typeMap_refl]
  | succ r ih =>
    intro n m Q hγ f hcard t p hp ht
    -- a one-coordinate visible superface of `f`'s face
    have hvis : Finset.univ.image f ∈ Q.scheme.scheme.plan :=
      (typeMap_isSome_iff f Q).mp (by rw [hp]; rfl)
    have hcardF : (Finset.univ.image f).card = n := by
      rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, Fintype.card_fin]
    have hne : Finset.univ.image f ≠ (Finset.univ : Finset (Fin m)) := by
      intro heq
      rw [heq, Finset.card_univ, Fintype.card_fin] at hcardF
      omega
    obtain ⟨C, hC, hsub, hcardC⟩ :=
      Q.scheme.scheme.isPlan.exists_visible_card_succ_superface hvis hne
    obtain ⟨c, hcC, hcF⟩ := Finset.exists_of_ssubset hsub
    have hcf : c ∉ Set.range f := by
      rintro ⟨i, rfl⟩
      exact hcF (Finset.mem_image_of_mem f (Finset.mem_univ i))
    have himage : Finset.univ.image (snoc f c hcf) = C := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        induction i using Fin.lastCases with
        | last => rw [snoc_apply_last]; exact hcC
        | cast j =>
          rw [snoc_apply_castSucc]
          exact hsub.subset (Finset.mem_image_of_mem f (Finset.mem_univ j))
      · rw [hcardC, hcardF, Finset.card_image_of_injective _ (snoc f c hcf).injective,
          Finset.card_univ, Fintype.card_fin]
    set g : Fin (n + 1) ↪ Fin m := snoc f c hcf with hgdef
    have hvg : Finset.univ.image g ∈ Q.scheme.scheme.plan := himage ▸ hC
    -- the one-point candidate: the donor's restriction to the superface
    set p' : S α.1 (n + 1) := Q.restrictFace g hvg with hp'def
    have hp' : typeMap g Q = some p' := typeMap_eq_some g Q hvg
    have hcof : IsCoface p p' := by
      change typeMap Fin.castSuccEmb p' = some p
      rw [typeMap_trans Fin.castSuccEmb g Q p' hp', hgdef, castSuccEmb_trans_snoc]
      exact hp
    -- finite-cut receiving at the cap
    obtain ⟨y, hy, q', hq', h, hagree⟩ :=
      hFC t p ht p' hcof γ hγbot hγα
    -- repair the donor to the actual received root, retaining the `γ`-caps
    obtain ⟨⟨Ds, labels, bounds, lawful⟩, hDs, hQ₁g, hQ₁γ⟩ :=
      exists_stage_extends_capped_emb Q.scheme g hvg q' h.symm Q.respects hγ hγα
        (fun i => (hagree (SemScheme.castCell h.symm i)).symm)
    dsimp only at hDs
    subst Ds
    let Q₁ : S α.1 m := ⟨Q.scheme, labels, bounds, lawful⟩
    -- the induction hypothesis over the received root
    obtain ⟨u, Q', hgu, hu, h', hagree'⟩ :=
      ih Q₁ hγ g (by omega) (snoc t y hy) q' hQ₁g hq'
    refine ⟨u, Q', ?_, hu, h', fun d => (hagree' d).trans (hQ₁γ _)⟩
    have hf : f = Fin.castSuccEmb.trans g := (castSuccEmb_trans_snoc f c hcf).symm
    rw [hf, Function.Embedding.trans_assoc, hgu, castSuccEmb_trans_snoc]

/-- **Finite-cover receiving.**  Over an exact realized root `t ↦ p`, every finite legal donor
`Q` whose face `f` is `p` is received below any proper cutoff `δ` below the stage: an actual
tuple `u` over `t` on `Q`'s exact scheme agrees with `Q` below `δ`.  No stage block is spent. -/
theorem finiteCoverReceiving_of_receiving (hcons : R.IsExactParentConsistent)
    (hFC : FiniteCutReceiving R) {n m : ℕ} (Q : S α.1 m) (f : Fin n ↪ Fin m)
    (t : Fin n ↪ M) (p : S α.1 n) (hp : typeMap f Q = some p) (ht : R.eval t = some p)
    (δ : ExtOrd) (hδbot : ⊥ < δ) (hδα : δ < ofOrd α.1) :
    ∃ (u : Fin m ↪ M) (Q' : S α.1 m), f.trans u = t ∧ R.eval u = some Q' ∧
      ∃ h : Q'.scheme = Q.scheme,
        ∀ d, min (Q'.label d) δ = min (Q.label (SemScheme.castCell h d)) δ := by
  obtain ⟨ν, rfl, hν⟩ : ∃ ν : Ordinal.{0}, δ = ofOrd ν ∧ ν < α.1 := by
    rcases ExtOrd.cases δ with rfl | rfl | ⟨ν, rfl⟩
    · exact absurd hδbot (lt_irrefl _)
    · exact absurd hδα (not_lt.mpr le_top)
    · exact ⟨ν, rfl, ofOrd_lt_ofOrd.mp hδα⟩
  have hnm : n ≤ m := by
    have := Fintype.card_le_of_embedding f
    simpa only [Fintype.card_fin] using this
  obtain ⟨u, Q', hfu, hu, h, hagree⟩ :=
    receive_cover_at_cap_of_receiving hcons hFC (γ := ofOrd (ν + m))
    (bot_lt_ofOrd _) (ofOrd_lt_ofOrd.mpr (add_nat_lt_limitStage hν m)) (m - n) Q
    (selfVis_ofOrd_add_nat ν m) f (by omega) t p hp ht
  exact ⟨u, Q', hfu, hu, h, fun d => GradeTailRestoration.cap_below (hagree d)
    (ofOrd_le_ofOrd.mpr (le_add_nat ν m))⟩

end VaughtConjecture.Knight.FiniteCoverReceiving
