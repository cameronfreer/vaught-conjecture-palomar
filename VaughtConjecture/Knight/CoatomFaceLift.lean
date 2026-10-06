/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteCofaceSupply
public import VaughtConjecture.Knight.CoatomAmalgamation
public import VaughtConjecture.Knight.VisibleFaceOneStep

/-! # Finite coface lifting from coatom amalgamation

The finite consequences of `MaximalCoatomAmalgamationSupply`: zero-padded
face lifting, exact-pair amalgamation, and uniformity/high-grade cofaces.
Their statements and namespaces are unchanged. The Henkin model-existence
and spectrum applications remain in `CoatomHenkinBridge`.
-/

@[expose] public section

namespace VaughtConjecture.Knight
open StageType TypeTower Cardinal
namespace FixedHeight
variable {α : Ordinal.{0}}

/-! ### Face-embedding algebra -/

theorem extendFace_trans {k n N : ℕ} (e : Fin k ↪ Fin n) (h : Fin n ↪ Fin N) :
    (extendFace e).trans (extendFace h) = extendFace (e.trans h) := by
  refine Function.Embedding.ext fun i => ?_
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

theorem castSuccEmb_trans_extendFace {n N : ℕ} (g : Fin n ↪ Fin N) :
    (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)).trans (extendFace g) = g.trans Fin.castSuccEmb := by
  refine Function.Embedding.ext fun i => ?_
  simp [Fin.castSuccEmb_apply]

/-- The image of an embedding of `Fin n` into itself is everything. -/
theorem image_univ_eq_univ_of_card {n : ℕ} (g : Fin n ↪ Fin n) :
    Finset.univ.image g = Finset.univ :=
  Finset.eq_univ_of_card _ (by rw [Finset.card_image_of_injective _ g.injective]; simp)

/-- The coatom pair of one step of the chain: the second coatom is the initial face (the
enlarged master face), the first is the one-point extension of the lower-face embedding `e`;
the common lower face enters the first along `castSuccEmb` and the second along `e`. -/
def _root_.VaughtConjecture.Knight.CoatomPair.step {n : ℕ} (e : Fin n ↪ Fin (n + 1)) :
    CoatomPair n where
  f₁ := extendFace e
  f₂ := Fin.castSuccEmb
  g₁ := Fin.castSuccEmb
  g₂ := e
  comm := castSuccEmb_trans_extendFace e
  ne := by
    intro h
    have hl : Fin.last (n + 1) ∈ Finset.univ.image (extendFace e) :=
      Finset.mem_image.mpr ⟨Fin.last n, Finset.mem_univ _, extendFace_last e⟩
    rw [h] at hl
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hl
    exact (Fin.castSucc_lt_last k).ne hk

/-! ### The zero-padded face lift -/

/-- **The zero-padded face lift**, by induction on the codimension `m` of the face. -/
theorem pinnedCofaceLift (H : MaximalCoatomAmalgamationSupply α) :
    ∀ (m : ℕ) {N n : ℕ}, N = n + m → ∀ (P : S α N) (g : Fin n ↪ Fin N) (p : S α n),
      typeMap g P = some p → ∀ q : S α (n + 1), IsCoface p q →
        ∃ Q : S α (N + 1), IsCoface P Q ∧ typeMap (extendFace g) Q = some q := by
  intro m
  induction m with
  | zero =>
    intro N n hN P g p hg q hq
    subst hN
    -- `g` is a permutation; relabel `q` along the inverse of `extendFace g`.
    have hgbij : Function.Bijective g := Finite.injective_iff_bijective.mp g.injective
    let σg := Equiv.ofBijective g hgbij
    have hσbij : Function.Bijective (extendFace g) :=
      Finite.injective_iff_bijective.mp (extendFace g).injective
    let σ := Equiv.ofBijective (extendFace g) hσbij
    have hvis : Finset.univ.image σ.symm.toEmbedding ∈ q.scheme.scheme.plan := by
      rw [image_univ_eq_univ_of_card]
      exact q.scheme.scheme.isPlan.domain_mem
    refine ⟨q.restrictFace σ.symm.toEmbedding hvis, ?_, ?_⟩
    · have hQ := typeMap_eq_some σ.symm.toEmbedding q hvis
      change typeMap Fin.castSuccEmb (q.restrictFace σ.symm.toEmbedding hvis) = some P
      rw [typeMap_trans _ _ q _ hQ]
      have hcomp : Fin.castSuccEmb.trans σ.symm.toEmbedding =
          σg.symm.toEmbedding.trans Fin.castSuccEmb := by
        refine Function.Embedding.ext fun j => ?_
        change σ.symm (Fin.castSucc j) = Fin.castSucc (σg.symm j)
        apply σ.injective
        rw [Equiv.apply_symm_apply]
        change Fin.castSucc j = extendFace g (Fin.castSucc (σg.symm j))
        rw [extendFace_castSucc]
        congr 1
        exact (Equiv.apply_symm_apply σg j).symm
      rw [hcomp, ← typeMap_trans _ _ q p hq, typeMap_trans _ _ P p hg]
      have hid : σg.symm.toEmbedding.trans g = Function.Embedding.refl _ := by
        refine Function.Embedding.ext fun j => ?_
        exact Equiv.apply_symm_apply σg j
      rw [hid, typeMap_refl]
    · have hQ := typeMap_eq_some σ.symm.toEmbedding q hvis
      rw [typeMap_trans _ _ q _ hQ]
      have hid : (extendFace g).trans σ.symm.toEmbedding = Function.Embedding.refl _ := by
        refine Function.Embedding.ext fun j => ?_
        exact Equiv.symm_apply_apply σ j
      rw [hid, typeMap_refl]
  | succ m ih =>
    intro N n hN P g p hg q hq
    -- the face is visible and proper; take a one-point visible superface `C`
    have hB : Finset.univ.image g ∈ P.scheme.scheme.plan :=
      (typeMap_isSome_iff g P).mp (by rw [hg]; rfl)
    have hBne : Finset.univ.image g ≠ Finset.univ := by
      intro h
      have := congrArg Finset.card h
      rw [Finset.card_image_of_injective _ g.injective] at this
      simp at this
      omega
    obtain ⟨C, hC, hBC, hcard⟩ :=
      P.scheme.scheme.isPlan.exists_visible_card_succ_superface hB hBne
    rw [Finset.card_image_of_injective _ g.injective, Finset.card_univ, Fintype.card_fin] at hcard
    -- enumerate `C` and factor `g` through it
    let h : Fin (n + 1) ↪ Fin N := (C.orderEmbOfFin hcard).toEmbedding
    have hrange : Finset.univ.image h = C := by
      apply Finset.coe_injective
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact Finset.range_orderEmbOfFin C hcard
    have hmem : ∀ i, g i ∈ C := fun i =>
      hBC.subset (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    let e : Fin n ↪ Fin (n + 1) :=
      ⟨fun i => (C.orderIsoOfFin hcard).symm ⟨g i, hmem i⟩, fun i j hij => by
        have := congrArg (fun x => ((C.orderIsoOfFin hcard) x).1) hij
        simp only [OrderIso.apply_symm_apply] at this
        exact g.injective this⟩
    have hfactor : e.trans h = g := by
      refine Function.Embedding.ext fun i => ?_
      change (C.orderEmbOfFin hcard) ((C.orderIsoOfFin hcard).symm ⟨g i, hmem i⟩) = g i
      rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    have hC' : Finset.univ.image h ∈ P.scheme.scheme.plan := by rwa [hrange]
    have hp' := typeMap_eq_some h P hC'
    set p' := P.restrictFace h hC' with hp'def
    have hep : typeMap e p' = some p := by
      rw [typeMap_trans _ _ P p' hp', hfactor]; exact hg
    -- one coatom amalgamation: `q` and `p'` over `p`
    obtain ⟨Q', hQ', -⟩ := H n (CoatomPair.step e) q p' ⟨p, hq, hep⟩
    have hQ'₁ : typeMap (extendFace e) Q' = some q := hQ'.face₁
    have hQ'₂ : IsCoface p' Q' := hQ'.face₂
    -- lift `Q'` over the enlarged face by the induction hypothesis
    obtain ⟨Q, hQP, hQh⟩ := ih (N := N) (n := n + 1) (by omega) P h p' hp' Q' hQ'₂
    refine ⟨Q, hQP, ?_⟩
    rw [← hfactor, ← extendFace_trans, ← typeMap_trans _ _ Q Q' hQh]
    exact hQ'₁

/-- **Rung 1 from the receiver**: the pinned coface supply. -/
theorem pinnedCofaceSupply_of_supply {β : LimitStage}
    (H : MaximalCoatomAmalgamationSupply β.1) : PinnedCofaceSupply β := by
  intro N n P g p hg q hq
  have hle : n ≤ N := by
    have := Fintype.card_le_of_injective g g.injective
    simpa using this
  exact pinnedCofaceLift H (N - n) (by omega) P g p hg q hq

/-- Exact-pair amalgamation (two cofaces of a common base amalgamate) is a theorem from the
receiver — it is the coatom instance of Cor. 4.3.22. -/
theorem exactPairAmalgamation_of_supply {β : LimitStage}
    (H : MaximalCoatomAmalgamationSupply β.1) : ExactPairAmalgamation β :=
  PinnedCofaceSupply.exactPairAmalgamation (pinnedCofaceSupply_of_supply H)

/-! ### The band producer and the master supply -/

/-- A uniformity coface of every base, from the receiver and the seed labelled `γ + 1`. -/
theorem exists_uniformity_coface {β : LimitStage} (H : MaximalCoatomAmalgamationSupply β.1)
    {n : ℕ} (p : S β.1 n) (γ : Ordinal.{0}) (_h1 : Value.IsNonSuccessor γ) (h2 : γ < β.1) :
    ∃ q ∈ UniformityFamily (α := β.1) γ, IsCoface p q := by
  obtain ⟨r, Sig, hr⟩ := exists_successorOneType_of_lt β.2 h2
  refine exists_uniformity_candidate H p r Sig ?_ ?_
  · rw [hr, ExtOrd.ofOrd_le_ofOrd]; exact Order.le_succ γ
  · rw [hr, ExtOrd.ofOrd_lt_ofOrd]; exact (add_lt_add_iff_left γ).mpr Ordinal.one_lt_omega0

/-- A high-grade-dominance coface of every base, from the receiver and the seed labelled
`γ + 1`. -/
theorem exists_highGrade_coface {β : LimitStage} (H : MaximalCoatomAmalgamationSupply β.1)
    {n : ℕ} (p : S β.1 n) (γ : Ordinal.{0}) (h2 : γ < β.1) :
    ∃ q ∈ HighGradeDominanceFamily (α := β.1) γ, IsCoface p q := by
  obtain ⟨r, Sig, hr⟩ := exists_successorOneType_of_lt β.2 h2
  refine exists_highGradeDominance_candidate H p r Sig ?_
  rw [hr, ExtOrd.ofOrd_lt_ofOrd]; exact Order.lt_succ γ

end FixedHeight
end VaughtConjecture.Knight
