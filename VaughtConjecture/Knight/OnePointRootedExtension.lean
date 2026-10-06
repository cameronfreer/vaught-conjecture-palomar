/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RootedExtension
public import VaughtConjecture.Knight.TerminalBase
public import VaughtConjecture.Knight.VisibleFaceOneStep
public import VaughtConjecture.Knight.PairedTrace

/-! # Literal one-point rooted transfer: interface, terminal dichotomy, iteration

## The request-local dichotomy (Lemma 5.5.1 + Prop. 7.3.3 reorganized)

The paper's two global cases — hollow/finite characteristic ⇒ requests transfer (Prop. 7.3.3);
non-hollow/infinite characteristic ⇒ the model prolongs (Lemma 5.5.1) — reorganized as one
request-local disjunction: every selected rooted one-point request is realized, or the source
prolongs to the next block.  At a terminal source the second disjunct is impossible, so every
request transfers.  The substantive direction (from a failed request, build the next-block
prolongation) is
the provisional `M⁺` construction, parked: it needs the faithful transitivity of `⇒`
(Lemma 2.3.14, blocked math).

## Iteration

`rootedExtensionOver_of_onePoint`: literal one-point rooted transfer iterates to the
finite-extension `RootedExtensionOver` (trivial admissibility): walk the plan of the target
from the face `image f` to the full face one coordinate at a time
(`IsPlan.exists_visible_card_succ_superface`), extending the enumeration by `snoc`; at the full
face the enumeration is a bijection and exact consistency reindexes the realization to `f`.
Admissibility is trivial: the paper's cutoff clauses are automatic on tail-core charts
(`FiniteCoreEnvelope`).  Hence KVC need only supply literal one-point transfer over the
selected root.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower KnightRealization

universe w

variable {α : LimitStage} {M : Type w}

/-- **Literal one-point rooted transfer** (Prop. 7.3.3's shape): over every evaluated tuple
containing the root, every admissible one-point extension of the realized label is realized
(the new point is the last coordinate). -/
def OnePointRootedExtensionOver (W : KnightRealization α M) {c : ℕ} (core : Fin c ↪ M)
    (Adm : RootedAdmissibility α) : Prop :=
  ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), (∃ e : Fin c ↪ Fin n, e.trans t = core) →
    W.eval t = some p →
    ∀ (P : S α.1 (n + 1)), typeMap Fin.castSuccEmb P = some p → Adm Fin.castSuccEmb p P →
      ∃ u : Fin (n + 1) ↪ M, Fin.castSuccEmb.trans u = t ∧ W.eval u = some P

/-- Finite-extension transfer specializes to one-point transfer. -/
theorem RootedExtensionOver.onePoint {W : KnightRealization α M} {c : ℕ} {core : Fin c ↪ M}
    {Adm : RootedAdmissibility α} (h : RootedExtensionOver W core Adm) :
    OnePointRootedExtensionOver W core Adm :=
  fun t p he ht P hP hadm => h t p he ht Fin.castSuccEmb P hP hadm

/-- **The request-local dichotomy at a block** (Lemma 5.5.1 + Prop. 7.3.3 merged): every
selected one-point request over the root is realized, or the source prolongs to the next
block within the models. -/
def OnePointTransferOrProlongation {ρ : Ordinal.{0}} (W : KnightRealization (blockStage ρ) M)
    {c : ℕ} (core : Fin c ↪ M) (Adm : RootedAdmissibility (blockStage ρ)) : Prop :=
  ∀ {n : ℕ} (t : Fin n ↪ M) (p : S (blockStage ρ).1 n), (∃ e : Fin c ↪ Fin n, e.trans t = core) →
    W.eval t = some p →
    ∀ (P : S (blockStage ρ).1 (n + 1)), typeMap Fin.castSuccEmb P = some p →
      Adm Fin.castSuccEmb p P →
      (∃ u : Fin (n + 1) ↪ M, Fin.castSuccEmb.trans u = t ∧ W.eval u = some P) ∨
        W.ProlongsToIn IsModelClass (blockStage_le_succ ρ)

/-- **At a terminal source every selected request transfers.** -/
theorem onePointRootedExtensionOver_of_noProlongation {ρ : Ordinal.{0}}
    {W : KnightRealization (blockStage ρ) M} {c : ℕ} {core : Fin c ↪ M}
    {Adm : RootedAdmissibility (blockStage ρ)} (h : OnePointTransferOrProlongation W core Adm)
    (hstop : W.NoProlongationToIn IsModelClass (blockStage_le_succ ρ)) :
    OnePointRootedExtensionOver W core Adm := by
  intro n t p he ht P hP hadm
  rcases h t p he ht P hP hadm with hreal | hpro
  · exact hreal
  · exact absurd hpro hstop

/-- The global dichotomy implies the request-local one: on the transfer branch every request
is realized; on the prolongation branch the second disjunct holds. -/
theorem onePointTransferOrProlongation_of_dichotomy {ρ : Ordinal.{0}}
    {W : KnightRealization (blockStage ρ) M} {c : ℕ} {core : Fin c ↪ M}
    {Adm : RootedAdmissibility (blockStage ρ)}
    (h : OnePointRootedExtensionOver W core Adm ∨
      W.ProlongsToIn IsModelClass (blockStage_le_succ ρ)) :
    OnePointTransferOrProlongation W core Adm := by
  intro n t p he ht P hP hadm
  rcases h with htr | hpro
  · exact Or.inl (htr t p he ht P hP hadm)
  · exact Or.inr hpro

/-! ### Iteration -/


open AmalgamationPlan

/-- The trivial admissibility predicate. -/
def AdmTop (α : LimitStage) : RootedAdmissibility α := fun _ _ _ => True

theorem image_snoc_univ {n N : ℕ} (e : Fin n ↪ Fin N) (x : Fin N) (hx : x ∉ Set.range e) :
    (Finset.univ : Finset (Fin (n + 1))).image (snoc e x hx) =
      insert x (Finset.univ.image e) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    rcases eq_or_ne i (Fin.last n) with rfl | h
    · left; exact snoc_apply_last e x hx
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr h
      right; exact ⟨j, (snoc_apply_castSucc e x hx j).symm⟩
  · rintro (hy | ⟨j, rfl⟩)
    · exact ⟨Fin.last n, (snoc_apply_last e x hx).trans hy.symm⟩
    · exact ⟨j.castSucc, snoc_apply_castSucc e x hx j⟩

/-- The chain invariant at a visible face `B` of `P`: an enumeration `e` of `B` extending `f`
through `c`, and a realization of `P ↾ e` extending `t` through `c`. -/
structure FaceRealization (W : KnightRealization α M) {n N : ℕ} (t : Fin n ↪ M)
    (f : Fin n ↪ Fin N) (P : S α.1 N) (B : Finset (Fin N)) : Type w where
  k : ℕ
  e : Fin k ↪ Fin N
  image_e : Finset.univ.image e = B
  c : Fin n ↪ Fin k
  c_e : c.trans e = f
  u : Fin k ↪ M
  c_u : c.trans u = t
  hvis : Finset.univ.image e ∈ P.scheme.scheme.plan
  eval_u : W.eval u = some (P.restrictFace e hvis)

/-- The chain step: a visible superface with one more coordinate. -/
theorem FaceRealization.step {W : KnightRealization α M} {c₀ : ℕ} {core : Fin c₀ ↪ M}
    (hone : OnePointRootedExtensionOver W core (AdmTop α)) {n N : ℕ} {t : Fin n ↪ M}
    (hroot : ∃ e₀ : Fin c₀ ↪ Fin n, e₀.trans t = core) {f : Fin n ↪ Fin N} {P : S α.1 N}
    {B C : Finset (Fin N)} (R : FaceRealization W t f P B) (hC : C ∈ P.scheme.scheme.plan)
    (hBC : B ⊂ C) (hcard : C.card = B.card + 1) : Nonempty (FaceRealization W t f P C) := by
  classical
  obtain ⟨x, hxC, hxB⟩ := Finset.exists_of_ssubset hBC
  have hCeq : C = insert x B := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset hxC hBC.subset
    · rw [Finset.card_insert_of_notMem hxB, hcard]
  have hx : x ∉ Set.range R.e := by
    rintro ⟨i, hi⟩
    apply hxB
    rw [← R.image_e]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  let e' := snoc R.e x hx
  have himg : Finset.univ.image e' = C := by
    rw [image_snoc_univ, R.image_e, hCeq]
  have hvis' : Finset.univ.image e' ∈ P.scheme.scheme.plan := himg ▸ hC
  have hP' : typeMap e' P = some (P.restrictFace e' hvis') := typeMap_eq_some e' P hvis'
  have hstep : typeMap Fin.castSuccEmb (P.restrictFace e' hvis') =
      some (P.restrictFace R.e R.hvis) := by
    rw [typeMap_trans Fin.castSuccEmb e' P _ hP', castSuccEmb_trans_snoc]
    exact typeMap_eq_some R.e P R.hvis
  have hroot' : ∃ e₀ : Fin c₀ ↪ Fin R.k, e₀.trans R.u = core := by
    obtain ⟨e₀, he₀⟩ := hroot
    exact ⟨e₀.trans R.c, by rw [Function.Embedding.trans_assoc, R.c_u, he₀]⟩
  obtain ⟨u', hu'u, hu'P⟩ := hone R.u _ hroot' R.eval_u _ hstep trivial
  refine ⟨⟨R.k + 1, e', himg, R.c.trans Fin.castSuccEmb, ?_, u', ?_, hvis', hu'P⟩⟩
  · rw [Function.Embedding.trans_assoc, castSuccEmb_trans_snoc, R.c_e]
  · rw [Function.Embedding.trans_assoc, hu'u, R.c_u]

/-- A maximal realized face is full: every proper face admits a strict extension. -/
theorem FaceRealization.exists_full {α : LimitStage} {M : Type*}
    {W : KnightRealization α M} {c₀ : ℕ} {core : Fin c₀ ↪ M}
    (hone : OnePointRootedExtensionOver W core (AdmTop α)) {n N : ℕ} {t : Fin n ↪ M}
    (hroot : ∃ e₀ : Fin c₀ ↪ Fin n, e₀.trans t = core) {f : Fin n ↪ Fin N} {P : S α.1 N}
    {B : Finset (Fin N)} (hB : B ∈ P.scheme.scheme.plan)
    (R : FaceRealization W t f P B) : Nonempty (FaceRealization W t f P Finset.univ) := by
  classical
  let faces := Finset.univ.filter fun C : Finset (Fin N) =>
    C ∈ P.scheme.scheme.plan ∧ Nonempty (FaceRealization W t f P C)
  have hinit : B ∈ faces := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB, ⟨R⟩⟩
  obtain ⟨C, hC, hmax⟩ := faces.exists_max_image Finset.card ⟨_, hinit⟩
  obtain ⟨hCvis, ⟨RC⟩⟩ := (Finset.mem_filter.mp hC).2
  by_cases hfull : C = Finset.univ
  · exact ⟨hfull ▸ RC⟩
  obtain ⟨D, hD, hCD, hcard⟩ :=
    P.scheme.scheme.isPlan.exists_visible_card_succ_superface hCvis hfull
  have hDmem : D ∈ faces := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hD, RC.step hone hroot hD hCD hcard⟩
  have hle := hmax D hDmem
  omega


/-- Climb the plan to the full face. -/
theorem FaceRealization.exists_univ {W : KnightRealization α M} {c₀ : ℕ} {core : Fin c₀ ↪ M}
    (hone : OnePointRootedExtensionOver W core (AdmTop α)) {n N : ℕ} {t : Fin n ↪ M}
    (hroot : ∃ e₀ : Fin c₀ ↪ Fin n, e₀.trans t = core) {f : Fin n ↪ Fin N} {P : S α.1 N} :
    ∀ (m : ℕ) (B : Finset (Fin N)), B ∈ P.scheme.scheme.plan → N - B.card = m →
      FaceRealization W t f P B → Nonempty (FaceRealization W t f P Finset.univ) := by
  intro _ B hB _ R
  exact R.exists_full hone hroot hB

/-- **One-point rooted transfer iterates to finite-extension rooted transfer** (trivial
admissibility). -/
theorem rootedExtensionOver_of_onePoint {W : KnightRealization α M}
    (hcons : W.IsExactParentConsistent) {c₀ : ℕ} {core : Fin c₀ ↪ M}
    (hone : OnePointRootedExtensionOver W core (AdmTop α)) :
    RootedExtensionOver W core (AdmTop α) := by
  intro n t p hroot ht N f P hfP _
  -- the base face
  have hvis : Finset.univ.image f ∈ P.scheme.scheme.plan :=
    (typeMap_isSome_iff f P).mp (by rw [hfP]; rfl)
  have hp : P.restrictFace f hvis = p := by
    have := typeMap_eq_some f P hvis
    rw [hfP] at this
    exact (Option.some_injective _ this).symm
  let R₀ : FaceRealization W t f P (Finset.univ.image f) :=
    ⟨n, f, rfl, Function.Embedding.refl _, Function.Embedding.refl_trans _, t,
      Function.Embedding.refl_trans _, hvis, by rw [hp]; exact ht⟩
  obtain ⟨R⟩ :=
    R₀.exists_full hone hroot hvis
  -- the full face: `e` is a bijection
  have hsurj : Function.Surjective R.e := by
    intro y
    have hy : y ∈ Finset.univ.image R.e := by rw [R.image_e]; exact Finset.mem_univ y
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hy
    exact ⟨i, hi⟩
  let eq : Fin R.k ≃ Fin N := R.e.equivOfSurjective hsurj
  let g : Fin N ↪ Fin R.k := eq.symm.toEmbedding
  have hge : g.trans R.e = Function.Embedding.refl _ :=
    Function.Embedding.ext fun y => eq.apply_symm_apply y
  have heg : R.e.trans g = Function.Embedding.refl _ :=
    Function.Embedding.ext fun i => eq.symm_apply_apply i
  refine ⟨g.trans R.u, ?_, ?_⟩
  · have hf : f.trans (g.trans R.u) = (R.c.trans R.e).trans (g.trans R.u) :=
      congrArg (fun h : Fin n ↪ Fin N => h.trans (g.trans R.u)) R.c_e.symm
    rw [hf, Function.Embedding.trans_assoc, ← Function.Embedding.trans_assoc R.e g R.u, heg,
      Function.Embedding.refl_trans, R.c_u]
  · rw [exactParent_typeMap hcons R.u _ g R.eval_u,
      typeMap_trans g R.e P _ (typeMap_eq_some R.e P R.hvis), hge, typeMap_refl]

end VaughtConjecture.Knight
