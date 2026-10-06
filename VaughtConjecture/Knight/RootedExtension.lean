/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RootedKarp
public import VaughtConjecture.Knight.PairedTrace

/-! # The core-rooted extension property and its back-and-forth consumer

Knight's Prop. 7.3.3 is a ONE-model, core-rooted extension theorem: over tuples containing a
finite core, every coface satisfying the forced characteristic-arity/anchor restrictions is
realized.  Prop. 10.2.1 then says "apply Prop. 7.3.3 and perform a back-and-forth".  This
module compiles that back-and-forth, generically:

* `RootedAdmissibility α` — a predicate on rooted extensions (root embedding, base label,
  extension label);
* `RootedExtensionOver W core Adm` — over every evaluated tuple containing `core`, every
  admissible rooted extension of the realized label is realized in `W`;
* `RealizedAdmissible W Adm` — every realized rooted extension is admissible;
* `restrictedStepSupply_of_rootedExtension` — the extension property for ONE shared
  admissibility predicate, with every realized extension admissible, yields the selected
  transfer step below every common chart containing the cores;
* `nonempty_iso_of_rootedExtension` — hence two exactly-consistent covering realizations on
  countable carriers with cores of equal label are isomorphic.

This is a SUFFICIENT ADAPTER for the pair-local interface of `TerminalParameterCode`
(`PairLocalTerminalData`): the seed's actual consumer (Prop. 10.2.1) only alternates
Prop. 7.3.3 in a back-and-forth, i.e. needs one selected transfer step at each reached
common chart, not a global one-model extension theory.

The proof is the restricted common-chart step supply below core-containing nodes, seeded by
the cores (`nonempty_iso_of_restrictedCommonChartStepSupply`): a scheduled new point is
absorbed by covering into a realized rooted extension, which is admissible, hence realized
over the other side's chart by the extension property.  No universal menu intersection
between arbitrary source models is involved. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower KnightRealization

universe w

/-- An admissibility predicate on rooted extensions: root embedding, base label, extension
label. -/
abbrev RootedAdmissibility (α : LimitStage) : Type 1 :=
  ∀ {n N : ℕ}, (Fin n ↪ Fin N) → S α.1 n → S α.1 N → Prop

variable {α : LimitStage} {M : Type w}

/-- **The core-rooted extension property** (Prop. 7.3.3 shape): over every evaluated tuple
containing the core, every admissible rooted extension of the realized label is realized. -/
def RootedExtensionOver (W : KnightRealization α M) {c : ℕ} (core : Fin c ↪ M)
    (Adm : RootedAdmissibility α) : Prop :=
  ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), (∃ e : Fin c ↪ Fin n, e.trans t = core) →
    W.eval t = some p →
    ∀ {N : ℕ} (f : Fin n ↪ Fin N) (P : S α.1 N), typeMap f P = some p → Adm f p P →
      ∃ u : Fin N ↪ M, f.trans u = t ∧ W.eval u = some P

/-- Every realized rooted extension **over a tuple containing the root** is admissible
(root-sensitive: the back-and-forth only consults admissibility at charts containing the
selected root, and it carries the root embedding). -/
def RealizedAdmissibleOver (W : KnightRealization α M) {c : ℕ} (core : Fin c ↪ M)
    (Adm : RootedAdmissibility α) : Prop :=
  ∀ {n N : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (f : Fin n ↪ Fin N) (u : Fin N ↪ M)
    (P : S α.1 N), (∃ e : Fin c ↪ Fin n, e.trans t = core) →
    W.eval t = some p → f.trans u = t → W.eval u = some P → Adm f p P

/-- Every realized rooted extension is admissible (the root-free, stronger form). -/
def RealizedAdmissible (W : KnightRealization α M) (Adm : RootedAdmissibility α) : Prop :=
  ∀ {n N : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (f : Fin n ↪ Fin N) (u : Fin N ↪ M)
    (P : S α.1 N), W.eval t = some p → f.trans u = t → W.eval u = some P → Adm f p P

theorem RealizedAdmissible.over {W : KnightRealization α M} {Adm : RootedAdmissibility α}
    (h : RealizedAdmissible W Adm) {c : ℕ} (core : Fin c ↪ M) :
    RealizedAdmissibleOver W core Adm :=
  fun t p f u P _ ht hf hu => h t p f u P ht hf hu

/-- The rooted embedding of a chart into a covering of its one-point extension. -/
theorem trans_snoc_cover {n k : ℕ} {t : Fin n ↪ M} {x : M} {hx : x ∉ Set.range t}
    {s : Fin (n + 1 + k) ↪ M} (hst : (Fin.castAddEmb k).trans s = snoc t x hx) :
    (Fin.castSuccEmb.trans (Fin.castAddEmb k)).trans s = t := by
  ext i
  have h := DFunLike.congr_fun hst (Fin.castSucc i)
  simp only [Function.Embedding.trans_apply, Fin.castAddEmb_apply] at h
  change s (Fin.castAdd k (Fin.castSucc i)) = t i
  rw [h]
  exact snoc_apply_castSucc t x hx i

theorem cover_mem_range {n k : ℕ} {t : Fin n ↪ M} {x : M} {hx : x ∉ Set.range t}
    {s : Fin (n + 1 + k) ↪ M} (hst : (Fin.castAddEmb k).trans s = snoc t x hx) :
    ∃ i, s i = x := by
  refine ⟨Fin.castAdd k (Fin.last n), ?_⟩
  have h := DFunLike.congr_fun hst (Fin.last n)
  simp only [Function.Embedding.trans_apply, Fin.castAddEmb_apply] at h
  rw [h]
  exact snoc_apply_last t x hx

/-- The common charts containing a given pair of cores. -/
def ContainsCores {M₁ M₂ : Type w} {W₁ : KnightRealization α M₁} {W₂ : KnightRealization α M₂}
    {c : ℕ} (core₁ : Fin c ↪ M₁) (core₂ : Fin c ↪ M₂)
    (nd : CommonChartNode (A₁ := W₁) (A₂ := W₂)) : Prop :=
  ∃ e : Fin c ↪ Fin nd.arity, e.trans nd.tuple₁ = core₁ ∧ e.trans nd.tuple₂ = core₂

/-- **The selected transfer step from the core-rooted extension property**: below every
common chart containing the cores, a scheduled point is absorbed — covering realizes a
rooted extension on its side, admissibility transfers it, and the other side's extension
property realizes it over the other chart. -/
theorem restrictedStepSupply_of_rootedExtension {M₁ M₂ : Type w}
    {W₁ : KnightRealization α M₁} {W₂ : KnightRealization α M₂}
    (h₁ : W₁.IsExactParentConsistent) (h₂ : W₂.IsExactParentConsistent)
    (hc₁ : W₁.IsInitialSegmentCovering) (hc₂ : W₂.IsInitialSegmentCovering)
    (Adm : RootedAdmissibility α) {c : ℕ} (core₁ : Fin c ↪ M₁) (core₂ : Fin c ↪ M₂)
    (hext₁ : RootedExtensionOver W₁ core₁ Adm) (hext₂ : RootedExtensionOver W₂ core₂ Adm)
    (hadm₁ : RealizedAdmissibleOver W₁ core₁ Adm) (hadm₂ : RealizedAdmissibleOver W₂ core₂ Adm) :
    RestrictedCommonChartStepSupply (A₁ := W₁) (A₂ := W₂) (ContainsCores core₁ core₂) := by
  classical
  rintro nd ⟨e, he₁, he₂⟩ z
  rcases z with x | y
  · by_cases hx : x ∈ Set.range nd.tuple₁
    · obtain ⟨i, hi⟩ := hx
      exact ⟨⟨⟨nd, Function.Embedding.refl _, rfl, rfl,
        fun x' hx' => ⟨i, hi.trans (Sum.inl.inj hx')⟩,
        fun y hy => absurd hy Sum.inl_ne_inr⟩, ⟨e, he₁, he₂⟩⟩⟩
    · obtain ⟨k, s₁, hst, hsome⟩ := hc₁ (snoc nd.tuple₁ x hx)
      obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hsome
      let f : Fin nd.arity ↪ Fin (nd.arity + 1 + k) := Fin.castSuccEmb.trans (Fin.castAddEmb k)
      have hft : f.trans s₁ = nd.tuple₁ := trans_snoc_cover hst
      have hadm : Adm f nd.type P := hadm₁ nd.tuple₁ nd.type f s₁ P ⟨e, he₁⟩ nd.eval₁ hft hP
      have htm : typeMap f P = some nd.type := by
        rw [← exactParent_typeMap h₁ s₁ P f hP, hft]
        exact nd.eval₁
      obtain ⟨u, hut, huP⟩ := hext₂ nd.tuple₂ nd.type ⟨e, he₂⟩ nd.eval₂ f P htm hadm
      refine ⟨⟨⟨⟨nd.arity + 1 + k, s₁, u, P, hP, huP⟩, f, hft, hut, ?_, ?_⟩, ?_⟩⟩
      · intro x' hx'
        obtain ⟨i, hi⟩ := cover_mem_range hst
        exact ⟨i, hi.trans (Sum.inl.inj hx')⟩
      · exact fun y hy => absurd hy Sum.inl_ne_inr
      · refine ⟨e.trans f, ?_, ?_⟩
        · rw [Function.Embedding.trans_assoc, hft, he₁]
        · rw [Function.Embedding.trans_assoc, hut, he₂]
  · by_cases hy : y ∈ Set.range nd.tuple₂
    · obtain ⟨i, hi⟩ := hy
      exact ⟨⟨⟨nd, Function.Embedding.refl _, rfl, rfl,
        fun x hx => absurd hx.symm Sum.inl_ne_inr,
        fun y' hy' => ⟨i, hi.trans (Sum.inr.inj hy')⟩⟩, ⟨e, he₁, he₂⟩⟩⟩
    · obtain ⟨k, s₂, hst, hsome⟩ := hc₂ (snoc nd.tuple₂ y hy)
      obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hsome
      let f : Fin nd.arity ↪ Fin (nd.arity + 1 + k) := Fin.castSuccEmb.trans (Fin.castAddEmb k)
      have hft : f.trans s₂ = nd.tuple₂ := trans_snoc_cover hst
      have hadm : Adm f nd.type P := hadm₂ nd.tuple₂ nd.type f s₂ P ⟨e, he₂⟩ nd.eval₂ hft hP
      have htm : typeMap f P = some nd.type := by
        rw [← exactParent_typeMap h₂ s₂ P f hP, hft]
        exact nd.eval₂
      obtain ⟨u, hut, huP⟩ := hext₁ nd.tuple₁ nd.type ⟨e, he₁⟩ nd.eval₁ f P htm hadm
      refine ⟨⟨⟨⟨nd.arity + 1 + k, u, s₂, P, huP, hP⟩, f, hut, hft, ?_, ?_⟩, ?_⟩⟩
      · exact fun x hx => absurd hx.symm Sum.inl_ne_inr
      · intro y' hy'
        obtain ⟨i, hi⟩ := cover_mem_range hst
        exact ⟨i, hi.trans (Sum.inr.inj hy')⟩
      · refine ⟨e.trans f, ?_, ?_⟩
        · rw [Function.Embedding.trans_assoc, hut, he₁]
        · rw [Function.Embedding.trans_assoc, hft, he₂]

/-- **The root-preserving back-and-forth consumer**: two exactly-consistent covering
realizations on countable carriers, with the core-rooted extension property for one shared
admissibility predicate, every realized rooted extension admissible, and cores of equal label,
are isomorphic by an isomorphism carrying one core onto the other coordinatewise. -/
theorem exists_iso_of_rootedExtension {M₁ M₂ : Type w}
    [Countable M₁] [Countable M₂] [Nonempty M₁] [Nonempty M₂]
    {W₁ : KnightRealization α M₁} {W₂ : KnightRealization α M₂}
    (h₁ : W₁.IsExactParentConsistent) (h₂ : W₂.IsExactParentConsistent)
    (hc₁ : W₁.IsInitialSegmentCovering) (hc₂ : W₂.IsInitialSegmentCovering)
    (Adm : RootedAdmissibility α) {c : ℕ} (core₁ : Fin c ↪ M₁) (core₂ : Fin c ↪ M₂)
    (s : S α.1 c) (hs₁ : W₁.eval core₁ = some s) (hs₂ : W₂.eval core₂ = some s)
    (hext₁ : RootedExtensionOver W₁ core₁ Adm) (hext₂ : RootedExtensionOver W₂ core₂ Adm)
    (hadm₁ : RealizedAdmissibleOver W₁ core₁ Adm) (hadm₂ : RealizedAdmissibleOver W₂ core₂ Adm) :
    ∃ e : W₁.Iso W₂, ∀ i, e.1 (core₁ i) = core₂ i :=
  exists_iso_of_restrictedCommonChartStepSupply h₁ h₂ (ContainsCores core₁ core₂)
    ⟨c, core₁, core₂, s, hs₁, hs₂⟩ ⟨Function.Embedding.refl _, rfl, rfl⟩
    (restrictedStepSupply_of_rootedExtension h₁ h₂ hc₁ hc₂ Adm core₁ core₂ hext₁ hext₂
      hadm₁ hadm₂)

/-- **The back-and-forth consumer**: two exactly-consistent covering realizations on
countable carriers, with the core-rooted extension property for one shared admissibility
predicate, every realized rooted extension admissible, and cores of equal label, are
isomorphic. -/
theorem nonempty_iso_of_rootedExtension {M₁ M₂ : Type w}
    [Countable M₁] [Countable M₂] [Nonempty M₁] [Nonempty M₂]
    {W₁ : KnightRealization α M₁} {W₂ : KnightRealization α M₂}
    (h₁ : W₁.IsExactParentConsistent) (h₂ : W₂.IsExactParentConsistent)
    (hc₁ : W₁.IsInitialSegmentCovering) (hc₂ : W₂.IsInitialSegmentCovering)
    (Adm : RootedAdmissibility α) {c : ℕ} (core₁ : Fin c ↪ M₁) (core₂ : Fin c ↪ M₂)
    (s : S α.1 c) (hs₁ : W₁.eval core₁ = some s) (hs₂ : W₂.eval core₂ = some s)
    (hext₁ : RootedExtensionOver W₁ core₁ Adm) (hext₂ : RootedExtensionOver W₂ core₂ Adm)
    (hadm₁ : RealizedAdmissibleOver W₁ core₁ Adm) (hadm₂ : RealizedAdmissibleOver W₂ core₂ Adm) :
    Nonempty (W₁.Iso W₂) :=
  let ⟨e, _⟩ := exists_iso_of_rootedExtension h₁ h₂ hc₁ hc₂ Adm core₁ core₂ s hs₁ hs₂ hext₁
    hext₂ hadm₁ hadm₂
  ⟨e⟩

end VaughtConjecture.Knight
