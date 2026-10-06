/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteCoverReceiving
public import VaughtConjecture.Knight.TopSupportRigidCoreCap

/-! # Classification from globally rigid top-support cores

Model-level chart extension, isomorphism, and countability results for globally rigid cores.
-/

@[expose] public section

namespace VaughtConjecture.Knight.TopSupportRigidCore
open TypeTower StageType KnightRealization Value ExtOrd
universe w
variable {α : LimitStage} {M M₁ M₂ : Type w} {R : KnightRealization α M}
  {R₁ : KnightRealization α M₁} {R₂ : KnightRealization α M₂}

/-- **One forth step**: a common chart containing both cores extends to one containing a
scheduled point of the first model, by covering it in the first model, receiving the cover's
type over the second side above every proper label, and reading the tops back from rigidity of
the first model's core. -/
theorem exists_step_left (hM₁ : R₁.IsModel) (hM₂ : R₂.IsModel) {k : ℕ} {B₁ : Fin k ↪ M₁}
    {B₂ : Fin k ↪ M₂} (r₁ : RigidCore R₁ B₁) (nd : CommonChartNode (A₁ := R₁) (A₂ := R₂))
    (hnd : CoreChart B₁ B₂ nd) (x : M₁) :
    ∃ (next : CommonChartNode (A₁ := R₁) (A₂ := R₂)) (emb : Fin nd.arity ↪ Fin next.arity),
      emb.trans next.tuple₁ = nd.tuple₁ ∧ emb.trans next.tuple₂ = nd.tuple₂ ∧
      (∃ i, next.tuple₁ i = x) ∧ CoreChart B₁ B₂ next := by
  exact exists_step_left_of_receiving hM₁.consistent hM₁.covering hM₂.consistent
    (OrdinaryModelReceiving.finiteCutReceiving hM₂) r₁ nd hnd x

/-- The chart invariant is preserved by density on both sides. -/
theorem restrictedStepSupply (hM₁ : R₁.IsModel) (hM₂ : R₂.IsModel) {k : ℕ} {B₁ : Fin k ↪ M₁}
    {B₂ : Fin k ↪ M₂} (r₁ : RigidCore R₁ B₁) (r₂ : RigidCore R₂ B₂) :
    RestrictedCommonChartStepSupply (A₁ := R₁) (A₂ := R₂) (CoreChart B₁ B₂) := by
  exact restrictedStepSupply_of_receiving hM₁.consistent hM₁.covering
    (OrdinaryModelReceiving.finiteCutReceiving hM₁) hM₂.consistent hM₂.covering
    (OrdinaryModelReceiving.finiteCutReceiving hM₂) r₁ r₂

/-- **Root-preserving classification**: two countable models at the same stage with globally
rigid cores of the same finite type are isomorphic by an isomorphism carrying one core onto the
other coordinatewise. -/
theorem exists_iso_of_rigidCores [Countable M₁] [Countable M₂] (hM₁ : R₁.IsModel)
    (hM₂ : R₂.IsModel) {k : ℕ} {B₁ : Fin k ↪ M₁} {B₂ : Fin k ↪ M₂} {b : S α.1 k}
    (h₁ : R₁.eval B₁ = some b) (h₂ : R₂.eval B₂ = some b) (r₁ : RigidCore R₁ B₁)
    (r₂ : RigidCore R₂ B₂) : ∃ e : R₁.Iso R₂, ∀ i, e.1 (B₁ i) = B₂ i := by
  have := hM₁.nonempty
  have := hM₂.nonempty
  exact exists_iso_of_rigidCores_of_receiving hM₁.consistent hM₁.covering
    (OrdinaryModelReceiving.finiteCutReceiving hM₁) hM₂.consistent hM₂.covering
    (OrdinaryModelReceiving.finiteCutReceiving hM₂) h₁ h₂ r₁ r₂

/-- **Classification**: two countable models at the same stage with globally rigid cores of the
same finite type are isomorphic. -/
theorem nonempty_iso_of_rigidCores [Countable M₁] [Countable M₂] (hM₁ : R₁.IsModel)
    (hM₂ : R₂.IsModel) {k : ℕ} {B₁ : Fin k ↪ M₁} {B₂ : Fin k ↪ M₂} {b : S α.1 k}
    (h₁ : R₁.eval B₁ = some b) (h₂ : R₂.eval B₂ = some b) (r₁ : RigidCore R₁ B₁)
    (r₂ : RigidCore R₂ B₂) : Nonempty (R₁.Iso R₂) := by
  have := hM₁.nonempty
  have := hM₂.nonempty
  exact nonempty_iso_of_rigidCores_of_receiving hM₁.consistent hM₁.covering
    (OrdinaryModelReceiving.finiteCutReceiving hM₁) hM₂.consistent hM₂.covering
    (OrdinaryModelReceiving.finiteCutReceiving hM₂) h₁ h₂ r₁ r₂

/-- The classification with the core arities and types given up to `HEq`. -/
theorem nonempty_iso_of_rigidCores' [Countable M₁] [Countable M₂] (hM₁ : R₁.IsModel)
    (hM₂ : R₂.IsModel) {k₁ k₂ : ℕ} {B₁ : Fin k₁ ↪ M₁} {B₂ : Fin k₂ ↪ M₂} {b₁ : S α.1 k₁}
    {b₂ : S α.1 k₂} (h₁ : R₁.eval B₁ = some b₁) (h₂ : R₂.eval B₂ = some b₂)
    (r₁ : RigidCore R₁ B₁) (r₂ : RigidCore R₂ B₂) (hk : k₁ = k₂) (hb : HEq b₁ b₂) :
    Nonempty (R₁.Iso R₂) := by
  have := hM₁.nonempty
  have := hM₂.nonempty
  exact nonempty_iso_of_rigidCores'_of_receiving hM₁.consistent hM₁.covering
    (OrdinaryModelReceiving.finiteCutReceiving hM₁) hM₂.consistent hM₂.covering
    (OrdinaryModelReceiving.finiteCutReceiving hM₂) h₁ h₂ r₁ r₂ hk hb

/-- **Countability**: at a countable stage, a family of pairwise non-isomorphic countable models
each with a globally rigid core is countable. -/
theorem countable_of_rigidCores {ι : Type*} (hα : α.1.card ≤ Cardinal.aleph0)
    {N : ι → Type w} [∀ i, Countable (N i)] (W : ∀ i, KnightRealization α (N i))
    (hW : ∀ i, (W i).IsModel)
    (core : ∀ i, ∃ (k : ℕ) (B : Fin k ↪ N i) (b : S α.1 k), (W i).eval B = some b ∧
      RigidCore (W i) B)
    (hanti : ∀ i j, i ≠ j → IsEmpty ((W i).Iso (W j))) : Countable ι := by
  choose k B b hb hr using core
  have : ∀ n, Countable (S α.1 n) := fun n => StageType.countable_S hα n
  let φ : ι → Σ n : ℕ, S α.1 n := fun i => ⟨k i, b i⟩
  have hinj : Function.Injective φ := by
    intro i j hij
    by_contra hne
    have hk : k i = k j := congrArg Sigma.fst hij
    have hbij : HEq (b i) (b j) := (Sigma.ext_iff.mp hij).2
    exact (hanti i j hne).false (nonempty_iso_of_rigidCores' (hW i) (hW j) (hb i) (hb j) (hr i)
      (hr j) hk hbij).some
  exact hinj.countable

/-- Enlarging a globally rigid core preserves rigidity, whether or not the
initial tuple itself has a label. -/
theorem rigidCore_mono {k m : ℕ} {B : Fin k ↪ M} {C : Fin m ↪ M}
    (hB : RigidCore R B) (f : Fin k ↪ Fin m) (hf : f.trans C = B) : RigidCore R C := by
  intro n D d hd e he H hH ht
  apply hB D d hd (f.trans e) (by rw [Function.Embedding.trans_assoc, he, hf]) H hH
  intro x hx htop
  apply ht x ?_ htop
  intro z hz
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (hx hz)
  exact Finset.mem_image.mpr ⟨f i, Finset.mem_univ _, hi⟩

/-- Any globally rigid tuple has an actual labelled rigid cover. -/
theorem exists_labelled_core (hM : R.IsModel)
    (h : ∃ (k : ℕ) (B : Fin k ↪ M), RigidCore R B) :
    ∃ (k : ℕ) (B : Fin k ↪ M) (b : S α.1 k), R.eval B = some b ∧ RigidCore R B := by
  obtain ⟨k, B, hB⟩ := h
  obtain ⟨j, C, hC, hsome⟩ := hM.covering B
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨k + j, C, c, hc, rigidCore_mono hB (Fin.castAddEmb j) hC⟩

end VaughtConjecture.Knight.TopSupportRigidCore
