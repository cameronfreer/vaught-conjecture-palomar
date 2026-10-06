/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionInjectivity

/-! # Reduction preserves the specified isomorphism

Between models at a fixed block, a bijection is an isomorphism iff it is an
isomorphism of their reducts to any lower block. The lift keeps that bijection
literally; reduction gives an equivalence of isomorphism types, compatible with
identity, inverse and composition. In particular the sets of automorphisms are
equal on the same carrier, not merely abstractly isomorphic.
-/

@[expose] public section

namespace VaughtConjecture.Knight.KnightRealization

open TypeTower

universe w w' w''
variable {M : Type w} {N : Type w'} {P : Type w''} {σ ρ : Ordinal.{0}}
  {W : KnightRealization (blockStage ρ) M}
  {V : KnightRealization (blockStage ρ) N}
  {Z : KnightRealization (blockStage ρ) P}

/-- The very bijection giving an isomorphism of lower reducts preserves the
upper models. No choice of a new permutation is involved. -/
theorem isIso_of_reduct_isIso (h : σ ≤ ρ) (hW : W.IsModel) (hV : V.IsModel)
    {e : M ≃ N}
    (he : (W.reduct (blockStage_mono h)).IsIso (V.reduct (blockStage_mono h)) e) :
    W.IsIso V e := by
  have hWV : W.map e = V := by
    apply eq_of_reduct_eq_of_le ρ σ h _ _ (hW.map e) hV
    rw [Realization.reduct_map]
    exact he.map_eq
  rw [← hWV]
  exact fun {n} t => Realization.isIso_map e W (n := n) t

/-- Isomorphism of a specified bijection is unchanged by reduction. -/
theorem isIso_reduct_iff (h : σ ≤ ρ) (hW : W.IsModel) (hV : V.IsModel)
    (e : M ≃ N) :
    (W.reduct (blockStage_mono h)).IsIso (V.reduct (blockStage_mono h)) e ↔
      W.IsIso V e :=
  ⟨isIso_of_reduct_isIso h hW hV, Realization.IsIso.reduct (blockStage_mono h)⟩

/-- Lift a specified reduct isomorphism, keeping its underlying bijection. -/
def liftReductIso (h : σ ≤ ρ) (hW : W.IsModel) (hV : V.IsModel)
    (i : (W.reduct (blockStage_mono h)).Iso (V.reduct (blockStage_mono h))) :
    W.Iso V :=
  ⟨i.1, isIso_of_reduct_isIso h hW hV i.2⟩

@[simp] theorem liftReductIso_val (h : σ ≤ ρ) (hW : W.IsModel) (hV : V.IsModel)
    (i : (W.reduct (blockStage_mono h)).Iso (V.reduct (blockStage_mono h))) :
    (liftReductIso h hW hV i).1 = i.1 := rfl

/-- Reduction is an equivalence on the actual isomorphisms, not just `Nonempty`. -/
noncomputable def reductIsoEquiv (h : σ ≤ ρ) (hW : W.IsModel) (hV : V.IsModel) :
    W.Iso V ≃ (W.reduct (blockStage_mono h)).Iso (V.reduct (blockStage_mono h)) where
  toFun := Realization.Iso.reduct (blockStage_mono h)
  invFun := liftReductIso h hW hV
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp] theorem liftReductIso_refl (h : σ ≤ ρ) (hW : W.IsModel) :
    liftReductIso h hW hW (Realization.Iso.refl _) = Realization.Iso.refl W :=
  Subtype.ext rfl

@[simp] theorem liftReductIso_symm (h : σ ≤ ρ) (hW : W.IsModel) (hV : V.IsModel)
    (i : (W.reduct (blockStage_mono h)).Iso (V.reduct (blockStage_mono h))) :
    liftReductIso h hV hW i.symm = (liftReductIso h hW hV i).symm :=
  Subtype.ext rfl

@[simp] theorem liftReductIso_trans (h : σ ≤ ρ)
    (hW : W.IsModel) (hV : V.IsModel) (hZ : Z.IsModel)
    (i : (W.reduct (blockStage_mono h)).Iso (V.reduct (blockStage_mono h)))
    (j : (V.reduct (blockStage_mono h)).Iso (Z.reduct (blockStage_mono h))) :
    liftReductIso h hW hZ (i.trans j) =
      (liftReductIso h hW hV i).trans (liftReductIso h hV hZ j) :=
  Subtype.ext rfl

/-- Automorphisms are the same permutations before and after reduction. -/
theorem automorphisms_reduct_eq (h : σ ≤ ρ) (hW : W.IsModel) :
    {e : M ≃ M | (W.reduct (blockStage_mono h)).IsIso (W.reduct (blockStage_mono h)) e} =
      {e : M ≃ M | W.IsIso W e} :=
  Set.ext fun e => isIso_reduct_iff h hW hW e

end VaughtConjecture.Knight.KnightRealization
