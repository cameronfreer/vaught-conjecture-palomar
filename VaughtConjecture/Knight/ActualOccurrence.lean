/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Terminal

/-! # Literal restriction of actual occurrences

Coordinate geometry and exact parent consistency restrict an already realized
extension to any named subroot. This does not realize a chosen labelling, assert
readback, or use covering or any existential model clause. Literal face identities
separately identify the restricted scheme and its installed occurrence map.

The hollow, stable and ordinary receiving applications share this transport;
their lawful-row constructions, realization mechanisms and readback proofs remain
separate. Historical names for the coordinate geometry are preserved.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight
open TypeTower KnightRealization StageType

/-- The last coordinate is not a cast-successor. -/
theorem last_not_mem_range_trans_castSuccEmb {n m : ℕ} (e : Fin n ↪ Fin m) :
    Fin.last m ∉ Set.range (e.trans Fin.castSuccEmb) := by
  rintro ⟨i, hi⟩
  exact (Fin.castSucc_lt_last (e i)).ne hi

/-- The one-point extension of a coordinate embedding: the new point goes to the new point. -/
def onePointProj {n m : ℕ} (e : Fin n ↪ Fin m) : Fin (n + 1) ↪ Fin (m + 1) :=
  snoc (e.trans Fin.castSuccEmb) (Fin.last m) (last_not_mem_range_trans_castSuccEmb e)

@[simp] theorem onePointProj_castSucc {n m : ℕ} (e : Fin n ↪ Fin m) (i : Fin n) :
    onePointProj e (Fin.castSucc i) = Fin.castSucc (e i) :=
  snoc_apply_castSucc _ _ _ i

@[simp] theorem onePointProj_last {n m : ℕ} (e : Fin n ↪ Fin m) :
    onePointProj e (Fin.last n) = Fin.last m :=
  snoc_apply_last _ _ _

namespace StageType

/-- Restrict to a literal semantic face and identify every installed occurrence.
No assertion about the restricted labels is an input. -/
theorem exists_restriction_with_map {α : Ordinal.{0}} {m n : ℕ}
    {E : SemScheme n} {P : SemScheme m} (f : Fin m ↪ Fin n)
    (hv : Finset.univ.image f ∈ E.scheme.plan) (he : E.restrictFace f hv = P)
    (occ : Cell P.scheme → Cell E.scheme)
    (hocc : ∀ d, CellScheme.restrictFace.toCell E.scheme f hv
      (SemScheme.castCell he.symm d) = occ d)
    {r : S α n} (hr : r.scheme = E) :
    ∃ s : S α m, ∃ hs : typeMap f r = some s, ∃ hp : s.scheme = P,
      ∀ d, mapCell hs (SemScheme.castCell hp.symm d) = SemScheme.castCell hr.symm (occ d) := by
  obtain ⟨Er, v, hb, hlaw⟩ := r
  dsimp only at hr
  subst Er
  let r : S α n := ⟨E, v, hb, hlaw⟩
  exact ⟨r.restrictFace f hv, typeMap_eq_some _ _ hv, he, hocc⟩

end StageType

namespace KnightRealization
universe w
variable {M : Type w} {m n : ℕ}

/-- Concatenating along a restricted tuple is restricting along `onePointProj e`. -/
theorem onePointProj_trans_snoc (e : Fin m ↪ Fin n) (t : Fin n ↪ M) (y : M)
    (hy : y ∉ Set.range t) (hy' : y ∉ Set.range (e.trans t)) :
    (onePointProj e).trans (snoc t y hy) = snoc (e.trans t) y hy' := by
  ext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

/-- Keep the actual witness point while restricting its occurrence to a named
subroot. The tuple equation is exported for later stable-value transport. -/
theorem restrict_actual_extension {α : LimitStage} {W : KnightRealization α M}
    (hW : W.IsExactParentConsistent) (e : Fin m ↪ Fin n)
    {u : Fin n ↪ M} {t : Fin m ↪ M} (ht : e.trans u = t)
    {y : M} (hy : y ∉ Set.range u) {r : S α.1 (n + 1)} {s : S α.1 (m + 1)}
    (hr : W.eval (snoc u y hy) = some r) (hs : typeMap (onePointProj e) r = some s) :
    ∃ hyRoot : y ∉ Set.range t,
      (onePointProj e).trans (snoc u y hy) = snoc t y hyRoot ∧
      W.eval (snoc t y hyRoot) = some s := by
  subst t
  have hyRoot : y ∉ Set.range (e.trans u) := fun ⟨i, hi⟩ => hy ⟨e i, hi⟩
  have he := onePointProj_trans_snoc e u y hy hyRoot
  refine ⟨hyRoot, he, ?_⟩
  rw [← he, hW (snoc u y hy) r (onePointProj e) hr]
  exact hs

end KnightRealization
end VaughtConjecture.Knight
