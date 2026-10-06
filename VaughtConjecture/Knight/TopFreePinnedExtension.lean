/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LawfulCapping
public import VaughtConjecture.Knight.CanonicalCoatomFiniteSupply
public import VaughtConjecture.Knight.CoatomFaceLift

/-! # Top-free pinned extensions for capped requests

The exact finite supplier is capped only after choosing a proper self-visible bound
above the entire old master and the observation cutoff. The master stays literal;
the donor retains its exact scheme and every observation, but need not retain tops.
No self-visibility of the observation cutoff itself is assumed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.TopFreePinnedExtension
open TypeTower StageType Value ExtOrd FixedHeight CellScheme.restrictFace

variable {β : LimitStage} {n m : ℕ}

noncomputable def cap (Q : S β.1 (n + 1)) (γ : ExtOrd)
    (hγ : extVisibilityReplace γ (n + 1) (n + 1) = γ) (hγβ : γ < ofOrd β.1) :
    S β.1 (n + 1) where
  scheme := Q.scheme
  label d := min (Q.label d) γ
  label_bound _ := Or.inl ((min_le_right _ _).trans_lt hγβ)
  respects := FiniteCutCapping.respects_cap Q.respects hγ

theorem cap_typeMap_fixed (Q : S β.1 (n + 1)) (γ : ExtOrd)
    (hγ : extVisibilityReplace γ (n + 1) (n + 1) = γ) (hγβ : γ < ofOrd β.1)
    (f : Fin m ↪ Fin (n + 1)) (P : S β.1 m) (hf : typeMap f Q = some P)
    (hP : ∀ d, P.label d ≤ γ) : typeMap f (cap Q γ hγ hγβ) = some P := by
  have hv := (typeMap_isSome_iff f Q).mp (by rw [hf]; rfl)
  have he := Option.some.inj ((typeMap_eq_some f Q hv).symm.trans hf)
  subst P
  rw [typeMap_eq_some f (cap Q γ hγ hγβ) hv]
  congr 1
  refine StageType.ext (t₁ := (cap Q γ hγ hγβ).restrictFace f hv)
    (t₂ := Q.restrictFace f hv) rfl ?_
  apply heq_of_eq
  funext d
  exact min_eq_left (hP d)

/-- An arbitrary prescribed donor over a visible face of a top-free master is
received at any proper observation cutoff by a top-free literal master extension.
Includes the empty master/root, bottom cutoff and donor labels equal to top. -/
theorem exists_pinned {N n : ℕ} (P : S β.1 N) (hP : ∀ d, P.label d ≠ ⊤)
    (g : Fin n ↪ Fin N) (p : S β.1 n) (hg : typeMap g P = some p)
    (q : S β.1 (n + 1)) (hq : IsCoface p q)
    (δ : ExtOrd) (hδ : δ < ofOrd β.1) :
    ∃ Q : S β.1 (N + 1), IsCoface P Q ∧ (∀ d, Q.label d ≠ ⊤) ∧
      ∃ q' : S β.1 (n + 1), typeMap (extendFace g) Q = some q' ∧
        ∃ he : q'.scheme = q.scheme,
          ∀ d, min (q'.label d) δ = min (q.label (SemScheme.castCell he d)) δ := by
  classical
  obtain ⟨Q, hQP, hQq⟩ :=
    pinnedCofaceSupply_of_supply (CanonicalCoatomSupply.supply β.2) P g p hg q hq
  let v : Cell P.scheme.scheme ⊕ Unit → ExtOrd := Sum.elim P.label (fun _ => δ)
  have hv : ∀ i, v i < ofOrd β.1 := by
    intro i
    cases i with
    | inl d => exact (P.label_bound d).resolve_right (hP d)
    | inr u => exact hδ
  obtain ⟨γ, hγ, _, hvγ, hγβ⟩ :=
    FiniteCutCapping.exists_cap_below_limit v β.2 hv (N + 1)
  have hδγ : δ ≤ γ := hvγ (.inr ())
  have hPγ : ∀ d, P.label d ≤ γ := fun d => hvγ (.inl d)
  let Q' := cap Q γ hγ hγβ
  have hqvis := (typeMap_isSome_iff (extendFace g) Q).mp (by rw [hQq]; rfl)
  have he := Option.some.inj ((typeMap_eq_some (extendFace g) Q hqvis).symm.trans hQq)
  subst q
  refine ⟨Q', cap_typeMap_fixed Q γ hγ hγβ Fin.castSuccEmb P hQP hPγ,
    fun d => ne_top_of_lt ((min_le_right (Q.label d) γ).trans_lt hγβ),
    Q'.restrictFace (extendFace g) hqvis, typeMap_eq_some (extendFace g) Q' hqvis, rfl, ?_⟩
  intro d
  change min (min _ γ) δ = min _ δ
  rw [min_assoc, min_eq_right hδγ]
  rfl

end VaughtConjecture.Knight.TopFreePinnedExtension
