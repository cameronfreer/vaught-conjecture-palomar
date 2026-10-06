/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CapReceivingModel

/-! # Complete positive-root cap receiving using an actual positive chart

The finite singleton attachment is constructed by the ordinary finite supplier.
No actual singleton chart, target modelhood, uniformity or dominance is assumed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FiniteCutReceiving
open TypeTower StageType KnightRealization Value ExtOrd CellScheme.restrictFace
universe w
variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-- A single positive chart bootstraps empty-root receiving. -/
theorem of_positive_chart (hcons : R.IsExactParentConsistent)
    (hchart : ∃ (m : ℕ) (u : Fin (m + 1) ↪ M) (P : S α.1 (m + 1)), R.eval u = some P)
    (hpos : ∀ {n : ℕ}, 0 < n → ∀ (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
      ∀ q : S α.1 (n + 1), IsCoface p q →
        ∀ δ : ExtOrd, ⊥ < δ → δ < ofOrd α.1 →
          ∃ (y : M) (hy : y ∉ Set.range t) (r : S α.1 (n + 1)),
            R.eval (snoc t y hy) = some r ∧ ∃ he : r.scheme = q.scheme,
              ∀ d, min (r.label d) δ = min (q.label (SemScheme.castCell he d)) δ) :
    FiniteCutReceiving R := by
  intro n t p hp q hqp δ hδ hδα
  cases n with
  | succ n => exact hpos (Nat.succ_pos n) t p hp q hqp δ hδ hδα
  | zero =>
    obtain ⟨m, u, P, hP⟩ := hchart
    obtain ⟨Q, hQP, hQq, _⟩ := exists_amalgam_point (CanonicalCoatomSupply.supply α.2)
      m (Fin.last (m + 1)) P q
    have hcof : IsCoface P Q := by
      change typeMap Fin.castSuccEmb Q = some P
      rw [castSuccEmb_eq_succAboveEmb_last]
      exact hQP
    obtain ⟨y, hy, r, hr, he, hcap⟩ := hpos (Nat.succ_pos m) u P hP Q hcof δ hδ hδα
    obtain ⟨rs, rl, rb, rr⟩ := r
    dsimp only at he
    subst rs
    let r : S α.1 (m + 2) := ⟨Q.scheme, rl, rb, rr⟩
    let f := pointEmb (Fin.last (m + 1))
    have hv : Finset.univ.image f ∈ Q.scheme.scheme.plan :=
      (typeMap_isSome_iff f Q).mp (by rw [hQq]; rfl)
    have heq : Q.restrictFace f hv = q :=
      Option.some.inj ((typeMap_eq_some f Q hv).symm.trans hQq)
    have hlabels : ∀ {a b : S α.1 1} (h : a = b) (d : Cell a.scheme.scheme),
        a.label d = b.label (SemScheme.castCell (congrArg StageType.scheme h) d) := by
      intro a b h d
      cases h
      rfl
    have hy0 : y ∉ Set.range t := fun ⟨i, _⟩ => i.elim0
    have htup : f.trans (snoc u y hy) = snoc t y hy0 := by
      ext i
      obtain rfl : i = Fin.last 0 := Subsingleton.elim _ _
      change snoc u y hy (Fin.last (m + 1)) = snoc t y hy0 (Fin.last 0)
      simp only [snoc_apply_last]
    have hscheme := congrArg StageType.scheme heq
    change (r.restrictFace f hv).scheme = q.scheme at hscheme
    refine ⟨y, hy0, r.restrictFace f hv, ?_, hscheme, ?_⟩
    · rw [← htup, hcons _ r f hr]
      exact typeMap_eq_some f r hv
    · intro d
      exact (hcap (toCell Q.scheme.scheme f hv d)).trans
        (congrArg (fun x => min x δ) (hlabels heq d))

/-- Nonemptiness and covering supply the positive chart, without a model request clause. -/
theorem of_positive (hne : Nonempty M) (hcons : R.IsExactParentConsistent)
    (hcover : R.IsInitialSegmentCovering)
    (hpos : ∀ {n : ℕ}, 0 < n → ∀ (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
      ∀ q : S α.1 (n + 1), IsCoface p q →
        ∀ δ : ExtOrd, ⊥ < δ → δ < ofOrd α.1 →
          ∃ (y : M) (hy : y ∉ Set.range t) (r : S α.1 (n + 1)),
            R.eval (snoc t y hy) = some r ∧ ∃ he : r.scheme = q.scheme,
              ∀ d, min (r.label d) δ = min (q.label (SemScheme.castCell he d)) δ) :
    FiniteCutReceiving R := by
  refine of_positive_chart hcons ?_ hpos
  obtain ⟨x⟩ := hne
  let t : Fin 1 ↪ M := ⟨fun _ => x, fun a b _ => Subsingleton.elim a b⟩
  obtain ⟨k, u, _, hu⟩ := hcover t
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hu
  refine ⟨k, ?_⟩
  have hh : ∃ (u : Fin (1 + k) ↪ M) (P : S α.1 (1 + k)), R.eval u = some P :=
    ⟨u, P, hP⟩
  rw [Nat.add_comm 1 k] at hh
  exact hh

end VaughtConjecture.Knight.FiniteCutReceiving
