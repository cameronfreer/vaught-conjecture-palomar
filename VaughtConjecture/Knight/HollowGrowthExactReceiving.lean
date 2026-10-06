/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HollowGrowthReadback
public import VaughtConjecture.Knight.HollowGrowthPadding
public import VaughtConjecture.Knight.TopSupportReceiving
public import VaughtConjecture.Knight.GrowthCarrierEvaluation

/-! # Exact receiving in hollow growth models

An acquired input's legal carrier is realized by generalized saturation.
Coface consistency retains the actual private face, and physical readback
therefore retains every donor label literally, including top. Padding and
restriction give exact one-point receiving over arbitrary realized roots,
the empty root included. No display or stage-bound premise is added.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.HollowGrowthTemplate
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor
noncomputable section
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}

namespace Input
variable {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {q : S α.1 (n + 1)} {Nmin : ℕ}
  {D : HollowGrowthReference.Data (W := W) t p (donorRequests q) (n + 1) Nmin}
  (I : Input q D)

include I in
/-- The donor scheme and its labelling are both exact. The new point is
fresh even over the acquired private context. -/
theorem receives_exactly (hM : W.IsModel) :
    ∃ (y : M) (_hy : y ∉ Set.range D.context.tuple) (hyRoot : y ∉ Set.range t),
      W.eval (snoc t y hyRoot) = some q := by
  obtain ⟨y, hy, hyRoot, s, heval, he, hc⟩ :=
    GrowthCarrierEvaluation.exists_correct_donor D.context.type q.scheme p.scheme D.face
      I.hvC I.hvP I.hC I.hP I.relative I.attachment I.donor_arity_lt
      W.actualLabelling hM D.context.eval_eq I.actual_inClass
  have hlabel : ∀ d, s.label (SemScheme.castCell he.symm d) = q.label d :=
    congrFun (I.exact_of_correct hc)
  have hsq : s = q := StageType.eq_of_label he hlabel
  have hr : ∃ hyRoot : y ∉ Set.range (D.face.trans D.context.tuple),
      W.eval (snoc (D.face.trans D.context.tuple) y hyRoot) = some q :=
    ⟨hyRoot, hsq ▸ heval⟩
  exact ⟨y, hy, by simpa only [D.face_tuple] using hr⟩

end Input

/-- Positive roots use the acquired input directly, without enlarging the donor. -/
theorem receives_exactly_of_pos (hM : W.IsModel) (hg : W.HasTopGradeGrowth)
    (hh : W.IsHollow) {n : ℕ} (hn : 0 < n) (t : Fin n ↪ M) (p : S α.1 n)
    (hp : W.eval t = some p) (q : S α.1 (n + 1)) (hq : IsCoface p q) :
    ∃ (y : M) (hy : y ∉ Set.range t), W.eval (snoc t y hy) = some q := by
  obtain ⟨D, ⟨I⟩⟩ := acquire q hM hg hh hn hp hq 0
  obtain ⟨y, _, hy, heval⟩ := I.receives_exactly hM
  exact ⟨y, hy, heval⟩

/-- Exact one-point receiving over every actual root, with no root-arity
restriction and no loss at donor tops. -/
theorem receives_exactly (hM : W.IsModel) (hg : W.HasTopGradeGrowth) (hh : W.IsHollow)
    {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (hp : W.eval t = some p)
    (q : S α.1 (n + 1)) (hq : IsCoface p q) :
    ∃ (y : M) (hy : y ∉ Set.range t), W.eval (snoc t y hy) = some q := by
  by_cases hn : 0 < n
  · exact receives_exactly_of_pos hM hg hh hn t p hp q hq
  obtain ⟨z, hz, pR, _, _, Q, _, hkeep, D, ⟨I⟩⟩ :=
    acquire_padded hM hg hh t p hp q hq 0
  obtain ⟨y, _, hy, heval⟩ := I.receives_exactly hM
  have he := exactParent_typeMap hM.consistent
    (snoc (snoc t z hz) y hy) Q (FixedHeight.extendFace Fin.castSuccEmb) heval
  rw [donor_tuple] at he
  exact ⟨y, _, he.trans hkeep⟩

end
end VaughtConjecture.Knight.HollowGrowthTemplate
