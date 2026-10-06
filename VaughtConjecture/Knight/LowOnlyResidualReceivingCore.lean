/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyCofaceAttachmentCore

/-! # Exact receiving in the finite-characteristic residual

V-C's first-loss acquisition supplies the actual private context and strict
source gaps. Reidentifying its common root with the literal coface map feeds
the constructed legal LOW receiver. Finite-cover receiving plus its selected
separator certificate returns the enlarged donor exactly; restriction then
returns the original donor over the original tuple with a genuinely fresh point.

No receiver interface, physical chart, selected display, or cutoff is assumed.
A positive constant top-grade tail, absence of a globally rigid core, and the
donor's top-grade bound remain explicit. The target supplies exact consistency and finite-cut
receiving; no realization covering or modelhood is needed. The growth branch is separate.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyResidualReceiving
open TypeTower StageType KnightRealization Value ExtOrd CappedDonor LowOnly
noncomputable section
universe w

/-- In the residual finite-characteristic branch, every legal donor coface
whose tops have grade at most the characteristic occurs exactly over its root. -/
theorem receive_of_tail {M : Type w} {α : LimitStage} {W : KnightRealization α M}
    (hcons : W.IsExactParentConsistent) (hFC : FiniteCutReceiving W) {K : ℕ}
    (hcoin : KnightRealization.IsCoinitial {x : W.LabelledExt | x.type.topGrade = K}) (hKpos : 0 <
      K)
    (hres : ∀ {k : ℕ} (B : Fin k ↪ M), ¬ TopSupportRigidCore.RigidCore W B)
    {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (hp : W.eval t = some p)
    (q : S α.1 (n + 1)) (hq : IsCoface p q)
    (hqK : ∀ d, q.label d = ⊤ → q.scheme.scheme.grade d ≤ K) :
    ∃ (y : M) (hy : y ∉ Set.range t), W.eval (snoc t y hy) = some q := by
  obtain ⟨k, u, CT, e, pR, Q, hu, hut, hCT, hQ, hQe, F, hFp, -, hFB, hc, hr, hadm⟩ :=
    FirstLossLowFamily.exists_lowOnlyFamily_of_tail hcons hcoin hKpos hres t p hp q hq hqK
  have hshared : F.root.Shared F.p CT.label := by
    rw [hFp]
    exact (hadm 0 ⊥ (selfVis_bot _)).shared
  obtain ⟨v, hv, hroot⟩ := LowOnlyCofaceAttachment.receive_of_shared_of_receiving hQ hCT hcons hFC
    u hu
    F hFB hFp hshared hc hr
  let v₀ : Fin (n + 1) ↪ M := (FixedHeight.extendFace e).trans v
  have hval : W.eval v₀ = some q := (hcons v Q (FixedHeight.extendFace e) hv).trans hQe
  have hprefix : Fin.castSuccEmb.trans v₀ = t := by
    change Fin.castSuccEmb.trans ((FixedHeight.extendFace e).trans v) = t
    rw [← Function.Embedding.trans_assoc, FixedHeight.castSuccEmb_trans_extendFace,
      Function.Embedding.trans_assoc, hroot, ← Function.Embedding.trans_assoc, hut]
  have hy : v₀ (Fin.last n) ∉ Set.range t := by
    rintro ⟨i, hi⟩
    have he : v₀ i.castSucc = v₀ (Fin.last n) :=
      (congrArg (fun f : Fin n ↪ M => f i) hprefix).trans hi
    exact (Fin.castSucc_lt_last i).ne (v₀.injective he)
  have heq : snoc t (v₀ (Fin.last n)) hy = v₀ := by
    apply Function.Embedding.ext
    intro i
    induction i using Fin.lastCases with
    | last => exact snoc_apply_last _ _ _
    | cast j =>
      exact (snoc_apply_castSucc _ _ _ j).trans
        (congrArg (fun f : Fin n ↪ M => f j) hprefix).symm
  exact ⟨v₀ (Fin.last n), hy, heq.symm ▸ hval⟩

end
end VaughtConjecture.Knight.LowOnlyResidualReceiving
